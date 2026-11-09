#!/usr/bin/env python3
"""Check the planned study's allocation and structural consistency, not launch readiness."""

import argparse
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pending_paths(value, prefix=""):
    if isinstance(value, dict):
        for key, child in value.items():
            yield from pending_paths(child, f"{prefix}.{key}" if prefix else key)
    elif value is None:
        yield prefix


def validate(config):
    b = config["benchmark"]
    a = config["agents"]
    h = config["humans"]
    s = config["stages"]
    j = config["judge"]
    analysis = config["analysis"]
    pilot = config["pilot"]
    counts = {
        "tasks": b["tasks"],
        "train_tasks": b["train_tasks"],
        "validation_tasks": b["validation_tasks"],
        "heldout_test_tasks": b["heldout_test_tasks"],
        "agents": a["count"],
        "outputs_per_cell": a["outputs_per_task_agent_per_stage"],
        "total_people": h["total_people"],
        "training_validation_people": h["training_validation_people"],
        "final_audit_people": h["final_audit_people"],
        "base_ratings": h["base_ratings_per_artifact"],
        "dense_tasks": h["dense_tasks"],
        "dense_ratings": h["dense_total_ratings_per_artifact"],
    }
    for name, value in counts.items():
        require(type(value) is int and value > 0, f"{name} must be a positive integer")
    require(b["tasks"] == b["train_tasks"] + b["validation_tasks"] + b["heldout_test_tasks"],
            "Task splits must partition the benchmark")
    require(a["count"] == len(set(a["required_systems"])) == len(a["required_systems"]),
            "Required solver systems must be distinct and match agent count")
    require(h["total_people"] == h["training_validation_people"] + h["final_audit_people"],
            "Human pools must sum to the total people")
    require(h["disjoint_pools"] is True, "Training/validation and audit people must be disjoint")
    require(h["dense_task_source"] == "heldout_test", "Dense tasks must be held out")
    require(h["dense_tasks"] <= b["heldout_test_tasks"], "Dense subset exceeds test tasks")
    require(h["base_ratings_per_artifact"] <= h["training_validation_people"],
            "Too few training/validation people for distinct base ratings")
    require(h["base_ratings_per_artifact"] <= h["dense_total_ratings_per_artifact"] <= h["final_audit_people"],
            "Dense total must include base ratings and fit the audit pool")

    artifacts_per_task = a["count"] * a["outputs_per_task_agent_per_stage"]
    train_val_artifacts = (b["train_tasks"] + b["validation_tasks"]) * artifacts_per_task
    audit_artifacts = b["tasks"] * artifacts_per_task
    train_val_reviews = train_val_artifacts * h["base_ratings_per_artifact"]
    audit_base = audit_artifacts * h["base_ratings_per_artifact"]
    dense_extra = h["dense_tasks"] * artifacts_per_task * (
        h["dense_total_ratings_per_artifact"] - h["base_ratings_per_artifact"])
    expected = {
        "training_validation_artifacts": train_val_artifacts,
        "final_audit_artifacts": audit_artifacts,
        "total_artifacts": train_val_artifacts + audit_artifacts,
        "training_validation_reviews": train_val_reviews,
        "final_audit_base_reviews": audit_base,
        "dense_extra_reviews": dense_extra,
        "total_reviews": train_val_reviews + audit_base + dense_extra,
    }
    for name, value in expected.items():
        require(type(s[name]) is int and s[name] == value,
                f"stages.{name}: recorded {s[name]!r}, derived {value}")
    for total, people, field in [
        (train_val_reviews, h["training_validation_people"], "balanced_reviews_per_training_validation_person"),
        (audit_base + dense_extra, h["final_audit_people"], "balanced_reviews_per_final_audit_person"),
    ]:
        require(total % people == 0, f"Exact workload balance is impossible for {field}")
        require(s[field] == total // people, f"Incorrect workload in {field}")

    require(s["fresh_final_generation_for_seen_tasks"] is True,
            "Seen tasks require fresh final-audit generations")
    require(b["group_related_variants"] is True, "Related task variants must stay together")
    require(j["inputs"] == ["python_source", "candidate_lean", "gold_reference_lean"],
            "The judge must use all three declared inputs")
    require(j["rating_categories"] == list(range(6)) and j["probability_vector_length"] == 6,
            "The judge must predict all six ordinal categories")
    require(j["output"] == "probability_mass_function", "Output must be an explicit probability forecast")
    require(analysis["primary_metric"] == "normalized_ranked_probability_score"
            and analysis["primary_metric_range"] == [0, 1]
            and analysis["threshold_events"] == list(range(5)), "Invalid normalized RPS specification")
    require(analysis["weighting"] == "mean_within_artifact_then_equal_mean_across_artifacts",
            "Dense annotation must not change artifact weighting")
    require(analysis["selection_split"] == "validation"
            and analysis["selection_metric"] == analysis["primary_metric"],
            "Use the common validation RPS for selection")
    require(isinstance(analysis["secondary_metrics"], list)
            and {"ce", "tvd"}.issubset(analysis["secondary_metrics"]),
            "The shared secondary evaluation panel must include CE and TVD")
    require(analysis["tvd_target"] == "per_artifact_empirical_human_rating_distribution",
            "TVD compares with the per-artifact empirical human rating distribution")
    require(analysis["main_judges"] == 1 and analysis["leave_one_agent_out_judges"] == a["count"],
            "Evaluate one main judge and one transfer judge per agent")
    require(analysis["transfer_test_tasks_per_agent"] == b["heldout_test_tasks"],
            "Each transfer procedure must use all held-out test tasks")
    require(analysis["exclude_target_agent_from_training_and_validation"] is True,
            "Target-agent information must be excluded from training and validation")
    require(analysis["retain_individual_ratings"] is True, "Individual human ratings must be preserved")
    require(not pilot["uses_final_audit_people"] and not pilot["uses_heldout_test_tasks"],
            "Pilot must preserve final-audit people and test tasks")
    return expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, default=Path(__file__).resolve().parents[1] / "config.json")
    args = parser.parse_args()
    try:
        config = json.loads(args.config.read_text())
        derived = validate(config)
    except (OSError, json.JSONDecodeError, KeyError, TypeError, ValueError) as error:
        parser.exit(1, f"Design check failed: {error}\n")
    print(json.dumps({
        "design_check": "passed",
        "study_status": config["status"],
        "derived_budget": derived,
        "unresolved_fields": list(pending_paths(config)),
        "note": "Counts and structure checked; no ratings collected or statistical sufficiency established by this script.",
    }, indent=2))


if __name__ == "__main__":
    main()

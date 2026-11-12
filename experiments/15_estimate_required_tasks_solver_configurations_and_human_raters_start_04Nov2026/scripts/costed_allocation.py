#!/usr/bin/env python3
"""Rating-collection scenarios computed from saved results and participant-entered times.

Reads tracked public files only: no model call, no private data, no new rating.

    python3 costed_allocation.py           verify results/costed_allocation.json
    python3 costed_allocation.py --write   regenerate that file
    python3 costed_allocation.py --tables  print the Markdown tables quoted in the docs

Every number is arithmetic on the cited inputs. The standard deviations are implied by
saved 95% percentile-bootstrap intervals under a normal approximation; they are planning
inputs for a different future study, not measurements of it.
"""
import argparse
import csv
import json
import math
import statistics
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
EXPERIMENT = HERE.parent
ROOT = EXPERIMENT.parents[1]
ARCHIVE = ROOT / "experiments/archive"
LEARNING_CURVE = ARCHIVE / "17_measure_judge_learning_from_4_to_20_tasks_and_more_human_ratings_start_11Nov2026_end_11Nov2026/results/results.json"
MIXTURE_TEST = ARCHIVE / "10_fit_5_judge_mixtures_to_75_outputs_pearson_vs_ranked_probability_start_09Nov2026_end_09Nov2026/results/results.json"
COLLECTION = ROOT / "experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026"
MAIN_TASK = COLLECTION / "rating_task_packet/main_rating_task"
OUTPUT = EXPERIMENT / "results/costed_allocation.json"

Z_95_TWO_SIDED = 1.959963984540054  # standard normal 0.975 quantile
Z_80_POWER = 0.8416212335729143     # standard normal 0.80 quantile
RATINGS_PER_FILE = 2                # experiment 09's current target: two independent ratings per file
HALF_WIDTH_TARGETS = [0.02, 0.01, 0.005]
EVALUATION_SIZES = [25, 65, 150]
RATER_POOL_SIZES = [4, 8, 12]
# Agent-suggested starting block, not a user decision: see METHODS_AND_ALLOCATION.md.
DEVELOPMENT_TRAINING_TASKS = 16
DEVELOPMENT_VALIDATION_TASKS = 8


def relative(path):
    return str(path.relative_to(ROOT))


def implied_sd(low, high, units):
    """Unit-level standard deviation implied by a 95% interval for a mean over `units` units."""
    return (high - low) / (2 * Z_95_TWO_SIDED) * math.sqrt(units)


def units_for_half_width(sd, half_width):
    return math.ceil((Z_95_TWO_SIDED * sd / half_width) ** 2)


def units_for_power(sd, difference):
    return math.ceil(((Z_95_TWO_SIDED + Z_80_POWER) * sd / difference) ** 2)


def half_width_at(sd, units):
    return Z_95_TWO_SIDED * sd / math.sqrt(units)


def line_counts(pattern_root, pattern):
    return [sum(1 for _ in path.open(errors="replace")) for path in sorted(pattern_root.glob(pattern))]


def entered_minutes():
    """Participant-entered `minutes_spent` values in the primary raw rating files, by packet."""
    packets = {"warm_up": "__warmup_", "current_main": "__native_main_", "historical_main": "__setN_"}
    found = {name: {"values": [], "raters": set()} for name in packets}
    for path in sorted((COLLECTION / "ratings").glob("*.csv")):
        packet = next((name for name, marker in packets.items() if marker in path.name), None)
        if packet is None:
            continue
        with path.open(newline="") as handle:
            for row in csv.DictReader(handle):
                try:
                    minutes = float((row.get("minutes_spent") or "").strip())
                except ValueError:
                    continue  # blank, N/A or free text: never estimated here
                found[packet]["values"].append(minutes)
                found[packet]["raters"].add(row.get("rater_id", ""))
    summary = {}
    for name, data in found.items():
        values = data["values"]
        summary[name] = {
            "entries": len(values),
            "raters_with_entries": len(data["raters"]),
            "median_minutes": statistics.median(values) if values else None,
            "mean_minutes": statistics.mean(values) if values else None,
            "min_minutes": min(values) if values else None,
            "max_minutes": max(values) if values else None,
        }
    return summary


def compute():
    curve = json.loads(LEARNING_CURVE.read_text())
    mixture = json.loads(MIXTURE_TEST.read_text())
    tasks = curve["n_tasks"]
    test_families = mixture["counts"]["test"]["families"]

    paired_by_training_size = curve["paired_ce_minus_corr"]
    at_20 = paired_by_training_size["20"]
    loss_trained = curve["curve_tasks"]["rps"]["ce_mixture"]
    refit = mixture["paired_method4_minus_method2"]["rps"]
    fixed = mixture["paired_fixed_intervals"]["rps"]

    paired_sd = {
        "averaged_forecasts_25_tasks": {
            "source": relative(LEARNING_CURVE),
            "what": "proper-loss mixture minus Pearson mixture, 20 training tasks; each held-out forecast averaged over the splits that tested it",
            "point": at_20["point"], "interval_95": at_20["ci95"], "resampled_units": tasks, "unit": "task",
            "implied_sd": implied_sd(*at_20["ci95"], tasks),
        },
        "one_fit_fixed_about_9_test_families": {
            "source": relative(MIXTURE_TEST),
            "what": "RPS-trained mixture minus Pearson mixture on the original test split, fitted judges held fixed",
            "point": refit["estimate"], "interval_95": [fixed["low"], fixed["high"]],
            "resampled_units": test_families, "unit": "task family",
            "implied_sd": implied_sd(fixed["low"], fixed["high"], test_families),
        },
        "refit_and_reselect_about_9_test_families": {
            "source": relative(MIXTURE_TEST),
            "what": "same contrast, refitting and reselecting both judges inside every resample; skewed interval, rough",
            "point": refit["estimate"], "interval_95": [refit["low"], refit["high"]],
            "resampled_units": test_families, "unit": "task family",
            "implied_sd": implied_sd(refit["low"], refit["high"], test_families),
        },
    }
    observed_differences = {f"observed_gap_at_{n}_training_tasks": abs(paired_by_training_size[n]["point"]) for n in ("4", "12", "20")}
    for case in paired_sd.values():
        sd = case["implied_sd"]
        case["units_for_half_width"] = {f"{w:g}": units_for_half_width(sd, w) for w in HALF_WIDTH_TARGETS}
        case["half_width_at_units"] = {str(n): half_width_at(sd, n) for n in EVALUATION_SIZES}
        case["units_for_80_percent_power"] = {name: units_for_power(sd, d) for name, d in observed_differences.items()}

    level_20 = loss_trained["20"]
    level_sd = implied_sd(*level_20["ci95"], tasks)
    one_judge_level = {
        "source": relative(LEARNING_CURVE),
        "what": "held-out RPS of the proper-loss mixture at 20 training tasks",
        "point": level_20["point"], "interval_95": level_20["ci95"], "resampled_units": tasks, "unit": "task",
        "implied_sd": level_sd,
        "units_for_half_width": {f"{w:g}": units_for_half_width(level_sd, w) for w in HALF_WIDTH_TARGETS},
        "half_width_at_units": {str(n): half_width_at(level_sd, n) for n in EVALUATION_SIZES},
    }

    reference = loss_trained["20"]["point"]
    learning_curve = {
        "source": relative(LEARNING_CURVE),
        "what": "held-out RPS of the proper-loss mixture minus its value at 20 training tasks",
        "excess_over_20_tasks": {n: loss_trained[n]["point"] - reference for n in sorted(loss_trained, key=int)},
        "one_rating_per_file_instead_of_all": curve["drop_4_to_20"]["ce_mixture, ratings 1 to all"]["point"],
        "two_ratings_per_file_instead_of_all": curve["drop_4_to_20"]["ce_mixture, ratings 2 to all"]["point"],
    }

    with (MAIN_TASK / "ratings.csv").open(newline="") as handle:
        form_rows = list(csv.DictReader(handle))
    per_task = {}
    for row in form_rows:
        per_task[row["task_folder"]] = per_task.get(row["task_folder"], 0) + 1
    files, packet_tasks = len(form_rows), len(per_task)
    files_per_task = files / packet_tasks
    packet = {
        "source": relative(MAIN_TASK / "ratings.csv"),
        "files": files, "tasks": packet_tasks, "files_per_task": files_per_task,
        "tasks_by_file_count": {str(k): sum(1 for v in per_task.values() if v == k) for k in sorted(set(per_task.values()))},
        "ratings_per_file_target": RATINGS_PER_FILE, "independent_rating_target": files * RATINGS_PER_FILE,
    }

    minutes = entered_minutes()
    warm_up_lines = line_counts(COLLECTION / "rating_task_packet", "warm_up_*/agent_lean/*.lean")
    main_lines = line_counts(MAIN_TASK, "task_*/agent_lean/*.lean")
    length_ratio = statistics.median(main_lines) / statistics.median(warm_up_lines)
    warm_up_median = minutes["warm_up"]["median_minutes"]
    review_time = {
        "source": relative(COLLECTION / "ratings"),
        "entered_minutes": minutes,
        "warm_up_candidate_files": len(warm_up_lines), "warm_up_median_lines": statistics.median(warm_up_lines),
        "main_candidate_files": len(main_lines), "main_median_lines": statistics.median(main_lines),
        "main_to_warm_up_median_length_ratio": length_ratio,
        "assumed_minutes_if_time_scaled_with_length": None if warm_up_median is None else warm_up_median * length_ratio,
    }
    minute_cases = {"measured_warm_up_median": warm_up_median,
                    "assumed_length_scaled": review_time["assumed_minutes_if_time_scaled_with_length"]}
    if minutes["current_main"]["median_minutes"] is not None:
        minute_cases["measured_current_main_median"] = minutes["current_main"]["median_minutes"]

    development_tasks = DEVELOPMENT_TRAINING_TASKS + DEVELOPMENT_VALIDATION_TASKS
    middle = paired_sd["averaged_forecasts_25_tasks"]["units_for_half_width"]
    plans = {
        "finish_current_packet": {"new_development_tasks": 0, "new_evaluation_tasks": 0},
        "add_development_pool": {"new_development_tasks": development_tasks, "new_evaluation_tasks": 0},
        "add_development_pool_and_reach_half_width_0.01": {
            "new_development_tasks": development_tasks, "new_evaluation_tasks": max(0, middle["0.01"] - packet_tasks)},
        "add_development_pool_and_reach_half_width_0.005": {
            "new_development_tasks": development_tasks, "new_evaluation_tasks": max(0, middle["0.005"] - packet_tasks)},
    }
    scenarios = {}
    for name, plan in plans.items():
        new_tasks = plan["new_development_tasks"] + plan["new_evaluation_tasks"]
        new_ratings = math.ceil(new_tasks * files_per_task) * RATINGS_PER_FILE
        total = packet["independent_rating_target"] + new_ratings
        scenarios[name] = {
            **plan,
            "evaluation_tasks": packet_tasks + plan["new_evaluation_tasks"],
            "new_ratings_at_measured_files_per_task": new_ratings,
            "total_independent_ratings": total,
            "hours": {case: None if value is None else total * value / 60 for case, value in minute_cases.items()},
            "ratings_per_person": {str(h): math.ceil(total / h) for h in RATER_POOL_SIZES},
        }

    return json.loads(json.dumps({
        "description": "Planning arithmetic for experiment 15; not a measurement of any future study and not an adopted allocation.",
        "constants": {"z_95_two_sided": Z_95_TWO_SIDED, "z_80_power": Z_80_POWER,
                      "development_training_tasks": DEVELOPMENT_TRAINING_TASKS,
                      "development_validation_tasks": DEVELOPMENT_VALIDATION_TASKS},
        "paired_rps_contrast_sd": paired_sd,
        "observed_absolute_differences": observed_differences,
        "one_judge_rps_level": one_judge_level,
        "learning_curve": learning_curve,
        "current_packet": packet,
        "review_time": review_time,
        "scenarios": scenarios,
    }), parse_float=lambda text: round(float(text), 6))


def tables(result):
    lines = ["| Variability evidence | Implied SD | Units for ±0.02 | ±0.01 | ±0.005 | Half-width at 25 units |", "| --- | ---: | ---: | ---: | ---: | ---: |"]
    for name, case in result["paired_rps_contrast_sd"].items():
        need = case["units_for_half_width"]
        lines.append(f"| {name} | {case['implied_sd']:.4f} | {need['0.02']} | {need['0.01']} | {need['0.005']} | ±{case['half_width_at_units']['25']:.4f} |")
    lines += ["", "| Variability evidence | " + " | ".join(result["observed_absolute_differences"]) + " |", "| --- | ---: | ---: | ---: |"]
    for name, case in result["paired_rps_contrast_sd"].items():
        lines.append(f"| {name} | " + " | ".join(str(v) for v in case["units_for_80_percent_power"].values()) + " |")
    lines += ["", "| Scenario | Evaluation tasks | Total ratings | Hours | Ratings per person (4 / 8 / 12 people) |", "| --- | ---: | ---: | --- | --- |"]
    for name, scenario in result["scenarios"].items():
        hours = "; ".join(f"{case}: {'unmeasured' if value is None else format(value, '.1f')}" for case, value in scenario["hours"].items())
        people = " / ".join(str(v) for v in scenario["ratings_per_person"].values())
        lines.append(f"| {name} | {scenario['evaluation_tasks']} | {scenario['total_independent_ratings']} | {hours} | {people} |")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--write", action="store_true", help="regenerate the saved result")
    parser.add_argument("--tables", action="store_true", help="print Markdown tables")
    arguments = parser.parse_args()
    result = compute()
    if arguments.tables:
        print(tables(result))
    if arguments.write:
        OUTPUT.parent.mkdir(exist_ok=True)
        OUTPUT.write_text(json.dumps(result, indent=2) + "\n")
        print(f"Wrote {relative(OUTPUT)}")
    elif not arguments.tables:
        saved = json.loads(OUTPUT.read_text())
        if saved != result:
            sys.exit(f"{relative(OUTPUT)} is stale: rerun {relative(Path(__file__))} --write and update the quoted tables.")
        print("Costed allocation matches its inputs.")


if __name__ == "__main__":
    main()

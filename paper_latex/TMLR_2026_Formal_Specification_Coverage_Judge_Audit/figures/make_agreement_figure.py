#!/usr/bin/env python3
"""TLDR: Draw Figure 1 (Pearson and Spearman correlations with 95% task-bootstrap intervals across audit views) from the archived aggregate JSON; no per-item data."""
from __future__ import annotations

import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE = ROOT / "experiments/archive/19_audit_gpt_5_3_codex_rubric_judge_on_75_rated_outputs_start_12Nov2026_end_12Nov2026/POSTHOC_CLI_RUBRIC_JUDGE_AGREEMENT_11-12-2026.json"
OUTPUT = HERE / "agreement_intervals.pdf"
# Categorical slots 1 and 2 of the validated default palette (light mode); markers differ as a second encoding.
SERIES = (("pearson_r", "Pearson $r$", "#2a78d6", "o"), ("spearman_rho", "Spearman $\\rho$", "#eb6834", "s"))
INK, MUTED, GRID = "#0b0b0b", "#52514e", "#e4e3df"


def main() -> None:
    data = json.loads(SOURCE.read_text())
    subsets = data["reference_subsets_raw"]
    rows = [
        ("All artifacts (75 artifacts, 25 tasks)", data["item_level"]["raw"]),
        ("Task means (25 tasks)", data["raw_task_means"]),
        ("Within task, centered (75 artifacts)", data["raw_within_task_centered"]),
        ("Judge read the raters' reference statements (51, 17)", subsets["judge_reference_statements_match_rating_era"]),
        ("Judge read different reference statements (24, 8)", subsets["judge_reference_statements_differ_from_rating_era"]),
        ("Isotonic remapping, out of fold (75, 25)", data["item_level"]["isotonic_two_fold_task_split"]),
    ]
    plt.rcParams.update({"font.size": 8.5, "pdf.fonttype": 42, "ps.fonttype": 42, "axes.edgecolor": MUTED, "axes.labelcolor": INK, "xtick.color": MUTED, "ytick.color": INK})
    fig, ax = plt.subplots(figsize=(6.4, 2.9))
    offsets = {"pearson_r": -0.14, "spearman_rho": 0.14}
    for key, label, color, marker in SERIES:
        for position, (_, stats) in enumerate(rows):
            point = stats[key]
            y = position + offsets[key]
            ax.plot([point["lo"], point["hi"]], [y, y], color=color, linewidth=2.0, solid_capstyle="round", zorder=2)
            ax.plot(point["value"], y, marker=marker, markersize=6.5, color=color, markeredgecolor="white", markeredgewidth=1.2, linestyle="none", zorder=3, label=label if position == 0 else None)
    ax.axvline(0.0, color=MUTED, linewidth=0.8, zorder=1)
    ax.set_yticks(range(len(rows)))
    ax.set_yticklabels([name for name, _ in rows])
    ax.invert_yaxis()
    ax.set_xlim(-0.4, 1.0)
    ax.set_xlabel("Correlation with the pooled human rating")
    ax.grid(axis="x", color=GRID, linewidth=0.6, zorder=0)
    ax.tick_params(axis="y", length=0)
    for side in ("top", "right", "left"):
        ax.spines[side].set_visible(False)
    ax.legend(loc="lower right", bbox_to_anchor=(1.0, 1.0), frameon=False, ncol=2, handletextpad=0.3, columnspacing=1.2, borderaxespad=0.1)
    fig.tight_layout(pad=0.3)
    fig.savefig(OUTPUT, metadata={"CreationDate": None, "ModDate": None, "Creator": None, "Producer": None})
    print(f"Wrote {OUTPUT}")


if __name__ == "__main__":
    main()

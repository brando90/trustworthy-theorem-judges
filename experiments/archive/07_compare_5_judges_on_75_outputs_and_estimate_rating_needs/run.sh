#!/usr/bin/env bash
# Reproduce experiment 07 on CPU: zero model calls, no paid API.
# Needs: a checkout of brando90/veribench at be287d9bb2f7bd35ba6db1b8735c9ba10d00eade (VERIBENCH_SRC), python3 with numpy and scipy.
# Per-item ratings and scores stay in the ignored private/ dir; only aggregate JSON/markdown is committed.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../../.." && pwd)"
PY="${PY:-python3}"
PRIVATE="${PRIVATE:-$REPO/private/exp07}"
JUDGE_OBJECTIVES_REPO="${JUDGE_OBJECTIVES_REPO:-$REPO/../judges-dont-need-psychometrics-or-corr}"
IMPORTER="$JUDGE_OBJECTIVES_REPO/experiments/03_exp06_ce_vs_pearson_matched_budget/historical_exp06/scripts/import_cached.py"
: "${VERIBENCH_SRC:?set VERIBENCH_SRC to a veribench checkout at be287d9b}"
mkdir -p "$HERE/logs" "$HERE/results" "$PRIVATE"
{
  if [ ! -f "$PRIVATE/dataset.json" ]; then
    if [ ! -f "$IMPORTER" ]; then
      printf '%s\n' "Missing canonical importer: $IMPORTER. Set JUDGE_OBJECTIVES_REPO to the position-paper checkout." >&2
      exit 1
    fi
    "$PY" "$IMPORTER" --source "$VERIBENCH_SRC" --private "$PRIVATE" --audit "$HERE/results/import_audit.json"
  fi
  "$PY" "$HERE/scripts/exp1_metrics.py" --private "$PRIVATE" --out "$HERE/results/metrics.json"
  "$PY" "$HERE/scripts/exp1_scaling.py" --private "$PRIVATE" --out "$HERE/results/scaling.json"
  "$PY" "$HERE/scripts/write_results.py" --metrics "$HERE/results/metrics.json" --scaling "$HERE/results/scaling.json" --out "$HERE/results.md"
} 2>&1 | tee "$HERE/logs/run_$(date +%Y%m%d_%H%M%S).log"

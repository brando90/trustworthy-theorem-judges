#!/usr/bin/env bash
# Reproduce experiment 07 on CPU: zero model calls, no paid API.
# Needs: a checkout of brando90/veribench at be287d9bb2f7bd35ba6db1b8735c9ba10d00eade (VERIBENCH_SRC), python3 with numpy and scipy.
# Per-item ratings and scores stay in the ignored private/ dir; only aggregate JSON/markdown is committed.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
PY="${PY:-python3}"
PRIVATE="${PRIVATE:-$REPO/private/exp07}"
: "${VERIBENCH_SRC:?set VERIBENCH_SRC to a veribench checkout at be287d9b}"
mkdir -p "$HERE/logs" "$HERE/results" "$PRIVATE"
{
  [ -f "$PRIVATE/dataset.json" ] || "$PY" "$REPO/experiments/archive/06_information_loss_vs_correlation_judge_selection/scripts/import_cached.py" \
      --source "$VERIBENCH_SRC" --private "$PRIVATE" --audit "$HERE/results/import_audit.json"
  "$PY" "$HERE/scripts/exp1_metrics.py" --private "$PRIVATE" --out "$HERE/results/metrics.json"
  "$PY" "$HERE/scripts/exp1_scaling.py" --private "$PRIVATE" --out "$HERE/results/scaling.json"
  "$PY" "$HERE/scripts/write_results.py" --metrics "$HERE/results/metrics.json" --scaling "$HERE/results/scaling.json" --out "$HERE/results.md"
} 2>&1 | tee "$HERE/logs/run_$(date +%Y%m%d_%H%M%S).log"

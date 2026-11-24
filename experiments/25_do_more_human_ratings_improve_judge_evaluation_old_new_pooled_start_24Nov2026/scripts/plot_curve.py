#!/usr/bin/env python3
"""Exp 25 (dated 11-24-2026): learning-curve figure from results/aggregates.json. Usage: python3 plot_curve.py results/aggregates.json results/learning_curve.png"""
import json, sys
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
r = json.load(open(sys.argv[1]))["learning_curve"]
fig, ax = plt.subplots(1, 2, figsize=(11, 4))
for name, c in (("old (25 tasks)", "old"), ("new (25 tasks)", "new"), ("pooled (50 tasks)", "pooled")):
    ks = sorted(map(int, r[c]))
    ax[0].plot(ks, [r[c][str(k)]["RPS"]["mean_ci_width"] for k in ks], "o-", label=name)
    ax[1].plot(ks, [r[c][str(k)]["RPS"]["sd_of_estimate"] for k in ks], "o-", label=name)
ax[0].set_title("Mean 95% interval width of RPS vs tasks"); ax[1].set_title("SD of RPS estimate across k-task subsets")
for a in ax:
    a.set_xlabel("number of tasks k"); a.grid(True); a.legend()
ax[0].set_ylabel("width"); ax[1].set_ylabel("SD")
fig.suptitle("GPT-6 Astra judge, H2 prompt; 40 random subsets per k, 200 bootstrap draws each (SD is 0 at the full set by construction)")
fig.tight_layout(); fig.savefig(sys.argv[2], dpi=130)

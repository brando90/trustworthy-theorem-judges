"""Figure 1 of the ICML 2027 draft: per-artifact mean judge score vs mean human rating, old and new sets (11-24-2026).

Reads the dated anonymised copies in experiments/27_*/data_11-24-2026/. Prints the offsets and Spearman it plots so they can be checked
against experiments/25_*/RESULTS.md. Usage: python3 fig_scatter.py <repo_root> <out_png>
"""
import sys, glob, csv, collections
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy.stats import spearmanr

root, out = sys.argv[1], sys.argv[2]
d = glob.glob(f"{root}/experiments/27_*/data_11-24-2026")[0]
hum = {}
for f in ("old", "new"):
    for r in csv.DictReader(open(f"{d}/human_ratings_{f}_11-24-2026.csv")):
        hum[r["item"]] = (f, np.mean([int(x) for x in r["ratings_sorted_0to5_rater_identity_removed"].split()]))
js = collections.defaultdict(list)
for r in csv.DictReader(open(f"{d}/judge_scores_h2_11-24-2026.csv")):
    js[(r["judge"], r["item"])].append(int(r["score_0to5"]))
judges = sorted({k[0] for k in js})
print("judges in file:", judges)
want = [("H2_astra", "GPT-6 Astra"), ("H2_opus", "Claude Opus 5.5")]
fig, axs = plt.subplots(1, 2, figsize=(7.0, 3.1), sharex=True, sharey=True)
col = {"old": "#1f77b4", "new": "#ff7f0e"}
for ax, (jn, label) in zip(axs, want):
    for s in ("old", "new"):
        items = [i for i, (f, _) in hum.items() if f == s and (jn, i) in js]
        x = np.array([hum[i][1] for i in items]); y = np.array([np.mean(js[(jn, i)]) for i in items])
        rho = spearmanr(x, y)[0]
        print(f"{jn} {s}: n={len(items)} mean judge-mean human = {np.mean(y - x):+.3f} spearman={rho:.2f}")
        ax.scatter(x + np.random.default_rng(0).uniform(-.04, .04, len(x)), y, s=14, alpha=.7, color=col[s],
                   label=f"{s} set: mean offset {np.mean(y - x):+.2f}")
    ax.plot([0, 5], [0, 5], color="k", lw=1, ls="--")
    ax.set_title(label, fontsize=9); ax.set_xlabel("mean human rating"); ax.grid(True); ax.legend(fontsize=7, loc="lower right")
axs[0].set_ylabel("mean judge score (3 calls)")
ax.set_xlim(-0.1, 5.1); ax.set_ylim(-0.1, 5.1)
fig.tight_layout(); fig.savefig(out, dpi=200)

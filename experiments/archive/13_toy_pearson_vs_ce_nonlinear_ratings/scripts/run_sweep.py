"""Run the toy sweep: scenarios A/B x n train tasks x seeds; writes results/raw.jsonl and results/population.json."""
import sys, json, time, os
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np
from multiprocessing import Pool
import toy

NS = [4, 8, 16, 20, 32, 64, 128, 256, 512, 1024, 2048]
SEEDS = int(sys.argv[1]) if len(sys.argv) > 1 else 150
K, NTEST = 3, 500
out = os.path.join(os.path.dirname(__file__), '..', 'results')

if __name__ == '__main__':
    t = time.time()
    pop = {sc: {k: {a: float(b) for a, b in toy.population_limit(sc, k).items()} for k in toy.FITS} for sc in 'AB'}
    json.dump(pop, open(f'{out}/population.json', 'w'), indent=1)
    jobs = [(sc, n, s, K, NTEST) for n in NS[::-1] for sc in 'AB' for s in range(SEEDS)]
    with Pool(4) as p, open(f'{out}/raw.jsonl', 'w') as f:
        for i, (sc, n, s, o) in enumerate(p.imap_unordered(toy.run_one, jobs, chunksize=4)):
            f.write(json.dumps(dict(scenario=sc, n=n, seed=s, **{k: {a: float(b) for a, b in v.items()} for k, v in o.items()})) + '\n')
            if i % 200 == 0: print(i, len(jobs), round(time.time() - t), flush=True)
    print('done', round(time.time() - t), 's')

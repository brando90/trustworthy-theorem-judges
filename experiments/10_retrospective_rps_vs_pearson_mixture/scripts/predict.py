"""Apply saved mixture parameters to externally supplied historical-format ratings."""
import argparse
import hashlib
import json
from pathlib import Path

import numpy as np

from models import histogram, smooth, predict


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--model',required=True)
    ap.add_argument('--ratings',required=True)
    ap.add_argument('--method',default='validation_selected')
    ap.add_argument('--out',required=True)
    args=ap.parse_args()
    model_path=Path(args.model); model=json.loads(model_path.read_text())
    rows=json.loads(Path(args.ratings).read_text())
    assert isinstance(rows,list) and rows
    assert len({r['artifact_id'] for r in rows})==len(rows)
    q=[]
    for row in rows:
        assert set(row)=={'artifact_id','ratings'}
        assert set(row['ratings'])==set(model['candidate_order'])
        assert all(len(row['ratings'][n])==3 for n in model['candidate_order'])
        q.append([smooth(histogram(row['ratings'][name]),model['epsilon']) for name in model['candidate_order']])
    result=predict(np.array(q),model['models'][args.method])
    digest=hashlib.sha256(model_path.read_bytes()).hexdigest()
    payload={'model_sha256':digest,'method':args.method,'forecasts':[
        {'artifact_id':row['artifact_id'],'probabilities':prob.tolist(),
         'expected_normalized_rating':float(prob @ (np.arange(6)/5))}
        for row,prob in zip(rows,result)]}
    with Path(args.out).open('x') as f: json.dump(payload,f,indent=2,allow_nan=False)


if __name__=='__main__': main()

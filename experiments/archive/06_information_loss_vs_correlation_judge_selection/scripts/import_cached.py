#!/usr/bin/env python3
"""TLDR: Import immutable historical ratings and receipts privately; publish aggregate audit only."""
import argparse, collections, hashlib, json, subprocess
from pathlib import Path

REV = 'be287d9bb2f7bd35ba6db1b8735c9ba10d00eade'
BASE = 'experiments/100_karpathy_recipe_tc_judge_search_human_train_val_test/'
RUNS = {
    'H0_sol': ['w1_H0_sol_high', 'ab_H0_sol'],
    'H0_opus': ['w1_H0_opus55_max', 'ab_H0_opus'],
    'H1_sol': ['p3_i1_H1_sol_high', 'ab_H1_sol'],
    'H2_sol': ['p3_i2_H2_sol_high', 'p4_val_H2_sol_high', 'p5_test_H2_sol_high'],
    'H2_opus': ['p3_i3_H2_opus55_max', 'p4_val_H2_opus55_max', 'p5_test_H2_opus55_max'],
}

def family(task):
    if task in ['0_bisect_right','1_bisect_left','binary_search']: return 'binary_search_family'
    if task in ['bubble_sort','insertion_sort','merge_sort','selection_sort']: return 'sorting_family'
    if task in ['2_heappush','3_heappop']: return 'heap_family'
    return task

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--source',required=True);ap.add_argument('--private',required=True);ap.add_argument('--audit',required=True);a=ap.parse_args()
    private=Path(a.private);private.mkdir(parents=True,exist_ok=True)
    assert not (private/'dataset.json').exists(), 'Do not overwrite an imported dataset'
    hashes={}
    def blob(path):
        b=subprocess.check_output(['git','show',REV+':'+path],cwd=a.source)
        hashes[path]=hashlib.sha256(b).hexdigest()
        out=private/'source'/path;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(b)
        return b
    raw=blob(BASE+'inputs/items.jsonl');items=[json.loads(l) for l in raw.splitlines() if l.strip()]
    items=sorted(items,key=lambda x:x['item']);assert len(items)==75 and len({i['item'] for i in items})==75
    rows=[]
    for i in items:
        ratings=[i[k] for k in ('p1','p2','p3') if i[k] is not None]
        assert len(ratings) in (2,3) and all(isinstance(r,(int,float)) and r==int(r) and 0<=r<=5 for r in ratings)
        ratings=[int(r) for r in ratings]
        rows.append({'item':i['item'],'task':i['task'],'family':family(i['task']),'split':i['split'],'ratings':ratings,
                     'ordinary':not i['ref_placeholder_at_annotation'],'ambiguous':i['ref_ambiguous_in_window'],
                     'candidate_matches_annotation':i['candidate_matches_annotation_rev'],
                     'ratings_by_expert':[i[k] for k in ('p1','p2','p3')]})
    outputs={};models={};audit_counts={};traces=[]
    for name,runs in RUNS.items():
        cells={};configs=[];status=collections.Counter()
        for run in runs:
            prefix=BASE+'runs/'+run+'/'
            m=json.loads(blob(prefix+'manifest.json'));assert m['items_sha256']==hashlib.sha256(raw).hexdigest()
            configs.append(m['config']);manifest={c['cell']:c for c in m['cells'] if c['kind']=='main'}
            paths=subprocess.check_output(['git','ls-tree','-r','--name-only',REV,'--',prefix+'receipts/'],cwd=a.source,text=True).splitlines()
            observed=set()
            for path in paths:
                r=json.loads(blob(path))
                if r['kind']!='main':continue
                observed.add(r['cell']);status[r['status']]+=1
                assert r['cell'] in manifest and r['prompt_sha256']==manifest[r['cell']]['prompt_sha256']
                assert r['status']=='COMPLETE' and isinstance(r['score_raw'],int) and 0<=r['score_raw']<=5
                assert abs(r['score']-r['score_raw']/5)<1e-12
                key=(r['item'],r['repeat']);assert key not in cells
                assert r['task']==next(i['task'] for i in rows if i['item']==r['item'])
                cells[key]=r['score_raw']
                if len(traces)<3:traces.append({'candidate':name,'receipt':path,'receipt_sha256':hashes[path],'prompt_sha256':r['prompt_sha256'],'item':r['item']})
            assert observed==set(manifest)
        assert len(cells)==225
        outputs[name]=[[cells[(i['item'],r)] for r in (1,2,3)] for i in rows]
        models[name]=configs;audit_counts[name]=dict(status)
    dataset={'source_commit':REV,'rows':rows,'outputs':outputs,'models':models}
    encoded=(json.dumps(dataset,sort_keys=True,indent=2)+'\n').encode();(private/'dataset.json').write_bytes(encoded)
    (private/'source_hashes.json').write_text(json.dumps(hashes,sort_keys=True,indent=2)+'\n')
    (private/'traces.json').write_text(json.dumps(traces,indent=2)+'\n')
    audit={'source_commit':REV,'dataset_sha256':hashlib.sha256(encoded).hexdigest(),'source_manifest_sha256':hashlib.sha256((private/'source_hashes.json').read_bytes()).hexdigest(),
           'artifacts':len(rows),'tasks':len({r['task'] for r in rows}),'families':len({r['family'] for r in rows}),'expert_ratings':sum(len(r['ratings']) for r in rows),
           'ordinary_artifacts':sum(r['ordinary'] for r in rows),'ambiguous_reference_artifacts':sum(r['ambiguous'] for r in rows),
           'candidate_annotation_matches':dict(collections.Counter(str(r['candidate_matches_annotation']) for r in rows)),
           'statuses':audit_counts,'models':models,'receipt_manifest_prompt_checks':1125,'manifest_input_hash_checks':12,
           'input_audit_limit':'Manifest input hash and receipt prompt hashes bound; original rater-time byte delivery cannot be independently reconstructed here. Historical reference ambiguity flags retained.',
           'native_probabilities':False,'new_inference_calls':0,'source_files_preserved':len(hashes)}
    out=Path(a.audit);out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(audit,indent=2)+'\n')
    print(json.dumps({k:audit[k] for k in ('artifacts','tasks','families','expert_ratings','ordinary_artifacts','ambiguous_reference_artifacts','source_files_preserved')}))

if __name__=='__main__': main()

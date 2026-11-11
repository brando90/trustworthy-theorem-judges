"""Parse raw open-weight judge outputs into dataset_pool.json (same schema as the exp 11/12 dataset, extra judges appended).
Usage: python3 assemble.py --raw out_dir --base ../AT-2924/dataset.json --out dataset_pool.json"""
import json, glob, os, sys, argparse, collections
ap=argparse.ArgumentParser(); ap.add_argument('--raw'); ap.add_argument('--base'); ap.add_argument('--out'); ap.add_argument('--maxmiss',type=int,default=3)
a=ap.parse_args()
def objs(text):
    out,start,depth,in_str,esc=[],None,0,False,False
    for i,ch in enumerate(text):
        if in_str:
            if esc: esc=False
            elif ch=='\\': esc=True
            elif ch=='"': in_str=False
            continue
        if ch=='"': in_str=True
        elif ch=='{':
            start=i if depth==0 else start; depth+=1
        elif ch=='}' and depth:
            depth-=1
            if depth==0 and start is not None:
                try:
                    o=json.loads(text[start:i+1]); 
                    if isinstance(o,dict): out.append(o)
                except Exception: pass
                start=None
    return out
def parse(text):
    found=[]
    for o in objs(text):
        v=o.get('final_score_0_5')
        if isinstance(v,bool) or not isinstance(v,(int,float)): continue
        if float(v).is_integer() and 0<=v<=5: found.append(int(v))
    if not found or len(set(found))!=1: return None
    return found[0]
base=json.load(open(a.base)); items=[r['item'] for r in base['rows']]
d=dict(base); d['outputs']=dict(base['outputs']); d['candidate_order']=list(base['candidate_order']); stats={}
for f in sorted(glob.glob(a.raw+'/*.jsonl')):
    key=os.path.basename(f)[:-6]
    if not os.path.exists(f+'.done'): continue
    R=collections.defaultdict(dict); err=collections.Counter(); valid=[]
    for l in open(f):
        r=json.loads(l)
        if 'error' in r: err[r['prompt']]+=1; continue
        sc=[s for s in (parse(t) for t in r['texts']) if s is not None]
        valid.append(len(sc)/len(r['texts'])); R[r['prompt']][r['item']]=sc[:3]
    for pr in ('H0','H1','H2'):
        miss=[i for i in items if len(R[pr].get(i,[]))<1]; short=sum(1 for i in items if 0<len(R[pr].get(i,[]))<3)
        name=f'{key}_{pr}'; stats[name]={'missing_items':len(miss),'items_with_<3_valid':short,'errors':err[pr]}
        if len(miss)>a.maxmiss: stats[name]['dropped']=True; continue
        # fill an item with no valid sample by the judge's own mean rating (counted in stats)
        allv=[s for i in items for s in R[pr].get(i,[])]; fill=int(round(sum(allv)/len(allv)))
        d['outputs'][name]=[R[pr].get(i) or [fill] for i in items]; d['candidate_order'].append(name)
json.dump(d,open(a.out,'w')); json.dump(stats,open(a.out.replace('.json','_stats.json'),'w'),indent=1)
print(len(d['candidate_order']),'judges'); print(json.dumps(stats))

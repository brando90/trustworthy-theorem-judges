import sys, json
V='/var/lib/agent/scratch/AT-2807/veribench/experiments/100_karpathy_recipe_tc_judge_search_human_train_val_test'
sys.path.insert(0,V+'/scripts')
import prompts, common
items=common.load_items()
R={'H0':'H0_human_mirror','H1':'H1_human_mirror_rater_conventions','H2':'H2_human_mirror_conventions_demos'}
out=open('prompts.jsonl','w'); import statistics
L=[]
for k,rub in R.items():
    for it in items:
        cand=common.read_text(it['candidate_path'])
        s,u=prompts.render(rub,it,cand,it['candidate_file'])
        out.write(json.dumps({'item':it['item'],'task':it['task'],'prompt':k,'system':s,'user':u})+'\n')
        L.append((k,len(s)+len(u)))
out.close()
for k in R: 
    v=[n for kk,n in L if kk==k]; print(k,len(v),'chars min/med/max',min(v),int(statistics.median(v)),max(v))

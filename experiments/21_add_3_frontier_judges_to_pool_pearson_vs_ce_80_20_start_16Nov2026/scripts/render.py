import sys,json,os
WORK=os.getcwd()
V='<private VeriBench checkout>/experiments/100_karpathy_recipe_tc_judge_search_human_train_val_test'
sys.path.insert(0,V+'/scripts'); os.chdir(V)
import prompts, common
items=common.load_items('all')
out=[]
for it in items:
    cand=common.read_text(it['candidate_path'])
    s,u=prompts.render('H2_human_mirror_conventions_demos',it,cand,it['candidate_file'])
    out.append({'item':it['item'],'task':it['task'],'split':it['split'],'system':s,'user':u})
os.chdir(WORK)
with open('prompts_h2_75.jsonl','w') as f:
    for o in out: f.write(json.dumps(o)+'\n')
import statistics
L=[len(o['system'])+len(o['user']) for o in out]
print(len(out),min(L),statistics.mean(L),max(L), 'approx tokens mean',statistics.mean(L)/3.5)

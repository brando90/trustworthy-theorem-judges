import json, itertools, math
D='/var/lib/agent/scratch/AT-2931/agent_fixed/'
d=json.load(open(D+'train_only.json'))
J=d['candidate_judges']; names=J+['train_marginal']
def hist(x):
    h=[0.0]*6
    for v in x: h[v]+=1
    return [v/len(x) for v in h]
def fl(h):
    h=[max(v,1e-6) for v in h]; s=sum(h); return [v/s for v in h]
T=d['train']; N=len(T)
P=[hist(a['human_ratings_0to5']) for a in T]
marg=fl(hist([r for a in T for r in a['human_ratings_0to5']]))
# per artifact: list of (p_r, [component q_r for 6 comps]) for p_r>0
items=[]
for i,a in enumerate(T):
    it=[]
    for r in range(6):
        if P[i][r]>0:
            comp=[fl(hist(a['judge_cached_scalar_ratings_0to5'][j]))[r] for j in J]+[marg[r]]
            it.append((P[i][r],comp))
    items.append(it)
def ce(w):
    t=0
    for it in items:
        for p,c in it: t-=p*math.log(sum(a*b for a,b in zip(w,c)))
    return t/N
n=20; res=[]
for c in itertools.product(range(n+1),repeat=5):
    s=sum(c)
    if s<=n:
        w=[x/n for x in c]+[(n-s)/n]; res.append((ce(w),w))
res.sort(key=lambda x:x[0])
oh=sorted((ce([1.0 if i==k else 0.0 for i in range(6)]),names[k]) for k in range(6))
# EM for mixture weights (monotone, convex problem -> global opt)
w=[1/6]*6
for _ in range(20000):
    nw=[0.0]*6
    for it in items:
        for p,c in it:
            m=sum(a*b for a,b in zip(w,c))
            for k in range(6): nw[k]+=p*w[k]*c[k]/m
    nw=[x/N for x in nw]
    if max(abs(a-b) for a,b in zip(nw,w))<1e-10: w=nw;break
    w=nw
print('grid',len(res)); print('onehots',oh)
for c,x in res[:5]: print(round(c,5),x)
print('EM',ce(w),dict(zip(names,[round(x,4) for x in w])))
json.dump({'n_grid':len(res),'w':w,'ce':ce(w),'grid_top':res[:5],'onehots':oh},open(D+'work_ce/result.json','w'))

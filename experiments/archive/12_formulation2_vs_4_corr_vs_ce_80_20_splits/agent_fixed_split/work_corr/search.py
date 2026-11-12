import json, itertools, math
D='/var/lib/agent/scratch/AT-2931/agent_fixed/'
d=json.load(open(D+'train_only.json'))
J=d['candidate_judges']; names=J+['train_marginal']
def hist(x,floor):
    h=[x.count(r)/len(x) for r in range(6)]
    if floor:
        h=[max(v,1e-6) for v in h]; s=sum(h); h=[v/s for v in h]
    return h
tr=d['train']
marg=hist([r for a in tr for r in a['human_ratings_0to5']],True)
ex=lambda h: sum(r/5*h[r] for r in range(6))
E=[];y=[]
for a in tr:
    row=[ex(hist(a['judge_cached_scalar_ratings_0to5'][j],True)) for j in J]+[ex(marg)]
    E.append(row); y.append(sum(a['human_ratings_0to5'])/len(a['human_ratings_0to5'])/5)
def pear(s):
    n=len(s); ms=sum(s)/n; my=sum(y)/n
    vs=sum((v-ms)**2 for v in s); vy=sum((v-my)**2 for v in y)
    if vs<1e-18: return -2
    return sum((a-ms)*(b-my) for a,b in zip(s,y))/math.sqrt(vs*vy)
def corr(w): return pear([sum(wi*ei for wi,ei in zip(w,r)) for r in E])
res=[];N=20
for c in itertools.product(range(N+1),repeat=5):
    if sum(c)<=N:
        w=[v/N for v in c]+[(N-sum(c))/N]
        res.append((corr(w),w))
print(len(res),'candidates')
for k,n in enumerate(names[:5]): print('single',n,round(corr([1.0 if i==k else 0.0 for i in range(6)]),4))
res.sort(key=lambda t:-t[0])
best=res[0][0]
for r,w in res[:8]: print(round(r,5),{n:v for n,v in zip(names,w) if v>0})
tied=[(r,w) for r,w in res if best-r<1e-9]
print('ties',len(tied))
tied.sort(key=lambda t:sum(v>0 for v in t[1]))
r,w=tied[0]
print('chosen',r,w)
json.dump({"weights":dict(zip(names,w)),"train_pearson":r,
 "how_chosen":"Exhaustive grid over the 6-component simplex (step 0.05, 53130 candidates incl. all one-hot) maximizing train Pearson between expected rating and human mean/5; ties broken by fewest nonzero components. No other loss used."},open(D+'spec_corr.json','w'),indent=1)

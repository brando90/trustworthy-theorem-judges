import re, pathlib, json, collections, sys
S = pathlib.Path(sys.argv[1])
idx = collections.defaultdict(list)
for p in pathlib.Path('/Users/brandomiranda/veribench/veribench_dataset/py_src').rglob('*.py'):
    try: s = p.read_text()
    except Exception: continue
    for f in set(re.findall(r'^def\s+(\w+)\s*\(', s, re.M)): idx[f.lower().replace('_', '')].append(str(p))
norm = lambda x: re.sub(r'[^a-z0-9]', '', x.lower())
hit = {}; amb = 0; AMB = []
for d in sorted((S / 'tiny').iterdir()):
    g = (d / 'gold.lean').read_text()
    m = re.search(r"VeriBench\s*[^\w\s]\s*([^\n]+)", g); title = m.group(1) if m else ''
    names = re.findall(r'Implementation of `([^`]+)`', g) + re.findall(r'^def\s+(\w+)', g, re.M)
    c = []
    for n in names:
        c = idx.get(n.split('.')[-1].lower().replace('_', ''), [])
        if c: break
    if len(c) > 1:
        tk = norm(title)
        c = [x for x in c if norm(pathlib.Path(x).stem) and (norm(pathlib.Path(x).stem) in tk or tk in norm(pathlib.Path(x).stem))] or c
        amb += len(c) > 1
        if len(c) > 1: AMB.append(d.name)
    if c: hit[d.name] = c[0]
print(len(hit), "mapped; ambiguous", amb)
json.dump(hit, open(S / 'pymap.json', 'w'), indent=0)

json.dump(AMB, open(S / 'ambiguous.json', 'w'))

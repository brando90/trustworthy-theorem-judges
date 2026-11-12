# TLDR: Parse the `#gold_check` Lean logs of the 840 Lean-accepted Tiny-256 runs (condition 5, every gold name proved), write results/gold_name_check.json and add `all_gold_names_proved` and `counted_all5` to results/per_run.csv.
# usage: python3 gold_name_check.py <log_dir> <exp145_dir> [<exp142_bridges_dir>]
import csv, json, re, sys, os, collections
logd, exp = sys.argv[1], sys.argv[2]
br = sys.argv[3] if len(sys.argv) > 3 else None
LT = '\r\n' if b'\r\n' in open(f'{exp}/results/per_run.csv','rb').read(2000) else '\n'
rows = list(csv.DictReader(open(f'{exp}/results/per_run.csv', newline='')))
orig_cols = list(rows[0].keys())
out = {}
for r in rows:
    if r['lean_entails_raw'] != '1':
        continue
    m = r['mod']; p = f'{logd}/{m}.log'
    res = dict(run=r['run'], solver=r['solver'], task=r['task'], mod=m)
    if not os.path.exists(p):
        res.update(status='no_log', all_gold_names_proved=0, reason='no log'); out[m] = res; continue
    t = open(p).read()
    exit0 = bool(re.search(r'(?m)^exit 0$', t))
    err = bool(re.search(r'(?m)^\S+:\d+:\d+: error', t))
    g = re.findall(r'GCHK (\S+) (\w+)(.*)', t)
    s = re.search(r'GSUMMARY gold=(\d+) proved=(\d+) dup_last_components=(\d+)', t)
    st = collections.defaultdict(list)
    for nm, k, d in g:
        st[k].append(nm if (not d.strip() or k=='OK') else f'{nm} {d.strip()}')
    res.update(compiled_ok=exit0 and not err, gold_total=int(s.group(1)) if s else None,
               proved=int(s.group(2)) if s else None, dup_last_components=int(s.group(3)) if s else None,
               missing=st['MISSING'], nonstd_axioms=st['NONSTD'], not_theorem=st['NOT_THEOREM'],
               private_helpers=st['PRIVATE_HELPER'], structure_fields=st['STRUCTURE_FIELD'], nested_aux=st['NESTED_AUX'], gold_names=[x for k in ('OK','MISSING','NONSTD','NOT_THEOREM') for x in st[k]])
    ok = (res['compiled_ok'] and s is not None and res['gold_total'] > 0 and res['gold_total'] == res['proved']
          and not st['MISSING'] and not st['NONSTD'] and not st['NOT_THEOREM'] and True)
    res['all_gold_names_proved'] = int(ok)
    reasons = []
    if not res['compiled_ok']: reasons.append('bridge did not compile cleanly in the check')
    if s is None: reasons.append('no GSUMMARY')
    elif res['gold_total'] == 0: reasons.append('no gold theorem found')
    if st['MISSING']: reasons.append('missing/renamed/unproved: ' + ', '.join(st['MISSING']))
    if st['NONSTD']: reasons.append('non-standard axioms: ' + ', '.join(st['NONSTD']))
    if st['NOT_THEOREM']: reasons.append('not a theorem: ' + ', '.join(st['NOT_THEOREM']))
    res['reason'] = '; '.join(reasons)
    # cross-check with the prover's own claim (experiment 142 bridge json): reading, not Lean
    if br and os.path.exists(f'{br}/Bridge_{m}.json'):
        try:
            j = json.load(open(f'{br}/Bridge_{m}.json'))
            res['prover_k_gold'] = j.get('k_gold'); res['prover_not_proved'] = [x['name'] if isinstance(x, dict) else x for x in j.get('not_proved', [])]
        except Exception:
            res['prover_json'] = 'unreadable'
    out[m] = res
json.dump(out, open(f'{exp}/results/gold_name_check.json', 'w'), indent=1)
for r in rows:
    m = r['mod']
    if r['lean_entails_raw'] == '1':
        r['all_gold_names_proved'] = str(out[m]['all_gold_names_proved'])
        r['counted_all5'] = '1' if (r['lean_entails'] == '1' and out[m]['all_gold_names_proved'] == 1) else '0'
    else:
        r['all_gold_names_proved'] = ''; r['counted_all5'] = '0'
with open(f'{exp}/results/per_run.csv', 'w', newline='') as f:
    w = csv.DictWriter(f, fieldnames=orig_cols + ['all_gold_names_proved', 'counted_all5'], lineterminator=LT); w.writeheader(); w.writerows(rows)
# per-solver before/after
tab = collections.OrderedDict()
for r in rows:
    d = tab.setdefault(r['solver'], dict(runs=0, accepted=0, counted_1to4=0, counted_all5=0, cond5_fail_among_accepted=0, cond5_fail_among_counted=0))
    d['runs'] += 1
    d['accepted'] += r['lean_entails_raw'] == '1'
    d['counted_1to4'] += r['lean_entails'] == '1'
    d['counted_all5'] += r['counted_all5'] == '1'
    d['cond5_fail_among_accepted'] += r['all_gold_names_proved'] == '0'
    d['cond5_fail_among_counted'] += (r['lean_entails'] == '1' and r['all_gold_names_proved'] == '0')
tot = {k: sum(d[k] for d in tab.values()) for k in next(iter(tab.values()))}
json.dump(dict(per_solver=tab, total=tot), open(f'{exp}/results/gold_name_check_summary.json', 'w'), indent=1)
print(json.dumps(dict(per_solver=tab, total=tot), indent=1))

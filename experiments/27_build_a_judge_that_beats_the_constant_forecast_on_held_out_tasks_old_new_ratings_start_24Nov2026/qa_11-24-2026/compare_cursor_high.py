"""Compare Cursor's independent output with the frozen report (11-24-2026).

Run from qa_11-24-2026: python3 compare_cursor_high.py
"""
import json
from pathlib import Path
root=Path(__file__).resolve().parent
r=json.loads((root/'qa_cursor_high.json').read_text())
p=json.loads((root.parent/'results/test_results_11-24-2026.json').read_text())
mp={'final_Q':'FINAL_judge','constant_per_set':'BASE_constant_per_set','pooled_constant':'BASE_constant_pooled','uniform':'BASE_uniform','h2':'BASE_H2_raw_astra_opus'}
items=[]
for sub,vals in r['task1_forecast_metrics'].items():
 for judge,metrics in vals['forecasts'].items():
  for m in ['rps','ce','tvd']:
   a=metrics[m];b=p['subsets'][sub]['metrics'][mp[judge]][m.upper()]['point']
   items.append(dict(name=f'{sub}/{judge}/{m.upper()}',independent=a,frozen=b,delta=a-b,match_3dp=f'{a:.3f}'==f'{b:.3f}'))
for base in ['constant_per_set','h2']:
 for m,v in r['task2_task_bootstrap'][f'final_Q_minus_{base}'].items():
  ref=p['subsets']['pooled']['paired_differences'][f'DIFF_FINAL_minus_{mp[base]}|{m.upper()}']
  for field,a,b in [('point',v['estimate'],ref['point']),('ci_low',v['ci95'][0],ref['ci95'][0]),('ci_high',v['ci95'][1],ref['ci95'][1])]:
   items.append(dict(name=f'paired/{base}/{m.upper()}/{field}',independent=a,frozen=b,delta=a-b,match_3dp=f'{a:.3f}'==f'{b:.3f}'))
out=dict(compared=len(items),matched_3dp=sum(v['match_3dp'] for v in items),max_absolute_difference=max(abs(v['delta']) for v in items),comparisons=items)
(root/'cursor_high_comparison.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='comparisons'},indent=2))
assert out['matched_3dp']==out['compared']==63

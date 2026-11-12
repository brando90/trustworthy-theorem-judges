"""Reconcile frozen sheet snapshots without adding duplicate observations."""
import csv
import hashlib
import io
import json
import re
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
PREP = HERE.parents[1]
CANONICAL = PREP.parent / 'legacy_veribench/human_round/private_ratings_setN'
NAMES = {'T01': 'Rylan Schaeffer', 'T02': 'Yegor Denisov-Blanch',
         'T03': 'Dilara Soylu', 'T04': 'Allen Nie', 'T05': 'Srivatsava Daruru',
         'T06': 'Donald Poindexter Jr', 'T07': 'Simon Obstbaum',
         'V02': 'Nikil Ravi', 'A1': 'Brando Miranda'}
ASSIGNED = {'T01': ['N17', 'N21'], 'T05': ['N01', 'N23']}

def score(value):
    try:
        n = float(value)
        return int(n) if n.is_integer() and 0 <= n <= 5 else None
    except (TypeError, ValueError):
        return None

snapshots = json.loads((HERE / 'sheet_snapshots.json').read_text())
summary = []
for snap in snapshots:
    source = snap['source']
    rid = re.search(r'\b(T\d\d|V\d\d|A1)\b', source['title']).group(0)
    packet = 'warmup' if 'warm-up' in source['title'] else 'setN'
    values = snap['export']['values']
    header = next(i for i, row in enumerate(values) if 'final_score_0_5' in row)
    fields = values[header]
    rows = [dict(zip(fields, row + [''] * (len(fields) - len(row))))
            for row in values[header + 1:] if len(row) > 1 and row[1]]
    assert len(rows) == (6 if packet == 'warmup' else 125)
    ids = [r['item_id'] for r in rows]
    assert len(ids) == len(set(ids))
    assert all(r['rater_id'] == rid for r in rows)
    folder = HERE / f'{packet}_{rid}'
    folder.mkdir(exist_ok=True)
    buf = io.StringIO(newline='')
    writer = csv.DictWriter(buf, fieldnames=fields, lineterminator='\n')
    writer.writeheader()
    writer.writerows(rows)
    (folder / 'ratings.csv').write_text(buf.getvalue())
    prior_path = CANONICAL / f'{packet}_{rid}.csv'
    prior_rows = list(csv.DictReader(prior_path.open())) if prior_path.exists() else []
    prior = {r['item_id']: score(r.get('final_score_0_5')) for r in prior_rows}
    valid = {r['item_id']: score(r.get('final_score_0_5')) for r in rows
             if score(r.get('final_score_0_5')) is not None}
    added = sorted(k for k in valid if prior.get(k) is None)
    revised = sorted(k for k in valid if prior.get(k) is not None and valid[k] != prior[k])
    missing_now = sorted(k for k, v in prior.items() if v is not None and k not in valid)
    na = [r['item_id'] for r in rows if str(r.get('final_score_0_5', '')).strip().lower() in {'n/a', 'na'}]
    invalid = [r['item_id'] for r in rows if str(r.get('final_score_0_5', '')).strip()
               and r['item_id'] not in valid and r['item_id'] not in na]
    assigned = rows if rid == 'A1' or packet == 'warmup' else [r for r in rows if r['task_folder'] in ASSIGNED.get(rid, [])]
    record = {'rater_id': rid, 'name': NAMES[rid], 'packet': packet,
              'source_sheet_id': source['id'], 'source_url': source['url'],
              'source_modified_utc': source['updated_at'], 'source_range': snap['export']['range'],
              'checked_date': '11-11-2026', 'rows_checked': len(rows),
              'valid_scores': len(valid), 'not_applicable_rows': len(na), 'invalid_rows': invalid,
              'assigned_rows': len(assigned), 'assigned_valid_scores': sum(r['item_id'] in valid for r in assigned),
              'new_observation_keys': added, 'revised_observation_keys': revised,
              'previously_present_now_missing': missing_now,
              'duplicate_observations': sum(k in prior and prior[k] == v for k, v in valid.items()),
              'existing_import': str(prior_path) if prior_path.exists() else None,
              'csv_sha256': hashlib.sha256((folder / 'ratings.csv').read_bytes()).hexdigest(),
              'dedup_key': ['round/packet', 'rater_id', 'item_id'],
              'action': 'Snapshot only; existing canonical import unchanged.'}
    (folder / 'SOURCE_RECEIPT.json').write_text(json.dumps(record, indent=2) + '\n')
    summary.append(record)

result = {'checked_date': '11-11-2026', 'recorded_utc': datetime.now(timezone.utc).isoformat(),
          'sheets_checked': len(summary), 'new_observations': sum(len(r['new_observation_keys']) for r in summary),
          'revised_observations': sum(len(r['revised_observation_keys']) for r in summary),
          'sheets': summary,
          'slava': 'Emailed CSV route; no incoming message or returned CSV found in scoped Gmail searches.',
          'excluded': 'Jacob declined; templates excluded; prospects without assignments are not missing submissions.',
          'scope': 'Collection inventory only. No qualification changes, judge selection, test analysis, or emails.'}
(HERE / 'SUMMARY.json').write_text(json.dumps(result, indent=2) + '\n')
for r in summary:
    print(f"{r['name']}: {r['packet']} {r['valid_scores']}/{r['rows_checked']} numeric; {r['not_applicable_rows']} N/A; new={len(r['new_observation_keys'])}, revised={len(r['revised_observation_keys'])}")
print(f"TOTAL new={result['new_observations']}, revised={result['revised_observations']}")

"""Create unsent review copies; never contact raters or read rating values."""
from pathlib import Path
import csv, json, zipfile
P=Path(__file__).resolve().parent
rows=list(csv.DictReader((P/'ROSTER.csv').open()))
for r in rows:
 if r['rater_id']=='T03':
  r['status_as_of']='Reconfirmed 10-28-2026 in email; completion not established'
  r['replied']+=' | 10-28-2026: plans to finish and catch deadline; receipts/latest_relevant_replies.json'
with (P/'ROSTER.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
receipts=[json.loads(x) for x in (P/'sources/DELIVERY_RECEIPTS.jsonl').read_text().splitlines() if x.strip()]
base=(P/'drafts/EMAIL_Brando_BODY.txt').read_text()
ai=base.split('You may use artificial intelligence',1)[1].split('\n\n',1)[0]
ai='You may use artificial intelligence'+ai
closing=base[base.index('P.S. Feel free'):]
deadline='Please finish by Friday, 11-13-2026 if possible; Sunday, 11-15-2026 is the final deadline. This replaces the deadline printed in the packet.'
queue=[]
for r in rows:
 rid=r['rater_id']
 if r['current_status'] in ('author_sensitivity','declined','extra_only'):continue
 kind='setN' if r['current_status']=='qualified' else 'warmup'
 receipt=next(x for x in receipts if x.get('rater')==rid and x.get('packet')==kind and x.get('zip'))
 packet=P/'packets'/receipt['zip']
 sheet=receipt.get('sheet_url','')
 name={'T01':'Rylan','T03':'Dilara','T04':'Allen','T05':'Srivatsava','T06':'Don','T07':'Simon','V01':'Slava','V02':'Nikil'}[rid]
 if kind=='setN':
  folders=receipt['folders']
  body=f'''Hi {name},

Your VeriBench rating packet is attached.

Your personal rating sheet:
{sheet}

1. Unzip the attachment and read START_HERE.md and human_judgements_prompt.md. Use your personal sheet above.
2. Rate your assigned folders, {' and '.join(folders)}, in that order. Each contains python_source, gold_lean and agent_lean.
3. Match each filename inside agent_lean to its row in your sheet.
4. Compare theorem statements, not proofs, and enter one 0–5 score per agent file using the instructions. Your sheet saves automatically; leave unfinished rows blank.

{ai}

The packet contains your two assigned tasks and 10 agent files. {deadline}

{closing}'''
  subject='VeriBench human-rating packet: your rating task, closes 11-15-2026'
 else:
  route=f'Your personal warm-up sheet:\n{sheet}' if sheet else 'Please fill in the rating_sheet_V01.csv included in the packet and email it back to me privately.'
  save='Your sheet saves automatically; leave unfinished rows blank.' if sheet else 'Keep the filenames and item IDs unchanged; leave unfinished rows blank.'
  body=f'''Hi {name},

Your VeriBench warm-up packet is attached. If you have already completed it, please let me know so I can check it before sending your task folders.

{route}

Unzip the attachment and read START_HERE.md and the rating instructions. Compare theorem statements, not proofs, and enter one 0–5 score for each of the six agent files. {save}

{ai}

{deadline} Please complete the warm-up as soon as you can so there is time for your assigned tasks.

{closing}'''
  subject='VeriBench human-rating warm-up: closes 11-15-2026'
 (P/f'drafts/EMAIL_{rid}_BODY.txt').write_text(body)
 headers={'to':r['delivery_email'],'bcc':'brandojazz@gmail.com,brando.science@gmail.com,brando9@stanford.edu','subject':subject,'attachment':str(packet),'body_file':f'EMAIL_{rid}_BODY.txt','new_message':True,'reply_message_id':None,'status':'prepared, unsent; exact text approval required','sheet_url':sheet}
 (P/f'drafts/EMAIL_{rid}_HEADERS.json').write_text(json.dumps(headers,indent=2)+'\n')
 queue.append({'rater_id':rid,'name':r['name'],'kind':kind,'body':f'drafts/EMAIL_{rid}_BODY.txt','headers':f'drafts/EMAIL_{rid}_HEADERS.json','attachment_exists':packet.exists(),'sheet_access':'prior sharing receipt; live check pending' if sheet else 'CSV return by private email'})
(P/'DISPATCH_QUEUE.json').write_text(json.dumps(queue,indent=2)+'\n')
# Preserve delivered slots exactly, including slot numbers.
assigned=list(csv.DictReader((P/'ASSIGNMENT_delivered.csv').open()))
with (P/'COVERAGE.csv').open('w',newline='') as f:
 w=csv.writer(f);w.writerow(['task_folder','slot','rater_id','status'])
 for n in range(1,26):
  for slot in (1,2):
   found=next((r for r in assigned if r['task_folder']==f'N{n:02}' and r['slot']==str(slot)),None)
   w.writerow([f'N{n:02}',slot,found['rater_id'] if found else '', 'delivered_completion_unverified' if found else 'unfilled'])
print('Prepared',len(queue),'individual email drafts and a 50-slot coverage ledger; no emails sent.')

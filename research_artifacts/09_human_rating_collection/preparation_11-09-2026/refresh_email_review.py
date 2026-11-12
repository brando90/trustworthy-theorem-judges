"""Freeze the exact recipient messages for private coordinator review; never sends."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    queue = json.loads((ROOT / 'DISPATCH_QUEUE.json').read_text())
    old = json.loads((ROOT / 'REVIEW_TEAM_EMAILS_MANIFEST.json').read_text())
    names = {x['rater_id']: x['name'] for x in old['messages']}
    messages = []
    body = [
        '# Review the eight human-rating emails',
        '**TLDR:** These exact messages and original attachments are ready for approval. No collaborator message in this review has been sent. Preferred completion: Friday, 11-13-2026; final deadline: Sunday, 11-15-2026.',
        'All seven personal Google Sheets have verified restricted editor access. Slava uses the existing private CSV return route. The drafts preserve the scientific instructions, localized-help policy and P.S., with the recipient-specific link, assignment, filenames and count. Rylan and Don have explicit sign-in notes because their delivery and sheet accounts differ.',
        'Approval and authorization to send apply to one new email per recipient below. Normal Gmail grouping is fine. Broader recruitment is separate.',
        '## Recipient index',
    ]
    for item in queue:
        h = json.loads((ROOT / item['headers']).read_text())
        body.append(f"- {names[item['rater_id']]} ({item['rater_id']}): {h['to']} — {item['kind']}")
    for item in queue:
        rid = item['rater_id']
        hp = ROOT / item['headers']
        h = json.loads(hp.read_text())
        bp = ROOT / item['body']
        attachment = Path(h['attachment'])
        messages.append(dict(rater_id=rid, name=names[rid], to=h['to'], subject=h['subject'],
                             body_file=item['body'], body_sha256=sha(bp),
                             attachment=str(attachment), attachment_sha256=sha(attachment),
                             headers_sha256=sha(hp)))
        body.extend([f"## {names[rid]} — {rid}",
                     f"To: {h['to']}  \nBCC: {h['bcc']}  \nSubject: {h['subject']}",
                     f"Attachment: [{attachment.name}]({attachment})  \nSHA-256: `{sha(attachment)}`",
                     '```text\n' + bp.read_text().rstrip() + '\n```'])
    review = ROOT / 'REVIEW_TEAM_EMAILS.md'
    review.write_text('\n\n'.join(body) + '\n')
    manifest = dict(date='11-09-2026', status='prepared_awaiting_exact_text_and_send_approval',
                    review_sha256=sha(review), messages=messages)
    (ROOT / 'REVIEW_TEAM_EMAILS_MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print('Frozen eight exact messages and attachment hashes for private review; no email sent.')

if __name__ == '__main__':
    main()

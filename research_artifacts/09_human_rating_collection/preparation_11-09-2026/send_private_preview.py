"""Send explicitly authorized previews only to Brando; preserve exact body/ZIP."""
import email
import hashlib
import importlib.util
import imaplib
import json
import sys
from datetime import datetime, timezone
from email.message import EmailMessage
from email.utils import formatdate, make_msgid
from pathlib import Path

BASE = Path(__file__).resolve().parent

def send_verified(key, subject, body, attachments=(), to='brandojazz@gmail.com'):
    assert to in {'brandojazz@gmail.com', 'brando.science@gmail.com'}
    receipt = BASE / 'receipts' / f'{key}.json'
    if receipt.exists():
        raise RuntimeError('Existing receipt; inspect it rather than resending.')
    sender = 'brandojazz@gmail.com'
    password = (Path.home() / 'keys/gmail_app_password.txt').read_text().strip()
    spec = importlib.util.spec_from_file_location('uutils_emailing', Path.home() / 'ultimate-utils/py_src/uutils/emailing.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    msg = EmailMessage()
    msg['Subject'], msg['From'], msg['To'] = subject, sender, to
    msg['Date'], msg['Message-ID'] = formatdate(localtime=True), make_msgid(domain='gmail.com')
    msg.set_content(body)
    hashes = {}
    for file in attachments:
        p = Path(file)
        data = p.read_bytes()
        hashes[p.name] = hashlib.sha256(data).hexdigest()
        msg.add_attachment(data, maintype='application', subtype='zip', filename=p.name)
    record = dict(created_utc=datetime.now(timezone.utc).isoformat(), to=to,
                  bcc=[sender,'brando.science@gmail.com','brando9@stanford.edu'],
                  subject=subject, message_id=msg['Message-ID'],
                  body_sha256=hashlib.sha256(body.encode()).hexdigest(), attachment_sha256=hashes,
                  smtp_completed=False, inbox_verified=False, no_reply_headers=True)
    receipt.write_text(json.dumps(record, indent=2)+'\n')
    notifier = module.SMTPNotifier('smtp.gmail.com',587,sender,password,sender,bcc=','.join(record['bcc']))
    notifier._send(msg,to)
    record['smtp_completed'] = True
    receipt.write_text(json.dumps(record, indent=2)+'\n')
    with imaplib.IMAP4_SSL('imap.gmail.com') as inbox:
        inbox.login(sender,password)
        inbox.select('INBOX',readonly=True)
        ok, hits = inbox.uid('search',None,'HEADER','Message-ID',f'"{msg["Message-ID"]}"')
        if ok != 'OK' or not hits[0]:
            print(f'{key}: SMTP complete; inbox confirmation pending. Do not resend.')
            return
        uid = hits[0].split()[-1]
        ok, fetched = inbox.uid('fetch',uid,'(BODY.PEEK[])')
        raw = next(x[1] for x in fetched if isinstance(x,tuple))
        delivered = email.message_from_bytes(raw,policy=email.policy.default)
        assert not delivered.get('In-Reply-To') and not delivered.get('References')
        assert delivered.get_body(preferencelist=('plain',)).get_content().replace('\r\n','\n').rstrip('\n') == body.rstrip('\n')
        actual = {x.get_filename():hashlib.sha256(x.get_payload(decode=True)).hexdigest() for x in delivered.iter_attachments()}
        assert actual == hashes
        record.update(inbox_verified=True,imap_uid=uid.decode())
        receipt.write_text(json.dumps(record,indent=2)+'\n')
    print(f'{key}: delivered to Brando; exact body and attachment hashes verified.')

if __name__ == '__main__':
    rid = sys.argv[1]
    assert rid in {'T01','T03','T04','T05','T06','T07','V01','V02'}
    headers = json.loads((BASE / 'drafts' / f'EMAIL_{rid}_HEADERS.json').read_text())
    body = (BASE / 'drafts' / f'EMAIL_{rid}_BODY.txt').read_text()
    suffix = 'SIGNIN' if rid in {'T01','T06'} else 'REVIEW'
    send_verified(f'PREVIEW_{rid}_{suffix}_11-09-2026',headers['subject'],body,[headers['attachment']])

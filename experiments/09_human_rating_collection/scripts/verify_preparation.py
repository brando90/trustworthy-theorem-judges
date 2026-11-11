#!/usr/bin/env python3
"""Verify private collection preparation without reading other raters' scores."""
import csv
import hashlib
import json
from pathlib import Path
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parents[3]
PREP = ROOT / 'private/09_human_rating_collection/preparation_11-09-2026'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if not PREP.is_dir():
        raise SystemExit('Private preparation record is not installed on this machine.')
    receipt = json.loads((PREP / 'COPY_RECEIPT.json').read_text())
    for row in receipt['files']:
        assert digest(ROOT / row['destination']) == row['sha256'], row['destination']
    archive = PREP / 'packets/VeriBench_Brando_Rating_Packet_Human1.zip'
    assert digest(archive) == '66199e4e404d1ceccdc1cf97a128fd0c89103f58f7d071b9482a339eb301fb90'
    candidates = set()
    with ZipFile(archive) as z:
        for name in z.namelist():
            if name.endswith('/'):
                continue
            relative = Path(name).relative_to('VeriBench_Brando_Rating_Packet_Human1')
            assert (ROOT / 'private/original' / relative).read_bytes() == z.read(name), name
            if relative.parent.name == 'agent_lean':
                candidates.add((relative.parts[0], relative.name))
    assert len(candidates) == 125
    sheet = json.loads((PREP / 'receipts/BRANDO_SHEET_IDENTITY.json').read_text())
    assert set(map(tuple, sheet['folder_filename_pairs'])) == candidates
    assignment_path = PREP / 'ASSIGNMENT_delivered.csv'
    assert assignment_path.read_bytes() == (PREP / 'sources/ASSIGNMENT_delivered.csv').read_bytes()
    assignments = list(csv.DictReader(assignment_path.open()))
    assert len(assignments) == 4
    assert len({(r['task_folder'], r['slot']) for r in assignments}) == 4
    assert all(r['rater_id'] not in {'A1', 'V03'} for r in assignments)
    roster = {r['rater_id']: r for r in csv.DictReader((PREP / 'ROSTER.csv').open())}
    assert roster['V03']['current_status'] == 'declined'
    for row in assignments:
        assert roster[row['rater_id']]['current_status'] == 'qualified'
    queue = json.loads((PREP / 'DISPATCH_QUEUE.json').read_text())
    assert len(queue) == 8
    review = json.loads((PREP / 'REVIEW_TEAM_EMAILS_MANIFEST.json').read_text())
    assert digest(PREP / 'REVIEW_TEAM_EMAILS.md') == review['review_sha256']
    messages = {item['rater_id']: item for item in review['messages']}
    assert len(messages) == len(review['messages']) == len(queue)
    permissions = json.loads((PREP / 'receipts/TEAM_PERMISSION_CHECKS.json').read_text())
    assert not permissions['not_yet_verified']
    expected_sheet_ids = set()
    for item in queue:
        headers = json.loads((PREP / item['headers']).read_text())
        body = (PREP / item['body']).read_text()
        approved_candidate = messages[item['rater_id']]
        assert digest(PREP / item['body']) == approved_candidate['body_sha256']
        assert digest(PREP / item['headers']) == approved_candidate['headers_sha256']
        assert digest(Path(headers['attachment'])) == approved_candidate['attachment_sha256']
        assert headers['to'] == approved_candidate['to']
        assert headers['subject'] == approved_candidate['subject']
        assert headers['new_message'] and not headers['reply_message_id']
        assert Path(headers['attachment']).is_file()
        assert headers['to'] == roster[item['rater_id']]['delivery_email']
        assert '11-13-2026' in body and '11-15-2026' in body
        assert 'Email is preferred for questions!' in body and 'Lean concepts' in body
        assert 'TLDR' not in body and 'Snapshot:' not in body
        assert sheet['sheet_url'] not in body
        if headers['sheet_url']:
            assert headers['sheet_url'] in body
            expected_sheet_ids.add(item['rater_id'])
        if item['kind'] == 'setN':
            with ZipFile(headers['attachment']) as z:
                files = [n for n in z.namelist() if '/agent_lean/' in n and n.endswith('.lean')]
                assert len(files) == 10
                actual_folders = {Path(n).parts[1] for n in files}
                expected_folders = {r['task_folder'] for r in assignments if r['rater_id'] == item['rater_id']}
                assert actual_folders == expected_folders
    assert set(permissions['verified_editor_permissions']) == expected_sheet_ids
    print('PASS: approved archive, 125 sheet identities, four delivered slots, eight individual drafts.')
    print('PASS: frozen review hashes and all seven recorded editor-access checks; live access may change.')
    print('Dispatch status: HOLD. The 11-11-2026 common-form amendment requires revised team sheets, '
          'packets and exact-text review after Brando\'s pilot. This check validates the historical preparation only.')
    print('No scores entered, no test ratings inspected, no collaborator messages sent by this check.')


if __name__ == '__main__':
    main()

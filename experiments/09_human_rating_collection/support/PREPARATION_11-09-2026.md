# Human-rating preparation — 11-09-2026

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_human_rating_collection/support/PREPARATION_11-09-2026.md>

**TLDR:** The existing rating packet is available in this repository's private store. The preferred deadline is Friday, 11-13-2026; the final deadline is Sunday, 11-15-2026. Personal rating can start; collaborator dispatch remains a separate, explicitly approved action.

## Current collection

**Coordination:** [Prepare human grading task](codex://threads/01a1a8f9-dcb7-7381-9368-91d6e51faffd) is the sole owner for this preparation and the practical human-rating judge. Follow the [consolidated ownership record](COORDINATION_11-09-2026.md); migration and historical methodology chats do not create separate dispatch owners.

This is the inherited set-N collection: 25 Python tasks, five candidate files per task, and 125 candidate files. Its primary design calls for two qualified independent raters per candidate, or 50 folder assignments and 250 individual ratings. The coordinator's own ratings are an additional sensitivity panel, not replacements for those two ratings. These are design counts, not completed observations. This collection is separate from the larger prospective design in experiment 02.

The active preparation record is `private/09_human_rating_collection/preparation_11-09-2026/README.md`. It contains the private roster, delivery queue, original attachments, source receipts, and proposed email bodies. The migration checkpoint beside this document tracks the broader move from VeriBench; this preparation record does not change that migration's files or ownership.

## Verified preparation

- The approved personal ZIP contains 25 folders and 125 candidates. Its bytes match the original delivery, and every extracted file matches the ZIP.
- The coordinator's personal sheet was opened in the signed-in owner browser, and its 125 identity rows match the packet. No rating was entered.
- The updated personal email was delivered as a new message, with the original ZIP and authorized deadline. Its inbox attachment hash was verified.
- Delivered team assignments are preserved, including their original filenames and slot numbers. Do not rerun the historical random assignment script over them.
- Two task emails and six warm-up emails are prepared individually, with each recipient's original packet and return route. They are unsent drafts for text review.
- All seven team Google Sheets have verified restricted editor access through the signed-in owner browser. The eighth recipient uses the existing private CSV return route. No permissions or rating values were changed.
- The private `REVIEW_TEAM_EMAILS.md` contains all eight exact messages; its manifest freezes the body, header and attachment hashes. Two drafts name the required sign-in account because it differs from the delivery address.
- The declined participant was removed from active assignment capacity using the user's explicit correction. Previously invited people are not counted as consenting raters.
- Original packet dates remain historical. The newly authorized email deadline supersedes them; the delivered ZIPs are not rewritten.

## Sending protocol

Before using this protocol, read the [required judge-development context](JUDGE_FORMULATIONS_11-09-2026.md). The two main formulations are training-correlation optimization (2) and proper-loss training (4); the collection must preserve independent raw observations and exposure history for both. Keep this coordinator context out of the locked participant email.

1. Use the private roster and delivery ledger. Check consent, warm-up status, assigned folders, prior delivery, and the correct account for the personal sheet. Keep individual sheets restricted; never send another rater's link or ratings.
2. Use the frozen attachment for an existing assignment. Match its candidate filenames to the sheet's identity columns, without opening sealed rating values. Record the attachment hash. For a new assignment, preserve the same scientific file bytes and create a new delivery receipt.
3. Keep the approved prose, including localized artificial intelligence (AI) help and the email-preferred P.S. The approved personal template contains a personal sheet and a full assignment. Team drafts explicitly propose the recipient-specific link, assigned folder names, instruction filename, and file count; those differences require text approval under the user's template lock.
4. Send a complete new email, with the real ZIP attachment, normal subject, and no reply/thread headers. Gmail may group messages automatically. Do not add chat-only summaries or revision labels to the rater email. Blind-copy the coordinator's required inboxes; add visible copies only if requested.
5. Every requested text correction gets a new preview email to the coordinator. Drafting and text approval do not by themselves authorize dispatch to collaborators. After an explicit send instruction, verify delivery once and record the message identifier, recipients, attachment hash, assignment, and deadline.
6. Collect each person's ratings independently. Use the inherited warm-up qualification procedure without changing its threshold. Keep the coordinator's ratings separate and preserve exposure history. Do not inspect sealed set-N scores to select a judge.

## Remaining collection work

The inherited delivery ledger records four of the 50 required folder assignments as delivered, not completed. Other consenting participants still need their warm-up status resolved before primary assignments. Recruitment and completed human ratings cannot be substituted by packet preparation. All seven sheet-access checks are complete. Scoped owner-inbox searches for recent participant rating replies found no new matching replies; that does not establish whether a sheet is complete. Review the concrete individual drafts before authorizing team delivery, then reconcile any intervening replies or completion metadata without opening sealed scores.

Run `python3 experiments/09_human_rating_collection/support/scripts/verify_preparation.py` on the coordinator's machine to check the frozen packet, identity mapping, assignment continuity, and proposed messages. The private data are deliberately absent from public clones.

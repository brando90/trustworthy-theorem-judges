# Privacy and consent

**Doc link:** <https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/20_predict_a_persons_ratings_from_a_persona_built_from_public_information_start_14Nov2026/PRIVACY_AND_CONSENT.md>

**TLDR:** Public information only, nothing behind a login, nothing private. A colleague's persona goes into this repository only with that person's OK, and nothing about a named person is published without it.

## What may be collected

- Only pages anyone can open without signing in: a personal or lab site, a university or company profile, papers and talks, a public professional profile page, public code repositories.
- A page that needs a login, an invitation or a follower approval is out. This includes most Instagram and LinkedIn content. If it opens only when signed in, do not use it and do not look for a way around it.
- This repository, its rating files and any rating sheet are never a source for a persona. They hold the ratings being predicted.
- Collect what bears on how the person would judge formal specification coverage: field and training, research topics, publications, public writing about evaluation, proofs or formal methods, and professional role. Leave out health, family, relationships, religion, politics, sexual orientation, home address, finances and anything the person did not publish about their work or public views.
- Do not infer a sensitive trait from indirect signals.

## What may be stored

- Each source is recorded as link, retrieval date, a short quote and a content hash. Raw page copies stay outside public Git.
- The persona text cites its sources by number. It states only what a source says.
- Brando consents for his own persona, in his words of 11-14-2026.
- For anyone else, the persona text, its source list and any result tied to the person's name are committed only after that person says OK. Until then, nothing about them is committed here. If they do not answer, nothing is stored. How each person is asked is Brando's decision, and this folder sends no message.
- A person can ask to see their persona and the results about them, and can have them removed from the repository going forward (earlier commits stay in Git history; say so when asking).

## What may be published

- Nothing about a named person (persona, predictions, how close the persona was) is published without that person's OK.
- Without OK, a person counts only inside pooled results under a code, never by name.
- Report the persona as a model-written approximation. It is a test of how much public information predicts a rating tendency. It does not replace the person, and it is never used to stand in for their rating in the data.

## Stored with the persona

Which model and harness wrote it, the date, and the source numbers. The persona and its hash are committed before the person's ratings are read, so the order can be checked.

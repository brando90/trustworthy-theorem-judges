# Review all 31 rating emails (100-file packets), 11-16-2026

**TLDR:** These are the 31 unsent Gmail drafts (one per rater, `0` sent). Every email is the common text below with the rater's first name, personal Sheet link, own `.zip` (100 agent files) and, for some, a one-paragraph opener. Send only with `python3 experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/support/scripts/native_packet_generation/build_full_team_packets.py send --confirm --all` after Brando's yes; it sends each draft as it stands in Gmail (so edits there are kept), skips anyone already sent and moves the sent draft to Trash.

- **Subject:** VeriBench human-rating main rating task: closes Thursday, 11-19-2026, 6pm PT
- **From:** Brando Miranda <brandojazz@gmail.com>
- **BCC (every email):** brando.science@gmail.com, brandojazz@gmail.com, brando9@stanford.edu

## Common text

```text
Hi {first name},

Your VeriBench rating packet is attached: 100 agent files in 25 task folders. Your sheet lists them in your own order; please work from the top down and do as many as you can, even a few helps.

Your personal rating sheet:
{personal Sheet link}

What to do:
1. Unzip the attachment and read START_HERE.md.
2. In each task folder, compare the agent's theorem statements in agent_lean/ with the reference statements in gold_lean/, and rate how well the agent's statements cover the reference (not the proofs).
3. In your sheet, for each file enter a score from 0 to 5 and a one-sentence rationale in your own words, and answer yes, no or unsure to the AI question (column ai_assisted_rating_attestation). This is a first round, so I would love your feedback on the form: if the rationale is too much work, or you would prefer not to have that column, please tell me. If anything in a task looks wrong, just email me.

Please choose the score yourself and use AI only for help with Lean notation or a specific point. Your sheet saves automatically, so there is nothing to send back.

Please finish by 6pm Pacific on Thursday, 11-19-2026 if you can, so I can run experiments overnight and show results in a meeting the next day. If you can only get part of it done by then, that is still very helpful. Filling it in as you go is even better: your sheet saves automatically, and I will pull the data and start my analysis as it comes in, so we can iterate.

P.S. Feel free to email me with any questions. Email is preferred for questions! Happy to clarify anything! The full instructions are also public at https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/09_prepare_packets_and_collect_human_ratings_start_28Sep2026/rating_task_packet/main_rating_task/START_HERE.md

Brando (drafted with Claude)
-----
Brando Miranda
Ph.D. Student
Computer Science, Stanford University
EDGE Scholar, Stanford University
brando9@stanford.edu
website: https://brando90.github.io/brandomiranda/
```

## Openers (inserted after the greeting)

- **coauthor:** Would you be willing to help with a human-rating task for VeriBench? Your ratings would be really valuable, and if you are interested and have time, I would be happy to add you as a co-author on the papers this data is used for. No pressure at all.
- **varun:** Would you be willing to help with a human-rating task for VeriBench? Your ratings would be really valuable, and if you are interested and have time, I would be happy to add you as a co-author on the papers this data is used for. No pressure at all. Doing these ratings is also a great way to get intimately familiar with Lean 4 autoformalization—and if you have seen Andrej Karpathy's and Rylan Schaeffer's advice on becoming a top machine learning researcher (for example, how much of ImageNet Karpathy inspected firsthand), looking closely at the actual data yourself is essential.
- **weekend:** Your ratings would be extremely valuable. If you can finish early, that would be even better, as many ratings as you have time for.

## Per-rater differences

| ID | Rater | To | Greeting | Opener | Personal Sheet | Zip SHA-256 (first 12) |
| --- | --- | --- | --- | --- | --- | --- |
| `T01` | Rylan Schaeffer | rschaef@cs.stanford.edu | Rylan | — | [Sheet](https://docs.google.com/spreadsheets/d/1fOr2oE2Fmibw9y8qDL7pMMuj6XH9luMJOMLDzIcBqo0/edit) | `4415e024dd9c` |
| `T02` | Yegor Denisov-Blanch | ydebl@stanford.edu | Yegor | — | [Sheet](https://docs.google.com/spreadsheets/d/1Hpcb4NP754RDWstDkiaTR59K9AX2vXNL6IR9iXKRo-Y/edit) | `63916aa6cb90` |
| `T03` | Dilara Soylu | soylu@stanford.edu | Dilara | — | [Sheet](https://docs.google.com/spreadsheets/d/1D6Enb6IKRAZOoqhmk7bHwTqsFZ10U5dH3H3gRmJ8XPk/edit) | `82c6237782a2` |
| `T04` | Allen Nie | aimingnie@gmail.com | Allen | — | [Sheet](https://docs.google.com/spreadsheets/d/1iE_2PfDe1uw4_eGJCa-YV_kj1ZodQajZQ0nxDDv5YNo/edit) | `002a3447ae60` |
| `T05` | Srivatsava Daruru (Sri) | vatsava@gmail.com | Srivatsava | — | [Sheet](https://docs.google.com/spreadsheets/d/163ZxKeTXqseLrmwY-b5QjqeBulinHsZAiAPo1zsJdJI/edit) | `c75da2bd0dff` |
| `T06` | Donald Poindexter Jr | ddpoindexterjr@gmail.com | Don | — | [Sheet](https://docs.google.com/spreadsheets/d/1l_zdHObt3_0hd0MJkIJ5btU51hxNsHKwHyBUv0cuSLg/edit) | `df1893c308f3` |
| `T07` | Simon Obstbaum | simon@obstbaum.eu | Simon | — | [Sheet](https://docs.google.com/spreadsheets/d/1KMYUiMbL7wEvKn9KGN8KjHSca1DcYT-uZE3psSeqrq4/edit) | `0408da02e36b` |
| `T08` | Amy Lu | amylucky@stanford.edu | Amy | coauthor | [Sheet](https://docs.google.com/spreadsheets/d/1YLq64komUf0lD8fdChDYeTZS--zpulbn-XTVhLWVUlE/edit) | `bd4d819449a1` |
| `T09` | Ethan R Lee | eth127@stanford.edu | Ethan | coauthor | [Sheet](https://docs.google.com/spreadsheets/d/1HraAoO6Cczkm2-8ec2Tj97Cuc75LIUWwRUvKgJl5bCw/edit) | `46383e9d767b` |
| `T10` | Ethan Hersch | ehersch@stanford.edu | Ethan | — | [Sheet](https://docs.google.com/spreadsheets/d/1QUKFbM9AQbjj3sQo7x0mQSKiWLCm8Ta_qrkeejxDZ_8/edit) | `b904f3c57546` |
| `T11` | Kirill Acharya | kacharya@stanford.edu | Kirill | — | [Sheet](https://docs.google.com/spreadsheets/d/1gHkqMYIZyzPJI4rRsNS4_9Dyat2B3x7HDA4YTulkr3U/edit) | `9420e49a9bb2` |
| `T12` | Rakshit Kaushik | rakshitk@stanford.edu | Rakshit | weekend | [Sheet](https://docs.google.com/spreadsheets/d/1rHhh1sCq_Trzlda3fRu-RXES9QG_M1Wb0CzP6Utj7eQ/edit) | `d028132da40b` |
| `T13` | Zhanke Zhou | cszkzhou@comp.hkbu.edu.hk | Zhanke | — | [Sheet](https://docs.google.com/spreadsheets/d/13yAF6JYrXcpSWMoGa_PZp9qqrTDllVCP47ygivEdifg/edit) | `04b50a87f780` |
| `T14` | Daneshvar Amrollahi | daneshva@stanford.edu | Daneshvar | — | [Sheet](https://docs.google.com/spreadsheets/d/1onFAX0J9uMmiMEq2t7g75lxxrfGw7B7NjnqnmzRpT_I/edit) | `d26655172c6d` |
| `T15` | Leni Aniva | aniva@stanford.edu | Leni | — | [Sheet](https://docs.google.com/spreadsheets/d/1Axk32oyQgk299JNEIi4M9bHcBlYPTwJrDyFXOAGnKY0/edit) | `529ec2c1268d` |
| `T16` | Iddah Mlauzi | iddah@stanford.edu | Iddah | — | [Sheet](https://docs.google.com/spreadsheets/d/11CSWZi89IiLeZDfJCjeJ13VbM0AJEYiNKLpwG0JFCGo/edit) | `d6f369a5ee60` |
| `T17` | Elyas Obbad | eobbad@gmail.com | Elyas | — | [Sheet](https://docs.google.com/spreadsheets/d/1jIk9KsjMO1A_vgTBN6-R-kB6_hww7AJrggdKiWg8daY/edit) | `54712f4dc796` |
| `T18` | Weston Kirk | wkirk@stanford.edu | Weston | — | [Sheet](https://docs.google.com/spreadsheets/d/1ygdl8LPRna7e2m7l44iHizCWyknHuM9HPMbKstONVuE/edit) | `d5516d9a9683` |
| `T19` | Zixiao Jolene Wang | zixiaowang@g.harvard.edu | Zixiao | — | [Sheet](https://docs.google.com/spreadsheets/d/1vgngMlu0V-bQz19ZPks0KIkQvSRQy9ZNR3cW-F54HSE/edit) | `500294ce067a` |
| `T20` | Kai Fronsdal | kaif@stanford.edu | Kai | — | [Sheet](https://docs.google.com/spreadsheets/d/15mji6A89i4dIaVZnmnx-PqNjaeRgq53ZEOFu9kugyZc/edit) | `09a2a7c35aa9` |
| `T21` | Ying Li | louisely@stanford.edu | Ying | — | [Sheet](https://docs.google.com/spreadsheets/d/1S4gFJYeoLoFNWIyAqbVxD0AdiKfAwNx0hIEFENyw31Q/edit) | `579ebe0e45c3` |
| `T22` | Shurui Liu | srliu@stanford.edu | Shurui | — | [Sheet](https://docs.google.com/spreadsheets/d/1u-iS1GwIeaubBxvfOOq46WVhqUQxlQftAPn_RidZLIU/edit) | `d1a9f1c93211` |
| `T23` | Steven Dillmann | stevendi@stanford.edu | Steven | — | [Sheet](https://docs.google.com/spreadsheets/d/1vsH0CxrabDY_8aPWlKvZUadV6U7fOsFjRVUMzt-e6T0/edit) | `0ab88b905b64` |
| `T24` | Santiago Cuellar | santiago@galois.com | Santiago | — | [Sheet](https://docs.google.com/spreadsheets/d/1HA8aAPI4aRXSlAZxCiygFO5mbzNydOrcqnOVjS1lftQ/edit) | `6a59de4faac7` |
| `T25` | John Sarracino | sarracino2@llnl.gov | John | — | [Sheet](https://docs.google.com/spreadsheets/d/10fnyfoqZmsL51cczGSj-k_a6s72YjHMW42NvaC3DL9g/edit) | `b07a4705fa25` |
| `T26` | Donghyun Lee | lukedhlee@berkeley.edu | Donghyun | — | [Sheet](https://docs.google.com/spreadsheets/d/11lvfec1IYxHCB1cucfgKb8V1eO4rAa44sAfEzU-NgfU/edit) | `b7ee59a4e62d` |
| `T27` | Anka Reuel | anka@cs.stanford.edu | Anka | coauthor | [Sheet](https://docs.google.com/spreadsheets/d/1M7B9cln6YiazYfncbpYj-oXujpKl6JCz4vS4W7s7X8A/edit) | `c67154e117fb` |
| `T28` | Max Lamparth | lamparth@stanford.edu | Max | coauthor | [Sheet](https://docs.google.com/spreadsheets/d/1buaJ9ZcH2tpzM34j7Y-J3jdfpTeC80DXb_4nj_nTfyY/edit) | `7d007ebd4324` |
| `T29` | Varun Raj Madan | vmadan@stanford.edu | Varun | varun | [Sheet](https://docs.google.com/spreadsheets/d/1FNdY9J873-8gOLCWM3ps0zhSQ8rcOMrY4LCVL8oZQng/edit) | `74fde949458c` |
| `V01` | Slava Naprienko | slava@vals.ai | Slava | — | [Sheet](https://docs.google.com/spreadsheets/d/1ioE_bZBy4g9mQj6-xK2CVtqbzF3FJtiU-UvPYLiCkZo/edit) | `da6e253a04e5` |
| `V02` | Nikil Ravi | nikil@vals.ai | Nikil | — | [Sheet](https://docs.google.com/spreadsheets/d/1iuxZBCPDm0LMSZ2iAgiB9twyHoThcQMPPOGx4eTBnGc/edit) | `37475ea86f46` |

Varun's opener leaves out the dictated clause about Anthropic ("not interested" vs "now interested" was ambiguous); add it in his Gmail draft if wanted.

# Trustworthy theorem judges

Can a language model tell which gold-reference theorems follow from an agent’s formal specification? We collect independent human ratings of statement coverage. The planned judge comparison uses the same candidates and gold statements twice, with and without the gold proofs. A separate comparison asks how the judgments relate to what a theorem prover can establish.

## Rate a file

Open the extracted packet’s `START_HERE.md` and `Rating_Instructions.md`. Read the Python source and gold theorem statements, then open the first candidate in its folder. A gold statement counts as covered if the candidate statements imply it, possibly by combining several lemmas. Apply the packet’s 0–5 rubric and record one final score per candidate file. A score summarizes the whole file.

The coordinator uses the personal sheet supplied with the original packet. Team members use a separate answer sheet each. Keep completed ratings private until collection closes.

## Prepare identical examples for independent ratings

The coordinator needs the original, extracted VeriBench human-rating packet. The public checkout contains the builder. On the coordinator’s machine, the packet, individual answers and shareable archives live under the ignored `private/` directory.

From the repository root, build an archive for the folders assigned to a rater. For example, for folder 1:

```sh
python3 scripts/make_team_packet.py private/original private/team-folder-01.zip --folders 1
```

Pass multiple folder numbers to package an assignment. Omit `--folders` to package all 25 folders. Use a new output filename for each build. The builder checks the frozen delivery manifest, preserves the original example bytes and filenames, and includes the rubric, instructions, a blank answer sheet and file checksums. Send the same archive to people rating the same assignment. Each returns their own completed sheet privately.

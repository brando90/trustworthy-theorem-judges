#!/usr/bin/env python3
"""TLDR: Safely regenerate historical analyzer outputs without overwriting the consolidated report or modifying frozen code."""
import argparse
import json
import runpy
import subprocess
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
DOC='https://github.com/brando90/trustworthy-theorem-judges/blob/main/experiments/05_fresh_local_prover_target_judges/'
COMPANION='https://docs.google.com/document/d/1zB-gYk-zU1wToS_E_carGSRGtUcF1NgZ-jWF5t1SJws'

def one(condition):
    folder=ROOT if condition=='v1' else ROOT/'conditions/nonthinking_v2'
    script=folder/'scripts/analyze.py'
    original=Path.write_text
    permitted={folder/'results/analysis.json',folder/'results.md'}
    def write(path,data,*args,**kwargs):
        path=path.resolve()
        if path not in permitted:raise RuntimeError('Unexpected historical-analyzer output: '+str(path))
        if path==folder/'results.md':
            if condition=='v1':
                path=ROOT/'results/v1_results.md'
                data=data.replace('(results/analysis.json)','(analysis.json)')
            else:
                metrics=json.loads((folder/'results/analysis.json').read_text())
                assert [metrics['judges'][j]['brier_bootstrap']['valid_resamples'] for j in ['J0','J1']]==[6843,9375]
                assert [metrics['judges'][j]['observed_pairs'] for j in ['J0','J1']]==[1,3]
                data=data.replace('differences,  correlation','differences, correlation')
                data=data.replace('95% task-family bootstrap interval','Mechanical bootstrap interval (not inferential)')
                data=data.replace('Full-denominator Brier bounds','Hypothetical missing-loss bounds')
                warning=('**Post-run reporting qualification:** Inferential intervals are unavailable: J0 has one observed family (6,843 valid draws; 3,157 empty draws), J1 has two (9,375 valid; 625 empty). '
                         'The mechanical [0,0] results are not evidence of precision. Missing-loss bounds assume hypothetical defined losses for every missing cell; malformed artifacts have no defined semantic outcome. '
                         'See the [consolidated report](../../results.md) and [post-run protocol notes](../../PROTOCOL_OBSERVATIONS.md). The frozen analyzer and numerical JSON are unchanged.\n\n')
                title='# Fresh local prover-target judge results\n\n'
                data=data.replace(title,title+'**Doc link:** <'+DOC+'conditions/nonthinking_v2/results.md>\n\n**Companion notes:** [Google Doc]('+COMPANION+')\n\n'+warning,1)
        return original(path,data,*args,**kwargs)
    Path.write_text=write
    sys.path.insert(0,str(script.parent))
    try:runpy.run_path(str(script),run_name='__main__')
    finally:Path.write_text=original

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--one',choices=['v1','v2']);args=parser.parse_args()
    if args.one:one(args.one)
    else:
        for condition in ['v1','v2']:subprocess.run([sys.executable,__file__,'--one',condition],check=True)
        subprocess.run([sys.executable,str(ROOT/'scripts/report.py')],check=True)
if __name__=='__main__':main()

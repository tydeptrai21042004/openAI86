#!/usr/bin/env python3
"""Check the exact theorem reports; only use after a successful Lean build."""
from pathlib import Path
import sys
from axiom_report_parser import parse_axioms, UnrecognizedAxiomReport
names = ['OpenAI086.v21_paper_lemma33_prefix','OpenAI086.v21_paper_lemma33_variation']
try:
    log=Path(sys.argv[1]).read_text()
    for n in names:
        print(n, sorted(parse_axioms(log,n)))
except (OSError, IndexError, UnrecognizedAxiomReport) as e:
    sys.exit(f'NOT VERIFIED: {e}')
print('Both exact axiom reports accepted; this does not certify Theorem 1.1.')

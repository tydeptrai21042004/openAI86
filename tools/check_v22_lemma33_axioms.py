#!/usr/bin/env python3
"""Only run after Lean has successfully built and emitted these four reports."""
from pathlib import Path
import sys
from axiom_report_parser import parse_axioms, UnrecognizedAxiomReport
names = ['OpenAI086.v21_paper_lemma33_prefix','OpenAI086.v21_paper_lemma33_variation',
         'OpenAI086.v22_submodule_prefix','OpenAI086.v22_submodule_variation']
try:
    log=Path(sys.argv[1]).read_text()
    for n in names:
        print(n, sorted(parse_axioms(log,n)))
except (OSError, IndexError, UnrecognizedAxiomReport) as e:
    sys.exit(f'NOT VERIFIED: {e}')
print('All four exact reports accepted after build; not a certificate for Theorem 1.1.')

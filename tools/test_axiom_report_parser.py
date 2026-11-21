#!/usr/bin/env python3
"""Self-tests for a strict exact-main-theorem axiom gate."""
from axiom_report_parser import parse_axioms, UnrecognizedAxiomReport
T='OpenAI086.Theorem1_1_Proved'
examples = [
    (f"'{T}' depends on axioms: [propext, Classical.choice, Quot.sound]", True),
    (f"'{T}' does not depend on any axioms", True),
    (f"'{T}' depends on axioms: [propext, sorryAx]", False),
    (f"'{T}' depends on axioms: [MyHiddenAxiom]", False),
    ("Theorem compiled successfully", False),
    ("'OpenAI086.AnotherTheorem' depends on axioms: [propext]", False),
    (f"'{T}' depends on axioms: [propext, Classical.choice, Quot.sound, Lean.ofReduceBool]", True),
]
for msg, accepted in examples:
    try:
        parse_axioms(msg, T)
    except UnrecognizedAxiomReport:
        actual = False
    else:
        actual = True
    assert actual == accepted, (msg, accepted, actual)
print(f'PASS: {len(examples)} exact-theorem axiom parser cases')

#!/usr/bin/env python3
"""Fail-closed parser for Lean `#print axioms` output.

A successful Lean process exit status is not, by itself, a proof certificate:
we also require an actual, attributable axiom report for the exact local
main theorem and reject unexpected axioms. This parser is intentionally
conservative. Unsupported Lean output formats cause a failure.
"""
from __future__ import annotations
import re

TRUSTED_AXIOMS = frozenset({
    'propext', 'Quot.sound', 'Classical.choice', 'Lean.ofReduceBool',
})

class UnrecognizedAxiomReport(ValueError):
    pass


def parse_axioms(stdout: str, theorem: str) -> set[str]:
    ident = re.escape(theorem)
    # Mathlib/Lean report: 'Namespace.name' depends on axioms: [a, b, ...]
    report = re.search(
        rf"(?m)^\s*(?:['`\"])?{ident}(?:['`\"])?\s+depends on axioms:\s*\[([^\]]*)\]\s*$",
        stdout,
    )
    if report:
        entries = {x.strip() for x in report.group(1).split(',') if x.strip()}
        unknown = entries - TRUSTED_AXIOMS
        if unknown:
            raise UnrecognizedAxiomReport(
                f'Unapproved axiom dependencies for {theorem}: {sorted(unknown)}'
            )
        return entries
    noaxioms = re.search(
        rf"(?m)^\s*(?:['`\"])?{ident}(?:['`\"])?\s+does not depend on any axioms\s*$",
        stdout,
    )
    if noaxioms:
        return set()
    raise UnrecognizedAxiomReport(
        f'Missing exact `#print axioms {theorem}` report; refusing certification.'
    )

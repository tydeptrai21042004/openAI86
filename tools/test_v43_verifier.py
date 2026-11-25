#!/usr/bin/env python3
"""Test fail-closed orchestration with simulated subprocess responses.
These are Python unit tests, NOT simulated Lean proof certificates.
Temporary directories prevent mock outputs entering the project registry.
"""
import json
import tempfile
from pathlib import Path
from subprocess import CompletedProcess
import unittest
from unittest.mock import patch
import verify_v43_targets as v

class VerifierTests(unittest.TestCase):
    def run_case(self, responses, available=True):
        with tempfile.TemporaryDirectory() as d, patch.object(v, 'ROOT', Path(d)), \
            patch.object(v, 'source_hash', return_value='mock-only'), \
            patch.object(v.shutil, 'which', return_value='/mock' if available else None), \
            patch.object(v.subprocess, 'run', side_effect=responses) as run:
            rc=v.verify('3.1')
            result=json.loads((Path(d)/'verification/reports/V43/3.1/result.json').read_text())
            return rc,result,run.call_count
    def proc(self, code, out=''):
        return CompletedProcess([],code,stdout=out)
    def test_missing_tools(self):
        rc,s,c=self.run_case([],False)
        self.assertEqual((rc,c),(2,0)); self.assertFalse(s['paper_result_certified'])
    def test_build_error(self):
        rc,s,c=self.run_case([self.proc(1,'error')]); self.assertEqual((rc,c),(1,1))
        self.assertEqual(s['status'],'BUILD FAILED')
    def test_check_error(self):
        rc,s,c=self.run_case([self.proc(0),self.proc(1,'error')]); self.assertEqual((rc,c),(1,2))
    def test_missing_axiom_report(self):
        rc,s,_=self.run_case([self.proc(0),self.proc(0,'unrelated declaration')]); self.assertEqual(rc,1)
    def test_sorry_ax_rejected(self):
        rc,s,_=self.run_case([self.proc(0),self.proc(0,"'OpenAI086.v43_lemma31' depends on axioms: [sorryAx]\n")]); self.assertEqual(rc,1)
    def test_unapproved_axiom_rejected(self):
        rc,s,_=self.run_case([self.proc(0),self.proc(0,"'OpenAI086.v43_lemma31' depends on axioms: [Lean.ofReduceBool]\n")]); self.assertEqual(rc,1)
    def test_wrong_theorem_rejected(self):
        rc,s,_=self.run_case([self.proc(0),self.proc(0,"'Other' does not depend on any axioms\n")]); self.assertEqual(rc,1)
    def test_valid_report_does_not_promote_paper(self):
        rc,s,_=self.run_case([self.proc(0),self.proc(0,"'OpenAI086.v43_lemma31' depends on axioms: [propext, Classical.choice]\n")]); self.assertEqual(rc,0)
        self.assertFalse(s['paper_result_certified']); self.assertEqual(s['status'],'ENCODED STATEMENT KERNEL CHECKED')

if __name__=='__main__': unittest.main()

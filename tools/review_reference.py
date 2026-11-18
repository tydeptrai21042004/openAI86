#!/usr/bin/env python3
"""Read-only pre-merge audit of a third-party Lean proof archive.

This is NOT a Lean kernel verification or a guarantee of mathematical validity.
It intentionally writes no reference source into the independent Lean project.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
import zipfile

TARGETS = {
    'TrilinearHT/Auto/Prerequisites/RademacherMenshov.lean': [
        'theorem nestedProjectionProduct_prefix_rows',
        'theorem nestedProjectionProduct_successive_jumps',
    ],
    'TrilinearHT/Auto/Sec04ColumnProjections.lean': [
        'theorem columnSpatialCompression',
        'theorem columnSpatialCompression_complements',
    ],
    'TrilinearHT/Theorems.lean': [
        'theorem trilinear_ht_bound',
    ],
}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('zip', help='Path to the downloaded reference repository ZIP')
    parser.add_argument('--output', default='', help='Optional JSON output path')
    args = parser.parse_args()
    zpath = Path(args.zip)
    if not zpath.is_file():
        print(f'REFERENCE NOT FOUND: {zpath}', file=sys.stderr)
        raise SystemExit(2)
    findings = {'archive_name': zpath.name,
                'archive_sha256': hashlib.sha256(zpath.read_bytes()).hexdigest(),
                'evaluation': 'read_only_static_review_not_kernel_verification',
                'suggested_use': 'ideas_only; independent proofs; no import or code transplant',
                'checked': {}, 'issues': []}
    with zipfile.ZipFile(zpath) as z:
        names = z.namelist()
        def locate(suffix):
            matches = [n for n in names if n.endswith(suffix)]
            return matches[0] if len(matches) == 1 else None
        source = {}
        for suffix, expected in TARGETS.items():
            name = locate(suffix)
            if name is None:
                findings['issues'].append(f'Missing/ambiguous reference file: {suffix}')
                continue
            contents = z.read(name)
            txt = contents.decode('utf-8')
            source[suffix] = txt
            checks = {decl: bool(re.search(r'^\s*' + re.escape(decl) + r'\b', txt, re.M))
                      for decl in expected}
            findings['checked'][suffix] = {
                'sha256': hashlib.sha256(contents).hexdigest(),
                'line_count': len(txt.splitlines()), 'declarations': checks}
            findings['issues'].extend(f'{suffix}: missing {k}' for k, v in checks.items() if not v)
        tc = locate('lean-toolchain')
        if tc:
            findings['reference_toolchain'] = z.read(tc).decode().strip()
        license_name = locate('/LICENSE')
        findings['license_found'] = bool(license_name)
        if license_name:
            findings['reference_license_starts'] = z.read(license_name).decode()[:100].strip()
        lean_files = [n for n in names if n.endswith('.lean')]
        findings['lean_file_count'] = len(lean_files)
        findings['raw_source_number_of_axiom_declaration_lines'] = sum(
            len(re.findall(r'^\s*axiom\s+\w+', z.read(n).decode('utf-8','replace'), re.M))
            for n in lean_files)
        findings['raw_source_number_of_sorry_tokens'] = sum(
            len(re.findall(r'\bsorry\b', z.read(n).decode('utf-8','replace')))
            for n in lean_files)
        if findings['raw_source_number_of_axiom_declaration_lines']:
            findings['issues'].append('AXIOM-LIKE declarations detected; examine source manually')
        if findings['raw_source_number_of_sorry_tokens']:
            findings['issues'].append('sorry token detected; examine source manually')
    root = Path(__file__).resolve().parents[1]
    imported = []
    for own in root.rglob('*.lean'):
        owntext = own.read_text()
        imported += [(str(own.relative_to(root)), line) for line in owntext.splitlines()
                     if re.match(r'^\s*import\s+TrilinearHT(?:\.|$)', line)]
    findings['external_imports_in_independent_project'] = imported
    if imported: findings['issues'].append('Independent project imports reference proof source')
    findings['premerge_static_status'] = 'REVIEW' if findings['issues'] else 'CANDIDATE_IDEAS_ONLY'
    result = json.dumps(findings, ensure_ascii=False, indent=2)
    if args.output:
        Path(args.output).write_text(result+'\n', encoding='utf8')
    print(result)
    if findings['issues']:
        raise SystemExit(1)

if __name__ == '__main__':
    main()

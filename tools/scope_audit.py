#!/usr/bin/env python3
"""Independent static proof-inventory report. Never kernel certification."""
import json,re
from pathlib import Path
root=Path(__file__).resolve().parents[1]
files=sorted((root/'OpenAI086').rglob('*.lean'))+[root/'OpenAI086.lean',root/'OpenAI086Whole.lean']
lemmas=[]
for f in files:
 for n,line in enumerate(f.read_text('utf8').splitlines(),1):
  m=re.match(r'^theorem\s+(\S+)',line.strip())
  if m:lemmas.append({'file':str(f.relative_to(root)),'line':n,'name':m.group(1)})
source=json.loads((root/'verification/PAPER_RESULTS_INDEX.json').read_text())
items=source['results']
report={'audit_kind':'STATIC_ONLY_NOT_KERNEL_VERIFICATION',
        'lean_files':len(files),'theorem_declarations_in_sources':len(lemmas),
        'numbered_paper_results':len(items),
        'numbered_results_with_partial_components':sum(x['formalization']=='partial' for x in items),
        'numbered_full_results_kernel_verified':0,
        'main_theorem_kernel_verified':False,
        'external_published_lean_code_imported':False,
        'lean_kernel_build_executed_by_this_script':False,
        'additional_independent_modules':[
          'ArbitraryDepthTelescoping','OrderedProductTelescoping',
          'FiniteStoppingSets','FiniteMarginalCancellation',
          'PathLabelEnergy','QuadraticChartsElementary','EntryRankSummation',
          'ComponentIntersections','EntryRankConcrete','SparsePairBudget',
          'SparseBlockAccounting','ColoredPathUniqueness',
          'InterleavedGapBudget','FirstFailureFour',
          'BadDensityIncidence','PredictorEnergy',
          'BadDensityBudgetAssembly','NestedCoordinateProducts',
          'CommonGoodHeight','SparsePairObstruction','HeightBinsOneDim',
          'ConditionalMainTransfer', 'PairedKernelBound',
          'GlobalLipschitzCancellation', 'SchwartzSizeBridge',
          'FiniteAlignedProjectionBlocks','FiniteVariableProjectionBlocks',
          'FiniteBadPartnerPruning']}
(root/'verification/SCOPE_AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))

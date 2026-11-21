#!/usr/bin/env python3
"""Finite exact-arithmetic tests of three errata. Not a Lean proof."""
from itertools import product
from fractions import Fraction
import json
counts={"endpoint_counterexamples":0,"interleaved_chains":0,
        "predictor_identities":0,"first_failure_role_masks":0}
# Without P_N subset C_N, a negative terminal gap is possible.
p=[1,1];c=[1,0]
assert p[0] <= c[0] <= p[1] and not p[1] <= c[1]
counts['endpoint_counterexamples']+=1
# Valid interleaved log-cardinality gaps telescope exactly and are bounded by L.
for n in range(1,5):
  for vals in product(range(4),repeat=2*(n+1)):
    p=vals[:n+1]; c=vals[n+1:]
    if any(p[i]>c[i] for i in range(n+1)): continue
    if any(c[i]>p[i+1] for i in range(n)): continue
    lhs=sum(c[i]-p[i] for i in range(n+1))
    assert 0<=lhs<=c[n]-p[0]
    counts['interleaved_chains']+=1
# General predictor identity: each private input difference remains present.
for e,a0,a1,p0,p1 in product(range(3),repeat=5):
  # The square root is exact for eps in {0,1,4}.
  eps=[0,1,4][e];root=[0,1,2][e]
  lhs=(eps*a1-root*p1)-(eps*a0-root*p0)
  rhs=eps*(a1-a0)-root*(p1-p0)
  assert lhs==rhs
  counts['predictor_identities']+=1
# First failure: all preceding roles pass; later roles are unrestricted.
for n in (3,4):
  for bad in product((False,True),repeat=n):
    earliest=next((i for i,x in enumerate(bad) if x),None)
    for role in range(n):
      expected=bad[role] and all(not bad[k] for k in range(role))
      assert (earliest==role)==expected
      counts['first_failure_role_masks']+=1
print(json.dumps({'status':'finite_regression_only_not_kernel_verification','checks':counts},indent=2))

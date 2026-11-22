#!/usr/bin/env python3
"""Exhaustive finite test of V5 constructive dyadic prefix decomposition.

This reproduces the recursion in FiniteDyadicPrefixBlocks.lean;
it is a model check, not a Lean kernel proof.
"""
from fractions import Fraction as F
import json
# Fixed rational signal; prefix sums let us test large prefixes exactly
# without allocating a fresh O(n) Fraction array at every test case.
max_index=2**11+19
values=[F((7*j)%23-11,(j%5)+1) for j in range(max_index)]
prefix=[F(0)]
for v in values:
    prefix.append(prefix[-1]+v)

def blocks(k,start,n):
    if k==0:
        return [] if n==0 else [(start,1)]
    if n==2**k:
        return [(start,2**k)]
    if n<=2**(k-1):
        return blocks(k-1,start,n)
    return [(start,2**(k-1))]+blocks(k-1,start+2**(k-1),n-2**(k-1))

cases=0
powers=0
for k in range(12):
    for n in range(2**k+1):
        for start in (0,1,3,19):
            a=blocks(k,start,n)
            assert len(a) <= k+1
            assert sum(w for _,w in a)==n
            assert [j for s,w in a for j in range(s,s+w)] == list(range(start,start+n))
            assert len({w for _,w in a})==len(a)
            assert all(w>0 and w&(w-1)==0 for s,w in a)
            if start==0:
                assert all(s%w==0 for s,w in a)
                powers+=1
            block_total=sum((prefix[s+w]-prefix[s] for s,w in a),F(0))
            assert block_total==prefix[start+n]-prefix[start]
            cases+=1
print(json.dumps({'status':'PASS','prefix_compositions':cases,
                  'alignment_cases':powers,'max_k':11,'lean_kernel':'NOT_RUN'},indent=2))

#!/usr/bin/env python3
"""Exact integer/rational regression for new Section 8.6 height-lag proof.
Not a Lean kernel certificate. Also checks why B must be LINEAR in Lemma 3.3.
"""
from fractions import Fraction
from random import Random
import json, math
rng=Random(20261122)
counts={"height_lag_identities":0,"height_lag_budgets":0,"row_nonlinearity_counterexample":0}
for lag in range(0,15):
    for H in range(0,30):
        for _ in range(7):
            a=[rng.randint(-20,80) for i in range(H+lag+2)]
            lhs=sum(a[h+lag]-a[h] for h in range(H))
            rhs=sum(a[H+r]-a[r] for r in range(lag))
            assert lhs==rhs, (lag,H,lhs,rhs)
            counts['height_lag_identities']+=1
            # Boundary condition: p(r)>=0 and p(H+r)<=cap.
            cap=max([0]+[a[H+r] for r in range(lag)])
            for r in range(lag):
                a[r]=max(0,a[r])
                a[H+r]=min(a[H+r],cap)
            lhs=sum(a[h+lag]-a[h] for h in range(H))
            assert lhs<=lag*cap, (lag,H,lhs,cap)
            counts['height_lag_budgets']+=1
# Counterexample to an incorrectly typed old row-prefix target:
# d=T, x=(1,...,1), P_n projects onto first n coordinates.
# B_n(y)=||y|| if y==P_n x, else 0. All P_n x are distinct.
# The functions B_n are NOT linear but satisfy sum B_n(y)^2<=||y||^2.
T=512
lhs=sum(range(1,T+1))
log_envelope=(T+1).bit_length()-1+2  # Nat.log2(T+1)+2
rhs=log_envelope**2 * T
assert lhs>rhs, (lhs,rhs)
counts['row_nonlinearity_counterexample']=1
print(json.dumps({'kind':'exact_arithmetic_regression_not_kernel_proof',
 'checks':counts,'nonlinear_counterexample':{'T':T,'lhs':lhs,'rhs':rhs,
 'conclusion':'linear map type is required for valid Lemma 3.3'}},indent=2))

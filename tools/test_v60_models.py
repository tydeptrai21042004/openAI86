#!/usr/bin/env python3
"""Exact rational regression models; these are not Lean proofs."""
from fractions import Fraction as F
from random import Random
import json
rng=Random(60)
for _ in range(400):
    # p=1/2, integer square inputs; min-power with errors at power one
    vals=[rng.randint(0,100) for _ in range(rng.randint(1,12))]
    eta=rng.randint(0,100); err=F(rng.randint(0,100),7)
    a=sum(v*v for v in vals)+err
    assert min(eta*eta,a) <= eta*sum(vals)+err
for _ in range(400):
    # row and column group inequality with integer beta_i >= 1
    m=[[F(rng.randint(0,10),7) for _ in range(4)] for _ in range(3)]
    beta=[rng.randint(1,3) for _ in m]
    from math import prod
    assert sum(prod(m[i][j]**beta[i] for i in range(3)) for j in range(4)) <= prod(sum(row)**b for row,b in zip(m,beta))
for _ in range(400):
    # exact outer absorption C_N <= 1+K(A+c*C_N)
    K=F(rng.randint(1,100),7); A=F(rng.randint(0,100),11); c=1/(2*K)
    CN=(1+K*A)/(1-K*c)
    assert CN <= 2+2*K*A
c=F(1,2080); eps=c/2
assert c/(c-eps)==2 and 1-eps/c==F(1,2) and 2*eps*(1/c-1)==1-c
print(json.dumps({'kind':'exact_model_regressions_not_kernel_proofs','counts':{'minimum_with_errors':400,'group_product_integer_exponents':400,'outer_absorption':400,'paper_exponents':1},'total':1201},indent=2))

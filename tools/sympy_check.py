#!/usr/bin/env python3
"""Independent, non-formal algebraic smoke test. Not a Lean proof."""
import sympy as s
x,t,lam,beta,gamma=s.symbols('x t lam beta gamma', real=True)
w=[-1,3,-3,1]
for k in range(4):
    expr=s.expand(sum(w[j]*(x+j*t)**k for j in range(4)))
    expected=6*t**3 if k==3 else 0
    assert s.simplify(expr-expected)==0, (k,expr)
Q=lambda y:lam*y*y+beta*y+gamma
assert s.expand(sum(w[j]*Q(x+j*t) for j in range(4)))==0
for a,b in [(0,1),(1,2),(0,3),(2,3)]:
    yi,yj=x+a*t,x+b*t
    assert s.expand((b-a)*x-(b*yi-a*yj))==0
    assert s.expand((b-a)*t-(yj-yi))==0
print('SYMPY PASS: algebraic checks only (not a Lean build or analytic proof).')

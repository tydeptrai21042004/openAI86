#!/usr/bin/env python3
"""Deterministic exact finite checks; not a Lean kernel certificate."""
import random
from itertools import product
rng=random.Random(8142026)
cases=0
for nv in range(0,13):
  nodes=range(nv)
  for _ in range(200):
    degree=rng.randrange(nv+1)
    nbs={x:set(rng.sample(list(nodes),rng.randrange(min(degree,nv)+1))) for x in nodes}
    base=set(rng.sample(list(nodes),rng.randrange(nv+1)))
    current=base
    for t in range(6):
      assert len(current)<=((degree+1)**t)*len(base)
      nxt=current|set().union(*(nbs[x] for x in current)) if current else set()
      assert len(nxt)<=(degree+1)*len(current)
      assert current<=nxt
      current=nxt
      cases+=1

for _ in range(5000):
    a,b,c,d,da,db,dc,dd=(rng.randint(-10,10) for j in range(8))
    left=(a+da)*(b+db)*(c+dc)*(d+dd)-a*b*c*d
    right=(da*(b+db)*(c+dc)*(d+dd)+
       a*db*(c+dc)*(d+dd)+a*b*dc*(d+dd)+a*b*c*dd)
    assert left==right
    assert (a+da)*(b+db)*c*d == (a*b+da*b+a*db+da*db)*c*d
    cases+=2
print('V7 catalog + 4-slot exact integer tests: PASS',cases,'cases')

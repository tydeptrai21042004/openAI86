#!/usr/bin/env python3
"""Exact rational regressions for stopping and budget algebra, not Lean proofs."""
from fractions import Fraction as F
from random import Random
from math import ceil, log2
rng = Random(46)
path_count = budget_count = 0
for _ in range(1500):
    D = rng.randint(2, 32)
    G = 4*D**5
    # Positive and zero averages; finite chains with child average <= 2 parent.
    a = [F(rng.randint(0, 10), 3)]
    for i in range(rng.randrange(1, 90)):
        a.append(a[-1]*F(rng.randint(0, 8),4))
    root = 0
    path = [a[0]]
    for n in range(1,len(a)):
        assert a[n] <= 4*a[root]
        if a[n] > 2*a[root]:
            root = n
            path.insert(0,a[n])
        assert a[n] <= 2*a[root]
    M = max(a)
    assert path[0] == a[root]
    assert all(x >= 2*y for x,y in zip(path,path[1:]))
    assert sum(x*x for x in path) <= F(4,3)*M*M
    if M > 0:
        t = M/(G*D**2)
        low = sum(x for x in path if x < t)
        high = sum(x >= t for x in path)
        assert G*low <= 2*M/D**2
        if high:
            assert 2**(high-1) <= G*D**2
        # Integer comparison to an exact power, not a floating log check.
        assert high <= 1+(G*D**2).bit_length()-1
    path_count += 1
for _ in range(500):
    D = F(rng.randint(2,32)); L = F(rng.randint(1,100)); U = F(rng.randint(1,100)); Z = F(rng.randint(1,20),3)
    # arbitrary partitions of the upper energy budgets
    n = rng.randint(1,20)
    w = [F(rng.randint(1,100)) for _ in range(n)]; ws = sum(w)
    rep = [(8/D**2+L)*Z**2*x/ws for x in w]
    avg = [F(16,3)*Z**2*x/ws for x in w]
    rows = [4*U*r+4*D**(-20)*D**3*a for r,a in zip(rep,avg)]
    assert sum(rows) == (4*U*(8/D**2+L)+F(64,3)*D**(-17))*Z**2
    budget_count += 1
print(f'{path_count} exact stopping-path cases; {budget_count} exact budget-assembly cases passed. Not kernel certification.')

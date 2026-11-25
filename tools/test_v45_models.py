#!/usr/bin/env python3
"""Exact rational complex finite models; NOT verification of the Lean proofs."""
import random
import sympy as s

rng = random.Random(45086)

def c():
    return s.Rational(rng.randint(-3, 3), 2) + s.I*s.Rational(rng.randint(-3, 3), 3)

def zero(m):
    return all(s.simplify(x) == 0 for x in m)

def refit(M, z, W):
    if M.cols == 0:
        return s.zeros(M.rows, 1), s.zeros(0, 1)
    co = (M.conjugate().T*W*M).inv()*(M.conjugate().T*W*z)
    co = co.applyfunc(s.simplify)
    return (M*co).applyfunc(s.simplify), co

for _ in range(12):
    n = rng.randint(1, 3)
    m = rng.randint(2, 4)
    a = [s.Rational(rng.randint(1, 4), 3) for i in range(n)]
    phys = [[c() for i in range(n)] for x in range(m)]
    f = [c() for x in range(m)]
    w0 = [rng.randint(1, 5) for x in range(m)]
    w = [s.Rational(k, sum(w0)) for k in w0]
    M = s.Matrix([[phys[x][i] if k == 0 else (a[i] if k == i+1 else 0)
                   for i in range(n)] for x in range(m) for k in range(n+1)])
    W = s.diag(*[w[x] for x in range(m) for k in range(n+1)])
    z = s.Matrix([f[x] if k == 0 else 0 for x in range(m) for k in range(n+1)])
    g, co = refit(M, z, W)
    for i in range(n):
        moment = sum(w[x]*(f[x]-g[x*(n+1)])*s.conjugate(phys[x][i]) for x in range(m))
        assert s.simplify(moment-a[i]**2*co[i]) == 0
print('Scalar normal equation: 12 exact complex rational finite models passed')

for _ in range(12):
    m = 6
    W = s.diag(*[s.Rational(rng.randint(1, 5), 7) for x in range(m)])
    z = s.Matrix([c() for x in range(m)])
    # Each local space has one inherited column and one private additional
    # test, guaranteeing independence by nonzero first and last entries.
    cols = []
    g = s.zeros(m, 1)
    coarse = s.zeros(m, 1)
    for q in range(3):
        inherited = s.zeros(m, 1)
        inherited[2*q] = 1+c()*s.I
        if s.simplify(inherited[2*q]) == 0:
            inherited[2*q] = 1
        inherited[2*q+1] = c()
        additional = s.zeros(m, 1)
        additional[2*q+1] = 1
        M = s.Matrix.hstack(inherited, additional) if q % 2 == 0 else inherited
        local, _ = refit(M, z, W)
        g += local
        coarse += inherited
        cols.append(M)
    for M in cols:
        assert zero(M.conjugate().T*W*(g-z))
    assert zero(g.conjugate().T*W*g-z.conjugate().T*W*g)
    a, _ = refit(coarse, z, W)
    b, _ = refit(coarse, g, W)
    assert zero(a-b)
print('Disjoint-cut moments, energy and coarse refits: 12 exact complex rational finite models passed')

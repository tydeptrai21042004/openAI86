#!/usr/bin/env python3
"""Exact Fractions: V14 full-height Lemma 8.6 counting bridge.

Finite tests verify the mathematics used in the *candidate* Lean proofs,
not Lean elaboration or the trilinear Hilbert transform theorem.
"""
from fractions import Fraction as F
from functools import lru_cache
import random

rng = random.Random(20261123)
checks = dict(full_height_split=0, chronological_vertical=0,
              chronological_horizontal=0, pointwise_bound=0,
              aggregate_bound=0, absorbed=0, feasible=0, strict_numeric=0,
              level_energy=0, level_energy_sharp=0, split_edge=0,
              dyadic_unique_widths=0, dyadic_partition=0,
              dyadic_alignment=0, dyadic_same_width_separation=0)

@lru_cache(None)
def log_bin(n):
    k = 0
    while 11 ** (k + 1) <= n * 10 ** (k + 1):
        k += 1
        assert k < 10 * (n + 1)
    return k

def density(a, b):
    return F(len(a & b), len(b)) if b else F(0)

def harmonic(n):
    return sum((F(1, k) for k in range(1, n + 1)), F(0))

# Actual nested systems. A label enters a C-list one spatial position
# earlier than (or at the same time as) it enters the corresponding P-list.
# All labels use the same nondecreasing height threshold for both lists.
def trial(N, H, lag, M):
    total = H + lag
    births = [(rng.randrange(N + 2), rng.randrange(total + 1), rng.randrange(2))
              for _ in range(M)]
    def c(i,h):
        return {r for r,(pos,t,_) in enumerate(births) if i >= pos and h >= t}
    def p(i,h):
        return {r for r,(pos,t,delay) in enumerate(births) if i >= pos + delay and h >= t}
    for i in range(N+1):
        for h in range(total):
            assert p(i,h) <= c(i,h)
            if i < N: assert c(i,h) <= p(i+1,h)
            if h + 1 < total:
                assert p(i,h) <= p(i,h+1)
                assert c(i,h) <= c(i,h+1)
    # At most B position-exception events per primary, and A height-bad
    # events per primary per spatial position. Y is chosen independently
    # across the two axes, as the actual lemma permits.
    A, B = rng.randrange(0,4), rng.randrange(0,3)
    xpos = {r:set(rng.sample(range(N+1), k=min(B,N+1))) for r in range(M)}
    X = [{r for r in range(M) if i in xpos[r]} for i in range(N+1)]
    ypos = {(i,r):set(rng.sample(range(H),k=min(A,H)))
            for i in range(N+1) for r in range(M)}
    Y = [[{r for r in range(M) if h in ypos[i,r]} for h in range(H)]
         for i in range(N+1)]
    beta = rng.choice([F(1,10),F(1,3),F(1,2),F(2,3)])
    L = log_bin(M)
    HM = harmonic(M)
    bad_after, full_bad = [], []
    vbud, hbud = [], [F(0) for _ in range(H)]
    for i in range(N+1):
        bb, vb = [], F(0)
        for h in range(H):
            old = p(i,h)
            new = p(i,h+lag)
            ch = c(i,h+lag)
            xi, yi = X[i], Y[i][h]
            py = density(yi,ch); px = density(xi,ch)
            bad = int(log_bin(len(old)) != log_bin(len(ch)) or
                      density(xi|yi,ch) > beta)
            gap = (log_bin(len(new)) - log_bin(len(old)) +
                   log_bin(len(ch)) - log_bin(len(new)))
            assert F(bad) <= gap + (py + px)/beta
            checks['pointwise_bound'] += 1
            vb += (log_bin(len(new))-log_bin(len(old))) + py/beta
            hbud[h] += (log_bin(len(ch))-log_bin(len(new))) + px/beta
            bb.append(bad)
        vbud.append(vb)
        bad_after.append(bb)
        full_bad.append([1]*lag + bb)
        assert sum(full_bad[-1]) == lag + sum(bb)
        checks['full_height_split'] += 1
        assert sum(F(len(Y[i][h]&c(i,h+lag)),len(c(i,h+lag)))
                   if c(i,h+lag) else F(0) for h in range(H)) <= A*HM
        checks['chronological_vertical'] += 1
    for h in range(H):
        assert sum(density(X[i],c(i,h+lag)) for i in range(N+1)) <= B*HM
        checks['chronological_horizontal'] += 1
    Q = lag*L + A*HM/beta
    R = L + B*HM/beta
    assert all(v <= Q for v in vbud)
    assert all(v <= R for v in hbud)
    assert sum(map(sum,bad_after)) <= (N+1)*Q+H*R
    checks['aggregate_bound'] += 1
    for delta in [F(1,8),F(1,4),F(1,2),F(3,4)]:
        if 2*(lag+Q) <= delta*total and all(sum(b)>=delta*total for b in full_bad):
            assert F(N+1) <= 2*R/delta
            checks['absorbed'] += 1
        if 2*(lag+Q) <= delta*total and all(sum(b)>delta*total for b in full_bad):
            assert F(N+1) < 2*R/delta
            checks['strict_numeric'] += 1

for M in range(1,9):
    for N in range(0,5):
        for H in range(1,12):
            for lag in range(0,4):
                for _ in range(6):
                    trial(N,H,lag,M)

# Construct a non-vacuous case satisfying both the full bad-height
# density and the manuscript's quantitative absorption constraint.
for lag in range(1,5):
    M=1; N=0; H=100; beta=F(1,2); A=0; B=1; delta=F(1,2)
    L=log_bin(M); HM=harmonic(M)
    total=H+lag; Q=lag*L+A*HM/beta; R=L+B*HM/beta
    bad=[1]*total  # X_0={0}, C_0={0}, Y empty, P=C constant.
    assert 2*(lag+Q) <= delta*total
    assert sum(bad)>delta*total
    assert N+1<2*R/delta
    checks['feasible']+=1


# Independent scalar version of the layer-energy inequality used in
# the binary-prefix Rademacher–Menshov assembly for Lemma 3.3.
for L in range(0,10):
    for Rr in range(0,9):
        for _ in range(500):
            rows=[[F(rng.randint(-6,6),rng.randint(1,6)) for _ in range(L)]
                  for _ in range(Rr)]
            E=max((sum(row[l]**2 for row in rows) for l in range(L)),default=F(0))
            lhs=sum((sum(row)**2 for row in rows),F(0))
            assert lhs <= L*L*E
            checks['level_energy']+=1
for L in range(1,15):
    # Equality for one row containing the same scalar in every level.
    E=F(25,9)
    assert (L*F(5,3))**2 == L*L*E
    checks['level_energy_sharp']+=1
for H in range(0,15):
    for lag in range(0,15):
        f=[F(rng.randint(-10,10),rng.randint(1,10)) for _ in range(H)]
        full=[F(1) if t<lag else f[t-lag] for t in range(H+lag)]
        assert sum(full,F(0))==lag+sum(f,F(0))
        checks['split_edge']+=1


# Match the repository's recursive dyadic prefix constructor. This is
# the missing one-block-per-length structural invariant required to
# turn a variable prefix into a sum over at most k+1 Bessel levels.
def dyadic_blocks(k, start, length):
    if k == 0:
        return [] if length == 0 else [(start, 1)]
    if length == 2**k:
        return [(start, 2**k)]
    if length <= 2**(k-1):
        return dyadic_blocks(k-1, start, length)
    return [(start, 2**(k-1))] + dyadic_blocks(
        k-1, start+2**(k-1), length-2**(k-1))

for k in range(0,12):
    for length in range(0,2**k+1):
        for start in [0, 7, 2**k+11]:
            blocks=dyadic_blocks(k,start,length)
            widths=[w for _,w in blocks]
            assert len(widths)==len(set(widths))
            assert len(widths)<=k+1
            assert all(0<w<=length and w&(w-1)==0 for w in widths)
            checks['dyadic_unique_widths']+=1
            x=start
            for a,w in blocks:
                assert a==x
                x+=w
            assert x==start+length
            checks['dyadic_partition']+=1


# Shared aligned dyadic grid: start at a multiple of the largest width.
# At a fixed width, two different block starts must be separated by
# at least that width. No computational check replaces a Lean proof.
for k in range(0,12):
    level_grid={}
    for length in range(0,2**k+1):
        for start in [0,2**k,3*2**k]:
            for a,w in dyadic_blocks(k,start,length):
                assert a%w==0
                checks['dyadic_alignment']+=1
                level_grid.setdefault(w,set()).add(a)
    for w, starts in level_grid.items():
        ordered=sorted(starts)
        for a,b in zip(ordered,ordered[1:]):
            assert a+w<=b
            checks['dyadic_same_width_separation']+=1

print('V14 exact full-window counting tests PASS', checks,
      'total=',sum(checks.values()),'(NOT Lean kernel verification)')

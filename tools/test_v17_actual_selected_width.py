#!/usr/bin/env python3
"""Exact rational checks of the V17 bounded dyadic block selector.

These are **models**, not Lean elaboration. No tests are counted as
proofs of the paper; no numerical rounding is used.
"""
from itertools import product
import os
FAST = os.environ.get("V17_FAST", "0") == "1"
from random import Random
from test_v15_actual_projection_blocks import (
    Q, Z, pmat, paper_block, blocks, mv, add, row_eval, e,
    matmul,
)

rng = Random(171803)
checks = 0

def check(ok, label):
    global checks
    if not ok:
        raise AssertionError(label)
    checks += 1

def select(k, n, width):
    choices = [(s,w) for s,w in blocks(k, 0, n+1) if w==width]
    check(len(choices)<=1, (k,n,width,'duplicate width'))
    if not choices:
        return False, 0
    s,w = choices[0]
    check(s+w<=n+1,(k,n,width,'outside prefix'))
    check(s%w==0,(k,n,width,'unaligned'))
    b=s//w
    check(b < 2**k,(k,n,width,b,'Fin index overflow'))
    return True,b

# Every possible selected block across a wide range of depths and widths.
for k in range(0,7 if FAST else 9):
    for n in range(1<<k):
        bs=blocks(k,0,n+1)
        check(sum(w for s,w in bs)==n+1,(k,n,'coverage'))
        check(len(bs)<=k+1,(k,n,'logarithmic number of widths'))
        for width in [1<<j for j in range(k+1)]+[0,3,7]:
            active, b=select(k,n,width)
            check((not active or b < (1<<k)),(k,n,width,'finite choice'))
            if k <= (4 if FAST else 5):
                for layer in range(4):
                    actual=Z
                    for s,w in bs:
                        if w==width:
                            actual=add(actual,paper_block(layer,w,s//w))
                    selected=paper_block(layer,width,b) if active else Z
                    check(actual==selected,(k,n,width,layer,'selected operator'))

vectors=[tuple(Q(t) for t in z) for z in
         [(1,-2,3),(0,1,0),(1,0,0),(1,1,1),(2,3,-4)]]

# ONE WIDTH: independently selected prefix depth in each row; the exact
# row-Bessel constant is 1, even though the row masks differ.
for k in range(0,5 if FAST else 6):
    for layer in range(4):
        for width in [1<<j for j in range(k+1)]:
            for trial in range(20 if FAST else 75):
                depths=[rng.randrange(1<<k) for _ in range(3)]
                x=rng.choice(vectors)
                lhs=Q(0)
                for row,n in enumerate(depths):
                    active,block=select(k,n,width)
                    y=mv(paper_block(layer,width,block),x) if active else (Q(0),)*3
                    lhs+=row_eval(row,y)**2
                check(lhs<=e(x), (k,layer,width,depths,'fixed-width Bessel'))

# Full ONE-LAYER logarithmic bound using the *sum* over all widths.
for k in range(0,6 if FAST else 7):
    for layer in range(4):
        for trial in range(30 if FAST else 100):
            depths=[rng.randrange(1<<k) for _ in range(3)]
            x=rng.choice(vectors)
            vals=[]
            for row,n in enumerate(depths):
                summed=Q(0)
                for width in [1<<j for j in range(k+1)]:
                    active,block=select(k,n,width)
                    if active:
                        summed+=row_eval(row,mv(paper_block(layer,width,block),x))
                direct=row_eval(row,mv(pmat(layer,n),x))
                check(summed==direct,(k,layer,depths,row,'linear sum'))
                vals.append(direct)
            check(sum((v*v for v in vals),Q(0))<=Q((k+1)**2)*e(x),
                  (k,layer,depths,'one-layer logarithmic bound'))

# Multiple ordered layers, with masks from the same bounded selector.
# This confirms the bounded-index bridge is not restricted to m=1.
for k in range(1,4 if FAST else 5):
    widths=[1<<j for j in range(k+1)]
    for m in (2,3,4):
        for trial in range(4 if FAST else 9):
            depths=[[rng.randrange(1<<k) for _ in range(m)] for _ in range(3)]
            x=rng.choice(vectors)
            for row in range(3):
                direct=x
                for layer,n in enumerate(depths[row]):
                    direct=mv(pmat(layer,n),direct)
                expanded=(Q(0),Q(0),Q(0))
                for word in product(widths,repeat=m):
                    selections=[select(k,depths[row][layer],w)
                                for layer,w in enumerate(word)]
                    if not all(active for active,b in selections):
                        continue
                    y=x
                    for layer,((active,b),w) in enumerate(zip(selections,word)):
                        y=mv(paper_block(layer,w,b),y)
                    expanded=tuple(expanded[i]+y[i] for i in range(3))
                check(direct==expanded,(k,m,row,'ordered masked expansion'))

# Independent width-tuple enumeration: every m-tuple appears once,
# including the empty (identity) product, with the exact count (k+1)^m.
for k in range(7):
    alphabet=[1<<j for j in range(k+1)]
    for m in range(5):
        words=list(product(alphabet, repeat=m))
        check(len(words)==(k+1)**m,(k,m,'word cardinality'))
        check(len(set(words))==len(words),(k,m,'unique width tuples'))
        if m==0:
            check(words==[()],(k,m,'empty product'))

check(matmul(pmat(1,0),pmat(2,0))!=matmul(pmat(2,0),pmat(1,0)),
      'projections commute unexpectedly')
print(f'V17 bounded selection / one-layer bound: {checks:,} exact rational checks PASSED')
print('Checks are only mathematical models; Lean kernel compilation is not available.')

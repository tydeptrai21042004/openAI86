#!/usr/bin/env python3
"""Exact rational regression of V16's NEW common-width algebraic bridge.

These tests independently evaluate the mathematical identities in the new
Lean source. They are not kernel compilation or manuscript certification.
"""
from fractions import Fraction as F
from itertools import product
from random import Random
from test_v15_actual_projection_blocks import (
    Q, I, Z, pmat, prep, delta, block_sum, paper_block, blocks, matmul,
    mv, add, row_eval, e
)

R = Random(160333)
checks=0

def record(ok, description):
    global checks
    assert ok, description
    checks += 1

def dwidths(k): return {1 << j for j in range(k + 1)}

def grouped(layer,k,n):
    # n denotes last included increment, so the prefix length is n+1.
    width_set=dwidths(k)
    pieces={w: Z for w in width_set}
    selected=blocks(k,0,n+1)
    record(sum(w for s,w in selected)==n+1,(layer,k,n,'covered'))
    record(len({w for s,w in selected})==len(selected),(layer,k,n,'unique widths'))
    for s,w in selected:
        record(w in width_set,(n,s,w,'member'))
        record(s%w==0,(n,s,w,'aligned'))
        record(block_sum(layer,s,w)==paper_block(layer,w,s//w), (layer,s,w,'projection block'))
        pieces[w]=add(pieces[w],block_sum(layer,s,w))
    for w in width_set-set(w for s,w in selected):
        record(pieces[w]==Z,(layer,k,n,w,'zero if absent'))
    got=Z
    for w in width_set:got=add(got,pieces[w])
    record(got==pmat(layer,n), (layer,k,n,'recovered prefix'))
    return pieces

def apply_grouped_ordered(layer, depths, k, x):
    y=x
    for i in range(layer):
        groups=grouped_cache[(i,k,depths[i])]
        total=(Q(0),Q(0),Q(0))
        for w in dwidths(k):
            piece=mv(groups[w],y)
            total=tuple(total[j]+piece[j] for j in range(3))
        y=total
    return y

# Every N from 0 to 2^k-1, including P0 and all binary carries.
grouped_cache={}
for k in range(7):
    for n in range(1<<k):
        for layer in range(4):
            grouped_cache[(layer,k,n)]=grouped(layer,k,n)

record(pmat(0,0)!=Z,'Initial P0 must be nonzero')
record(grouped_cache[(0,3,0)][1]==pmat(0,0),'P0 occurs in width-one block')
record(blocks(4,0,1)!=blocks(4,0,2),'Different rows require different width sets')

vectors=[tuple(Q(v) for v in xs) for xs in
         [(1,-2,3), (2,0,-1), (1,1,1), (-4,2,5), (0,1,0)]]

# Different rows and even different layers may select independent depths.
for k in range(1,7):
    for m in (1,2,3,4):
        for _ in range(45):
            depths=[R.randrange(1<<k) for i in range(m)]
            x=R.choice(vectors)
            y=x
            for i in range(m):y=mv(pmat(i,depths[i]),y)
            got=apply_grouped_ordered(m,depths,k,x)
            record(y==got,('row-specific ordered grouping',k,m,depths))

# Explicit nested width-tuple expansion for m=1..4, where zero widths
# are allowed and the multiplication order is deliberately noncommuting.
for k in range(0,4):
    widths=sorted(dwidths(k))
    for m in (1,2,3,4):
        # bound the naive cartesian product to keep exact arithmetic fast
        for _ in range(20):
            ns=[R.randrange(1<<k) for i in range(m)]
            x=R.choice(vectors)
            expanded=(Q(0),Q(0),Q(0))
            for word in product(widths,repeat=m):
                y=x
                for i,w in enumerate(word):
                    y=mv(grouped_cache[(i,k,ns[i])][w],y)
                expanded=tuple(expanded[j]+y[j] for j in range(3))
            direct=x
            for i in range(m):direct=mv(pmat(i,ns[i]),direct)
            record(expanded==direct,('full word expansion',k,m,ns))

# The exact bridge from a row-width group to its zero mask and ONE
# aligned block index. This is a finite model of the pending Lean glue.
for k in range(1,6):
    widths=sorted(dwidths(k))
    for m in (1,2,3,4):
        for _ in range(60):
            prefix=[R.randrange(1<<k) for _ in range(3)]
            x=R.choice(vectors)
            direct=Q(0)
            assembled=Q(0)
            for row in range(3):
                y=x
                for i in range(m):y=mv(pmat(i,prefix[row]),y)
                direct+=row_eval(row,y)
            # Sum over WIDTH TUPLES, not list positions. A missing width
            # in any layer activates a zero mask for that entire word.
            # Each row may make its own independent choice.
            for word in product(widths, repeat=m):
                for row in range(3):
                    chosen=[next(((s//w) for s,w0 in blocks(k,0,prefix[row]+1)
                                  if w0==w),None) for w in word]
                    if any(b is None for b in chosen):
                        contribution=Q(0)
                    else:
                        y=x
                        for i,(w,b) in enumerate(zip(word,chosen)):
                            y=mv(paper_block(i,w,b),y)
                        contribution=row_eval(row,y)
                    assembled+=contribution
            record(assembled==direct,('mask/group/row linear output',k,m,prefix))

# Sharp fixed-width zero-mask Bessel and K² level assembly.
for m in (1,2,3,4):
    for K in range(1,5):
        for _ in range(100):
            x=R.choice(vectors)
            widths=[[R.randrange(1,7) for i in range(m)] for a in range(K)]
            choices=[[[R.randrange(4) for i in range(m)] for row in range(3)]
                     for a in range(K)]
            active=[[R.choice((True,False)) for row in range(3)] for a in range(K)]
            sums=[Q(0)]*3
            for a in range(K):
                energy=Q(0)
                for row in range(3):
                    if not active[a][row]:
                        continue
                    y=x
                    for i in range(m):
                        y=mv(paper_block(i,widths[a][i],choices[a][row][i]),y)
                    value=row_eval(row,y)
                    energy+=value*value
                    sums[row]+=value
                record(energy<=e(x),('masked tuple Bessel',m,K,a))
            record(sum((y*y for y in sums),Q(0))<=K*K*e(x),
                   ('masked multilevel Bessel',m,K))

# A finite-model check of the target row-prefix inequality. The theorem
# itself is NOT claimed Lean-proved until both Bessel and reindexing compile.
for m in (1,2,3,4):
    for k in range(1,7):
        for _ in range(60):
            nchoice=[R.randrange(1<<k) for row in range(3)]
            x=R.choice(vectors)
            total=Q(0)
            for row in range(3):
                y=x
                for i in range(m):y=mv(pmat(i,nchoice[row]),y)
                total+=row_eval(row,y)**2
            record(total<=F((k+1)**(2*m))*e(x),('row bound',m,k,nchoice,total))

# A genuinely noncommuting pair of layers is covered in the tests.
record(matmul(pmat(1,0),pmat(2,0)) != matmul(pmat(2,0),pmat(1,0)),
       'noncommutativity must be nontrivial')
print(f'V16 common-width grouping: {checks:,} exact rational checks PASSED')
print('Scope: width support, uniqueness, alignment, P0 inclusion,')
print('       row/layer-dependent depths, ordered m-layer distribution,')
print('       finite-model log inequality (NOT a Lean certificate).')

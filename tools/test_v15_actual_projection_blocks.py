#!/usr/bin/env python3
"""V15 exact Fraction regression for dyadic projection blocks.

Checks mathematical *models*, not Lean theorems. Every entry and inequality
is computed with Fractions (not floating point).  We use different rational
orthogonal bases across layers, hence genuinely noncommuting projectors.
"""
from fractions import Fraction as F
from itertools import product
from random import Random

r=Random(866815)
Q=lambda a,b=1: F(a,b)
I=[[Q(i==j) for j in range(3)] for i in range(3)]
Z=[[Q(0) for j in range(3)] for i in range(3)]

# Rational orthogonal rotations in different coordinate planes.
A=[[Q(3,5),Q(-4,5),Q(0)],[Q(4,5),Q(3,5),Q(0)],[Q(0),Q(0),Q(1)]]
C=[[Q(1),Q(0),Q(0)],[Q(0),Q(5,13),Q(-12,13)],[Q(0),Q(12,13),Q(5,13)]]

def matmul(a,b):return [[sum((a[i][k]*b[k][j] for k in range(3)),Q(0)) for j in range(3)] for i in range(3)]
def mv(a,x):return tuple(sum((a[i][k]*x[k] for k in range(3)),Q(0)) for i in range(3))
def tr(a):return [list(z) for z in zip(*a)]
def sub(a,b):return [[a[i][j]-b[i][j] for j in range(3)] for i in range(3)]
def add(a,b):return [[a[i][j]+b[i][j] for j in range(3)] for i in range(3)]
def vdot(x,y):return sum((x[i]*y[i] for i in range(3)),Q(0))
def sq(x):return vdot(x,x)

bases=[I,A,C,matmul(A,C)]
for U in bases:
    assert matmul(tr(U),U)==I

def pmat(layer,n):
    U=bases[layer]
    rk=min(3,1+n//2) # P0 is NONZERO, to detect the missing-initial-term bug
    return matmul(matmul(U,[[Q(i==j and j<rk) for j in range(3)] for i in range(3)]),tr(U))

def prep(layer,n):return Z if n==0 else pmat(layer,n-1)
def delta(layer,k):return pmat(layer,0) if k==0 else sub(pmat(layer,k),pmat(layer,k-1))
def block_sum(layer,start,width):
    out=Z
    for k in range(start,start+width):out=add(out,delta(layer,k))
    return out

def paper_block(layer,width,idx):return sub(prep(layer,(idx+1)*width),prep(layer,idx*width))
def e(x):return sq(x)

def blocks(k,start,n):
    if k==0:return [] if n==0 else [(start,1)]
    if n==2**k:return [(start,2**k)]
    if n<=2**(k-1):return blocks(k-1,start,n)
    return [(start,2**(k-1))]+blocks(k-1,start+2**(k-1),n-2**(k-1))

# Orthogonal row map: B_r(x) is the r-th coordinate in basis U.
B=bases[3]
def row_eval(idx,x):return vdot(tuple(B[i][idx] for i in range(3)),x)

def test():
    checks=0
    vectors=[tuple(map(Q,x)) for x in [(1,2,-1),(3,-2,0),(1,0,0),(0,1,0),(0,0,1),(1,1,1),(-3,2,4)]]
    for layer in range(4):
        for n in range(17):
            P=pmat(layer,n)
            assert matmul(P,P)==P and tr(P)==P
            if n<16:
                assert matmul(P,pmat(layer,n+1))==P
            checks+=3
        for width in range(1,9):
            for idx in range(8):
                assert block_sum(layer,idx*width,width)==paper_block(layer,width,idx)
                checks+=1
            for cnt in range(9):
                for x in vectors:
                    lhs=sum((e(mv(paper_block(layer,width,i),x)) for i in range(cnt)),Q(0))
                    assert lhs<=e(x)
                    # Exact energy telescoping with the zero-augmented family.
                    assert lhs==e(mv(prep(layer,cnt*width),x))
                    checks+=2
    assert paper_block(1,1,0)==pmat(1,0)
    assert sub(pmat(1,1),pmat(1,0))!=pmat(1,0)
    checks+=2
    for n in range(0,65):
        k=max(0,(n-1).bit_length())
        bs=blocks(k,0,n)
        assert sum(w for _,w in bs)==n
        assert len({w for _,w in bs})==len(bs)
        for s,w in bs:assert s%w==0
        for layer in range(3):
            lhs=Z
            for s,w in bs:lhs=add(lhs,block_sum(layer,s,w))
            assert lhs==prep(layer,n)
            checks+=len(bs)+3
    # One family; all row-dependent prefix decisions (exact, not sampled).
    for layer in range(4):
        for T in range(0,8):
            L=1+T.bit_length() # 1 + ceil(log2(T+1))
            for choices in product(range(T+1),repeat=3):
                for x in vectors[:3]:
                    lhs=sum((row_eval(j,mv(pmat(layer,choices[j]),x))**2 for j in range(3)),Q(0))
                    assert lhs<=L**2*e(x)
                    checks+=1
    # Noncommuting products: each layer has its own width and block index.
    for m in (2,3,4):
        for test_id in range(900):
            x=r.choice(vectors)
            widths=[r.randint(1,8) for i in range(m)]
            picks=[[r.randrange(6) for i in range(m)] for j in range(3)]
            def word(j):
                y=x
                for i in range(m): y=mv(paper_block(i,widths[i],picks[j][i]),y)
                return y
            lhs=sum((row_eval(j,word(j))**2 for j in range(3)),Q(0))
            assert lhs<=e(x), (m,widths,picks,lhs,e(x))
            checks+=1
    # Actual level-sum assembly: each level has its own independently
    # chosen width tuple, and the row operator sees the SUM of outputs.
    for m in (1,2,3):
        for K in range(1,5):
            for test_id in range(240):
                x=r.choice(vectors)
                widths=[[r.randint(0,7) for _ in range(m)] for a in range(K)]
                picks=[[[r.randrange(5) for _ in range(m)] for _ in range(3)]
                       for a in range(K)]
                total=Q(0)
                for j in range(3):
                    value=Q(0)
                    for a in range(K):
                        y=x
                        for i in range(m):
                            y=mv(paper_block(i,widths[a][i],picks[a][j][i]),y)
                        value+=row_eval(j,y)
                    total+=value**2
                assert total<=K**2*e(x)
                checks+=1
    # Independent finite MODEL of the still-open Lean hdecomp:
    # distribute actual per-layer dyadic prefix block lists across
    # the ordered noncommuting product. This checks the full algebra
    # but does NOT substitute for a Lean theorem with typed tuple levels.
    for m in (1,2,3):
        for n in range(24):
            size=n+1
            k=(size-1).bit_length()
            choices=blocks(k,0,size)
            for x in vectors[:4]:
                model=(Q(0),Q(0),Q(0))
                for tup in product(choices,repeat=m):
                    y=x
                    for i,(start,width) in enumerate(tup):
                        y=mv(block_sum(i,start,width),y)
                    model=tuple(model[j]+y[j] for j in range(3))
                target=x
                for i in range(m):target=mv(pmat(i,n),target)
                assert model==target,(m,n,model,target)
                checks+=1
    # Verify noncommutation is non-vacuous for the chosen bases.
    assert matmul(pmat(1,0),pmat(2,0))!=matmul(pmat(2,0),pmat(1,0))
    checks+=1
    print(f'V15 exact rational projection-block checks PASSED: {checks:,}')
    print('Tested P0 inclusion, all projection axioms, dyadic identities,')
    print('fixed-width Bessel, m=1 log bounds, and noncommuting products.')

if __name__=='__main__':test()

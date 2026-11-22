#!/usr/bin/env python3
"""Exact integer tests for V7 algebra; NOT a Lean-kernel certificate.

A deterministic test for noncommutative ordered expansion, operator
increments, dyadic-prefix exactness, and the O(log N) block budget.
"""
import random

R = random.Random(2601122)
DIM = 3
I = tuple(tuple(int(i == j) for j in range(DIM)) for i in range(DIM))
Z = tuple(tuple(0 for j in range(DIM)) for i in range(DIM))

def add(a,b): return tuple(tuple(a[i][j]+b[i][j] for j in range(DIM)) for i in range(DIM))
def sub(a,b): return tuple(tuple(a[i][j]-b[i][j] for j in range(DIM)) for i in range(DIM))
def mm(a,b): return tuple(tuple(sum(a[i][z]*b[z][j] for z in range(DIM)) for j in range(DIM)) for i in range(DIM))
def sum_m(xs):
    y=Z
    for x in xs:y=add(y,x)
    return y

def random_mat():
    return tuple(tuple(R.randint(-3,3) for j in range(DIM)) for i in range(DIM))

def blocks(k,start,length):
    if k==0:return [] if length==0 else [(start,1)]
    if length==2**k:return [(start,2**k)]
    if length<=2**(k-1):return blocks(k-1,start,length)
    return [(start,2**(k-1))]+blocks(k-1,start+2**(k-1),length-2**(k-1))

def operator_prefix(p,n,k):
    inc=[p[0]]+[sub(p[j],p[j-1]) for j in range(1,n+1)]
    seq=blocks(k,0,n+1)
    return sum_m(sum_m(inc[st:st+w]) for st,w in seq),seq

def ordered_prod(ms):
    out=I
    for m in ms:out=mm(m,out)
    return out

def expanded_prod(levels):
    # Sum over all block words in the original layer order.
    words=[I]
    for layer in levels:
        words=[mm(b,w) for w in words for b in layer]
    return sum_m(words)

cases=0
# Exact operator identities with arbitrary (not even projection) matrices.
for k in range(8):
    for n in range(2**k):
        for _ in range(5):
            p=[random_mat() for _ in range(n+1)]
            got,segments=operator_prefix(p,n,k)
            assert got==p[n],(k,n,segments)
            assert len(segments)<=k+1
            assert sorted(set(w for _,w in segments))==sorted(w for _,w in segments)
            assert sum(w for _,w in segments)==n+1
            assert all(w&(w-1)==0 and st%w==0 for st,w in segments)
            cases+=1

# Noncommutativity matters: never permute the order of the layers.
for nlayer in range(0,6):
    for _ in range(600):
        levels=[[random_mat() for _ in range(R.randint(1,4))] for _ in range(nlayer)]
        got=ordered_prod([sum_m(L) for L in levels])
        want=expanded_prod(levels)
        assert got==want
        cases+=1

# Combined actual dyadic blocks and noncommuting ordered product.
for _ in range(3000):
    k=R.randint(1,5)
    nlayer=R.randint(0,4)
    levels=[]
    targets=[]
    for _i in range(nlayer):
        n=R.randrange(2**k)
        p=[random_mat() for _ in range(n+1)]
        final,bs=operator_prefix(p,n,k)
        assert final==p[n]
        ds=[p[0]]+[sub(p[j],p[j-1]) for j in range(1,n+1)]
        levels.append([sum_m(ds[st:st+w]) for st,w in bs])
        targets.append(p[n])
    assert ordered_prod(targets)==expanded_prod(levels)
    cases+=1

# A simple deterministic noncommutation witness.
A=((1,1,0),(0,1,0),(0,0,1))
B=((1,0,0),(1,1,0),(0,0,1))
assert mm(A,B)!=mm(B,A)
print('V7 exact noncommutative/dyadic operator tests: PASS',cases,'cases')

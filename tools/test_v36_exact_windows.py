#!/usr/bin/env python3
"""Independent exact Fraction regression for dyadic-window and family semantics.
This is not a proof or a substitute for Lean kernel execution.
"""
from fractions import Fraction as F
from itertools import product, combinations

def p2(k):
    return F(2)**k

def test_windows():
    count = 0
    for r,v,l,a,b in product([-120,-7,0,4,120],[-150,-8,0,3,150],[1,2],[-5,0,7],[-5,0,7]):
        if a>b: continue
        # ceil/floor on exact rational logarithms, no floating approximation
        lo=F(l*r+v-b,l); hi=F(l*r+v-a,l)
        nlo=-((-lo.numerator)//lo.denominator); nhi=hi.numerator//hi.denominator
        actual={n for n in range(nlo-3,nhi+4) if p2(a)<=p2(l*(r-n)+v)<=p2(b)}
        assert actual==set(range(nlo,nhi+1))
        count+=1
    return count

def test_families():
    values=[F(0), F(1,3),F(1),F(5),p2(150)]
    families=[set(s) for k in range(len(values)+1) for s in combinations(values,k)]
    count=0
    for fam in [[],[set()],families,families[1::3],families[::2]]:
        sup=[max(s|{F(0)}) for s in fam]
        E={v for v in sup if v>0}
        assert E<=set(values)
        for n,l,eps in product([-155,-3,0,4,155],[1,2],[F(0),F(1,3),F(1),p2(160)]):
            scale=p2(-n*l)
            m=max({F(0)}|{scale*v for v in E if scale*v<=eps})
            assert m==max({F(0)}|{scale*v for v in sup if scale*v<=eps})
            for bound in [F(-1),F(0),m,m+1]:
                assert (m<=bound)==(0<=bound and all(scale*v<=bound for v in sup if scale*v<=eps))
                count+=1
    return count

if __name__=='__main__':
    a,b=test_windows(),test_families()
    print(f'Exact Fraction model cases: windows={a}, family upper bounds={b}, total={a+b}; all passed. NOT a kernel certificate.')

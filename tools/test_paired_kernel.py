#!/usr/bin/env python3
"""Numerical regression for the new O(1) paired-kernel lemma.

These are diagnostics, never Lean proof certificates.  Uses complex-valued
Schwartz factors f_j(y)=c_j exp(-a_j y²) exp(i b_j y).
"""
import cmath, math, random, sys
random.seed(20261121)

def factor(c,a,b,y):
    return c * math.exp(-a*y*y) * cmath.exp(1j*b*y)

cases=0
worst=0.0
for trial in range(48):
    configs=[]
    for j in range(3):
        re=random.uniform(-1.1,1.1); im=random.uniform(-1.1,1.1)
        a=random.uniform(.18,2.0); b=random.uniform(-4.2,4.2)
        configs.append((complex(re,im),a,b))
    M=max(abs(c) for c,a,b in configs)
    # Sup norm of gaussian derivative, using |f'| <= |c|(sqrt(2a/e)+|b|).
    Ks=[abs(c)*(math.sqrt(2*a/math.e)+abs(b)) for c,a,b in configs]
    B=(2*Ks[0]+4*Ks[1]+6*Ks[2])*M*M
    for k in range(125):
        t=(1 if random.random()<.5 else -1)*10**random.uniform(-4.4,1.1)
        x=random.uniform(-3.5,3.5)
        minus=math.prod(factor(*configs[j],x-(j+1)*t) for j in range(3))
        plus=math.prod(factor(*configs[j],x+(j+1)*t) for j in range(3))
        quotient=abs((minus-plus)/t)
        eps=1e-9*max(1,B)
        if quotient>B+eps:
            print(f'FAIL trial={trial} k={k} observed={quotient} upper={B}',file=sys.stderr)
            sys.exit(1)
        worst=max(worst,quotient/max(B,1e-16))
        cases+=1
print(f'PASS {cases} complex gaussian tests; largest observed / bound = {worst:.6g}')

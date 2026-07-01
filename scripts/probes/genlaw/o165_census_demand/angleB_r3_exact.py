# Angle B: EXACT r=3 bad-subset structure. r=3 => a0=4 (4-subsets), deg k=r-1=2, deficit 2.
# Bad <=> z^e + gamma z^f agrees with deg<=(r-2)=1 poly Q(z)=alpha+beta z on the 4 points.
# i.e. z^e + gamma z^f - alpha - beta z = 0 for all z in S (4 roots).
# Line (x^{n/2}, x^{n/2-1}): e=n/2, f=n/2-1. Note z^{n/2} = +-1 (z in mu_n): z^{n/2}=1 if z is a
# square (in mu_{n/2}), -1 if non-square. Let sigma(z) = z^{n/2} in {+1,-1}.
# Then z^e = z^{n/2} = sigma(z); z^f = z^{n/2-1} = sigma(z)/z = sigma(z) z^{-1}.
# So g(z) = sigma(z) + gamma sigma(z) z^{-1} = sigma(z)(1 + gamma/z).
# Bad: sigma(z)(1+gamma/z) = alpha + beta z on S (4 pts).  This is the EXACT r=3 reduction.
# We want to count distinct gamma. Let's MEASURE which (S, gamma) work and find the closed structure.

from math import comb, gcd
from itertools import combinations
from collections import Counter

p = 2013265921
def inv(x): return pow(x,p-2,p)
def mu_n(n):
    e=(p-1)//n
    for c in range(2,400):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return [pow(h,i,p) for i in range(n)]
    raise RuntimeError

def bad_r3(n):
    dom=mu_n(n); e,f=n//2,n//2-1
    idx={dom[i]:i for i in range(n)}; neg1=dom[n//2]
    # sigma(z)=z^{n/2}
    sig=[pow(dom[i],n//2,p) for i in range(n)]  # +1 or p-1
    fib={}
    for S in combinations(range(n),4):
        # solve: does there exist gamma s.t. {sigma(z)(1+gamma z^{-1}) : z in S} lies on a deg<=1 poly?
        # Equivalent to the h-condition; just reuse h test for safety.
        # g(z) = sigma + gamma sigma z^{-1}. value depends linearly on gamma.
        # deg<=1 through 4 pts: 2 conditions (DD_2=0, DD_3=0). With 1 free gamma => codim1 in S.
        # Use divided differences: DD_k of (z->v(z)) over S. v = A(z) + gamma B(z), A=sigma, B=sigma z^{-1}.
        # DD_2(A)+gamma DD_2(B)=0 and DD_3(A)+gamma DD_3(B)=0 with same gamma.
        zs=[dom[i] for i in S]
        A=[sig[i]%p for i in S]
        B=[(sig[i]*inv(dom[i]))%p for i in S]
        def DD(vals):
            # divided differences table, return [DD_0..DD_3] top? we want DD_2 and DD_3 (Newton coeffs).
            n_=len(vals); tab=[v%p for v in vals]
            coeffs=[tab[0]]
            cur=tab[:]
            for level in range(1,n_):
                cur=[ ((cur[i+1]-cur[i])*inv((zs[i+level]-zs[i])%p))%p for i in range(n_-level)]
                coeffs.append(cur[0])
            return coeffs  # coeffs[k] = DD_k = coeff of newton basis
        cA=DD(A); cB=DD(B)
        # need gamma with cA[2]+gamma cB[2]=0 and cA[3]+gamma cB[3]=0
        # from level2: gamma = -cA[2]/cB[2] (if cB[2]!=0). plug into level3.
        gam=None; ok=False
        for lev in (2,3):
            pass
        # solve consistently:
        if cB[2]%p!=0:
            g=(-cA[2]*inv(cB[2]))%p
            if (cA[3]+g*cB[3])%p==0:
                gam=g; ok=True
        else:
            if cA[2]%p==0:
                # level2 auto; use level3
                if cB[3]%p!=0:
                    g=(-cA[3]*inv(cB[3]))%p; gam=g; ok=True
                else:
                    ok=(cA[3]%p==0); gam=None
        if ok and gam is not None and gam!=0:
            fib.setdefault(gam,[]).append(tuple(S))
    return fib,dom,idx,neg1,sig

if __name__=="__main__":
    for n in [16,32]:
        fib,dom,idx,neg1,sig=bad_r3(n)
        print(f"n={n}: #distinct nonzero gamma = {len(fib)}  (expect O_P*n = {comb(n//4,2)*n})")
        # decode each gamma's canonical subset structure
        # classify by sigma-pattern: how many squares (sigma=1) vs non-squares (sigma=-1) in S
        sqset = set(i for i in range(n) if sig[i]==1)
        patt=Counter()
        for g,subs in fib.items():
            S=subs[0]
            nsq=sum(1 for i in S if i in sqset)
            patt[(len(subs), nsq)]+=1
        print(f"   (fibersize, #squares-in-S) dist: {dict(sorted(patt.items()))}")
        # Is gamma itself a square / in mu_{n/2}? gamma^{n/2}=?
        gs=list(fib)[:5]
        print("   sample gamma^{n/2}:", [pow(g,n//2,p) for g in gs], "(1=square)")

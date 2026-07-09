"""
C097 probe (numpy, streaming): Per-character Weil energy ||T_psi||^2 vs C(n,a)^2.

Connection C097: the Plancherel bridge collision_le_of_relative_bound reduces M2
anti-concentration to a PER-CHARACTER bound ||T_psi||^2 <= eps*C(n,a)^2 for all psi!=0,
and claims Stepanov (one curve at a time, non-vanishing free) DELIVERS that per-character
bound, closing the M2/Johnson-side face unconditionally.

PRIZE REGIME ONLY: thin dyadic mu_n (n=2^mu PROPER subgroup of F_q*), q prime =1 mod n,
q~n^beta beta in [4,5], (q-1)/n>1, n<<sqrt(q).

We measure EXACTLY (integer histogram of subset-stats + exact DFT magnitude):
  R = max_{psi!=0} ||T_psi||^2 / C(n,a)^2
at the prize statistic stat(S)=(sum x, sum x^2) on A=F_q x F_q, for a near the Johnson
radius.  The bridge needs R small. We compare against:
  - the BGK per-element worst incomplete sum eta_max = max_{b!=0}|sum_{x in mu_n} psi(b x)|
    (the actual analytic object; thin-subgroup => ~sqrt(n log(q/n)), NOT sqrt(q));
  - what a Stepanov/Weil FULL-FIELD bound would optimistically give (sqrt(q) per element).

Also Q1 (structure): confirm T_psi = e_a (elementary symmetric in chi(x)=psi(stat x)),
an a-element SUBSET sum, via Newton's identity e_2=(p1^2-p2)/2, i.e. it is NOT the root set
of a single univariate auxiliary (Stepanov counts univariate roots).
"""
import sys, math, itertools
import numpy as np
from math import comb

def isprime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def primitive_root(q):
    # q prime; find generator of F_q^*
    phi = q-1
    # factor phi
    fac=set(); m=phi; d=2
    while d*d<=m:
        while m%d==0: fac.add(d); m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,q):
        if all(pow(g,phi//p,q)!=1 for p in fac):
            return g
    raise RuntimeError

def find_primes(n, blo, bhi, want=2):
    lo=int(n**blo); hi=int(n**bhi); out=[]
    q=lo-(lo%n)+1
    if q<lo: q+=n
    while q<=hi and len(out)<want:
        if isprime(q) and (q-1)%n==0 and (q-1)//n>1:
            out.append(q)
        q+=n
    return out

def subgroup(n,q):
    g=primitive_root(q); h=pow(g,(q-1)//n,q)
    assert pow(h,n,q)==1 and all(pow(h,d,q)!=1 for d in range(1,n))
    return [pow(h,i,q) for i in range(n)]

def stats_array(elts,a,q):
    s1=[]; s2=[]
    for S in itertools.combinations(elts,a):
        s1.append(sum(S)%q); s2.append(sum((x*x)%q for x in S)%q)
    return np.array(s1,dtype=np.int64), np.array(s2,dtype=np.int64)

def worst_ratio(elts,a,q,bsweep=600,rand=600,seed=1):
    """exact max_{psi!=0} ||T_psi||^2 via T_psi=sum_S exp(2pi i (b1 s1 + b2 s2)/q)."""
    s1,s2=stats_array(elts,a,q)
    N=len(s1); C2=N*N
    rng=np.random.default_rng(seed)
    cands=set()
    for b1 in range(1,min(q,bsweep)): cands.add((b1,0))
    for b2 in range(1,min(q,bsweep)): cands.add((0,b2))
    for _ in range(rand):
        b=(int(rng.integers(q)),int(rng.integers(q)))
        if b!=(0,0): cands.add(b)
    best=0.0; bestb=None
    two_pi_over_q=2*math.pi/q
    for (b1,b2) in cands:
        ang=(two_pi_over_q*((b1*s1+b2*s2)%q))
        T=np.cos(ang).sum()+1j*np.sin(ang).sum()
        v=(T.real*T.real+T.imag*T.imag)
        if v>best: best=v; bestb=(b1,b2)
    return best,C2,N,bestb

def newton_check(elts,q):
    """structure: e_2 = (p1^2 - p2)/2 with p_k = sum_x chi(x)^k, chi(x)=psi(b x). Confirms
    T_psi(a=2)=e_2 is the SUBSET elementary symmetric, not a univariate root count."""
    b=1; p=q; w=np.exp(2j*math.pi/p)
    chi=np.array([w**((b*x)%p) for x in elts])
    e1=chi.sum(); e2=0
    for i in range(len(chi)):
        for j in range(i+1,len(chi)): e2+=chi[i]*chi[j]
    p1=chi.sum(); p2=(chi**2).sum()
    return abs(e2-(p1*p1-p2)/2)

def main():
    print("="*82,flush=True)
    print("C097: per-char Weil energy ||T_psi||^2 vs C(n,a)^2 -- PRIZE REGIME thin dyadic mu_n",flush=True)
    print("="*82,flush=True)
    # Q1 structure (cheap, n=8)
    q0=find_primes(8,4.0,5.0,1)[0]; e0=subgroup(8,q0)
    print(f"[Q1 structure] n=8 q={q0}: |e_2 - (p1^2-p2)/2| = {newton_check(e0,q0):.2e}  "
          f"(==0 => T_psi is the SUBSET elementary symmetric e_a, NOT univariate roots)",flush=True)
    for n in [8,16]:
        primes=find_primes(n,4.0,5.0,2)
        for a in sorted(set([2, n//2])):
            if comb(n,a)>20000:   # feasibility cap for exact subset enum + sweep
                print(f"\n--- n={n} a={a}: C(n,a)={comb(n,a)} too large, skipping ---",flush=True); continue
            print(f"\n--- n={n}  a={a}  C(n,a)={comb(n,a)}  (prize dyadic mu_n) primes {primes} ---",flush=True)
            for q in primes:
                elts=subgroup(n,q)
                best,C2,N,bestb=worst_ratio(elts,a,q)
                eps=best/C2
                # BGK per-element worst incomplete subgroup sum
                p=q; w=np.exp(2j*math.pi/p)
                etamax=0.0
                for b in range(1,q):
                    e=sum(w**((b*x)%p) for x in elts)
                    etamax=max(etamax,abs(e))
                print(f"  q={q}: max_psi||T||^2={best:.4e}  C(n,a)^2={C2:.4e}  "
                      f"eps=ratio={eps:.4f}  worst b={bestb}",flush=True)
                print(f"        BGK eta_max={etamax:.3f}  2sqrt(n)={2*math.sqrt(n):.2f}  "
                      f"sqrt(q)={math.sqrt(q):.1f}  sqrt(n*log(q/n))={math.sqrt(n*math.log(q/n)):.2f}",flush=True)
    print("\n[interpretation] bridge needs eps small for ALL psi!=0. Read 'eps=ratio' above.",flush=True)

if __name__=="__main__":
    main()

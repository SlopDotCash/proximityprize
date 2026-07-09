"""
sweep_A33_margin_fast.py  —  A33 (407-T05) honest crux, numpy-accelerated.

Measures  margin(n) = sqrt(n*k) - MAXragged(n)  at the Kambire-worst intermediate direction
(d ~ sqrt(n)), for n=8,16,32 at rho=1/4 and rho=1/2, to decide whether REALIZABILITY's
improvement over sqrt(n*k) PERSISTS or VANISHES as n grows.

Method (exact over F_q via MDS k-subset interpolation, numpy-vectorized eval):
  For each gamma: received r(x)=x^a+gamma x^b on mu_n; for each k-subset K interpolate the
  unique deg-<k codeword c_K through r|K (MDS), evaluate c_K on all of mu_n, agreement set
  S = {x: c_K(x)=r(x)}.  MAXragged = max |S| over (gamma,K) with S NOT a coset-union.
  n<=16: ALL gamma, ALL k-subsets (EXACT).  n=32: sampled (gamma_s gammas, ksub_s subsets) ->
  LOWER bound on MAXragged -> UPPER bound on margin (conservative: won't overstate the gain).

Run:  python sweep_A33_margin_fast.py
"""
import itertools, math, random
import numpy as np

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    d=3
    while d*d<=m:
        if m%d==0: return False
        d+=2
    return True
def prim_root(q):
    phi=q-1; fac=set(); m=phi; d=2
    while d*d<=m:
        while m%d==0: fac.add(d); m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,q):
        if all(pow(g,phi//pf,q)!=1 for pf in fac): return g
def mu_n(n,q):
    z=pow(prim_root(q),(q-1)//n,q); return [pow(z,j,q) for j in range(n)]
def divisors(n): return [d for d in range(1,n+1) if n%d==0]
def is_coset_union(S,n):
    Ss=set(int(x)%n for x in S)
    if len(Ss)<=1: return False
    for d in divisors(n):
        if d==1 or d==n: continue
        g=n//d; H=[(i*g)%n for i in range(d)]
        if all(((s+h)%n in Ss) for s in Ss for h in H): return True
    return False

def smallest_prime_1modn(n):
    c=n+1
    while not is_prime(c): c+=n
    return c
def kambire_worst_d(n,k):
    ds=sorted(set(math.gcd(abs(aa-bb),n) for aa in range(k,n) for bb in range(k,n) if aa!=bb
                  if math.gcd(abs(aa-bb),n) not in (1,n)))
    return min(ds,key=lambda dd:abs(dd-max(2,int(round(n**0.5))))) if ds else None
def genuine_dir(n,k,d):
    for bb in range(k,n):
        aa=bb+d
        if aa<n and math.gcd(aa-bb,n)==d: return aa,bb
    return None,None

def gauss_solve_mod(A, q):
    """solve A x = b for augmented A (k x (k+1)) over F_q using python ints. return x or None."""
    k=len(A)
    A=[row[:] for row in A]
    for c in range(k):
        piv=None
        for i in range(c,k):
            if A[i][c]%q!=0: piv=i; break
        if piv is None: return None
        A[c],A[piv]=A[piv],A[c]
        ip=pow(A[c][c],q-2,q); A[c]=[(v*ip)%q for v in A[c]]
        for i in range(k):
            if i!=c and A[i][c]%q!=0:
                f=A[i][c]; A[i]=[(A[i][t]-f*A[c][t])%q for t in range(k+1)]
    return [A[i][k]%q for i in range(k)]

def max_ragged(n,k,a,b,q,exact,gamma_s,ksub_s):
    mu_elts=mu_n(n,q)
    xa=np.array([pow(mu_elts[j],a,q) for j in range(n)],dtype=object)
    xb=np.array([pow(mu_elts[j],b,q) for j in range(n)],dtype=object)
    # Vandermonde rows for all points (python ints)
    Vand=[[pow(mu_elts[j],t,q) for t in range(k)] for j in range(n)]
    best=0
    gammas=range(q) if exact else random.sample(range(q),min(gamma_s,q))
    for gamma in gammas:
        rvals=[(int(xa[j])+gamma*int(xb[j]))%q for j in range(n)]
        if exact:
            Ks=itertools.combinations(range(n),k)
        else:
            seen=set(); Ks=[]
            for _ in range(ksub_s):
                K=tuple(sorted(random.sample(range(n),k)))
                if K not in seen: seen.add(K); Ks.append(K)
        for K in Ks:
            Aug=[Vand[j][:]+[rvals[j]] for j in K]
            coef=gauss_solve_mod(Aug,q)
            if coef is None: continue
            # evaluate codeword at all points: sum coef[t]*x^t
            S=[]
            for j in range(n):
                val=0
                for t in range(k-1,-1,-1):
                    val=(val*mu_elts[j]+coef[t])%q
                if val==rvals[j]: S.append(j)
            if len(S)>best and not is_coset_union(S,n):
                best=len(S)
    return best

if __name__=="__main__":
    print("\n### A33 margin-fast: sqrt(n*k) - MAXragged at Kambire-worst direction\n")
    for rho_name,rho in [("1/4",0.25),("1/2",0.5)]:
        print(f"rho={rho_name}:")
        print(f"  {'n':>5} {'k':>4} {'d':>4} {'s':>4} {'(a,b)':>9} {'q':>8} {'mode':>8} | {'MAXrag':>6} {'sqrt(nk)':>9} {'margin':>7} {'mar/sqrt':>9}")
        for n in [8,16,32]:
            k=int(round(rho*n))
            if k<1: continue
            d=kambire_worst_d(n,k)
            if d is None: continue
            a,b=genuine_dir(n,k,d)
            if a is None: continue
            s=n//d; q=smallest_prime_1modn(n)
            exact=(n<=16) and (math.comb(n,k)<=5000)
            mr=max_ragged(n,k,a,b,q,exact,gamma_s=200,ksub_s=4000)
            tgt=math.sqrt(n*k); mar=tgt-mr; mode="EXACT" if exact else "SAMP-LB"
            print(f"  {n:>5} {k:>4} {d:>4} {s:>4} {('('+str(a)+','+str(b)+')'):>9} {q:>8} {mode:>8} | {mr:>6} {tgt:>9.3f} {mar:>7.3f} {mar/tgt:>9.4f}")
        print()
    print("NOTE: n=32 SAMP-LB underestimates MAXragged -> margin is an UPPER bound (conservative).")
    print("### DONE.")

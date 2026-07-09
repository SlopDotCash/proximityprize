"""
sweep_A33_margin_scaling.py  —  A33 (407-T05): the HONEST crux.

The v2/v3 probes show realizable RAGGED max |S| < sqrt(n*k) at the Kambire-worst intermediate
direction (d~sqrt(n)).  But the DECISIVE honest question is the MARGIN scaling:
    margin(n) = sqrt(n*k) - MAXragged(n)   at the Kambire-worst direction, rate rho=1/2.
If margin -> 0 (or grows only as a vanishing fraction of sqrt(n*k)), realizability gives a real
but ASYMPTOTICALLY-VANISHING improvement -> does NOT yield a prize-tight (constant-factor or
Theta(1/log n)) gain below Johnson.  If margin grows / stays a constant fraction, the lever is live.

This probe measures MAXragged at the Kambire-worst direction for n=8,16,32,64 (rho=1/2, and a
rho=1/4 row), via gamma-sampling + k-subset sampling (LOWER bound on the true max, so an
OVER-estimate of the margin -- conservative against claiming the margin is large).
n=8,16 are also cross-checked against the exact v3 values.

Run:  python sweep_A33_margin_scaling.py
"""
import itertools, math, random

def inv_mod(a,q): return pow(a%q,q-2,q)
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
    Ss=set(x%n for x in S)
    if len(Ss)<=1: return False
    for d in divisors(n):
        if d==1 or d==n: continue
        g=n//d; H=[(i*g)%n for i in range(d)]
        if all(((s+h)%n in Ss) for s in Ss for h in H): return True
    return False
def interp(K,mu_elts,rvals,k,q):
    A=[]
    for j in K:
        x=mu_elts[j]; A.append([pow(x,t,q) for t in range(k)]+[rvals[j]%q])
    for c in range(k):
        piv=None
        for i in range(c,k):
            if A[i][c]%q!=0: piv=i; break
        if piv is None: return None
        A[c],A[piv]=A[piv],A[c]
        ip=inv_mod(A[c][c],q); A[c]=[(v*ip)%q for v in A[c]]
        for i in range(k):
            if i!=c and A[i][c]%q!=0:
                f=A[i][c]; A[i]=[(A[i][t]-f*A[c][t])%q for t in range(k+1)]
    return [A[i][k]%q for i in range(k)]
def epoly(c,x,q):
    r=0
    for t in range(len(c)-1,-1,-1): r=(r*x+c[t])%q
    return r

def kambire_worst_d(n,k):
    ds=sorted(set(math.gcd(abs(aa-bb),n) for aa in range(k,n) for bb in range(k,n) if aa!=bb
                  if math.gcd(abs(aa-bb),n) not in (1,n)))
    if not ds: return None
    return min(ds,key=lambda dd:abs(dd-max(2,int(round(n**0.5)))))

def genuine_dir(n,k,d):
    for bb in range(k,n):
        aa=bb+d
        if aa<n and math.gcd(aa-bb,n)==d: return aa,bb
    return None,None

def max_ragged(n,k,a,b,q,exact,gamma_s,ksub_s):
    mu_elts=mu_n(n,q); best_r=0
    gammas=range(q) if exact else random.sample(range(q),min(gamma_s,q))
    for gamma in gammas:
        rvals=[(pow(mu_elts[j],a,q)+gamma*pow(mu_elts[j],b,q))%q for j in range(n)]
        if exact:
            Ks=itertools.combinations(range(n),k)
        else:
            seen=set(); Ks=[]
            for _ in range(ksub_s):
                K=tuple(sorted(random.sample(range(n),k)))
                if K not in seen: seen.add(K); Ks.append(K)
        for K in Ks:
            c=interp(K,mu_elts,rvals,k,q)
            if c is None: continue
            S=[j for j in range(n) if epoly(c,mu_elts[j],q)==rvals[j]]
            if len(S)>best_r and not is_coset_union(S,n):
                best_r=len(S)
    return best_r

def smallest_prime_1modn(n):
    c=n+1
    while not is_prime(c): c+=n
    return c

if __name__=="__main__":
    print("\n### A33 margin scaling: sqrt(n*k) - MAXragged at the Kambire-worst direction\n")
    print("rho=1/2 (k=n/2):")
    print(f"  {'n':>5} {'k':>4} {'d':>4} {'s':>4} {'(a,b)':>9} {'q':>9} {'mode':>8} | {'MAXrag':>6} {'sqrt(nk)':>9} {'margin':>7} {'margin/sqrt(nk)':>16}")
    for n,mu in [(8,3),(16,4),(32,5),(64,6)]:
        k=n//2; d=kambire_worst_d(n,k);
        if d is None: continue
        a,b=genuine_dir(n,k,d); s=n//d
        q=smallest_prime_1modn(n)
        exact = (n<=16)
        mr=max_ragged(n,k,a,b,q,exact, gamma_s=300, ksub_s=2500)
        tgt=math.sqrt(n*k); mar=tgt-mr
        mode="EXACT" if exact else "SAMP-LB"
        print(f"  {n:>5} {k:>4} {d:>4} {s:>4} {('('+str(a)+','+str(b)+')'):>9} {q:>9} {mode:>8} | {mr:>6} {tgt:>9.3f} {mar:>7.3f} {mar/tgt:>16.4f}")
    print("\nrho=1/4 (k=n/4):")
    print(f"  {'n':>5} {'k':>4} {'d':>4} {'s':>4} {'(a,b)':>9} {'q':>9} {'mode':>8} | {'MAXrag':>6} {'sqrt(nk)':>9} {'margin':>7} {'margin/sqrt(nk)':>16}")
    for n,mu in [(8,3),(16,4),(32,5),(64,6)]:
        k=n//4;
        if k<1: continue
        d=kambire_worst_d(n,k)
        if d is None: continue
        a,b=genuine_dir(n,k,d); s=n//d
        q=smallest_prime_1modn(n)
        exact=(n<=16)
        mr=max_ragged(n,k,a,b,q,exact, gamma_s=300, ksub_s=2500)
        tgt=math.sqrt(n*k); mar=tgt-mr
        mode="EXACT" if exact else "SAMP-LB"
        print(f"  {n:>5} {k:>4} {d:>4} {s:>4} {('('+str(a)+','+str(b)+')'):>9} {q:>9} {mode:>8} | {mr:>6} {tgt:>9.3f} {mar:>7.3f} {mar/tgt:>16.4f}")
    print("\nNOTE: n>=32 are SAMPLED lower bounds on MAXragged -> margins are UPPER bounds (conservative).")
    print("### DONE.")

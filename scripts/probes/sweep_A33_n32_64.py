"""
A33 (407-T05): n=32, n=64 sampled MAXragged at Kambire-worst direction, rho=1/4.
Tests whether the EXACT-small-n ratio MAXragged/sqrt(n*k) = 3/4 (n=8,16) PERSISTS as n grows
(=> realizability gives a CONSTANT-FACTOR sub-sqrt(nk) gain) or DRIFTS toward 1 (=> vanishing).
Sampled => MAXragged is a LOWER bound => ratio is a LOWER bound (conservative against claiming a
large constant-factor gain: the true ratio could be HIGHER, i.e. closer to 1).
"""
import itertools, math, random

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
def gsolve(A,q):
    k=len(A); A=[r[:] for r in A]
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

def max_ragged_sampled(n,k,a,b,q,gamma_s,ksub_s):
    mu_elts=mu_n(n,q)
    xa=[pow(mu_elts[j],a,q) for j in range(n)]
    xb=[pow(mu_elts[j],b,q) for j in range(n)]
    Vand=[[pow(mu_elts[j],t,q) for t in range(k)] for j in range(n)]
    best=0; bestS=None
    for _ in range(gamma_s):
        gamma=random.randrange(q)
        rvals=[(xa[j]+gamma*xb[j])%q for j in range(n)]
        seen=set()
        for _ in range(ksub_s):
            K=tuple(sorted(random.sample(range(n),k)))
            if K in seen: continue
            seen.add(K)
            Aug=[Vand[j][:]+[rvals[j]] for j in K]
            coef=gsolve(Aug,q)
            if coef is None: continue
            S=[]
            for j in range(n):
                val=0
                for t in range(k-1,-1,-1): val=(val*mu_elts[j]+coef[t])%q
                if val==rvals[j]: S.append(j)
            if len(S)>best and not is_coset_union(S,n):
                best=len(S); bestS=S
    return best,bestS

if __name__=="__main__":
    print("\n### A33 n=32,64 ratio test (rho=1/4), Kambire-worst direction\n")
    print(f"  {'n':>5} {'k':>4} {'d':>4} {'s':>4} {'(a,b)':>10} {'q':>8} | {'MAXrag-LB':>9} {'sqrt(nk)':>9} {'ratio-LB':>9} {'3/2 k':>7}")
    for n in [32,64]:
        k=n//4; d=kambire_worst_d(n,k)
        if d is None: continue
        a,b=genuine_dir(n,k,d); s=n//d; q=smallest_prime_1modn(n)
        gs = 120 if n==32 else 40
        ks = 2500 if n==32 else 1500
        mr,S=max_ragged_sampled(n,k,a,b,q,gs,ks)
        tgt=math.sqrt(n*k)
        print(f"  {n:>5} {k:>4} {d:>4} {s:>4} {('('+str(a)+','+str(b)+')'):>10} {q:>8} | {mr:>9} {tgt:>9.3f} {mr/tgt:>9.4f} {1.5*k:>7.1f}")
        if S is not None:
            print(f"        witness ragged S (exps, |S|={len(S)}): {sorted(int(x) for x in S)}")
    print("\nNOTE: sampled => MAXrag is a LOWER bound => ratio-LB is a LOWER bound on the true ratio.")
    print("### DONE.")

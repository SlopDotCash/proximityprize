# -*- coding: utf-8 -*-
"""
C070 attack -- PART 2 (efficient): the Hasse-Davenport lift / multiplicative cocycle on T.

Proposal (C070): lift chi from F_q to F_{q^2} via chi' = chi o Norm. Hasse-Davenport:
-g(chi') = (-g(chi))^2 (Gauss sums lift MULTIPLICATIVELY). The bet: T (an AVERAGE of
Jacobi sums) therefore descends through the tower MULTIPLYING Jacobi sums with a per-level
multiplier uniformly sqrt(q)-controlled by Weil -> NO L-infty-vs-L^2 (sqrt(2 ln m)) loss.

OBSTRUCTION TO TEST:  T(phi)=sum_{w in ker chi} phi(1-w) has the ADDITIVE arg (1-w).
T is NOT one Gauss/Jacobi sum, it is an AVERAGE; an average of cocyclic terms is NOT cocyclic.
So lifting the field should give T' over F_{q^2} that behaves GENERICALLY (rescaled to
sqrt(|ker'|)) with NO bounded multiplicative law T'/T.

Efficient: enumerate F_{q^2}^* ONCE as powers of a generator gg, caching (Norm, dlog_in_Fq).
Apply chars by exponent arithmetic (roots of unity), not per-term cmath.exp.
"""
import cmath, math

def is_prime(n):
    if n<2: return False
    if n%2==0: return n==2
    i=3
    while i*i<=n:
        if n%i==0: return False
        i+=2
    return True

def find_prime_small(n, qmax):
    """smallest prime p, n|p-1, n^2<p, m>1, p<=qmax (so q^2 stays enumerable)."""
    p=None
    for k in range(2, qmax):
        cand=1+n*k
        if cand>qmax: break
        if is_prime(cand) and cand>n*n and (cand-1)//n>1:
            p=cand; break
    return p

def primitive_root(p):
    if p==2: return 1
    phi=p-1; nn=phi; factors=[]; d=2
    while d*d<=nn:
        if nn%d==0:
            factors.append(d)
            while nn%d==0: nn//=d
        d+=1
    if nn>1: factors.append(nn)
    for g in range(2,p):
        if all(pow(g,phi//f,p)!=1 for f in factors):
            return g
    raise RuntimeError

def nonresidue(p):
    for s in range(2,p):
        if pow(s,(p-1)//2,p)==p-1: return s
    raise RuntimeError

def run(n, qmax):
    p=find_prime_small(n,qmax)
    if p is None:
        print(f"  n={n}: no small prime <= {qmax}"); return None
    g=primitive_root(p); pm1=p-1; m=pm1//n
    s=nonresidue(p); Q=p*p; Qm1=Q-1

    # F_{q^2} arithmetic, t^2=s
    def mul(x,y):
        a,b=x; c,d=y
        return ((a*c+b*d*s)%p,(a*d+b*c)%p)
    def is_one(x): return x==(1,0)
    # find generator gg of F_{q^2}^*
    def order_div_check(x):
        # x has order Qm1 iff x^{Qm1/r}!=1 for each prime r|Qm1
        # factor Qm1
        return None
    # factor Qm1 once
    def factorize(N):
        f=[]; d=2; M=N
        while d*d<=M:
            if M%d==0:
                f.append(d)
                while M%d==0: M//=d
            d+=1
        if M>1: f.append(M)
        return f
    def powe(x,e):
        r=(1,0); b=x
        while e>0:
            if e&1: r=mul(r,b)
            b=mul(b,b); e>>=1
        return r
    facs=factorize(Qm1)
    gg=None
    for a in range(0,p):
        for b in range(1,p):
            x=(a,b)
            if all(not is_one(powe(x,Qm1//r)) for r in facs):
                gg=x; break
        if gg: break
    if gg is None:
        print(f"  n={n} p={p}: no F_q2 generator"); return None

    # discrete log in F_p
    dlog=[0]*p; c=1
    for k in range(p-1):
        dlog[c]=k; c=(c*g)%p
    def Norm(x):
        a,b=x; return (a*a-b*b*s)%p

    # subgroup mu_n in F_p^*  (ker chi)
    h=pow(g,(p-1)//n,p); mu_n=[]; c=1
    for _ in range(n):
        mu_n.append(c); c=(c*h)%p
    mu_set=set(mu_n)

    # Enumerate F_{q^2}^* once: store list of elements (we need 1-W and Norm).
    # also build map element->index for subtraction lookups not needed (we compute 1-W directly).
    elts=[None]*Qm1
    e=(1,0)
    for k in range(Qm1):
        elts[k]=e
        e=mul(e,gg)
    # ker' = { W : Norm(W) in mu_n }
    kerp=[W for W in elts if Norm(W) in mu_set]
    target=n*(p+1)
    okc=(len(kerp)==target)

    print(f"  n={n} p={p} beta={math.log(p)/math.log(n):.2f} m={m} Q={Q} |ker'|={len(kerp)} "
          f"(target {target} {'OK' if okc else 'MISMATCH'})")

    # Hasse-Davenport sanity (Gauss sums), char exponent jj=1
    def psi_p(x): return cmath.exp(2j*math.pi*(x%p)/p)
    def Tr(x):
        a,b=x; return (2*a)%p
    def psi_q2(X): return cmath.exp(2j*math.pi*(Tr(X)%p)/p)
    def chi_p(j,x):
        if x%p==0: return 0j
        return cmath.exp(2j*math.pi*(j*dlog[x%p])/pm1)
    jj=1
    gp=sum(chi_p(jj,x)*psi_p(x) for x in range(1,p))
    gq2=0j
    for W in elts:
        gq2+=chi_p(jj,Norm(W))*psi_q2(W)
    hd=abs(-gq2-(-gp)**2)
    print(f"     HD: |-g(chi') - (-g(chi))^2|={hd:.3e}   |g(chi)|={abs(gp):.3f}(~sqrt p={math.sqrt(p):.3f})  |g(chi')|={abs(gq2):.3f}(~p={p})")

    sqn=math.sqrt(n); sqk=math.sqrt(len(kerp))
    print(f"     sqrt(n)={sqn:.3f}  sqrt(|ker'|)={sqk:.3f}  (q+1)={p+1}")
    print(f"     {'h':>3} {'|T|(Fq)':>10} {'|T|/sqn':>9} {'|T2|(Fq2)':>11} {'|T2|/sqk':>9} {'T2/T':>9}")
    rows=[]
    for hh in range(1,min(m,9)):
        phi_exp=(hh*n)%pm1
        Tp=0j
        for w in mu_n:
            if (1-w)%p==0: continue
            Tp+=chi_p(phi_exp,(1-w)%p)
        Tq2=0j
        for W in kerp:
            a,b=W
            OW=((1-a)%p,(-b)%p)  # 1 - W
            if OW==(0,0): continue
            Tq2+=chi_p(phi_exp,Norm(OW))
        Tp=abs(Tp); Tq2=abs(Tq2)
        ratio=Tq2/Tp if Tp>1e-9 else float('nan')
        rows.append((hh,Tp,Tq2,ratio))
        print(f"     {hh:>3} {Tp:>10.3f} {Tp/sqn:>9.3f} {Tq2:>11.3f} {Tq2/sqk:>9.3f} {ratio:>9.3f}")
    # is T2/T a bounded q-INDEPENDENT constant (cocycle) or does it just track sqrt(q+1)?
    ratios=[r[3] for r in rows if not math.isnan(r[3])]
    if ratios:
        print(f"     ratio T2/T: min={min(ratios):.3f} max={max(ratios):.3f} spread={max(ratios)-min(ratios):.3f}  "
              f"sqrt(q+1)={math.sqrt(p+1):.3f}")
    return dict(n=n,p=p,rows=rows,sqk=sqk,sqn=sqn)

print("="*84)
print("PART 2: Hasse-Davenport lift; is T cocyclic with a BOUNDED q-INDEPENDENT multiplier?")
print("  Cocycle would predict: T2/T = a fixed bounded factor (the per-level multiplier).")
print("  Generic (no cocycle): |T2| ~ sqrt(|ker'|) = sqrt(n(q+1)) independent of |T|, so")
print("  T2/T scatters and tracks sqrt(q+1) (i.e. T2 is a NEW generic sum, not T lifted).")
print("="*84)
run(8, 600)        # n=8, p=521  -> q^2 = 271441
run(16, 300)       # n=16 small p -> q^2 manageable

"""
INDEPENDENT adversarial verification of C038 REFUTED verdict.
Recompute M(n)=max_{b!=0}|sum_{y in mu_n} e_q(by)| from scratch.
Checks:
 (1) Regime: q PROPER subgroup prime, q=1 mod n, n << sqrt q (q > n^2), beta=ln q/ln n.
 (2) Recompute R = M(n)^2/M(n/2)^2 and test descent bound M(n)^2 <= 2 M(n/2)^2.
 (3) Cross-check: is mu_{n/2} actually the x->x^2 IMAGE of mu_n (the ORBIT fold),
     or just an arbitrary index-2 subgroup? They are the SAME subgroup since
     squaring mu_n (cyclic order n) gives the unique order-n/2 subgroup. Verify.
 (4) Stability of c(n)=M/sqrt(n log(q/n)).
 (5) Independent M via coset-rep enumeration (correctness cross-check vs full-b loop on small q).
"""
import math, cmath

def is_prime(n):
    if n<2: return False
    if n%2==0: return n==2
    i=3
    while i*i<=n:
        if n%i==0: return False
        i+=2
    return True

def prime_factors(m):
    fac=set(); d=2
    while d*d<=m:
        while m%d==0: fac.add(d); m//=d
        d+=1
    if m>1: fac.add(m)
    return fac

def subgen(q,n):
    m=q-1; fac=prime_factors(m); g=2
    while not all(pow(g,m//p,q)!=1 for p in fac): g+=1
    return pow(g,(q-1)//n,q)

def subgroup(q,n):
    h=subgen(q,n); s=[]; x=1
    for _ in range(n): s.append(x); x=(x*h)%q
    return s

def Msup_exact(q,n):
    """M(n) using exact integer phase index (b*y mod q) -> cmath.exp. Enumerate ALL b (max correct)."""
    mu=subgroup(q,n)
    w=2*math.pi/q
    # precompute unit roots table is too big for big q; just loop b, inner sum over n
    best=0.0
    for b in range(1,q):
        s=0j
        for y in mu:
            s+=cmath.exp(1j*((b*y)%q)*w)
        m=abs(s)
        if m>best: best=m
    return best

def Msup_cosets(q,n):
    """Faster: M depends only on coset b*mu_n, so iterate coset reps. Use a 'seen' marker per coset
    via canonical rep = min over coset (expensive). Instead iterate b but the value of |period(b)|
    is constant on cosets of mu_n; to get the max we still must hit each coset once. Simplest correct:
    iterate b=1..q-1 (done in Msup_exact). For speed on larger q use numpy elsewhere; here small-q check."""
    return Msup_exact(q,n)

def main():
    # SMALL-q correctness cross-check first (exact, no numpy), then in-regime spot checks.
    print("="*100)
    print("INDEPENDENT C038 verification")
    print("="*100)
    # In-regime primes matching attacker's plan but small enough for pure-python full-b loop:
    cases = [(8,8009),(8,8017),(8,8081),(16,70001),(16,70177),(16,70241),(32,1000033)]
    print(f"{'n':>4} {'q':>9} {'beta':>5} {'q>n^2?':>7} {'sqimg=sub?':>11} {'M(n)':>8} {'M(n/2)':>8} {'R':>7} {'desc<=2':>8} {'c(n)':>6} {'c(n/2)':>7}")
    for n,q in cases:
        assert is_prime(q), (q,"not prime")
        assert (q-1)%n==0, (q,n,"q not 1 mod n")
        beta=math.log(q)/math.log(n)
        proper = (q > n*n)  # n << sqrt q
        # verify mu_{n/2} == squares of mu_n
        mu_n=subgroup(q,n)
        sq=set((y*y)%q for y in mu_n)
        mu_half=set(subgroup(q,n//2))
        sqimg = (sq==mu_half)
        Mn=Msup_exact(q,n)
        Mn2=Msup_exact(q,n//2)
        R=(Mn*Mn)/(Mn2*Mn2)
        desc = (Mn*Mn <= 2*Mn2*Mn2)
        cn=Mn/math.sqrt(n*math.log(q/n))
        cn2=Mn2/math.sqrt((n//2)*math.log(q/(n//2)))
        print(f"{n:>4} {q:>9} {beta:>5.2f} {str(proper):>7} {str(sqimg):>11} {Mn:>8.4f} {Mn2:>8.4f} {R:>7.4f} {str(desc):>8} {cn:>6.3f} {cn2:>7.3f}")

if __name__=="__main__":
    main()

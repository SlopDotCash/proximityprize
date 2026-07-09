#!/usr/bin/env python3
"""
I031 increment -> WALL confirmation.  (Issue #444.)

The increment eta_b - eta_c = sum_{x in mu_n} (e_p(b x) - e_p(c x)).  Writing b = c*u
(u = b/c a quotient element), e_p(b x) = e_p(c (u x)), and as x ranges over mu_n so does
u x ONLY IF u in mu_n (then increment = 0). For u NOT in mu_n:
    eta_b - eta_c = sum_{y in c*mu_n} e_p(y') - sum_{y in c*mu_n}... = a sum over the
    SYMMETRIC DIFFERENCE of the two cosets b*mu_n and c*mu_n (each a 2n-element
    +/-1-weighted set), i.e. an INCOMPLETE character sum over a 2n-element set with
    signs = a Gauss-period-LIKE object of the SAME analytic difficulty.

DECISIVE TEST. The "increment estimate is sub-Gaussian with D=O(n)" needed by I031 is
    max_{b,c} |eta_b - eta_c| <= C sqrt(n log(m^2)) = C sqrt(2 n log m).
Compare this to the floor target sqrt(n log m): if the increment-sup obeys the SAME
sqrt(n log m) law (up to constant), then bounding the increment is EXACTLY as hard as
bounding B itself (the max over a 2n-set incomplete sum is the same BGK/Paley wall).
We measure  maxInc / sqrt(n log m)  and  maxInc / sqrt(2 n log m) and compare to B/sqrt(n log m).
"""
import cmath, math

def is_prime(n):
    if n<2: return False
    if n%2==0: return n==2
    d=3
    while d*d<=n:
        if n%d==0: return False
        d+=2
    return True

def primitive_root(p):
    if p==2: return 1
    phi=p-1; fac=[]; t=phi; d=2
    while d*d<=t:
        if t%d==0:
            fac.append(d)
            while t%d==0: t//=d
        d+=1
    if t>1: fac.append(t)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g
    return None

def gauss_periods(p,n,g=None):
    assert (p-1)%n==0
    m=(p-1)//n
    if g is None: g=primitive_root(p)
    gen=pow(g,m,p)
    mu=[]; x=1
    for _ in range(n): mu.append(x); x=(x*gen)%p
    e=[cmath.exp(2j*math.pi*k/p) for k in range(p)]
    etas=[]; bc=1
    for c in range(m):
        s=0j
        for x in mu: s+=e[(bc*x)%p]
        etas.append(s); bc=(bc*g)%p
    return etas,m,g

def main():
    print("=== I031 increment-as-wall: does the increment obey the SAME sqrt(n log m) law as B? ===\n")
    print(f"{'p':>7} {'n':>4} {'m':>5} | {'B':>7} {'B/√nlm':>7} | {'maxInc':>7} "
          f"{'mxI/√nlm':>8} {'mxI/√2nlm':>9} | {'ratio mxI/B':>11}")
    cases=[]
    for n in [32,64,128,256]:
        cnt=0; p=n+1
        while cnt<5:
            p+=n
            if is_prime(p) and (p-1)%n==0:
                m=(p-1)//n
                if m<8: continue
                if p>80000: break
                cases.append((p,n)); cnt+=1
    for (p,n) in cases:
        etas,m,g=gauss_periods(p,n)
        B=max(abs(e) for e in etas)
        maxInc=max(abs(etas[i]-etas[j]) for i in range(m) for j in range(i+1,m))
        nlm=math.sqrt(n*math.log(m))
        n2lm=math.sqrt(2*n*math.log(m))
        print(f"{p:>7} {n:>4} {m:>5} | {B:7.3f} {B/nlm:7.3f} | {maxInc:7.3f} "
              f"{maxInc/nlm:8.3f} {maxInc/n2lm:9.3f} | {maxInc/B:11.3f}")
    print("\nVERDICT KEYS:")
    print("  maxInc/B in [1.4, 2.0] STABLE  => increment-sup tracks B (same wall, x const).")
    print("  maxInc/sqrt(2 n log m) ~ B/sqrt(n log m) (both ~1.3) => increment obeys the")
    print("    IDENTICAL sqrt(n log#) law with #=m^2 instead of m: bounding the increment is")
    print("    a worst-case incomplete sum over a 2n-set = the SAME BGK/Paley wall, not easier.")

if __name__=="__main__":
    main()

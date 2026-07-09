#!/usr/bin/env python3
"""
C051 probe: does the GG25 curve close-set (#curveCloseSet, F4) coincide with the
MCA / spectral incidence count (#badScalars = I(delta), F3) -- i.e. is the
F4 -> F3 reduction identity-level (no analytic slack) ?

Setup (PRIZE REGIME -- proper dyadic subgroup mu_n of F_q^*, q = n^beta, multiple primes):
  - smooth eval domain D = mu_n  (n = 2^mu a PROPER subgroup of F_q^*)
  - RS code: codewords = { (P(x))_{x in D} : deg P < k },  k = rate*n
  - stack u = (u0, u1):  ell = 1, curve alpha |-> u0 + alpha*u1  (coordinatewise on D)
  - close set  A_delta(u,f) = { alpha in F_q : Delta(u0 + alpha*u1, f(alpha)) <= delta }
      where f(alpha) = a NEAREST codeword to (u0 + alpha*u1).   (GG25 Def 3.1, ell=1)
  - badScalars   B_delta(u) = { alpha in F_q : exists codeword c, Delta(u0+alpha*u1, c) <= delta }
      = the gamma-explainable / line-incidence count (F3, the MCA wall object).

CLAIM (C051):  for f(alpha) := nearest codeword,  A_delta(u,f) == B_delta(u)  exactly.
This is the "identity-level, no analytic slack" assertion.  If they differ, the map
loses/gains slack and the claim of conservation is wrong.

We brute-force exact decoding (radius <= delta*n) over small proper-subgroup primes.
"""
import itertools, sys

def find_primes_with_subgroup(n, beta_lo, beta_hi, want=2):
    """primes q == 1 mod n, n^beta_lo <= q <= n^beta_hi, n a PROPER subgroup (n < q-1)."""
    lo = int(n**beta_lo); hi = int(n**beta_hi)
    out = []
    q = lo + (n - (lo % n)) + 1  # first q>=lo with q==1 mod n
    while q % n != 1: q += 1
    while q <= hi and len(out) < want:
        if q > 2 and is_prime(q) and (q-1) > n and (q-1) % n == 0:
            out.append(q)
        q += n
    return out

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def subgroup(q, n):
    """the order-n dyadic subgroup mu_n of F_q^*."""
    # find a generator g of F_q^*, then mu_n = <g^((q-1)/n)>
    g = primitive_root(q)
    h = pow(g, (q-1)//n, q)
    S = []
    x = 1
    for _ in range(n):
        S.append(x); x = (x*h) % q
    assert len(set(S)) == n
    return S

def primitive_root(q):
    phi = q-1
    fac = factorize(phi)
    for g in range(2, q):
        if all(pow(g, phi//p, q) != 1 for p in fac):
            return g
    raise RuntimeError

def factorize(m):
    f=set(); d=2
    while d*d<=m:
        while m%d==0: f.add(d); m//=d
        d+=1
    if m>1: f.add(m)
    return f

def eval_poly(coeffs, x, q):
    r=0
    for c in reversed(coeffs):
        r=(r*x+c)%q
    return r

def hamming(a,b):
    return sum(1 for x,y in zip(a,b) if x!=y)

def all_codewords(D, k, q):
    """all RS codewords (deg<k) as tuples over domain D. Feasible for small q^k."""
    cws=[]
    for coeffs in itertools.product(range(q), repeat=k):
        cws.append(tuple(eval_poly(coeffs,x,q) for x in D))
    return cws

def main():
    results=[]
    # n = 8, proper subgroup, multiple primes, beta ~ 1.5-2 (small enough to brute force q^k)
    for n in [8, 16]:
        # need q^k codewords enumerable: keep k small (rate small), q small-ish but PROPER subgroup
        primes = find_primes_with_subgroup(n, 1.3, 2.6, want=3)
        for q in primes:
            D = subgroup(q, n)
            k = 2  # rate k/n; small to enumerate q^k codewords
            if q**k > 400000:   # enumeration budget
                continue
            cws = all_codewords(D, k, q)
            Dn = n
            # delta as fraction; window radius -- test a couple of radii
            for D_int in [Dn - k, Dn - k - 1]:   # decoding radius (integer hamming threshold)
                if D_int < 0: continue
                delta = D_int / Dn
                # pick a NON-degenerate stack u=(u0,u1): both nonzero, u1 a "far" direction.
                # use a deterministic pseudo-random stack from q
                u0 = tuple((7*i + 3) % q for i,_ in enumerate(D))
                u1 = tuple((5*i + 1) % q for i,_ in enumerate(D))
                # F4: curve close set with f(alpha) = nearest codeword
                closeset=set(); badset=set()
                for alpha in range(q):
                    curve = tuple((u0[i] + alpha*u1[i]) % q for i in range(n))
                    dmin = min(hamming(curve,c) for c in cws)
                    # F3 badScalars: exists codeword within radius
                    explainable = (dmin <= D_int)
                    if explainable: badset.add(alpha)
                    # F4 close set: f(alpha)=nearest cw, alpha close iff dist(curve, f)<=D_int
                    #   nearest cw distance is dmin, so close iff dmin<=D_int -- SAME condition
                    if dmin <= D_int: closeset.add(alpha)
                eq = (closeset == badset)
                results.append((n,q,k,D_int,delta,len(closeset),len(badset),eq))
                print(f"n={n} q={q} k={k} radius={D_int} delta={delta:.3f}  "
                      f"#closeset={len(closeset)} #badScalars={len(badset)}  EQUAL={eq}")
    print("\nSUMMARY: all EQUAL =", all(r[7] for r in results), " (",len(results),"cells )")
    # Now the SUBTLETY: the GG25 def fixes f:F->C as ANY codeword-valued function, not
    # necessarily the nearest. Test a DIFFERENT f (a fixed single codeword) to see the gap.
    print("\n--- subtlety: f != nearest codeword (fixed codeword f0) ---")
    for n in [8]:
        primes = find_primes_with_subgroup(n, 1.3, 2.6, want=1)
        for q in primes:
            D=subgroup(q,n); k=2
            if q**k>400000: continue
            cws=all_codewords(D,k,q)
            u0=tuple((7*i+3)%q for i in range(n)); u1=tuple((5*i+1)%q for i in range(n))
            f0=cws[3]  # a fixed codeword as f(alpha)=f0 for all alpha
            D_int=n-k
            cs_fixed=set(); badset=set()
            for alpha in range(q):
                curve=tuple((u0[i]+alpha*u1[i])%q for i in range(n))
                if hamming(curve,f0)<=D_int: cs_fixed.add(alpha)
                if min(hamming(curve,c) for c in cws)<=D_int: badset.add(alpha)
            print(f" n={n} q={q}: #closeset(f=f0)={len(cs_fixed)}  #badScalars(nearest)={len(badset)}  "
                  f"closeset SUBSET bad={cs_fixed<=badset}")

if __name__=="__main__":
    main()

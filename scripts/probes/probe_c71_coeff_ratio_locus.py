#!/usr/bin/env python3
"""
#444 door-(iv) Lane-1 — FOLLOW-ON to _DoorIVC71MultiTermCoeffInterference (commit 3591ed7c8).

That result proved the multi-term worst case is a COEFFICIENT-INTERFERENCE object: [T4] only 3/10
winning (support,coeff) pairs use unit coefficients, so the worst case lives at NON-UNIT coefficient
ratios. The natural next question for an exploitable arithmetic handle:

  Does the worst-case COEFFICIENT RATIO LOCUS itself have arithmetic structure?

If, for the prime-independent winning supports {(1,3,4),(2,3,6),(3,4)}, the ratios r = c2/c1 (2-term)
that ACHIEVE s23max form a STRUCTURED set (e.g. roots of unity, QRs, a coset of <mu>, or values tied
to the dilation generator mu), that is a deeper handle a coefficient-sensitive incidence bound could
grip. If the worst-ratio set is generic / fills F_p* densely with no multiplicative structure, the
handle is just "non-unit" and no finer.

This probe (for a fixed 2-term support, EXACT full-alpha-sweep bad-strength, thin mu_n, NEVER n=q-1):
sweeps the FULL coefficient ratio r in F_p* and records the set R* = { r : strength(X^i + r*X^j) =
max over r }. Then tests R* for:
  (S1) closure under r -> r^{-1} (the i<->j swap symmetry)
  (S2) multiplicative structure: is R* a coset/union-of-cosets of a subgroup of F_p*? (gcd of the
       discrete logs of R* elements; if R* = a single coset of <g^d>, the dlogs are an AP mod (p-1))
  (S3) relation to the dilation generator mu (mu^k for the support gaps): is the worst r a power of
       mu, or r = mu^{i-j} (the eigenvalue ratio), or unrelated?
  (S4) is r ever a root of unity of small order (r^t = 1 for small t)?
EXACT, thin mu_n, NEVER n=q-1, multi-prime incl p>n^3.
"""
import itertools
from math import gcd, sqrt, ceil

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def primes_1_mod_n(n, lo, cap):
    out = []; p = (lo | 1)
    while len(out) < cap:
        if (p - 1) % n == 0 and is_prime(p): out.append(p)
        p += 2
    return out

def prime_factors(m):
    fs = set(); d = 2
    while d*d <= m:
        while m % d == 0: fs.add(d); m //= d
        d += 1
    if m > 1: fs.add(m)
    return fs

def root_of_unity(p, n):
    g = 2
    while True:
        w = pow(g, (p-1)//n, p)
        if w != 1 and pow(w, n, p) == 1 and all(pow(w, n//q, p) != 1 for q in prime_factors(n)):
            return w
        g += 1

def primitive_root(p):
    fs = prime_factors(p-1)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fs):
            return g
    return None

def dlog_table(g, p):
    t = {}; x = 1
    for e in range(p-1):
        t[x] = e; x = x*g % p
    return t

def max_agreement_to_RS(v, dom, k, p):
    n = len(dom); best = 0
    for S in itertools.combinations(range(n), k):
        xs = [dom[i] for i in S]; ys = [v[i] for i in S]; agree = 0
        for jj in range(n):
            xq = dom[jj]; num = 0
            for a in range(k):
                term = ys[a]; xa = xs[a]
                for b in range(k):
                    if b == a: continue
                    term = term * ((xq - xs[b]) % p) % p * pow((xa - xs[b]) % p, p-2, p) % p
                num = (num + term) % p
            if num == v[jj]: agree += 1
        if agree > best:
            best = agree
            if best == n: break
    return best

def bad_strength_vec(fvals, dom, k, p, thr, g0):
    n = len(dom); bad = 0
    for alpha in range(1, p):
        v = [(g0[j] + alpha*fvals[j]) % p for j in range(n)]
        if max_agreement_to_RS(v, dom, k, p) >= thr: bad += 1
    return bad

def evalmono(exps_coeffs, dom, p):
    return [sum(c*pow(x,e,p) for e,c in exps_coeffs) % p for x in dom]

def analyze_ratio_set(Rstar, p, g, dlog, mu, n):
    if not Rstar:
        return "  R* empty"
    out = []
    # S1: inverse closure
    inv_closed = all(pow(r, p-2, p) in Rstar for r in Rstar)
    out.append(f"  [S1] inverse(r->r^-1)-closed: {inv_closed}  |R*|={len(Rstar)}")
    # S2: multiplicative structure via dlogs
    dl = sorted(dlog[r] for r in Rstar)
    diffs = [dl[i+1]-dl[i] for i in range(len(dl)-1)]
    g_ap = 0
    for d in diffs: g_ap = gcd(g_ap, d)
    # also gcd with (p-1) to detect coset-of-subgroup
    sub_idx = gcd(g_ap, p-1) if g_ap else (p-1)
    out.append(f"  [S2] dlog set (base g, mod p-1={p-1}): {dl[:12]}{'...' if len(dl)>12 else ''}")
    out.append(f"       gcd of consecutive dlog-gaps = {g_ap}; gcd with p-1 = {sub_idx} "
               f"(=> R* in coset of subgroup of index {sub_idx if sub_idx else '?'}: "
               f"{'YES structured' if sub_idx not in (0,1) and len(Rstar)>1 else 'no fine structure'})")
    # S3: relation to mu / eigenvalue ratios mu^{i-j}
    mu_powers = {pow(mu, e, p): e for e in range(n)}
    in_mu = {r: mu_powers[r] for r in Rstar if r in mu_powers}
    out.append(f"  [S3] R* elements that are powers of dilation mu (mu^e, e in 0..n-1): {in_mu}")
    # S4: small-order roots of unity
    small_ord = {}
    for r in Rstar:
        for t in range(2, n+1):
            if pow(r, t, p) == 1:
                small_ord[r] = t; break
    out.append(f"  [S4] R* elements that are small-order roots of unity (order<=n): {small_ord}")
    return "\n".join(out)

def run(n, plist, k):
    rho = k/n; thr = ceil(sqrt(rho)*n)
    # the prize-independent winning 2-term supports from 3591ed7c8 (drop the 3-term for ratio clarity)
    supports2 = [(3,4)]   # the lone winning genuine 2-term support
    print(f"\n=== n={n} k={k} thr={thr}/{n}  winning 2-term support(s)={supports2} ===")
    for p in plist:
        w = root_of_unity(p, n); dom = [pow(w,j,p) for j in range(n)]
        g0 = evalmono([(k+1,1)], dom, p)
        g = primitive_root(p); dlog = dlog_table(g, p)
        tag = "p>n^3" if p > n**3 else "p<=n^3"
        for (i,j) in supports2:
            best = 0; strength_by_r = {}
            for r in range(1, p):
                fv = evalmono([(i,1),(j,r)], dom, p)
                if all(x==0 for x in fv): continue
                s = bad_strength_vec(fv, dom, k, p, thr, g0)
                strength_by_r[r] = s
                best = max(best, s)
            Rstar = set(r for r,s in strength_by_r.items() if s == best)
            print(f"  p={p} ({tag}) support=({i},{j}): max-strength={best} over r; |R*|={len(Rstar)} "
                  f"(of {p-1} ratios)")
            print(analyze_ratio_set(Rstar, p, g, dlog, w, n))

if __name__ == "__main__":
    run(8, primes_1_mod_n(8, 16, 2) + primes_1_mod_n(8, 8**3+1, 1), 2)
    print("\nDONE")

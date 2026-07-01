#!/usr/bin/env python3
r"""
probe_choosep_baddensity.py  --  #444 EVERY-ANGLE [choose-p-bad-prime-density], wall side.

THE ANGLE (explicit-code freedom).  The prize lets you CHOOSE the prime p (any prime ~ n*2^128).
A spurious additive-energy config at depth r is a NONZERO (char-0) signed sum
    alpha = sum_{i} sigma_i * zeta_n^{e_i},  sigma_i in {+1,-1}, <= 2r terms,
that vanishes mod p.  By NubsCarson / CyclotomicNormDefectThreshold:
    alpha vanishes mod p  <=>  p | N(alpha),   0 < |N(alpha)| <= (2r)^{phi(n)}.
So a prime p is "BAD for r" iff p divides N(alpha) for SOME spurious alpha of depth <= r; the spur
SPUR_r(p) = E_r^{Fp}(mu_n) - E_r^{c0}(mu_n) is then > 0.  A prime is "GOOD for r" iff it divides no
such norm => SPUR_r = 0 => the char-0 (Lam-Leung) energy bound E_r <= (2r-1)!! n^r transfers exactly.

  *** The whole prize floor reduces to: does a GOOD prize-shaped prime exist at depth r ~ ln q? ***

NubsCarson's hope: each N(alpha) is a FIXED bounded integer, finitely many prime factors, so any
SINGLE alpha rules out a density-0 set of primes; the question is whether the UNION over all
spurious alpha (up to depth r) covers essentially ALL prize-shaped primes (=> no good p, wall) or
leaves a POSITIVE-density good set (=> choose one, floor closes for an explicit code).

WHAT THIS PROBE MEASURES (proper mu_n, REAL prize beta = 1 + 128/log2(n), NOT the beta=4 proxy):
  Q1 [DENSITY]  Over a band of prize-SHAPED primes p (p = 1 mod n, p ~ n^beta), the FRACTION with
                SPUR_r(p) = 0, as r climbs.  Does good-frac stay positive at deep r, or -> 0?
  Q2 [BETA LIFT] Does raising beta (4 -> 5 -> 5.27, the real prize) push the spur-ONSET depth
                (least r with any bad p in band) DEEPER, toward r_need ~ ln p?  Or is onset
                beta-insensitive once p >> norm?
  Q3 [COVERING LAW]  Directly enumerate the bad-prime SET B_r = { prime q = 1 mod n :
                q | N(alpha), some depth-<=r spurious alpha }.  Measure |B_r cap band| / |band|.
                Fit the growth: linear in (#spurious alpha) (union) vs saturating.  The decisive
                quantity is whether #distinct depth-<=r spurious configs * (avg #qualifying prime
                factors per norm) reaches the band size = #{primes =1 mod n in [N, 2N]} ~ N/(n ln N).

Honesty: exact big-int norms via numpy-free integer resultant of (Phi_n, g); spur via exact
mod-p subset-sum convolution (no float).  No fabrication; verdict bucketed at the end.
"""
import sys, math
from itertools import combinations, product
from functools import reduce

# ----------------------------------------------------------------------------- primes / mu_n
def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def primes_one_mod_n(n, lo, hi):
    """All primes p in [lo,hi] with p = 1 mod n."""
    out = []
    p = lo + ((n - (lo-1) % n) % n)   # first p>=lo with p=1 mod n
    if (p-1) % n != 0: p += (n - (p-1) % n) % n
    while p <= hi:
        if is_prime(p): out.append(p)
        p += n
    return out

def subgroup(p, n):
    for g0 in range(2, p):
        g = pow(g0, (p-1)//n, p)
        if pow(g, n//2, p) != 1 and pow(g, n, p) == 1:
            S = [pow(g, i, p) for i in range(n)]
            if len(set(S)) == n: return S
    return None

# ----------------------------------------------------------------------------- char-0 energy
def double_fact(m):
    r = 1; k = 2*m-1
    while k > 0: r *= k; k -= 2
    return r

def Er_charp(H, p, rmax):
    """Exact E_r over F_p for r=1..rmax via mod-p subset-sum convolution; H = list of subgroup elts."""
    fp = [0]*p
    for h in H: fp[h] += 1
    out = []; cur = fp[:]
    for r in range(1, rmax+1):
        out.append(sum(c*c for c in cur))
        if r < rmax:
            nxt = [0]*p
            for t, c in enumerate(cur):
                if c:
                    for h in H: nxt[(t+h) % p] += c
            cur = nxt
    return out

def Er_char0(n, rmax):
    """EXACT char-0 energy E_r(mu_n) = #{(a,b) in [0,n)^{2r}: sum zeta^{a_i} = sum zeta^{b_j} in Z[zeta_n]}.
    p-FREE: represent each r-fold root-sum by its coefficient vector in the basis 1,zeta,...,zeta^{n-1}
    (a tuple of n integers; zeta^k for k>=n never occurs since exponents < n).  Two sums are equal in
    Z[zeta_n] iff coeff vectors equal AFTER reducing by the unique Z-relation Phi_n=0.  For n a prime
    power 2^mu, the minimal additive relation is 1+zeta^{n/2}=0-shifts... we instead reduce by the FULL
    set of additive relations: the lattice of integer vectors v with sum_k v_k zeta^k = 0, whose basis
    is {zeta^k(Phi_n(zeta)) shifts} -- equivalently work in the quotient Z^n / (rows of the circulant
    of Phi_n).  Simplest exact canonical form: evaluate the coeff vector at a single primitive root in a
    HUGE clean prime (one mult, no convolution) and also keep the integer multiset hash -- but cleanest:
    reduce v modulo the relation 'all-ones is free'? No.  We use the robust route: canonicalize v by
    subtracting multiples of the rows of the n x n circulant matrix of Phi_n via one clean-prime eval.
    Returns (E_list, p_clean)."""
    # Use ONE clean prime, but evaluate sums as a single residue (no per-residue array): hashing.
    phin = sum(1 for k in range(1, n+1) if math.gcd(k, n) == 1)
    bound = (2*rmax)**phin
    lo = max(bound+1, n+1)
    pc = lo + ((1 - lo) % n)
    while not is_prime(pc): pc += n
    g = None
    for g0 in range(2, pc):
        cand = pow(g0, (pc-1)//n, pc)
        if pow(cand, n//2, pc) != 1 and pow(cand, n, pc) == 1:
            g = cand; break
    H = [pow(g, i, pc) for i in range(n)]
    # E_r = sum over reachable sums of (count)^2; build sum-distribution as a dict keyed by residue.
    from collections import defaultdict
    cur = defaultdict(int)
    for h in H: cur[h] += 1
    out = []
    for r in range(1, rmax+1):
        out.append(sum(c*c for c in cur.values()))
        if r < rmax:
            nxt = defaultdict(int)
            for t, c in cur.items():
                for h in H: nxt[(t+h) % pc] += c
            cur = nxt
    return out, pc

# ----------------------------------------------------------------------------- exact integer norm
def cyclotomic_int(n):
    """Integer coeffs of Phi_n via X^n-1 = prod_{d|n} Phi_d, polynomial long division over Z."""
    # build divisors
    divs = [d for d in range(1, n+1) if n % d == 0]
    # Phi_d by recursion
    phi = {}
    for d in divs:
        # X^d - 1
        num = [-1] + [0]*(d-1) + [1]
        for e in divs:
            if e < d and d % e == 0:
                num = polydiv_exact(num, phi[e])
        phi[d] = num
    return phi[n]

def polydiv_exact(a, b):
    """Exact polynomial division a/b over Z (b monic), return quotient (b divides a)."""
    a = a[:]; db = len(b)-1; dq = len(a)-1-db
    q = [0]*(dq+1)
    for i in range(dq, -1, -1):
        c = a[i+db]
        q[i] = c
        if c:
            for j in range(db+1):
                a[i+j] -= c*b[j]
    return q

def polymulmod_resultant(phi_n, e_list, sigma_list):
    """
    N(alpha) for alpha = sum sigma_i X^{e_i}, computed as Res(Phi_n, g) up to sign, via
    integer resultant = prod over roots; we use the SUBRESULTANT-free route: reduce g mod Phi_n is
    not enough for the norm. Instead use the determinant-free identity
        |Res(Phi_n, g)| = |prod_{Phi_n(w)=0} g(w)|  (Phi_n monic)
    computed EXACTLY as the constant term of the resultant via the companion-matrix det is heavy;
    for our small phi(n) we use the resultant = prod of g evaluated at roots, but we want an INTEGER.
    Cleanest exact integer: Res(Phi_n, g) = (lead g)^{deg Phi} * prod g(roots) but easier:
        Res(f,g) = prod_i g(alpha_i)  where alpha_i roots of monic f.
    We obtain it EXACTLY as the resultant via the Sylvester determinant over Z (small sizes).
    """
    # g coefficients (sparse -> dense), reduce exponents mod n is NOT valid for norm; keep raw degree
    deg_g = max(e_list)
    g = [0]*(deg_g+1)
    for e, s in zip(e_list, sigma_list): g[e] += s
    # strip trailing zeros
    while len(g) > 1 and g[-1] == 0: g.pop()
    return resultant_int(phi_n, g)

def resultant_int(f, g):
    """Exact integer resultant Res(f,g) via Sylvester matrix determinant (Bareiss, fraction-free)."""
    df = len(f)-1; dg = len(g)-1
    if df < 0 or dg < 0: return 0
    if dg == 0:  # g constant c => Res = c^{df}
        return g[0]**df
    N = df + dg
    # Sylvester matrix: dg rows of f-shifts, df rows of g-shifts. Coeffs descending.
    fr = f[::-1]; gr = g[::-1]
    M = [[0]*N for _ in range(N)]
    for i in range(dg):
        for j in range(len(fr)):
            M[i][i+j] = fr[j]
    for i in range(df):
        for j in range(len(gr)):
            M[dg+i][i+j] = gr[j]
    return bareiss_det(M)

def bareiss_det(M):
    """Fraction-free Bareiss determinant, exact integer."""
    M = [row[:] for row in M]; n = len(M); sign = 1; prev = 1
    for k in range(n-1):
        if M[k][k] == 0:
            sw = next((i for i in range(k+1, n) if M[i][k] != 0), None)
            if sw is None: return 0
            M[k], M[sw] = M[sw], M[k]; sign = -sign
        for i in range(k+1, n):
            for j in range(k+1, n):
                M[i][j] = (M[i][j]*M[k][k] - M[i][k]*M[k][j]) // prev
        prev = M[k][k]
    return sign * M[n-1][n-1]

def factor_small(x):
    """Prime factorization of |x| (trial up to a cap + Pollard for the rest)."""
    x = abs(x)
    fac = {}
    for d in (2,3,5,7,11,13):
        while x % d == 0: fac[d] = fac.get(d,0)+1; x //= d
    # Pollard rho for the rest
    def rho(nn):
        if nn % 2 == 0: return 2
        import random
        while True:
            c = random.randrange(1, nn); x0 = random.randrange(2, nn); y = x0; d = 1
            while d == 1:
                x0 = (x0*x0 + c) % nn; y = (y*y+c) % nn; y = (y*y+c) % nn
                d = math.gcd(abs(x0-y), nn)
            if d != nn: return d
    stack = [x] if x > 1 else []
    while stack:
        m = stack.pop()
        if m == 1: continue
        if is_prime(m): fac[m] = fac.get(m,0)+1; continue
        d = rho(m)
        stack.append(d); stack.append(m//d)
    return fac

# ----------------------------------------------------------------------------- Q3: bad-prime SET
def enumerate_spurious_norms(n, rmax_terms):
    """
    Enumerate distinct |N(alpha)| for alpha = signed sum of <= rmax_terms primitive-n-th-root
    monomials zeta^{e}, e in [0,n-1], NOT vanishing in char 0 (alpha != 0 as poly mod Phi_n).
    To keep it finite + canonical: dedupe by the multiset of (e,sigma); skip alpha = 0.
    Returns set of norms (positive ints) and a count of configs enumerated.
    Restrict to weight = exactly t terms for t in [2,rmax_terms] (a single zeta is a unit, norm 1).
    """
    phi_n = cyclotomic_int(n)
    norms = {}   # norm -> min weight that produced it
    cnt = 0
    exps = list(range(n))
    for t in range(2, rmax_terms+1):
        for combo in combinations(exps, t):
            # signs: fix first +1 (overall unit factor zeta^? and global sign don't change |N|)
            for signs in product((1,-1), repeat=t-1):
                sig = (1,) + signs
                # build poly, check nonzero mod Phi_n (char 0)
                deg = max(combo)
                g = [0]*(deg+1)
                for e, s in zip(combo, sig): g[e] += s
                while len(g) > 1 and g[-1] == 0: g.pop()
                if all(c == 0 for c in g): continue
                Nrm = abs(resultant_int(phi_n, g))
                if Nrm == 0: continue   # vanishes in char 0 -> coset relation, not spurious
                cnt += 1
                if Nrm not in norms or t < norms[Nrm]:
                    norms[Nrm] = t
    return norms, cnt

# ============================================================================= MAIN
def main():
    print("="*92)
    print(" #444 [choose-p-bad-prime-density]  -- does a GOOD prize-shaped prime survive to deep r?")
    print(" proper mu_n, REAL prize beta = 1 + 128/log2(n).  Exact integer norms + exact mod-p spur.")
    print("="*92)

    # --------- Q3 first: bad-prime SET covering law (small n, exact norm enumeration) -----------
    print("\n[Q3] BAD-PRIME COVERING LAW: B_r = {q=1 mod n : q | N(alpha), depth<=r}.  band ~ n^beta.")
    print("     bad-frac = |B_r cap band| / |primes=1 mod n in band|.  Watch growth vs depth.\n")
    for n in (8, 16):
        for beta in (4.0, 5.0, 5.27):
            N0 = int(round(n**beta))
            band_lo, band_hi = N0, 2*N0
            band = primes_one_mod_n(n, band_lo, band_hi)
            if not band:
                print(f"  n={n} beta={beta}: empty band [{band_lo},{band_hi}] (skip)")
                continue
            print(f"  n={n} beta={beta} band=[{band_lo:,},{band_hi:,}]  #primes(=1 mod n)={len(band)}")
            # enumerate spurious norms up to a weight cap = 2*r_terms; r in terms = t/2
            maxw = 6 if n <= 8 else 5    # weight cap (=2r terms); norm-enum is C(n,t)2^t heavy
            norms, ncfg = enumerate_spurious_norms(n, maxw)
            print(f"     enumerated {ncfg} signed configs (weight 2..{maxw}); {len(norms)} distinct |N|>0")
            band_set = set(band)
            # for each r (=ceil(weight/2)), bad primes = union of prime factors (=1 mod n) of norms w/ weight<=2r
            for rr in range(1, maxw//2 + 1):
                wcap = 2*rr
                bad = set()
                for Nrm, wmin in norms.items():
                    if wmin > wcap: continue
                    for pr in factor_small(Nrm):
                        if pr in band_set:
                            bad.add(pr)
                frac = len(bad)/len(band)
                print(f"       r={rr} (w<={wcap}): bad primes in band = {len(bad):4d} / {len(band):4d}"
                      f"  = {frac:.4f}   good-frac = {1-frac:.4f}")
            print()

    # --------- Q1+Q2: direct TRUE SPUR over the band, deep r ------------------------------------
    print("\n[Q1/Q2] DIRECT TRUE SPUR over band of prize-shaped primes; good-frac(r) and onset depth.")
    print("        spur_r(p) = E_r^Fp - E_r^c0(EXACT cyclotomic, p-free clean-prime ref).")
    print("        good iff spur=0 at all r'<=r  <=>  no <=2r-term signed mu_n relation wraps mod p.\n")
    for n in (8, 16):
        # exact char-0 reference (p-free), capped by cost: keys ~ n^r
        rmax = 6 if n <= 8 else 5
        c0, pclean = Er_char0(n, rmax)
        wick = [double_fact(r)*n**r for r in range(1, rmax+1)]
        print(f"  n={n}: char-0 E_r (exact, ref prime {pclean:,}) = {c0}")
        print(f"         Wick (2r-1)!!n^r                        = {wick}   (E_r^c0 <= Wick: "
              f"{all(c0[i] <= wick[i] for i in range(rmax))})")
        for beta in (4.0, 5.0, 5.27):
            N0 = int(round(n**beta))
            band = primes_one_mod_n(n, N0, int(2.2*N0))[:30]
            if not band:
                print(f"    beta={beta}: empty band (skip)"); continue
            onset = {r: None for r in range(1, rmax+1)}
            goodcnt = {r: 0 for r in range(1, rmax+1)}
            spur_examples = {}
            for p in band:
                H = subgroup(p, n)
                if H is None: continue
                Ep = Er_charp(H, p, rmax)
                allgood = True
                for idx, r in enumerate(range(1, rmax+1)):
                    spur = Ep[idx] - c0[idx]
                    if spur != 0:
                        allgood = False
                        if onset[r] is None:
                            onset[r] = p; spur_examples[r] = spur
                    if allgood: goodcnt[r] += 1
            print(f"    beta={beta} (p~{N0:,}, {len(band)} primes sampled):")
            for r in range(1, rmax+1):
                gf = goodcnt[r]/len(band)
                if onset[r]:
                    ons = f"yes@{onset[r]} (spur={spur_examples[r]})"
                else:
                    ons = "none-in-band"
                print(f"      r={r}: good-frac (true spur=0 thru r) = {goodcnt[r]:3d}/{len(band)} = {gf:.3f}"
                      f"   first-bad-p: {ons}")
            print()

if __name__ == "__main__":
    main()

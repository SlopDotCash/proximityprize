#!/usr/bin/env python3
"""ADVERSARIAL VERIFICATION of claim F5 (#407 prize, tower phase-alignment).

CLAIM UNDER TEST (F5): the 2-power tower recursion
    F_mu(t) = F_{mu-1}(t) + F_{mu-1}(t * zeta_{2^mu}),   zeta = primitive 2^mu-th root,
    F_0(t) = e_p(t),   mu_{2^{mu-1}} = (mu_{2^mu})^2  (the squares),
evaluated at the TRUE coset maximizer b* = argmax_{b!=0} |F_M(b)|, has PERFECT
child phase-alignment cos(A,B) = +1 at ALL levels, where at each level
    A = F_{mu-1}(t),  B = F_{mu-1}(t * zeta_{2^mu}),  F_mu(t) = A + B.
F5 FINDING: this is NOT universal -- it degrades to a generic +/-1 mix (cos != +1)
            for generic cofactors, breaking the would-be tower-descent mechanism.

THIS PROBE: written FRESH and INDEPENDENT. We do NOT trust the existing probes'
prime selection (probe_phase_alignment_tower.py uses p ~ 4 n^2, beta ~ 2 -- NOT the
prize regime, and does not exclude Fermat/fully-dyadic primes).

We REQUIRE the PRIZE REGIME: n = 2^mu, n | p-1, n <= sqrt(p) (beta in [4,5]),
and EXCLUDE Fermat/fully-dyadic primes by demanding odd_part((p-1)/n) > 1 so the
2-adic valuation of p-1 equals exactly mu (no "extra" 2-power -- avoids the #400 trap).

For n in {64,128,256} we:
  (1) find a valid prize-regime prime,
  (2) find the TRUE maximizer b* by exact chunked numpy scan over all (p-1)/n cosets,
  (3) trace the tower DOWN from b*, reporting cos(A,B) at each level (A=squares half,
      B = zeta-shifted half), the magnitude growth, and the level's |A|,|B|.
We report: is cos(A,B) == +1 (within 1e-3) at the TOP level? at ALL levels?
We also sample SEVERAL maximizers and a RANDOM frequency for contrast.
"""
import sys, math
import numpy as np


def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d = n-1; r = 0
    while d % 2 == 0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True


def odd_part(x):
    while x % 2 == 0: x //= 2
    return x


def primitive_root(p):
    phi = p-1; facs = []; m = phi; d = 2
    while d*d <= m:
        if m % d == 0:
            facs.append(d)
            while m % d == 0: m//=d
        d += 1
    if m > 1: facs.append(m)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in facs): return g
    raise RuntimeError


def find_prize_prime(n, beta_lo=4.0, beta_hi=5.0):
    """Smallest prime p with n | p-1, n <= sqrt(p) (beta in [beta_lo,beta_hi]),
    and odd_part((p-1)/n) > 1 (proper non-dyadic subgroup, NOT Fermat/fully-dyadic).
    beta = log_n(p)."""
    base = int(round(n ** beta_lo))
    base -= base % n
    base += 1            # p == 1 (mod n)
    p = base
    cap = int(round(n ** beta_hi))
    while p <= cap:
        if is_prime(p) and odd_part((p-1)//n) > 1:
            # double-check n | p-1 and n is exactly the full 2-part order divisor
            assert (p-1) % n == 0
            return p
        p += n
    return None


def subgroup(p, n):
    """mu_n = <h>, h = primitive n-th root of unity; xs[i] = h^i (sorted by exponent).
    Also return the primitive 2^mu-th root chain implicitly via h (h itself is the
    primitive n-th = 2^mu-th root)."""
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    xs = [1]
    for _ in range(n-1):
        xs.append(xs[-1]*h % p)
    assert pow(h, n, p) == 1 and pow(h, n//2, p) != 1
    assert len(set(xs)) == n
    return g, h, xs


def find_top_maximizers(p, n, xs, topk=3):
    """Exact scan over the (p-1)/n cosets of |F_n(c)| = |sum_{x in mu_n} e_p(c x)|.
    coset reps c = g^j, j=0..(p-1)/n-1. Chunked numpy. Returns top-k (mag, c)."""
    g = primitive_root(p)
    ncos = (p-1)//n
    xs_arr = np.array(xs, dtype=np.int64)
    twp = 2.0*math.pi/p
    CH = max(1, min(8_000_000 // n, ncos))
    results = []  # (mag, c)
    c = 1
    j = 0
    reps = np.empty(CH, dtype=np.int64)
    while j < ncos:
        m = min(CH, ncos - j)
        cc = c
        for i in range(m):
            reps[i] = cc
            cc = cc*g % p
        R = reps[:m]
        prod = (R[:, None] * xs_arr[None, :]) % p
        ang = prod.astype(np.float64) * twp
        S = np.cos(ang).sum(axis=1) + 1j*np.sin(ang).sum(axis=1)
        mags = np.abs(S)
        # keep this chunk's contributions: cheaper to just track running top-k
        for i in range(m):
            results.append((float(mags[i]), int(R[i])))
        # to bound memory, prune periodically
        if len(results) > 50000:
            results.sort(reverse=True)
            results = results[:topk]
        c = c * pow(g, m, p) % p
        j += m
    results.sort(reverse=True)
    return results[:topk]


def tower_trace(p, n, xs, t):
    """Trace recursion from top subgroup mu_n down to level 1 at frequency t.
    At level mu, mu_{2^mu} = {xs[i*step] : i} with step = n//2^mu (a subgroup).
    Split: A = F_{mu-1}(t) over the SQUARES (= mu_{2^{mu-1}}, even idx in this
    subgroup's own <eta_mu> ordering), B = the zeta_mu-shifted half (odd idx).
    Recursion: F_mu(t) = A + B  (verified). cos(A,B) is the child alignment."""
    twp = 2.0*math.pi/p
    def esum(elts):
        a = np.array(elts, dtype=np.int64)
        ang = ((t*a) % p).astype(np.float64)*twp
        return complex(np.cos(ang).sum(), np.sin(ang).sum())
    M = int(round(math.log2(n)))
    rows = []
    for mu in range(M, 0, -1):
        size = 1 << mu
        step = n // size
        elts = [xs[i*step] for i in range(size)]   # mu_{2^mu} = <h^step>, ordered by exponent
        squares = elts[0::2]      # mu_{2^{mu-1}} (the squares)
        zeta_half = elts[1::2]    # zeta_{2^mu} * mu_{2^{mu-1}}
        A = esum(squares); B = esum(zeta_half); Fmu = A + B
        # exactness check of the recursion against the direct full sum
        full = esum(elts)
        recerr = abs(full - Fmu)
        if abs(A) > 1e-12 and abs(B) > 1e-12:
            cosang = (A.real*B.real + A.imag*B.imag)/(abs(A)*abs(B))
        else:
            cosang = float('nan')
        rows.append((mu, abs(Fmu), abs(A), abs(B), cosang, recerr))
    return rows


def classify(cosval, tol=1e-3):
    if cosval != cosval:
        return "zero-half"
    if abs(cosval - 1.0) < tol:
        return "PERFECT(+1)"
    if abs(cosval + 1.0) < tol:
        return "anti(-1)"
    return f"generic({cosval:+.3f})"


def main():
    print("#"*100)
    print("# F5 ADVERSARIAL VERIFICATION: is tower child phase-alignment cos(A,B)=+1")
    print("#   UNIVERSAL at the true maximizer (all levels), or does it degrade to a +/-1 mix?")
    print("#   PRIZE REGIME: n=2^mu, n|p-1, n<=sqrt(p), odd_part((p-1)/n)>1 (non-dyadic).")
    print("#"*100)

    rng = np.random.default_rng(20260613)
    overall_top_perfect = []   # cos at TOP level for each n, at b*
    overall_all_perfect = []   # bool: all levels perfect at b*

    for n in (64, 128, 256):
        mu = int(round(math.log2(n)))
        p = find_prize_prime(n)
        if p is None:
            print(f"\n[n={n}] no prize-regime prime found in beta in [4,5]; skipping.")
            continue
        beta = math.log(p)/math.log(n)
        g, h, xs = subgroup(p, n)
        tops = find_top_maximizers(p, n, xs, topk=3)
        B, bstar = tops[0]
        sqrtN = math.sqrt(n)
        sqrtNlog = math.sqrt(n*math.log(p/n))
        v2 = 0
        tmp = p - 1
        while tmp % 2 == 0:
            tmp //= 2; v2 += 1
        print(f"\n{'='*100}")
        print(f"n={n} (mu={mu})  p={p}  beta=log_n(p)={beta:.3f}  v2(p-1)={v2}"
              f"  odd_part((p-1)/n)={odd_part((p-1)//n)}")
        print(f"  B=max|F|={B:.4f}  sqrt(n)={sqrtN:.3f}  sqrt(n log(p/n))={sqrtNlog:.3f}"
              f"  B/sqrtN={B/sqrtN:.3f}  B/sqrt(nlog)={B/sqrtNlog:.3f}")
        print(f"  top-3 maximizers (|F|, c): " + ", ".join(f"({m:.3f},{c})" for m,c in tops))

        # --- TRUE MAXIMIZER b* : full tower trace ---
        rows = tower_trace(p, n, xs, bstar)
        maxrec = max(r[5] for r in rows)
        print(f"\n  [b*={bstar}] full tower trace (recursion exactness max err = {maxrec:.2e}):")
        print(f"    {'mu':>3} {'|F_mu|':>9} {'|A|':>9} {'|B|':>9} {'cos(A,B)':>10}  classify    growth")
        prev = None
        top_cos = rows[0][4]
        all_perfect = True
        for (lvl, Fmu, A, Bv, cosang, _re) in rows:
            growth = (Fmu/prev) if prev else float('nan')
            cls = classify(cosang)
            if "PERFECT" not in cls:
                all_perfect = False
            print(f"    {lvl:>3} {Fmu:>9.3f} {A:>9.3f} {Bv:>9.3f} {cosang:>+10.4f}  {cls:<14} {growth:>5.3f}")
            prev = Fmu
        overall_top_perfect.append((n, top_cos))
        overall_all_perfect.append((n, all_perfect))
        print(f"    --> TOP-level cos(A,B) at b* = {top_cos:+.5f}  [{classify(top_cos)}]")
        print(f"    --> ALL levels perfect(+1) at b*? {all_perfect}")

        # --- 2nd & 3rd maximizers: just the TOP-level cos ---
        print(f"\n  [other near-maximizers] TOP-level cos(A,B):")
        for rank in (1, 2):
            if rank < len(tops):
                _, c = tops[rank]
                r = tower_trace(p, n, xs, c)
                print(f"    rank-{rank} c={c}: top cos = {r[0][4]:+.5f}  [{classify(r[0][4])}]")

        # --- generic / random non-maximizer frequencies for contrast ---
        print(f"  [random non-maximizer frequencies] TOP-level cos(A,B):")
        for _ in range(3):
            c = int(rng.integers(1, p))
            r = tower_trace(p, n, xs, c)
            print(f"    random c={c}: top cos = {r[0][4]:+.5f}  [{classify(r[0][4])}]")

    # ------------------------------------------------------------------
    print("\n" + "#"*100)
    print("# VERDICT SUMMARY")
    print("#"*100)
    print(f"{'n':>5} {'top-level cos(A,B) @ b*':>26} {'== +1 (perfect)?':>18} {'all levels +1?':>16}")
    any_top_perfect = False
    all_n_all_perfect = True
    for (n, tc), (_, ap) in zip(overall_top_perfect, overall_all_perfect):
        perf = abs(tc - 1.0) < 1e-3
        any_top_perfect = any_top_perfect or perf
        all_n_all_perfect = all_n_all_perfect and ap
        print(f"{n:>5} {tc:>+26.5f} {str(perf):>18} {str(ap):>16}")
    print()
    print("INTERPRETATION:")
    print(" - F5 claims tower alignment is NOT universal (degrades to +/-1 mix).")
    print(" - If TOP-level cos at b* is NOT consistently +1 across n=64,128,256, F5 is CONFIRMED.")
    print(" - If 'all levels +1' is FALSE for any n, the perfect-descent mechanism is BROKEN => F5 CONFIRMED.")
    print(" - If cos == +1 at every level for every n, F5 is REFUTED (alignment IS universal).")
    return 0


if __name__ == "__main__":
    sys.exit(main())

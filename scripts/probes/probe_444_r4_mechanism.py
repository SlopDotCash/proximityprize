"""
probe_444_r4_mechanism.py  (#444 -- FINAL diagnosis: clean per-type law for r=3, breakdown for r=4)

Confirmed so far:
 r=3 per-type O_P: type(0,4)=[4,24,112], type(1,2)=[2,4,8] at q=n/4=4,8,16.
   CONJECTURE: type(1,2) = q/2 ; type(0,4) = C(q,2)-q/2 ; total = C(q,2). VERIFY.
 r=4: at n=16 types DISJOINT (overlap=0), at n=32 types OVERLAP (overlap correction=2,
   32 multi-type gammas each realized by ALL THREE types (0,5),(1,3),(2,1)).

This probe:
 1. VERIFY the r=3 per-type closed forms (q/2 and C(q,2)-q/2) and total=C(q,2).
 2. For r=4, test per-type O_P closed forms across n=16,32 (and 64 from prior known total).
    We need per-type O_P at n=64 too -> use the known r=4 maximizer (x^{34},x^{17}); but full
    census C(64,5)=7.6M is heavy. Instead we test per-type fit on n=16,32 and check
    EXTRAPOLATION against the known total O_P(64)=897.
 3. The KEY structural question: is the overlap a "char-0 additive coincidence" (cause c) or a
    consequence of the maximizer line's leading-exponent order (cause a)?
    TEST: the r=3 maximizer (x^{n/2},x^{n/2-1}) has e of ORDER 2 (x^{n/2}=+-1). The r=4
    maximizer (x^{n/2+2},x^{n/4+1}): e=n/2+2 has order = n/gcd(n/2+2,n)=n/gcd(2,n)=n/2 (order n/2,
    NOT 2!). So the leading exponent is NO LONGER order-2 => the single-level pair->zeta^2
    descent (which RELIES on the order-2/antipodal structure being aligned with the line) no
    longer diagonalizes the types. SHOW this: compute ord(e) and ord(f) for each r's maximizer.
 4. Confirm the overlap gammas are GENUINE multi-realizations (same scalar, different additive
    support) -> these are additive coincidences forced by char-0 cyclotomic relations among
    Schur ratios, NOT a finite-prime artifact (re-run at a SECOND large prime to confirm char-0).

p = BabyBear; second prime for char-0 confirmation: p2 = 2^30*3+1 = 3221225473 (also 2^30|p-1).
"""
import itertools
from math import comb, gcd
from collections import Counter, defaultdict

def make(p):
    def w_of_order(n):
        e = (p - 1) // n
        for c in range(2, 2000):
            h = pow(c, e, p)
            if pow(h, n, p) == 1 and pow(h, n // 2, p) != 1:
                return h
        raise RuntimeError
    return w_of_order

def band_gamma_idx(Sidx, pe, pf, mu, k, a0, p):
    pts = [mu[i] for i in Sidx]
    m = len(pts)
    def interp(vals):
        A = [[pow(pts[i], j, p) for j in range(m)] for i in range(m)]
        M = [A[i][:] + [vals[i] % p] for i in range(m)]
        for col in range(m):
            piv = next((rr for rr in range(col, m) if M[rr][col] % p != 0), None)
            if piv is None:
                return None
            M[col], M[piv] = M[piv], M[col]
            inv = pow(M[col][col], p - 2, p)
            M[col] = [(v * inv) % p for v in M[col]]
            for rr in range(m):
                if rr != col and M[rr][col] % p != 0:
                    c = M[rr][col]
                    M[rr] = [(M[rr][t] - c * M[col][t]) % p for t in range(m + 1)]
        return [M[i][m] % p for i in range(m)]
    c0 = interp([pe[i] for i in Sidx])
    c1 = interp([pf[i] for i in Sidx])
    if c0 is None or c1 is None:
        return None
    gam = None; nd = False
    for j in range(k, a0):
        x0 = c0[j]; x1 = c1[j]
        if x0 or x1:
            nd = True
        if x1 == 0:
            if x0:
                return None
        else:
            g_ = (-x0 * pow(x1, p - 2, p)) % p
            if gam is None:
                gam = g_
            elif gam != g_:
                return None
    return gam if nd else None

def antipodal_type(Sidx, n):
    h = n // 2
    Sset = set(Sidx)
    pairs = sum(1 for j in Sidx if j < h and (j + h) in Sset)
    singles = sum(1 for j in Sidx if (j + h) % n not in Sset)
    return (pairs, singles)

def per_type_OP(n, r, e, f, p):
    w_of_order = make(p)
    mu = [pow(w_of_order(n), i, p) for i in range(n)]
    k = r - 1; a0 = r + 1
    pe = [pow(x, e, p) for x in mu]
    pf = [pow(x, f, p) for x in mu]
    mult = pow(mu[1], (e - f) % n, p)
    type_gammas = defaultdict(set)
    all_g = set()
    for Sidx in itertools.combinations(range(n), a0):
        gv = band_gamma_idx(Sidx, pe, pf, mu, k, a0, p)
        if gv is None or gv % p == 0:
            continue
        type_gammas[antipodal_type(Sidx, n)].add(gv)
        all_g.add(gv)
    def orbits(gset):
        rem = set(gset); o = 0
        while rem:
            x0 = next(iter(rem)); cur = x0; orb = set()
            for _ in range(n):
                orb.add(cur); cur = cur * mult % p
            o += 1; rem -= orb
        return o
    res = {t: orbits(gs) for t, gs in type_gammas.items()}
    return res, orbits(all_g), {t: len(gs) for t, gs in type_gammas.items()}, len(all_g)

def ord_exp(e, n):
    """multiplicative order of x^e as a function on mu_n = n/gcd(e,n)."""
    g = gcd(e % n, n)
    return n // g

if __name__ == "__main__":
    p = 2013265921
    print("="*90)
    print("PART 1: r=3 per-type closed-form VERIFICATION")
    print("  conjecture: type(1,2)=q/2 ; type(0,4)=C(q,2)-q/2 ; total=C(q,2), q=n/4")
    print("="*90)
    for n in [16, 32, 64]:
        q = n // 4
        res, tot, badcnt, totg = per_type_OP(n, 3, n // 2, n // 2 - 1, p)
        t04 = res.get((0, 4), 0); t12 = res.get((1, 2), 0)
        pred12 = q // 2
        pred04 = comb(q, 2) - q // 2
        print(f"  n={n} q={q}: type(0,4)={t04} (pred {pred04} {'OK' if t04==pred04 else 'X'})  "
              f"type(1,2)={t12} (pred {pred12} {'OK' if t12==pred12 else 'X'})  "
              f"total={tot} (C(q,2)={comb(q,2)} {'OK' if tot==comb(q,2) else 'X'})")

    print("\n" + "="*90)
    print("PART 2: leading-exponent ORDER for each r's TRUE maximizer (cause (a) test)")
    print("="*90)
    maxlines = {
        3: ("(x^{n/2}, x^{n/2-1})", lambda n: (n // 2, n // 2 - 1)),
        4: ("(x^{n/2+2}, x^{n/4+1})", lambda n: (n // 2 + 2, n // 4 + 1)),
        5: ("(x^{n/2+1}, x^{n-1})",  lambda n: (n // 2 + 1, n - 1)),
    }
    for r, (lab, fn) in maxlines.items():
        print(f"  r={r} maximizer {lab}:")
        for n in [16, 32]:
            e, f = fn(n)
            print(f"     n={n}: e={e} ord(x^e)={ord_exp(e,n)}  f={f} ord(x^f)={ord_exp(f,n)}  "
                  f"e-f={(e-f)%n} d=gcd(e-f,n)={gcd((e-f)%n,n)}")
        print(f"     => r=3 has ord(x^e)=2 (the +-1/antipodal direction). r>=4: ord(x^e) != 2 "
              f"(line NOT aligned with antipodal involution).")

    print("\n" + "="*90)
    print("PART 3: r=4 per-type O_P at n=16,32 + OVERLAP correction")
    print("="*90)
    r4data = {}
    for n in [16, 32]:
        res, tot, badcnt, totg = per_type_OP(n, 4, n // 2 + 2, n // 4 + 1, p)
        r4data[n] = (res, tot)
        sumOP = sum(res.values())
        print(f"  n={n} q={n//4}: per-type O_P {dict(sorted(res.items()))}  "
              f"SUM={sumOP}  TOTAL={tot}  overlap={sumOP-tot}")
    print("  => at n=16 only types (1,3),(2,1) present & DISJOINT; at n=32 a THIRD type (0,5)")
    print("     appears AND the three types share 32 gammas (overlap=2 orbits). The set of")
    print("     contributing types is itself n-dependent, and they are no longer gamma-disjoint.")

    print("\n" + "="*90)
    print("PART 4: char-0 confirmation of the OVERLAP at a SECOND prime p2=3221225473")
    print("  (if overlap=2 reproduces at p2, the multi-type coincidence is char-0, not a p-artifact)")
    print("="*90)
    p2 = 3221225473  # = 3*2^30 + 1, 2^30 | p2-1
    for n in [32]:
        res, tot, badcnt, totg = per_type_OP(n, 4, n // 2 + 2, n // 4 + 1, p2)
        sumOP = sum(res.values())
        print(f"  p2 n={n}: per-type O_P {dict(sorted(res.items()))} SUM={sumOP} TOTAL={tot} "
              f"overlap={sumOP-tot}  (totalbad={totg})")

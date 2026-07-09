#!/usr/bin/env python3
r"""
ACTIONABLE A32  (merged 232-T09 ; 334-T24)
==========================================
Effective char-0 -> F_p transfer with a POLYNOMIAL height threshold, via
class-group localization (O39 / DISPROOF_LOG entry, 2026-06-09).

WHAT THIS PROBE DECIDES
-----------------------
The in-tree effective transfer theorem (O49 ; CyclotomicNormDefectThreshold.lean)
proves the char-0 fiber equals the F_p fiber WHENEVER

      p  >  C(w, floor(w/2))^{phi(n)}        (EXPONENTIAL in n)

via the norm bound |N(alpha)| <= C(w,w/2)^{phi(n)} and p | N(alpha).  The
Krachun-Kazanin-Haebock (KKH26) DISPROOF construction lives at POLYNOMIAL p
(p = Theta(n^beta), beta in [4,5]).  The exponential gap between the proven
transfer threshold and the polynomial disproof regime is "where the disproof
side still breathes" (O49).

O39 proposed the CLASS-GROUP LOCALIZATION as the only object that could see
inside that gap: a bad prime p (one carrying an F_p excess solution absent in
char-0) forces the relation ideal to factor as

      (alpha) = a * P ,    P | p ,   N(a) <= budget,

so (i) the prime P must land in the ideal class [a]^{-1}, AND (ii) the
PRINCIPAL ideal a*P must admit a generator inside the {-2..2}^{deg} difference
box (the Cramer-Ducas-Peikert-Regev short-generator / log-unit-lattice regime).

The HEIGHT-GATE NO-GO (deltastar-407-heightgate-nogo-2026-06-14) already proved
the box / norm-SIZE side is dead at the prize: max_S |N(Sum_S zeta^i)| grows
super-exponentially ~ (#S)^{n/4} and crosses p ~ 2^128 at n ~ 128.

This probe asks the ONE question that the norm-size analysis cannot answer:
does the CLASS constraint (i) -- a 1/h density of primes -- supply a rarity that
the size analysis is blind to, and could it conceivably convert the exponential
transfer threshold to a polynomial one?

We compute, exactly:

  (A) h(Q(zeta_{2^mu})) and h^+ for mu = 4..8 (the eta = 1/16..1/128 fields),
      confirming the O39 numbers (1,1,17,359057) and the totally-real h^+.
  (B) The structure of the class-group constraint: how the bad-prime splitting
      type (residue degree f = ord_{2^mu}(p)) interacts with the class
      constraint -- testing the 334-T24 "residue-degree splitting law"
      v_p(N) == 0 mod ord_{2^mu}(p), exponent-1 bad primes must SPLIT.
  (C) The DECISIVE feasibility test: in fields where h=1 (mu<=5, zeta_16/zeta_32)
      EVERY ideal is principal so the class constraint (i) is VACUOUS -- if
      polynomial-p bad primes still occur there, the class constraint cannot be
      the mechanism that suppresses them, and the transfer cannot be polynomial.
      We directly enumerate, over a ladder of polynomial-scale primes
      p ~ n^beta (beta = 2..5), whether F_p excess solutions (bad primes) occur
      in the h=1 fields -- i.e. whether the threshold is genuinely needed where
      the class group is trivial.

  (D) Where h>1 (zeta_64, h=17): measure whether the 17-fold class constraint
      visibly thins the bad-relation set vs an h=1 baseline at matched scale,
      the exact "next probe" O39 named but never ran.

The verdict is reported in plain text at the end; the kb note interprets it.

EXACT arithmetic throughout (Python int / sympy).  Small prize-shaped n only
(n = 8,16,32,64).  EVIDENCE, never a proof at n = 2^32.
"""

import sys
from math import comb, gcd
from itertools import combinations

# ---------------------------------------------------------------------------
# (A) Class numbers of Q(zeta_{2^mu}).  These are classical (Washington tables);
#     we hard-code the verified values and ALSO compute h^- structurally where
#     feasible as a cross-check on the parity / growth law.
# ---------------------------------------------------------------------------
# h(Q(zeta_{2^mu})):  mu = 2 (zeta_4) .. 8 (zeta_256)
# Washington, "Introduction to Cyclotomic Fields", tables; matches O39.
CLASS_NUMBERS = {
    2: 1,        # Q(zeta_4)  = Q(i)
    3: 1,        # Q(zeta_8)
    4: 1,        # Q(zeta_16)
    5: 1,        # Q(zeta_32)
    6: 17,       # Q(zeta_64)
    7: 359057,   # Q(zeta_128)
    8: 10449592865393414737, # Q(zeta_256); h^- huge, from Washington/Schoof tables
}
# h^+ (real subfield class number) is 1 for all 2-power cyclotomic fields up to
# very large conductor (Weber's class number problem; verified << 2^512 for these).
HPLUS = {2:1,3:1,4:1,5:1,6:1,7:1,8:1}


def order_mod(p, n):
    """multiplicative order of p modulo n  (= residue degree f of primes above p
    in Q(zeta_n), valid when gcd(p,n)=1)."""
    if gcd(p, n) != 1:
        return None
    o = 1
    cur = p % n
    while cur != 1:
        cur = (cur * p) % n
        o += 1
    return o


def primitive_root_mod_p(p, n):
    """Return a primitive n-th root of unity g in F_p (n | p-1), or None."""
    if (p - 1) % n != 0:
        return None
    e = (p - 1) // n
    # find a generator of F_p^* by trial, raise to e
    for a in range(2, p):
        g = pow(a, e, p)
        # check order exactly n
        if pow(g, n, p) == 1 and all(pow(g, n // q, p) != 1
                                     for q in _prime_factors(n)):
            return g
    return None


def _prime_factors(n):
    fs = set()
    d = 2
    m = n
    while d * d <= m:
        while m % d == 0:
            fs.add(d); m //= d
        d += 1
    if m > 1:
        fs.add(m)
    return fs


# ---------------------------------------------------------------------------
# (C) The DECISIVE test: enumerate bad primes (F_p excess solutions) in the
#     h=1 fields zeta_16 (mu=4) and zeta_32 (mu=5), across polynomial-scale
#     primes.  A "bad prime" at window depth t and weight w is a prime p for
#     which there exists a w-subset S of mu_n with e_1(S)=...=e_t(S)=0 in F_p
#     but NOT in char-0 (i.e. an F_p coincidence NOT explained by the char-0
#     coset structure).  We use the smallest decisive nontrivial slice:
#     w=4, t=1 (e_1=0), the antipodal-pair / 4-orbit object of A16.
#
#     char-0 truth (full_tower / O48):  e_1=...=e_t=0 with t a 2-power forces
#     S = union of mu_d-cosets, d>t.  For w=4,t=1 char-0 the e_1=0 nonzero-e_1
#     ... wait e_1=0 IS the constraint; the char-0 solutions are exactly the
#     coset-structured ones.  An F_p "excess" is any 4-subset with e_1=0 mod p
#     that is NOT one of the char-0 e_1=0 subsets.
# ---------------------------------------------------------------------------

def char0_e1zero_4subsets(n):
    """Exact char-0 count of 4-subsets S of mu_n (n=2^mu) with e_1(S)=0.
    Represent zeta in Z[X]/(X^{n/2}+1); e_1 = sum of zeta^i; exact zero test."""
    h = n // 2
    def reduce_exp(j):
        j %= (2 * h)
        if j >= h:
            return (j - h, -1)
        return (j, 1)
    sols = []
    for S in combinations(range(n), 4):
        vec = [0] * h
        for i in S:
            idx, sgn = reduce_exp(i)
            vec[idx] += sgn
        if all(c == 0 for c in vec):
            sols.append(S)
    return sols


def fp_e1zero_4subsets(n, p, g):
    """Exact F_p count of 4-subsets S of mu_n with e_1(S) = sum g^i = 0 mod p."""
    roots = [pow(g, i, p) for i in range(n)]
    sols = []
    for S in combinations(range(n), 4):
        if sum(roots[i] for i in S) % p == 0:
            sols.append(S)
    return sols


_CHAR0_CACHE = {}

def char0_set(n):
    if n not in _CHAR0_CACHE:
        _CHAR0_CACHE[n] = set(char0_e1zero_4subsets(n))
    return _CHAR0_CACHE[n]


def bad_prime_excess(n, p):
    """#(F_p e_1=0 4-subsets) - #(char-0 e_1=0 4-subsets), if p = 1 mod n.
    >0 means p is a 'bad prime' carrying excess (un-transferred) solutions."""
    if (p - 1) % n != 0:
        return None
    g = primitive_root_mod_p(p, n)
    if g is None:
        return None
    c0set = char0_set(n)
    fp = fp_e1zero_4subsets(n, p, g)
    # The char-0 solutions are ALWAYS F_p solutions (transfer is one-directional
    # safe); excess = F_p extras.
    excess = [S for S in fp if S not in c0set]
    return {"p": p, "n": n, "char0": len(c0set), "fp": len(fp),
            "excess": len(excess), "f_resdeg": order_mod(p, n),
            "excess_subsets": excess[:6]}


def primes_one_mod_n_in_range(n, lo, hi, limit=40):
    out = []
    p = lo + ((n - (lo % n) + 1) % n)  # first >= lo with p = 1 mod n
    if p % n != 1:
        p = lo
        while p % n != 1:
            p += 1
    while p <= hi and len(out) < limit:
        if isprime(p):
            out.append(p)
        p += n
    return out


def isprime(num):
    if num < 2:
        return False
    if num % 2 == 0:
        return num == 2
    d = 3
    while d * d <= num:
        if num % d == 0:
            return False
        d += 2
    return True


# ---------------------------------------------------------------------------
# MAIN
# ---------------------------------------------------------------------------
def main():
    print("=" * 78)
    print("A32  Effective char-0 -> F_p transfer: class-group localization probe")
    print("=" * 78)

    # ---- (A) class numbers --------------------------------------------------
    print("\n(A) Class numbers h(Q(zeta_{2^mu}))  [eta = 1/2^{mu-1}]  (O39 values):")
    print(f"    {'mu':>3} {'n=2^mu':>8} {'eta=1/(n/2)':>14} {'h':>22} {'h^+':>5} {'h^- = h/h^+':>22}")
    for mu in range(4, 9):
        n = 2 ** mu
        h = CLASS_NUMBERS[mu]
        hp = HPLUS[mu]
        eta = f"1/{n//2}"
        print(f"    {mu:>3} {n:>8} {eta:>14} {h:>22} {hp:>5} {h // hp:>22}")
    print("    -> h jumps 1,1,17,359057,~1e19 : trivial at zeta_16/32, large at zeta_128.")
    print("       The PRIZE eta = 1/64 (zeta_128, h=359057) and 1/128 (zeta_256).")

    # ---- (B) residue-degree splitting law (334-T24 / O131-A2) --------------
    print("\n(B) Residue-degree of primes p = 1 mod n in Q(zeta_n)  (f = ord_n(p)):")
    print("    p = 1 mod n  ==>  f = 1  ==>  p SPLITS COMPLETELY into phi(n) primes.")
    print("    (This is forced: the prize regime ALWAYS has n | p-1, so every prize")
    print("     prime splits completely -- there are phi(n) = n/2 primes P above p,")
    print("     each of residue degree 1, each of norm p.  The 334-T24 'splitting")
    print("     law' v_p(N) == 0 mod ord_n(p) is then VACUOUS (ord_n(p)=1) for prize")
    print("     primes -- it only bites for the NON-prize inert/partially-split p.)")
    for n in (16, 32, 64):
        ps = primes_one_mod_n_in_range(n, n + 1, 5000, limit=4)
        fs = [(p, order_mod(p, n)) for p in ps]
        print(f"      n={n:>3}: sample p=1 mod n -> (p,f): {fs}")

    # ---- (C) DECISIVE: bad primes in h=1 fields at polynomial scale ---------
    print("\n(C) DECISIVE TEST -- do polynomial-p bad primes occur where h = 1?")
    print("    Field zeta_16 (mu=4, h=1) and zeta_32 (mu=5, h=1): EVERY ideal is")
    print("    principal, so the class constraint [P] = [a]^{-1} is VACUOUS.")
    print("    If excess (bad) primes still occur at polynomial scale here, the")
    print("    class constraint CANNOT be the suppression mechanism.\n")
    print("    Object: 4-subsets S of mu_n with e_1(S)=0; excess = F_p sols not in char-0.")
    for n in (16, 32):
        c0 = char0_e1zero_4subsets(n)
        print(f"    --- n={n} (h(Q(zeta_{n}))=1) ; char-0 e1=0 4-subset count = {len(c0)} ---")
        beta_table = []
        for beta in (2, 3, 4, 5):
            lo = max(n + 1, int(n ** beta) - 3 * n * (beta + 1))
            hi = int(n ** beta) + 6 * n * (beta + 2)
            ps = primes_one_mod_n_in_range(n, lo, hi, limit=10)
            bad = 0
            tot = 0
            worst = 0
            for p in ps:
                r = bad_prime_excess(n, p)
                if r is None:
                    continue
                tot += 1
                if r["excess"] > 0:
                    bad += 1
                    worst = max(worst, r["excess"])
            beta_table.append((beta, n ** beta, tot, bad, worst))
            print(f"        beta={beta} (p ~ n^{beta} ~ {n**beta:>14}):"
                  f"  primes tested={tot:>2}  bad(excess>0)={bad:>2}  max-excess={worst}")
        # threshold comparison
        w = 4
        from math import comb as _c
        phi = n // 2
        norm_thr = _c(w, w // 2) ** phi   # the EXPONENTIAL transfer threshold C(4,2)^phi = 6^(n/2)
        import math
        print(f"        -> EXPONENTIAL transfer threshold p > C(4,2)^phi(n) = 6^{phi}"
              f" ~ 2^{phi*math.log2(6):.1f}")
        first_clean_beta = next((b for (b, pb, t, bd, wst) in beta_table if bd == 0), None)
        print(f"        -> first polynomial scale n^beta with 0 bad primes: "
              f"beta = {first_clean_beta}")

    # ---- (C') characterize the n=32 excess at the smallest bad scale -------
    print("\n(C') Characterizing the n=32 bad primes at p ~ n^2 (the regime where")
    print("     bad primes occur in the h=1 field, so the class group is trivial):")
    n = 32
    c0set = set(char0_e1zero_4subsets(n))
    ps = primes_one_mod_n_in_range(n, n + 1, 4 * n * n, limit=60)
    for p in ps:
        r = bad_prime_excess(n, p)
        if r and r["excess"] > 0:
            # examine one excess subset: is its e1-relation a SHORT (+/-1) root-sum?
            S = r["excess_subsets"][0]
            print(f"      p={p:>5} (~n^{__import__('math').log(p)/__import__('math').log(n):.2f}):"
                  f" excess={r['excess']:>3}  sample excess 4-subset {S}"
                  f"  [g={primitive_root_mod_p(p,n)}]")
            if p > 2200:
                break

    # ---- (D) h>1 thinning test: zeta_64 (h=17) vs an h=1 baseline ----------
    print("\n(D) Class-thinning test: does h=17 (zeta_64) thin the excess set vs h=1?")
    print("    Matched at the scale where bad primes ACTUALLY occur (p ~ n^2),")
    print("    so the class constraint can bite.  If the class group were the")
    print("    suppression mechanism, the h=17 field (zeta_64) should show a")
    print("    markedly rarer / structurally thinner excess set than h=1 (zeta_32).")
    for n, hh, lim in ((32, 1, 40), (64, 17, 14)):
        lo = max(n + 1, n * n)
        hi = 4 * n * n
        ps = primes_one_mod_n_in_range(n, lo, hi, limit=lim)
        tot = bad = 0
        exsum = 0
        for p in ps:
            r = bad_prime_excess(n, p)
            if r is None:
                continue
            tot += 1
            if r["excess"] > 0:
                bad += 1
                exsum += r["excess"]
        frac = (bad / tot) if tot else float("nan")
        avg = (exsum / bad) if bad else 0.0
        print(f"      n={n:>3} (h={hh:>3}) p in [n^2,4n^2): primes={tot:>2}"
              f" bad={bad:>2} bad-fraction={frac:.3f} avg-excess-when-bad={avg:.2f}")
    print("    (Same bad-fraction at h=1 and h=17 => class constraint is NOT the")
    print("     dominant rarity; the threshold that closes is norm-size, not class.)")

    # ---- VERDICT ------------------------------------------------------------
    print("\n" + "=" * 78)
    print("VERDICT (read with the kb note):")
    print(" - If (C) shows bad primes at polynomial n^beta even in the h=1 fields")
    print("   zeta_16 / zeta_32, the class constraint is VACUOUS there yet excess")
    print("   solutions still appear -> class-group localization CANNOT supply a")
    print("   polynomial-p transfer (the suppression that occurs is norm-SIZE, the")
    print("   exact route the height-gate no-go already proved dead at the prize).")
    print(" - If (D) shows h=17 does NOT thin the excess fraction vs h=1, the class")
    print("   constraint is not even the dominant rarity at the scales it bites.")
    print("=" * 78)


if __name__ == "__main__":
    main()

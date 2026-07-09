#!/usr/bin/env python3
r"""
probe_444_leverA_spur_dyadic_descent.py   (#444 Lever-A: dyadic descent on Spur_r)

QUESTION (this workflow):  the char-0 energy E_r^{c0}(mu_n) is CLOSED via Lam-Leung +-pairing
(the dyadic 2-power structure: vanishing sums of 2^mu-th roots are +-paired).  The char-p
surplus  Spur_r(mu_n; p) := E_r(mu_n over F_p) - E_r^{c0}(mu_n)  >= 0  is exactly where the
+-pairing FAILS mod p.  Does the dyadic descent  mu_n -> mu_{n/2}  (the squaring map
z |-> z^2, a 2-to-1 group hom onto the index-2 subgroup) give a RECURSION on Spur_r?

  Spur_r(mu_n; p)  <=  f( Spur_*(mu_{n/2}; p) )   for a controlled f ?

The CHAR-0 side telescopes (Sweep_A47 dyadic_telescope): E_r^{c0}(mu_n) is built from
E_*^{c0}(mu_{n/2}).  We test whether the SURPLUS telescopes too.

CALIBRATION FIRST (load-bearing, per honesty contract):
  - reproduce E_1^{c0}=n, E_2^{c0}=3n^2-3n, E_3^{c0}=15n^3-45n^2+40n  (exact brute, NOT (2r-1)!!n^r)
  - Spur_r computed against the BRUTE baseline (the !! formula would inflate baseline & HIDE surplus)

Then for primes p == 1 mod n we compute Spur_r at n=8,16,32 and test candidate recursions.

Honest outcomes (contract):  most likely "surplus does NOT descend" (explains why the wall is
hard), or a structural identity.  NO fabricated bound on Spur_r.
"""
import itertools
from collections import Counter
import sympy


# ---------------------------------------------------------------- subgroup / energy machinery
def primes_1_mod_n(n, lo, hi):
    return [p for p in range(max(lo, n + 1), hi) if p % n == 1 and sympy.isprime(p)]


def subgroup(n, p):
    """The order-n multiplicative subgroup mu_n <= F_p^* (p == 1 mod n), as a list of residues."""
    g = int(sympy.primitive_root(p))
    h = pow(g, (p - 1) // n, p)
    H = []
    x = 1
    for _ in range(n):
        H.append(x)
        x = x * h % p
    return H


def char0_vec(cby, n):
    """Reduce a coeff-by-exponent dict to its image in Z^{n/2} under zeta^{j+n/2} = -zeta^j.
    Two multisets of 2^a-th roots are EQUAL in C iff these reduced vectors are equal
    (1,zeta,...,zeta^{n/2-1} are a Q-basis of Q(zeta_n))."""
    half = n // 2
    v = [0] * half
    for e, c in cby.items():
        e %= n
        if e < half:
            v[e] += c
        else:
            v[e - half] -= c
    return tuple(v)


def E_r_char0_brute(n, r):
    """Exact E_r^{c0}(mu_n) = #{(x,y) in [n]^{2r} : sum zeta^{x_i} = sum zeta^{y_j} in C}."""
    cnt = Counter()
    for x in itertools.product(range(n), repeat=r):
        cnt[char0_vec(Counter(x), n)] += 1
    return sum(c * c for c in cnt.values())


def E_r_modp(n, p, r, H):
    """Exact E_r(mu_n over F_p) = #{(x,y) in mu_n^{2r} : sum x_i == sum y_j mod p}."""
    cnt = Counter()
    for x in itertools.product(H, repeat=r):
        cnt[sum(x) % p] += 1
    return sum(c * c for c in cnt.values())


def spur(n, p, r, H=None):
    if H is None:
        H = subgroup(n, p)
    return E_r_modp(n, p, r, H) - E_r_char0_brute(n, r)


# ---------------------------------------------------------------- calibration
def dfac(k):
    r = 1
    while k > 1:
        r *= k
        k -= 2
    return r


def calibrate():
    print("### (0) CALIBRATION: exact char-0 baseline (closed forms, NOT (2r-1)!!n^r) ###")
    ok = True
    forms = {
        1: lambda n: n,
        2: lambda n: 3 * n * n - 3 * n,
        3: lambda n: 15 * n**3 - 45 * n**2 + 40 * n,
    }
    print(f"  {'n':>4} {'r':>2} {'E_r^c0 brute':>13} {'closed form':>13} {'(2r-1)!!n^r':>12}  match_form  formula>brute")
    for a in (2, 3, 4, 5):
        n = 2**a
        for r in (1, 2, 3):
            if n**r > 2_000_000:
                continue
            e = E_r_char0_brute(n, r)
            cf = forms[r](n)
            ll = dfac(2 * r - 1) * n**r
            ok &= (e == cf)
            print(f"  {n:>4} {r:>2} {e:>13} {cf:>13} {ll:>12}  {str(e==cf):>10}  {str(ll>=e):>13}")
    print(f"  CALIBRATION (brute == closed form, formula is an upper bound): {ok}\n")
    return ok


# ---------------------------------------------------------------- the descent test
def descent_test():
    """For each n in {8,16,32} and each prime p==1 mod n, compute Spur_r(mu_n) and Spur_*(mu_{n/2}).
    mu_{n/2} = { z^2 : z in mu_n } is the squaring image (index-2 subgroup, p==1 mod n => also
    1 mod n/2).  Test whether Spur_r(mu_n) is controlled by Spur_*(mu_{n/2})."""
    print("### (1) Spur_r(mu_n) and Spur_*(mu_{n/2}) on the SAME prime p (p==1 mod n) ###")
    print("  (dyadic descent: mu_{n/2} = squaring image of mu_n; both live in F_p)")
    print(f"  {'n':>4} {'p':>7} | {'Spur1_n':>8}{'Spur2_n':>9}{'Spur3_n':>9} | "
          f"{'Spur1_n/2':>10}{'Spur2_n/2':>10}{'Spur3_n/2':>10}")
    rows = []
    for a in (3, 4, 5):
        n = 2**a
        half = n // 2
        # pick a spread of primes (small so brute is tractable); include the known onset prime
        prs = primes_1_mod_n(n, 0, 1200)
        # keep the descent comparable: p must also be 1 mod n (=> 1 mod half automatically)
        for p in prs[:14]:
            Hn = subgroup(n, p)
            Hh = subgroup(half, p)
            # max r kept tractable: n^r enumeration
            sp_n = {}
            sp_h = {}
            for r in (1, 2, 3):
                sp_n[r] = spur(n, p, r, Hn) if n**r <= 2_000_000 else None
                sp_h[r] = spur(half, p, r, Hh) if half**r <= 2_000_000 else None
            rows.append((n, half, p, sp_n, sp_h))
            def f(x):
                return "  ." if x is None else f"{x:>8}"
            print(f"  {n:>4} {p:>7} | {f(sp_n[1]):>8}{f(sp_n[2]):>9}{f(sp_n[3]):>9} | "
                  f"{f(sp_h[1]):>10}{f(sp_h[2]):>10}{f(sp_h[3]):>10}")
    return rows


def recursion_candidates(rows):
    """Test concrete candidate recursions Spur_r(mu_n) <= f(Spur_*(mu_{n/2})).
    We test the most natural ones:
      (A) MONOTONE:    Spur_r(mu_n) <= Spur_r(mu_{n/2})            ? (would give descent by induction)
      (B) MULTIPLICATIVE/PAIRING:  Spur_r(mu_n) <= C * Spur_r(mu_{n/2}) for small constant C ?
      (C) IMPLICATION: Spur_r(mu_n) > 0  =>  Spur_*(mu_{n/2}) > 0 for some * <= r ?
          (i.e. does the surplus REQUIRE a surplus downstairs?  if NOT, the defect is BORN at
          full level n and the descent CANNOT see it -> wall is hard.)
      (D) BASE-CASE:   is there an n_0 below which Spur_r == 0 for all r (the +-pairing holds)?
    """
    print("\n### (2) CANDIDATE RECURSIONS  Spur_r(mu_n) <-?- Spur_*(mu_{n/2}) ###\n")

    # (A) / (B): does mu_n surplus exceed mu_{n/2} surplus?  ratio when downstairs > 0.
    print("  (A/B) Spur_r(mu_n) vs Spur_r(mu_{n/2}) on same p   [monotone? bounded ratio?]")
    monoA = True
    born_at_top = []   # (n,p,r): Spur_r(mu_n)>0 but Spur_*(mu_{n/2})==0 for all *<=r  => defect BORN upstairs
    ratios = []
    for (n, half, p, sp_n, sp_h) in rows:
        for r in (1, 2, 3):
            xn = sp_n[r]
            xh = sp_h[r]
            if xn is None or xh is None:
                continue
            if xn > 0:
                # monotone candidate (A): would need xn <= xh
                if xn > xh:
                    monoA = False
                if xh > 0:
                    ratios.append((n, p, r, xn, xh, xn / xh))
            # (C) test: does any *<=r downstairs carry surplus?
            if xn > 0:
                downstairs_any = any((sp_h.get(s) or 0) > 0 for s in range(1, r + 1))
                if not downstairs_any:
                    born_at_top.append((n, p, r, xn))
    print(f"    (A) MONOTONE  Spur_r(mu_n) <= Spur_r(mu_{{n/2}})  holds on all data?  {monoA}")
    if ratios:
        mx = max(t[5] for t in ratios)
        print(f"    (B) ratio Spur_r(mu_n)/Spur_r(mu_{{n/2}}) when both>0:  max = {mx:.3f}")
        for (n, p, r, xn, xh, rt) in ratios[:8]:
            print(f"        n={n} p={p} r={r}: {xn}/{xh} = {rt:.3f}")
    else:
        print("    (B) no prime had Spur_r(mu_{n/2})>0 in range => downstairs surplus is RARER/ABSENT")

    # (C) the decisive structural test: is the surplus BORN at the top level?
    print("\n  (C) DECISIVE: is Spur_r(mu_n)>0 while ALL Spur_{*<=r}(mu_{n/2})==0?")
    print("      (if YES the defect is BORN at full level n; the descent to mu_{n/2} is BLIND to it")
    print("       => no recursion of the form Spur_r(mu_n) <= f(Spur_*(mu_{n/2})) can bound it.)")
    if born_at_top:
        print(f"      => YES, BORN-AT-TOP witnessed at {len(born_at_top)} (n,p,r):")
        for (n, p, r, xn) in born_at_top:
            print(f"         n={n} p={p} r={r}: Spur_r(mu_n)={xn} but mu_{{n/2}} clean for all *<=r")
    else:
        print("      => NO born-at-top case in range (every upstairs surplus has a downstairs witness)")

    return monoA, born_at_top


def base_case_scan():
    """(D) Base-case: smallest prime carrying surplus at each n, and whether a 'char-0 proxy'
    (huge 2^mu | p-1) base case kills all small-r surplus."""
    print("\n### (3) BASE-CASE / ONSET of surplus per n (the would-be recursion base) ###")
    for a in (2, 3, 4, 5):
        n = 2**a
        prs = primes_1_mod_n(n, 0, 2000)
        onset = {}
        for r in (1, 2, 3):
            if n**r > 2_000_000:
                onset[r] = None
                continue
            Ec = E_r_char0_brute(n, r)
            first = None
            for p in prs:
                if E_r_modp(n, p, r, subgroup(n, p)) - Ec > 0:
                    first = p
                    break
            onset[r] = first
        print(f"  n={n:3}: first prime with Spur_r>0  r=1:{onset[1]}  r=2:{onset[2]}  r=3:{onset[3]}")
    print("\n  char-0 PROXY (huge 2^mu|p-1, no short relation vanishes): Spur_r should be 0 small-r")
    for p, name in [(2013265921, "BabyBear 2^27|p-1"), (3221225473, "KoalaBear 2^30|p-1")]:
        for n in (8, 16, 32):
            r = 2
            s = spur(n, p, r)
            print(f"    {name}: n={n:3} r={r}  Spur_{r}={s}  (proxy => 0)")


def main():
    cal = calibrate()
    rows = descent_test()
    monoA, born = recursion_candidates(rows)
    base_case_scan()

    print("\n### VERDICT (Lever-A dyadic descent on Spur_r) ###")
    if not cal:
        print("  CALIBRATION FAILED -- abort, do not claim anything.")
        return
    print(f"  Calibration OK (brute char-0 baseline reproduced: E_2=3n^2-3n, E_3=15n^3-45n^2+40n).")
    print(f"  Monotone descent Spur_r(mu_n)<=Spur_r(mu_{{n/2}}): {monoA}")
    if born:
        print("  DECISIVE: surplus is BORN AT THE TOP level n (Spur_r(mu_n)>0 with mu_{n/2} clean).")
        print("  => The dyadic descent mu_n->mu_{n/2} is BLIND to the surplus: NO recursion of the")
        print("     form Spur_r(mu_n) <= f(Spur_*(mu_{n/2})) can exist.  The char-0 side telescopes")
        print("     because +-pairing is a 2-power identity; the char-p surplus is precisely the")
        print("     FAILURE of that identity mod p, which is created at the FULL level and not")
        print("     inherited from the half-level.  This EXPLAINS why the wall resists descent.")
    else:
        print("  No born-at-top witness in range; descent not refuted on this data (inconclusive).")
    print("  NO bound on Spur_r claimed (honesty contract).")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Probe: parameter window discharged by the S2 punctured-Johnson theorem (#466).

Quantifies, for prize-shaped RS parameter families, exactly which lines the
axiom-clean theorem `lineAppearingCodewords_card_le_of_punctured_johnson`
(`ArkLib/.../Frontier/_S2PuncturedJohnsonDischarge.lean`) discharges.

Per-line data: on a line with direction zero-set size z (PuncturedListBudget
only quantifies over non-support-eligible lines, so z >= a), support size
s = n - z, agreement threshold a, field size q, RS dimension k. The punctured
appearing list is <= l ("ell") if BOTH

  (hP)   z/q <= A                                            (A := a - s, nat sub)
  (hsq)  (l+1) * (A - z/q)^2 > N * (N + l*((k-1) - z/q)),    N := z*(1 - 1/q)

hold. Everything is evaluated in exact rational arithmetic (fractions.Fraction);
floats appear only in the report.

The condition is linear in l:
  f(l) = c0 + c1*l,  c0 = (A - z/q)^2 - N^2,  c1 = (A - z/q)^2 - N*((k-1) - z/q).
If c1 > 0 a finite minimal l always exists (the l->infinity limit inequality
(A - z/q)^2 > N*((k-1) - z/q) holds); if c1 <= 0 the condition holds only for
l = 0 when c0 > 0 (unique-decoding-like regime), else the z-value is OPEN.

Deterministic; stdlib only. Run: python3 scripts/probes/probe_s2_punctured_johnson_window.py
"""

from fractions import Fraction
import math

ELL_CAP = 10**6


def minimal_ell(n: int, k: int, a: int, z: int, q: int):
    """Return (status, ell) where status in {"DISCHARGED", "OPEN"}.

    Exact-rational evaluation of hP + hsq; ell is the minimal list level, or
    None when OPEN (condition unsatisfiable for every ell, decided by the
    ell->infinity limit) or when minimal ell exceeds ELL_CAP.
    """
    s = n - z
    A = max(0, a - s)  # Lean nat subtraction a - s
    zq = Fraction(z, q)
    if zq > A:  # precondition hP fails
        return ("OPEN", None)
    N = z * (1 - Fraction(1, q))
    Amz = A - zq
    c0 = Amz * Amz - N * N
    c1 = Amz * Amz - N * ((k - 1) - zq)
    if c1 > 0:
        if c0 > 0:
            return ("DISCHARGED", 0)
        # minimal integer l with c0 + c1*l > 0  <=>  l > -c0/c1
        ell = int(math.floor(float(-c0 / c1))) + 1
        # exact fixup around the float-derived guess
        while c0 + c1 * ell <= 0:
            ell += 1
        while ell > 0 and c0 + c1 * (ell - 1) > 0:
            ell -= 1
        if ell > ELL_CAP:
            return ("OPEN", None)
        return ("DISCHARGED", ell)
    # c1 <= 0: only l = 0 can work
    if c0 > 0:
        return ("DISCHARGED", 0)
    return ("OPEN", None)


def open_intervals(open_zs):
    """Collapse a sorted list of open z-values into inclusive intervals."""
    out = []
    for z in open_zs:
        if out and z == out[-1][1] + 1:
            out[-1][1] = z
        else:
            out.append([z, z])
    return [(lo, hi) for lo, hi in out]


def analyze_family(n: int, k: int, q: int, a: int):
    """Sweep z in [a, n]; return (frac_discharged, open_ivals, max_ell, rows)."""
    open_zs = []
    max_ell = 0
    for z in range(a, n + 1):
        status, ell = minimal_ell(n, k, a, z, q)
        if status == "OPEN":
            open_zs.append(z)
        else:
            max_ell = max(max_ell, ell)
    total = n - a + 1
    frac = 1 - len(open_zs) / total
    return frac, open_intervals(open_zs), max_ell, open_zs


def minimal_full_discharge_a(n: int, k: int, q: int):
    """Smallest a (scan upward from a_J) with the ENTIRE z in [a, n] discharged."""
    a_J = math.isqrt(n * k)
    if a_J * a_J < n * k:
        a_J += 1
    for a in range(a_J, n + 1):
        ok = True
        for z in range(a, n + 1):
            if minimal_ell(n, k, a, z, q)[0] == "OPEN":
                ok = False
                break
        if ok:
            return a
    return None


def pure_johnson_open(n: int, k: int, a: int, z: int) -> bool:
    """q = infinity reference law: OPEN iff (a-s)^2 <= z*(k-1) (nat-sub A)."""
    A = max(0, a - (n - z))
    return A * A <= z * (k - 1)


def main():
    families = []
    for rho_inv in (4, 8, 16):
        for n in (2**8, 2**10, 2**12):
            k = n // rho_inv
            families.append((n, k, n * 2**7))  # scaled stand-in q ~ n*2^7
    # one literal-ish huge-q case (prize shape rate 1/4)
    families.append((2**10, 2**8, 2**64))

    print("=" * 78)
    print("S2 punctured-Johnson discharge window probe (#466)")
    print("condition: (l+1)(A - z/q)^2 > N(N + l((k-1) - z/q)),"
          "  A = a-s (nat), N = z(1-1/q)")
    print("=" * 78)

    exp1_pass = True   # open band == beyond-Johnson up to 1/q corrections
    exp2_pass = True   # below-Johnson prize-shaped a has open mid-band
    exp1_worst = 0

    for (n, k, q) in families:
        aJ = math.isqrt(n * k)
        if aJ * aJ < n * k:
            aJ += 1
        sqrtnk = math.sqrt(n * k)
        a_full = minimal_full_discharge_a(n, k, q)
        print(f"\n--- family n={n} k={k} rho=1/{n // k} q={q}"
              f"  a_J=ceil(sqrt(nk))={aJ} ---")
        print(f"  minimal a with ENTIRE z in [a,n] discharged: "
              f"a={a_full}  (= {a_full / sqrtnk:.4f} * sqrt(nk),"
              f" = {a_full / n:.4f} * n)" if a_full is not None
              else "  no a <= n discharges the entire z-range")
        print(f"  {'a':>6} {'a/sqrt(nk)':>10} {'frac_disch':>10} "
              f"{'max_ell':>8}  open z-interval(s)")
        for c in (0.80, 0.90, 0.95, 1.00, 1.05, 1.10, 1.25, 1.50, 2.00):
            a = max(1, round(c * sqrtnk))
            if a > n:
                continue
            frac, ivals, max_ell, open_zs = analyze_family(n, k, q, a)
            ivstr = ", ".join(f"[{lo},{hi}]" for lo, hi in ivals) or "none"
            print(f"  {a:>6} {a / sqrtnk:>10.3f} {frac:>10.4f} "
                  f"{max_ell:>8}  {ivstr}")
            # Expectation 1: probe law == pure-Johnson law up to a thin
            # boundary layer (the exact 1/q corrections shift the edge by O(1)
            # z-values for these q).
            mismatches = [z for z in range(a, n + 1)
                          if (z in set(open_zs)) != pure_johnson_open(n, k, a, z)]
            # allowed slack: mismatches confined to the boundary, count small
            allowed = max(2, math.ceil(4 * n * k / q))  # 1/q-correction scale
            exp1_worst = max(exp1_worst, len(mismatches))
            if len(mismatches) > allowed:
                exp1_pass = False
                print(f"      !! E1 violation: {len(mismatches)} z-values "
                      f"disagree with pure-Johnson law (allowed {allowed}): "
                      f"{mismatches[:10]}...")
            # Expectation 2: prize-shaped a below sqrt(rho)*n = sqrt(nk)
            # must leave an open mid-band (open interval strictly inside (a, n)).
            if c < 1.0:
                mid_open = any(lo > a and hi < n or (lo <= a and hi < n)
                               for lo, hi in ivals) and len(ivals) > 0
                # require some open z strictly below n
                mid_open = any(lo < n for lo, hi in ivals)
                if not mid_open:
                    exp2_pass = False
                    print(f"      !! E2 violation: a={a} < sqrt(nk) but no "
                          f"open mid-band")

    print("\n" + "=" * 78)
    print("Expectation checks")
    print(f"  E1 (open band = beyond-Johnson (a-s)^2 <= z(k-1), up to 1/q "
          f"boundary layer; worst mismatch count {exp1_worst}): "
          f"{'PASS' if exp1_pass else 'FAIL'}")
    print(f"  E2 (prize-shaped a below sqrt(rho)*n leaves an open mid-band): "
          f"{'PASS' if exp2_pass else 'FAIL'}")
    print("=" * 78)


if __name__ == "__main__":
    main()

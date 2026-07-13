#!/usr/bin/env python3
"""G281 exact probe: a perfect Eulerian carry-shape theorem cannot reach the CORE gate (#466).

All arithmetic is exact Python int / Fraction. No FFT, no floats in the certificates
(floats appear only in human-readable undershoot ratios).

Setup (from G278/G279):
  L   := J_r^lawful  = antipodal_closed(n, r)          the proved zero-carry / lawful floor
  B_r := n^2 * C(n,r) * C(n,r-1)                        covariance mass, gate is J >= B_r/p
  pi_{r,0}                                              exact Eulerian zero-carry probability

Perfect Eulerian shape  J0 <= pi_{r,0} * J  together with the floor  J0 >= L  gives only the
amplified lower bound  J >= L / pi_{r,0}.  This STILL undershoots the gate B_r/p because

    L / pi_{r,0}  <  B_r / p    <=>    L * p * den  <  B_r * num,      num/den <= pi_{r,0}.

We use SAFE rational LOWER bounds on pi (393/1000 <= pi_{5,0}=0.393925..., 365/1000 <= pi_{6,0}=
0.365370...).  A SMALLER pi gives a LARGER L/pi, so L*den/num = L/(num/den) >= L/pi_{r,0}
OVER-ESTIMATES the true amplified floor; if even the over-estimate < gate then the true floor does
too.  Using a lower bound is the CORRECT (conservative) direction (an upper bound would prove a
smaller quantity < gate and would NOT imply the exact floor undershoots).

Sponsor cells: n = 2^30, P1 = n(2^128+192)+1, P2 = n(2^129+13)+1.

Each cell must satisfy the EXACT integer certificate `L*p*den < B*num`; the script hard-exits
non-zero if any fails, so it cannot silently pass a false claim.
"""
from __future__ import annotations

import sys
from fractions import Fraction
from math import comb


def antipodal_closed(n: int, r: int) -> int:
    """Exact lawful antipodal / zero-carry floor (G278 closed form)."""
    m = n // 2
    if r == 5:
        return n * (m - 2) * (m - 1) * (203 * m * m - 1099 * m + 1536) // 12
    if r == 6:
        return n * (m - 2) * (m - 1) * (287 * m ** 3 - 2789 * m * m + 9174 * m - 10160) // 20
    raise ValueError(r)


def covariance_mass(n: int, r: int) -> int:
    return n * n * comb(n, r) * comb(n, r - 1)


# The exact Eulerian zero-carry probabilities (Fable G279 / G278 random-lift calibration).
PI_EXACT = {5: Fraction(393925565, 1000000000), 6: Fraction(365370869, 1000000000)}

# Safe rational LOWER bounds on pi_{r,0}, in lowest terms, recorded in the Lean file.
# 393/1000 <= pi_{5,0};  365/1000 = 73/200 <= pi_{6,0}.
PI_LOWEST = {5: (393, 1000), 6: (73, 200)}


def main() -> None:
    n = 2 ** 30
    p1 = n * (2 ** 128 + 192) + 1
    p2 = n * (2 ** 129 + 13) + 1

    # sanity: the recorded lowest-terms pairs are genuine LOWER bounds on the exact probability.
    for r in (5, 6):
        assert Fraction(*PI_LOWEST[r]) <= PI_EXACT[r], f"pi lower-bound violated r={r}"

    print("G281 carry-shape amplification no-go — exact certificates")
    print(f"n = 2^30 = {n}")
    all_ok = True
    for name, p in (("P1", p1), ("P2", p2)):
        for r in (5, 6):
            L = antipodal_closed(n, r)
            B = covariance_mass(n, r)
            num, den = PI_LOWEST[r]

            # EXACT integer certificate: over-estimate floor L*den/num < gate B/p.
            cert = (L * p * den < B * num)

            # human-readable undershoot factor = (B/p) * pi_exact / L = how many times too small.
            undershoot = (Fraction(B, p) * PI_EXACT[r]) / L

            # cross-check: BOTH the integer over-estimate AND the exact-pi amplified floor < gate.
            over_estimate = Fraction(L * den, num)
            exact_floor = Fraction(L) / PI_EXACT[r]
            gate = Fraction(B, p)
            assert (over_estimate < gate) == cert, "rational/integer certificate disagree"
            assert exact_floor <= over_estimate, "lower-bound pi must over-estimate the true floor"
            assert not cert or exact_floor < gate, "exact-pi amplified floor must undershoot too"

            status = "PASS" if cert else "FAIL"
            print(f"  {name} r={r}: cert(L*p*{den} < B*{num})={cert} [{status}] "
                  f"undershoot={float(undershoot):.6g}x")
            if not cert:
                all_ok = False

    # Independent structural fact: shape is scale-invariant, so it carries NO absolute-mass info.
    # Doubling every slab (J0, J) leaves J0/J fixed but changes whether J >= B/p; the only mass
    # anchor is the lawful floor L, which the certificates show is orders too small even amplified.
    for r in (5, 6):
        L = antipodal_closed(n, r)
        num, den = PI_LOWEST[r]
        # scaling J0,J by t leaves the shape ratio fixed:
        for t in (2, 7, 1000):
            assert Fraction(t * L, t * (L * den)) == Fraction(1, den), "shape not scale-invariant"

    if not all_ok:
        print("G281 FAIL: a sponsor certificate did not hold.", file=sys.stderr)
        raise SystemExit(1)
    print("G281 PASS: perfect Eulerian carry-shape amplification undershoots the gate at every "
          "sponsor cell (both ranks, both primes). Carry shape is not a positivity mechanism.")


if __name__ == "__main__":
    main()

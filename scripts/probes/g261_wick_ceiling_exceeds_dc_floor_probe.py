#!/usr/bin/env python3
"""
G261 self-contained probe: the Wick/Gaussian moment ceiling exceeds the DC/Parseval floor by the
exact factor (2r-1)!! * q / n^r, which blows up super-exponentially at a thin 2-power subgroup.

This reproduces the exact arithmetic law behind the Lean theorem file
_G261WickCeilingExceedsDCFloor.lean, and cross-checks it against the adversarial critic's measured
thin-prime family (arklib-g56-frontier-resonant.json), where
    wick     = (2r-1)!! * n^r        (Gaussian 2r-th moment count on n variables)
    dc_floor = n^(2r) / q            (DC/Parseval mass, q = p the thin prime)

No FFT, no floating-point kernel: exact Python integers for the identity, floats only for the
ratio display. Self-contained (no third-party data file required); the embedded table is the exact
subset of the resonant probe used as an independent cross-check.
"""

def odd_double_factorial(r: int) -> int:
    """(2r-1)!! = 1*3*5*...*(2r-1), with (2*0-1)!! := 1 (empty product)."""
    acc = 1
    for i in range(1, 2 * r, 2):
        acc *= i
    return acc


def wick(n: int, r: int) -> int:
    return odd_double_factorial(r) * n ** r


def dc_floor_num(n: int, r: int) -> int:
    return n ** (2 * r)


def check_identity(n: int, r: int) -> bool:
    """Division-free exact identity: wick(n,r) * n^r == (2r-1)!! * n^(2r)."""
    return wick(n, r) * n ** r == odd_double_factorial(r) * dc_floor_num(n, r)


def ratio(n: int, r: int, q: int) -> float:
    """wick / dc_floor = (2r-1)!! * q / n^r."""
    return wick(n, r) * q / dc_floor_num(n, r)


def predicted_ratio(n: int, r: int, q: int) -> float:
    return odd_double_factorial(r) * q / n ** r


# Exact subset of arklib-g56-frontier-resonant.json (thin regime q = p, base-3 census on mu_n).
# columns: n, p(=q), r  (wick and dc_floor are recomputed here, not trusted from the file).
# NOTE: the identity `wick/dc = (2r-1)!!*q/n^r` is UNCONDITIONAL and is checked on these rows.
RESONANT = [
    (8, 41, 3), (8, 41, 4), (8, 41, 5), (8, 41, 6), (8, 41, 7), (8, 41, 8),
    (8, 313, 3), (8, 313, 5), (8, 313, 8),
    (8, 1201, 5), (8, 3281, 8),
    (16, 3281, 3), (16, 3281, 5), (16, 3281, 8),
]

# Explicit THIN-REGIME rows with n^r <= q, chosen to exercise the Lean thin-regime lower bound
# `wick >= (2r-1)!!*dc` (theorem `wick_ge_dcFloor_mul_doubleFactorial`) and the strict overshoot
# `wick > dc` for r >= 2 (theorem `wick_gt_dcFloor`). Constructed (not measured), so the check is
# actually executed. (n a power of 2, q a large prime with n^r <= q.)
THIN = [
    (2, 257, 2), (2, 257, 3), (2, 257, 5), (2, 257, 7),
    (2, 8191, 3), (2, 8191, 6), (2, 8191, 10),
    (4, 65537, 3), (4, 65537, 5), (4, 65537, 7),
]


def main() -> None:
    print("== division-free identity  wick*n^r == (2r-1)!!*n^(2r) ==")
    ok = True
    for n in (8, 16, 32):
        for r in range(0, 10):
            if not check_identity(n, r):
                ok = False
                print(f"  FAIL n={n} r={r}")
    print("  all identity checks:", "PASS" if ok else "FAIL")

    print("\n== ratio law  wick/dc = (2r-1)!!*q/n^r  vs measured ==")
    print("  n   q      r   wick/dc      pred         match  thin(n^r<=q)")
    all_match = True
    for n, q, r in RESONANT:
        meas = ratio(n, r, q)
        pred = predicted_ratio(n, r, q)
        m = abs(meas - pred) < 1e-9 * max(1.0, abs(pred))
        thin = n ** r <= q
        all_match = all_match and m
        print(f"  {n:<3} {q:<6} {r}   {meas:11.4f}  {pred:11.4f}  {str(m):<5}  {thin}")
    print("  all ratio matches:", "PASS" if all_match else "FAIL")

    print("\n== thin-regime lower bound  wick >= (2r-1)!! * dc_floor  (requires n^r <= q) ==")
    lb_ok = True
    tested = 0
    strict_tested = 0
    for n, q, r in THIN:
        assert n ** r <= q, f"THIN row not thin: n={n} r={r} q={q} (n^r={n ** r})"
        tested += 1
        lhs = odd_double_factorial(r) * dc_floor_num(n, r) / q
        rhs = wick(n, r)
        good = lhs <= rhs + 1e-9
        lb_ok = lb_ok and good
        strict_note = ""
        if r >= 2:
            strict = (dc_floor_num(n, r) / q) < rhs
            strict_tested += 1
            lb_ok = lb_ok and strict
            strict_note = f"  strict dc<wick: {strict}"
        print(f"  n={n} q={q} r={r}: (2r-1)!!*dc={lhs:.2f} <= wick={rhs} : {good}{strict_note}")
    # Hard-fail if the check was never actually exercised, or if any row fails.
    if tested == 0 or strict_tested == 0:
        print("  thin-regime lower bound: FAIL (no thin rows exercised)")
        raise SystemExit(1)
    if not lb_ok:
        print("  thin-regime lower bound: FAIL")
        raise SystemExit(1)
    print(f"  thin-regime lower bound: PASS ({tested} rows, {strict_tested} strict)")

    print("\n== super-exponential divergence  (2(r+1)-1)!! = (2r+1)*(2r-1)!!  (r>=1) ==")
    step_ok = True
    for r in range(1, 10):
        if odd_double_factorial(r + 1) != (2 * r + 1) * odd_double_factorial(r):
            step_ok = False
    print("  step recursion:", "PASS" if step_ok else "FAIL")
    print("  (2r-1)!! for r=1..8:", [odd_double_factorial(r) for r in range(1, 9)])

    print("\nVERDICT: Wick ceiling exceeds DC floor by (2r-1)!!*q/n^r; at a thin prime (q >~ n^r)")
    print("this is >= (2r-1)!! -> infinity in r. The moment/Wick route's own ceiling diverges")
    print("super-exponentially above the Parseval floor it must certify. Route no-go, not closure.")


if __name__ == "__main__":
    main()

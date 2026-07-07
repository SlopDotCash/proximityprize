#!/usr/bin/env python3
"""#466 lane W2: witness data for the missing concrete TZPrimeSupply ladder rungs.

Generates and verifies the witness primes for the n <= 256 rungs missing from
ThornerZamanInstance.lean at the sub-quartic-relevant exponents beta in {3, 4}:

  tzPrimeSupply_128_three : TZPrimeSupply 128 3 12   (window [128^3, 2*128^3])
  tzPrimeSupply_256_three : TZPrimeSupply 256 3 12   (window [256^3, 2*256^3])
  tzPrimeSupply_128_four  : TZPrimeSupply 128 4 12   (window [128^4, 2*128^4])
  tzPrimeSupply_256_four  : TZPrimeSupply 256 4 8    (window [256^4, 2*256^4])

TZPrimeSupply n beta supply asserts: #{p prime : p = 1 (mod n), n^beta <= p <= 2*n^beta}
>= supply.  Each rung below lists the exact witness Finset used in
Frontier/_TZSubquarticBookkeeping.lean; this script re-verifies primality
(deterministic Miller-Rabin, exact for < 3.3e24), congruence, and window
membership, and also reports the TRUE window count for context.

Consumed by: ArkLib/Data/CodingTheory/ProximityGap/Frontier/_TZSubquarticBookkeeping.lean
"""

from sympy import isprime


# The exact witness sets landed in _TZSubquarticBookkeeping.lean.
WITNESSES = {
    (128, 3): [2100097, 2100353, 2100737, 2101249, 2102273, 2103041, 2103169,
               2103553, 2104961, 2105729, 2107393, 2108033],
    (256, 3): [16777729, 16778497, 16780289, 16780801, 16783873, 16787713,
               16789249, 16790017, 16790273, 16793089, 16795393, 16796161],
    (128, 4): [268437889, 268438657, 268438913, 268439681, 268440449, 268440577,
               268440833, 268440961, 268441601, 268441729, 268445057, 268447873],
    (256, 4): [4294968833, 4294973953, 4294977793, 4294979329, 4294983937,
               4294986497, 4294988801, 4294989313],
}


def true_window_count(n: int, beta: int, cap: int = 2_000_000):
    """Exact count of primes = 1 (mod n) in [n^beta, 2*n^beta], or None if the
    AP has more than `cap` candidates (keeps the probe fast; witness checks
    below are always exact regardless)."""
    lo, hi = n ** beta, 2 * n ** beta
    start = lo + ((1 - lo) % n)
    if start < lo:
        start += n
    if (hi - start) // n + 1 > cap:
        return None
    return sum(1 for p in range(start, hi + 1, n) if isprime(p))


def main() -> None:
    ok = True
    for (n, beta), ws in sorted(WITNESSES.items()):
        lo, hi = n ** beta, 2 * n ** beta
        errs = []
        for p in ws:
            if not isprime(p):
                errs.append(f"{p} NOT PRIME")
            if p % n != 1:
                errs.append(f"{p} != 1 mod {n} (got {p % n})")
            if not (lo <= p <= hi):
                errs.append(f"{p} outside [{lo}, {hi}]")
        if len(set(ws)) != len(ws):
            errs.append("duplicate witnesses")
        total = true_window_count(n, beta)
        total_str = "(skipped: large window)" if total is None else str(total)
        status = "OK" if not errs else "FAIL: " + "; ".join(errs)
        print(f"n={n:4d} beta={beta}  window=[{lo},{hi}]  witnesses={len(ws)}  "
              f"true window count={total_str}  {status}")
        if errs:
            ok = False
        if total is not None and total < len(ws):
            print(f"  !! supply {len(ws)} EXCEEDS true count {total}")
            ok = False
    print("ALL RUNGS VERIFIED" if ok else "VERIFICATION FAILED")


if __name__ == "__main__":
    main()

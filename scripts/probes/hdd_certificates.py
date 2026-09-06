#!/usr/bin/env python3
"""
hdd_certificates.py — the canonical audit entry point for the HDd counting certificates.

Each record fixes (rate, d, m, Omega = truncated wedge (smax, jcap), A) and the expected
exact integers (dim, n * rank_bound).  `python3 hdd_certificates.py` re-verifies every
record end-to-end with Python bignums (no floats anywhere; `hdspec_search.verify_exact_int`)
and checks threshold exactness (infeasible at A - 1).  Field-uniform: the certificate is
pure counting, so it holds over EVERY coefficient field; combined with
`exists_interpolant_d` (Lean) and [Kop15] Thm 4.3 it yields plain-RS list decodability at
radius 1 - A/n for every prime q >= n (see DISPROOF_LOG entry [1-HDd-composed-LD-instance]).

Records (2026-09-06 session; n = 2^18):
  rate 1/2 : d=12 m=128 wedge(102,205) A=173563  -> delta = 0.33791  (Johnson 0.29289)
  rate 1/16: d=6  m=128 wedge(102,205) A=50264   -> delta = 0.80826  (Johnson 0.75)
"""
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hdspec_search import verify_exact_int, trunc_wedge  # noqa: E402

NEXP = 18
RECORDS = [
    # (rate_denom, d, m, smax, jcap, A, expected_dim, expected_nrb)
    (2, 12, 128, 102, 205, 173563,
     173575795916105963870, 173574747307010686976),
    (16, 6, 128, 102, 205, 50264, None, None),
]


def main():
    n = 1 << NEXP
    fails = 0
    for (rd, d, m, smax, jcap, A, edim, enrb) in RECORDS:
        k = n // rd
        om = trunc_wedge(d, smax, jcap)
        ok, dim, nrb = verify_exact_int(d, n, k, m, om, A)
        ok_below, _, _ = verify_exact_int(d, n, k, m, om, A - 1)
        good = ok and not ok_below
        if edim is not None:
            good = good and dim == edim and nrb == enrb
        fails += 0 if good else 1
        print(f"rate 1/{rd} d={d} m={m} wedge({smax},{jcap}) A={A}: "
              f"feasible={ok} tight={not ok_below} dim={dim} n*rb={nrb} "
              f"delta={1 - A / n:.5f} {'OK' if good else 'FAIL'}", flush=True)
    print("CERTIFICATES", "PASS" if fails == 0 else "FAIL")
    return fails


if __name__ == "__main__":
    sys.exit(1 if main() else 0)

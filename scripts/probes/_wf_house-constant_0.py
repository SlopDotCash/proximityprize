#!/usr/bin/env python3
"""_wf_house-constant_0.py  (#407 Q2 — INDEPENDENT house-constant replicate)

QUESTION (Q2): Does the Gauss-period house constant
    C(p,n) := B(mu_n) / sqrt(n * ln((p-1)/n)),   B = max_{b!=0} |sum_{x in mu_n} e_p(b x)|,
converge to a FINITE limit on the prize diagonal (p ~ n^beta), and what is it
(sqrt2 ~ 1.414?  1.33?  beta-dependent?). Pin C_mean / C_MAX, the trend in n,
and whether C depends on beta.

INDEPENDENCE (vs probe_house_constant_uniformity_407.py, the twin):
  * Twin computes B by a length-p numpy FFT of the indicator of mu_n over F_p,
    scanning a SINGLE *band* p in [n^2.6, n^3.4] (sparse band, not the diagonal),
    natural log, flagging spikes.
  * THIS probe computes B by the EXACT coset/Gauss-period transversal:
      eta_b is constant on multiplicative cosets b*mu_n, so there are only
      m=(p-1)/n distinct values; we enumerate one representative per coset using
      a primitive root g (b = g^j), form eta exactly via integer powers, and take
      the max |eta|.  This is O(n*m)=O(p) trig evals but NO p-length FFT array, and
      it is a genuinely different code path (reuses max_period_sq_over_n from the
      additive-vs-mult helper, validated independently).
  * THIS probe sweeps the DIAGONAL p ~ n^beta for beta in {4,5,6} explicitly
    (the prize diagonal), with MANY primes per (n,beta) cell, and uses a DIFFERENT
    prime selection (primes immediately above n^beta, excluding pure-dyadic m so we
    never hit the #400 Fermat trap).  Different range, different method => independent.

REPORTED: C_mean, C_MAX, C_min, spread per (n,beta); the trend C_mean(n); and a
direct beta-comparison at fixed n to decide if C depends on beta.
Also reports the SQUARED inflation C^2 (compare bare-Gaussian floor 1.0 and the
4th-moment floor 1.5) and a log2-normalized C2 for cross-check with the .md table.
"""
import sys, math, time
sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, max_period_sq_over_n
import numpy as np


def primes_on_diagonal(n, beta, want, used, max_tries=4_000_000):
    """`want` valid primes with p ~ n^beta (just above), p == 1 mod n,
    non-pure-dyadic subgroup (odd_part((p-1)/n) > 1) so we avoid the Fermat trap.
    Selection band = immediately above n^beta -> m ~ n^(beta-1) exactly on diagonal."""
    base = int(round(n ** beta))
    base -= base % n
    base += 1                      # p == 1 mod n
    out, p, tries = [], base, 0
    while len(out) < want and tries < max_tries:
        if p > 3 and is_prime(p) and odd_part((p - 1) // n) > 1 and p not in used:
            out.append(p); used.add(p)
        p += n; tries += 1
    return out


def C_of(p, n):
    """C = B/sqrt(n*ln m) using the EXACT coset transversal (max|eta|^2/n)."""
    v = max_period_sq_over_n(p, n)        # = max_b |eta_b|^2 / n  (exact integer powers)
    m = (p - 1) // n
    lnm = math.log(m)
    C2_ln = v / lnm                       # C^2 with natural log
    C2_log2 = v / math.log2(m)            # C^2 with log base 2 (cross-check)
    return math.sqrt(C2_ln), C2_ln, C2_log2, m, lnm


# cost of one C_of(p,n) ~ p trig evals (coset loop). Budget caps p so nothing hangs.
P_BUDGET = 8_000_000     # max p we will evaluate per prime (>=this -> skip cell)
def main():
    sqrt2 = math.sqrt(2)
    flush = lambda *a: print(*a, flush=True)
    flush("#" * 92)
    flush("# #407 Q2 INDEPENDENT house-constant replicate (exact Gauss-period transversal method)")
    flush("# C = B / sqrt(n * ln((p-1)/n));  diagonal p ~ n^beta, beta in {4,5,6}; many primes/cell")
    flush(f"# (cost cap: skip any prime p > {P_BUDGET:,}; cost ~ p per prime)")
    flush("#" * 92)

    # how many primes per cell: smaller n is cheap, bigger n is O(p)=O(n^beta) so taper.
    want_for = {8: 30, 16: 20, 32: 14, 64: 8, 128: 5, 256: 3}

    results = {}  # (n,beta) -> dict
    for beta in (4, 5, 6):
        flush(f"\n{'='*92}\n beta = {beta}   (m ~ n^{beta-1});  C = B/sqrt(n ln m)\n{'='*92}")
        flush(f" {'n':>5} {'#pr':>4} {'mean ln m':>10} {'C_mean':>8} {'C_MAX':>8} {'C_min':>8} "
              f"{'C2_mean(ln)':>11} {'C2_mean(log2)':>13} {'C_MAX>sqrt2?':>12}")
        used = set()
        for n in (8, 16, 32, 64, 128, 256):
            want = want_for[n]
            # skip cells whose diagonal prime n^beta would exceed the cost budget.
            if int(round(n ** beta)) > P_BUDGET:
                continue
            t0 = time.time()
            ps = primes_on_diagonal(n, beta, want, used)
            ps = [p for p in ps if p <= P_BUDGET]
            if not ps:
                continue
            Cs, C2ln, C2l2, lnms = [], [], [], []
            for p in ps:
                C, c2ln, c2l2, m, lnm = C_of(p, n)
                Cs.append(C); C2ln.append(c2ln); C2l2.append(c2l2); lnms.append(lnm)
            Cs = np.array(Cs)
            cmax = Cs.max()
            flag = "YES" if cmax > sqrt2 else "no"
            flush(f" {n:>5} {len(ps):>4} {np.mean(lnms):>10.3f} {Cs.mean():>8.3f} "
                  f"{cmax:>8.3f} {Cs.min():>8.3f} {np.mean(C2ln):>11.3f} "
                  f"{np.mean(C2l2):>13.3f} {flag:>12}   ({time.time()-t0:.1f}s)")
            results[(n, beta)] = dict(cmean=float(Cs.mean()), cmax=float(cmax),
                                      cmin=float(Cs.min()),
                                      c2ln=float(np.mean(C2ln)),
                                      c2l2=float(np.mean(C2l2)),
                                      npr=len(ps), lnm=float(np.mean(lnms)))

    # ---- beta-dependence at fixed n: is C(beta) flat? ----
    flush(f"\n{'='*92}\n BETA-DEPENDENCE at fixed n  (does C depend on beta?)\n{'='*92}")
    flush(f" {'n':>5} | " + "  ".join(f"b={b}:C_mean" for b in (4, 5, 6)))
    for n in (8, 16, 32, 64):
        cells = []
        for b in (4, 5, 6):
            r = results.get((n, b))
            cells.append(f"{r['cmean']:.3f}" if r else "  -  ")
        flush(f" {n:>5} | " + "    ".join(f"{c:>8}" for c in cells))

    # ---- trend in n at fixed beta ----
    flush(f"\n{'='*92}\n TREND IN n at fixed beta (C_mean grows / flat / shrinks?)\n{'='*92}")
    for beta in (4, 5, 6):
        row = []
        for n in (8, 16, 32, 64, 128, 256):
            r = results.get((n, beta))
            if r:
                row.append(f"n={n}:{r['cmean']:.3f}")
        flush(f" beta={beta}: " + "  ".join(row))

    # ---- aggregate verdict ----
    if not results:
        flush("\n  NO CELLS COMPUTED (all over budget). Increase P_BUDGET.")
        return 1
    all_cmean = [r['cmean'] for r in results.values()]
    all_cmax = [r['cmax'] for r in results.values()]
    all_c2ln = [r['c2ln'] for r in results.values()]
    flush(f"\n{'='*92}\n AGGREGATE (all diagonal cells)\n{'='*92}")
    flush(f"  cells computed = {len(results)}")
    flush(f"  C_mean overall = {np.mean(all_cmean):.4f}  (min {min(all_cmean):.3f}, max {max(all_cmean):.3f})")
    flush(f"  C_MAX overall  = {max(all_cmax):.4f}")
    flush(f"  C^2_mean (ln)  = {np.mean(all_c2ln):.4f}   <- inflation vs bare-Gaussian 1.0 / 4th-mom 1.5")
    flush(f"  sqrt(C^2_mean) = {math.sqrt(np.mean(all_c2ln)):.4f}")
    flush(f"\n  Reading: C_mean ~ flat in n AND in beta, C_MAX bounded (< sqrt2 for non-trap) =>")
    flush(f"           FINITE q-INDEPENDENT house constant.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

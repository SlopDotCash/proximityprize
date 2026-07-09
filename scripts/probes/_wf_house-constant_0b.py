#!/usr/bin/env python3
"""_wf_house-constant_0b.py  (#407 Q2 — deeper replicate 1/2 + EVT correction fit)

Follow-up to _wf_house-constant_0.py (my replicate, distinct from twin _wf_house-constant_1.py).
Two goals:

(A) REACH LARGER n on the diagonal p~n^beta using BOTH an exact coset transversal
    AND an independent length-p FFT (cross-method agreement check), with a bigger
    budget so we get n up to 64/128 at beta=4 and n up to 32 at beta=5.

(B) Decide WHY C drifts (n=8:~1.06 -> n=32:~1.24 at beta=4; and beta=4 -> beta=6
    DROPS at fixed n).  EVT prediction for the max of m near-iid complex Gauss sums:
        |S|^2/n ~ Exp(1)-like;  max of m  =>  max|S|^2/n ~ ln m + gamma + lower order.
    Hence  C^2 = max|S|^2/(n ln m) = 1 + gamma/ln m + ...  -> 1 (from ABOVE) as ln m->oo.
    So the SAME asymptotic constant C=1 should explain BOTH drifts if we FIT
        C^2  vs  1/ln m   (and against ln(ln m)/ln m).
    A clean intercept ~1.0 with positive slope = limit is 1 (NOT sqrt2, NOT beta-dep);
    the apparent beta/n drift is just the finite-ln(m) EVT correction.

Reports: per-(n,beta) C via coset and via FFT (must agree); pooled fit of C^2 vs 1/ln m;
extrapolated intercept C^2(ln m -> oo).
"""
import sys, math, time
sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, max_period_sq_over_n, primitive_root
import numpy as np

GAMMA = 0.5772156649015329


def primes_on_diagonal(n, beta, want, used, max_tries=8_000_000):
    base = int(round(n ** beta)); base -= base % n; base += 1
    out, p, tries = [], base, 0
    while len(out) < want and tries < max_tries:
        if p > 3 and is_prime(p) and odd_part((p - 1) // n) > 1 and p not in used:
            out.append(p); used.add(p)
        p += n; tries += 1
    return out


def B_fft(p, n):
    """Independent B via length-p FFT of the indicator of mu_n (different code path
    from the coset transversal). Returns max_{b!=0}|eta_b|."""
    g = primitive_root(p)
    eta = pow(g, (p - 1) // n, p)
    f = np.zeros(p)
    x = 1
    for _ in range(n):
        f[x] = 1.0
        x = x * eta % p
    S = np.fft.fft(f)
    a = np.abs(S); a[0] = 0.0
    return float(np.max(a))


def main():
    flush = lambda *a: print(*a, flush=True)
    sqrt2 = math.sqrt(2)
    flush("#" * 96)
    flush("# #407 Q2 deeper replicate: coset vs FFT agreement + EVT correction fit C^2 = 1 + gamma/ln m")
    flush("#" * 96)

    P_BUDGET_FFT = 40_000_000     # FFT array of float64 length p: 40M*8B=320MB ok
    P_BUDGET_COSET = 12_000_000   # coset is O(p) python trig: keep modest, only as cross-check

    cells = []
    for beta in (4, 5, 6):
        for n in (8, 16, 32, 64, 128):
            cells.append((n, beta))

    want_for = {8: 12, 16: 10, 32: 8, 64: 5, 128: 3}

    rows = []  # (n, beta, lnm, C_coset, C_fft, c2)
    used_global = {}
    flush(f"\n{'n':>4} {'beta':>4} {'#pr':>3} {'mean ln m':>9} {'C_coset':>8} {'C_fft':>7} "
          f"{'agree?':>7} {'C2(ln)':>7}")
    for (n, beta) in cells:
        if int(round(n ** beta)) > P_BUDGET_FFT:
            continue
        used = used_global.setdefault(beta, set())
        ps = primes_on_diagonal(n, beta, want_for[n], used)
        ps = [p for p in ps if p <= P_BUDGET_FFT]
        if not ps:
            continue
        C_coset_list, C_fft_list, lnms = [], [], []
        for p in ps:
            m = (p - 1) // n
            lnm = math.log(m)
            B_f = B_fft(p, n)
            C_f = B_f / math.sqrt(n * lnm)
            C_fft_list.append(C_f)
            if p <= P_BUDGET_COSET:
                v = max_period_sq_over_n(p, n)
                C_c = math.sqrt(v / lnm)
                C_coset_list.append(C_c)
            lnms.append(lnm)
        C_fft = float(np.mean(C_fft_list))
        C_coset = float(np.mean(C_coset_list)) if C_coset_list else float('nan')
        lnm_mean = float(np.mean(lnms))
        agree = "yes" if (C_coset_list and abs(C_coset - C_fft) < 0.01) else \
                ("n/a" if not C_coset_list else "NO!")
        c2 = C_fft ** 2
        flush(f"{n:>4} {beta:>4} {len(ps):>3} {lnm_mean:>9.3f} "
              f"{C_coset:>8.3f} {C_fft:>7.3f} {agree:>7} {c2:>7.3f}")
        rows.append((n, beta, lnm_mean, C_coset, C_fft, c2))

    flush(f"\n{'='*96}\n EVT FIT  C^2 = A + B/ln m   (pooled over all (n,beta) cells)\n{'='*96}")
    X = np.array([1.0 / r[2] for r in rows])
    Y = np.array([r[5] for r in rows])
    Am = np.vstack([X, np.ones_like(X)]).T
    (slopeB, intA), res, *_ = np.linalg.lstsq(Am, Y, rcond=None)
    ss_tot = ((Y - Y.mean()) ** 2).sum()
    ss_res = float(res[0]) if len(res) else ((Y - Am @ [slopeB, intA]) ** 2).sum()
    r2 = 1 - ss_res / ss_tot
    flush(f"   C^2 = {intA:.4f} + {slopeB:.4f}/ln m     R^2={r2:.4f}")
    flush(f"   => intercept A (= C^2 as ln m -> oo) = {intA:.4f}  -> C_inf = {math.sqrt(max(intA,0)):.4f}")
    flush(f"   EVT predicts A=1, B=gamma={GAMMA:.4f}.  Measured B={slopeB:.4f}.")

    flush(f"\n RESIDUAL vs pure EVT  (C^2 - [1 + gamma/ln m]):  should be ~0 if law is exact")
    for (n, beta, lnm, Cc, Cf, c2) in rows:
        pred = 1.0 + GAMMA / lnm
        flush(f"   n={n:>3} beta={beta} ln m={lnm:6.3f}  C2={c2:6.3f}  EVTpred={pred:6.3f}  resid={c2-pred:+.3f}")

    flush(f"\n{'='*96}\n BETA-INDEPENDENCE controlled for ln m\n{'='*96}")
    flush("   If C depends only on ln m (not on beta or n separately), points at equal ln m coincide.")
    by_lnm = sorted(rows, key=lambda r: r[2])
    for (n, beta, lnm, Cc, Cf, c2) in by_lnm:
        flush(f"   ln m={lnm:6.3f}  (n={n:>3}, beta={beta})  C={Cf:.4f}")

    flush(f"\n{'='*96}\n VERDICT\n{'='*96}")
    allC = [r[4] for r in rows]
    allCmax = max(r[4] for r in rows)
    flush(f"  C_mean over all cells = {np.mean(allC):.4f}   C_MAX = {allCmax:.4f}  (sqrt2={sqrt2:.4f})")
    flush(f"  Extrapolated C(ln m -> oo) = {math.sqrt(max(intA,0)):.4f}")
    flush(f"  If intercept ~1.0 and points collapse onto a single C(ln m) curve =>")
    flush(f"  FINITE limit C=1 (NOT sqrt2); apparent n/beta drift = finite-ln(m) EVT correction.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

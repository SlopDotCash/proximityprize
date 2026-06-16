#!/usr/bin/env python3
"""_wf_house-constant_0c.py  (#407 Q2 — the n-trend: does C grow or plateau?)

Replicates 0/0b found: C is NOT a function of ln m alone; it is driven by n
(C grows with n at fixed beta, shrinks with beta at fixed n).  The decisive question
for "finite house constant" is therefore: as n -> oo on the diagonal, does C_mean(n)
PLATEAU (finite house constant) or keep GROWING (no finite constant; would refute the
clean closed form)?

This probe pushes n as high as feasible at the CHEAPEST diagonal beta=4 (smallest p per n
that is still 'on diagonal' = m~n^3), with many primes per n, and fits C_mean(n) against
several candidate growth laws:
    (i)  C^2 = a + b/ln m            (pure EVT, already refuted)
    (ii) C^2 = a + b*(ln n)/(ln m)   (= a + b/(beta-1): EVT with the RIGHT count.
         KEY INSIGHT: the m periods are NOT iid; they come in n-fold coset blocks and
         the relevant 'effective independent count' tracks n.  ln n / ln m = 1/(beta-1).)
    (iii)C^2 = a + b*ln(ln n)        (slow growth in n -> no finite constant)
A flat C^2 vs ln n (slope ~0) => finite constant; positive persistent slope => grows.

For n where p=n^4 exceeds the FFT budget we use the EXACT coset transversal (O(p) but no
big array) up to a higher budget, and a random-b LOWER-bound sample beyond that.
"""
import sys, math, time, random
sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, max_period_sq_over_n, primitive_root
import numpy as np

random.seed(40717)
GAMMA = 0.5772156649015329


def primes_on_diagonal(n, beta, want, used, max_tries=12_000_000):
    base = int(round(n ** beta)); base -= base % n; base += 1
    out, p, tries = [], base, 0
    while len(out) < want and tries < max_tries:
        if p > 3 and is_prime(p) and odd_part((p - 1) // n) > 1 and p not in used:
            out.append(p); used.add(p)
        p += n; tries += 1
    return out


def B_fft(p, n):
    g = primitive_root(p); eta = pow(g, (p - 1) // n, p)
    f = np.zeros(p); x = 1
    for _ in range(n):
        f[x] = 1.0; x = x * eta % p
    S = np.fft.fft(f); a = np.abs(S); a[0] = 0.0
    return float(np.max(a))


def B_sample_lower(p, n, ksamp=3_000_000):
    """Random-b LOWER bound on B (vectorized). C_sample <= C_true. For huge p."""
    g = primitive_root(p); eta = pow(g, (p - 1) // n, p)
    xs = np.array([pow(eta, i, p) for i in range(n)], dtype=np.int64)
    twp = 2.0 * math.pi / p
    best = 0.0
    bs = np.random.randint(1, p, size=ksamp, dtype=np.int64)
    CH = max(1, 4_000_000 // n)
    for j in range(0, ksamp, CH):
        bb = bs[j:j+CH]
        ang = ((bb[:, None] * xs[None, :]) % p).astype(np.float64) * twp
        S2 = np.cos(ang).sum(1) ** 2 + np.sin(ang).sum(1) ** 2
        mx = float(S2.max())
        if mx > best: best = mx
    return math.sqrt(best)


def main():
    flush = lambda *a: print(*a, flush=True)
    sqrt2 = math.sqrt(2)
    flush("#" * 96)
    flush("# #407 Q2  n-TREND on the beta=4 diagonal: does C_mean(n) plateau or grow?")
    flush("#" * 96)

    P_FFT = 100_000          # FFT only for tiny p; coset (low memory) for the rest
    P_COSET = 30_000_000     # coset transversal is O(p) chunked trig, low memory
    beta = 4

    want_for = {8: 16, 16: 12, 32: 10, 64: 4, 128: 1, 256: 1}
    ns = [8, 16, 32, 64, 128, 256]

    rows = []  # (n, lnm, C, mode)
    used = set()
    flush(f"\n diagonal beta={beta} (m~n^3);  C = B/sqrt(n*ln m)")
    flush(f" {'n':>5} {'#pr':>3} {'mean p':>14} {'mean ln m':>9} {'C_mean':>7} {'C_MAX':>7} {'mode':>7}")
    for n in ns:
        ps = primes_on_diagonal(n, beta, want_for[n], used)
        if not ps:
            continue
        Cs, lnms = [], []
        mode = None
        for p in ps:
            m = (p - 1) // n; lnm = math.log(m)
            if p <= P_FFT:
                B = B_fft(p, n); mode = "fft"
            elif p <= P_COSET:       # exact coset transversal (low memory, O(p))
                v = max_period_sq_over_n(p, n); B = math.sqrt(v * n); mode = "coset"
            else:
                B = B_sample_lower(p, n); mode = "sample(LB)"
            Cs.append(B / math.sqrt(n * lnm)); lnms.append(lnm)
        Cs = np.array(Cs)
        rows.append((n, float(np.mean(lnms)), float(Cs.mean()), float(Cs.max()), mode))
        flush(f" {n:>5} {len(ps):>3} {np.mean(ps):>14.0f} {np.mean(lnms):>9.3f} "
              f"{Cs.mean():>7.3f} {Cs.max():>7.3f} {mode:>11}")

    flush(f"\n{'='*96}\n GROWTH-LAW FITS for C_mean(n) on beta=4 diagonal\n{'='*96}")
    N = np.array([r[0] for r in rows], float)
    C = np.array([r[2] for r in rows], float)
    C2 = C ** 2
    lnm = np.array([r[1] for r in rows], float)
    lnn = np.log(N)

    def fit(label, X):
        A = np.vstack([X, np.ones_like(X)]).T
        (b, a), res, *_ = np.linalg.lstsq(A, C2, rcond=None)
        ss_tot = ((C2 - C2.mean()) ** 2).sum()
        ss_res = float(res[0]) if len(res) else ((C2 - A @ [b, a]) ** 2).sum()
        r2 = 1 - ss_res / ss_tot
        flush(f"   {label:38s}:  C^2 = {a:.4f} + {b:.4f}*X   R^2={r2:.4f}")
        return a, b, r2

    fit("(i)   X = 1/ln m   [pure EVT]", 1.0 / lnm)
    fit("(ii)  X = ln n / ln m = 1/(beta-1)", lnn / lnm)
    fit("(iii) X = ln(ln n)  [grows w/o bound]", np.log(lnn))
    fit("(iv)  X = ln n       [grows linearly]", lnn)

    flush(f"\n   Direct C_mean vs n (is the last step shrinking? -> plateau):")
    for i, (n, lm, c, cmax, mode) in enumerate(rows):
        dC = "" if i == 0 else f"  dC/dlog2(n)={ (c-rows[i-1][2])/(math.log2(n)-math.log2(rows[i-1][0])):+.4f}"
        flush(f"     n={n:>4}  C_mean={c:.4f}{dC}")

    flush(f"\n{'='*96}\n VERDICT (n-trend, beta=4)\n{'='*96}")
    flush(f"  C ranges {C.min():.3f}..{C.max():.3f} over n={int(N.min())}..{int(N.max())}.")
    flush(f"  If dC/dlog2(n) is SHRINKING toward 0 -> plateau (finite house constant).")
    flush(f"  If roughly CONSTANT -> C ~ a + b*log2(n): GROWS, no finite constant in n.")
    flush(f"  Note: sample(LB) rows are LOWER bounds (true C >= shown).")
    return 0


if __name__ == "__main__":
    sys.exit(main())

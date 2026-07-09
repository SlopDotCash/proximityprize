#!/usr/bin/env python3
"""_wf_house-constant_1.py  (#407 -- INDEPENDENT REPLICATE 2/2 of the Gauss-period house constant)

Q2: Does the house constant
    C(p,n) := B(mu_n) / sqrt(n * ln((p-1)/n)),   B = max_{b!=0} |sum_{x in mu_n} e_p(bx)|,
converge to a FINITE limit on the prize diagonal p ~ n^beta, and what is it (sqrt2=1.414? 1.33?
beta-dependent?) -- multi-prime sweep, beta in {4,5,6}, n=8..256, many primes per n.

INDEPENDENT METHOD (deliberately DIFFERENT from the FFT twin):
  - NO numpy FFT.  B is the max over the m=(p-1)/n DISTINCT Gauss-period eigenvalues
    eta_j = sum_{x in mu_n} e_p(g^j x), j=0..m-1 (constant on cosets of mu_n in F_p^*).
    Two exact/independent estimators of B:
      * EXACT mode (p small enough, m*n <= WORKCAP): evaluate ALL m coset sums directly,
        max |eta_j|.  Algebraically distinct from FFT -> genuine cross-validation.
      * SAMPLE mode (large p on deep diagonal): draw KSAMP random b in F_p^*, take max
        |sum_x e_p(bx)| -- a rigorous LOWER bound on B (so C_sample <= C_true).  Reported
        separately and flagged; lower bounds that already cluster near the EXACT-mode value
        confirm the limit without needing FFT on a 1e9-length array.
  - Primes drawn directly ON each diagonal p ~ n^beta (window scan around round(n^beta) for
    p == 1 mod n, Miller-Rabin).  Hits the TRUE prize diagonal, not a fixed band.

Reports per (n,beta): mode, #primes, C_mean, C_median, C_MAX, prime achieving max.
Then beta-comparison and n-trend tables.
"""
import math, random
import numpy as np

random.seed(40717)
np.random.seed(40717)

_SPRP = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
def is_prime(x):
    if x < 2: return False
    for w in _SPRP:
        if x % w == 0: return x == w
    d, s = x - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for w in _SPRP:
        v = pow(w, d, x)
        if v in (1, x - 1): continue
        for _ in range(s - 1):
            v = v * v % x
            if v == x - 1: break
        else:
            return False
    return True

def primitive_root(p):
    n = p - 1
    fac = set(); d = 2; m = n
    while d * d <= m:
        if m % d == 0:
            fac.add(d)
            while m % d == 0: m //= d
        d += 1 if d == 2 else 2
    if m > 1: fac.add(m)
    for g in range(2, p):
        if all(pow(g, n // q, p) != 1 for q in fac):
            return g
    return None

def mu_n_elements(p, n, g):
    m = (p - 1) // n
    h = pow(g, m, p)
    mu = [0] * n
    x = 1
    for i in range(n):
        mu[i] = x
        x = x * h % p
    return mu

WORKCAP = 400_000      # max m for EXACT mode (m coset reps scanned)
KSAMP   = 8000         # random b-samples for SAMPLE mode (lower bound on B)
CHUNK   = 20_000       # cosets / samples processed per numpy batch (memory bound)

def _max_over_bs(bs, mu_arr, p):
    """Vectorized: max_b |sum_{x in mu} exp(2pi i (b*x mod p)/p)| over array bs (no FFT)."""
    tp = 2.0 * math.pi / p
    best = 0.0
    for s in range(0, len(bs), CHUNK):
        bb = bs[s:s + CHUNK].astype(np.int64)           # (K,)
        # phases (K, n): (b * x) mod p  -- explicit character matrix, NOT an FFT
        prod = (bb[:, None] * mu_arr[None, :]) % p       # (K, n)
        ph = np.exp((1j * tp) * prod)                    # (K, n)
        sums = ph.sum(axis=1)                            # (K,)
        mx = float(np.max(np.abs(sums)))
        if mx > best: best = mx
    return best

def house_C(p, n):
    """Return (C, mode). mode='exact' (all m cosets) or 'samp' (random lower bound)."""
    g = primitive_root(p)
    if g is None: return None
    mu = mu_n_elements(p, n, g)
    mu_arr = np.array(mu, dtype=np.int64)
    m = (p - 1) // n
    if m <= WORKCAP:
        # all coset reps r_j = g^j, j=0..m-1  (multiplicative walk to build the b-list)
        bs = np.empty(m, dtype=np.int64)
        r = 1
        for j in range(m):
            bs[j] = r
            r = r * g % p
        best = _max_over_bs(bs, mu_arr, p)
        mode = 'exact'
    else:
        bs = np.random.randint(1, p, size=KSAMP, dtype=np.int64)
        best = _max_over_bs(bs, mu_arr, p)
        mode = 'samp'
    return best / math.sqrt(n * math.log(m)), mode

def primes_near_diagonal(n, beta, want):
    T = int(round(n ** beta))
    base = T - ((T - 1) % n)
    out = []; up = base + n; down = base; step = 0
    while len(out) < want and (down > n or up < 4 * T):
        for cand in (down, up):
            if cand > n and is_prime(cand):
                out.append(cand)
                if len(out) >= want: break
        down -= n; up += n; step += 1
        if step > 2_000_000: break
    return sorted(set(out))

NS = [8, 16, 32, 64, 128, 256]
BETAS = [4, 5, 6]

def nprimes_for(n, beta):
    p_est = n ** beta
    m_est = p_est / n
    # cost ~ m*n (exact) or KSAMP*n (samp); keep total work per (n,beta) bounded
    if m_est <= WORKCAP:                      # exact mode
        if p_est <= 3e5:  return 60
        if p_est <= 3e6:  return 36
        return 16
    return 20   # sample mode: KSAMP*n*nprimes work, cheap

def _fft_C(p, n):
    """Twin's FFT method, for cross-validation only."""
    g = primitive_root(p)
    mu = mu_n_elements(p, n, g)
    f = np.zeros(p)
    for x in mu: f[x] = 1.0
    a = np.abs(np.fft.fft(f)); a[0] = 0.0
    m = (p - 1) // n
    return float(np.max(a)) / math.sqrt(n * math.log(m))

print("CROSS-VALIDATION: my direct coset method vs the twin's FFT method (must agree exactly):")
for (p, n) in [(3137, 8), (67169, 16), (1048129, 32)]:
    cd = house_C(p, n)[0]; cf = _fft_C(p, n)
    print(f"   p={p:>9} n={n:>3}: direct C={cd:.6f}  FFT C={cf:.6f}  |diff|={abs(cd-cf):.2e}")
print()

print("INDEPENDENT REPLICATE (direct coset/eigenvalue sum, NO FFT): Gauss-period house constant")
print("C = B / sqrt(n * ln((p-1)/n)),  B = max_{b!=0}|sum_{x in mu_n} e_p(bx)|")
print("Prize diagonal p ~ n^beta, beta in {4,5,6}, n=8..256.  sqrt2=1.41421, sqrt(1.75)=1.32288")
print("mode 'exact' = all m cosets; 'samp' = max over %d random b (LOWER bound on B)\n" % KSAMP)

results = {}
hdr = f"{'n':>4} {'beta':>4} {'mode':>5} {'#p':>3} {'p_lo':>13} {'p_hi':>13} {'C_mean':>7} {'C_med':>7} {'C_MAX':>7} {'@p_max':>13}"
print(hdr); print("-" * len(hdr))
for n in NS:
    for beta in BETAS:
        ps = primes_near_diagonal(n, beta, nprimes_for(n, beta))
        Cs = []; worst = (0.0, None); mode = '?'
        for p in ps:
            res = house_C(p, n)
            if res is None: continue
            C, mode = res
            Cs.append(C)
            if C > worst[0]: worst = (C, p)
        if not Cs: continue
        Cs_s = sorted(Cs)
        cmean = sum(Cs) / len(Cs); cmed = Cs_s[len(Cs_s) // 2]
        results[(n, beta)] = dict(np=len(Cs), mean=cmean, med=cmed, mx=worst[0],
                                  pmax=worst[1], plo=ps[0], phi=ps[-1], mode=mode)
        print(f"{n:>4} {beta:>4} {mode:>5} {len(Cs):>3} {ps[0]:>13} {ps[-1]:>13} "
              f"{cmean:>7.3f} {cmed:>7.3f} {worst[0]:>7.3f} {worst[1]:>13}", flush=True)

print("\nBETA-DEPENDENCE (does C depend on beta?):  [exact-mode rows dominate; samp = lower bd]")
print(f"{'beta':>4} {'mean C_mean':>12} {'mean C_MAX':>11} {'overall C_MAX':>14} {'@(n,p)':>20}")
for beta in BETAS:
    keys = [(n, beta) for n in NS if (n, beta) in results]
    if not keys: continue
    means = [results[k]['mean'] for k in keys]; mxs = [results[k]['mx'] for k in keys]
    omx = max(keys, key=lambda k: results[k]['mx'])
    loc = f"({omx[0]},{results[omx]['pmax']})"
    print(f"{beta:>4} {sum(means)/len(means):>12.3f} {sum(mxs)/len(mxs):>11.3f} "
          f"{results[omx]['mx']:>14.3f} {loc:>20}")

print("\nN-TREND at beta=5 (grow with n -> unbounded; settle -> finite limit):")
print(f"{'n':>5} {'mode':>5} {'C_mean':>7} {'C_MAX':>7}")
for n in NS:
    k = (n, 5)
    if k in results:
        print(f"{n:>5} {results[k]['mode']:>5} {results[k]['mean']:>7.3f} {results[k]['mx']:>7.3f}")

print("\nN-TREND at beta=4 (densest exact-mode coverage):")
print(f"{'n':>5} {'mode':>5} {'C_mean':>7} {'C_MAX':>7}")
for n in NS:
    k = (n, 4)
    if k in results:
        print(f"{n:>5} {results[k]['mode']:>5} {results[k]['mean']:>7.3f} {results[k]['mx']:>7.3f}")

exact_keys = [k for k in results if results[k]['mode'] == 'exact']
allmax = max(results[k]['mx'] for k in exact_keys)
allmean = sum(results[k]['mean'] for k in exact_keys) / len(exact_keys)
gk = max(exact_keys, key=lambda k: results[k]['mx'])
print(f"\nGLOBAL (EXACT mode only): C_mean = {allmean:.3f}")
print(f"GLOBAL (EXACT mode only): C_MAX  = {allmax:.3f}  at (n={gk[0]}, beta={gk[1]}, p={results[gk]['pmax']})")
samp_max = max((results[k]['mx'] for k in results if results[k]['mode'] == 'samp'), default=0.0)
print(f"SAMPLE-mode C_MAX (lower bound, deep diagonal) = {samp_max:.3f}")
print(f"reference: sqrt2={math.sqrt(2):.5f}  |  1.33  |  sqrt(1.75)={math.sqrt(1.75):.5f}")

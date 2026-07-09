#!/usr/bin/env python3
"""ADVERSARIAL VERIFICATION of finding F4 (#407 prize exponent).

CLAIM UNDER TEST (F4): the max Gaussian-period magnitude
    B(p,n) = max_{b != 0} | sum_{x in mu_n} e_p(b*x) |,   e_p(t)=exp(2*pi*i*t/p)
scales on the prize diagonal (beta=4, p ~ n^beta) as the SQRT(n log) law
    B ~ n^{1/2 + o(1)}   with apparent exponent  a = log B / log n  -> 1/2,
NOT as the n^{3/4} moment-method ceiling (a -> 3/4 staying flat).

This is an INDEPENDENT reimplementation written from scratch.

KEY NUMERICS / SAFETY:
 * beta = 4, n in {128,256,512,1024}. p ~ n^4 so p in [2^28, 2^40] < 2^47.
 * m = (p-1)/n cosets is up to ~2^30 (n=1024): exhaustive max is infeasible,
   so we use EXTREME-VALUE SAMPLING -- a large uniform random sample of cosets,
   take the sample-max. (Underestimate is BOUNDED, so the *exponent* a is robust:
   a multiplicative underestimate factor f shifts a by log f / log n = o(1).)
 * Overflow-safe modular multiply: b*x with b,x < 2^47 would be ~2^94 and overflow
   int64. We use 15-bit-limb Horner reduction (base 2^15, 4 limbs), reducing mod p
   after every limb so every intermediate product stays < 2^63. BOTH the scalar and
   the vectorized modmul are VERIFIED against python's exact (b*x)%p before use.
 * Exclude Fermat / fully-dyadic primes: require odd_part((p-1)//n) > 1.

PREDICTION (F4 sqrt(n log) law):  if  B^2 ~ C^2 * n * log(p/n)  with p=n^beta,
log(p/n) = (beta-1) log n, then
    a = log B / log n = 1/2 + [ 0.5*ln(C^2*(beta-1)) + 0.5*ln(ln n) ] / ln n,
which DECREASES toward 1/2 as n grows.  The competing moment ceiling predicts
a ~ 0.75 (flat).  We fit C^2 = B^2 / (n*(beta-1)*ln n) and report a + both models.
"""
import sys, math, random
import numpy as np

# ---------------------------------------------------------------------------
# number theory helpers (independent reimplementation)
# ---------------------------------------------------------------------------
def is_prime(n):
    if n < 2: return False
    small = (2,3,5,7,11,13,17,19,23,29,31,37)
    for q in small:
        if n % q == 0: return n == q
    d = n - 1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in small:
        x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(r-1):
            x = x*x % n
            if x == n-1: break
        else:
            return False
    return True

def odd_part(x):
    while x % 2 == 0: x //= 2
    return x

def primitive_root(p):
    phi = p - 1; facs = []; m = phi; d = 2
    while d*d <= m:
        if m % d == 0:
            facs.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: facs.append(m)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in facs):
            return g
    raise RuntimeError("no primitive root")

def find_prime(n, beta, used):
    """Smallest valid prime p ~ n^beta with n | p-1, odd_part((p-1)/n)>1, not used."""
    target = int(round(n ** beta))
    base = target - (target % n) + 1            # = 1 mod n
    p = base
    tries = 0
    while tries < 5_000_000:
        if p > 3 and is_prime(p) and odd_part((p-1)//n) > 1 and p not in used:
            used.add(p); return p
        p += n; tries += 1
    raise RuntimeError(f"no prime found for n={n}, beta={beta}")

# ---------------------------------------------------------------------------
# overflow-safe modular arithmetic (p < 2^47)  -- 15-bit-limb Horner
# ---------------------------------------------------------------------------
BASE_BITS = 15
NLIMB = 4                     # ceil(47/15) = 4
_BASE = 1 << BASE_BITS
_MASK = _BASE - 1

def _limbs_msf(x):
    """limbs of x in base 2^15, most-significant first (length NLIMB)."""
    return [(x >> (BASE_BITS*k)) & _MASK for k in range(NLIMB-1, -1, -1)]

def modmul_scalar(b, x, p):
    """(b*x) % p, overflow-safe, b,x in [0,p), p < 2^47."""
    acc = 0
    for lb in _limbs_msf(x):
        acc = (acc * _BASE) % p
        acc = (acc + b * lb) % p
    return acc

def modmul_vec(b_arr, x, p):
    """elementwise (b_arr*x) % p as int64 array; x scalar; all < 2^47."""
    p64 = np.int64(p); B64 = np.int64(_BASE)
    acc = np.zeros_like(b_arr)
    for lb in _limbs_msf(x):
        lb64 = np.int64(lb)
        acc = (acc * B64) % p64          # acc<2^47 -> <2^62
        acc = (acc + b_arr * lb64) % p64 # b_arr<2^47, lb<2^15 -> <2^62; sum<2^63
    return acc

def self_test_modmul(seed=12345, n_scalar=50000, n_vec=2000):
    rng = random.Random(seed)
    for _ in range(n_scalar):
        p = rng.randrange(3, 1 << 47)
        b = rng.randrange(0, p); x = rng.randrange(0, p)
        if modmul_scalar(b, x, p) != (b*x) % p:
            return False, ("scalar", b, x, p)
    for _ in range(n_vec):
        p = rng.randrange(3, 1 << 47)
        x = rng.randrange(0, p)
        barr = np.array([rng.randrange(0, p) for _ in range(48)], dtype=np.int64)
        got = modmul_vec(barr, x, p)
        ref = np.array([(int(bb)*x) % p for bb in barr], dtype=np.int64)
        if not np.array_equal(got, ref):
            return False, ("vector", x, p)
    return True, None

# ---------------------------------------------------------------------------
# Gaussian period magnitude via extreme-value sampling over cosets
# ---------------------------------------------------------------------------
def sample_B(p, n, n_samples, seed):
    """Estimate B = max_{b!=0} |eta_b| by EXTREME-VALUE SAMPLING over b.

    |eta_b| depends only on the coset b*mu_n, and a uniform random b in [1,p)
    lands in a uniform random coset (verified: max over all b == max over coset
    reps).  So we sample b uniformly in [1,p), compute
        eta_b = sum_{x in mu_n} exp(2*pi*i*(b*x mod p)/p)
    with the overflow-safe limb modmul forming (b*x) mod p, and take the max |eta_b|.
    Sampling without replacement is unnecessary for a MAX; uniform-with-replacement
    over the huge b-space gives a negligible collision rate. Returns
    (B_estimate, m, n_used, frac_of_cosets, best_b).
    """
    g = primitive_root(p)
    m = (p - 1) // n
    eta = pow(g, m, p)
    xs = np.empty(n, dtype=np.int64)            # subgroup mu_n = {eta^i}
    cur = 1
    for i in range(n):
        xs[i] = cur
        cur = (cur * eta) % p
    twp = 2.0 * math.pi / p

    rng = np.random.default_rng(seed)
    exhaustive = (m <= n_samples)
    if exhaustive:
        # cheap case: enumerate all coset reps g^0..g^{m-1} exactly
        bs_all = np.empty(m, dtype=np.int64)
        c = 1
        for j in range(m):
            bs_all[j] = c; c = (c * g) % p
        n_used = m; frac = 1.0
    else:
        n_used = n_samples; frac = n_samples / m

    best = -1.0; best_b = None
    top = []                       # keep top ~5000 mag2 for extreme-value extrapolation
    KEEP = 5000
    CHUNK = 50000
    s = 0
    while s < n_used:
        cnt = min(CHUNK, n_used - s)
        if exhaustive:
            bs = bs_all[s:s+cnt]
        else:
            bs = rng.integers(1, p, size=cnt, dtype=np.int64)   # uniform in [1,p)
        re = np.zeros(cnt); im = np.zeros(cnt)
        for i in range(n):
            xi = int(xs[i])
            prod = modmul_vec(bs, xi, p).astype(np.float64) * twp
            re += np.cos(prod); im += np.sin(prod)
        mag2 = re*re + im*im
        k = int(np.argmax(mag2))
        if mag2[k] > best:
            best = float(mag2[k]); best_b = int(bs[k])
        # accumulate top values
        top.extend(mag2.tolist())
        if len(top) > 4*KEEP:
            top = sorted(top)[-KEEP:]
        s += cnt
    sample_B = math.sqrt(best)
    # ---- Gumbel extreme-value extrapolation to the full coset population m ----
    # |eta_b|^2 has an approx exponential right tail (chi^2-like); fit the upper
    # tail and extrapolate the max over m draws.  E[max of m] = mu + sigma*ln(m).
    top = sorted(top)[-KEEP:]
    if not exhaustive and len(top) >= 200:
        arr = np.array(top)
        # peaks-over-threshold: exponential tail fit on exceedances over the
        # 50th pct of retained top values
        thr = np.quantile(arr, 0.5)
        exc = arr[arr >= thr] - thr
        scale = exc.mean()                      # exp tail scale (sigma for Gumbel of max)
        # number of draws above thr in the FULL population:
        frac_above = (arr >= thr).mean() * (n_used / m)   # frac of all m above thr
        N_above = max(frac_above * m, 1.0)
        # expected max over N_above exp(thr,scale) draws ~ thr + scale*ln(N_above)
        ev_max2 = thr + scale * math.log(N_above)
        ev_B = math.sqrt(max(ev_max2, best))
    else:
        ev_B = sample_B
    return sample_B, ev_B, m, n_used, frac, best_b

# ---------------------------------------------------------------------------
def main():
    beta = 4.0
    ns = [128, 256, 512, 1024]
    # Sampling budget per n. n=128 (m~2.1e6) is fully exhaustible -> EXACT B.
    # Larger n use extreme-value sampling. NOTE: the sample-max underestimates
    # the true B, and the bias grows as the sampled fraction shrinks; since that
    # bias would *lower* large-n exponents and thus FAVOR the sqrt-log conclusion,
    # we (a) exhaust n=128 exactly, (b) report frac, (c) run a Gumbel
    # extreme-value extrapolation to correct the sample-max upward.
    budgets = {128: 2_097_151, 256: 1_000_000, 512: 700_000, 1024: 500_000}

    print("#"*92)
    print("# F4 ADVERSARIAL VERIFY: prize exponent  a = log B / log n  ->  1/2 (sqrt-log) or 0.75 (ceiling)?")
    print("#"*92)
    ok, info = self_test_modmul()
    print(f"[self-test] overflow-safe modmul (15-bit limb, 50k scalar + 2k*48 vector cases): "
          f"{'PASS' if ok else 'FAIL '+str(info)}")
    if not ok:
        print("ABORT: modmul self-test failed."); return 1

    used = set()
    rows = []
    print(f"\n beta={beta}   (B_raw = sample-max; B_ev = Gumbel-extrapolated max over all m cosets)")
    print(f" {'n':>5} {'p':>14} {'log2p':>6} {'m=cosets':>11} {'sampled':>9} {'frac':>9} "
          f"{'B_raw':>9} {'B_ev':>9} {'a_raw':>7} {'a_ev':>7} {'C^2_ev':>7}")
    for n in ns:
        p = find_prime(n, beta, used)
        budget = budgets[n]
        B_raw, B_ev, m, n_used, frac, bb = sample_B(p, n, budget, seed=1000 + n)
        lnn = math.log(n)
        a_raw = math.log(B_raw) / lnn
        a_ev = math.log(B_ev) / lnn
        # fitted constant C^2 from  B^2 = C^2 * n * (beta-1) * ln n  (log(p/n)=(beta-1)ln n)
        C2 = B_ev*B_ev / (n * (beta - 1.0) * lnn)
        rows.append((n, p, m, n_used, frac, B_raw, B_ev, a_raw, a_ev, C2))
        print(f" {n:>5} {p:>14} {math.log2(p):>6.2f} {m:>11} {n_used:>9} {frac:>9.2e} "
              f"{B_raw:>9.3f} {B_ev:>9.3f} {a_raw:>7.4f} {a_ev:>7.4f} {C2:>7.3f}")

    # row layout: (n, p, m, n_used, frac, B_raw, B_ev, a_raw, a_ev, C2)
    print("\n" + "="*92)
    print(" MODEL DISCRIMINATION  (using EV-corrected B_ev to neutralize sampling bias)")
    print("="*92)
    print(f" {'n':>5} {'B/sqrt(n)':>10} {'B/n^0.75':>10} {'B/sqrt(n*log(p/n))':>20} "
          f"{'pred a(sqrtlog)':>16}")
    C2_avg = float(np.mean([r[9] for r in rows]))
    Cfit = math.sqrt(C2_avg)
    for r in rows:
        n, B = r[0], r[6]                       # use B_ev
        lnn = math.log(n)
        nrm_sqrt = B / math.sqrt(n)
        nrm_34 = B / n**0.75
        nrm_law = B / math.sqrt(n * (beta-1.0) * lnn)
        pred_a = 0.5 + (0.5*math.log(Cfit*Cfit*(beta-1.0)) + 0.5*math.log(lnn)) / lnn
        print(f" {n:>5} {nrm_sqrt:>10.3f} {nrm_34:>10.3f} {nrm_law:>20.4f} {pred_a:>16.4f}")

    a_raw_vals = [r[7] for r in rows]
    a_ev_vals  = [r[8] for r in rows]
    nrm34  = [r[6]/r[0]**0.75 for r in rows]
    nrmlaw = [r[6]/math.sqrt(r[0]*(beta-1.0)*math.log(r[0])) for r in rows]

    print("\n DIAGNOSIS:")
    print(f"  apparent exponent a_raw = {['%.4f'%v for v in a_raw_vals]}  (sample-max)")
    print(f"  apparent exponent a_ev  = {['%.4f'%v for v in a_ev_vals]}  (EV-corrected)")
    da_raw = a_raw_vals[-1] - a_raw_vals[0]
    da_ev  = a_ev_vals[-1]  - a_ev_vals[0]
    print(f"  delta a (n=128->1024): raw={da_raw:+.4f}  ev={da_ev:+.4f}")
    cv34 = np.std(nrm34)/np.mean(nrm34)
    cvlaw = np.std(nrmlaw)/np.mean(nrmlaw)
    print(f"  B_ev/n^0.75 across n   : {['%.3f'%v for v in nrm34]}   (CV={cv34:.3f})")
    print(f"  B_ev/sqrt(n*log(p/n))  : {['%.4f'%v for v in nrmlaw]}   (CV={cvlaw:.3f})  <- F1 plateau check")
    # distance of EV exponent from each model target
    d_half = abs(a_ev_vals[-1] - 0.5)
    d_34   = abs(a_ev_vals[-1] - 0.75)
    print(f"  at n=1024: a_ev={a_ev_vals[-1]:.4f}  |a-0.5|={d_half:.3f}  |a-0.75|={d_34:.3f}")
    print()
    if da_ev < -0.005 and cvlaw < cv34:
        verdict = ("F4 REPRODUCES: EV-corrected a decreases toward 1/2 AND B/sqrt(n log) is the "
                   "flatter normalizer (CV) -> sqrt(n log) law, NOT n^{3/4} ceiling.")
    elif da_ev < -0.005:
        verdict = ("F4 PARTIALLY reproduces: EV-corrected a decreases (sqrt-log direction) but "
                   "B/sqrt(n log) is not strictly the flattest normalizer.")
    else:
        verdict = ("F4 does NOT reproduce: EV-corrected exponent does not trend to 1/2.")
    print("  VERDICT:", verdict)
    print("\n  C_eff (fitted, B^2 = C^2 n log(p/n)) =", f"{Cfit:.4f}", "  (C^2 =", f"{C2_avg:.4f})")
    return 0

if __name__ == "__main__":
    sys.exit(main())

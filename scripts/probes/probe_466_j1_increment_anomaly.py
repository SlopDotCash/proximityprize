#!/usr/bin/env python3
"""
[466-J1] Shift-resolved increment anomaly scan — does the Jacobi-cocycle chaining
candidate (doctrine-v3 survivor #1) have ANY fuel?

Setup: p ≡ 1 mod n, n = 2^k ≈ p^{1/4}, g of order n, μ_n = <g>. Periods
η_b = Σ_{j<n} e_p(b g^j) for b over coset reps of F_p^*/μ_n (m = (p−1)/n cosets).

G69/G70 proved the EUCLIDEAN increment metric is BGK-tight (flat-Dudley dead). The one
named surviving chaining candidate injects Jacobi-phase (cocycle) structure — which can
only help if the increment field η_{bs} − η_b, resolved by the multiplicative shift s,
shows structure BEYOND its Euclidean scale:
  - anomalously light or heavy tails at special shifts s (vs Gaussian at scale σ(s)),
  - or shift-classes where max_b |D| deviates from the Gaussian-EVT prediction
    σ(s)·√(2 log m).

VERDICT semantics: if for EVERY shift class the normalized max and tail statistics match
the Gaussian model within fluctuation bands, the increment field is |η|-Euclidean-complete
and the cocycle candidate has nothing to grab — survivor #1 dies (doctrine v4). Any
anomalous shift class is the first non-|η| signal of the campaign.
"""
import numpy as np, sys

def isprime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        if m % q == 0: return m == q
    d = m-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else:
            return False
    return True

def find_g_of_order(n, p):
    for h in range(2, p):
        g = pow(h, (p-1)//n, p)
        if g != 1 and pow(g, n//2, p) != 1:
            return g
    raise RuntimeError

def eta_field(n, p):
    """η_b for b = γ^i, i < m, γ a generator of F_p^* (so cosets are indexed by i mod m)."""
    # find primitive root γ
    fac = []
    q = p-1; d = 2
    while d*d <= q:
        if q % d == 0:
            fac.append(d)
            while q % d == 0: q //= d
        d += 1
    if q > 1: fac.append(q)
    for gam in range(2, p):
        if all(pow(gam, (p-1)//f, p) != 1 for f in fac):
            break
    m = (p-1)//n
    g = pow(gam, m, p)  # order n
    # subgroup elements
    sub = np.empty(n, dtype=np.int64)
    x = 1
    for j in range(n):
        sub[j] = x; x = x*g % p
    # coset reps γ^i
    reps = np.empty(m, dtype=np.int64)
    x = 1
    for i in range(m):
        reps[i] = x; x = x*gam % p
    # η_i = Σ_j e_p(reps[i]*sub[j])  — vectorized in blocks
    eta = np.empty(m, dtype=np.complex128)
    B = 4096
    tw = np.exp(2j*np.pi/p)
    for lo in range(0, m, B):
        r = reps[lo:lo+B, None]
        prod = (r * sub[None, :]) % p
        eta[lo:lo+B] = np.exp(2j*np.pi*prod/p).sum(axis=1)
    return eta, m

def main():
    cells = [(32, 1048609), (32, 1049057), (64, 16778497)]
    rng = np.random.default_rng(466)
    for n, p in cells:
        if not isprime(p) or (p-1) % n:
            print(f"SKIP ({n},{p})"); continue
        eta, m = eta_field(n, p)
        M = np.abs(eta).max()
        print(f"cell (n={n}, p={p}, m={m}): M = max|eta| = {M:.3f}, "
              f"M/sqrt(n) = {M/np.sqrt(n):.3f}, sqrt(2 ln m) = {np.sqrt(2*np.log(m)):.3f}",
              flush=True)
        # shift-resolved increments: Δ_s(b) = η_{b·γ^s} − η_b  (index shift by s mod m)
        # scan all shifts s in a stratified sample + all "smooth" shifts
        smooth = sorted(set([1,2,3,4,6,8,12,16,24,32,48,64,m//2, m//4, m//8, m//3 if m%3==0 else 1]))
        rand = sorted(rng.choice(np.arange(5, m-5), size=48, replace=False).tolist())
        worst = []
        stats = []
        for s in sorted(set(smooth + rand)):
            d = np.roll(eta, -s) - eta
            sig = d.std() / np.sqrt(2)  # per-component std (complex)
            mx = np.abs(d).max()
            # Gaussian EVT prediction for max of m complex Gaussians (Rayleigh maxima):
            pred = sig*np.sqrt(2)*np.sqrt(np.log(m))
            kurt = (np.abs(d)**4).mean() / ((np.abs(d)**2).mean()**2)  # 2 for complex Gaussian
            stats.append((s, sig, mx/pred, kurt))
            worst.append((abs(kurt-2.0), mx/pred, s, sig, kurt))
        ratios = np.array([x[2] for x in stats]); kurts = np.array([x[3] for x in stats])
        print(f"  shifts scanned = {len(stats)}; max/EVTpred: min={ratios.min():.3f} "
              f"med={np.median(ratios):.3f} max={ratios.max():.3f}; "
              f"kurtosis(|D|²-normalized, Gaussian=2): min={kurts.min():.4f} "
              f"med={np.median(kurts):.4f} max={kurts.max():.4f}", flush=True)
        worst.sort(reverse=True)
        for w in worst[:5]:
            print(f"   anomaly-ranked shift s={w[2]}: sigma={w[3]:.3f} "
                  f"max/pred={w[1]:.3f} kurt={w[4]:.4f}", flush=True)
    print("READ: kurt ≈ 2 and max/pred in [0.9, 1.25] across ALL shift classes (incl. "
          "smooth/structured s) = increment field is Euclidean-complete, cocycle candidate "
          "DEAD. Any shift with kurt far from 2 or max/pred outlier = first non-|eta| "
          "signal; investigate its arithmetic (s vs subgroup/index structure).", flush=True)

if __name__ == "__main__":
    main()

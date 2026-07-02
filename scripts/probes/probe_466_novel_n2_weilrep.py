#!/usr/bin/env python3
"""
probe_466_novel_n2_weilrep.py -- N2-weil-rep lane sanity probe (#466 novel-math round).

Verifies the EXACT identities in the Weil-representation (oscillator / cat-map) chain
for eta_b = sum_{x in mu_n} e_p(b x), mu_n = order-n subgroup of F_p^x, m = (p-1)/n:

  (I1)  annihilator / Gauss decomposition (= the split-torus matrix-coefficient identity):
        eta_b = (1/m) * ( -1 + sum_{1 != chi in Ann(mu_n)} conj(chi)(b) * tau(chi) ),
        tau(chi) = sum_{x != 0} chi(x) e_p(x). Ann(mu_n) = {chi_k : n | k} (m characters).
  (I2)  exact purity: |tau(chi)| = sqrt(p) for every nontrivial chi (Gauss; the
        Gurevich-Hadani weight bound is EXACT and elementary in the split case).
  (I3)  dual identity (self-duality): for eps_chi = tau(chi)/sqrt(p),
        sum_{1 != chi in Ann} conj(chi)(b) eps_chi = (m*eta_b + 1)/sqrt(p);
        hence CORE <=> max_b |sum eps-walk| <= C*sqrt(m log m) (exchange-rate check).
  (I4)  m-th power complete-sum lift: mu_n = (F_p^x)^m and
        eta_b = (1/m) * ( S_m(b) - 1 ),  S_m(b) = sum_{y in F_p} e_p(b y^m)
        (the degree-m Weil-vacuous presentation).
  (C)   prize-point constants: purity overshoot sqrt(p)/target at n=2^30
        (diagonal p ~ n^4 and prize q ~ n*2^128).

All checks are numpy-FFT exact-to-float; residuals reported.  Light: <10s.
"""
import numpy as np

def primitive_root(p):
    fac = []
    t = p - 1
    d = 2
    while d * d <= t:
        if t % d == 0:
            fac.append(d)
            while t % d == 0:
                t //= d
        d += 1
    if t > 1:
        fac.append(t)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise RuntimeError

def run(n, p):
    assert (p - 1) % n == 0
    m = (p - 1) // n
    g = primitive_root(p)
    # discrete-log table: dlog[g^a mod p] = a
    dlog = np.zeros(p, dtype=np.int64)
    x = 1
    for a in range(p - 1):
        dlog[x] = a
        x = (x * g) % p
    # eta_b for all b via additive-side direct sum (n small)
    mu = [pow(g, j * m, p) for j in range(n)]
    b_arr = np.arange(p)
    eta = np.zeros(p, dtype=np.complex128)
    for u in mu:
        eta += np.exp(2j * np.pi * ((b_arr * u) % p) / p)
    M = np.max(np.abs(eta[1:]))
    # multiplicative-side: vals[a] = e_p(g^a); tau(chi_k) = sum_a e((-?) ) --
    # chi_k(g^a) = e(k a/(p-1)); tau(chi_k) = sum_a chi_k(g^a) e_p(g^a)
    powers = np.empty(p - 1, dtype=np.int64)
    x = 1
    for a in range(p - 1):
        powers[a] = x
        x = (x * g) % p
    vals = np.exp(2j * np.pi * powers / p)
    # tau_k = sum_a vals[a] * e(+ka/(p-1))  = (p-1)-point inverse-style DFT
    tau = np.fft.ifft(vals) * (p - 1)  # ifft gives (1/(p-1)) sum vals[a] e(+2pi i ka/(p-1))
    # (I2) exact purity for nontrivial chi in Ann
    ks = [n * t for t in range(1, m)]
    purity_err = max(abs(abs(tau[k]) - np.sqrt(p)) for k in ks) if ks else 0.0
    # (I1) reconstruct eta_b from the m-1 nontrivial annihilator Gauss sums
    #      conj(chi_k)(b) = e(-k*dlog[b]/(p-1))
    recon_err = 0.0
    rng = np.random.default_rng(466)
    test_b = rng.integers(1, p, size=min(64, p - 1))
    for b in test_b:
        a = dlog[b]
        s = -1.0 + 0j
        for k in ks:
            s += np.exp(-2j * np.pi * k * a / (p - 1)) * tau[k]
        recon_err = max(recon_err, abs(s / m - eta[b]))
    # (I3) dual identity + exchange rate
    dual_max = 0.0
    for b in range(1, p):
        pass  # dual sum = (m*eta_b+1)/sqrt(p) by (I1); verify on samples, use closed form
    dual_err = 0.0
    for b in test_b:
        a = dlog[b]
        s = sum(np.exp(-2j * np.pi * k * a / (p - 1)) * tau[k] / np.sqrt(p) for k in ks)
        dual_err = max(dual_err, abs(s - (m * eta[b] + 1) / np.sqrt(p)))
    dual_max = np.max(np.abs(m * eta[1:] + 1)) / np.sqrt(p)
    # (I4) m-th power lift on samples
    lift_err = 0.0
    y = np.arange(p, dtype=np.int64)
    ym = np.array([pow(int(t), m, p) for t in range(p)], dtype=np.int64)
    for b in test_b[:8]:
        Sm = np.exp(2j * np.pi * ((b * ym) % p) / p).sum()
        lift_err = max(lift_err, abs((Sm - 1) / m - eta[b]))
    L = np.log(p / n)
    C = M / np.sqrt(n * L)
    C_dual = dual_max / np.sqrt(m * np.log(m)) if m > 1 else float('nan')
    print(f"n={n:5d} p={p:7d} m={m:5d} | M={M:9.4f} C={C:6.3f} | "
          f"purity_err={purity_err:.2e} recon_err={recon_err:.2e} "
          f"dual_err={dual_err:.2e} lift_err={lift_err:.2e} | "
          f"dual_max={dual_max:9.3f} C_dual={C_dual:6.3f} "
          f"(sqrt(m ln m)={np.sqrt(m*np.log(m)) if m>1 else 0:8.2f})")

print("== N2-weil-rep exact-identity probe ==")
for (n, p) in [(8, 41), (8, 4129), (16, 257), (16, 65537), (32, 12289)]:
    run(n, p)

print("\n== prize-point constants (symbolic) ==")
import math
n = 2**30
for tag, logq, logm in [("analytic diagonal p~n^4", 120.0, 90.0),
                        ("prize q~n*2^128      ", 158.0, 128.0)]:
    Lm = logm * math.log(2)
    target = math.sqrt(n * Lm)
    sqrtp = 2.0 ** (logq / 2)
    print(f"{tag}: sqrt(p)=2^{logq/2:.1f}  target C*sqrt(n ln(p/n))=2^{math.log2(target):.2f}"
          f"  purity overshoot = 2^{logq/2 - math.log2(target):.2f}")

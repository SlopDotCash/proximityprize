#!/usr/bin/env python3
"""R19 DEPLETED task (c): the chi-family fourth moment WITHOUT Holder.

Objects: characters chi with chi^m = chi0, chi != chi0 (m-1 of them);
T_chi(t) = sum_{x in mu_n} conj(chi(t-x)); g(chi) Gauss sum.
Master: m*I_H(s0 notin D) = -n + A(s0), A = sum_chi g(chi) T_chi(s0).

Question: expand sum_t |A|^4 = sum_{quad} g1 g2 conj(g3 g4) M(quad),
M(quad) = sum_t T1 T2 conj(T3) conj(T4).
 - PAIRED quadruples ({chi3,chi4}={chi1,chi2}): M = sum_t |T1|^2 |T2|^2 (real >= 0).
 - OFF-PAIRED: how big is |M|? Weil predicts ~ n^4 sqrt(p) if no degenerate mass;
   the danger is hidden n^2 p mass (would kill the K=O(1) route).
Also directly measure holder-loss = sum_t|A|^4 / [(m-1)^2 q^2 * Cw n^2 q] scaling.
"""
import numpy as np
from sympy import isprime, primitive_root

def find_prime(target, mod):
    p = target + ((1 - target) % mod)
    while not isprime(p): p += mod
    return p

def run(n, beta, m):
    target = int(round(n**beta))
    p = find_prime(target, n*m)
    g = primitive_root(p)
    # discrete log table
    dlog = np.zeros(p, dtype=np.int64); x = 1
    for k in range(p-1):
        dlog[x] = k; x = x*g % p
    h = pow(g, (p-1)//n, p)
    mun = []; x = 1
    for _ in range(n): mun.append(x); x = x*h % p
    # characters chi_j (j=1..m-1): chi_j(x) = e(2pi i j dlog(x)/m) on x!=0, 0 at 0
    om = np.exp(2j*np.pi/m)
    chivals = []  # chi_j as array over F_p
    for j in range(1, m):
        arr = om**((j*dlog) % m)
        arr[0] = 0.0
        chivals.append(arr)
    ind = np.zeros(p); ind[mun] = 1.0
    Find = np.fft.fft(ind)
    # T_chi(t) = sum_x conj(chi(t-x)) 1_mun(x) = (conj(chi) * ind)(t) circular conv
    Ts = []
    gs = []
    psi = np.exp(2j*np.pi*np.arange(p)/p)
    for j, cv in enumerate(chivals):
        cc = np.conj(cv)
        T = np.fft.ifft(np.fft.fft(cc)*Find)
        Ts.append(T)
        gs.append(np.sum(cv*psi))  # g(chi) = sum_x chi(x) e(x/p)
    Ts = np.array(Ts); gs = np.array(gs)
    M4 = np.array([float(np.sum(np.abs(T)**4)) for T in Ts])
    Cw_meas = M4.max()/(n*n*p)
    # full A fourth moment
    A = np.tensordot(gs, Ts, axes=1)
    S4A = float(np.sum(np.abs(A)**4))
    # paired mass (multiset-paired quadruples, with gauss factors |g|^2=p... careful:
    # paired quads have g1 g2 conj(g3 g4) = |g1|^2 |g2|^2 = p^2 (if chi1,chi2 both nonreal
    # primitive? |g|^2 = p for chi nontrivial since p prime, chi primitive mod p)
    paired = 0.0
    mm = m-1
    cross = np.zeros((mm, mm))
    for a in range(mm):
        for b in range(mm):
            cross[a, b] = float(np.sum(np.abs(Ts[a])**2*np.abs(Ts[b])**2))
    # count of paired quads: (chi1,chi2) ordered, {chi3,chi4}={chi1,chi2}: 2 if distinct,1 if equal
    pairedmass = 0.0
    for a in range(mm):
        for b in range(mm):
            mult = 2 if a != b else 1
            pairedmass += mult * p*p * cross[a, b]
    # off-paired max |M| and total off mass with |g|^4=p^2 weights
    offmax = 0.0; offsum = 0.0; ncheck = 0
    rng = np.random.default_rng(0)
    quads = []
    if mm >= 2:
        # enumerate all quads if small, else sample
        import itertools
        allq = list(itertools.product(range(mm), repeat=4))
        offq = [qd for qd in allq
                if sorted(qd[:2]) != sorted(qd[2:])]
        if len(offq) > 400:
            idx = rng.choice(len(offq), 400, replace=False)
            offq_s = [offq[i] for i in idx]
        else:
            offq_s = offq
        for (a, b, c, d) in offq_s:
            M = np.sum(Ts[a]*Ts[b]*np.conj(Ts[c])*np.conj(Ts[d]))
            am = abs(M)
            offmax = max(offmax, am)
            offsum += am
            ncheck += 1
        offsum *= len(offq)/max(ncheck, 1)   # extrapolate total
    print(f"n={n} beta={beta} m={m} p={p}: Cw_meas={Cw_meas:.3f} "
          f"S4A={S4A:.3e} paired={pairedmass:.3e} paired/S4A={pairedmass/S4A:.3f} "
          f"holder_bound/(S4A)={(mm**3*p*p*np.sum(M4))/S4A:.1f}")
    if mm >= 2:
        print(f"   offpaired: max|M|/(n^4 sqrt(p))={offmax/(n**4*np.sqrt(p)):.3f} "
              f"max|M|/(n^2 p)={offmax/(n*n*p):.4f} "
              f"est total off mass * p^2 / S4A={offsum*p*p/S4A:.3f}")

for (n, beta, m) in ((16, 4.0, 2), (16, 4.0, 4), (16, 4.0, 8),
                     (32, 3.5, 4), (32, 3.5, 8), (32, 4.0, 4), (32, 4.0, 8),
                     (16, 3.5, 16), (16, 4.0, 16)):
    run(n, beta, m)

#!/usr/bin/env python3
"""R17 WEIL lane probe: r=2 rung of the incidence tower via completion + Weil.

Chain (m = deg = index of H):
  I_H(s0 not in mu_n) = (-n + sum_{chi != chi0, chi^m=chi0} g(chi) T_chi(s0)) / m
  T_chi(t) = sum_{x in mu_n} chibar(t - x)
  Second moment: sum_t |T_chi|^2 = n(p - n)          [EXACT, Jacobi 2-pt orthogonality]
  Fourth moment: sum_t |T_chi|^4 <= Dm*p + 3 n^4 sqrt(p),
     Dm = 2n^2 - n (m>2) or 3n^2 - 2n (m=2)          [Weil for quartic rational twists]
  => for p >= n^4: sum_t |T_chi|^4 <= (Dm/n^2 + 3) n^2 p <= 6 n^2 p
  => S2^D <= 8/m^4 ( q n^4 + (m-1)^4 p^2 sum_chi 4thmom )
  => S2^D <= K(m) q Sigma^2 with K(m) = 200 (m-1)^4 / m^2   (p >= max(n^4, 16 n^2 m^2))
"""
import numpy as np
from sympy import isprime

def cell(n, m, p, do_fourth=True):
    print(f"\n=== n={n} m=deg={m} p={p}  (p/n^4 = {p/n**4:.3g}) ===")
    assert isprime(p) and (p-1) % (n*m) == 0
    # generator
    def order(g):
        o, x = 1, g
        while x != 1:
            x = x*g % p; o += 1
        return o
    g = 2
    while order(g) != p-1:
        g += 1
    # mu_n and H (index m)
    mun = sorted({pow(g, (p-1)//n * k, p) for k in range(n)})
    H = np.zeros(p, dtype=bool)
    for k in range(0, p-1, m):
        H[pow(g, k, p)] = True
    assert all(H[x] for x in mun), "mu_n not in H"
    # eta via FFT: eta_b = sum_x e(bx/p)
    ind = np.zeros(p); ind[mun] = 1
    eta = np.fft.fft(ind)  # eta[b] = sum_x ind[x] e^{-2pi i bx/p}  (a character choice; fine)
    # I_H(s0) = sum_{b in H} conj(eta_b) psi(b s0); with psi(u)=e^{-2pi i u/p}: FFT of w
    w = np.conj(eta) * H
    I = np.fft.fft(w)
    # Sigma, S2^D, D = {0} u mu_n
    Sigma = np.sum(np.abs(eta[H])**2)
    mask = np.ones(p, dtype=bool); mask[0] = False; mask[mun] = False
    S2D = np.sum(np.abs(I[mask])**4)
    q = float(p)
    print(f"  Sigma = {Sigma:.6g}  (nq/m = {n*q/m:.6g}, ratio {Sigma/(n*q/m):.4f})")
    print(f"  S2D/(2 q Sigma^2) = {S2D/(2*q*Sigma**2):.4f}   [StrongR2Rung const-2 ratio]")
    Km = 200*(m-1)**4/m**2
    print(f"  S2D/(q Sigma^2)   = {S2D/(q*Sigma**2):.4f}   vs claimed K(m) = {Km:.1f}")
    # characters chi with chi^m = chi0: chi_j(g^k) = e(jk m'/(p-1)) with j multiple of (p-1)/m
    # discrete log table
    dlog = np.zeros(p, dtype=np.int64); dlog[0] = -1
    x = 1
    for k in range(p-1):
        dlog[x] = k; x = x*g % p
    fourth_sum = 0.0
    id_ok, sm_ok = True, True
    Gsum = np.zeros(p, dtype=complex)
    for j in range(1, m):
        e = j*(p-1)//m
        chi = np.exp(2j*np.pi*e*dlog/(p-1)); chi[0] = 0
        # T_chi(t) = sum_x chibar(t-x)
        T = np.zeros(p, dtype=complex)
        for xv in mun:
            T += np.conj(chi[(np.arange(p)-xv) % p])
        # gauss sum with SAME psi as above: g(chi) = sum_b chi(b) e^{-2pi i b/p}
        gs = np.sum(chi*np.exp(-2j*np.pi*np.arange(p)/p))
        Gsum += gs*T
        m2 = np.sum(np.abs(T)**2)
        if abs(m2 - n*(p-n)) > 1e-4*n*p: sm_ok = False
        if do_fourth:
            m4 = np.sum(np.abs(T)**4)
            fourth_sum += m4
            Dm = 3*n*n-2*n if m == 2 else 2*n*n-n
            bound = Dm*p + 3*n**4*np.sqrt(p)
            print(f"  chi_{j}: 2nd mom / n(p-n) = {m2/(n*(p-n)):.6f};"
                  f" 4th mom = {m4:.4g}, /n^2p = {m4/(n*n*p):.3f},"
                  f" / (Dm p + 3n^4 sqrt p) = {m4/bound:.4f}")
    print(f"  exact 2nd moment identity sum_t|T|^2 = n(p-n): {'OK' if sm_ok else 'FAIL'}")
    # decomposition identity check off mu_n: m*I = -n + Gsum
    off = mask.copy()
    err = np.max(np.abs(m*I[off] - (-n + Gsum[off])))
    print(f"  decomposition identity max err (off-diag): {err:.2e}")
    if do_fourth:
        rhs = 8/m**4*(q*n**4 + (m-1)**4*p**2*fourth_sum)
        print(f"  chain check: S2D <= 8/m^4(qn^4 + (m-1)^4 p^2 * sum_chi m4): "
              f"ratio = {S2D/rhs:.4g} {'OK' if S2D <= rhs else 'FAIL'}")

# sanity small cell (identities; regime p >= n^4 NOT satisfied -> fourth moment may exceed 6n^2p)
cell(8, 2, 97)
# regime-valid cells p >= n^4
for p in range(4096, 6000):
    if isprime(p) and (p-1) % 16 == 0:
        cell(8, 2, p); break
for p in range(4096, 9000):
    if isprime(p) and (p-1) % 32 == 0:
        cell(8, 4, p); break
cell(16, 2, 65537)
# the R16 refuted cell (p << n^4): show regime violation shows up in the 4th moment
cell(64, 8, 7681)

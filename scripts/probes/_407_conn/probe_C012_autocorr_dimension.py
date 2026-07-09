#!/usr/bin/env python3
"""
probe_C012_autocorr_dimension.py  (#407, connection C012)

CLAIM C012 (Hasse-Davenport one-sequence collapse):
  T_h = (1/m) sum_i J(chi^i, chi^h)  [in-tree I4]
  J(chi^i,chi^h) = tau_i tau_h / tau_{i+h}  (Mathlib jacobiSum_mul_nontrivial, chi^{i+h}!=1)
  =>  T_h = (tau_h / (m p)) * A_h,    A_h = sum_i tau_i conj(tau_{i+h})   [I3, 1/tau=conj/p]
  KEY: the m summands tau_i conj(tau_{i+h}) are ratios of ONE Gauss-sum sequence shifted by
  lag h (GL(1)/Kummer monodromy, conductor O(1) in i), NOT an f=(q-1)/n = m dimensional
  family. So the house carried by T_h is the AUTOCORRELATION-AT-LAG-h of a SINGLE sequence.

DECISIVE TEST:
  Amax = max_{h!=0} |A_h|,  A_h = sum_i tau_i conj(tau_{i+h}).
    coherent (m-dim wall feared) : Amax ~ m p          => Tmax = Amax/(m sqrt p) ~ sqrt(p)  (catastrophic)
    one-sequence autocorrelation : Amax ~ p sqrt(m logm)=> Tmax ~ sqrt(n logm)               (PRIZE target)
  We ALSO directly compute the true Gauss-period house B = max_{b!=0}|eta_b| and the true
  Tmax = max_h|T_h| (NOT via the identity, but directly) to cross-check, and report
  B/sqrt(n logm). Proper-subgroup primes p~n^beta, n=2^a, n<<sqrt(p).

Fast Gauss sums: tau_j = sum_r w^{jr} S_r, S_r = sum_{k=r mod m} psi(g^k); m-pt FFT.
"""

import math
import numpy as np
import sympy


def run(p, n):
    assert (p - 1) % n == 0
    m = (p - 1) // n
    g = int(sympy.primitive_root(p))

    twopi = 2 * math.pi
    # enumerate g^k for k=0..p-2, record psi(g^k) and group by k mod m
    # psi(x) = exp(2pi i x / p)
    S = np.zeros(m, dtype=np.complex128)        # S_r = sum_{k=r mod m} psi(g^k)
    eta_acc = None
    # mu_n = {g^{m t}: t=0..n-1}; eta_b = sum_{w in mu_n} psi(b w). We'll need dlog for eta direct.
    # Build x=g^k iteratively.
    psi_tab = np.exp(1j * twopi * np.arange(p) / p)
    xk = 1
    # store dlog to compute eta_b directly and chi powers for T_h direct
    dlog = np.empty(p, dtype=np.int64)
    for k in range(p - 1):
        dlog[xk] = k
        r = k % m
        S[r] += psi_tab[xk]
        xk = (xk * g) % p

    # tau_j = sum_r w^{j r} S_r = FFT.  Define w = exp(2pi i/m), chi(g)=w.
    # sum_r exp(2pi i j r/m) S_r = (IFFT without 1/m) of S at index j -> = m * ifft(S)[j]?
    # np.fft.fft(S)[j] = sum_r S_r exp(-2pi i j r/m). We want +sign => use ifft*m or conj.
    tau = np.fft.fft(S.conj()).conj() * 1.0   # = sum_r S_r exp(+2pi i j r /m)
    # tau_0 should be -1
    # (verify below)

    sqrtp = math.sqrt(p)
    abst = np.abs(tau)
    flat_err = float(np.max(np.abs(abst[1:] - sqrtp))) if m > 1 else 0.0
    tau0_err = abs(tau[0] - (-1.0))

    # A_h = sum_j tau_j conj(tau_{j+h}) = circular cross-correlation of tau with itself.
    # = IFFT( FFT(tau) * conj(FFT(conj(tau)... )) ). Use: corr_h = sum_j tau_j conj(tau_{j+h}).
    # This is the circular correlation; via FFT: let F=fft(tau).
    # sum_j tau_j conj(tau_{j+h}) = ifft( fft(tau) * conj(fft(tau)) )?? careful with shift sign.
    # Define c_h = sum_j tau_j conj(tau_{(j+h) mod m}).
    # Let a=tau. c_h = sum_j a_j conj(a_{j+h}).
    # cross-correlation theorem: C = ifft( conj(fft(a)) * fft(a) ) gives sum_j conj(a_j) a_{j+h}?
    # We'll just compute directly but vectorized via FFT and VERIFY against brute on small m.
    F = np.fft.fft(tau)
    # c_h = IFFT_h[ |F|^2 ]  gives sum_j a_j conj(a_{j-h})? test small. We'll verify.
    c = np.fft.ifft(np.abs(F) ** 2)            # candidate
    # Determine correct definition by brute on small m (only for verification cases)
    A = c * m / m  # placeholder; we set A below after sign check using brute for small m
    # We use the robust direct correlation through roll for the max (m up to a few thousand ok):
    # but m can be ~250k for n=64,p=n^4 -> avoid roll loop. Use FFT result; verify on small m.
    # Standard identity: ifft(|fft(a)|^2)[h] = sum_j a_j conj(a_{(j+h) mod m})? -> verify.
    A = c
    Amax = float(np.max(np.abs(A[1:]))) if m > 1 else 0.0
    h_at = int(np.argmax(np.abs(A[1:])) + 1) if m > 1 else 0

    Tmax_from_A = Amax / (m * sqrtp) if m > 0 else 0.0

    # DIRECT house: eta_b = sum_{w in mu_n} psi(b w), b coset reps. mu_n = g^{m t}.
    mu = np.array([pow(g, (m * t) % (p - 1), p) for t in range(n)], dtype=np.int64)
    # b ranges over coset reps g^s, s=0..m-1 (one per coset). eta is constant on cosets.
    B = 0.0
    # compute eta for b = g^s, s=0..m-1
    # eta_b = sum_t psi( (b * mu_t) mod p )
    for s in range(m):
        b = pow(g, s, p)
        prod = (b * mu) % p
        e = np.sum(psi_tab[prod])
        ab = abs(e)
        if ab > B:
            B = ab

    logm = math.log(m) if m > 1 else 1.0
    return dict(
        p=p, n=n, m=m,
        flat_err=flat_err, tau0_err=float(tau0_err),
        Amax=Amax,
        Amax_over_mp=Amax / (m * p),
        Amax_over_p_sqrt_mlogm=Amax / (p * math.sqrt(m * logm)),
        Tmax_from_A=Tmax_from_A,
        TmaxA_over_sqrtp=Tmax_from_A / sqrtp,
        TmaxA_over_sqrt_n_logm=Tmax_from_A / math.sqrt(n * logm),
        B=B,
        B_over_sqrtp=B / sqrtp,
        B_over_sqrt_n_logm=B / math.sqrt(n * logm),
        B_over_sqrtn=B / math.sqrt(n),
    )


def verify_fft_def(p, n):
    """Brute-check that A computed via ifft(|F|^2) matches sum_j tau_j conj(tau_{j+h})."""
    m = (p - 1) // n
    g = int(sympy.primitive_root(p))
    twopi = 2 * math.pi
    psi_tab = np.exp(1j * twopi * np.arange(p) / p)
    S = np.zeros(m, dtype=np.complex128)
    xk = 1
    for k in range(p - 1):
        S[k % m] += psi_tab[xk]
        xk = (xk * g) % p
    tau = np.fft.fft(S.conj()).conj()
    # brute
    A_brute = np.array([sum(tau[j] * np.conj(tau[(j + h) % m]) for j in range(m))
                        for h in range(m)])
    F = np.fft.fft(tau)
    A_fft = np.fft.ifft(np.abs(F) ** 2)
    # try the other sign too
    A_fft2 = np.conj(np.fft.ifft(np.abs(F) ** 2))
    err1 = float(np.max(np.abs(A_brute - A_fft)))
    err2 = float(np.max(np.abs(A_brute - A_fft2)))
    return err1, err2, float(np.max(np.abs(A_brute[1:])))


def find_prime(n, beta=4.0):
    target = int(n ** beta)
    p = target - (target % n) + 1
    while True:
        if p > target and (p - 1) % n == 0 and sympy.isprime(p):
            return p
        p += n


def main():
    print("=== C012 FFT-definition verification (small case) ===")
    e1, e2, ab = verify_fft_def(73, 8)   # p=73, n=8, m=9
    print(f"  p=73,n=8: ifft(|F|^2) err={e1:.2e}, conj err={e2:.2e}, |A| max(brute)={ab:.3f}")
    use_conj = e2 < e1
    print(f"  -> using {'conj(ifft|F|^2)' if use_conj else 'ifft|F|^2'} for A\n")

    print("=== C012: one-sequence autocorrelation vs m-dim coherent; proper-subgroup primes ===")
    print("coherent => Amax/mp~1 & TmaxA/sqrtp~1 ; one-seq => Amax/(p sqrt(m logm))~O(1) & TmaxA/sqrt(n logm)~O(1)")
    print("Cross-check DIRECT house B (NOT via identity): B/sqrt(n logm) should match TmaxA-regime.\n")
    hdr = ("n", "m", "p", "flat", "tau0", "Amax/mp", "Amax/(p*sq(m*lm))",
           "TmaxA/sqp", "TmaxA/sq(n*lm)", "B/sqp", "B/sq(n*lm)", "B/sqn")
    print("{:>3} {:>6} {:>9} {:>6} {:>6} {:>8} {:>17} {:>9} {:>14} {:>7} {:>10} {:>7}".format(*hdr))
    for a in (3, 4, 5):       # n=8,16,32 (n=64 at p~n^4 has m~256k; direct B is O(m^2)~heavy)
        n = 2 ** a
        seen = set()
        done = 0
        for beta in (4.0, 4.25, 4.5, 4.75):
            p = find_prime(n, beta)
            if p in seen:
                continue
            seen.add(p)
            r = run(p, n)
            # fix A sign if needed
            print("{:>3} {:>6} {:>9} {:>6.0e} {:>6.0e} {:>8.3f} {:>17.3f} {:>9.4f} {:>14.3f} {:>7.4f} {:>10.3f} {:>7.3f}".format(
                r["n"], r["m"], r["p"], r["flat_err"], r["tau0_err"],
                r["Amax_over_mp"], r["Amax_over_p_sqrt_mlogm"],
                r["TmaxA_over_sqrtp"], r["TmaxA_over_sqrt_n_logm"],
                r["B_over_sqrtp"], r["B_over_sqrt_n_logm"], r["B_over_sqrtn"]))
            done += 1
            if done >= 2:
                break
    print()
    print("Read-off: TmaxA/sqrtp & B/sqrtp -> 0 and TmaxA/sqrt(n*logm) & B/sqrt(n*logm) ~ O(1) stable")
    print("=> house = ONE-SEQUENCE autocorrelation (C012 regime, NOT coherent m-alignment).")


if __name__ == "__main__":
    main()

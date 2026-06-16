#!/usr/bin/env python3
"""
probe_C012_dimension_crux.py  (#407, C012) -- THE crux test.

C012 says: T_h = (1/m) sum_i J(chi^i, chi^h) is the autocorrelation-at-lag-h of ONE
Gauss-sum sequence (tau_i), so its cancellation is governed by a SINGLE GL(1)/Kummer
Sato-Tate (conductor O(1) in i), NOT an m-dimensional family -> the largesieve dim wall is
mis-applied.

But the SHARP question is whether the >sqrt-m cancellation needed in
   S_h := sum_{i=0}^{m-1} J(chi^i,chi^h)/sqrt(p)   (T_h = sqrt(p) S_h / m, |J/sqrt p| = 1 typ.)
is actually delivered by one-sequence (1-dim) structure, or whether the i-summands behave
as m ~independent unit phases (so cancellation is the SAME m-term random-sum / BGK problem).

TESTS (exact, proper-subgroup primes p~n^4):
 (1) Phase decorrelation of the i-sequence  u_i := J(chi^i,chi^h)/|J| (unit phases):
     compute its OWN lag-1 autocorrelation  r1 = (1/m)|sum_i u_i conj(u_{i+1})|.
     If u_i were a 1-dim (rank-1, geometric) sequence u_i = z * w^{c i}, then |r1| = 1
     (perfectly coherent shift). If u_i is random-like (m effectively-independent phases),
     |r1| ~ 1/sqrt(m) -> 0.  This DIRECTLY measures the effective dimension of the i-sequence.
 (2) Compare max_h |S_h| growth:  1-dim/coherent would give |S_h| ~ m (no cancellation in
     the average -> T_h ~ sqrt(p), catastrophic, ALREADY refuted). Random-like gives
     |S_h| ~ sqrt(m logm) -> T_h ~ sqrt(n logm). We report max_h|S_h|/sqrt(m logm).
 (3) "Effective rank": singular spectrum of the i x h Jacobi-phase matrix M[i,h]=u_{i,h}.
     A genuine GL(1) one-parameter family -> low numerical rank. m independent phases ->
     full rank (flat singular values ~ sqrt(stuff)). Report participation ratio PR =
     (sum s^2)^2 / sum s^4  (1 = rank-1, m = full uniform rank).
"""

import math
import numpy as np
import sympy


def jacobi_phase_matrix(p, n):
    """Return tau (len m) and the unit-phase Jacobi matrix U[i,h]=J(chi^i,chi^h)/|...|, plus S_h."""
    m = (p - 1) // n
    g = int(sympy.primitive_root(p))
    twopi = 2 * math.pi
    psi_tab = np.exp(1j * twopi * np.arange(p) / p)
    # tau via S_r grouping
    Sr = np.zeros(m, dtype=np.complex128)
    xk = 1
    for k in range(p - 1):
        Sr[k % m] += psi_tab[xk]
        xk = (xk * g) % p
    tau = np.fft.fft(Sr.conj()).conj()
    sqrtp = math.sqrt(p)
    # J(chi^i,chi^h) = tau_i tau_h / tau_{i+h}  when chi^{i+h} != 1 (i.e. (i+h) mod m != 0)
    # Build M[i,h] = J(chi^i,chi^h) for i,h in 0..m-1 (skip where i+h ==0 mod m or i==0 or h==0).
    return tau, sqrtp, m, g


def run(p, n):
    tau, sqrtp, m, g = jacobi_phase_matrix(p, n)
    # S_h = sum_i J(chi^i,chi^h)/sqrt(p), restricted to nontrivial terms; T_h = sqrt(p)*S_h/m...
    # but I4 sums ALL i incl. boundary (J defined directly). Use the GAUSS-QUOTIENT form on the
    # nontrivial part and add the in-tree exact T_h check via the tangent identity-equivalent.
    # We compute J(chi^i,chi^h) = tau_i*tau_h/tau_{i+h} for (i+h)%m!=0 (chi^{i+h} nontriv),
    # and for i+h==0 mod m use J = -chi^h(-1) (standard) -- but those are O(m) terms of size O(1),
    # negligible vs the main sqrt(p)-scale; we include the dominant nontrivial terms.
    logm = math.log(m)
    # i-sequence unit phases for each h: u_i(h) = (tau_i / tau_{i+h}) (unit modulus since |tau|=sqrtp)
    # J/sqrt(p) = (tau_i tau_h / tau_{i+h})/sqrt p = (tau_h/sqrt p) * (tau_i/tau_{i+h}).
    # tau_h/sqrt p is a fixed unit phase per h; the i-DEPENDENCE is entirely tau_i/tau_{i+h}.
    idx = np.arange(m)
    tau_arr = tau
    # Ratio matrix R[i,h] = tau_i / tau_{(i+h) mod m}, unit modulus. Built column by column,
    # but maxS and r1 are accumulated WITHOUT storing the full matrix (memory-light).
    # S_h = (tau_h/sqrt p) * sum_i R[i,h].
    maxS = 0.0
    r1_list = []
    do_PR = (m <= 6000)
    cols = [] if do_PR else None
    inv_tau = 1.0 / tau_arr
    for h in range(1, m):
        ratio = tau_arr * inv_tau[(idx + h) % m]      # tau_i / tau_{i+h}, unit modulus
        Sh = (tau_arr[h] / sqrtp) * np.sum(ratio)
        aS = abs(Sh)
        if aS > maxS:
            maxS = aS
        r1 = abs(np.sum(ratio * np.conj(np.roll(ratio, -1)))) / m
        r1_list.append(r1)
        if do_PR:
            cols.append(ratio)
    if do_PR:
        R = np.stack(cols, axis=1)
        fro2 = float(np.sum(np.abs(R) ** 2))
        G = R.conj().T @ R
        fro4 = float(np.sum(np.abs(G) ** 2))
        PR = (fro2 ** 2) / fro4 if fro4 > 0 else 0.0
    else:
        PR = float("nan")
    mean_r1 = float(np.mean(r1_list))
    max_r1 = float(np.max(r1_list))
    return dict(
        p=p, n=n, m=m,
        maxS=maxS,
        maxS_over_sqrt_mlogm=maxS / math.sqrt(m * logm),
        maxS_over_m=maxS / m,                      # coherent => ~1
        mean_r1=mean_r1, max_r1=max_r1,            # 1 => rank-1 coherent; 1/sqrt(m) => random-like
        one_over_sqrtm=1.0 / math.sqrt(m),
        PR=PR, PR_over_m=PR / m,                   # PR/m ~1 => full rank (m-dim) ; ~1/m => rank-1
    )


def find_prime(n, beta=4.0):
    target = int(n ** beta)
    p = target - (target % n) + 1
    while True:
        if p > target and (p - 1) % n == 0 and sympy.isprime(p):
            return p
        p += n


def main():
    print("=== C012 CRUX: effective dimension of the i-sequence in T_h = (1/m) sum_i J(chi^i,chi^h) ===")
    print("rank-1/coherent (GL(1) geometric)  : r1~1,  PR/m~1/m,  maxS/m~1  (=> T_h~sqrt p, refuted)")
    print("random-like (m-dim, BGK wall)      : r1~1/sqrt(m), PR/m~1, maxS/sqrt(m logm)~O(1)\n")
    hdr = ("n", "m", "p", "mean_r1", "1/sqrtm", "max_r1", "PR/m", "maxS/m", "maxS/sqrt(m logm)")
    print("{:>3} {:>6} {:>9} {:>9} {:>9} {:>8} {:>8} {:>8} {:>18}".format(*hdr))
    for a in (3, 4, 5):
        n = 2 ** a
        seen = set()
        done = 0
        for beta in (4.0, 4.25, 4.5):
            p = find_prime(n, beta)
            if p in seen:
                continue
            seen.add(p)
            if (p - 1) // n > 90000:    # cap m for the per-h loop runtime
                continue
            r = run(p, n)
            print("{:>3} {:>6} {:>9} {:>9.4f} {:>9.4f} {:>8.4f} {:>8.4f} {:>8.4f} {:>18.3f}".format(
                r["n"], r["m"], r["p"], r["mean_r1"], r["one_over_sqrtm"], r["max_r1"],
                r["PR_over_m"], r["maxS_over_m"], r["maxS_over_sqrt_mlogm"]))
            done += 1
            if done >= 2:
                break
    print()
    print("VERDICT KEY: if mean_r1 ~ 1/sqrt(m) and PR/m ~ O(1), the i-sequence is EFFECTIVELY")
    print("FULL-RANK (m independent phases) -> the GL(1) 'one-sequence conductor O(1)' collapse")
    print("does NOT reduce the cancellation problem; the m-dim/BGK wall is the right obstruction.")


if __name__ == "__main__":
    main()

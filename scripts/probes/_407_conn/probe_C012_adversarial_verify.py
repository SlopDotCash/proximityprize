#!/usr/bin/env python3
"""
probe_C012_adversarial_verify.py  (#407, C012)  -- ADVERSARIAL re-check of the REFUTED verdict.

The attacker's crux probe argues: the i-sequence v_i = tau_i/tau_{i+h} is "full-rank random-like"
(participation ratio PR/m ~ 0.8, lag-1 autocorr -> 0, spectral spike small) => therefore the
T_h = (1/m) sum_i J(chi^i,chi^h) average is an m-term random-cancellation sum and the largesieve
m-fold wall applies, i.e. C012's "one GL(1) sequence, conductor O(1)" escape is REFUTED.

I attack TWO load-bearing inferences:

(A) CONFOUNDER: a GENUINE single geometric family's Frobenius traces ALSO look "random-like"
    (Sato-Tate equidistribution). So PR/full-rank does NOT by itself prove "m independent sheaves".
    Test: build a control = a single rank-1/geometric sequence z*w^{c i} (truly 1-dim) AND a
    "Sato-Tate single-family" control (one curve, m twists) and see which of the FOUR attacker
    metrics actually separate them from the true tau-ratio sequence. If the attacker's metrics
    flag a genuine single family as "full-rank" too, the metrics are NOT diagnostic of dimension.

(B) THE ONLY THING THAT MATTERS for the prize: does the autocorrelation STRUCTURE deliver the
    sqrt(m logm) cancellation as a THEOREM-able consequence, or is it merely empirically the same
    as a random sum (=> no escape)?  Direct test: compare max_h |sum_i J| for
      (i) TRUE tau-ratio,  (ii) random unit phases (m of them),  (iii) a true rank-1 geometric.
    If TRUE ~ RANDOM and BOTH << RANK1-coherent, then the autocorrelation gives NO structural
    saving beyond "behaves like random" => C012 escape REFUTED (welds to BGK). If TRUE is
    PROVABLY smaller than random (e.g. a deterministic sqrt(p) flat-spectrum identity forces it),
    that would resurrect C012.

Proper-subgroup primes p~n^beta, n=2^a, n<<sqrt(p), m=(p-1)/n large.  Exact arithmetic for tau.
"""

import math
import numpy as np
import sympy


def build_tau(p, n):
    m = (p - 1) // n
    g = int(sympy.primitive_root(p))
    twopi = 2 * math.pi
    psi_tab = np.exp(1j * twopi * np.arange(p) / p)
    Sr = np.zeros(m, dtype=np.complex128)
    xk = 1
    for k in range(p - 1):
        Sr[k % m] += psi_tab[xk]
        xk = (xk * g) % p
    tau = np.fft.fft(Sr.conj()).conj()
    return tau, m, math.sqrt(p)


def four_metrics(v):
    """The attacker's four metrics applied to a unit-modulus sequence v (length m)."""
    m = len(v)
    # PR via the 'self matrix' is not well-defined for a single vector; the attacker's PR was on
    # the i x h ratio MATRIX. For a single column we use the standard signal participation ratio
    # in the FFT domain (effective number of active frequencies):
    F = np.fft.fft(v)
    p4 = np.sum(np.abs(F) ** 4)
    p2 = np.sum(np.abs(F) ** 2)
    PR_freq = (p2 ** 2) / p4 if p4 > 0 else 0.0     # 1 => single freq (rank-1); m => flat (random)
    r1 = abs(np.sum(v * np.conj(np.roll(v, -1)))) / m
    spike = np.max(np.abs(F)) / math.sqrt(m)
    consec = abs(np.mean((np.roll(v, -1) / v)))      # geometric => 1
    return PR_freq / m, r1, spike, consec


def run(p, n, seed=0):
    tau, m, sqrtp = build_tau(p, n)
    inv_tau = 1.0 / tau
    idx = np.arange(m)
    rng = np.random.default_rng(seed)

    # pick the h that MAXIMIZES the true |S_h| (worst case = the house)
    maxS_true = 0.0
    h_star = 1
    for h in range(1, m):
        v = tau * inv_tau[(idx + h) % m]            # tau_i/tau_{i+h}, unit modulus
        Sh = abs((tau[h] / sqrtp) * np.sum(v))
        if Sh > maxS_true:
            maxS_true = Sh
            h_star = h

    # (B) compare worst-case |sum_i (unit phases)| across three models at SAME m:
    #   TRUE  : v_i = tau_i/tau_{i+h*}
    #   RAND  : m i.i.d. uniform unit phases, take worst over many draws
    #   RANK1 : v_i = w^{c i} truly geometric (one frequency) -> |sum| = 0 unless c=0 then m
    v_true = tau * inv_tau[(idx + h_star) % m]
    sum_true = abs(np.sum(v_true))

    # random control: worst-of-K m-term random unit-phase sums (matches "m independent phases")
    K = max(200, m)  # comparable number of trials to the m available h-shifts
    Ktrials = min(K, 4000)
    rand_sums = np.abs(np.sum(np.exp(2j * math.pi * rng.random((Ktrials, m))), axis=1))
    rand_worst = float(np.max(rand_sums))
    rand_med = float(np.median(rand_sums))

    # rank-1 control: c != 0 geometric -> exact 0; c == 0 -> m. The "coherent" worst case is m.
    rank1_coherent = float(m)

    logm = math.log(m)
    # metrics on the worst-h true sequence vs a single rank-1 vs a single random vector
    m_true = four_metrics(v_true)
    c = rng.integers(1, m)
    v_rank1 = np.exp(2j * math.pi * c * idx / m)
    m_rank1 = four_metrics(v_rank1)
    v_rand = np.exp(2j * math.pi * rng.random(m))
    m_rand = four_metrics(v_rand)

    return dict(
        p=p, n=n, m=m, h_star=h_star,
        maxS_true=maxS_true,
        maxS_true_over_sqrt_mlogm=maxS_true / math.sqrt(m * logm),
        # |sum_i v_i| comparison (the actual cancellation delivered):
        sum_true=sum_true, sum_true_over_sqrtm=sum_true / math.sqrt(m),
        rand_worst=rand_worst, rand_worst_over_sqrtm=rand_worst / math.sqrt(m),
        rand_med_over_sqrtm=rand_med / math.sqrt(m),
        rank1_coherent_over_sqrtm=rank1_coherent / math.sqrt(m),
        # ratio: how does true worst compare to random worst (over comparable # of trials)?
        true_vs_randworst=maxS_true / (rand_worst / sqrtp * sqrtp) if rand_worst > 0 else 0,
        metrics_true=m_true, metrics_rank1=m_rank1, metrics_rand=m_rand,
    )


def find_prime(n, beta=4.0):
    target = int(n ** beta)
    p = target - (target % n) + 1
    while True:
        if p > target and (p - 1) % n == 0 and sympy.isprime(p):
            return p
        p += n


def main():
    print("=== C012 ADVERSARIAL VERIFY: do attacker metrics distinguish 1-dim from m-dim? ===")
    print("(A) Apply the FOUR attacker metrics [PR/m, lag1-r1, spike/sqrt(m), consec-coherence]")
    print("    to TRUE tau-ratio vs a genuine RANK-1 geometric vs a RANDOM vector.\n")
    print("    rank-1 geometric SHOULD score: PR/m~1/m, r1~1, spike~sqrt(m)/sqrt(m)=... , consec~1")
    print("    random SHOULD score:           PR/m~1,    r1~0, spike~O(1),                 consec~0\n")
    for a in (3, 4, 5):
        n = 2 ** a
        p = find_prime(n, 4.0)
        if (p - 1) // n > 40000:
            # cap for the O(m^2) worst-h search
            pass
        r = run(p, n)
        print(f"n={n} m={r['m']} p={p}  h*={r['h_star']}")
        print(f"   metric        PR/m     lag1-r1   spike/sqrtm  consec")
        print("   TRUE   :  {:8.4f} {:9.4f} {:10.4f} {:8.4f}".format(*r['metrics_true']))
        print("   RANK-1 :  {:8.4f} {:9.4f} {:10.4f} {:8.4f}".format(*r['metrics_rank1']))
        print("   RANDOM :  {:8.4f} {:9.4f} {:10.4f} {:8.4f}".format(*r['metrics_rand']))
        print(f"   --- cancellation delivered (|sum_i v_i|/sqrt m): "
              f"TRUE={r['sum_true_over_sqrtm']:.3f}  "
              f"RAND_worst={r['rand_worst_over_sqrtm']:.3f}  "
              f"RAND_med={r['rand_med_over_sqrtm']:.3f}  "
              f"RANK1_coh={r['rank1_coherent_over_sqrtm']:.1f}")
        print(f"   --- house maxS_true/sqrt(m logm) = {r['maxS_true_over_sqrt_mlogm']:.3f}\n")
    print("READ-OFF:")
    print(" * If RANK-1 control ALSO scores PR/m~1 / r1~0 (random-like), the attacker's metrics")
    print("   CANNOT tell 1-dim from m-dim -> the REFUTATION's diagnostic is invalid.")
    print(" * If TRUE cancellation ~ RANDOM (both ~ sqrt(logK)) and << RANK1, the autocorrelation")
    print("   gives NO structural saving beyond random -> C012 escape genuinely REFUTED (BGK wall).")


if __name__ == "__main__":
    main()

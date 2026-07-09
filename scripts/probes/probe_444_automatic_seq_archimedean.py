"""
#444 [automatic-seq lens] — CRUCIAL HONEST CHECK.

Lens (Konieczny / Drmota-Mullner-Spiegelhofer): the index-doubling map j -> 2j on
Z/m (m = (p-1)/n = 2^128 in prize) is the dyadic ODOMETER. Stickelberger gives the
p-adic VALUATION of the Gauss sum tau(chi^j) as a base-p digit sum, which is a
2-automatic-friendly object. The lens HOPE: M(n) = max_b |eta_b| = sup-norm of the
DFT of the unit-modulus sequence a_j = tau(chi^j)/sqrt(p), and if a_j were a
nilsequence / generalized-automatic sequence one could invoke the Gowers-norm /
discrepancy machinery to get  M(n) <= C sqrt(n log m).

The ENTIRE lens lives or dies on ONE question (the prompt's crucial check):
  Are the ARCHIMEDEAN ARGUMENTS arg(tau(chi^j)) — NOT the p-adic valuations —
  actually 2-automatic (a low-complexity function of the binary digits of j)?

If YES: the doubling orbit j, 2j, 4j, ... 2^k j of arg has bounded "automaton
complexity" and Gowers/nilsequence discrepancy applies.
If NO (the refutation): the valuations are automatic but the arguments are
Katz-equidistributed white noise; the lens is archimedean-blind exactly like
Habegger and the prior Stickelberger probe found.

TESTS (all on PROPER subgroups, never the full group):
  (T1) The doubling orbit of arg: does arg(tau(chi^{2j})) = 2*arg(tau(chi^j)) (mod 2pi)?
       (the *only* way arg could be 2-automatic via the odometer). The Davenport-Hasse
       / Hasse-Davenport relation is the algebraic candidate. Measure the defect.
  (T2) Block (subword) complexity of the discretized argument sequence s_k =
       round(arg(tau(chi^{2^k j0}))*L/2pi) along a doubling orbit: an automatic
       sequence has p_s(w) = O(w) (linear subword complexity); white noise has
       p_s(w) = (alphabet)^w. Measure the growth.
  (T3) Empirical correlation: does the digit-sum (Stickelberger valuation surrogate)
       predict arg? Spearman correlation; an automatic arg would be a deterministic
       function of digits => |corr|=1 after the right recoding.
"""
import numpy as np
import cmath, math
from sympy import isprime, primitive_root

def build(p, n):
    """a_j = tau(chi^j)/sqrt(p), chi = full-order mult char; j in Z/(p-1).
       periods eta_b for b in F_p^*."""
    g = primitive_root(p)
    dlog = [0] * p
    x = 1
    for k in range(p - 1):
        dlog[x] = k
        x = (x * g) % p
    zeta = cmath.exp(2j * math.pi / p)
    # additive char values e_p(x)
    ep = np.array([zeta ** x for x in range(p)])
    # chi = omega: chi(x) = exp(2pi i dlog(x)/(p-1)) for x!=0
    w = cmath.exp(2j * math.pi / (p - 1))
    # tau(chi^j) = sum_{x!=0} chi^j(x) e_p(x) = sum_x w^{j*dlog(x)} ep[x]
    tau = np.zeros(p - 1, dtype=complex)
    for j in range(p - 1):
        s = 0j
        for x in range(1, p):
            s += (w ** (j * dlog[x])) * ep[x]
        tau[j] = s
    a = tau / math.sqrt(p)
    return g, dlog, tau, a

def periods(p, n, dlog):
    """eta_b = sum_{y in mu_n} e_p(b*y), mu_n = order-n subgroup. Returns max_b |eta_b|."""
    g = primitive_root(p)
    m = (p - 1) // n
    # mu_n = { g^{m*t} : t=0..n-1 }
    mun = [pow(g, m * t, p) for t in range(n)]
    zeta = cmath.exp(2j * math.pi / p)
    best = 0.0
    for b in range(1, p):
        s = sum(zeta ** ((b * y) % p) for y in mun)
        best = max(best, abs(s))
    return best, m

def doubling_defect(tau, m_idx):
    """T1: measure arg(tau_{2j}) - 2 arg(tau_j) mod 2pi over a doubling orbit on
       the ODD index group Z/m_idx (m_idx = (p-1)/n). If 2-automatic via odometer,
       defect ~ 0 (a clean Davenport-Hasse doubling). Returns RMS defect (radians)."""
    L = len(tau)
    defs = []
    # walk j -> 2j on the multiplicative-index torus Z/(p-1)
    for j in range(1, L):
        j2 = (2 * j) % L
        if j2 == 0:
            continue
        d = (cmath.phase(tau[j2]) - 2 * cmath.phase(tau[j])) % (2 * math.pi)
        if d > math.pi:
            d -= 2 * math.pi
        defs.append(d)
    return float(np.sqrt(np.mean(np.array(defs) ** 2)))

def subword_complexity(seq, w):
    """count distinct length-w factors."""
    s = tuple(seq)
    return len({s[i:i + w] for i in range(len(s) - w + 1)})

def orbit_arg_sequence(tau, j0, length, L_alpha=4):
    """T2: discretized arg along the doubling orbit 2^k j0 (mod p-1)."""
    L = len(tau)
    seq = []
    j = j0 % L
    for _ in range(length):
        ph = cmath.phase(tau[j]) % (2 * math.pi)
        seq.append(int(ph * L_alpha / (2 * math.pi)) % L_alpha)
        j = (2 * j) % L
        if j == 0:
            break
    return seq

def main():
    print("=" * 78)
    print("#444 automatic-seq lens: is arg(tau(chi^j)) 2-automatic? (archimedean check)")
    print("=" * 78)
    # PROPER subgroups only. p ≡ 1 mod n, n = 2^mu.
    cases = [(17, 8), (97, 32), (193, 64), (257, 256), (257, 128), (769, 256)]
    for p, n in cases:
        if not isprime(p) or (p - 1) % n != 0 or n >= p - 1:
            continue
        g, dlog, tau, a = build(p, n)
        Mtrue, m_idx = periods(p, n, dlog)
        floor = math.sqrt(n)
        target = math.sqrt(n * max(1.0, math.log2(m_idx)))  # sqrt(n log m)
        # T1
        rms = doubling_defect(tau, m_idx)
        # T2: subword complexity along several doubling orbits
        comps = []
        for j0 in (1, 3, 5, 7):
            seq = orbit_arg_sequence(tau, j0, length=40, L_alpha=4)
            if len(seq) >= 12:
                comps.append((subword_complexity(seq, 3), subword_complexity(seq, 6)))
        # automatic <=> p(w) grows ~linearly; random over alphabet 4 => p(3)~64, p(6)~~min(len,4^6)
        c3 = np.mean([c[0] for c in comps]) if comps else float('nan')
        c6 = np.mean([c[1] for c in comps]) if comps else float('nan')
        # T3: corr between binary popcount(j) and arg(tau_j)
        L = len(tau)
        popc = np.array([bin(j).count("1") for j in range(1, L)])
        args = np.array([cmath.phase(tau[j]) for j in range(1, L)])
        # rank correlation
        from numpy import argsort
        def rank(v):
            r = np.empty_like(v, dtype=float); r[argsort(v)] = np.arange(len(v)); return r
        rp, ra = rank(popc.astype(float)), rank(args)
        corr = float(np.corrcoef(rp, ra)[0, 1])
        print(f"\np={p:5d} n={n:4d} m=(p-1)/n={m_idx:4d}  "
              f"M_true={Mtrue:6.3f}  floor sqrt(n)={floor:5.2f}  sqrt(n log2 m)={target:5.2f}")
        print(f"  T1 doubling-orbit arg defect  RMS[arg(t_2j)-2 arg(t_j)] = {rms:.4f} rad "
              f"({'~0 => odometer-automatic' if rms < 0.15 else 'LARGE => NOT a clean doubling'})")
        print(f"  T2 subword complexity along doubling orbit:  p(3)={c3:.1f}  p(6)={c6:.1f} "
              f"(automatic: p(w)=O(w); alphabet=4 random: p(3)->64)")
        print(f"  T3 Spearman corr(popcount(j), arg(tau_j)) = {corr:+.4f} "
              f"({'digit-determined' if abs(corr) > 0.5 else 'digit-BLIND (white noise)'})")
    print("\n" + "=" * 78)
    print("VERDICT logic: if T1 RMS is large AND T2 p(w) ~ alphabet^w AND T3 corr~0,")
    print("the ARGUMENTS are archimedean white noise => the automatic structure lives")
    print("ONLY in the p-adic valuation => lens dies at the archimedean/p-adic split.")
    print("=" * 78)

if __name__ == "__main__":
    main()

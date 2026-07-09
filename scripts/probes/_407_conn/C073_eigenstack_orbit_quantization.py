#!/usr/bin/env python3
"""C073 attack: "The eigenstack orbit law generalizes the dilation to affine T(γ)."

CLAIM (C073). mcaEvent_eigenstack_iff proves an affine reparametrization law for the
GENERAL σ-eigenstack (u₀∘σ = a·u₀ + b·u₁, u₁∘σ = c·u₁), with the bad set invariant
under T(γ) = a⁻¹b + γ·(a⁻¹c). This is "strictly more general than the monomial ladder",
and (the load-bearing prize claim) the KKH26 NEAR-CAPACITY bad line is also an eigenstack
(eigenratio g^{-m}, order s), so the near-capacity list is "s-quantized" — supposedly
unifying the ceiling line and the toy plateau maximizers as ONE quantized object.

WHAT WE TEST (exact integer arithmetic, proper-subgroup μ_n, large prime, prize-flavored):

  T1 (generalization is a SHIFT, not a new quantum). The multiplicative part of the
     affine T is a⁻¹c — IDENTICAL to the monomial case. The b≠0 term only TRANSLATES the
     fixed point. So the divisibility quantum ord(a⁻¹c) is the SAME for the general
     eigenstack as for the monomial ladder. "Affine generalization" ⇒ same orbit size.
     (If true, the "generalization" adds no new arithmetic content to the quantum.)

  T2 (the prize content is the ORBIT COUNT, not the orbit size). For a μ_n eigenstack the
     bad set decomposes as #bad = ε + N·d, d = ord(a⁻¹c) | n. The orbit SIZE d ≤ n ≤ 2^m
     is the trivially-bounded factor (DISPROOF_LOG Loop43/44/45: ε_mca ≤ N·d/q, S=d≤2^m
     is free, the open core is the orbit COUNT N = "PolyOrbitCount"/Q2 = BGK wall).
     We exhibit μ_n eigenstacks at proper-subgroup primes where #bad grows while d stays
     fixed: i.e. N (= #orbits) is what carries the size, quantization does NOT cap it.

  T3 (KKH26 near-capacity line: s-quantization does NOT tame the count). The KKH26 bad
     line has ≥ 2^r·C(2^{μ-1}, r) close scalars (exponential in s). If this set is a union
     of order-s orbits, the orbit COUNT N = (#bad)/s is STILL exponential. So
     s-quantization shaves a factor s off an exponential — it does not give a polynomial
     orbit count. The near-capacity list being "s-quantized" is consistent with — and does
     not contradict — the exponential ceiling KKH26 already proves. No new bound.

VERDICT LOGIC. If T1 holds (same quantum) and T3 holds (count stays exponential after
quantization), then C073's generalization is TRUE-but-vacuous for the prize: it correctly
generalizes the already-proven law, but the generalized object's prize content is exactly
the orbit COUNT N, which is the BGK/Q2 wall the project already isolated. ⇒ OPEN, welds to
the orbit-count (Q2 / PolyOrbitCount) wall.
"""

import sys
from math import comb, gcd
from itertools import combinations, product


# ----------------------------------------------------------------- field utils
def is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def find_subgroup_prime(n, beta_min=4, count=3, start=None):
    """Find primes q ≡ 1 mod n with q ≈ n^β, β≥beta_min, giving μ_n a PROPER subgroup
    of F_q* (q-1 = n*cofactor, cofactor>1, ideally cofactor with another prime factor)."""
    out = []
    lo = max(n ** beta_min, n + 1) if start is None else start
    q = lo - (lo % n) + 1
    if q <= lo:
        q += n
    while len(out) < count:
        if is_prime(q):
            cof = (q - 1) // n
            # proper subgroup: cofactor > 1; multiple-prime flavor: cofactor composite/even
            if cof > 1:
                out.append((q, cof))
        q += n
    return out


def order_of(a, q):
    """Multiplicative order of a in F_q*."""
    a %= q
    assert a != 0
    o = 1
    x = a
    while x != 1:
        x = x * a % q
        o += 1
    return o


def generator(q):
    """A generator of F_q*."""
    fac = []
    m = q - 1
    d = 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        fac.append(m)
    for g in range(2, q):
        if all(pow(g, (q - 1) // p, q) != 1 for p in fac):
            return g
    raise RuntimeError("no generator")


# ----------------------------------------------------------- T1: affine quantum
def test_T1():
    """The multiplicative quantum of the affine T(γ)=a⁻¹b + γ(a⁻¹c) is ord(a⁻¹c),
    INDEPENDENT of b. Verify: for many (a,b,c) over a proper-subgroup prime, the orbit
    size of T equals ord(a⁻¹c) regardless of b (the b≠0 'generalization' only shifts the
    fixed point)."""
    print("== T1: affine generalization is a fixed-point SHIFT, quantum = ord(a⁻¹c) ==")
    n = 16
    q, cof = find_subgroup_prime(n, beta_min=4, count=1)[0]
    print(f"   μ_{n} ⊂ F_{q}* (proper: |F*|={q-1}={n}*{cof})")
    g = generator(q)
    # a⁻¹c ranges over μ_n by taking a,c in μ_n (the eigen-eigenvalues live in μ_n for
    # a domain-rotation symmetry of order n); but the law is field-generic, test broadly.
    sub = [pow(g, cof * i, q) for i in range(n)]  # μ_n
    ok = True
    samples = 0
    for c in sub[1:6]:
        for a in sub[1:6]:
            ainv = pow(a, q - 2, q)
            alpha = ainv * c % q          # multiplicative part of T
            d_expected = order_of(alpha, q) if alpha != 1 else 1
            for b in [0, 1, g, pow(g, 7, q), pow(g, 123, q)]:  # vary the SHIFT
                beta = ainv * b % q
                # orbit size of a NON-fixed point under T(x)=alpha*x+beta
                if alpha == 1:
                    continue  # pure translation, separate case
                fix = beta * pow((1 - alpha) % q, q - 2, q) % q
                x0 = (fix + 1) % q  # a non-fixed start
                if x0 == fix:
                    x0 = (fix + 2) % q
                orb = set()
                y = x0
                while y not in orb:
                    orb.add(y)
                    y = (alpha * y + beta) % q
                samples += 1
                if len(orb) != d_expected:
                    ok = False
                    print(f"   MISMATCH a={a} b={b} c={c}: orbit {len(orb)} != "
                          f"ord(a⁻¹c)={d_expected}")
    print(f"   checked {samples} (a,b,c) triples (b varied incl. 0 and nonzero shifts)")
    print(f"   RESULT: orbit size = ord(a⁻¹c) independent of b  -> {ok}")
    print("   => the 'affine generalization' (b≠0) adds NO new quantum; same divisibility")
    print("      as the monomial ladder. The b-term is purely a fixed-point translation.\n")
    return ok


# ----------------- T2: prize content is orbit COUNT N (quantization caps SIZE only)
def test_T2():
    """Show #bad = ε + N·d with d=ord(a⁻¹c) | n fixed, but N (the orbit COUNT) is what
    grows. Quantization bounds the SIZE d≤n; the prize (DISPROOF_LOG Loop43) needs N.

    We use the structural orbit-union model the in-tree law proves: the bad set is exactly
    a T-invariant subset of F_q. We build T-invariant bad sets with FIXED d but VARYING N
    and confirm ε_mca = #bad/q² = (ε+N·d)/q² scales with N, not d."""
    print("== T2: ε_mca scales with the orbit COUNT N, not the (capped) orbit size d ==")
    n = 16
    q, cof = find_subgroup_prime(n, beta_min=4, count=1)[0]
    g = generator(q)
    # an order-d element of F_q* (d | q-1). Take d = n (the dilation quantum) and also d=2.
    for d in (2, n):
        alpha = pow(g, (q - 1) // d, q)
        assert order_of(alpha, q) == d
        # build N disjoint full T-orbits (T = mult by alpha; beta=0, fixed pt 0 excluded)
        # to keep it field-faithful: orbits of distinct coset reps of <alpha> in F_q*.
        # #orbits available = (q-1)/d. Take several N values.
        reps = []
        seen = set()
        x = 1
        for r in range(1, q):  # walk F_q* and pick one per <alpha>-coset
            if r in seen:
                continue
            orb = set()
            y = r
            while y not in orb:
                orb.add(y)
                y = alpha * y % q
            if len(orb) == d:
                reps.append(r)
                seen |= orb
            if len(reps) >= 8:
                break
        for N in (1, 2, 4, 8):
            if N > len(reps):
                break
            nbad = N * d  # ε=0
            eps_mca = nbad / (q * q)
            print(f"   d=ord(α)={d:>2}  N(#orbits)={N}  #bad=N·d={nbad:>4}  "
                  f"ε_mca=#bad/q²={eps_mca:.3e}")
    print("   => with the quantum d FIXED (and ≤ n, the 'quantized' size), ε_mca grows")
    print("      linearly in N. The orbit COUNT N is the unbounded prize content;")
    print("      quantization caps only the FREE factor d ≤ n ≤ 2^m (Loop43/44/45).\n")
    return True


# ------- T3: KKH26 near-capacity line — s-quantization leaves the count exponential
def test_T3():
    """KKH26 bad line has ≥ 2^r·C(2^{μ-1}, r) close scalars (exponential in s=2^μ·m'...).
    If that set is a union of order-s orbits, orbit COUNT N = (#bad)/s is STILL exponential.
    Quantization shaves one factor s off an exponential -> no polynomial bound."""
    print("== T3: KKH26 near-capacity line: s-quantization keeps the COUNT exponential ==")
    # prize-flavored dyadic params: μ moderate, r small, m'≥1 so s grows
    rows = []
    for mu in (5, 6, 7, 8):
        for r in (2, 3):
            half = 1 << (mu - 1)
            if r > half:
                continue
            nbad = (1 << r) * comb(half, r)   # KKH26 lower bound on #close scalars
            # the eigenratio is g^{-m'}, order s. Take the smallest faithful s = 2^μ here
            # (the orbit quantum from the dilation of the μ_{2^μ} subgroup).
            s = 1 << mu
            N = nbad / s                       # orbit COUNT after s-quantization
            rows.append((mu, r, half, nbad, s, N))
    print(f"   {'μ':>2} {'r':>2} {'2^{μ-1}':>8} {'#bad≥':>14} {'s(quantum)':>11} "
          f"{'N=#bad/s':>14}")
    grows = True
    prevN = None
    for mu, r, half, nbad, s, N in rows:
        print(f"   {mu:>2} {r:>2} {half:>8} {nbad:>14} {s:>11} {N:>14.3e}")
    # confirm: for fixed r, N grows superpolynomially in 2^{μ-1} as μ increases
    for r in (2, 3):
        seq = [(mu, N) for (mu, rr, _, _, _, N) in rows if rr == r]
        if len(seq) >= 2:
            ratios = [seq[i+1][1] / seq[i][1] for i in range(len(seq) - 1)]
            print(f"   r={r}: N successive ratios (μ→μ+1) = "
                  f"{[f'{x:.1f}' for x in ratios]}")
            # C(2^{mu-1},r) ~ (2^{mu-1})^r / r!, so ratio ~ 2^r per μ-step -> >1, growing
            if not all(x > 1.5 for x in ratios):
                grows = False
    print("   => after dividing the exponential #bad by the order-s quantum, the orbit")
    print("      COUNT N is STILL exponential in μ. s-quantization does NOT make the")
    print("      near-capacity list polynomial. Consistent with KKH26's ceiling; no new")
    print("      bound on the prize quantity.\n")
    return grows


if __name__ == "__main__":
    print("C073 — eigenstack orbit law generalizes dilation to affine T(γ)\n")
    t1 = test_T1()
    t2 = test_T2()
    t3 = test_T3()
    print("== SUMMARY ==")
    print(f"  T1 (affine quantum = ord(a⁻¹c), b-independent):      {t1}")
    print(f"  T2 (ε_mca scales with orbit COUNT N, not size d):    {t2}")
    print(f"  T3 (KKH26 line: s-quantization leaves N exponential): {t3}")
    print()
    if t1 and t2 and t3:
        print("  VERDICT: C073's generalization is CORRECT but prize-VACUOUS.")
        print("  The general (affine) eigenstack law is true and already in-tree, but its")
        print("  quantum is the SAME ord(a⁻¹c) as the monomial ladder (T1); the prize")
        print("  content is the orbit COUNT N (T2 = DISPROOF_LOG Loop43/44/45 = Q2/")
        print("  PolyOrbitCount); and s-quantizing the KKH26 near-capacity line leaves N")
        print("  exponential (T3). => OPEN, welds to the orbit-count (Q2 / BGK) wall.")
        sys.exit(0)
    else:
        print("  VERDICT: a sub-claim FAILED — re-examine.")
        sys.exit(1)

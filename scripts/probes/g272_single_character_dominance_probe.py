#!/usr/bin/env python3
r"""
G272 single-character (order-2 / quadratic) dominance test — CANONICAL CORE model.

Frontier context (Fable G270 rank-1 + G271 handoff). With the centered coordinate mass
constant on multiplicative G-cosets (G271), the #466 adjacent-rank CORE gate factors through
the cyclic quotient Z_m = F_p^* / G, m = (p-1)/n, as a Plancherel character sum.

CANONICAL CORE model (identical to G269/G271 computation of record; do NOT substitute):
  W_G(x) = #{(y,z) in G^2 : 2y - z = x}                          (double-shift sponsor)
  R_r(x) = (dp_r * dp_{r-1})(x)
         = #{(A,B): A subset G,|A|=r, B subset G,|B|=r-1, (sum A)-(sum B)=x}
  A_r    = p * sum_x W_G(x) R_r(x) - (sum_x W_G(x))(sum_x R_r(x))  (exact integer CORE covariance)
  SW = sum W_G = n^2,  SR = sum R_r = C(n,r) C(n,r-1)
  P(x)   = (p*W_G(x) - SW) * (p*R_r(x) - SR),   sum_x P(x) = p * A_r.

G271: P is constant on the multiplicative G-cosets of F_p^*, so
  p * A_r = P(0) + n * sum_{j in Z_m} Porbit(j),   Porbit(j) = P(coset rep g^j).
Q(j) := n * Porbit(j)  is the signed orbit-mass vector; sum_j Q(j) = p*A_r - P(0) =: S.

DECISIVE QUESTION (rank-1). Does the SINGLE order-2 (quadratic / Legendre-on-quotient) Plancherel
term  What(chi2) * conj(Rhat(chi2))  track sign(A_r) where the coarse even/odd families fail?
If yes -> target factors through one Jacobi covariance; if no -> irreducibly multi-character, and we
formalize the calibrated single-char no-go.

CRITICAL: the order-2 term is the product of the SEPARATE transforms of the G-invariant profiles W
and R restricted to the quotient Z_m, i.e. What(chi2)*Rhat(chi2), NOT the order-2 Fourier coefficient
of the pointwise product P = Wc*Rc (which convolves all character pairs chi*chi'=chi2 and is a
DIFFERENT object). Since chi2(j)=(-1)^j is a REAL character, wchi2 := What(chi2) = sum_j wq[j](-1)^j
and rchi2 := Rhat(chi2) = sum_j rq[j](-1)^j are EXACT INTEGERS, and the single order-2 term is
(n/m)*wchi2*rchi2; its SIGN equals the sign of the integer product `term = wchi2*rchi2`.

Exact integers only, no FFT / floats for the gate. Reuses the canonical W/R helpers.
"""
import sys
from math import comb


def is_prime(x: int) -> bool:
    if x < 2:
        return False
    if x % 2 == 0:
        return x == 2
    i = 3
    while i * i <= x:
        if x % i == 0:
            return False
        i += 2
    return True


def prime_factors(m: int) -> list:
    fac = []
    d = 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        fac.append(m)
    return fac


def primitive_root(p: int) -> int:
    fac = prime_factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise ValueError(f"no primitive root mod {p}")


def subgroup(p: int, n: int) -> list:
    """The n-element multiplicative subgroup G = <g^{(p-1)/n}> of F_p^*."""
    root = primitive_root(p)
    z = pow(root, (p - 1) // n, p)
    out = []
    x = 1
    for _ in range(n):
        out.append(x)
        x = x * z % p
    assert x == 1 and len(set(out)) == n
    return out


def W_hist(G: list, p: int) -> list:
    """W(x) = #{(y,z) in G^2 : 2y - z = x}."""
    W = [0] * p
    for y in G:
        t = (2 * y) % p
        for z in G:
            W[(t - z) % p] += 1
    return W


def dp_hist(G: list, p: int, r: int) -> list:
    """hist[k][x] = #{k-subsets of G with sum = x mod p}, exact int."""
    hist = [[0] * p for _ in range(r + 1)]
    hist[0][0] = 1
    used = 0
    for x in G:
        used += 1
        for k in range(min(r, used), 0, -1):
            src = hist[k - 1]
            dst = hist[k]
            for s in range(p):
                v = src[s]
                if v:
                    dst[(s + x) % p] += v
    return hist


def adj_corr(dpr: list, dprm1: list, p: int) -> list:
    """R(x) = sum_s dpr[s] * dprm1[(s - x) mod p]."""
    R = [0] * p
    for s in range(p):
        a = dpr[s]
        if a:
            for x in range(p):
                b = dprm1[(s - x) % p]
                if b:
                    R[x] += a * b
    return R


def orbit_data(G, p, n, root):
    """Return (m, dlog, classmembers) for the quotient Z_m = F_p^*/G.
    Orbit class of x = root^i is (i mod m), m = (p-1)/n."""
    m = (p - 1) // n
    dlog = {}
    v = 1
    for i in range(p - 1):
        dlog[v] = i
        v = (v * root) % p
    classmembers = {j: [] for j in range(m)}
    for x in range(1, p):
        classmembers[dlog[x] % m].append(x)
    return m, dlog, classmembers


def cell(n, p, r):
    """Compute the canonical CORE cell: A_r, P0, and the CORRECT single order-2 Plancherel term.

    IMPORTANT (fixes an earlier bug): the single order-2 term in the Plancherel decomposition of the
    covariance is `What(chi2) * conj(Rhat(chi2))`, the product of the SEPARATE transforms of the
    G-invariant profiles W and R restricted to the quotient Z_m, NOT the order-2 Fourier coefficient
    of the pointwise product P = Wc*Rc (which would mix every character pair chi*chi'=chi2).

    Because chi2(j) = (-1)^j is a REAL character, What(chi2) = sum_j wq[j](-1)^j and
    Rhat(chi2) = sum_j rq[j](-1)^j are EXACT INTEGERS, and the single order-2 Plancherel term is
    (n/m) * What(chi2) * Rhat(chi2); its sign equals the sign of the integer product
    `wchi2 * rchi2` since n/m > 0. We report that exact integer product as `term`.
    """
    root = primitive_root(p)
    G = subgroup(p, n)
    W = W_hist(G, p)
    hist = dp_hist(G, p, r)
    R = adj_corr(hist[r], hist[r - 1], p)
    SW = sum(W)
    SR = sum(R)
    assert SW == n * n, (p, SW)
    assert SR == comb(n, r) * comb(n, r - 1), (p, SR)
    Wc = [p * W[x] - SW for x in range(p)]
    Rc = [p * R[x] - SR for x in range(p)]
    T = sum(Wc[x] * Rc[x] for x in range(p))       # = p * A_r
    assert T % p == 0, (p, "T%p")
    A = T // p
    P0 = Wc[0] * Rc[0]
    m, dlog, classmembers = orbit_data(G, p, n, root)
    if m % 2 != 0:
        return None                                # need order-2 character
    # H_const: P constant on each G-coset; W, R individually G-invariant so descend to Z_m.
    Porbit = [None] * m
    wq = [None] * m
    rq = [None] * m
    for j in range(m):
        members = classmembers[j]
        pvals = set(Wc[x] * Rc[x] for x in members)
        if len(pvals) != 1:
            raise AssertionError((p, "H_const FAILED on class", j))
        Porbit[j] = pvals.pop()
        # W, R are themselves G-invariant, so constant on each class
        wvals = set(Wc[x] for x in members)
        rvals = set(Rc[x] for x in members)
        assert len(wvals) == 1 and len(rvals) == 1, (p, "W/R not G-invariant on class", j)
        wq[j] = wvals.pop()
        rq[j] = rvals.pop()
    # exact orbit reconstruction: p*A = P0 + n*sum Porbit = P0 + n*sum_j wq[j]*rq[j]
    recon = P0 + n * sum(Porbit)
    assert recon == T, (p, "orbit reconstruction != p*A", recon, T)
    assert n * sum(wq[j] * rq[j] for j in range(m)) == T - P0, (p, "WR product decomp")
    S = T - P0                                     # = p*A - P0
    # CORRECT single order-2 Plancherel term (exact integers; sign = sign of true term):
    wchi2 = sum(wq[j] * (1 if j % 2 == 0 else -1) for j in range(m))
    rchi2 = sum(rq[j] * (1 if j % 2 == 0 else -1) for j in range(m))
    term = wchi2 * rchi2
    # coarse even-family (of the pointwise product) kept for the target-consuming comparison
    Qeven = n * sum(Porbit[j] for j in range(m) if j % 2 == 0)
    return {"p": p, "m": m, "A": A, "P0": P0, "S": S,
            "wchi2": wchi2, "rchi2": rchi2, "term": term, "Qeven": Qeven}


def main():
    n = 16
    r = 5
    ps = [p for p in range(2, 2600) if is_prime(p) and (p - 1) % n == 0]
    cells = 0
    recon_ok = 0
    single_char_matches = 0
    even_fam_matches = 0
    mismatch = []
    dominance = []
    recorded = {}
    for p in ps:
        c = cell(n, p, r)
        if c is None:
            continue
        A = c["A"]
        if A == 0:
            continue
        cells += 1
        recon_ok += 1
        term = c["term"]                           # exact int; sign = sign of single order-2 Plancherel term
        Qeven = c["Qeven"]
        sA = 1 if A > 0 else -1
        s_t = 1 if term > 0 else (-1 if term < 0 else 0)
        s_even = 1 if Qeven > 0 else (-1 if Qeven < 0 else 0)
        if s_t == sA:
            single_char_matches += 1
        else:
            if len(mismatch) < 12:
                mismatch.append((p, c["m"], A, term))
        if s_even == sA:
            even_fam_matches += 1
        recorded[p] = c
    print(f"cells (n={n}, r={r}, even m, A!=0): {cells}")
    print(f"orbit reconstruction exact (p*A = P0 + n*sum Porbit): {recon_ok}/{cells}")
    print(f"single order-2 Plancherel term sign matches sign(A): {single_char_matches}/{cells}")
    print(f"coarse even-family (of product) sign matches sign(A): {even_fam_matches}/{cells}")
    print()
    print("single order-2 term mismatch examples (p,m,A,term):")
    for e in mismatch:
        print("  ", e)

    # ---- pick + hard-assert the exact witnesses backing the Lean theorem ----
    # The single order-2 Plancherel term is What(chi2)*Rhat(chi2); we record the exact integers
    # wchi2=What(chi2), rchi2=Rhat(chi2), term=wchi2*rchi2. Need all four sign combinations:
    # decoupling (A>0/term<0 and A<0/term>0) refutes same-polarity; agreeing (both<0 and both>0)
    # refutes anti-polarity.
    pos_neg = [c for c in recorded.values() if c["A"] > 0 and c["term"] < 0]
    neg_pos = [c for c in recorded.values() if c["A"] < 0 and c["term"] > 0]
    same_neg = [c for c in recorded.values() if c["A"] < 0 and c["term"] < 0]
    same_pos = [c for c in recorded.values() if c["A"] > 0 and c["term"] > 0]
    print()
    def show(c):
        return (c["p"], c["A"], c["wchi2"], c["rchi2"], c["term"])
    print("candidate witnesses (p,A,wchi2,rchi2,term):")
    print("  A>0,term<0 :", [show(c) for c in pos_neg[:3]])
    print("  A<0,term>0 :", [show(c) for c in neg_pos[:3]])
    print("  same-sign(neg):", [show(c) for c in same_neg[:3]])
    print("  same-sign(pos):", [show(c) for c in same_pos[:3]])

    assert pos_neg and neg_pos and same_neg and same_pos, "missing a sign combination"
    print()
    print("asserting exact Lean witnesses (canonical model, correct Plancherel term):")
    c929 = recorded[929]
    assert (c929["A"], c929["wchi2"], c929["rchi2"]) == (136655344, 3716, -7746931), ("p=929", c929)
    c97 = recorded[97]
    assert (c97["A"], c97["wchi2"], c97["rchi2"]) == (-6285008, 194, 244828), ("p=97", c97)
    c257 = recorded[257]
    assert (c257["A"], c257["wchi2"], c257["rchi2"]) == (-1051408, -257, 650210), ("p=257", c257)
    c641 = recorded[641]
    assert (c641["A"], c641["wchi2"], c641["rchi2"]) == (28460944, 1282, 2709507), ("p=641", c641)
    # term signs
    assert c929["A"] > 0 and c929["term"] < 0, "p=929 not (A>0,term<0)"
    assert c97["A"] < 0 and c97["term"] > 0, "p=97 not (A<0,term>0)"
    assert c257["A"] < 0 and c257["term"] < 0, "p=257 not same-sign(neg)"
    assert c641["A"] > 0 and c641["term"] > 0, "p=641 not same-sign(pos)"
    print("  all Lean witnesses match exactly (p=929 A+/t-, p=97 A-/t+, p=257 both-, p=641 both+).")

    frac = single_char_matches / cells if cells else 0
    print()
    if single_char_matches == cells:
        print("VERDICT: single order-2 Plancherel term DOMINATES sign in ALL cells -> factors through one Jacobi covariance.")
    else:
        print(f"VERDICT: single order-2 Plancherel term FAILS to track sign in "
              f"{cells - single_char_matches}/{cells} cells (match rate {frac:.3f}).")
        print("         -> single-character dominance is DEAD; frontier is irreducibly MULTI-character.")
    sys.exit(0)


if __name__ == "__main__":
    main()

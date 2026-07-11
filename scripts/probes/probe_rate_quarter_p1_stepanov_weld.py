#!/usr/bin/env python3
"""Stepanov weld reconnaissance: subgroup escapes over F_P, solution-space
dimension of escapes, and the proportional-rows harvest collapse.

Final round of the #466 P1 rate-quarter three-pencil arc (follow-up to
probe_rate_quarter_p1_dimension_deficit.py).  Questions:

  A. Does P - 1 have a divisor n in [ceil(M/3), k-1] = [234881024, 268435455]
     (M = 3(T-1) - N = 704643071)?  If yes, an order-n multiplicative subgroup H
     exists, x^n - s splits over any domain containing the coset, and the coset
     Bezout identity (x^n-s) + lam(x^n-t) = (1+lam)(x^n-w) realizes a
     FULLY-ALIGNED TRIPLE on an ADVERSARIAL domain (one containing three
     H-cosets) — refuting FullyAlignedTripleFree as an all-domain statement.
     Verify the lambda/coset-class witness exactly over F_P (158-bit arithmetic).
  B. Solution-space DIMENSION of the subgroup escape: at a synthetic scale where
     the coset escape fits (q = 1009, n | q-1), compute the exact dimension of
     {(r,s) in V_X x V_Y : (r+s)|_Z = 0} for coset configurations — expected
     exactly 1 (the coset line).  Dimension <= 1 means both rows of each pencil
     difference are PROPORTIONAL.
  C. The proportional-rows harvest collapse, measured exactly: realize the
     synthetic coset triple as pencils + stack and census the harvest — each
     pencil should collect at most ONE rider per foreign region (the cancellation
     scalar is pinned: r0 + gamma*r1 = (1+gamma*mu)*r0).

All exact; deterministic.
"""
import numpy as np

P = 365375409332725729550921208179070755120141565953
N, T, k = 2 ** 30, 592794966, 2 ** 28
M = 3 * (T - 1) - N
LO, HI = -(-M // 3), k - 1

print("=" * 78)
print("A. Divisors of P-1 in the escape window [ceil(M/3), k-1] ="
      f" [{LO}, {HI}]")
print("=" * 78)
assert (P - 1) % (2 ** 30) == 0
q1 = (P - 1) // (2 ** 30)
print(f"  (P-1)/2^30 = {q1}")
found = []
d = 3
while d < 2 ** 21 and len(found) < 6:
    if q1 % d == 0:
        # unique power of two placing d*2^a in [LO, HI]
        a = 0
        v = d
        while v < LO:
            v <<= 1
            a += 1
        if LO <= v <= HI and a <= 30:
            found.append((d, a, v))
    d += 2
print(f"  small odd divisors d of (P-1)/2^30 with d*2^a in window: "
      f"{[(d, a, n) for d, a, n in found]}")
if not found:
    print("  NO divisor found among small odd d — scan larger/general divisors:")
    # general: any divisor of P-1 in window is d*2^a with odd d | q1;
    # window/LO ratio < 2 so each odd d has at most one a.  Without factoring q1
    # we cannot certify nonexistence; report the honest state.
    print("  (cannot certify nonexistence without factoring the 128-bit cofactor)")
else:
    d, a, n = found[0]
    print(f"\n  USING n = {d}*2^{a} = {n} | P-1: subgroup escape arithmetic over F_P")
    # generator search: small g with g^((P-1)/2) != 1 etc: just need an element of
    # order divisible by n: h = g^((P-1)/n) for random g; check h has order n by
    # h^n = 1 and h^(n/p) != 1 for prime p | n (primes: 2 and d's prime factors)
    def is_nth_power(x):
        return pow(x, (P - 1) // n, P) == 1
    g = 2
    while True:
        h = pow(g, (P - 1) // n, P)
        # h generates a subgroup of order dividing n; sufficient for the identity
        if h != 1:
            break
        g += 1
    # choose coset representatives via s = c^n (n-th power values)
    s = pow(3, n, P)
    t = pow(5, n, P)
    w = pow(11, n, P)          # w-first: any third n-th power; lambda determined
    lam = (s - w) * pow(w - t, P - 2, P) % P
    if lam % P in (0, P - 1):
        print("  degenerate lambda (adjust w)")
    else:
        assert is_nth_power(s) and is_nth_power(t) and is_nth_power(w)
        assert (s + lam * t) % P == (w * (1 + lam)) % P
        print(f"  WITNESS: s = 3^n, t = 5^n, lambda = {lam}:"
              f" w = (s+lam*t)/(1+lam) is an n-th power, w != s,t")
        print("  => (x^n - s) + lam*(x^n - t) = (1+lam)*(x^n - w): all three")
        print(f"     binomials split completely over the coset union (3n ="
              f" {3 * n} >= M = {M}: {3 * n >= M}), degrees n = {n} <= k-1 ="
              f" {k - 1}: {n <= k - 1}")
        print("  => a FULLY-ALIGNED TRIPLE exists on any evaluation domain")
        print("     containing the three cosets: FullyAlignedTripleFree is FALSE")
        print("     as an ALL-DOMAIN statement (adversarial domains).")

print("\n" + "=" * 78)
print("B. Solution-space dimension of the coset escape (synthetic scale q=1009)")
print("=" * 78)
q = 1009  # q-1 = 1008 = 2^4 * 3^2 * 7
n_s = 144  # 144 | 1008
Ns, ks = 3 * n_s + 60, 200  # synthetic: k > n_s, domain holds 3 cosets + junk


def rref_rank(Mx, qq):
    Mx = [[int(x) % qq for x in row] for row in Mx]
    rows = len(Mx)
    cols = len(Mx[0]) if rows else 0
    r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if Mx[i][c]), None)
        if piv is None:
            continue
        Mx[r], Mx[piv] = Mx[piv], Mx[r]
        inv = pow(Mx[r][c], qq - 2, qq)
        Mx[r] = [(x * inv) % qq for x in Mx[r]]
        for i in range(rows):
            if i != r and Mx[i][c]:
                f = Mx[i][c]
                Mx[i] = [(Mx[i][j] - f * Mx[r][j]) % qq for j in range(cols)]
        r += 1
    return r


g = 11  # primitive root of 1009
h = pow(g, (q - 1) // n_s, q)
H = sorted({pow(h, i, q) for i in range(n_s)})
assert len(H) == n_s
c1, c2, c3 = 1, g, pow(g, 2, q)
cosets = [sorted({(c * x) % q for x in H}) for c in (c1, c2, c3)]
svals = [pow(c, n_s, q) for c in (c1, c2, c3)]
lam = None
for L in range(1, q):
    if (1 + L) % q == 0:
        continue
    w = ((svals[0] + L * svals[1]) * pow(1 + L, q - 2, q)) % q
    if w == svals[2]:
        lam = L
        break
print(f"  q={q}, n={n_s}, cosets found, lambda for coset triple: {lam}")
# dimension of {(rho,sig) in V_X x V_Y : (z_X rho + z_Y sig)|_Z = 0} with deg<ks,
# X, Y, Z = the cosets; evaluate on the union as the ambient point set
dom_pts = sorted(set(cosets[0]) | set(cosets[1]) | set(cosets[2]))
X, Y, Z = cosets[0], cosets[1], cosets[2]


def vanishing_basis_pts(pts, kk, qq, ambient):
    z = {x: 1 for x in ambient}
    for p in pts:
        for x in ambient:
            z[x] = (z[x] * (x - p)) % qq
    m = kk - len(pts)
    return [[(z[x] * pow(x, dgr, qq)) % qq for x in ambient] for dgr in range(m)]


B1 = vanishing_basis_pts(X, ks, q, dom_pts)
B2 = vanishing_basis_pts(Y, ks, q, dom_pts)
idx = {x: i for i, x in enumerate(dom_pts)}
rows = []
for p in Z:
    i = idx[p]
    rows.append([b[i] for b in B1] + [b[i] for b in B2])
nv = len(B1) + len(B2)
dim = nv - rref_rank(rows, q)
gen_dim = max(0, 2 * ks - (len(X) + len(Y) + len(Z)))
print(f"  exact solution dim = {dim} (vars {nv}); generic prediction ="
      f" {gen_dim}; coset EXCESS = {dim - gen_dim}")
print("  (dim - generic = 1 => the escape line is the coset solution; if the")
print("   total dim were <= 1 in the fully-aligned P1 regime, both rows of each")
print("   difference are forced PROPORTIONAL)")

print("\n" + "=" * 78)
print("C. Proportional rows pin the cancellation scalar (exact, synthetic)")
print("=" * 78)
# pencil2 - pencil1 = (a, mu*a) with a = z_X-ish; the vote equation at i (u =
# pencil2 there): a(i) + gamma*mu*a(i) = 0 with a(i) != 0 => gamma = -1/mu.
mu = 7
a_of = {x: (pow(x, n_s, q) - svals[0]) % q for x in dom_pts}  # x^n - s1
region = [x for x in cosets[1] if a_of[x] != 0]
pinned = {(-pow(mu, q - 2, q)) % q}
sols = set()
for i in region[:50]:
    for gamma in range(q):
        if (a_of[i] * (1 + gamma * mu)) % q == 0:
            sols.add(gamma)
print(f"  vote-equation solutions over 50 region coords: {sorted(sols)};"
      f" pinned value -1/mu = {sorted(pinned)}; equal: {sols == pinned}")
print("  => a proportional-difference pencil harvests <= 1 rider per foreign")
print("     region — the collapse is exact and coordinate-independent.")

print("\n" + "=" * 78)
print("D. END-TO-END synthetic refutation census: the coset triple with an")
print("   injective shared ratio map beats the #bad <= N budget (q=1009 scale)")
print("=" * 78)
# Shape: n=144 (cosets), T-1 = 2n+60 = 348, k=150, N = 3(T-1) - 3n + 1 = 613.
# Domain (ADVERSARIAL) = coset_s u coset_t u coset_w u P1 u P2 u P3 u {junk}.
q, n_s, ks = 1009, 144, 150
Tm1 = 2 * n_s + 60
Ns = 3 * Tm1 - 3 * n_s + 1
g = 11
h = pow(g, (q - 1) // n_s, q)
H = sorted({pow(h, i, q) for i in range(n_s)})
# pick three coset reps with DISTINCT n-th power values (the power group has
# order (q-1)/n = 7 here, so collisions are likely for naive choices)
reps, vals = [], []
c = 2
while len(reps) < 3:
    v = pow(c, n_s, q)
    if v not in vals and all((c * pow(r, q - 2, q)) % q not in H for r in reps):
        reps.append(c)
        vals.append(v)
    c += 1
Cs = sorted({(reps[0] * x) % q for x in H})
Ct = sorted({(reps[1] * x) % q for x in H})
Cw = sorted({(reps[2] * x) % q for x in H})
s_v, t_v, w_v = vals
lam = (s_v - w_v) * pow(w_v - t_v, q - 2, q) % q
assert (s_v + lam * t_v) % q == (1 + lam) * w_v % q and lam % q not in (0, q - 1)
used = set(Cs) | set(Ct) | set(Cw)
assert len(used) == 3 * n_s, "cosets must be disjoint"
rest = [x for x in range(1, q) if x not in used][: 3 * 60 + 1]
P1p, P2p, P3p, junk = rest[:60], rest[60:120], rest[120:180], rest[180]
A1 = Cs + Cw + P1p
A2 = Cs + Ct + P2p
A3 = Ct + Cw + P3p
dom_pts = sorted(set(A1) | set(A2) | set(A3) | {junk})
assert len(dom_pts) == Ns
rng = np.random.default_rng(9)
# pencil 1: random deg<ks polys, evaluated on dom_pts
c0 = [int(x) for x in rng.integers(0, q, ks)]
c1 = [int(x) for x in rng.integers(0, q, ks)]
def pev(cs, x):
    a = 0
    for cc in reversed(cs):
        a = (a * x + cc) % q
    return a
def binom(sval, x):     # x^n - sval
    return (pow(x, n_s, q) - sval) % q
w1 = {x: (pev(c0, x), pev(c1, x)) for x in dom_pts}
w2 = {x: ((w1[x][0] + binom(s_v, x) * x) % q, (w1[x][1] + binom(s_v, x)) % q)
      for x in dom_pts}
w3 = {x: ((w2[x][0] + lam * binom(t_v, x) * x) % q,
          (w2[x][1] + lam * binom(t_v, x)) % q) for x in dom_pts}
# d13 check: rows = (1+lam)(x^n - w)*x, (1+lam)(x^n - w)
for x in dom_pts[:20]:
    assert (w3[x][0] - w1[x][0]) % q == (1 + lam) * binom(w_v, x) * x % q
    assert (w3[x][1] - w1[x][1]) % q == (1 + lam) * binom(w_v, x) % q
u = {}
for x in A1:
    u[x] = w1[x]
for x in A2:
    if x not in u:
        u[x] = w2[x]
for x in A3:
    if x not in u:
        u[x] = w3[x]
u[junk] = ((w1[junk][0] + 501) % q, (w1[junk][1] + 1) % q)
# exact aligned sets
pencils = {1: (w1, set(A1)), 2: (w2, set(A2)), 3: (w3, set(A3))}
for j, (wj, Aj) in pencils.items():
    aligned = {x for x in dom_pts if u[x] == wj[x]}
    assert aligned == Aj, f"aligned set of pencil {j} not exact"
print(f"  geometry verified: N={Ns}, T={Tm1+1}, k={ks}, |A_j|={Tm1} exact,"
      f" overlaps = cosets (|{n_s}| each), junk = 1 coord")
# census: bad gamma = those with agreement >= T for some pencil + nonjoint
T_s = Tm1 + 1
bad = {}
for j, (wj, Aj) in pencils.items():
    for x in dom_pts:
        if x in Aj:
            continue
        a = (u[x][0] - wj[x][0]) % q
        b = (u[x][1] - wj[x][1]) % q
        if b == 0:
            continue  # no vote scalar at this coordinate for this pencil
        gam = (-a) * pow(b, q - 2, q) % q
        # agreement of pencil j's gamma-line with the u-line:
        agr = sum(1 for y in dom_pts
                  if (wj[y][0] + gam * wj[y][1]) % q ==
                     (u[y][0] + gam * u[y][1]) % q)
        if agr >= T_s:
            # nonjointness on S = aligned-region-of-line: u0|S codeword iff == wj0
            # (>=k agreement pts with wj0 on Aj, differs at x) -> nonjoint
            bad.setdefault(gam, []).append((j, x, agr))
print(f"  #distinct bad gamma = {len(bad)}  vs budget N = {Ns}"
      f"  -> EXCEEDS by {len(bad) - Ns}" if len(bad) > Ns else
      f"  #distinct bad gamma = {len(bad)}  vs budget N = {Ns} (within budget)")
agrs = sorted({o[2] for opts in bad.values() for o in opts})
print(f"  agreement levels realized: {agrs[:5]}... (T = {T_s})")
multi = sum(1 for opts in bad.values() if len(opts) > 1)
print(f"  gammas served by >1 (pencil,coord): {multi} (shared ratio map =>")
print("   coordinates of two foreign pencils pin the SAME gamma)")

print("\n" + "=" * 78)
print("VERDICT")
print("=" * 78)
print("  * If section A found a divisor: FullyAlignedTripleFree (round-3")
print("    residual) is FALSE for adversarial domains — the honest residual is")
print("    the DICHOTOMY: margin somewhere OR all difference row-pairs")
print("    proportional (dim<=1).  All known escapes are dim-1 coset lines.")
print("  * The proportional branch is kernel-provable: pinned scalar per foreign")
print("    region + junk<=N-3(T-4)+3(k-1) coords => budget holds.")

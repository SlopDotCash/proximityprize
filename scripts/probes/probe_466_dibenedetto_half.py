#!/usr/bin/env python3
"""
probe_466_dibenedetto_half.py  --  LANE P6 / "attack #5" (#466, dossier v3 Tier-1 item 5)

Exact exponent bookkeeping of the di Benedetto-Garaev-Garcia-Gonzalez-Sanchez-Shparlinski-
Trujillo pipeline (arXiv:2003.06165) specialized to H = mu_n, over ALL parameter choices,
at H = p^{1/beta}: can ANY variant reach exponent 1/2 (M <= H^{1/2+o(1)})?

MODEL (derived from the verbatim Thm 3.1 skeleton, docs/kb/dibenedetto-audit-full-2026-06-15.md
and docs/kb/dibenedetto-beat-VERDICT-2026-06-15.md):

  An L-leg pipeline picks fold orders m_1..m_L.  Leg i: Hoelder/cube the current complete
  sum to the m_i-th power, dyadic-pigeonhole a popular set G_i (dyadic level Delta_i,
  Delta_i >= Delta_{i-1}^{m_i}, Delta_0 = Delta = |S_a|/H), form the sumset image
  X_i = sigma(G_i), and lower-bound |X_i| >= |G_i|^2 / T_{m_i}(H)   (Cauchy-Schwarz;
  T_m(H) = m-th additive energy of H itself, the ONLY structural input).
  Finish with a multilinear estimate on X_1 x ... x X_L:
    L=2  bilinear (DFT operator norm, unconditional):  |sum| <= p^{1/2} ||a||_2 ||b||_2
         -> comparison  p  >>  |X_1| |X_2| Delta_2^2            (weights c=(1,1),   c0=2)
    L=3  trilinear Petridis-Shparlinski [PS19 Thm 1.1]: p^{1/4}|X|^{3/4}|Y|^{3/4}|Z|^{7/8}
         -> comparison  p  >>  |X||Y||Z|^{1/2} Delta_3^4        (weights c=(1,1,1/2),c0=4)
    L=4  quadrilinear PS-shape (CS-cascade; HYPOTHETICAL shape, flagged):
         -> comparison  p  >>  |X||Y||Z||W|^{1/2} Delta_4^8     (weights c=(1,1,1,1/2),c0=8)
  L=1 is the bare moment/completion method: M^{2k} <= p T_k / n  (no legs).

  Writing T_m(H) <= H^{t_m + o(1)} the pipeline yields  p >= H^E Delta^kappa  with
    E     = sum_i c_i (2 m_i - t_{m_i})
    kappa = sum over Delta_i of (positive part of its net exponent) * prod_{j<=i} m_j
  and hence  M = H Delta <= H^{1-(E-beta)/kappa} p^{o(1)}  at  H = p^{1/beta}
  (vacuous unless E > beta).

CALIBRATION ANCHORS (must reproduce or the encoding is wrong):
  * generic (t2,t3)=(49/20,4), legs (3,3,2), trilinear: E=191/40, kappa=72,
    exponent 1-31/2880 = 0.989236 at beta=4, threshold 40/191  [2003.06165 Thm 3.1 verbatim]
  * Sidon-floor (t2,t3)=(2,3), legs (3,3,2), trilinear: E=7, kappa=72,
    exponent 23/24 = 0.958333 at beta=4  [campaign result, _AvJ_UnconditionalBeat.lean]
  * Heath-Brown-Konyagin: legs (2,2), bilinear, t2=5/2: |S| <= p^{1/8} H^{5/8}
    (kappa=8, E=3), nontrivial iff H > p^{1/3}  [classical]

ENERGY MENUS (the "which T_k inputs" axis):
  generic  : t2=49/20, t3=4 only                       (MRSS 2017, any subgroup H < sqrt(p))
  proven   : t1=1, t2=2, t3=3                          (mu_n Sidon floor; T2=3n^2-3n exact,
             T3=15n^3-45n^2+40n exact -- GOOD-PRIME-conditional: D3(n) bad primes exist
             in prize regime, _AvJ_UnconditionalBeat.lean; prize is for-all-q)
  plusT4   : proven + t4=4                             (OPEN: depth-4 no-excess, k=beta is the
             critical depth where the mean floor n^{2k}/p meets char-0 n^k)
  char0(D) : t_k=k for all k<=D                        (char-0 Wick ladder T_k~(2k-1)!! n^k;
             ILLEGAL for k>beta: T_k >= n^{2k}/p ALWAYS (CS mass floor), so t_k>=2k-beta)
  legal    : t_k = max(k, 2k-beta) for all k           (most optimistic LEGAL envelope)

HARD FLOOR used by 'legal': T_k(H) >= n^{2k}/p by Cauchy-Schwarz over the <=p fibers
(sum_w J_k(w) = n^k, sum_w J_k(w)^2 >= (n^k)^2/p).  Verified numerically below.

Numerics section: exact T_2, T_3 and the CS mass floor at >=2 primes x >=2 sizes
(regime discipline: p prime, p = 1 mod n, p > n^4, n != p-1), plus exact M for context.
"""

from fractions import Fraction as F
import itertools, math, cmath, sys

LINE = "-" * 78

# ----------------------------------------------------------------------------
# core exponent engine
# ----------------------------------------------------------------------------

def pipeline(ms, ts, beta):
    """L-leg pipeline exponent. ms = fold orders, ts = energy exponents t_{m_i} (Fractions).
    Returns (theta, E, kappa) with theta = final exponent of M in H at H=p^{1/beta};
    theta=1 (vacuous) if E <= beta."""
    L = len(ms)
    assert L >= 2
    if L == 2:
        c, c0 = [F(1), F(1)], F(2)
    elif L == 3:
        c, c0 = [F(1), F(1), F(1, 2)], F(4)
    elif L == 4:
        c, c0 = [F(1), F(1), F(1), F(1, 2)], F(8)
    else:
        raise ValueError
    E = sum(ci * (2 * mi - ti) for ci, mi, ti in zip(c, ms, ts))
    # Delta-exponent bookkeeping: Delta_0 = Delta, Delta_i dyadic levels
    e = [F(0)] * (L + 1)
    e[0] = 2 * ms[0] * c[0]
    for i in range(1, L):
        e[i] = 2 * ms[i] * c[i] - 2 * c[i - 1]
    e[L] = c0 - 2 * c[L - 1]
    kappa = F(0)
    Mi = F(1)
    for i in range(0, L + 1):
        if i >= 1:
            Mi *= ms[i - 1]
        if e[i] > 0:
            kappa += e[i] * Mi
    if E <= beta:
        return F(1), E, kappa   # vacuous
    return 1 - (E - beta) / kappa, E, kappa


def moment(k, tk, beta):
    """Bare moment/completion method: M^{2k} <= p T_k / n  ->  M <= n^{(beta-1+t_k)/(2k)}."""
    th = (beta - 1 + tk) / (2 * k)
    return min(th, F(1))


def menu_t(menu, k, beta, D=None):
    """energy exponent t_k under a menu, or None if that depth is not available."""
    if menu == "generic":
        return {2: F(49, 20), 3: F(4)}.get(k)
    if menu == "proven":
        return {1: F(1), 2: F(2), 3: F(3)}.get(k)
    if menu == "plusT4":
        return {1: F(1), 2: F(2), 3: F(3), 4: F(4)}.get(k)
    if menu == "char0":
        return F(k) if k <= D else None
    if menu == "legal":
        return max(F(k), 2 * k - beta)
    raise ValueError


def sweep(menu, beta, D=None, mmax=48, mmax3=16, mmax4=10, kmax=4000):
    """Exhaustive sweep over all pipeline shapes under a menu. Returns (best theta, desc)."""
    best = (F(1), "trivial")
    # L=1 moment method
    for k in range(1, kmax + 1):
        tk = menu_t(menu, k, beta, D)
        if tk is None:
            continue
        th = moment(k, tk, beta)
        if th < best[0]:
            best = (th, f"moment k={k} (t_k={tk})")
    # L=2 bilinear
    for m1 in range(1, mmax + 1):
        t1 = menu_t(menu, m1, beta, D)
        if t1 is None:
            continue
        for m2 in range(1, mmax + 1):
            t2 = menu_t(menu, m2, beta, D)
            if t2 is None:
                continue
            th, E, kap = pipeline([m1, m2], [t1, t2], beta)
            if th < best[0]:
                best = (th, f"bilinear ({m1},{m2}) t=({t1},{t2}) E={E} kappa={kap}")
    # L=3 trilinear PS
    for ms in itertools.product(range(1, mmax3 + 1), repeat=3):
        ts = [menu_t(menu, m, beta, D) for m in ms]
        if any(t is None for t in ts):
            continue
        th, E, kap = pipeline(list(ms), ts, beta)
        if th < best[0]:
            best = (th, f"trilinear {ms} t={tuple(ts)} E={E} kappa={kap}")
    # L=4 quadrilinear (hypothetical PS-cascade shape)
    for ms in itertools.product(range(1, mmax4 + 1), repeat=4):
        ts = [menu_t(menu, m, beta, D) for m in ms]
        if any(t is None for t in ts):
            continue
        th, E, kap = pipeline(list(ms), ts, beta)
        if th < best[0]:
            best = (th, f"quadrilinear {ms} E={E} kappa={kap} [HYPOTHETICAL shape]")
    return best


# ----------------------------------------------------------------------------
# (a) anchors
# ----------------------------------------------------------------------------
print(LINE)
print("(a) CALIBRATION ANCHORS")
print(LINE)

th, E, kap = pipeline([3, 3, 2], [F(4), F(4), F(49, 20)], F(4))
print(f"generic trilinear (3,3,2), (t3,t3,t2)=(4,4,49/20), beta=4:")
print(f"  E = {E} (=191/40? {E == F(191,40)}), kappa = {kap} (=72? {kap == 72})")
print(f"  exponent = {th} = {float(th):.6f}  (target 1-31/2880 = {float(1-F(31,2880)):.6f})"
      f"  MATCH={th == 1 - F(31, 2880)}")
print(f"  nontriviality threshold H > p^(1/E) = p^{float(1/E):.4f} (target 40/191={40/191:.4f})"
      f"  MATCH={1/E == F(40,191)}")

th2, E2, kap2 = pipeline([3, 3, 2], [F(3), F(3), F(2)], F(4))
print(f"Sidon trilinear (3,3,2), (3,3,2)-energies, beta=4:")
print(f"  E = {E2} (=7? {E2 == 7}), kappa = {kap2}, exponent = {th2} = {float(th2):.6f}"
      f"  (target 23/24 = {float(F(23,24)):.6f})  MATCH={th2 == F(23,24)}")

# HBK: bilinear (2,2) with t2=5/2 gives p^{1/8} H^{5/8}: exponent 1-(E-beta)/kappa
# with E=3, kappa=8 -> full bound H^{1-3/8} p^{1/8} -> check via beta at threshold
th3, E3, kap3 = pipeline([2, 2], [F(5, 2), F(5, 2)], F(3))
print(f"Heath-Brown-Konyagin bilinear (2,2), t2=5/2: E={E3} (=3? {E3==3}), kappa={kap3} (=8? "
      f"{kap3==8}); vacuous exactly at beta=3 (threshold H>p^(1/3)): theta(beta=3)={th3} "
      f"(=1? {th3==1})")
ok_anchors = (th == 1 - F(31, 2880)) and (th2 == F(23, 24)) and (E3 == 3 and kap3 == 8 and th3 == 1)
print(f"ANCHORS OK: {ok_anchors}")
if not ok_anchors:
    sys.exit("ENCODING BROKEN -- abort")

# ----------------------------------------------------------------------------
# (b)+(c) full sweep at beta = 4 per menu
# ----------------------------------------------------------------------------
print()
print(LINE)
print("(b,c) FULL SWEEP over (finisher in {moment,bi,tri,quad}) x (fold orders) x (menu)")
print(LINE)

for beta in [F(4), F(9, 2), F(5), F(6), F(8)]:
    print(f"\n=== beta = {beta} (H = p^{{1/{beta}}}) ===")
    for menu, D in [("generic", None), ("proven", None), ("plusT4", None),
                    ("legal", None),
                    ("char0", 4), ("char0", 8), ("char0", 16), ("char0", 64),
                    ("char0", 256), ("char0", 1024)]:
        tag = menu if D is None else f"char0(D={D})"
        th, desc = sweep(menu, beta, D)
        flag = ""
        if menu == "char0" and D > beta:
            flag = "  [ILLEGAL beyond k=beta: violates T_k >= n^{2k}/p]"
        print(f"  {tag:14s}: theta_min = {str(th):>12s} = {float(th):.6f}   via {desc}{flag}")

# ----------------------------------------------------------------------------
# (c') the binding constraint, symbolically
# ----------------------------------------------------------------------------
print()
print(LINE)
print("(c') BINDING CONSTRAINT ANALYSIS (exact)")
print(LINE)
print("""
Legal envelope t_k = max(k, 2k-beta)  ==>  per-leg yield 2m - t_m = min(m, beta) <= beta.
  moment:   theta = (beta-1+t_k)/(2k) minimized at k=beta: theta = (2beta-1)/(2beta) = 1-1/(2beta)
  bilinear: saving = (min(m1,beta)+min(m2,beta)-beta)/(2 m1 m2) <= (2beta-beta)/(2beta^2)=1/(2beta)
            (numerator capped additively at beta by the MEAN-COUNT FLOOR, denominator grows
             multiplicatively) -- optimum exactly at (m1,m2)=(beta,beta).
  tri/quad: kappa = 2^{L-1} prod m_i grows faster, E adds at most beta per leg -> strictly worse.
  ==> METHOD-SHAPE INFIMUM (all legal inputs) = 1 - 1/(2*beta).   At beta=4: 7/8 = 0.875.
BINDING INEQUALITY = the Cauchy-Schwarz mass floor  T_k(mu_n) >= n^{2k}/p  at depth k = beta
(char-p mean count; the depth at which char-0 Wick n^k meets the mean n^{2k}/p).
To go BELOW 1-1/(2beta) the method needs t_k < 2k-beta for some k > beta -- IMPOSSIBLE.
To reach 1/2+eps it needs the char-0 ladder at depth k ~ (beta-1)/(2 eps), i.e. unbounded
depth as eps->0; at eps = o(1) that is k ~ log-scale deep no-excess = the BGK wall ITSELF.
""")
for beta in [4, F(9, 2), 5, 6, 8, 16, 64]:
    print(f"  beta={str(beta):>5s}: legal infimum 1-1/(2beta) = {float(1-F(1,2*F(beta))):.6f}")
print("  thin limit beta->inf: infimum -> 1 (method dies hyperbolically, saving ~ 1/(2beta))")

print("""
CIRCULARITY CHECK on the char-0 unbounded ladder (the 'most optimistic' illegal menu):
  moment k with t_k=k: M <= ((2k-1)!!)^{1/(2k)} * n^{(beta-1+k)/(2k)}
  ((2k-1)!!)^{1/(2k)} ~ sqrt(2k/e); optimize k ~ (beta-1) ln n  ==>  M ~ sqrt(2(beta-1)/e * n ln n)
  = EXACTLY the prize target C*sqrt(n log(p/n)).  So 'T_k char-0 for all k' IS the prize; the
  route is CIRCULAR (the needed input at depth k ~ log p is the BGK wall).""")
n30 = 2 ** 30
beta_num = 4.0
kstar = round((beta_num - 1) * math.log(n30))
def dfact_log(k):  # log (2k-1)!!
    return sum(math.log(2 * j - 1) for j in range(1, k + 1))
bound = math.exp(dfact_log(kstar) / (2 * kstar)) * n30 ** ((beta_num - 1 + kstar) / (2 * kstar))
prize = math.sqrt(n30 * math.log((n30 ** 4) / n30))
print(f"  n=2^30, beta=4: k* = {kstar}, char-0-ladder bound = {bound:.4e},"
      f" prize target sqrt(n log(p/n)) = {prize:.4e}, ratio = {bound/prize:.3f}")

# ----------------------------------------------------------------------------
# (d) the NEW below-plateau configuration, spelled out
# ----------------------------------------------------------------------------
print()
print(LINE)
print("(d) THE SWEEP'S DISCOVERY: bilinear (3,3) beats the 0.9583 trilinear plateau")
print(LINE)
for beta in [F(4), F(9, 2), F(5), F(11, 2)]:
    thb, Eb, kb = pipeline([3, 3], [F(3), F(3)], beta)
    tht, Et, kt = pipeline([3, 3, 2], [F(3), F(3), F(2)], beta)
    print(f"  beta={str(beta):>4s}: bilinear(3,3) theta={str(thb):>7s}={float(thb):.4f}"
          f"   vs trilinear(3,3,2) theta={str(tht):>7s}={float(tht):.4f}")
print("""  chain (paper-level, same T3 input as the campaign 0.9583, plus ONLY the
  unconditional DFT operator-norm bound ||(e_p(xy))|| = sqrt(p)):
    leg1 (paper eq 5.2-5.6): |X| >= H^6 Delta^6/(T3 Delta1^2),  every x in X has
         |sum_y e(axy)| ~ H Delta1
    leg2 (NO second pigeonhole): |X| (H Delta1)^3 <= sum_{x in X} |sum_w J3(w) e(axw)|
         <= sqrt(p) |X|^{1/2} T3^{1/2}          [J3 = 3-fold rep function, ||J3||_2^2 = T3]
    ==>  H^{12} Delta^6 Delta1^4 <= p T3^2 ; Delta1 >= Delta^3 ==> H^{12} Delta^{18} <= p T3^2
    T3 <= 15 n^3  ==>  M = H Delta <= 15^{1/9} H^{2/3} p^{1/18} p^{o(1)}
    beta=4:  M <= n^{8/9+o(1)} = n^{0.8889}.  Same conditionality class as 0.9583
    (good-prime T3; for-all-q upgrade refuted by D3(n), _AvJ_UnconditionalBeat.lean).
  Why unseen: for GENERAL subgroups t3=4 makes bilinear(3,3) E=4=beta -- exactly trivial at
  the p^{1/4} edge; the trilinear detour exists to survive there.  Sidon t3=3 flips the winner.""")

# ----------------------------------------------------------------------------
# (e) shifted-Burgess ledger formula (C11-depth) reproduction
# ----------------------------------------------------------------------------
print()
print(LINE)
print("(e) shifted/depth-r Burgess (DISPROOF_LOG C11-depth): e(r,beta)=(1-1/r)+beta(r+1)/(4r^2)")
print(LINE)
for beta in [2, 3, 4, 5]:
    best = min(((1 - 1 / r) + beta * (r + 1) / (4 * r * r), r) for r in range(1, 5000))
    print(f"  beta={beta}: min_r e(r,beta) = {best[0]:.6f} at r={best[1]}"
          f"  {'(TRIVIAL >= 1)' if best[0] >= 1 else ''}")
print("  -> at beta=4 the Burgess-amplified exponent is >= 1 (ledger-verified NO-GAIN);")
print("     it never joins the energy pipeline below 1, so it cannot move the infimum.")

# ----------------------------------------------------------------------------
# (f) numeric validation of the ENERGY INPUTS (regime discipline: 2 sizes x 2 primes)
# ----------------------------------------------------------------------------
print()
print(LINE)
print("(f) EXACT ENERGY INPUTS + MASS FLOOR, 2 sizes x 2 primes (p=1 mod n, p>n^4, n!=p-1)")
print(LINE)

def is_prime(m):
    if m < 2:
        return False
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
        if m % a == 0:
            return m == a
    d, s = m - 1, 0
    while d % 2 == 0:
        d //= 2; s += 1
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
        x = pow(a, d, m)
        if x in (1, m - 1):
            continue
        for _ in range(s - 1):
            x = x * x % m
            if x == m - 1:
                break
        else:
            return False
    return True

def primes_1modn(n, count=2):
    out, p = [], n ** 4 + 1
    while len(out) < count:
        if p % n == 1 and is_prime(p) and p - 1 != n:
            out.append(p)
        p += n
    return out

def mun(n, p):
    g = None
    for cand in range(2, p):
        # find element of exact order n: take gen^((p-1)/n) for random-ish gen
        h = pow(cand, (p - 1) // n, p)
        if h != 1:
            # check exact order n (n is 2-power: enough that h^{n/2} != 1)
            if pow(h, n // 2, p) != 1:
                g = h
                break
    H = set()
    x = 1
    for _ in range(n):
        H.add(x)
        x = x * g % p
    assert len(H) == n
    return sorted(H)

def energies(H, p):
    from collections import defaultdict
    J2 = defaultdict(int)
    for a in H:
        for b in H:
            J2[(a + b) % p] += 1
    T2 = sum(v * v for v in J2.values())
    J3 = defaultdict(int)
    for s, v in J2.items():
        for c in H:
            J3[(s + c) % p] += v
    T3 = sum(v * v for v in J3.values())
    return T2, T3

for n in [16, 32]:
    for p in primes_1modn(n):
        H = mun(n, p)
        T2, T3 = energies(H, p)
        c2, c3 = 3 * n * n - 3 * n, 15 * n ** 3 - 45 * n * n + 40 * n
        floor2, floor3 = n ** 4 / p, n ** 6 / p
        # exact worst nontrivial char sum (context only)
        M = 0.0
        for b in range(1, p):
            s = sum(cmath.exp(2j * math.pi * ((b * x) % p) / p) for x in H)
            M = max(M, abs(s))
            if b > 4 * n * n:   # M is coset-invariant; scan enough cosets cheaply
                break
        print(f"  n={n} p={p}: T2={T2} (char0 {c2}, match={T2==c2})"
              f"  T3={T3} (char0 {c3}, match={T3==c3})")
        print(f"      mass floors: n^4/p={floor2:.2f} <= T2 OK={T2>=floor2},"
              f" n^6/p={floor3:.2f} <= T3 OK={T3>=floor3};"
              f"  M(partial-scan)={M:.2f}, sqrt(n ln(p/n))={math.sqrt(n*math.log(p/n)):.2f}")

# ----------------------------------------------------------------------------
# verdict
# ----------------------------------------------------------------------------
print()
print(LINE)
print("VERDICT (decision rule of the lane brief)")
print(LINE)
print("""
1. Route to 1/2: REFUTED for the method shape.  Over ALL finishers (moment/bilinear/
   trilinear/quadrilinear), ALL fold orders, ALL Hoelder splittings, and ALL LEGAL energy
   inputs (t_k >= max(k, 2k-beta), forced by the CS mass floor T_k >= n^{2k}/p):
       theta_min(beta) = 1 - 1/(2 beta);   theta_min(4) = 7/8 = 0.875  >>  1/2.
   Binding inequality: the char-p mean-count floor at depth k = beta.  Any sub-7/8
   exponent needs char-0-clean T_k at depth k > beta, and theta -> 1/2 needs depth
   k ~ log p  ==  the BGK wall (circular, as anticipated).
2. BUT the plateau 0.9583 is NOT the method cap.  The sweep finds bilinear (3,3):
   M <= n^{8/9+o(1)} = n^{0.8889} at beta=4 from the SAME good-prime T3 input as the
   campaign 0.9583, finishing with the unconditional sqrt(p) DFT norm instead of the
   trilinear PS lemma.  With the OPEN critical-depth input T4 = O(n^4): 7/8 = 0.875.
   Both are good-prime-conditional (D3/D4 bad-prime sets), high side of the wall,
   NOT prize closure.
3. beta-dependence: legal infimum 1-1/(2beta) = 0.875 / 0.8889 / 0.90 at beta = 4 / 4.5 / 5;
   proven-input best (bilinear (3,3)) = (6-beta)/18 saving, dies at beta=6 (vs trilinear
   at beta=7); thin limit: infimum -> 1.
""")

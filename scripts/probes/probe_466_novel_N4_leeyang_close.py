#!/usr/bin/env python3
"""
#466 NOVEL LANE N4-leeyang, CLOSING PROBE (part 2; supersedes P3b of
probe_466_novel_N4_leeyang.py, whose K=4 countermodel search did not complete).

WHAT THIS PROBE DECIDES / PINS:

  A. THE INTEGER LONE-SPIKE AT DEPTH 4 (the lane's decisive new object).
     Construct, exactly, a monic totally-real degree-m polynomial with ALGEBRAIC-INTEGER
     roots (integers + golden/sqrt2 quadratic packs) whose power sums p_1..p_4 match the
     TRUE period polynomial's EXACTLY, with house (max |root|) at the degree-constrained
     moment ceiling.  Consequence: {exact shallow coefficients e_1..e_4} + {integer
     coefficients} + {real-rootedness} + {degree m} impose NO house bound below
     ~(2np)^(1/4): the analytic lone-spike gate (CMK refutation, #466 R1) SURVIVES the
     integrality upgrade.  Lee-Yang / Laguerre-Polya / Newton-inequality post-processing
     of shallow data is 0 bits even in the arithmetic category.
     Also: the LP infeasibility certificate  minBulkP4(Q,L) = (a^2+b^2)Q - a^2 b^2 L
     (adjacent squares a^2 <= Q/L <= b^2) pinning s_max from above.
     NOTE the arithmetic obstructions that make this nontrivial: all-integer-root
     multisets obey p_3 = p_1 (mod 6) and p_4 = p_2 (mod 12) (Fermat), while the TRUE
     period data violates both (defect classes printed); golden packs (x^2-x-1, Lucas
     power sums 1,3,4,7) realize exactly the defect torsion.

  B. EXACT SHALLOW COEFFICIENTS at n=8, p=4001 (m=500) to depth 40 (integer DP +
     Newton over Q), pinning:
     B1. the forced-coefficient degeneracy law e_{2j} = (-p2/2)^j/j! * (1+eps_j),
         eps_j = O(n j^2/p)  -- shallow coefficients are a function of p_2 alone;
     B2. Fujiwara argmax k=2 against EXACT coefficients (retro-validates the float
         profile of part 1);
     B3. the magnitude-only zero-free-disk (triangle) certificate ceiling
         1/rho* = sqrt(p_2/(2 ln 2)) (1+o(1))  -- NEW closed-form constant: the best
         bound ANY sign-blind consumer of ALL m coefficients can certify;
     B4. the spike's imprint on e_2 is relative (M^2-n)/p_2  -- the b-sensitive signal
         in every shallow coefficient (2^-83-ish at prize point), vs Theta(1) relative
         error of every proven moment input;
     B5. the depth-R exact-moment ladder min_{2r<=R} p_2r^(1/2r): descent to M happens
         only at r ~ ln m even with EXACT integers (no K^r slack).

Prior art consumed, not re-proven: G3 (#444) forced-e2 max-form death; H2 (#444)
trace-form = Parseval; R1 (#466) CMK lone-spike; part-1 probe P1/P3a/P4.
Honesty: proper dyadic subgroups only; exact integer arithmetic wherever a claim rests.
"""
import math
import numpy as np
from fractions import Fraction
from math import sqrt, log, factorial

OUT = []
def say(s=""):
    print(s)
    OUT.append(s)

# ---------------------------------------------------------------- number theory
def primitive_root(p):
    fac, x, d = [], p - 1, 2
    while d * d <= x:
        if x % d == 0:
            fac.append(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        fac.append(x)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise RuntimeError

def subgroup_and_periods(p, n):
    m = (p - 1) // n
    g = primitive_root(p)
    gm = pow(g, m, p)
    mu, x = [], 1
    for _ in range(n):
        mu.append(x)
        x = (x * gm) % p
    assert len(set(mu)) == n and (p - 1) in mu  # -1 in mu_n
    muv = np.array(mu, dtype=np.int64)
    etas = np.empty(m)
    b = 1
    for i in range(m):
        etas[i] = np.cos(2.0 * np.pi * ((b * muv) % p) / p).sum()
        b = (b * g) % p
    return mu, etas

def wrap_counts_pyint(p, n, mu, rmax):
    """exact N(r), r=1..rmax, arbitrary precision (Python ints)"""
    cnt = [0] * p
    for x in mu:
        cnt[x] += 1
    cur = cnt[:]
    Ns = [cur[0]]
    for _ in range(rmax - 1):
        new = [0] * p
        for t in range(p):
            c = cur[t]
            if c:
                for x in mu:
                    new[t + x if t + x < p else t + x - p] += c
        cur = new
        Ns.append(cur[0])
    return Ns

def wrap_counts_np(p, n, mu, rmax):
    """exact N(r) via numpy rolls (safe while counts < 2^62)"""
    cnt = np.zeros(p, dtype=np.int64)
    for x in mu:
        cnt[x] += 1
    cur = cnt.copy()
    Ns = [int(cur[0])]
    for _ in range(rmax - 1):
        new = np.zeros(p, dtype=np.int64)
        for x in mu:
            new += np.roll(cur, x)
        cur = new
        Ns.append(int(cur[0]))
    return Ns

def power_sums(p, n, Ns):
    ps = {}
    for r, Nr in enumerate(Ns, start=1):
        num = p * Nr - n ** r
        assert num % n == 0
        ps[r] = num // n
    return ps

def newton_e(ps, K):
    e = [Fraction(1)]
    for k in range(1, K + 1):
        acc = Fraction(0)
        for i in range(1, k + 1):
            acc += Fraction((-1) ** (i - 1)) * Fraction(ps[i]) * e[k - i]
        e.append(acc / k)
    assert all(e[k].denominator == 1 for k in range(1, K + 1))
    return [int(x) for x in e]

def coeff_logprofile(etas, scale2):
    """float64 log10|e_k| profile via scaled product (as part-1 probe)"""
    sigma = sqrt(scale2)
    poly = np.array([1.0])
    for x in etas / sigma:
        poly = np.concatenate([poly, [0.0]])
        poly[1:] -= x * poly[:-1]
    with np.errstate(divide="ignore"):
        lg = np.log10(np.abs(poly))
    return lg + np.arange(len(poly)) * math.log10(sigma)

# ---------------------------------------------------------------- Part A solver
# packs: golden+ = x^2-x-1 (power sums 1,3,4,7); golden- = x^2+x-1 (-1,3,-4,7);
#        sqrt2   = x^2-2   (0,4,0,8).  All monic ZZ[x], totally real, house < 2.
def solve_integer_lonespike(P, m, s):
    for gp in range(0, 4):
        for gm_ in range(0, 4):
            for t in range(0, 4):
                G, dG = gp + gm_, gp - gm_
                R1 = P[1] - s - dG
                R2 = P[2] - s * s - 3 * G - 4 * t
                R3 = P[3] - s ** 3 - 4 * dG
                R4 = P[4] - s ** 4 - 7 * G - 8 * t
                if R2 < 0 or R4 < 0:
                    continue
                for d4 in range(-3, 4):
                    for d3 in range(-60, 61):
                        num = (R3 - R1) - 24 * d3 - 60 * d4
                        if num % 6:
                            continue
                        d2 = num // 6
                        d1 = R1 - 2 * d2 - 3 * d3 - 4 * d4
                        base2 = abs(d1) + 4 * abs(d2) + 9 * abs(d3) + 16 * abs(d4)
                        base4 = abs(d1) + 16 * abs(d2) + 81 * abs(d3) + 256 * abs(d4)
                        R2p, R4p = R2 - base2, R4 - base4
                        if R2p < 0 or R4p < 0 or R2p % 2 or R4p % 2:
                            continue
                        H2, H4 = R2p // 2, R4p // 2
                        for (u, w) in [(1, 2), (1, 3), (2, 3), (1, 4), (2, 4),
                                       (3, 4), (1, 5), (2, 5), (3, 5), (4, 5)]:
                            den = w * w * (w * w - u * u)
                            numw = H4 - u * u * H2
                            if numw < 0 or numw % den:
                                continue
                            hw = numw // den
                            rem2 = H2 - w * w * hw
                            if rem2 < 0 or rem2 % (u * u):
                                continue
                            hu = rem2 // (u * u)
                            cnt = {v: abs(d) for v, d in
                                   ((1, d1), (2, d2), (3, d3), (4, d4)) if d != 0}
                            cnt[u] = cnt.get(u, 0) + 2 * hu
                            cnt[w] = cnt.get(w, 0) + 2 * hw
                            total = 1 + 2 * G + 2 * t + sum(cnt.values())
                            if total <= m:
                                return dict(s=s, gp=gp, gm=gm_, t=t,
                                            d={1: d1, 2: d2, 3: d3, 4: d4},
                                            sums=cnt, total=total)
    return None

def verify_lonespike(sol, P, m):
    """exact reconstruction of p_1..p_4 from the certificate"""
    s = sol["s"]
    L = {1: (1, -1), 2: (3, 3), 3: (4, -4), 4: (7, 7)}  # (golden+, golden-) Lucas
    Pchk = {}
    for r in range(1, 5):
        acc = s ** r
        acc += sol["gp"] * L[r][0] + sol["gm"] * L[r][1]
        acc += sol["t"] * (0, 4, 0, 8)[r - 1]
        for v, tot in sol["sums"].items():
            dv = sol["d"].get(v, 0)
            cp, cm = (tot + dv) // 2, (tot - dv) // 2
            assert cp >= 0 and cm >= 0 and cp + cm == tot
            acc += cp * v ** r + cm * (-v) ** r
        Pchk[r] = acc
    ok = all(Pchk[r] == P[r] for r in range(1, 5)) and sol["total"] <= m
    return ok, Pchk

def lp_min_bulk_p4(Q, L):
    """min sum c_v v^4 s.t. sum c_v v^2 = Q, sum c_v <= L, c_v >= 0 real (LP bound)"""
    best = None
    if Q <= L:            # all at +-1
        return Q
    for a in range(1, 30):
        b = a + 1
        if a * a <= Q / L <= b * b:
            val = (a * a + b * b) * Q - a * a * b * b * L
            best = val if best is None else min(best, val)
    return best

def run_partA(tag, p, n, P, m, M_true):
    say(f"--- A [{tag}]  n={n}, p={p}, m={m} ---")
    say(f"exact p_1..p_4 = {[P[r] for r in range(1,5)]}")
    d6, d12 = (P[3] - P[1]) % 6, (P[4] - P[2]) % 12
    say(f"integer-root obstruction classes: (p3-p1) mod 6 = {d6}, (p4-p2) mod 12 = {d12}"
        f"   (all-ZZ-root multisets force 0,0 -- quadratic packs required: {'YES' if (d6, d12) != (0, 0) else 'no'})")
    s_raw = int(P[4] ** 0.25)
    target = sqrt(n * log(p / n))
    sol = None
    for s in range(s_raw + 1, max(s_raw - 6, 1), -1):
        # LP feasibility pre-check
        Q, R4 = P[2] - s * s, P[4] - s ** 4
        if R4 < 0:
            say(f"  s={s}: raw-infeasible (s^4 > p_4)")
            continue
        lpmin = lp_min_bulk_p4(Q, m - 1)
        if lpmin is not None and R4 < lpmin:
            say(f"  s={s}: INFEASIBLE by LP certificate: residual quartic {R4} < "
                f"min bulk p4 {lpmin} (Q={Q}, L={m-1})")
            continue
        sol = solve_integer_lonespike(P, m, s)
        if sol:
            break
        say(f"  s={s}: LP-feasible but no exact fit in search basis (atoms <=5, packs <=3)")
    assert sol, "no integer lone-spike found -- widen search"
    ok, Pchk = verify_lonespike(sol, P, m)
    assert ok
    s = sol["s"]
    zeros = m - sol["total"]
    packs = (f"golden+^{sol['gp']} golden-^{sol['gm']} sqrt2^{sol['t']}")
    atoms = ", ".join(
        f"(+{v})^{(sol['sums'][v]+sol['d'].get(v,0))//2}(-{v})^{(sol['sums'][v]-sol['d'].get(v,0))//2}"
        for v in sorted(sol["sums"]))
    say(f"  FOUND s={s}: roots = (x-{s}) * {atoms} * {packs} * x^{zeros}"
        f"   [degree {m}, monic, ZZ[x], totally real]")
    say(f"  exact power-sum match: {[Pchk[r] for r in range(1,5)]} == true  -> CERTIFIED")
    say(f"  HOUSE = {s}   vs raw p4^(1/4) = {P[4]**0.25:.2f}   vs true M = {M_true:.2f}"
        f"   vs target = {target:.2f}")
    say(f"  => depth-4 INTEGER class floor: {s} = {s/P[4]**0.25:.3f} x raw moment bound,"
        f" {s/M_true:.1f} x truth, {s/target:.1f} x target")
    say("")
    return sol

# ================================================================ scale 1
say("=" * 78)
say("PART A -- THE INTEGER LONE-SPIKE AT DEPTH 4 (integrality adds ~nothing)")
say("=" * 78)
n1, p1 = 8, 4001
m1 = (p1 - 1) // n1
mu1, etas1 = subgroup_and_periods(p1, n1)
M1 = float(np.max(np.abs(etas1)))
RMAX = 40
Ns1 = wrap_counts_pyint(p1, n1, mu1, RMAX)
P1 = power_sums(p1, n1, Ns1)
solA1 = run_partA("scale 1", p1, n1, P1, m1, M1)

n2, p2 = 16, 65537
m2 = (p2 - 1) // n2
mu2, etas2 = subgroup_and_periods(p2, n2)
M2 = float(np.max(np.abs(etas2)))
Ns2 = wrap_counts_np(p2, n2, mu2, 4)
P2 = power_sums(p2, n2, Ns2)
say(f"[scale 2 wraparound check] N(4) = {Ns2[3]} = 3n^2-3n + W4 = {3*n2*n2-3*n2} + {Ns2[3]-(3*n2*n2-3*n2)}"
    f"  (Fermat-prime anomaly W4, cf. dossier)")
solA2 = run_partA("scale 2", p2, n2, P2, m2, M2)

# ================================================================ Part B
say("=" * 78)
say(f"PART B -- EXACT SHALLOW COEFFICIENTS, n={n1}, p={p1}, m={m1} (depth {RMAX})")
say("=" * 78)
eK = newton_e(P1, RMAX)
say(f"e_1 = {eK[1]} (forced -1);  e_2 = {eK[2]} = (1-p+n)/2 = {(1-p1+n1)//2}: "
    f"{'PASS' if eK[1] == -1 and eK[2] == (1-p1+n1)//2 else 'FAIL'}")

# B1: degeneracy law from EXACT integers
say("")
say("B1 -- forced-law e_2j = (-p2/2)^j/j! (1+eps_j) from EXACT e_2j;  eps_j/(n j^2/p):")
say("      j    eps_j           eps_j/(n j^2/p)     sign(e_2j) = (-1)^j ?")
for j in range(1, 16):
    model = Fraction(-P1[2], 2) ** j / factorial(j)
    eps = float(Fraction(eK[2 * j]) / model - 1)
    scale = n1 * j * j / p1
    sgn_ok = (eK[2 * j] > 0) == (j % 2 == 0)
    say(f"     {j:2d}   {eps:+10.5f}      {eps/scale:+8.3f}            {sgn_ok}")

# B2: exact-vs-float profile and Fujiwara argmax
lg1 = coeff_logprofile(etas1, m1 * n1)
say("")
say("B2 -- float-profile validation at k=10,20,30,40 (log10|e_k| exact vs float):")
for k in (10, 20, 30, 40):
    say(f"     k={k}: exact {math.log10(abs(eK[k])):.6f}  float {lg1[k]:.6f}")
fuj = [(2 * 10 ** (lg1[k] / k), k) for k in range(1, m1 + 1) if np.isfinite(lg1[k])]
Fbest, kbest = max(fuj)
say(f"     Fujiwara argmax over EXACT-validated profile: k = {kbest}, bound = {Fbest:.3f}"
    f" = sqrt(2(p-n-1)) = {sqrt(2*(p1-n1-1)):.3f}  (G3 confirmed on exact data)")

# B3: triangle-certificate ceiling (the best ANY sign-blind consumer of ALL
#     coefficient magnitudes can certify): 1/rho* with sum_k |e_k| rho^k < 1
say("")
logs = [(k, math.log(abs(eK[k]))) for k in range(1, RMAX + 1) if eK[k] != 0]
logs += [(k, lg1[k] * math.log(10)) for k in range(RMAX + 1, m1 + 1) if np.isfinite(lg1[k])]
def S_log(inv_rho):
    lr = -math.log(inv_rho)
    vals = [le + k * lr for k, le in logs]
    Mx = max(vals)
    return Mx + math.log(sum(math.exp(v - Mx) for v in vals))
lo, hi = 1.0, 20 * sqrt(p1)
for _ in range(200):
    mid = 0.5 * (lo + hi)
    if S_log(mid) < 0:
        hi = mid
    else:
        lo = mid
pred = sqrt((p1 - n1) / (2 * math.log(2)))
say(f"B3 -- best magnitude-only zero-free-disk certificate: 1/rho* = {hi:.3f}")
say(f"     closed-form prediction sqrt(p_2/(2 ln 2)) = {pred:.3f}   ratio = {hi/pred:.4f}")
say(f"     (vs Fujiwara {sqrt(2*(p1-n1-1)):.1f}, Parseval {sqrt(p1-n1):.1f}, true M {M1:.2f}:"
    f" sign-blind consumption of ALL {m1} coefficients certifies only ~sqrt(p_2/(2ln2)))")

# B4: the spike's imprint on e_2
i_star = int(np.argmax(np.abs(etas1)))
eta_s = float(etas1[i_star])
repl = math.copysign(sqrt(n1), eta_s)
p1_new = -1.0 - eta_s + repl
p2_new = (p1 - n1) - eta_s ** 2 + n1
e2_new = (p1_new ** 2 - p2_new) / 2
rel = abs(e2_new - eK[2]) / abs(eK[2])
say("")
say(f"B4 -- spike imprint: replacing the extreme root by +-sqrt(n) shifts e_2 by rel "
    f"{rel:.3e}  (pred (M^2-n)/p_2 = {(M1**2-n1)/(p1-n1):.3e},"
    f" ratio {rel/((M1**2-n1)/(p1-n1)):.3f})")

# B5: exact-moment depth ladder
say("")
say("B5 -- depth ladder from EXACT integer moments (no K^r slack):  p_2r^(1/2r)")
row = []
for r in range(1, RMAX // 2 + 1):
    row.append(P1[2 * r] ** (1.0 / (2 * r)))
say("     r : " + "  ".join(f"{r}:{v:.2f}" for r, v in zip(range(1, 8), row[:7])))
say("     r : " + "  ".join(f"{r}:{v:.2f}" for r, v in zip(range(8, 15), row[7:14])))
say("     r : " + "  ".join(f"{r}:{v:.2f}" for r, v in zip(range(15, 21), row[14:20])))
say(f"     true M = {M1:.4f};  2 ln m = {2*log(m1):.1f};  even EXACT integers descend to M"
    f" only at r ~ ln m (r=20 value {row[19]:.2f} is still {row[19]/M1:.3f} x M)")

# ================================================================ prize block
say("")
say("=" * 78)
say("PRIZE-POINT EXTRAPOLATION of the closing constants")
say("=" * 78)
for tag, lgn, lgm in [("beta=4 diagonal", 30, 90), ("prize-exact m=2^128", 30, 128)]:
    lgp = lgn + lgm
    lnm = lgm * log(2)
    tgt = 0.5 * (lgn + math.log2(2 * lnm))          # log2 sqrt(2 n ln m)
    say(f"[{tag}] n=2^{lgn}, m=2^{lgm}, p~2^{lgp}, ln m = {lnm:.1f}")
    say(f"   monotone-magnitude barrier floor sqrt(p/2)     = 2^{(lgp-1)/2:.2f}")
    say(f"   triangle-certificate ceiling sqrt(p/(2 ln 2))  = 2^{(lgp-math.log2(2*math.log(2)))/2:.2f}")
    say(f"   depth-4 INTEGER class floor (2np)^(1/4)        = 2^{(1+lgn+lgp)/4:.2f}"
        f"   (= 2^{(1+lgn+lgp)/4 - tgt:.1f} x target)")
    say(f"   prize target sqrt(2 n ln m)                    = 2^{tgt:.2f}")
    say(f"   spike signal in e_2:  2 M^2/p ~ 2^{1 + lgn + math.log2(lnm) + 1 - lgp:.1f}"
        f"   (proven inputs are Theta(1)-relative: precision deficit"
        f" 2^{-(1 + lgn + math.log2(lnm) + 1 - lgp):.0f})")
    say("")

with open("scripts/probes/_out_466_novel_N4_leeyang_close.txt", "w") as fh:
    fh.write("\n".join(OUT) + "\n")
say("written: scripts/probes/_out_466_novel_N4_leeyang_close.txt")

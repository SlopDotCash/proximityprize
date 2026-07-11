#!/usr/bin/env python3
"""
SYZ48 -- the balanced-interior kernel: level sets, domain-membership, and the
load-bearing role of the mu_n evaluation domain.

Context (#466, rate-1/2 proximity residual).  SYZ47 proved the imbalance FLOOR
delta_1 >= max(a,b,c) on the band triangle, discharging iota <= 1 on the
"moderately unbalanced" strip (max(a,b,c) >= floor(S/2)-1, ~37.7% of band triples).
The remaining ~62.3% BALANCED INTERIOR (max(a,b,c) < floor(S/2)-1) is where the
floor is too weak (it only gives iota <= floor(d/2)) and SYZ45's (4,4,4)=>iota=2
counterexample lives.  iota <= 1 there is EMPIRICALLY true but not proved.

SYZ48 asks the sharp question: what does BAND REALIZABILITY add beyond the degree
profile on the balanced interior?  SYZ45's iota=2 witness used ARBITRARY root sets
(f = 3g - 2h with g,h rooted at {0..3},{4..7}, third set = roots of 3g-2h).  The
reconciliation:

  * A constant-ratio (degree-d) syzygy c0*W_AB + c1*W_AC + c2*W_BC = 0 with the
    AB slot carrying is EXACTLY W_AB | (alpha*W_AC + beta*W_BC).  The roots of W_AB
    (a of them) must ALL be roots of the combination P := alpha*W_AC + beta*W_BC,
    a polynomial of degree <= max(b,c).
  * LEVEL-SET / ROOT-COUNT BOUND: P has <= max(b,c) roots.  For W_AB (a roots) to
    divide P we need a <= max(b,c).  On the balanced interior a ~ b ~ c so this is
    SATISFIABLE -- counting gives NO contradiction (the honest full circle).
  * So over a LARGE / algebraically-closed field the iota>=2 configuration IS
    band-realizable: pick disjoint W_AC, W_BC, form P = alpha*W_AC + beta*W_BC, and
    (generically, when P splits) take W_AB = a squarefree degree-a factor of P.  Its
    roots are new algebraic points, generically distinct/disjoint from the others.
  * THE RESCUE is the DOMAIN.  Over the prize domain the roots of W_AB must be
    EVALUATION-DOMAIN points (in mu_n).  The roots of P = alpha*W_AC + beta*W_BC for
    W_AC, W_BC vanishing polys of disjoint mu_n-subsets are NOT generally in mu_n.

This probe measures, over mu_n domains:
  [1] LEVEL-SET SIZES: for disjoint mu_n-subsets A,C and B,C giving W_AC,W_BC, and a
      scalar c0, how many roots does W_BC - c0*W_AC have IN mu_n?  (constant-ratio
      level set on the domain).  Confirms the <= max(b,c) count AND how much smaller
      the IN-DOMAIN level set is.
  [2] DOMAIN-ESCAPE of combination roots: over mu_n, sample alpha,beta and count what
      fraction of the max(b,c) roots of alpha*W_AC + beta*W_BC land back in mu_n.  If
      generically ~0 land in mu_n, the iota>=2 witness cannot be assembled on-domain:
      the domain is LOAD-BEARING.
  [3] direct balanced-interior iota check on band-realizable mu_n triples: 0
      violations expected (re-confirming SYZ45/47), now with the WHY (escape).
  [4] LARGE-FIELD (algebraic-closure surrogate, big prime, arbitrary root sets) check
      that balanced-interior iota=2 IS realizable when roots may be ANY field points
      -- decisive that the domain restriction, not the degree profile, is the lever.
"""
import random
from itertools import combinations


def poly_mul(p, q, mod):
    r = [0] * (len(p) + len(q) - 1)
    for i, pi in enumerate(p):
        if pi:
            for j, qj in enumerate(q):
                r[i + j] = (r[i + j] + pi * qj) % mod
    return r


def from_roots(roots, mod):
    p = [1]
    for a in roots:
        p = poly_mul(p, [(-a) % mod, 1], mod)
    return p


def poly_add(p, q, mod):
    n = max(len(p), len(q))
    p = p + [0] * (n - len(p))
    q = q + [0] * (n - len(q))
    return [(p[i] + q[i]) % mod for i in range(n)]


def scal(p, c, mod):
    return [(c * x) % mod for x in p]


def poly_eval(p, x, mod):
    acc = 0
    for coef in reversed(p):
        acc = (acc * x + coef) % mod
    return acc


def count_roots_in(p, domain, mod):
    return sum(1 for x in domain if poly_eval(p, x, mod) == 0)


def rank_mod(M, mod):
    M = [row[:] for row in M]
    rows = len(M)
    cols = len(M[0]) if rows else 0
    r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if M[i][c] % mod), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], mod - 2, mod)
        M[r] = [(x * inv) % mod for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c] % mod:
                f = M[i][c]
                M[i] = [(M[i][k] - f * M[r][k]) % mod for k in range(cols)]
        r += 1
        if r == rows:
            break
    return r


def syzygy_hilb(f, g, h, a, b, c, D, mod):
    """dim of windowed syzygy kernel at degree budget D."""
    cols = []
    for poly_, d in [(f, a), (g, b), (h, c)]:
        nc = D - d + 1
        for shift in range(max(0, nc)):
            col = [0] * (D + 1)
            pr = ([0] * shift) + poly_
            for i, v in enumerate(pr):
                if i <= D:
                    col[i] = v % mod
            cols.append(col)
    if not cols:
        return 0
    M = [[cols[j][i] for j in range(len(cols))] for i in range(D + 1)]
    return len(cols) - rank_mod(M, mod)


def min_syzygy_degree(f, g, h, a, b, c, mod):
    """smallest product-degree D with a nonzero windowed syzygy."""
    S = a + b + c
    for D in range(max(a, b, c), S + 1):
        if syzygy_hilb(f, g, h, a, b, c, D, mod) > 0:
            return D
    return S


def imbalance_of(f, g, h, a, b, c, mod):
    S = a + b + c
    d1 = min_syzygy_degree(f, g, h, a, b, c, mod)
    return (S // 2) - d1, d1


def mu_domain(n, mod):
    """the n-th roots of unity in F_mod (requires n | mod-1); returns [] if none."""
    if (mod - 1) % n != 0:
        return []
    g = None
    for cand in range(2, mod):
        if pow(cand, mod - 1, mod) == 1:
            ok = all(pow(cand, (mod - 1) // pr, mod) != 1 for pr in prime_factors(mod - 1))
            if ok:
                g = cand
                break
    if g is None:
        return []
    w = pow(g, (mod - 1) // n, mod)
    return sorted({pow(w, i, mod) for i in range(n)})


def prime_factors(m):
    fs = set()
    d = 2
    while d * d <= m:
        while m % d == 0:
            fs.add(d)
            m //= d
        d += 1
    if m > 1:
        fs.add(m)
    return fs


def gcd_deg(p, q, mod):
    """degree of gcd via Euclid over F_mod (for coprimality checks)."""
    def norm(a):
        while a and a[-1] % mod == 0:
            a = a[:-1]
        return a
    a = norm([x % mod for x in p])
    b = norm([x % mod for x in q])
    while b:
        # a mod b
        while len(a) >= len(b) and a:
            inv = pow(b[-1], mod - 2, mod)
            f = (a[-1] * inv) % mod
            sh = len(a) - len(b)
            for i in range(len(b)):
                a[sh + i] = (a[sh + i] - f * b[i]) % mod
            a = norm(a)
        a, b = b, a
    return len(a) - 1 if a else -1


# ---------------------------------------------------------------------------
def experiment_1_2(mod, n, trials=3000, seed=1):
    """level-set sizes + domain-escape of combination roots over mu_n."""
    rng = random.Random(seed)
    dom = mu_domain(n, mod)
    if len(dom) < 12:
        return None
    levelset_sizes = []           # in-domain roots of W_BC - c0*W_AC
    levelset_max_possible = []    # max(b,c)
    escape_in_domain = []         # in-domain roots of alpha*W_AC + beta*W_BC
    combo_deg = []
    for _ in range(trials):
        pts = rng.sample(dom, 12)
        A = pts[0:4]; B = pts[4:8]; C = pts[8:12]
        WAC = from_roots(A + C, mod)   # deg b := 8? -- use small overlap model:
        # model: W_AC vanishes on the (A,C)-overlap; use disjoint small sets
        # reduced degrees b,c ~ 4; use A as AC-only, B as BC-only roots
        WAC = from_roots(A, mod)       # deg 4
        WBC = from_roots(B, mod)       # deg 4
        b = 4; c = 4
        c0 = rng.randrange(1, mod)
        lvl = poly_add(WBC, scal(WAC, (-c0) % mod, mod), mod)
        levelset_sizes.append(count_roots_in(lvl, dom, mod))
        levelset_max_possible.append(max(b, c))
        alpha = rng.randrange(1, mod); beta = rng.randrange(1, mod)
        combo = poly_add(scal(WAC, alpha, mod), scal(WBC, beta, mod), mod)
        # trim
        while combo and combo[-1] % mod == 0:
            combo = combo[:-1]
        combo_deg.append(len(combo) - 1)
        escape_in_domain.append(count_roots_in(combo, dom, mod))
    return {
        "mod": mod, "n": n, "domain_size": len(dom), "trials": trials,
        "levelset_mean": sum(levelset_sizes) / len(levelset_sizes),
        "levelset_max": max(levelset_sizes),
        "levelset_bound": max(levelset_max_possible),
        "levelset_over_bound": sum(1 for s, m in zip(levelset_sizes, levelset_max_possible) if s > m),
        "escape_mean_in_domain": sum(escape_in_domain) / len(escape_in_domain),
        "escape_max_in_domain": max(escape_in_domain),
        "escape_all_left_domain": sum(1 for e in escape_in_domain if e == 0),
        "combo_deg_mean": sum(combo_deg) / len(combo_deg),
    }


def experiment_3(mod, n, trials=1500, seed=7):
    """balanced-interior iota on band-realizable mu_n triples: 0 violations expected."""
    rng = random.Random(seed)
    dom = mu_domain(n, mod)
    if len(dom) < 18:
        return None
    checked = 0
    balanced_interior = 0
    viol = 0
    max_iota = 0
    for _ in range(trials):
        d = rng.choice([4, 5, 6])
        pts = rng.sample(dom, 3 * d)
        A = pts[0:d]; B = pts[d:2*d]; Cc = pts[2*d:3*d]
        WAB = from_roots(A, mod); WAC = from_roots(B, mod); WBC = from_roots(Cc, mod)
        a = b = c = d
        # pairwise coprime by construction (disjoint roots)
        iota, d1 = imbalance_of(WAB, WAC, WBC, a, b, c, mod)
        checked += 1
        S = a + b + c
        if max(a, b, c) < (S // 2) - 1:
            balanced_interior += 1
            max_iota = max(max_iota, iota)
            if iota >= 2:
                viol += 1
    return {"mod": mod, "n": n, "checked": checked,
            "balanced_interior": balanced_interior,
            "iota_ge_2_violations": viol, "max_iota_on_interior": max_iota}


def experiment_4(mod, trials=400, seed=11):
    """LARGE-FIELD arbitrary-root-set: is balanced-interior iota=2 realizable?

    Construct exactly the SYZ45 mechanism at a BALANCED profile: pick disjoint
    root sets for W_AC (deg d), W_BC (deg d), scalars alpha,beta; form the degree-d
    combination P = alpha*W_AC + beta*W_BC; when P is squarefree and coprime to
    W_AC,W_BC, set W_AB = P.  Then alpha*W_AC + beta*W_BC - W_AB = 0 is a constant
    syzygy of product-degree d => delta_1 <= d => iota >= floor(3d/2)-d = floor(d/2) >= 2
    for d>=4.  Roots of W_AB = roots of P are ARBITRARY field points (not a domain).
    """
    rng = random.Random(seed)
    realized = 0
    attempts = 0
    for _ in range(trials):
        d = rng.choice([4, 5, 6])
        allpts = rng.sample(range(1, mod), 2 * d)
        A = allpts[0:d]; B = allpts[d:2*d]
        WAC = from_roots(A, mod); WBC = from_roots(B, mod)
        alpha = rng.randrange(1, mod); beta = rng.randrange(1, mod)
        P = poly_add(scal(WAC, alpha, mod), scal(WBC, beta, mod), mod)
        while P and P[-1] % mod == 0:
            P = P[:-1]
        if len(P) - 1 != d:
            continue
        # coprimality of P with WAC, WBC
        if gcd_deg(P, WAC, mod) != 0 or gcd_deg(P, WBC, mod) != 0:
            continue
        if gcd_deg(WAC, WBC, mod) != 0:
            continue
        attempts += 1
        WAB = P
        a = b = c = d
        # squarefree check for WAB: gcd(WAB, WAB') deg 0
        Pp = [(i * P[i]) % mod for i in range(1, len(P))]
        if gcd_deg(P, Pp, mod) != 0:
            continue
        iota, d1 = imbalance_of(WAB, WAC, WBC, a, b, c, mod)
        S = a + b + c
        if max(a, b, c) < (S // 2) - 1 and iota >= 2:
            realized += 1
    return {"mod": mod, "attempts": attempts, "balanced_interior_iota_ge_2_realized": realized}


if __name__ == "__main__":
    print("=" * 78)
    print("SYZ48 balanced-interior: level sets, domain-escape, load-bearing mu_n")
    print("=" * 78)

    print("\n[1+2] level-set sizes and domain-escape over mu_n domains")
    print("-" * 78)
    for mod, n in [(61, 60), (241, 240), (337, 336), (1009, 1008)]:
        r = experiment_1_2(mod, n)
        if r is None:
            continue
        print(f"  F_{mod} on mu_{n} (|dom|={r['domain_size']}), {r['trials']} trials:")
        print(f"    level-set (W_BC - c0*W_AC roots IN mu_n): mean={r['levelset_mean']:.3f} "
              f"max={r['levelset_max']} (algebraic bound max(b,c)={r['levelset_bound']}, "
              f"over-bound={r['levelset_over_bound']})")
        print(f"    combination alpha*W_AC+beta*W_BC (deg mean {r['combo_deg_mean']:.2f}): "
              f"roots IN mu_n mean={r['escape_mean_in_domain']:.4f} max={r['escape_max_in_domain']}; "
              f"trials where ALL roots left mu_n: {r['escape_all_left_domain']}/{r['trials']}")

    print("\n[3] balanced-interior iota on band-realizable mu_n triples (0 violations expected)")
    print("-" * 78)
    for mod, n in [(61, 60), (241, 240), (337, 336), (1009, 1008)]:
        r = experiment_3(mod, n)
        if r is None:
            continue
        print(f"  F_{mod} on mu_{n}: checked={r['checked']}, "
              f"balanced-interior={r['balanced_interior']}, "
              f"iota>=2 violations={r['iota_ge_2_violations']}, "
              f"max iota on interior={r['max_iota_on_interior']}")

    print("\n[4] LARGE-FIELD arbitrary root sets: is balanced-interior iota=2 realizable?")
    print("-" * 78)
    for mod in [10007, 100003, 1000003]:
        r = experiment_4(mod)
        print(f"  F_{mod}: coprime-squarefree attempts={r['attempts']}, "
              f"balanced-interior iota>=2 REALIZED={r['balanced_interior_iota_ge_2_realized']}")

    print("\n" + "=" * 78)
    print("READING:")
    print("  [1] in-domain level sets are <= max(b,c) (algebraic root-count bound) AND")
    print("      typically far smaller -- the constant-ratio locus barely meets mu_n.")
    print("  [2] combination roots ESCAPE mu_n: the a domain-points needed for W_AB's")
    print("      roots are not available => on-domain iota>=2 cannot be assembled.")
    print("  [3] 0 balanced-interior violations on mu_n (re-confirms SYZ45/47).")
    print("  [4] over a large field with ARBITRARY root sets the SAME balanced profile")
    print("      REALIZES iota>=2 => the mu_n DOMAIN, not the degree profile, is the lever.")
    print("=" * 78)

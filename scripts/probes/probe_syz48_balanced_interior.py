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
  * Over an ALGEBRAICALLY CLOSED field the iota>=2 configuration exists as an
    algebraic syzygy: pick disjoint W_AC, W_BC, form P = alpha*W_AC + beta*W_BC, and
    (when P is squarefree and coprime to W_AC, W_BC) take W_AB = P.  Its roots are new
    algebraic points.  This needs a code domain containing those roots (an extension
    field / algebraic closure with a stated new evaluation domain).
  * A FINITE PRIME FIELD F_p, however large, is NOT an algebraic closure.  Over F_p the
    roots of P are evaluation points only when P SPLITS into distinct linear factors
    over F_p.  When P has a nonsplit factor, its "missing" roots are not other F_p
    coordinates at all: this is NONSPLITTING, not "escape to other base-field points".
    In experiments [1]-[3] the domains mu_(p-1) are all of F_p^*, so the only F_p point
    outside the domain is 0; every root "leaving mu_n" there is a nonsplit (non-F_p) root.

This probe measures, over mu_n domains (both mu_(p-1) = F_p^* and proper subgroups):
  [1] LEVEL-SET SIZES: for disjoint mu_n-subsets A,C and B,C giving W_AC,W_BC, and a
      scalar c0, how many roots does W_BC - c0*W_AC have IN mu_n?  (constant-ratio
      level set on the domain).  Confirms the valid nonzero-polynomial root bound
      <= max(b,c) and records how much smaller the IN-DOMAIN level set typically is.
  [2] ROOT LOCATION of a random combination alpha*W_AC + beta*W_BC, separated into
      (i) distinct roots in mu_n, (ii) distinct roots at F_p points OFF the domain
      (genuine escape to other base-field coordinates; only 0 is available when
      mu_n = F_p^*), and (iii) degree not accounted for by distinct F_p roots
      (nonsplitting over F_p), plus the fraction of combinations that split into
      distinct F_p roots.  These are statistics of RANDOM alpha,beta and random sets:
      typicality, NOT a universal obstruction.  A universal "on-domain iota>=2 cannot
      be assembled" claim is FALSE: SYZ49 exhibits an on-domain constant-syzygy witness
      over mu_12 in F_37, and the audit fixture L127 (repository review 2026-10-28)
      gives a full-cover proper-band mu_20 in F_41 configuration with iota = 2.
  [3] balanced-interior iota check on RANDOM disjoint mu_n root triples (equal
      degrees; these are random samples, not band-realizable cores): 0 violations in
      the sample is again typicality, not a proof.
  [4] PRIME-FIELD arbitrary root sets (F_p with p large; NOT an algebraic-closure
      surrogate): count (a) algebraic constant-syzygy configurations with W_AB = P
      squarefree and coprime (nonsplit P allowed: a polynomial/syzygy fact), and
      separately (b) those where P splits into d distinct F_p roots, i.e. an actual
      F_p-point realization with evaluation domain all of F_p.  Only (b) realizes the
      configuration on F_p points.

The exact Hilbert-function / gcd / root-count computations are exact finite-field
arithmetic; neither they nor the root bound supply a splitting/realizability bridge.
No published theorem or dyadic-prize instance is refuted or confirmed by this probe.
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


def poly_trim(p, mod):
    p = [x % mod for x in p]
    while p and p[-1] == 0:
        p = p[:-1]
    return p


def poly_rem(a, m, mod):
    """remainder of a modulo the nonzero polynomial m over F_mod."""
    a = poly_trim(a, mod)
    m = poly_trim(m, mod)
    inv = pow(m[-1], mod - 2, mod)
    while len(a) >= len(m) and a:
        f = (a[-1] * inv) % mod
        sh = len(a) - len(m)
        for i in range(len(m)):
            a[sh + i] = (a[sh + i] - f * m[i]) % mod
        a = poly_trim(a, mod)
    return a


def x_pow_mod(e, m, mod):
    """X^e modulo m over F_mod (square-and-multiply)."""
    result = poly_rem([1], m, mod)
    base = poly_rem([0, 1], m, mod)
    while e:
        if e & 1:
            result = poly_rem(poly_mul(result, base, mod), m, mod) if result and base else []
        e >>= 1
        if e:
            base = poly_rem(poly_mul(base, base, mod), m, mod) if base else []
    return result


def fp_root_count(p, mod):
    """number of DISTINCT roots of the nonzero polynomial p in the prime field F_mod.

    Exact: deg gcd(p, X^mod - X), since X^mod - X is the product of all (X - x), x in F_mod.
    """
    p = poly_trim(p, mod)
    if len(p) <= 1:
        return 0
    h = poly_add(x_pow_mod(mod, p, mod), [0, mod - 1], mod)
    return gcd_deg(p, h, mod)


def splits_squarefree(p, mod):
    """p is a product of distinct linear factors over F_mod (all roots are F_mod points)."""
    p = poly_trim(p, mod)
    return len(p) >= 2 and fp_root_count(p, mod) == len(p) - 1


# ---------------------------------------------------------------------------
def experiment_1_2(mod, n, trials=3000, seed=1):
    """level-set sizes + root location (domain / off-domain F_p / nonsplit) over mu_n."""
    rng = random.Random(seed)
    dom = mu_domain(n, mod)
    if len(dom) < 12:
        return None
    levelset_sizes = []           # in-domain roots of W_BC - c0*W_AC
    levelset_max_possible = []    # max(b,c)
    escape_in_domain = []         # in-domain roots of alpha*W_AC + beta*W_BC
    off_domain_fp = []            # distinct F_p roots of the combination OUTSIDE mu_n
    nonsplit_deg = []             # degree not accounted for by distinct F_p roots
    split_count = 0               # combinations splitting into distinct F_p roots
    combo_deg = []
    for _ in range(trials):
        pts = rng.sample(dom, 12)
        A = pts[0:4]; B = pts[4:8]
        # model: reduced degrees b = c = 4; A are the AC-only roots, B the BC-only roots
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
        deg = len(combo) - 1
        combo_deg.append(deg)
        in_dom = count_roots_in(combo, dom, mod)
        in_field = fp_root_count(combo, mod)
        escape_in_domain.append(in_dom)
        off_domain_fp.append(in_field - in_dom)
        nonsplit_deg.append(deg - in_field)
        if deg >= 1 and in_field == deg:
            split_count += 1
    return {
        "mod": mod, "n": n, "domain_size": len(dom), "trials": trials,
        "domain_is_all_units": len(dom) == mod - 1,
        "off_domain_fp_mean": sum(off_domain_fp) / len(off_domain_fp),
        "off_domain_fp_trials": sum(1 for e in off_domain_fp if e > 0),
        "nonsplit_deg_mean": sum(nonsplit_deg) / len(nonsplit_deg),
        "nonsplit_trials": sum(1 for e in nonsplit_deg if e > 0),
        "split_squarefree_trials": split_count,
        "levelset_mean": sum(levelset_sizes) / len(levelset_sizes),
        "levelset_max": max(levelset_sizes),
        "levelset_bound": max(levelset_max_possible),
        "levelset_over_bound": sum(1 for s, m in zip(levelset_sizes, levelset_max_possible) if s > m),
        "escape_mean_in_domain": sum(escape_in_domain) / len(escape_in_domain),
        "escape_max_in_domain": max(escape_in_domain),
        "no_root_in_domain": sum(1 for e in escape_in_domain if e == 0),
        "combo_deg_mean": sum(combo_deg) / len(combo_deg),
    }


def experiment_3(mod, n, trials=1500, seed=7):
    """balanced-interior iota on RANDOM disjoint mu_n root triples (sampled typicality only;
    these are not band-realizable cores, and on-domain iota=2 witnesses do exist: SYZ49, L127)."""
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


def experiment_4(mod, trials=400, seed=11, keep_examples=3):
    """PRIME-FIELD arbitrary root sets: algebraic iota=2 syzygies vs F_p-point realizations.

    Construct exactly the SYZ45 mechanism at a BALANCED profile: pick disjoint
    root sets for W_AC (deg d), W_BC (deg d), scalars alpha,beta; form the degree-d
    combination P = alpha*W_AC + beta*W_BC; when P is squarefree and coprime to
    W_AC,W_BC, set W_AB = P.  Then alpha*W_AC + beta*W_BC - W_AB = 0 is a constant
    syzygy of product-degree d => delta_1 <= d => iota >= floor(3d/2)-d = floor(d/2) >= 2
    for d>=4.  That is a polynomial/syzygy fact.  W_AB is the vanishing polynomial of d
    F_p evaluation points ONLY when P splits into d distinct linear factors over F_p, so
    the F_p-point realization count additionally requires splits_squarefree(P).
    """
    rng = random.Random(seed)
    realized = 0          # algebraic configurations (nonsplit P allowed)
    split_realized = 0    # of those, P splits into d distinct F_p roots
    attempts = 0
    examples = []
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
            n_fp = fp_root_count(P, mod)
            if n_fp == d:
                split_realized += 1
            if len(examples) < keep_examples:
                examples.append({"d": d, "P": list(P), "iota": iota,
                                 "distinct_fp_roots": n_fp, "splits": n_fp == d})
    return {"mod": mod, "attempts": attempts,
            "algebraic_iota_ge_2_configurations": realized,
            "split_fp_point_realizations": split_realized,
            "examples": examples}


if __name__ == "__main__":
    print("=" * 78)
    print("SYZ48 balanced-interior: level sets, root location (domain / F_p / nonsplit)")
    print("=" * 78)

    # mu_(p-1) = F_p^* (only 0 lies off-domain in F_p) and proper subgroups mu_n < F_p^*
    DOMAINS = [(61, 60), (241, 240), (337, 336), (1009, 1008), (41, 20), (241, 60), (1009, 336)]
    print("\n[1+2] level-set sizes and combination-root location over mu_n domains")
    print("-" * 78)
    for mod, n in DOMAINS:
        r = experiment_1_2(mod, n)
        if r is None:
            continue
        kind = "= F_p^*" if r["domain_is_all_units"] else "proper subgroup of F_p^*"
        print(f"  F_{mod} on mu_{n} {kind} (|dom|={r['domain_size']}), {r['trials']} trials:")
        print(f"    level-set (W_BC - c0*W_AC roots IN mu_n): mean={r['levelset_mean']:.3f} "
              f"max={r['levelset_max']} (algebraic bound max(b,c)={r['levelset_bound']}, "
              f"over-bound={r['levelset_over_bound']})")
        print(f"    combination alpha*W_AC+beta*W_BC (deg mean {r['combo_deg_mean']:.2f}): "
              f"distinct roots IN mu_n mean={r['escape_mean_in_domain']:.4f} "
              f"max={r['escape_max_in_domain']}; no root in mu_n: "
              f"{r['no_root_in_domain']}/{r['trials']}")
        print(f"      F_p roots OFF the domain (genuine base-field escape): mean="
              f"{r['off_domain_fp_mean']:.4f}, trials={r['off_domain_fp_trials']}/{r['trials']}")
        print(f"      degree NOT in distinct F_p roots (nonsplitting over F_p): mean="
              f"{r['nonsplit_deg_mean']:.4f}, trials={r['nonsplit_trials']}/{r['trials']}; "
              f"split into distinct F_p roots: {r['split_squarefree_trials']}/{r['trials']}")

    print("\n[3] balanced-interior iota on RANDOM disjoint mu_n root triples (sampled only)")
    print("-" * 78)
    for mod, n in DOMAINS:
        r = experiment_3(mod, n)
        if r is None:
            continue
        print(f"  F_{mod} on mu_{n}: checked={r['checked']}, "
              f"balanced-interior={r['balanced_interior']}, "
              f"iota>=2 violations={r['iota_ge_2_violations']}, "
              f"max iota on interior={r['max_iota_on_interior']}")

    print("\n[4] PRIME-FIELD arbitrary root sets: algebraic iota>=2 syzygies vs split realizations")
    print("-" * 78)
    for mod in [10007, 100003, 1000003]:
        r = experiment_4(mod)
        print(f"  F_{mod}: coprime-squarefree attempts={r['attempts']}, "
              f"algebraic balanced-interior iota>=2 syzygies (nonsplit W_AB allowed)="
              f"{r['algebraic_iota_ge_2_configurations']}, of which W_AB SPLITS into d "
              f"distinct F_p points={r['split_fp_point_realizations']}")
        for ex in r["examples"][:1]:
            print(f"    first accepted trial: d={ex['d']} P={ex['P']} iota={ex['iota']} "
                  f"distinct F_p roots={ex['distinct_fp_roots']} splits={ex['splits']}")

    print("\n" + "=" * 78)
    print("READING (random-sample statistics; no universal no-go is claimed):")
    print("  [1] in-domain level sets obey the valid root bound <= max(b,c) and are")
    print("      typically much smaller for random scalars.")
    print("  [2] combination roots that are not in mu_n are, when mu_n = F_p^*, NONSPLIT")
    print("      (not F_p points at all, except possibly 0); on proper subgroups some land")
    print("      on F_p points off the domain.  This is typicality of random alpha,beta,")
    print("      NOT an obstruction: on-domain iota=2 witnesses exist (SYZ49 mu_12 in F_37;")
    print("      audit fixture L127, full-cover proper-band mu_20 in F_41).")
    print("  [3] 0 balanced-interior violations among RANDOM mu_n triples (typicality only).")
    print("  [4] the balanced profile carries algebraic iota>=2 syzygies freely; an F_p-point")
    print("      realization needs W_AB to split, which only a minority of trials do.")
    print("      A prime field is not an algebraic closure; realizing the nonsplit cases")
    print("      needs an extension field with a stated new evaluation domain.")
    print("=" * 78)

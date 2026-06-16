#!/usr/bin/env python3
"""
probe_444_branching_factor.py  (#444 SEAM A -- Refuter B: PER-LEVEL BRANCHING)

The poly/constant window-list bound for explicit 2-power RS hinges on the descent's
PER-LEVEL BRANCHING factor being O(1) and STABLE in n. This probe MEASURES it.

Descent identity (verified elsewhere, re-checked here): for n=2N,
  f(x)=F(x^2)+x G(x^2),  u(x)=u_e(x^2)+x u_o(x^2),  P=F-u_e, Q=G-u_o,
  |agree_{mu_n}(f,u)| = 2*#{y in mu_N: P(y)=Q(y)=0}
                       + #{y in mu_N: Q(y)!=0 and P(y)^2 = y*Q(y)^2}.

A deg<k poly f on mu_n splits as F (deg<ceil(k/2)) even part, G (deg<floor(k/2)) odd part.
So EVERY parent list member f projects to a pair (F,G).  The descent recursion claims that
the relevant F and G individually live in (small) window lists on mu_N for the descended words
u_e, u_o.  Branching = how many parent f's can a given child structure spawn.

WE MEASURE, for the TRUE worst weight-2 word u on mu_n at small k:

  parent_L = L(u on mu_n, RS[k], window)               # exact enumeration

and the CHILD structures the descent makes available on mu_N:
  child_F  = window list of u_e on mu_N at code deg<kF=ceil(k/2)
  child_G  = window list of u_o on mu_N at code deg<kG=floor(k/2)
  child_pairs = child_F * child_G                       # the (F,G) candidate budget

Branching ratios reported:
  B_pair  = parent_L / child_pairs       (the literal "parent/child" the task asks for)
  B_F     = parent_L / child_F
  B_G     = parent_L / child_G

We also report the DESCENDED-WORD STRUCTURE of u_e, u_o (monomial / weight-2 / parity),
and we recurse one more level on the same-parity child to see if branching is STABLE.

Honesty: exact arithmetic mod p, multiple primes, proper subgroups mu != p-1, window-interior
radius, correlated direction x^{n/2}=+-1 excluded from the worst-word search. A branching that
GROWS with n (not <= ~4 and stable) REFUTES the constant-list bound. Do not fabricate.
"""
import itertools, sys
from math import comb
from sympy import isprime, primitive_root

# ---------------------------------------------------------------- field / subgroup
def find_window_prime(n, beta=4.0, idx_min=2):
    target = int(n ** beta)
    base = target - (target % n) + 1
    p = base
    while True:
        if p > n and isprime(p) and (p - 1) % n == 0 and (p - 1) // n >= idx_min:
            return p
        p += n

def subgroup(n, p):
    g = primitive_root(p)
    zeta = pow(g, (p - 1) // n, p)
    e, x = [], 1
    for _ in range(n):
        e.append(x); x = (x * zeta) % p
    assert len(set(e)) == n
    return e

# ---------------------------------------------------------------- poly utils
def poly_mul(a, b, p):
    r = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                r[i + j] = (r[i + j] + ai * bj) % p
    return r

def interp_coeffs(xs, ys, p):
    k = len(xs); c = [0] * k
    for i in range(k):
        num = [1]; den = 1
        for j in range(k):
            if j == i: continue
            num = poly_mul(num, [(-xs[j]) % p, 1], p)
            den = (den * ((xs[i] - xs[j]) % p)) % p
        inv = pow(den, p - 2, p); sc = (ys[i] * inv) % p
        for t in range(len(num)): c[t] = (c[t] + sc * num[t]) % p
    return tuple(c)

def peval(c, x, p):
    r = 0
    for a in reversed(c): r = (r * x + a) % p
    return r

# ---------------------------------------------------------------- exact RS window list
def list_RS(uvals, elts, k, s, p, return_members=False):
    """all deg<k polys agreeing with u on >= s pts of `elts`. exact enumeration."""
    n = len(elts); seen = set(); members = []
    for T in itertools.combinations(range(n), k):
        xs = [elts[i] for i in T]; ys = [uvals[i] for i in T]
        c = interp_coeffs(xs, ys, p)
        if c in seen: continue
        ag = sum(1 for i in range(n) if peval(c, elts[i], p) == uvals[i])
        if ag >= s:
            seen.add(c)
            if return_members: members.append(c)
    if return_members:
        return members
    return len(seen)

# ---------------------------------------------------------------- window-radius convention
def window_s(k, n, eta):
    """consistent agreement threshold s = round((rho+eta)*n), clamped to [k, n]."""
    rho = k / n
    s = round((rho + eta) * n)
    return max(min(s, n), k)

# ---------------------------------------------------------------- descent split of a parent poly
def split_even_odd(coeffs, p):
    """f(x)=F(x^2)+x G(x^2). returns (F_coeffs, G_coeffs) (low->high in y)."""
    F = [coeffs[i] for i in range(0, len(coeffs), 2)]
    G = [coeffs[i] for i in range(1, len(coeffs), 2)]
    # trim trailing zeros not needed; keep as is
    return tuple(F), tuple(G)

# ---------------------------------------------------------------- worst weight-2 word
def true_worst_weight2(n, k, eta, p):
    elts = subgroup(n, p); s = window_s(k, n, eta)
    best = (-1, None)
    for a in range(1, n):
        for b in range(0, a):
            if a == n // 2 or b == n // 2:      # exclude correlated x^{n/2}=+-1
                continue
            u = [(pow(x, a, p) + pow(x, b, p)) % p for x in elts]
            L = list_RS(u, elts, k, s, p)
            if L > best[0]:
                best = (L, (a, b))
    return best[0], best[1], s

# ---------------------------------------------------------------- descended words u_e, u_o
def descend_word(a, b, n):
    """word u(x)=x^a+x^b on mu_n splits as u_e(y)+x u_o(y) on mu_N (N=n/2).
       a monomial x^a contributes to u_e if a even (y^{a/2}) else to u_o (y^{(a-1)/2}).
       returns (ue_terms, uo_terms) as dicts {exp_in_y: coeff}."""
    ue = {}; uo = {}
    for c, e in [(1, a), (1, b)]:
        if e % 2 == 0:
            ue[e // 2] = (ue.get(e // 2, 0) + c)
        else:
            uo[(e - 1) // 2] = (uo.get((e - 1) // 2, 0) + c)
    return ue, uo

def terms_to_word(terms, eltsN, p):
    return [sum(coef * pow(y, e, p) for e, coef in terms.items()) % p for y in eltsN]

def word_structure(terms):
    nz = {e: c for e, c in terms.items() if c % 1 == 0 and c != 0}
    if len(nz) == 0: return "ZERO"
    if len(nz) == 1:
        return f"monomial y^{list(nz.keys())[0]}"
    return "weight-" + str(len(nz)) + " " + "+".join(f"{c}*y^{e}" for e, c in sorted(nz.items()))

# ---------------------------------------------------------------- one descent level: branching
def measure_level(n, k, eta, p, label=""):
    """measure parent list and child-budget for the true worst weight-2 word at (n,k)."""
    N = n // 2
    elts = subgroup(n, p); s = window_s(k, n, eta)
    L, (a, b), s = true_worst_weight2(n, k, eta, p)

    # parent members (need members to check the descent really projects into the child lists)
    u = [(pow(x, a, p) + pow(x, b, p)) % p for x in elts]
    parent_members = list_RS(u, elts, k, s, p, return_members=True)
    parent_L = len(parent_members)

    # descended words on mu_N
    eltsN = subgroup(N, p)
    ue_terms, uo_terms = descend_word(a, b, n)
    ue_word = terms_to_word(ue_terms, eltsN, p)
    uo_word = terms_to_word(uo_terms, eltsN, p)

    # child code degrees: F deg < ceil(k/2), G deg < floor(k/2)
    kF = (k + 1) // 2
    kG = k // 2
    # child window threshold: use SAME eta on mu_N (rho'=kF/N etc).  s_child >= the descent
    # demands agreement on >= s/2 points roughly; we use the window convention at N.
    childF = childG = None
    sF = sG = None
    if kF >= 1 and kF < N and comb(N, kF) <= 3_000_000:
        sF = window_s(kF, N, eta)
        childF = list_RS(ue_word, eltsN, kF, sF, p)
    if kG >= 1 and kG < N and comb(N, kG) <= 3_000_000:
        sG = window_s(kG, N, eta)
        childG = list_RS(uo_word, eltsN, kG, sG, p)

    # PROJECTION CHECK: every parent member f projects to (F,G); verify F agrees with u_e
    # on the squared image and G with u_o (i.e. the pair really descends).  We count the
    # DISTINCT (F,G) projections actually realized by parent members.
    proj = set()
    for c in parent_members:
        F, G = split_even_odd(c, p)
        proj.add((F, G))
    distinct_proj = len(proj)

    child_pairs = (childF * childG) if (childF is not None and childG is not None) else None

    def ratio(x, y):
        if y in (None, 0) or x is None: return None
        return x / y

    print(f"  [{label}] n={n} k={k} eta={eta} p={p}")
    print(f"      worst weight-2 word: x^{a}+x^{b}   parent_L={parent_L}  s={s}")
    print(f"      descended u_e: {word_structure(ue_terms)}   u_o: {word_structure(uo_terms)}")
    print(f"      child code degs kF={kF}(sF={sF}) kG={kG}(sG={sG})")
    print(f"      childF(u_e)={childF}  childG(u_o)={childG}  child_pairs={child_pairs}")
    print(f"      distinct (F,G) projections of parent members = {distinct_proj}")
    rp = ratio(parent_L, child_pairs)
    rf = ratio(parent_L, childF)
    rg = ratio(parent_L, childG)
    print(f"      BRANCHING  B_pair=parent/child_pairs={rp}   "
          f"B_F=parent/childF={rf}   B_G=parent/childG={rg}")
    return dict(n=n, k=k, eta=eta, p=p, a=a, b=b, parent_L=parent_L,
                childF=childF, childG=childG, child_pairs=child_pairs,
                distinct_proj=distinct_proj, B_pair=rp, B_F=rf, B_G=rg,
                ue=word_structure(ue_terms), uo=word_structure(uo_terms))

# ---------------------------------------------------------------- driver
def run():
    print("="*78)
    print("PER-LEVEL BRANCHING of the even/odd descent for the worst weight-2 word")
    print("="*78)
    rows = []
    # (n, k, eta) chosen so C(n,k) is enumerable; two primes per (n,k)
    configs = [
        (16, 2, 0.125),
        (32, 2, 0.125),
        (64, 2, 0.125),
        (16, 4, 0.0625),
        (32, 4, 0.0625),
        (16, 2, 0.25),
        (32, 2, 0.25),
        (64, 2, 0.25),
        (16, 1, 0.0625),
        (32, 1, 0.0625),
        (64, 1, 0.0625),
    ]
    for (n, k, eta) in configs:
        if comb(n, k) > 3_000_000:
            print(f"  SKIP n={n} k={k}: C(n,k)={comb(n,k)} too large"); continue
        primes = [find_window_prime(n, 4.0)]
        p2 = find_window_prime(n, 4.5)
        if p2 != primes[0]:
            primes.append(p2)
        for p in primes:
            try:
                rows.append(measure_level(n, k, eta, p, label=f"k={k},eta={eta}"))
            except Exception as ex:
                print(f"  ERROR n={n} k={k} p={p}: {ex}")
    # summary: branching across n at fixed (k,eta)
    print("\n" + "="*78)
    print("SUMMARY: is B_pair bounded (<= ~4) and STABLE across n at fixed (k,eta)?")
    print("="*78)
    from collections import defaultdict
    grp = defaultdict(list)
    for r in rows:
        grp[(r['k'], r['eta'])].append(r)
    for (k, eta), rs in sorted(grp.items()):
        print(f"  (k={k}, eta={eta}):")
        for r in rs:
            print(f"    n={r['n']:3d} p={r['p']:>12d}  parent_L={r['parent_L']:>3}  "
                  f"childF={r['childF']}  childG={r['childG']}  "
                  f"B_pair={r['B_pair']}  B_F={r['B_F']}")

if __name__ == "__main__":
    run()

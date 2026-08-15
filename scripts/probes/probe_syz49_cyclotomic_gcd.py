#!/usr/bin/env python3
"""
SYZ49 -- the cyclotomic-GCD bedrock: max level set of R = W_BC/W_AC on mu_n.

Context (#466, rate-1/2 proximity residual).  SYZ48 pinned the balanced-interior
kernel to a single on-domain question.  A constant-ratio (low) syzygy
    c0*W_AB + alpha*W_AC + beta*W_BC = 0   (AB slot carrying, c0 != 0)
is EXACTLY   W_AB | (alpha*W_AC + beta*W_BC).  For the AB slot to be band-realizable,
W_AB must vanish on `a` points of mu_n.  Equivalently:

    gcd( alpha*W_AC + beta*W_BC , X^n - 1 )  must have degree >= a.

Here W_AC, W_BC are the vanishing polynomials of DISJOINT mu_n-subsets S_AC, S_BC of
sizes b, c (band-sized).  The roots of alpha*W_AC + beta*W_BC that lie in mu_n are
EXACTLY the omega in mu_n \ (S_AC u S_BC) with

    R(omega) := W_BC(omega) / W_AC(omega) = -alpha/beta   (a single LEVEL lambda).

So:   max over (alpha,beta) of  deg gcd(alpha*W_AC+beta*W_BC, X^n-1)
    = MAX LEVEL SET of R on mu_n \ (S_AC u S_BC)
    = max_lambda #{ omega in mu_n\(S_AC u S_BC) : R(omega) = lambda }.

THE BEDROCK QUESTION: can this max level set reach `a` (band-sized ~ b,c) for ANY
disjoint S_AC, S_BC?  If NOT -- if the max level set is provably < a -- the
balanced-interior kernel is CLOSED (no low constant syzygy is band-realizable).

This probe measures the max-level-set law:
  [A] EXHAUSTIVE at small n: all disjoint pairs, all levels, exact max level set.
  [B] COSET-STRUCTURED S's: S_AC, S_BC unions of cosets of a subgroup H<=mu_n --
      is R quasi-periodic, and are its level sets forced small / degenerate?
  [C] ADVERSARIAL random + hill-climb at n up to a few hundred: growth law of the
      max level set vs n, vs b.
  [D] BGK correspondence: R constant on a set A  <=>  the discrete-log sum
      f(omega) = sum_{s in S_BC} L(omega - s) - sum_{s in S_AC} L(omega - s)  is
      constant on A, where L = discrete log.  This is the additive-combinatorics /
      character-sum shape of the ORIGINAL BGK wall.  Numeric confirmation.
"""
import random
from itertools import combinations


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


def primitive_root(mod):
    for cand in range(2, mod):
        if all(pow(cand, (mod - 1) // pr, mod) != 1 for pr in prime_factors(mod - 1)):
            return cand
    return None


def mu_domain(n, mod):
    """n-th roots of unity in F_mod as list ordered by exponent: [w^0,...,w^{n-1}]."""
    if (mod - 1) % n != 0:
        return None, None
    g = primitive_root(mod)
    w = pow(g, (mod - 1) // n, mod)
    pts = [pow(w, i, mod) for i in range(n)]
    return pts, w


def ratio_R(omega, S_AC, S_BC, mod):
    """R(omega) = prod_{s in S_BC}(omega-s) / prod_{s in S_AC}(omega-s)."""
    num = 1
    for s in S_BC:
        num = (num * ((omega - s) % mod)) % mod
    den = 1
    for s in S_AC:
        den = (den * ((omega - s) % mod)) % mod
    return (num * pow(den, mod - 2, mod)) % mod


def max_level_set(pts, S_AC, S_BC, mod):
    """max_lambda #{omega in pts \ (S_AC u S_BC): R(omega)=lambda}."""
    excl = set(S_AC) | set(S_BC)
    counts = {}
    for omega in pts:
        if omega in excl:
            continue
        lam = ratio_R(omega, S_AC, S_BC, mod)
        counts[lam] = counts.get(lam, 0) + 1
    if not counts:
        return 0, None
    best = max(counts.values())
    lam = max(counts, key=counts.get)
    return best, lam


# ---------------------------------------------------------------------------
def experiment_A(mod, n, b, c, max_pairs=200000):
    """EXHAUSTIVE (or capped) over disjoint pairs (S_AC size b, S_BC size c)."""
    pts, w = mu_domain(n, mod)
    if pts is None:
        return None
    idx = list(range(n))
    overall_max = 0
    argmax = None
    seen = 0
    # enumerate S_AC over index subsets, S_BC over disjoint index subsets
    for ac_idx in combinations(idx, b):
        rem = [i for i in idx if i not in set(ac_idx)]
        for bc_idx in combinations(rem, c):
            S_AC = [pts[i] for i in ac_idx]
            S_BC = [pts[i] for i in bc_idx]
            m, lam = max_level_set(pts, S_AC, S_BC, mod)
            if m > overall_max:
                overall_max = m
                argmax = (ac_idx, bc_idx, lam)
            seen += 1
            if seen >= max_pairs:
                return {"mod": mod, "n": n, "b": b, "c": c, "pairs": seen,
                        "capped": True, "max_level_set": overall_max, "argmax": argmax}
    return {"mod": mod, "n": n, "b": b, "c": c, "pairs": seen, "capped": False,
            "max_level_set": overall_max, "argmax": argmax}


def experiment_B(mod, n, hsize, trials=400, seed=3):
    """COSET-STRUCTURED S's: unions of cosets of subgroup H (order hsize) of mu_n.

    Requires hsize | n.  Build H = <w^(n/hsize)>.  Pick S_AC, S_BC each as a union
    of whole cosets of H (disjoint).  Measure max level set; compare to random-set
    baseline of the SAME sizes.
    """
    pts, w = mu_domain(n, mod)
    if pts is None or n % hsize != 0:
        return None
    ncoset = n // hsize
    # cosets indexed by residue r mod ncoset: {r, r+ncoset, ...}? No: H = powers of
    # w^{ncoset}; cosets are w^r * H for r=0..ncoset-1 => indices {r + ncoset*k}.
    cosets = [[(r + ncoset * k) for k in range(hsize)] for r in range(ncoset)]
    rng = random.Random(seed)
    struct_max = 0
    struct_hist = {}
    rand_max = 0
    ok = 0
    for _ in range(trials):
        if ncoset < 4:
            break
        # pick 1-2 cosets for AC, 1-2 disjoint cosets for BC
        na = rng.choice([1, 2]); nb = rng.choice([1, 2])
        if na + nb > ncoset:
            continue
        chosen = rng.sample(range(ncoset), na + nb)
        ac_cos = chosen[:na]; bc_cos = chosen[na:]
        S_AC = [pts[i] for cs in ac_cos for i in cosets[cs]]
        S_BC = [pts[i] for cs in bc_cos for i in cosets[cs]]
        m, lam = max_level_set(pts, S_AC, S_BC, mod)
        struct_max = max(struct_max, m)
        struct_hist[m] = struct_hist.get(m, 0) + 1
        # random baseline of same sizes
        allidx = rng.sample(range(n), len(S_AC) + len(S_BC))
        rA = [pts[i] for i in allidx[:len(S_AC)]]
        rB = [pts[i] for i in allidx[len(S_AC):]]
        mr, _ = max_level_set(pts, rA, rB, mod)
        rand_max = max(rand_max, mr)
        ok += 1
    return {"mod": mod, "n": n, "hsize": hsize, "ncoset": ncoset, "trials": ok,
            "coset_struct_max_level": struct_max, "coset_hist": dict(sorted(struct_hist.items())),
            "random_baseline_max_level": rand_max}


def experiment_C(mod, n, b, c, iters=4000, seed=5):
    """ADVERSARIAL hill-climb: maximize the max level set over disjoint (S_AC,S_BC)."""
    pts, w = mu_domain(n, mod)
    if pts is None or 2 * (b + c) > n:  # need room
        pass
    if pts is None:
        return None
    rng = random.Random(seed)

    def rand_pair():
        s = rng.sample(range(n), b + c)
        return set(s[:b]), set(s[b:])

    def evalp(ac, bc):
        S_AC = [pts[i] for i in ac]; S_BC = [pts[i] for i in bc]
        m, lam = max_level_set(pts, S_AC, S_BC, mod)
        return m

    best = 0
    best_pair = None
    # multi-restart hill climb
    restarts = max(6, iters // 500)
    for _ in range(restarts):
        ac, bc = rand_pair()
        cur = evalp(ac, bc)
        for _ in range(iters // restarts):
            used = ac | bc
            free = [i for i in range(n) if i not in used]
            if not free:
                break
            # swap a random member of ac or bc for a random free index
            move_ac = rng.random() < 0.5
            src = rng.choice(list(ac if move_ac else bc))
            dst = rng.choice(free)
            nac = set(ac); nbc = set(bc)
            if move_ac:
                nac.discard(src); nac.add(dst)
            else:
                nbc.discard(src); nbc.add(dst)
            val = evalp(nac, nbc)
            if val >= cur:
                cur = val; ac, bc = nac, nbc
        if cur > best:
            best = cur; best_pair = (sorted(ac), sorted(bc))
    return {"mod": mod, "n": n, "b": b, "c": c, "adversarial_max_level": best,
            "a_target(=b)": b}


def experiment_D(mod, n, b, c, seed=9):
    """BGK correspondence numeric check.

    log R(omega) = sum_{s in S_BC} L(omega-s) - sum_{s in S_AC} L(omega-s)  (mod (mod-1))
    where L = discrete log base primitive root g.  R constant on a set A  <=>  this
    additive discrete-log sum constant on A.  We verify the identity holds pointwise
    (sanity) and report the level-set structure through the log lens.
    """
    pts, w = mu_domain(n, mod)
    if pts is None:
        return None
    g = primitive_root(mod)
    # discrete log table
    dlog = {}
    acc = 1
    for e in range(mod - 1):
        dlog[acc] = e
        acc = (acc * g) % mod
    rng = random.Random(seed)
    s = rng.sample(range(n), b + c)
    S_AC = [pts[i] for i in s[:b]]; S_BC = [pts[i] for i in s[b:]]
    excl = set(S_AC) | set(S_BC)
    # check identity: dlog(R(omega)) == sum L(omega-s in BC) - sum L(omega-s in AC) mod (mod-1)
    ok = True
    logvals = {}
    for omega in pts:
        if omega in excl:
            continue
        R = ratio_R(omega, S_AC, S_BC, mod)
        lhs = dlog[R]
        rhs = (sum(dlog[(omega - t) % mod] for t in S_BC)
               - sum(dlog[(omega - t) % mod] for t in S_AC)) % (mod - 1)
        if lhs != rhs:
            ok = False
        logvals[omega] = lhs
    # max level set in log space = max multiplicity of logval
    counts = {}
    for v in logvals.values():
        counts[v] = counts.get(v, 0) + 1
    maxlvl = max(counts.values()) if counts else 0
    return {"mod": mod, "n": n, "identity_holds": ok,
            "max_level_set_via_dlog": maxlvl,
            "note": "R const on A <=> additive dlog-sum const on A (BGK character-sum shape)"}


if __name__ == "__main__":
    print("=" * 78)
    print("SYZ49 cyclotomic GCD: max level set of R = W_BC/W_AC on mu_n")
    print("=" * 78)

    print("\n[A] EXHAUSTIVE max level set over ALL disjoint pairs at small n")
    print("    (max level set = max_{alpha,beta} deg gcd(alpha W_AC+beta W_BC, X^n-1))")
    print("-" * 78)
    for mod, n, b, c in [(13, 12, 3, 3), (13, 12, 4, 4), (31, 6, 2, 2),
                          (31, 30, 3, 3), (41, 20, 4, 4), (43, 42, 3, 3)]:
        r = experiment_A(mod, n, b, c, max_pairs=120000)
        if r is None:
            continue
        cap = " (CAPPED)" if r["capped"] else ""
        print(f"  F_{mod}/mu_{n} sizes b=c={b}: pairs={r['pairs']}{cap}  "
              f"MAX LEVEL SET = {r['max_level_set']}   (a-target={b})")

    print("\n[B] COSET-STRUCTURED S's vs random baseline (same sizes)")
    print("-" * 78)
    for mod, n, h in [(13, 12, 3), (13, 12, 4), (41, 20, 4), (43, 42, 6), (61, 60, 5)]:
        r = experiment_B(mod, n, h)
        if r is None:
            continue
        print(f"  F_{mod}/mu_{n}, H order {h} ({r['ncoset']} cosets), {r['trials']} trials:")
        print(f"    coset-structured max level = {r['coset_struct_max_level']}  "
              f"hist={r['coset_hist']}")
        print(f"    random-baseline  max level = {r['random_baseline_max_level']}")

    print("\n[C] ADVERSARIAL hill-climb max level set vs n (growth law)")
    print("-" * 78)
    for mod, n, b, c in [(61, 60, 5, 5), (101, 100, 8, 8), (211, 210, 12, 12),
                          (241, 240, 16, 16), (337, 336, 20, 20), (421, 420, 30, 30)]:
        r = experiment_C(mod, n, b, c, iters=3000)
        if r is None:
            continue
        print(f"  F_{mod}/mu_{n} sizes b=c={b}: ADVERSARIAL MAX LEVEL SET = "
              f"{r['adversarial_max_level']}   (a-target={b})")

    print("\n[D] BGK correspondence: R const <=> additive discrete-log sum const")
    print("-" * 78)
    for mod, n, b, c in [(61, 60, 5, 5), (101, 100, 8, 8), (241, 240, 16, 16)]:
        r = experiment_D(mod, n, b, c)
        if r is None:
            continue
        print(f"  F_{mod}/mu_{n}: dlog identity holds = {r['identity_holds']}, "
              f"max level set via dlog = {r['max_level_set_via_dlog']}")
    print("    => level set of R = level set of the additive character-sum phase")
    print("       f(omega)=sum_{BC}L(omega-s)-sum_{AC}L(omega-s): the BGK wall shape.")

    print("\n" + "=" * 78)
    print("READING: if MAX LEVEL SET < a=b uniformly, the balanced-interior low")
    print("  constant syzygy is NOT band-realizable => interior kernel closes.")
    print("=" * 78)


# ===========================================================================
# SYZ49b -- PROPER-SUBGROUP analysis (mu_n a PROPER subset of F_p^x, p >> n).
# SYZ45's caveat: the bound fails on the FULL group F_p^x = mu_{p-1} partitioned
# into cosets (X^d - c binomial dependence).  Band-realizability requires mu_n to
# be a PROPER subgroup/subset.  Redo the max-level-set law there, and detect
# whether any level set that reaches `a` is FORCED to be coset/binomial-structured.
# ===========================================================================

def is_coset_structured(idx_set, n):
    """Is the index subset (subset of Z/n) a union of cosets of a nontrivial
    subgroup of Z/n?  Returns the largest such subgroup order (>1) or 1."""
    s = set(x % n for x in idx_set)
    best = 1
    # subgroups of Z/n = <n/k> for k | n, order k.  coset union = closed under +n/k.
    for k in range(2, n + 1):
        if n % k != 0:
            continue
        step = n // k  # generator of order-k subgroup
        if all(((x + step) % n) in s for x in s):
            best = max(best, k)
    return best


def binomial_structured_pair(ac_idx, bc_idx, n):
    """Do BOTH sets sit inside cosets of a common subgroup H (order d=|set|),
    i.e. each set = ONE full coset of the order-|set| subgroup?  That is exactly
    the X^d - c binomial family SYZ45 excludes."""
    b = len(ac_idx)
    if n % b != 0:
        return False
    step = n // b
    def is_single_coset(idx):
        s = sorted(x % n for x in idx)
        r0 = s[0]
        return sorted(s) == sorted((r0 + step * k) % n for k in range(b))
    return is_single_coset(ac_idx) and is_single_coset(bc_idx)


def experiment_A_proper(mod, n, b, c, max_pairs=200000):
    """Exhaustive/capped over disjoint pairs on a PROPER subgroup mu_n < F_mod^x.
    Reports max level set AND whether every argmax reaching `a=b` is coset-structured."""
    assert (mod - 1) % n == 0 and (mod - 1) != n, "need PROPER subgroup"
    pts, w = mu_domain(n, mod)
    idx = list(range(n))
    overall_max = 0
    argmax = None
    reached_a_all_coset = True
    reached_a_count = 0
    noncoset_max = 0     # max level set among NON-binomial-structured pairs
    seen = 0
    for ac_idx in combinations(idx, b):
        acs = set(ac_idx)
        rem = [i for i in idx if i not in acs]
        for bc_idx in combinations(rem, c):
            S_AC = [pts[i] for i in ac_idx]
            S_BC = [pts[i] for i in bc_idx]
            m, lam = max_level_set(pts, S_AC, S_BC, mod)
            binom = binomial_structured_pair(ac_idx, bc_idx, n)
            if not binom and m > noncoset_max:
                noncoset_max = m
            if m > overall_max:
                overall_max = m
                argmax = (ac_idx, bc_idx, lam, binom)
            if m >= b:
                reached_a_count += 1
                if not binom:
                    reached_a_all_coset = False
            seen += 1
            if seen >= max_pairs:
                return {"n": n, "mod": mod, "b": b, "capped": True, "pairs": seen,
                        "max_level_set": overall_max, "noncoset_max_level": noncoset_max,
                        "reached_a_count": reached_a_count,
                        "every_reach_a_is_binomial": reached_a_all_coset, "argmax": argmax}
    return {"n": n, "mod": mod, "b": b, "capped": False, "pairs": seen,
            "max_level_set": overall_max, "noncoset_max_level": noncoset_max,
            "reached_a_count": reached_a_count,
            "every_reach_a_is_binomial": reached_a_all_coset, "argmax": argmax}


def experiment_C_proper(mod, n, b, c, iters=4000, seed=5):
    """Adversarial hill-climb on a PROPER subgroup; report max level set + coset flag."""
    assert (mod - 1) % n == 0 and (mod - 1) != n, "need PROPER subgroup"
    pts, w = mu_domain(n, mod)
    rng = random.Random(seed)

    def evalp(ac, bc):
        S_AC = [pts[i] for i in ac]; S_BC = [pts[i] for i in bc]
        m, _ = max_level_set(pts, S_AC, S_BC, mod)
        return m

    best = 0; best_binom = None; best_pair = None
    restarts = max(8, iters // 400)
    for _ in range(restarts):
        s = rng.sample(range(n), b + c)
        ac = set(s[:b]); bc = set(s[b:])
        cur = evalp(ac, bc)
        for _ in range(iters // restarts):
            used = ac | bc
            free = [i for i in range(n) if i not in used]
            if not free:
                break
            move_ac = rng.random() < 0.5
            src = rng.choice(list(ac if move_ac else bc))
            dst = rng.choice(free)
            nac, nbc = set(ac), set(bc)
            (nac if move_ac else nbc).discard(src)
            (nac if move_ac else nbc).add(dst)
            val = evalp(nac, nbc)
            if val >= cur:
                cur = val; ac, bc = nac, nbc
        if cur > best:
            best = cur
            best_binom = binomial_structured_pair(sorted(ac), sorted(bc), n)
            best_pair = (sorted(ac), sorted(bc))
    return {"n": n, "mod": mod, "b": b, "adversarial_max_level": best,
            "argmax_is_binomial": best_binom, "a_target": b}


if __name__ == "__main__":
    print("\n\n" + "#" * 78)
    print("SYZ49b -- PROPER SUBGROUP mu_n < F_p^x  (p >> n; the band-realizable regime)")
    print("#" * 78)

    print("\n[A'] EXHAUSTIVE max level set on PROPER subgroups + coset diagnosis")
    print("     (does every level set that REACHES a require binomial/coset structure?)")
    print("-" * 78)
    # (mod, n, b) with n | mod-1 and n != mod-1  (proper)
    for mod, n, b in [(37, 12, 3), (37, 12, 4), (61, 12, 4), (73, 12, 4),
                       (41, 20, 4), (101, 20, 4), (61, 30, 5), (151, 30, 5)]:
        if (mod - 1) % n != 0 or mod - 1 == n:
            print(f"  skip F_{mod}/mu_{n} (not proper)"); continue
        r = experiment_A_proper(mod, n, b, b, max_pairs=150000)
        cap = " CAP" if r["capped"] else ""
        print(f"  F_{mod}/mu_{n} b=c={b}{cap}: MAXlvl={r['max_level_set']} "
              f"NONcoset_max={r['noncoset_max_level']} (a={b})  "
              f"#reach>=a={r['reached_a_count']}  every-reach-a-binomial={r['every_reach_a_is_binomial']}")

    print("\n[C'] ADVERSARIAL max level set on PROPER subgroups (growth law)")
    print("-" * 78)
    for mod, n, b in [(37, 12, 4), (73, 24, 8), (101, 20, 8), (241, 40, 13),
                       (151, 30, 10), (211, 30, 10), (241, 60, 20), (401, 40, 13)]:
        if (mod - 1) % n != 0 or mod - 1 == n:
            print(f"  skip F_{mod}/mu_{n} (not proper)"); continue
        r = experiment_C_proper(mod, n, b, b, iters=3000)
        print(f"  F_{mod}/mu_{n} b=c={b}: ADV MAXlvl={r['adversarial_max_level']} "
              f"binomial={r['argmax_is_binomial']}  (a={b})")

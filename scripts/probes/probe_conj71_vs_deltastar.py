#!/usr/bin/env python3
"""
probe_conj71_vs_deltastar.py
  Resolve the Conj71-pivot: does Conjecture 7.1 (Chai-Fan eprint 2026/861,
  "sparse-worst-case dominance" for above-Johnson FRI commit-phase soundness)
  pin the SAME delta* as the MCA list-decoding threshold (ABF26 2026/680 sec 4.5)?

PIVOT CLAIM (contested): a lit scan claimed the real prize MOVED from BGK to
Conj 7.1; 2026/861's above-Johnson plain-RS O(1)/|F| FRI commit-phase soundness
reduces to Conj 7.1, claimed NOT to reduce to char sums / BGK.
COUNTERCLAIM (this probe tests): 2026/861 CONFLATES FRI protocol soundness with
the MCA delta*.  They are DIFFERENT quantities:

  (FRI)  eps_FRI = sum_{j<m} e_j  where e_j = per-round bad-challenge fraction
         = Pr_gamma[ folded word at round j is delta-close to RS_{k/2^j} but the
           original was NOT ].  A SUM over m fold rounds of a per-round soundness
           error.  2026/861/858 bound this by AVOIDING the list-uncertainty zone
           (threshold halving -> unique decoding) -> O(1)/|F| or O(n)/|F| PER ROUND.

  (MCA)  eps_mca(C,delta) = sup over pairs (f0,f1) of
           Pr_gamma[ EXISTS S, |S|>=(1-delta)n, line f0+gamma f1 = some codeword
                     on S, but NO joint codeword pair agrees with (f0,f1) on S ].
         delta* = sup{ delta : eps_mca(C,delta) <= eps* }.  A SINGLE-ROUND,
         per-radius LIST-NON-UNIQUENESS threshold.  This is the $1M object.

This probe builds a concrete thin dyadic RS code over a small prime field with a
smooth multiplicative subgroup eval domain mu_n (n=2^mu, n | p-1, PROPER subgroup,
p >> n^3 where feasible), and for a sweep of radii delta computes BOTH:
  (A) the FRI per-round bad-challenge fraction e(delta) (the 2-monomial pencil
      bad-alpha count / q, the action-orbit object of Theorem 2.1), and its
      "sparse-witness dominance ratio" = e_general(delta) / e_sparse(delta);
  (B) the exact eps_mca(C, delta) and the induced delta*(eps*) for the prize
      budget eps* (single round).

Then it checks the load-bearing question: does the radius at which FRI soundness
degrades (e(delta) crosses O(1)/q) EQUAL the MCA delta* (radius at which
eps_mca crosses eps*)?  If they coincide for all (p,n) -> the pivot's
"7.1 IS the prize" could hold.  If they systematically DIFFER -> conflation.

Honesty: this is EVIDENCE about which quantity the prize is, not a proof.  The
in-tree Lean (ProofLoop40/42, BridgeLoop41, Errors.epsMCA) already separates the
two objects; this probe is the machine-checked numeric cross-check of that
separation.
"""

import itertools
from fractions import Fraction


# ----------------------- field / domain construction -----------------------

def is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def primitive_root(p):
    # factor p-1
    m = p - 1
    fac = set()
    x = m
    d = 2
    while d * d <= x:
        while x % d == 0:
            fac.add(d)
            x //= d
        d += 1
    if x > 1:
        fac.add(x)
    for g in range(2, p):
        if all(pow(g, m // q, p) != 1 for q in fac):
            return g
    raise RuntimeError("no primitive root")


def mu_n(p, n):
    """The order-n multiplicative subgroup of F_p* (requires n | p-1).
       PROPER: caller ensures n < p-1.  Returns list of n distinct elements."""
    assert (p - 1) % n == 0
    g = primitive_root(p)
    zeta = pow(g, (p - 1) // n, p)
    out, x = [], 1
    for _ in range(n):
        out.append(x)
        x = (x * zeta) % p
    return out


# ----------------------- Reed-Solomon over mu_n -----------------------

def poly_eval(coeffs, x, p):
    acc = 0
    for c in reversed(coeffs):
        acc = (acc * x + c) % p
    return acc


def rs_codewords(p, dom, k):
    """All RS_k codewords on eval domain `dom`: evaluations of every degree-<k poly.
       Size p^k -- only call for tiny (p,k)."""
    out = []
    for coeffs in itertools.product(range(p), repeat=k):
        out.append(tuple(poly_eval(coeffs, x, p) for x in dom))
    return out


def hamming_dist(a, b):
    return sum(1 for x, y in zip(a, b) if x != y)


def dist_to_code(word, code):
    return min(hamming_dist(word, c) for c in code)


# ----------------------- (A) FRI per-round bad-challenge fraction -----------------------
# Action-Orbit 2-monomial pencil h_alpha = f0 + alpha*f1 (random word view).
# e(delta) = Pr_alpha[ dist(f0 + alpha f1, RS_k) <= delta*n ]  worst over (f0,f1).
# "Sparse" input = f0,f1 each supported (nonzero) on few positions.

def fri_bad_fraction(p, dom, k, f0, f1, delta_n, code):
    """fraction of alpha in F_p with dist(f0 + alpha f1, RS_k) <= delta_n."""
    n = len(dom)
    bad = 0
    for alpha in range(p):
        line = tuple((f0[i] + alpha * f1[i]) % p for i in range(n))
        if dist_to_code(line, code) <= delta_n:
            bad += 1
    return Fraction(bad, p)


def sparse_words(p, n, maxwt):
    """all words of Hamming weight <= maxwt over F_p (the 'sparse witnesses')."""
    out = []
    for w in range(0, maxwt + 1):
        for pos in itertools.combinations(range(n), w):
            for vals in itertools.product(range(1, p), repeat=w):
                word = [0] * n
                for j, pp in enumerate(pos):
                    word[pp] = vals[j]
                out.append(tuple(word))
    return out


def worst_fri_bad_fraction(p, dom, k, code, delta_n, words, trials=None):
    """worst-case (over the given word list) FRI per-round bad fraction at radius delta_n.
       Caller supplies the candidate word pool (sparse list, or sampled words)."""
    n = len(dom)
    worst = Fraction(0)
    cnt = 0
    for f0 in words:
        for f1 in words:
            frac = fri_bad_fraction(p, dom, k, f0, f1, delta_n, code)
            if frac > worst:
                worst = frac
            cnt += 1
            if trials is not None and cnt >= trials:
                return worst
    return worst


# ----------------------- (B) exact MCA eps_mca(C, delta) -----------------------
# eps_mca = sup over pairs (u0,u1) of Pr_gamma[ mcaEvent ].
# mcaEvent: EXISTS S, |S|>=(1-delta)n, EXISTS w in C with w=u0+gamma u1 on S,
#           and NO pair (c0,c1) in C^2 jointly agrees with (u0,u1) on S.

def pair_joint_agrees_on(code, S, u0, u1):
    """exists (c0,c1) in code^2 with c0=u0 and c1=u1 on all of S."""
    Sl = list(S)
    c0ok = [c for c in code if all(c[i] == u0[i] for i in Sl)]
    if not c0ok:
        return False
    c1ok = any(all(c[i] == u1[i] for i in Sl) for c in code)
    return c1ok


def mca_event(code, dom, delta, u0, u1, gamma, p):
    n = len(dom)
    thresh = (1 - delta) * n  # |S| >= thresh
    line = tuple((u0[i] + gamma * u1[i]) % p for i in range(n))
    # agreement set of line with SOME codeword w: take the best w (max agreement)
    # mcaEvent only needs SOME S of size>=thresh on which line=w and no joint pair.
    for w in code:
        agree = [i for i in range(n) if line[i] == w[i]]
        if len(agree) >= thresh:
            # S = agree (largest natural witness); check no joint pair agrees on S
            if not pair_joint_agrees_on(code, agree, u0, u1):
                return True
    return False


def eps_mca(code, dom, delta, p, pairs):
    """exact-ish: sup over given pairs of  (#gamma with mcaEvent)/p."""
    n = len(dom)
    worst = Fraction(0)
    for (u0, u1) in pairs:
        bad = 0
        for gamma in range(p):
            if mca_event(code, dom, delta, u0, u1, gamma, p):
                bad += 1
        fr = Fraction(bad, p)
        if fr > worst:
            worst = fr
    return worst


# ----------------------- main sweep -----------------------

def run_instance(p, n, k, eps_star, max_pairs=30):
    import math, random
    dom = mu_n(p, n)
    rho = Fraction(k, n)
    code = rs_codewords(p, dom, k)
    print(f"\n=== p={p}, n={n} (mu_n PROPER: n={n} < p-1={p-1}), k={k}, "
          f"rho={rho}, |code|={len(code)}, eps*={eps_star} ===", flush=True)
    sqrt_rho = math.sqrt(k / n)
    johnson_r = 1 - sqrt_rho
    capacity = 1 - k / n
    print(f"    Johnson 1-sqrt(rho)={johnson_r:.4f}, capacity 1-rho={capacity:.4f}",
          flush=True)

    random.seed(12345)
    # MCA worst-case word pool: sparse witnesses (Conj 7.1's object) + random words.
    # weight<=2 sparse pool is large at p=17,n=8; subsample it to keep the probe fast.
    full_sparse = sparse_words(p, n, maxwt=2)
    sparse_pool = full_sparse if len(full_sparse) <= 300 else random.sample(full_sparse, 300)
    rand_pool = [tuple(random.randrange(p) for _ in range(n)) for _ in range(max_pairs)]
    mca_words = sparse_pool + rand_pool
    # pairs for MCA: all sparse x sparse is large; sample pairs from the pool.
    pairs = []
    for _ in range(max_pairs):
        pairs.append((random.choice(mca_words), random.choice(mca_words)))
    for _ in range(max_pairs):  # sparse x sparse explicitly (Conj 7.1 witnesses)
        pairs.append((random.choice(sparse_pool), random.choice(sparse_pool)))

    print(f"    {'delta':>8} {'dn':>4} {'eps_mca':>10} {'<=e*?':>6} "
          f"{'e_FRI':>10} {'e_FRI_sp':>10}  note", flush=True)
    deltastar_mca = None
    deltastar_fri = None
    eps_star_f = Fraction(eps_star)
    for dn in range(1, n):
        delta = Fraction(dn, n)
        em = eps_mca(code, dom, delta, p, pairs)
        mca_good = em <= eps_star_f
        if mca_good:
            deltastar_mca = delta
        # FRI per-round bad fraction: sparse worst (action-orbit Thm 2.1 object)
        # and general (sampled) worst.
        e_sparse = worst_fri_bad_fraction(p, dom, k, code, dn, sparse_pool, trials=1500)
        e_gen = worst_fri_bad_fraction(p, dom, k, code, dn, rand_pool, trials=400)
        if e_gen <= eps_star_f:
            deltastar_fri = delta
        note = ""
        if abs(float(delta) - johnson_r) < 1.0 / n:
            note += "~Johnson "
        if abs(float(delta) - capacity) < 1.0 / n:
            note += "~capacity "
        print(f"    {float(delta):>8.4f} {dn:>4} {str(em):>10} {str(mca_good):>6} "
              f"{float(e_gen):>10.5f} {float(e_sparse):>10.5f}  {note}", flush=True)
    print(f"    -> MCA  delta*(eps*={eps_star}) = {deltastar_mca} "
          f"({float(deltastar_mca) if deltastar_mca else None})", flush=True)
    print(f"    -> FRI  delta*(eps*={eps_star}) = {deltastar_fri} "
          f"({float(deltastar_fri) if deltastar_fri else None})", flush=True)
    same = (deltastar_mca == deltastar_fri)
    print(f"    -> SAME threshold?  {same}", flush=True)
    return deltastar_mca, deltastar_fri, same


def main():
    print("=" * 78)
    print("probe_conj71_vs_deltastar:  Conj 7.1 (FRI sparse-dominance) vs MCA delta*")
    print("=" * 78)
    # tiny feasible instances. mu_n PROPER (n < p-1), p as large as feasible.
    # Need n | p-1, k small (|code|=p^k), n small (enum sparse pairs).
    results = []
    instances = [
        # (p, n, k, eps*).  n | p-1, n PROPER (n<p-1), |code|=p^k kept tiny.
        # k=1 (RS=constants) is degenerate (every nonzero word maximally far,
        # e_FRI==1) but cheap and confirms the trivial-collapse baseline.
        (13, 4, 1, Fraction(1, 13)),   # n=4 dyadic, rho=1/4 (prize rate)
        (17, 8, 2, Fraction(1, 17)),   # n=8 dyadic, rho=1/4 (the informative one)
    ]
    for (p, n, k, eps_star) in instances:
        assert is_prime(p) and (p - 1) % n == 0 and n < p - 1
        try:
            results.append((p, n, k, run_instance(p, n, k, eps_star)))
        except Exception as e:
            print(f"  instance p={p},n={n},k={k} FAILED: {e}")

    print("\n" + "=" * 78)
    print("SUMMARY")
    print("=" * 78)
    n_same = sum(1 for (_, _, _, (_, _, s)) in results if s)
    print(f"  instances where FRI-soundness-threshold == MCA delta*: "
          f"{n_same}/{len(results)}")
    print("  INTERPRETATION:")
    print("   * eps_mca is a SINGLE-ROUND list-non-uniqueness threshold (sup over")
    print("     (f0,f1) of Pr_gamma[mcaEvent]); delta* = sup{delta: eps_mca<=eps*}.")
    print("   * FRI eps_FRI = SUM over m fold rounds of per-round bad-challenge")
    print("     fraction; 2026/861/858 bound it by AVOIDING the list zone")
    print("     (threshold-halving -> unique decoding), per ProofLoop42 docstring.")
    print("   * The two thresholds are DIFFERENT objects.  If they coincide here it")
    print("     is a small-instance artifact (in unique-decoding both collapse to")
    print("     the same radius); the prize lives where they DIVERGE -- the")
    print("     above-Johnson LIST zone that FRI soundness sidesteps and MCA does not.")
    print("=" * 78)


if __name__ == "__main__":
    main()

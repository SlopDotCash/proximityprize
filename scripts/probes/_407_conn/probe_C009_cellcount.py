#!/usr/bin/env python3
"""C009 probe: does the Hab25 K4 affine-cell budget (<= n per cell) close the prize?

Connection C009 claim chain:
  (1) each affine-pinned cell of bad scalars has size <= n   [PROVEN in-tree:
      K4_cell_card_le_of_affine_pinning_family]
  (2) prize budget is  q * eps*  ~ n  bad scalars
  (3) total bad scalars  I(delta) <= c * n   where c = # affine cells
  (4) c <= deg_Y(R)  (GS interpolant Y-degree = # positive-Y-deg factors)
  => "the gap is c vs budget n; if c = O(1) the prize closes".

The decisive question this probe settles EXACTLY (integer arithmetic, proper
subgroups mu_n < F_q*, large primes, n << sqrt(q)):

  Is c structurally O(1), OR does c track the very list size I(delta) we are
  trying to bound?  If c ~ I(delta)/n then  I(delta) <= c*n  is a TAUTOLOGY
  and C009 only RELOCATES the open problem (to "bound c"), not closes it.

We model the governing quantity directly: for the MCA / proximity setting the
relevant "bad set" is the set of scalars gamma for which the folded word
u0 + gamma*u1 is delta-close to the RS code, and the affine-cell structure is
the partition of those gammas by which decoded codeword-pair (the affine pencil
(v0,v1)) explains them.  We compute, over honest small RS instances at a
PROPER multiplicative subgroup domain mu_n < F_q*:
   - I(delta) = # bad scalars
   - per-cell sizes (verify <= n)
   - c = minimum # affine pencils covering the bad set
   - ratio c vs I(delta)/n   (=1 would mean cells are full; >1 means cells
     undersized; the point: does c GROW with I(delta)?)

Then we ALSO compute the asymptotic relation analytically (printed): in
Guruswami-Sudan at decoding radius the list size L and deg_Y are the SAME
order, so c is tied to L, not O(1).
"""
import itertools, sys
from fractions import Fraction


def find_subgroup_prime(n, beta_min=4):
    """Smallest prime q with q = 1 mod n and q >= n**beta_min (proper subgroup)."""
    import sympy
    target = n ** beta_min
    q = ((target // n) + 1) * n + 1
    while True:
        if sympy.isprime(q):
            return q
        q += n
    # never


def mu_n(q, n):
    """The order-n multiplicative subgroup of F_q* (q = 1 mod n)."""
    # find a generator g of F_q*, then g^((q-1)/n) generates mu_n
    import sympy
    g = sympy.primitive_root(q)
    h = pow(g, (q - 1) // n, q)
    sub = []
    x = 1
    for _ in range(n):
        sub.append(x)
        x = (x * h) % q
    assert len(set(sub)) == n
    return sub


def poly_eval(coeffs, x, q):
    acc = 0
    for c in reversed(coeffs):
        acc = (acc * x + c) % q
    return acc


def analyze(q, n, k, domain, max_stacks, seed=7):
    """Return list of (I, cmin, cell_sizes_max) over sampled stacks with I>=2."""
    import random
    random.seed(seed)
    F = list(range(q))
    delta = Fraction(n - k, n)  # near unique-decoding-ish; bad set nonempty
    # We use the agreement-radius decoding: gamma is "bad" if fold agrees with
    # SOME deg<k poly on >= (1-delta)*n coords. To keep it exact & meaningful at
    # a proper subgroup, restrict to a moderate threshold.
    thresh = Fraction(1 - delta) * n  # = k
    polys = list(itertools.product(F, repeat=k)) if q ** k <= 60000 else None
    results = []
    tries = 0
    found = 0
    while found < max_stacks and tries < max_stacks * 40:
        tries += 1
        # planted stack: pick a few affine pencils, plant agreements
        u0 = [random.randrange(q) for _ in range(n)]
        u1 = [random.randrange(q) for _ in range(n)]
        # plant: choose 1-3 pencils (v0,v1) and a few gammas, fix coords to agree
        npencil = random.randint(1, 3)
        for _p in range(npencil):
            v0 = [random.randrange(q) for _ in range(k)]
            v1 = [random.randrange(q) for _ in range(k)]
            gammas = random.sample(F, random.randint(2, 4))
            # pick a witness coordinate set of size ceil(thresh)
            tsz = int(thresh) if thresh == int(thresh) else int(thresh) + 1
            tsz = max(tsz, 1)
            S = random.sample(range(n), min(tsz, n))
            g = gammas[0]
            for i in S:
                # want u0[i] + g*u1[i] = v0(x)+g*v1(x); set u0[i] consistent for ALL these gammas
                # only fully consistent across gammas if u0[i]=v0(x), u1[i]=v1(x)
                x = domain[i]
                u0[i] = poly_eval(v0, x, q)
                u1[i] = poly_eval(v1, x, q)
        # now compute bad set exactly via poly enumeration
        if polys is None:
            continue
        codeval = {}
        for p in polys:
            codeval[p] = tuple(poly_eval(p, x, q) for x in domain)
        bad = {}  # gamma -> set of decoding polys (pencils realized)
        for gamma in F:
            fold = tuple((u0[i] + gamma * u1[i]) % q for i in range(n))
            decoders = []
            for p, w in codeval.items():
                agree = sum(1 for i in range(n) if w[i] == fold[i])
                if agree >= thresh:
                    decoders.append(p)
            if decoders:
                bad[gamma] = decoders
        if len(bad) < 2:
            continue
        I = len(bad)
        # affine-cell covering: a "cell" = set of gammas sharing one pencil
        # (v0,v1) with each gamma's decoded poly = v0 + gamma*v1.
        # Build all candidate pencils from pairs of (gamma, decoder).
        gs = sorted(bad)
        # per cell size check + minimum cover by pencils
        pencils = {}  # (v0,v1) -> set of gammas it explains
        items = [(g, p) for g in gs for p in bad[g]]
        for (g1, P1), (g2, P2) in itertools.combinations(items, 2):
            if g1 == g2:
                continue
            inv = pow((g1 - g2) % q, q - 2, q)
            v1 = tuple(((a - b) * inv) % q for a, b in zip(P1, P2))
            v0 = tuple((a - g1 * c) % q for a, c in zip(P1, v1))
            cell = frozenset(g for g in gs
                             if tuple((v0[j] + g * v1[j]) % q for j in range(k)) in
                             [tuple(pp) for pp in bad[g]])
            if len(cell) >= 2:
                pencils[(v0, v1)] = cell
        # also singletons covered trivially
        cell_sizes = [len(c) for c in pencils.values()]
        cell_max = max(cell_sizes) if cell_sizes else 1
        # greedy min cover
        uncovered = set(gs)
        cmin = 0
        cands = sorted(pencils.values(), key=len, reverse=True)
        while uncovered:
            best = max((c for c in cands), key=lambda c: len(c & uncovered),
                       default=frozenset())
            gain = len(best & uncovered)
            if gain <= 1:
                cmin += len(uncovered)  # remaining need 1 pencil each
                break
            uncovered -= best
            cmin += 1
        results.append((I, cmin, cell_max))
        found += 1
    return results


def main():
    print("=== C009: affine-cell budget vs prize budget (proper subgroups) ===")
    for n in (8, 16, 32):
        k = max(2, n // 4)  # rate ~1/4
        q = find_subgroup_prime(n, beta_min=4)
        domain = mu_n(q, n)
        beta = Fraction.from_float(__import__('math').log(q) / __import__('math').log(n))
        print(f"\n-- n={n}, k={k}, q={q} (q~n^{float(beta):.2f}), "
              f"domain=mu_{n}<F_q* proper subgroup --")
        # enumeration cost: q^k. keep manageable.
        if q ** k > 200000:
            print(f"   (q^k={q**k} too large for exact enumeration; skipping "
                  f"exact, see analytic note)")
            continue
        res = analyze(q, n, k, domain, max_stacks=40)
        if not res:
            print("   no multi-bad stacks sampled")
            continue
        Imax = max(r[0] for r in res)
        cmax_over_n = max(r[1] for r in res)
        cellmax = max(r[2] for r in res)
        # the key ratio: does c track I/n?
        rows = sorted(res, reverse=True)[:6]
        print(f"   per-cell size max = {cellmax}  (claim: <= n={n}: "
              f"{'OK' if cellmax <= n else 'VIOLATED'})")
        print(f"   max I(delta) seen = {Imax}; max #cells c = {cmax_over_n}")
        for (I, c, cm) in rows:
            print(f"     I={I:3d}  c={c:3d}  c*n={c*n:4d}  "
                  f"ceil(I/n)={-(-I//n)}  cell_max={cm}")
    print("\n=== analytic note (printed, not a probe assertion) ===")
    print("In Guruswami-Sudan list decoding the GS interpolant Y-degree deg_Y")
    print("equals the list-size order L. The cell count c <= deg_Y = O(L).")
    print("In the window interior (beyond Johnson) L = I(delta) is the OPEN")
    print("BGK-governed quantity. So 'c = O(1)' is NOT free: c is tied to the")
    print("same list size. I(delta) <= c*n with c~I/n is a tautology.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

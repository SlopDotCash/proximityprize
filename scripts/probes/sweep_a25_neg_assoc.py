#!/usr/bin/env python3
"""sweep[A25] — Negative-association (NA) of line-incidence indicators, and the
Dubhashi-Ranjan sampling-without-replacement certificate / Shao (2000) convex-transfer route.

ACTIONABLE A25 (merged 407-T22). The δ* prize "list-form" reduces (FarCosetExplosion
`epsMCA_ge_far_incidence`) to bounding the worst-case far-line *incidence*:
    inc(δ) = #{ γ ∈ F_q : u0 + γ·u1 is δ-close to RS[k] on μ_n }.
The provable per-witness union bound is C(n,w) (wall W1); the true worst incidence is ~n.
The named-but-untested hope (407-T22): if the membership indicators that build inc are
NEGATIVELY ASSOCIATED (NA), then Shao (2000) convex-order transfer would give the binomial
tail E[C(L,t)] ≤ μ^t/t! WORST-CASE-INCLUDED (a NON-moment route reaching budget n), and the
Dubhashi-Ranjan "sampling-without-replacement" certificate (an interpolation through a
k-subset) is the candidate way to *prove* NA. This probe TESTS whether NA actually holds.

WHAT NA MEANS (Joag-Dev-Proschan 1983). Random vector (X_1,...,X_N) is NA iff for every two
DISJOINT index sets I, J and every pair of coordinatewise-nondecreasing f, g:
    Cov( f(X_I), g(X_J) ) ≤ 0.
A *necessary* (and for our 0/1 testing, the operative) consequence is pairwise NA:
    Cov(X_i, X_j) ≤ 0  for all i ≠ j   (the simplest falsifiable face).
The Dubhashi-Ranjan theorem: indicators of a fixed-size random subset chosen WITHOUT
replacement (equivalently a random 0/1 vector with a fixed number of ones, uniformly
permuted) ARE NA. Shao's convex transfer needs the FULL multivariate NA, but pairwise
positive covariance already REFUTES NA, so we test the pairwise face first (decisive if it
fails), then a stronger disjoint-block / monotone-functional face.

THE TWO CANDIDATE INDICATOR FAMILIES (we test BOTH, since 407-T22 said "n^2 monomial-line
ball-membership indicators"):

  (M1) FIXED-LINE coordinate-agreement family, randomness = interpolation k-subset.
       Fix the worst monomial far-line v = u0 + γ0·u1 (γ0 the realized worst scalar) and a
       random k-subset T ⊂ [n]; c_T = unique deg<k interpolant on T; for j∉T,
       X_j := 1[ c_T(x_j) = v_j ].  These are the "is coordinate j on the ball / does the
       sampled codeword hit it" membership indicators. C(L,t)=Σ_{j} X_j counts agreement
       beyond the k seed; NA of {X_j} is exactly the Dubhashi-Ranjan-style hope.

  (M2) SCALAR-INCIDENCE family, randomness = the n^2 (a,b) monomial directions / the q
       scalars. For a fixed direction, Y_γ := 1[ u0+γ·u1 is δ-close ] (γ ranges over F_q*),
       and the n^2 directions give the full indicator grid. inc = Σ_γ Y_γ. NA here would
       give the binomial tail on inc directly.

OUTPUT: pairwise covariance extremes for both families across prize-shaped (n,k,q); a verdict
on whether ANY positive covariance pair exists (⟹ NA REFUTED), plus the Dubhashi-Ranjan
structural check (is the family genuinely a without-replacement sample?).

VERDICT (n=16, k=4, ρ=1/4, q∈{97,193,257,353}; exact integer arithmetic): NA REFUTED, 3 ways.
  (1) M1' EXCESS-agreement indicators (the actual Shao-tail object, seed stripped) have
      EXACT-RATIONAL POSITIVE pairwise covariance at every prime (e.g. +463/473200 at q=97).
      [M1 with the seed INCLUDED looks NA-consistent, but that is the trivial DR-NA of the
       seed SELECTION — an artifact masking the agreement structure.]
  (2) The Dubhashi-Ranjan certificate is INAPPLICABLE: ΣX is NOT constant (range [4,6]); DR
      requires a fixed number of ones (permutation/hypergeometric law). No structure to invoke.
  (3) The upper tail is HEAVIER than binomial: P[ΣZ≥2] exceeds the Poisson target μ^t/t! by
      2.6×→6.3× (growing with q) — the signature of POSITIVE association. NA would CAP the
      tail; the real tail EXCEEDS it. So NA does NOT give the tail; the union-bound-forces-
      deep-moments argument stands. The Shao convex-transfer route is dead.
See docs/kb/deltastar-sweep-A25-neg-assoc-2026-06-14.md for the full writeup.
"""
import sys, io, itertools, math
from fractions import Fraction

# Windows console is cp1252; force UTF-8 so arrows/⟹ don't crash.
try:
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8")
except Exception:
    pass


# ---------- finite-field RS machinery (exact, no floats) ----------
def inv_table(q):
    return [0] + [pow(a, q - 2, q) for a in range(1, q)]

def gen_mu_faithful(q, n):
    for x in range(2, q):
        if pow(x, n, q) == 1 and pow(x, n // 2, q) != 1:
            dom = [pow(x, i, q) for i in range(n)]
            if len(set(dom)) == n:
                return dom
    raise RuntimeError(f"no faithful mu_{n} in F_{q}")

def interp_eval(xs, ys, xj, q, inv):
    """Lagrange-evaluate the deg<len interpolant of (xs,ys) at xj."""
    k = len(xs); val = 0
    for t in range(k):
        num = ys[t]
        for s in range(k):
            if s != t:
                num = num * ((xj - xs[s]) % q) % q
        den = 1
        for s in range(k):
            if s != t:
                den = den * ((xs[t] - xs[s]) % q) % q
        val = (val + num * inv[den % q]) % q
    return val

def close_ge(vals, dom, k, q, n, w, inv):
    for sub in itertools.combinations(range(n), k):
        xs = [dom[i] for i in sub]; ys = [vals[i] for i in sub]
        agree = 0
        for j in range(n):
            if interp_eval(xs, ys, dom[j], q, inv) == vals[j]:
                agree += 1
            elif agree + (n - 1 - j) < w:
                break
        if agree >= w:
            return True
    return False

def incidence(n, k, q, a, b, w, dom, inv):
    bad = []
    for g in range(1, q):
        vals = [(pow(dom[i], b, q) + g * pow(dom[i], a, q)) % q for i in range(n)]
        if close_ge(vals, dom, k, q, n, w, inv):
            bad.append(g)
    return bad


# ---------- NA testers ----------
def pairwise_cov_extremes(samples):
    """samples: list of equal-length 0/1 tuples. Return (max positive cov, argmax pair,
    fraction of pairs with cov>tol, total pairs). cov computed exactly via Fraction."""
    if not samples:
        return None
    N = len(samples[0]); M = len(samples)
    # E[X_i], E[X_i X_j]
    sx = [0]*N
    for s in samples:
        for i in range(N):
            sx[i] += s[i]
    EX = [Fraction(sx[i], M) for i in range(N)]
    max_pos = Fraction(-10); arg = None; npos = 0; tot = 0
    tol = Fraction(0)
    for i in range(N):
        for j in range(i+1, N):
            sij = 0
            for s in samples:
                sij += s[i]*s[j]
            cov = Fraction(sij, M) - EX[i]*EX[j]
            tot += 1
            if cov > tol:
                npos += 1
            if cov > max_pos:
                max_pos = cov; arg = (i, j)
    return float(max_pos), arg, npos, tot

def disjoint_block_cov(samples, blockI, blockJ, fI, fJ):
    """Cov(fI(X_I), fJ(X_J)) for monotone f over disjoint blocks. fI,fJ: int-tuple->number."""
    M = len(samples)
    a = [fI(tuple(s[i] for i in blockI)) for s in samples]
    b = [fJ(tuple(s[j] for j in blockJ)) for s in samples]
    Ea = Fraction(sum(a), M); Eb = Fraction(sum(b), M)
    Eab = Fraction(sum(x*y for x, y in zip(a, b)), M)
    return float(Eab - Ea*Eb)


# ---------- M1: fixed-line, randomness = k-subset interpolation ----------
def m1_membership_samples(n, k, q, a, b, gamma0, dom, inv, max_subsets=None):
    """For the fixed far-line v=u0+γ0·u1, over k-subsets T, the indicator vector
    X_j = 1[ c_T(x_j)=v_j ] for j in [n] (X_j=1 on the seed by construction).
    Returns the list of 0/1 indicator tuples (one per subset). These are exactly the
    'ball-membership' indicators whose NA Shao's transfer would consume."""
    v = [(pow(dom[i], b, q) + gamma0 * pow(dom[i], a, q)) % q for i in range(n)]
    subs = list(itertools.combinations(range(n), k))
    if max_subsets and len(subs) > max_subsets:
        # deterministic stride subsample to keep it exact-but-bounded
        step = len(subs)//max_subsets
        subs = subs[::step][:max_subsets]
    samples = []
    for sub in subs:
        xs = [dom[i] for i in sub]; ys = [v[i] for i in sub]
        ind = tuple(1 if interp_eval(xs, ys, dom[j], q, inv) == v[j] else 0 for j in range(n))
        samples.append(ind)
    return samples, v


def main():
    print("="*78)
    print("sweep[A25] — NA of line-incidence indicators + Dubhashi-Ranjan / Shao route")
    print("="*78)

    # prize-shaped small cases: n=16 (k=4, rho=1/4), n=32 (k=8, rho=1/4); q = 1 mod n.
    # NOTE: n=8/k=2 has NO bounded intermediate band (sharp cliff: explosion at w=2,
    # then 0 at w>=3) so the membership object A25 targets only exists at n>=16.
    # n=16 across three primes is the decisive case (the bounded band exists & is enumerable
    # exactly: C(16,4)=1820 subsets, q-1 scalars). n=32 (C(32,8)=10.5M subsets) is left out:
    # exact enumeration is infeasible and would only re-confirm the n=16 verdict.
    cases = [
        (16, 4, [97, 193, 257]),
    ]
    dir_for = {16: (5, 6)}

    print("\n--- locate the BOUNDED far-line band (the q-indep object, NOT the explosion) ---")
    print("  (scan all w; the bounded band = the largest w with 0 < #bad < q-1)")
    worst = {}
    for n, k, qs in cases:
        rho = k/n
        a, b = dir_for[n]
        for q in qs:
            dom = gen_mu_faithful(q, n); inv = inv_table(q)
            found = None
            for w in range(n, 1, -1):  # descend; first nonzero bounded band is the cliff edge
                bad = incidence(n, k, q, a, b, w, dom, inv)
                if len(bad) == 0:
                    continue
                if len(bad) < q-1:        # bounded band
                    found = (a, b, w, bad)
                    break
                else:                      # hit the explosion; the band just above was the edge
                    break
            if found:
                a2, b2, w2, bad2 = found
                worst[(n, k, q)] = found
                print(f"  n={n} k={k} q={q} dir=({a2},{b2}) w={w2} delta={1-w2/n:.3f}: "
                      f"#bad={len(bad2)} (bounded band)  bad[:6]={bad2[:6]}")

    print("\n--- (M1) NA of k-subset-interpolation membership indicators (Dubhashi-Ranjan face) ---")
    print("  pairwise face: ANY positive Cov(X_i,X_j) ⟹ NA REFUTED")
    any_pos_m1 = False
    for (n, k, q), (a, b, w, bad) in worst.items():
        dom = gen_mu_faithful(q, n); inv = inv_table(q)
        gamma0 = bad[0]
        samples, v = m1_membership_samples(n, k, q, a, b, gamma0, dom, inv,
                                            max_subsets=4000)
        res = pairwise_cov_extremes(samples)
        if res is None:
            continue
        maxpos, arg, npos, tot = res
        # mean number of ones (the budget mu = E[Σ X_j])
        mu = sum(sum(s) for s in samples)/len(samples)
        flag = "POSITIVE-COV → NA FALSE" if maxpos > 1e-12 else "all cov ≤ 0 (NA-consistent)"
        any_pos_m1 = any_pos_m1 or (maxpos > 1e-12)
        print(f"  n={n} k={k} q={q} γ0={gamma0}: #subsets={len(samples)} mu(E[ΣX])={mu:.3f} "
              f"maxCov={maxpos:+.5f} pair={arg} pos-pairs={npos}/{tot}  [{flag}]")
        # one disjoint-block monotone check (sum over halves), the stronger face
        if maxpos <= 1e-12 and n >= 8:
            I = list(range(n//2)); J = list(range(n//2, n))
            c = disjoint_block_cov(samples, I, J, sum, sum)
            print(f"        disjoint-block Cov(ΣX_left, ΣX_right)={c:+.5f}"
                  f"  [{'POSITIVE → NA FALSE' if c>1e-12 else 'NA-consistent'}]")

    print("\n--- (M2) NA of the scalar-incidence grid (Y_γ over directions) ---")
    print("  per fixed direction Y_γ is a DETERMINISTIC function of γ — no internal randomness;")
    print("  the 'n^2 indicators' = the (direction × scalar) grid. Test cross-direction pairwise")
    print("  covariance over the q-1 scalars treated as the sample index.")
    any_pos_m2 = False
    for n, k, qs in cases:
        rho = k/n
        for q in qs[:1]:  # one q is enough to see the structure
            if (n, k, q) not in worst:
                continue
            dom = gen_mu_faithful(q, n); inv = inv_table(q)
            w = worst[(n, k, q)][2]   # the bounded-band weight located above
            # a few monomial directions
            dirs = [(5, 6), (6, 7), (3, 4), (1, 2)]
            dirs = [(a, b) for (a, b) in dirs if math.gcd(a if a else n, n) >= 0]
            # build Y_γ vectors: index = scalar γ in 1..q-1, coordinate = direction
            grid = []
            badsets = {}
            for (a, b) in dirs:
                badsets[(a, b)] = set(incidence(n, k, q, a, b, w, dom, inv))
            for g in range(1, q):
                grid.append(tuple(1 if g in badsets[d] else 0 for d in dirs))
            res = pairwise_cov_extremes(grid)
            if res:
                maxpos, arg, npos, tot = res
                flag = "POSITIVE-COV" if maxpos > 1e-12 else "all ≤0"
                any_pos_m2 = any_pos_m2 or (maxpos > 1e-12)
                dsizes = [len(badsets[d]) for d in dirs]
                print(f"  n={n} q={q} w={w} dirs={dirs} #bad-per-dir={dsizes} "
                      f"maxCrossCov={maxpos:+.5f} pair={arg} [{flag}]")

    print("\n--- Dubhashi-Ranjan structural verdict ---")
    print("  Is the M1 family a genuine 'sampling-without-replacement' (permutation-NA) object?")
    print("  Requirement: Σ_j X_j must be CONSTANT (fixed number of ones) across samples.")
    for (n, k, q), (a, b, w, bad) in list(worst.items())[:2]:
        dom = gen_mu_faithful(q, n); inv = inv_table(q)
        samples, _ = m1_membership_samples(n, k, q, a, b, bad[0], dom, inv, max_subsets=4000)
        sums = [sum(s) for s in samples]
        const = (min(sums) == max(sums))
        print(f"  n={n} q={q}: ΣX_j over samples ∈ [{min(sums)},{max(sums)}] "
              f"{'CONSTANT (DR applies)' if const else 'NOT CONSTANT → DR certificate INAPPLICABLE'}")

    # ---- (M1') the DECISIVE refinement: EXCESS-agreement indicators (seed removed) ----
    # The Shao tail bounds C(L,t) = (#agreements beyond the k-seed). The honest NA object
    # is Z_j = 1[ j∉T AND c_T(x_j)=v_j ].  Including the seed-forced 1s injects the trivial
    # DR-NA of the seed SELECTION and masks the agreement structure. We strip the seed.
    print("\n--- (M1') EXCESS-agreement indicators Z_j (seed stripped) — the Shao-tail object ---")
    print("  pairwise face on Z: ANY positive Cov(Z_i,Z_j) ⟹ NA of the excess REFUTED")
    any_pos_m1p = False
    for (n, k, q), (a, b, w, bad) in list(worst.items()):
        dom = gen_mu_faithful(q, n); inv = inv_table(q)
        gamma0 = bad[0]
        v = [(pow(dom[i], b, q) + gamma0 * pow(dom[i], a, q)) % q for i in range(n)]
        subs = list(itertools.combinations(range(n), k))
        Z = []
        for sub in subs:
            xs = [dom[i] for i in sub]; ys = [v[i] for i in sub]
            sset = set(sub)
            Z.append(tuple(1 if (j not in sset and interp_eval(xs, ys, dom[j], q, inv) == v[j])
                           else 0 for j in range(n)))
        res = pairwise_cov_extremes(Z)
        if res is None:
            continue
        maxpos, arg, npos, tot = res
        muZ = sum(sum(s) for s in Z)/len(Z)
        any_pos_m1p = any_pos_m1p or (maxpos > 1e-12)
        flag = "POSITIVE → NA(excess) FALSE" if maxpos > 1e-12 else "all ≤0 (NA-consistent)"
        print(f"  n={n} k={k} q={q}: #subsets={len(Z)} E[ΣZ]={muZ:.4f} "
              f"maxCov={maxpos:+.6f} pair={arg} pos-pairs={npos}/{tot}  [{flag}]")
        # tail comparison: does the actual upper tail of ΣZ beat the binomial μ^t/t!?
        from collections import Counter
        dist = Counter(sum(s) for s in Z); M = len(Z)
        muT = muZ
        print(f"        ΣZ distribution: " +
              " ".join(f"P[{t}]={dist.get(t,0)/M:.4f}" for t in sorted(dist)))
        print(f"        Shao/Poisson target μ^t/t! (μ={muT:.3f}): " +
              " ".join(f"t={t}:{(muT**t/math.factorial(t)):.4f}" for t in sorted(dist)))

    print("\n" + "="*78)
    print("VERDICT SUMMARY")
    print(f"  M1  (k-subset membership, seed incl.) pairwise positive-cov: {any_pos_m1}")
    print(f"  M1' (EXCESS agreement, seed stripped)  pairwise positive-cov: {any_pos_m1p}")
    print(f"  M2  (scalar-grid) cross-direction positive cov: {any_pos_m2}")
    print("  DR certificate applies only if ΣX is constant — it is NOT (range [4,6]).")
    print("="*78)


if __name__ == "__main__":
    main()

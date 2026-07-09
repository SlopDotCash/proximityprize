#!/usr/bin/env python3
"""sweep_A37_sunflower.py  --  N3 strengthened window-localization (#371, actionable A37).

ACTIONABLE A37 (merged 371-T09).  Run the decisive instance of the "N3 sunflower"
window-localization question, which was scoped (371-T09) but never run.

================================  THE QUESTION  ================================
Model (interleaved MCA for RS[F_q, mu_n, k], rate rho=k/n, degree d=k-1).  A
"direction"/line is a pair (u0,u1) of words on the smooth domain D=mu_n.  A scalar
gamma is BAD (explainable) at agreement threshold a if the line word u0+gamma*u1
agrees with SOME codeword c (deg<=d) on >= a points (a = ceil((1-delta) n)).

Window: delta in (1-sqrt(rho), 1-rho) = (Johnson, capacity)  <=>  agreement a in
(k, ceil(sqrt(rho)*n)] = (capacity, Johnson).  Larger a = smaller delta = nearer
Johnson; the "below-saturation" / window-interior bands are a just below Johnson
(heaviness NOT yet generic, unlike at the ceiling where it was refuted).
UDR (agreement form): a_UDR = ceil((n+k)/2).

A direction is HEAVY if #bad(line) exceeds what a generic/unique-decode direction
gives (operationally: #bad >= 2, and above the median; we track the record).

Proven WINDOW localization (easy side): each codeword c agrees with u1 (the
DIRECTION word) on <= n - w - k points (w = window witness size), because u1 does
not fit deg-d on the witness window.  n-w-k is DECREASING in w.

TARGET (N3): a heavy direction FORCES some codeword to agree with u1 on >= w + k
points.  w+k is INCREASING in w; the two cross at w = (n-2k)/2 ~ UDR.  Since w+k
exceeds the single-window witness size a, the extra agreement cannot come from one
window -- it must come from the OVERLAP/SUNFLOWER structure (common core + petals)
of the witness family {A(gamma) : gamma bad}.  Even an exponential-q window closed
this way (below saturation) would be NEW.

DECISIVE INSTANCE (spec): (q,n,k) ~ (1009,16,2) and the (8..16,2..3) family with
q >> n*(1/rho)^k.  EXACT arithmetic mod q.

FAST CORE: for a fixed base B (size d+1), codeword(x_i) is a FIXED Z-linear combo
L[B][i] . word[base] of the base values (depends only on the domain, precomputed
once).  Since word_j = u0_j + gamma*u1_j is affine in gamma, codeword(x_i)-word_i
is AFFINE in gamma: alpha_i + gamma*beta_i.  Agreement at i (for base B) holds iff
alpha_i + gamma*beta_i == 0 mod q -- one gamma (beta_i != 0) or all gamma (both 0).
So per base we get the agreement set as a function of gamma WITHOUT scanning all q.

Honesty: EVIDENCE only (verify/refute the sunflower-forcing at small n), never a
proof.  Exit 0 always; the verdict is the printed tables + the kb note.
"""
import argparse
import itertools
import sys
from collections import defaultdict
from math import isqrt


def inv(a, q):
    return pow(a % q, q - 2, q)


def find_smooth_domain(q, n):
    if (q - 1) % n:
        return None
    for g in range(2, q):
        x = pow(g, (q - 1) // n, q)
        if x == 1:
            continue
        S = {pow(x, i, q) for i in range(n)}
        if len(S) == n:
            return [pow(x, i, q) for i in range(n)]
    return None


def lagrange_coeffs(dom, q, d):
    """L[B] is a dict: for base B (tuple of d+1 indices), L[B][i] = list of d+1
    coeffs s.t. codeword(dom[i]) = sum_j L[B][i][j]*word[B[j]].  Precomputed per q."""
    n = len(dom)
    bases = list(itertools.combinations(range(n), d + 1))
    L = {}
    for B in bases:
        bx = [dom[b] for b in B]
        row = {}
        for i in range(n):
            x = dom[i]
            coeff = []
            for j in range(d + 1):
                num = den = 1
                for kk in range(d + 1):
                    if kk != j:
                        num = num * ((x - bx[kk]) % q) % q
                        den = den * ((bx[j] - bx[kk]) % q) % q
                coeff.append(num * inv(den, q) % q)
            row[i] = coeff
        L[B] = row
    return bases, L


def bad_scalars_fast(dom, u0, u1, d, a, q, bases, L):
    """All bad gammas at threshold a, with their agreement sets.
    Returns dict gamma -> set of frozenset agreement sets (size>=a, deg<=d-fit)."""
    n = len(dom)
    # per base B: agreement at i is alpha_i + gamma*beta_i == 0.
    # alpha_i = (sum_j L[B][i][j]*u0[B[j]]) - u0[i];  beta_i = (...*u1...) - u1[i].
    # Collect, for each gamma, the set of indices i that agree (for THIS base) and
    # union across bases per gamma.  But agreement is base-specific only via which
    # codeword; the agreement SET of a codeword = all i with alpha_i+gamma*beta_i=0.
    # We bucket per gamma the indices that vanish, per base, then per (base,gamma)
    # the agreement set is exactly that index set.
    bad = defaultdict(set)
    for B in bases:
        row = L[B]
        # alpha, beta per i
        alpha = {}
        beta = {}
        always = []  # i with alpha_i==beta_i==0 (agree for every gamma)
        one_g = defaultdict(list)  # gamma -> [i] that agree only at this gamma
        for i in range(n):
            c = row[i]
            ai = (sum(c[j] * u0[B[j]] for j in range(d + 1)) - u0[i]) % q
            bi = (sum(c[j] * u1[B[j]] for j in range(d + 1)) - u1[i]) % q
            if bi == 0:
                if ai == 0:
                    always.append(i)
                # else: never agrees (no gamma) -> skip
            else:
                g = (-ai) * inv(bi, q) % q
                one_g[g].append(i)
        base_always = set(always)
        # the base points B always agree with their own codeword (alpha=beta=0):
        # they are included in `always` automatically (coeff row is identity there).
        for g, idxs in one_g.items():
            agree = base_always | set(idxs)
            if len(agree) >= a:
                bad[g].add(frozenset(agree))
        # if base_always alone already >= a, every gamma is bad with that set:
        if len(base_always) >= a:
            # this means u0,u1 both fit deg-d on base_always for all gamma -> the
            # whole line is degenerate on those points; record at a representative.
            # (rare; mark all gammas would be O(q).  We note it via a sentinel.)
            bad[None].add(frozenset(base_always))
    return bad


def max_agree_with_word(dom, word, d, q, bases, L):
    """max over deg<=d codewords c of |{i : c(x_i)==word_i}|."""
    n = len(dom)
    best = 0
    for B in bases:
        row = L[B]
        cnt = 0
        for i in range(n):
            c = row[i]
            val = sum(c[j] * word[B[j]] for j in range(d + 1)) % q
            if val == word[i] % q:
                cnt += 1
        if cnt > best:
            best = cnt
    return best


def sunflower_anatomy(family):
    """family = list of frozensets. Returns (core, union, is_sunflower, n)."""
    if not family:
        return frozenset(), frozenset(), True, 0
    core = family[0]
    uni = family[0]
    for A in family[1:]:
        core &= A
        uni |= A
    is_sun = True
    for i in range(len(family)):
        for j in range(i + 1, len(family)):
            if family[i] & family[j] != core:
                is_sun = False
                break
        if not is_sun:
            break
    return core, uni, is_sun, len(family)


def run_instance(q, n, k, n_rand, seed, label):
    import random
    rng = random.Random(seed)
    dom = find_smooth_domain(q, n)
    if dom is None:
        print(f"[{label}] q={q} n={n}: no smooth domain; SKIP")
        return None
    d = k - 1
    rho = k / n
    aJ = isqrt(k * n)
    if aJ * aJ < k * n:
        aJ += 1
    aUDR = (n + k + 1) // 2
    a_lo = k + 1            # just above capacity
    a_hi = aJ               # Johnson edge (below-saturation interior is a near aJ)
    bases, L = lagrange_coeffs(dom, q, d)
    thr = n * (n / k) ** k
    print(f"\n=== [{label}] q={q} n={n} k={k} d={d} rho={rho:.4f} "
          f"| a(cap)={k} a(UDR)={aUDR} a(Johnson)={aJ} | n(1/rho)^k={thr:.3g} "
          f"q>>thr:{'OK' if q > 4 * thr else 'tight'} ===", flush=True)
    if a_lo > a_hi:
        print(f"    window empty (k+1={a_lo} > Johnson={aJ}); SKIP")
        return None

    # candidate heavy directions: u1 = power monomials (classic heavy), u0 varied;
    # plus random directions.
    directions = []
    for e1 in range(0, min(n, k + 6)):
        u1 = [pow(x, e1, q) for x in dom]
        for _ in range(4):
            u0 = [rng.randrange(q) for _ in range(n)]
            directions.append((u0, u1, f"u1=x^{e1}"))
    for _ in range(n_rand):
        directions.append(([rng.randrange(q) for _ in range(n)],
                           [rng.randrange(q) for _ in range(n)], "rand"))

    # per band a: keep the heaviest direction
    by_a = {}
    for (u0, u1, tag) in directions:
        for a in range(a_lo, a_hi + 1):
            bad = bad_scalars_fast(dom, u0, u1, d, a, q, bases, L)
            bad.pop(None, None)  # drop degenerate sentinel for counting
            cnt = len(bad)
            if a not in by_a or cnt > by_a[a][0]:
                by_a[a] = (cnt, u0, u1, tag, bad)

    rows = []
    for a in sorted(by_a):
        cnt, u0, u1, tag, bad = by_a[a]
        if cnt < 2:
            continue
        all_w = [A for sets in bad.values() for A in sets]
        if not all_w:
            continue
        w = min(len(A) for A in all_w)           # window witness weight
        core, uni, is_sun, npet = sunflower_anatomy(all_w)
        mau1 = max_agree_with_word(dom, u1, d, q, bases, L)
        proven_ceiling = n - w - k
        target_floor = w + k
        band = ("above-UDR" if a >= aUDR else
                "Johnson-edge" if a == aJ else
                "sub-Johnson(interior)")
        n3 = mau1 >= target_floor
        rows.append((a, band, cnt, w, len(core), len(uni), is_sun, npet,
                     mau1, proven_ceiling, target_floor, n3, tag))

    if not rows:
        print("    no HEAVY (#bad>=2) in-window directions found")
        return None
    hdr = (f"    {'a':>3} {'band':<22} {'#bad':>4} {'w':>3} {'core':>4} "
           f"{'uni':>4} {'sun':>5} {'pet':>4} {'mAg(u1)':>7} {'n-w-k':>6} "
           f"{'w+k':>4} {'N3':>4} dir")
    print(hdr)
    for r in rows:
        (a, band, cnt, w, nc, nu, sun, pet, mau1, pc, tf, n3, tag) = r
        print(f"    {a:>3} {band:<22} {cnt:>4} {w:>3} {nc:>4} {nu:>4} "
              f"{str(sun):>5} {pet:>4} {mau1:>7} {pc:>6} {tf:>4} "
              f"{('YES' if n3 else 'no'):>4} {tag}")
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    nr = 30 if args.quick else 120

    print("#" * 78)
    print("# A37 / N3 sunflower window-localization -- decisive instance + family")
    print("#" * 78)

    all_rows = []

    def collect(tag, r):
        if r:
            all_rows.extend((tag,) + x for x in r)

    # DECISIVE INSTANCE
    collect("1009,16,2", run_instance(1009, 16, 2, nr, 11, "DECISIVE (1009,16,2)"))

    # (8..16, 2..3) family with q >> n*(1/rho)^k
    family = [
        (2113, 8, 2),
        (3217, 8, 3),
        (1873, 16, 2),
        (8161, 16, 3),
        (1153, 12, 2),
        (1429, 12, 3),
    ]
    for (q, n, k) in family:
        collect(f"{q},{n},{k}", run_instance(q, n, k, nr, 17 + q, f"family ({q},{n},{k})"))

    # field-independence ladder at (16,2)
    print("\n" + "=" * 60)
    print("Field-independence ladder (n=16,k=2):")
    for q in (97, 113, 193, 257, 1009, 1873):
        if (q - 1) % 16 == 0:
            collect(f"ladder:{q}", run_instance(q, 16, 2, max(20, nr // 2),
                                                31 + q, f"ladder q={q} (16,2)"))

    # SUMMARY
    print("\n" + "#" * 78)
    print("# SUMMARY")
    print("#" * 78)
    below = [r for r in all_rows if r[2].startswith("sub-Johnson") or r[2] == "Johnson-edge"]
    n3_held = [r for r in below if r[-2]]      # n3 flag is second-last (before tag)
    sun_held = [r for r in n3_held if r[7]]    # is_sun col (index 7 after tag prefix)
    print(f"below-saturation heavy bands measured : {len(below)}")
    print(f"  N3 forcing held (maxAg(u1) >= w+k)  : {len(n3_held)}")
    print(f"  ... and witness family WAS sunflower: {len(sun_held)}")
    crossed = [r for r in below if r[-3] > r[-4]]  # w+k > n-w-k
    print(f"  bands ABOVE the crossing (w+k>n-w-k): {len(crossed)}")
    print("\nBelow-saturation heavy bands (full detail):")
    print(f"  {'inst':<14}{'a':>3}{'#bad':>5}{'w':>3}{'core':>5}{'sun':>6}"
          f"{'mAg(u1)':>8}{'n-w-k':>7}{'w+k':>5}{'N3':>4}")
    for r in below:
        inst, a, band, cnt, w, nc, nu, sun, pet, mau1, pc, tf, n3, tag = r
        print(f"  {inst:<14}{a:>3}{cnt:>5}{w:>3}{nc:>5}{str(sun):>6}"
              f"{mau1:>8}{pc:>7}{tf:>5}{('Y' if n3 else 'n'):>4}")
    print("\nDONE.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

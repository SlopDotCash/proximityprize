#!/usr/bin/env python3
"""Multi-core ladder optimization for the exact-rate-half prize bracket (thread rh:multicore-optimize).

After the three-core radix counterexample killed the 31/64 pin, this probe derives and
certifies the OPTIMIZED c-core construction at general agreement threshold.

Arithmetic frame (quotient size s, fibers of size m, n = s*m, base code RS_{s/2} on mu_s):
  * c cores, each a fiber subset of size a = s/2 + g  (g >= 1 excess),
  * spline codimension c*g, defect dimension d = s/2 - c*g  (need d >= 2),
  * base defect directions D_base = c*(s - a) = c*(s/2 - g),
  * radix/coset lift multiplies by m: D = D_base * m distinct bad scalars,
  * agreement threshold t = a*m + 1, bad error e = (s/2 - g)*m - 1,
  * first-field budget: D >= n + 1  <=>  c*(s/2 - g) >= s + 1,
  * second-field budget: D >= 2n + 1 <=>  c*(s/2 - g) >= 2s + 1.

Coset trick: with u0(x) = x*w0(x^m), u1(x) = w1(x^m) for base spline words w0, w1,
the bad scalar for direction (core i, outside fiber y=zeta^j, fiber point x) is
gamma = rho_{ij} * x, so the gamma set of one direction family is the multiplicative
coset rho_{ij}*g^j*mu_m.  Cosets of the subgroup mu_m are equal or disjoint, so the
count certificate reduces to pairwise distinctness of the 66 labels (rho*g^j)^m.

Parts:
  1. closed-form (c, g) ladder scan at s = 64 for both field budgets,
  2. exact mod-P certificate at the optimum (c=3, a=42) for the first prize field,
     and (c=5, a=38) for the second prize field,
  3. exact end-to-end toy validation (RS[16,8] over mu_16 in F_4001, c=2, a=5),
     brute-forcing every gamma and checking the mcaEvent count and properness,
  4. stop-point: g = 11 infeasible at s = 64; dyadic s-ladder; the family floor
     3*(e+1) >= n + 2m, attained at e = 357913941 (m = 1).
"""

import itertools
import random

# ---------------------------------------------------------------- field data
P1 = 365375409332725729550921208179070755120141565953
G1 = 303645430271030343624574566109998498685964493478  # order 2^30 mod P1
P2 = 730750818665451459101842416358141509841924915201
G2 = 192152681249815148642741928588691886362054863855  # order 2^30 mod P2

N = 2 ** 30


# ---------------------------------------------------------------- linear algebra mod p
def inverse(v, p):
    return pow(v, p - 2, p)


def rref(rows, p, width):
    """Row-reduce; returns (reduced_rows, pivot_columns)."""
    rows = [r[:] for r in rows if any(r)]
    out, pivots = [], []
    for col in range(width):
        src = next((i for i, r in enumerate(rows) if r[col] % p), None)
        if src is None:
            continue
        row = rows.pop(src)
        inv = inverse(row[col], p)
        row = [x * inv % p for x in row]
        rows = [
            [(x - r[col] * y) % p for x, y in zip(r, row)] if r[col] else r
            for r in rows
        ]
        out = [
            [(x - r[col] * y) % p for x, y in zip(r, row)] if r[col] else r
            for r in out
        ]
        out.append(row)
        pivots.append(col)
        if not rows:
            break
    return out, pivots


def reduce_vector(vec, rows, pivots, p):
    vec = vec[:]
    for row, piv in zip(rows, pivots):
        c = vec[piv] % p
        if c:
            vec = [(x - c * y) % p for x, y in zip(vec, row)]
    return vec


def kernel_basis(rows, p, width):
    """Basis of the right kernel of the row space."""
    red, pivots = rref(rows, p, width)
    free = [c for c in range(width) if c not in pivots]
    basis = []
    for f in free:
        v = [0] * width
        v[f] = 1
        for row, piv in zip(red, pivots):
            v[piv] = (-row[f]) % p
        basis.append(v)
    return basis


# ---------------------------------------------------------------- part 1: ladder scan
def feasible(s, c, g, budget_mult):
    return g >= 1 and c * g + 2 <= s // 2 and c * (s // 2 - g) >= budget_mult * s + 1


def part1():
    print("== part 1: (c, g) feasibility scan at s = 64 ==")
    for budget, tag in ((1, "first field (need c*(32-g) >= 65)"),
                        (2, "second field (need c*(32-g) >= 129)")):
        best = None
        rows = []
        for g in range(1, 15):
            ok = [c for c in range(2, 32) if feasible(64, c, g, budget)]
            if ok:
                rows.append((g, ok))
                best = (g, ok)
        for g, ok in rows:
            m = 2 ** 24
            e = (32 - g) * m - 1
            print(f"  budget x{budget}: g={g:2d} a={32+g} feasible c in {ok} "
                  f"-> e = {e} delta ~ {e / N:.9f}")
        assert best is not None
        g, ok = best
        print(f"  {tag}: deepest feasible g = {g} (a = {32 + g}), c = {ok}")
    # two cores never beat even the first-field budget at any s (parity: c=2)
    for s in (8, 16, 32, 64, 128, 256):
        assert not any(feasible(s, 2, g, 1) for g in range(1, s)), s
    print("  c = 2 infeasible at every s (checked s <= 256): PASS")
    print()


# ---------------------------------------------------------------- core machinery
def parity_rows_for_core(core, dom, kq, p):
    """Basis of functionals supported on `core` vanishing on RS_kq (deg < kq)."""
    a = len(core)
    vand = [[pow(dom[c], d, p) for c in core] for d in range(kq)]
    ker = kernel_basis(vand, p, a)  # dim a - kq expected
    rows = []
    for kv in ker:
        row = [0] * len(dom)
        for idx, c in enumerate(core):
            row[c] = kv[idx]
        rows.append(row)
    return rows


def lagrange_weights(points, x, dom, p):
    """Weights L_h(x) for interpolation basis on `points` evaluated at x (all in dom idx)."""
    ws = []
    for h in points:
        num, den = 1, 1
        for h2 in points:
            if h2 != h:
                num = num * (dom[x] - dom[h2]) % p
                den = den * (dom[h] - dom[h2]) % p
        ws.append(num * inverse(den, p))
    return ws


def defect_functional(core, outside, dom, kq, p):
    """Raw functional w |-> w(outside) - (interp of w on first kq core pts)(outside)."""
    pts = sorted(core)[:kq]
    row = [0] * len(dom)
    row[outside] = 1
    for h, w in zip(pts, lagrange_weights(pts, outside, dom, p)):
        row[h] = (-w) % p
    return row


def dot(row, vec, p):
    return sum(r * v for r, v in zip(row, vec)) % p


def certify_multicore(p, gbig, s, m, kq, a, c, tag, seed=0):
    """Exact certificate: c cores of size a on mu_s; returns witness dict or None."""
    rng = random.Random(seed)
    zeta = pow(gbig, m, p)
    assert pow(zeta, s, p) == 1 and pow(zeta, s // 2, p) == p - 1
    dom = [pow(zeta, j, p) for j in range(s)]
    for attempt in range(60):
        cores = [sorted(rng.sample(range(s), a)) for _ in range(c)]
        rows = []
        for core in cores:
            pr = parity_rows_for_core(core, dom, kq, p)
            if len(pr) != a - kq:
                break
            rows.extend(pr)
        else:
            red, pivots = rref(rows, p, s)
            if len(red) != c * (a - kq):
                continue  # dependent parity checks; resample
            # defect directions
            dirs = []  # (core index, outside j, raw functional)
            for ci, core in enumerate(cores):
                for j in range(s):
                    if j not in core:
                        dirs.append((ci, j, defect_functional(core, j, dom, kq, p)))
            reduced = [reduce_vector(d[2], red, pivots, p) for d in dirs]
            if any(not any(v) for v in reduced):
                continue
            # invariant: reduced directions span exactly dim (s - c*(a-kq)) - kq
            span_rank = len(rref(reduced, p, s)[0])
            want_rank = s - c * (a - kq) - kq
            norm = []
            for v in reduced:
                lead = next(x for x in v if x)
                inv = inverse(lead, p)
                norm.append(tuple(x * inv % p for x in v))
            n_distinct = len(set(norm))
            if n_distinct != len(dirs):
                continue
            # spline words: kernel of the parity rows (dim s - c*(a-kq))
            wbasis = kernel_basis(rows, p, s)
            for _ in range(40):
                c0 = [rng.randrange(p) for _ in wbasis]
                c1 = [rng.randrange(p) for _ in wbasis]
                w0 = [sum(cc * b[i] for cc, b in zip(c0, wbasis)) % p
                      for i in range(s)]
                w1 = [sum(cc * b[i] for cc, b in zip(c1, wbasis)) % p
                      for i in range(s)]
                d0 = [dot(d[2], w0, p) for d in dirs]
                d1 = [dot(d[2], w1, p) for d in dirs]
                if any(x == 0 for x in d0) or any(x == 0 for x in d1):
                    continue
                # rho = (w0(j) - A(zeta^j)) / (R(zeta^j) - w1(j)) = d0 / (-d1)
                rho = [x * inverse((-y) % p, p) % p for x, y in zip(d0, d1)]
                labels = [pow(r * pow(gbig, d[1], p) % p, m, p)
                          for r, d in zip(rho, dirs)]
                if len(set(labels)) != len(dirs):
                    continue
                print(f"  {tag}: cores(size {a}) x{c} rank={len(red)} "
                      f"defect_dim={want_rank} span_rank={span_rank}")
                print(f"    base directions = {len(dirs)}, all projectively distinct; "
                      f"labels (rho*g^j)^m pairwise distinct")
                count = len(dirs) * m
                print(f"    lifted bad-scalar count = {len(dirs)}*m = {count}")
                return dict(cores=cores, dirs=dirs, rho=rho, labels=labels,
                            w0=w0, w1=w1, dom=dom, red=red, pivots=pivots,
                            count=count)
    return None


def spot_check_fresh_identity(p, gbig, s, m, kq, wit, samples=8, seed=1):
    """Verify the per-direction fresh-point identity on the lifted domain."""
    rng = random.Random(seed)
    dom = wit["dom"]
    for _ in range(samples):
        di = rng.randrange(len(wit["dirs"]))
        ci, j, _ = wit["dirs"][di]
        core = wit["cores"][ci]
        pts = sorted(core)[:kq]
        # interpolants of w0, w1 on the core, evaluated at zeta^j
        wA = lagrange_weights(pts, j, dom, p)
        Aj = sum(w * wit["w0"][h] for w, h in zip(wA, pts)) % p
        Rj = sum(w * wit["w1"][h] for w, h in zip(wA, pts)) % p
        # check interpolant consistency on the remaining core points (w0, w1 in spline)
        extra = [h for h in core if h not in pts]
        for h in extra[:3]:
            wH = lagrange_weights(pts, h, dom, p)
            assert sum(w * wit["w0"][q] for w, q in zip(wH, pts)) % p == wit["w0"][h]
            assert sum(w * wit["w1"][q] for w, q in zip(wH, pts)) % p == wit["w1"][h]
        t = rng.randrange(m)
        x = pow(gbig, j + s * t, p)  # fiber point above zeta^j
        assert pow(x, m, p) == dom[j]
        gamma = wit["rho"][di] * x % p
        lhs = (x * Aj + gamma * Rj) % p
        rhs = (x * wit["w0"][j] + gamma * wit["w1"][j]) % p
        assert lhs == rhs, "fresh identity failed"
        assert Rj != wit["w1"][j], "mismatch (properness) failed"
    print("    fresh-point identity + properness mismatch: spot checks PASS")


def part2():
    print("== part 2: exact mod-P certificates at the s = 64 optimum ==")
    m = 2 ** 24
    wit1 = certify_multicore(P1, G1, 64, m, 32, 42, 3, "first field (c=3,a=42)")
    assert wit1 is not None, "first-field certificate not realizable"
    assert wit1["count"] == 66 * m == 1107296256 > N
    print(f"    budget: count - n = {wit1['count'] - N} (need >= 1): PASS")
    spot_check_fresh_identity(P1, G1, 64, m, 32, wit1)
    e1 = 22 * m - 1
    print(f"    NEW first-field bad radius: e = {e1}, delta = {e1}/2^30 "
          f"= {e1 / N:.10f}  (vs old 31/64 - 1/2^30 = {(31 * 2**24 - 1) / N:.10f})")
    print()
    wit2 = certify_multicore(P2, G2, 64, m, 32, 38, 5, "second field (c=5,a=38)")
    assert wit2 is not None, "second-field certificate not realizable"
    assert wit2["count"] == 130 * m == 2181038080 > 2 * N
    print(f"    budget: count - 2n = {wit2['count'] - 2 * N} (need >= 1): PASS")
    spot_check_fresh_identity(P2, G2, 64, m, 32, wit2)
    e2 = 26 * m - 1
    print(f"    NEW second-field bad radius: e = {e2}, delta = {e2}/2^30 "
          f"= {e2 / N:.10f}")
    print()
    return wit1, wit2


# ---------------------------------------------------------------- part 3: toy end-to-end
def toy():
    print("== part 3: toy end-to-end (RS[16,8] over mu_16 in F_4001, c=2, a=5) ==")
    p = 4001
    # element of order 16
    om = None
    for z in range(2, p):
        cand = pow(z, (p - 1) // 16, p)
        if pow(cand, 8, p) == p - 1:
            om = cand
            break
    s, m, kq, a, c = 8, 2, 4, 5, 2
    n, k = 16, 8
    zeta = pow(om, 2, p)
    dom8 = [pow(zeta, j, p) for j in range(s)]
    dom16 = [pow(om, i, p) for i in range(n)]
    rng = random.Random(7)
    wit = None
    for attempt in range(500):
        cores = [sorted(rng.sample(range(s), a)) for _ in range(c)]
        rows = []
        for core in cores:
            rows.extend(parity_rows_for_core(core, dom8, kq, p))
        red, pivots = rref(rows, p, s)
        if len(red) != c * (a - kq):
            continue
        dirs = [(ci, j, defect_functional(core, j, dom8, kq, p))
                for ci, core in enumerate(cores) for j in range(s) if j not in core]
        reduced = [reduce_vector(d[2], red, pivots, p) for d in dirs]
        if any(not any(v) for v in reduced):
            continue
        norm = set()
        for v in reduced:
            lead = next(x for x in v if x)
            inv = inverse(lead, p)
            norm.add(tuple(x * inv % p for x in v))
        if len(norm) != len(dirs):
            continue
        wbasis = kernel_basis(rows, p, s)
        for _ in range(200):
            c0 = [rng.randrange(p) for _ in wbasis]
            c1 = [rng.randrange(p) for _ in wbasis]
            w0 = [sum(cc * b[i] for cc, b in zip(c0, wbasis)) % p for i in range(s)]
            w1 = [sum(cc * b[i] for cc, b in zip(c1, wbasis)) % p for i in range(s)]
            d0 = [dot(d[2], w0, p) for d in dirs]
            d1 = [dot(d[2], w1, p) for d in dirs]
            if any(x == 0 for x in d0) or any(x == 0 for x in d1):
                continue
            rho = [x * inverse((-y) % p, p) % p for x, y in zip(d0, d1)]
            labels = [pow(r * pow(om, d[1], p) % p, m, p) for r, d in zip(rho, dirs)]
            if len(set(labels)) != len(dirs):
                continue
            wit = dict(cores=cores, dirs=dirs, rho=rho, w0=w0, w1=w1)
            break
        if wit:
            break
    assert wit, "toy certificate not realizable"
    print(f"  cores = {wit['cores']}, base directions = {len(wit['dirs'])} "
          f"(predicted {c * (s - a)}), lifted predicted gammas = {c * (s - a) * m}")

    u0 = [dom16[i] * wit["w0"][i % 8] % p for i in range(n)]
    u1 = [wit["w1"][i % 8] % p for i in range(n)]
    predicted = set()
    for (ci, j, _), r in zip(wit["dirs"], wit["rho"]):
        for t in range(m):
            predicted.add(r * pow(om, j + 8 * t, p) % p)
    assert len(predicted) == c * (s - a) * m, "coset collision in toy"

    def interp_eval(vals_pts, x):
        """Lagrange interpolation of (point, value) pairs, evaluated at x."""
        total = 0
        for xi, yi in vals_pts:
            num, den = 1, 1
            for xj, _ in vals_pts:
                if xj != xi:
                    num = num * (x - xj) % p
                    den = den * (xi - xj) % p
            total = (total + yi * num * inverse(den, p)) % p
        return total

    # exact bad-gamma enumeration at threshold agreement >= 11 (e <= 5, delta = 5/16)
    def bad_set(threshold):
        bad = set()
        universal = 0
        for S in itertools.combinations(range(n), threshold):
            base, rest = S[:k], S[k:]
            p0 = [(dom16[i], u0[i]) for i in base]
            p1 = [(dom16[i], u1[i]) for i in base]
            joint0 = all(interp_eval(p0, dom16[i]) == u0[i] for i in rest)
            joint1 = all(interp_eval(p1, dom16[i]) == u1[i] for i in rest)
            if joint0 and joint1:
                continue  # pairJointAgreesOn S -> never an mcaEvent witness on S
            # gamma solutions: for each extra point, a*gamma = b
            sols, allf = None, True
            for i in rest:
                aa = (interp_eval(p1, dom16[i]) - u1[i]) % p
                bb = (u0[i] - interp_eval(p0, dom16[i])) % p
                if aa == 0:
                    if bb != 0:
                        sols, allf = set(), False
                        break
                    continue  # this point is gamma-free
                gcur = bb * inverse(aa, p) % p
                if sols is None:
                    sols = {gcur}
                elif gcur not in sols:
                    sols, allf = set(), False
                    break
                allf = False
            if sols is None and allf:
                universal += 1  # entire line agrees on S: impossible when not joint
                continue
            bad |= sols or set()
        return bad, universal

    bad11, uni11 = bad_set(11)
    assert uni11 == 0
    missing = predicted - bad11
    print(f"  threshold 11 (e=5): predicted {len(predicted)} gammas, "
          f"brute-force mcaEvent gammas = {len(bad11)}, "
          f"predicted subset of actual: {not missing}")
    assert not missing, f"predicted gammas not bad: {sorted(missing)[:4]}"
    bad12, _ = bad_set(12)
    print(f"  threshold 12 (e=4): bad gammas for this stack = {len(bad12)} "
          f"(toy budget n = 16; construction stops, as arithmetic predicts "
          f"{'PASS' if len(bad12) <= 16 else 'FAIL'})")
    # toy arithmetic: no feasible (c,g) at s=8 for budget 1
    assert not any(feasible(8, cc, gg, 1) for cc in range(2, 8) for gg in range(1, 4))
    print("  toy arithmetic: no (c,g) beats budget at s=8 -> matches bracket-note toy")
    print()


# ---------------------------------------------------------------- part 4: stop point
def part4():
    print("== part 4: stop point and the family floor ==")
    # g = 11 infeasible at s = 64 for every c (first field)
    assert not any(feasible(64, c, 11, 1) for c in range(1, 64))
    print("  s=64, g=11: infeasible for every c (11c+2<=32 forces c<=2; "
          "65<=21c forces c>=4): PASS")
    assert not any(feasible(64, c, 7, 2) for c in range(1, 64))
    print("  s=64, g=7, second field: infeasible for every c: PASS")
    # dyadic ladder: best e per quotient size s = 2^t (c = 3 optimal)
    print("  dyadic ladder (first field budget), best achievable bad error e(s):")
    best_e = None
    for t in range(3, 30):
        s = 2 ** t
        m = N // s
        best = None
        for g in range(s // 2 - 2, 0, -1):
            if feasible(s, 3, g, 1):
                best = g
                break
        if best is None:
            continue
        e = (s // 2 - best) * m - 1
        h = s // 2 - best
        assert 3 * h >= s + 2, (s, h)  # the c=3 floor inequality
        if best_e is None or e < best_e[0]:
            best_e = (e, s)
        base_cert = 3 * h
        print(f"    s=2^{t:2d}: g={best:9d} h={h:9d} e={e:9d} "
              f"delta={e / N:.9f} base-cert size={base_cert}")
    print(f"  family floor over dyadic quotients (m>=2): e_min = {best_e[0]} at s={best_e[1]}")
    # m = 1 endpoint (no quotient): 3h >= n+2, e = h - 1 >= (n-1)/3
    h1 = (N + 2) // 3
    assert 3 * h1 == N + 2
    e_m1 = h1 - 1
    assert 3 * (e_m1 + 1) == N + 2 and e_m1 == (N - 1) // 3 == 357913941
    print(f"  m=1 endpoint: e = {e_m1} = (n-1)/3 exactly, delta = {e_m1 / N:.9f}")
    # general floor: any feasible (s even, c, g): 3*(e+1) = 3*h*m >= (s+2)*m = n + 2m
    for s in (8, 16, 32, 64, 128, 256, 512, 1024):
        for c in range(2, 40):
            for g in range(1, s // 2):
                if feasible(s, c, g, 1):
                    h = s // 2 - g
                    assert 3 * h >= s + 2, (s, c, g)
    print("  general floor 3h >= s+2 verified for all feasible (s<=1024, c<40): PASS")
    print("  => the c-core mechanism cannot certify any bad radius below "
          f"{357913941}/2^30 ~ 0.33333333240; candidate interior pin ~ 1/3.")
    print()


if __name__ == "__main__":
    part1()
    part2()
    toy()
    part4()
    print("ALL CHECKS PASS")

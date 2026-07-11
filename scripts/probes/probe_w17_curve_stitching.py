#!/usr/bin/env python3
"""Probe (W17, B2 curve-decodability stitching brick, 2026-07-10).

Fabricate-then-refute for the planned Lean lane `_W17CurveDecodStitching.lean`:

  Setting: F = GF(p), code C = RS[F, domain, k] (deg < k), stack u : Fin (l+1) -> F^n,
  f : F -> C, close set A = {alpha : dist(comb u alpha, f alpha) <= D} with D = floor(delta*n).

  Claim 1 (stitching spread, unconditional): for ANY (l+1)-subset B of the close set, the
  Lagrange-interpolated codeword stack cs (curve through the graph points (alpha, f alpha),
  alpha in B) satisfies    forall gamma in F:  dist(comb u gamma, comb cs gamma) <= (l+1)*D.

  Claim 2 (triangle): forall close beta: dist(f beta, comb cs beta) <= (l+2)*D.

  Claim 3 (ball fiber count): #distinct {f beta - comb cs beta : beta close}
           <= #{c in C : wt(c) <= (l+2)*D}   (trivially, since each difference IS such a cw).

  Claim 4 (UDR full explanation): if (l+2)*D < n-k+1 then f beta = comb cs beta for ALL
           close beta (single curve explains the WHOLE close set, b = a regime).

Adversarial search: random + planted-error instances, trying to refute the constants
(l+1), (l+2) and the UDR conclusion.  Any violation is printed loudly.
"""
import itertools
import random

random.seed(20260710)


def make_field(p):
    return p


def poly_eval(coeffs, x, p):
    acc = 0
    for c in reversed(coeffs):
        acc = (acc * x + c) % p
    return acc


def rs_codeword(coeffs, domain, p):
    return tuple(poly_eval(coeffs, d, p) for d in domain)


def dist(a, b):
    return sum(1 for x, y in zip(a, b) if x != y)


def comb(stack, alpha, p):
    # stack: list of l+1 rows, each a tuple of n values; returns sum_j alpha^j * row_j
    n = len(stack[0])
    out = []
    for i in range(n):
        acc, apow = 0, 1
        for row in stack:
            acc = (acc + apow * row[i]) % p
            apow = (apow * alpha) % p
        out.append(acc)
    return tuple(out)


def lagrange_stack(B, fvals, p, l):
    """Interpolate the codeword-curve through (alpha, fvals[alpha]) for alpha in B.
    Returns stack of l+1 rows (rows beyond |B|-1 are zero-padded via the polynomial
    coefficients of the Lagrange interpolation, degree <= |B|-1 <= l)."""
    n = len(next(iter(fvals.values())))
    # per coordinate i, interpolate the scalar polynomial through (alpha, f alpha i)
    rows = [[0] * n for _ in range(l + 1)]
    for i in range(n):
        # Lagrange: P(X) = sum_a f_a * prod_{b != a} (X - b)/(a - b)
        coeffs = [0] * (l + 1)
        for a in B:
            # numerator polynomial prod_{b != a} (X - b)
            num = [1]
            for b in B:
                if b == a:
                    continue
                # multiply num by (X - b)
                new = [0] * (len(num) + 1)
                for j, c in enumerate(num):
                    new[j + 1] = (new[j + 1] + c) % p
                    new[j] = (new[j] - b * c) % p
                num = new
            den = 1
            for b in B:
                if b != a:
                    den = (den * (a - b)) % p
            deninv = pow(den, p - 2, p)
            scale = (fvals[a][i] * deninv) % p
            for j, c in enumerate(num):
                coeffs[j] = (coeffs[j] + scale * c) % p
        for j in range(l + 1):
            rows[j][i] = coeffs[j]
    return [tuple(r) for r in rows]


def all_codewords(domain, k, p):
    cws = []
    for coeffs in itertools.product(range(p), repeat=k):
        cws.append(rs_codeword(coeffs, domain, p))
    return cws


def run_trial(p, n, k, l, D, trial, mode):
    domain = list(range(n))  # first n elements of GF(p), distinct since n <= p
    # build f : F -> C, u stack, with planted close seeds
    fvals = {}
    # random codeword-valued f
    for alpha in range(p):
        coeffs = [random.randrange(p) for _ in range(k)]
        fvals[alpha] = rs_codeword(coeffs, domain, p)
    # u stack: start from a codeword stack, then corrupt
    base = [rs_codeword([random.randrange(p) for _ in range(k)], domain, p)
            for _ in range(l + 1)]
    u = [list(r) for r in base]
    if mode == "corrupt_u":
        for _ in range(random.randrange(2 * D + 1)):
            u[random.randrange(l + 1)][random.randrange(n)] = random.randrange(p)
    u = [tuple(r) for r in u]
    # plant close seeds: for a random subset of seeds, set f alpha := decodable codeword
    planted = random.sample(range(p), min(p, l + 1 + random.randrange(4)))
    for alpha in planted:
        cu = comb(u, alpha, p)
        # find a codeword within D of comb u alpha by planting: take the curve value of the
        # base stack (a codeword) and hope; else plant f alpha = base-curve value
        cw = comb(base, alpha, p)
        if dist(cu, cw) <= D:
            fvals[alpha] = cw
        else:
            # corrupt cu at <= D coords back onto a codeword? just use cw anyway (may be far)
            fvals[alpha] = cw
    close = [alpha for alpha in range(p)
             if dist(comb(u, alpha, p), fvals[alpha]) <= D]
    if len(close) < l + 1:
        return None  # not enough close seeds; skip
    violations = []
    # test over several (l+1)-subsets B of close
    subsets = list(itertools.combinations(close, l + 1))
    random.shuffle(subsets)
    for B in subsets[:6]:
        cs = lagrange_stack(list(B), fvals, p, l)
        # sanity: rows of cs must be codewords (degree < k requires l+1 <= k? NO:
        # rows are coefficient-stacks of the curve in the SEED variable; each row is an
        # F-linear combination of the codewords f(alpha), alpha in B -> a codeword.)
        # Claim 1
        for gamma in range(p):
            d1 = dist(comb(u, gamma, p), comb(cs, gamma, p))
            if d1 > (l + 1) * D:
                violations.append(("CLAIM1", B, gamma, d1, (l + 1) * D))
        # Claim 2 + 4
        for beta in close:
            d2 = dist(fvals[beta], comb(cs, beta, p))
            if d2 > (l + 2) * D:
                violations.append(("CLAIM2", B, beta, d2, (l + 2) * D))
            if (l + 2) * D < n - k + 1 and d2 != 0:
                violations.append(("CLAIM4-UDR", B, beta, d2, "expected 0"))
        # interpolation sanity: cs passes through f alpha at alpha in B
        for alpha in B:
            if comb(cs, alpha, p) != fvals[alpha]:
                violations.append(("INTERP-SANITY", B, alpha))
    return violations


def main():
    total, skipped, bad = 0, 0, 0
    configs = [
        # (p, n, k, l, D)
        (13, 10, 2, 1, 1),   # (l+2)*D = 3 < n-k+1 = 9 : UDR regime
        (13, 10, 2, 1, 2),   # (l+2)*D = 6 < 9 : UDR regime
        (13, 10, 2, 1, 3),   # (l+2)*D = 9 = 9 : NOT UDR (boundary) - claims 1-3 only
        (13, 10, 3, 2, 1),   # l=2, (l+2)*D = 4 < 8 : UDR
        (13, 10, 4, 2, 2),   # l=2, (l+2)*D = 8 > 7 : NOT UDR
        (11, 8, 2, 1, 1),    # small
        (17, 12, 3, 1, 2),   # (l+2)*D = 6 < 10 : UDR
    ]
    for (p, n, k, l, D) in configs:
        for mode in ("clean", "corrupt_u"):
            for trial in range(40):
                res = run_trial(p, n, k, l, D, trial, mode)
                if res is None:
                    skipped += 1
                    continue
                total += 1
                udr = (l + 2) * D < n - k + 1
                for v in res:
                    if v[0] == "CLAIM4-UDR" and not udr:
                        continue
                    bad += 1
                    print("VIOLATION", (p, n, k, l, D, mode, trial), v)
    print(f"trials run={total} skipped={skipped} violations={bad}")
    if bad == 0:
        print("ALL CLAIMS SURVIVE (stitching spread (l+1)D, triangle (l+2)D, UDR full explanation)")


if __name__ == "__main__":
    main()

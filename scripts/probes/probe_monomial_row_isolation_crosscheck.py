#!/usr/bin/env python3
"""Independent crosscheck of the row-isolation classification: field arithmetic only.

The main probe classifies the rows ``N_e = (y-z) + y^e (z-1) + z^e (1-y)`` in the group
ring ``A_n = Z[y,z]/<y^n-1, z^n-1>`` by signed term algebra and shows that the ONLY pair
of distinct nonzero rows related by a monomial is ``{2, n-1}`` (certificate
``y z * N_(n-1) = N_2``).  This script re-derives the same integers with algorithms that
share no code with that route.

* ROUTE A (complete grid classification over F_p).  Rows are evaluated at every one of the
  ``n^2`` points of ``mu_n x mu_n`` with modular arithmetic -- no group ring, no term
  algebra, no fingerprint.  For an unordered pair ``{a,b}`` the identity
  ``N_a = c * y^i z^j * N_b`` on the grid forces ZERO SETS to be equal (a monomial never
  vanishes), which is tested first as an exact bitmask; when the zero sets agree, ``(i,j)``
  is pinned from two points where ``N_b != 0`` by solving a 2x2 system modulo ``n`` whose
  determinant is coprime to ``n``, and the candidate is then verified at EVERY grid point.
  Completeness: if an identity exists, every admissible pinning pair yields it, so a
  failure to verify is a proof of non-existence AT THE FUNCTION LEVEL; and because the
  ``n^2`` grid points against the ``n^2`` monomials form a Kronecker Vandermonde matrix
  with nonzero determinant when ``n | p - 1``, the function level and the group-ring level
  agree here.  The count of related pairs must be exactly one, ``{2, n-1}``, at every cell.
* ROUTE B (literal triples).  For every triple of distinct points of ``mu_n`` the raw
  collinearity determinants ``D_e(T)`` are computed by 2x2 elimination on the actual field
  values, and the bad-scalar set ``{-D_a(T)/D_b(T) : D_b(T) != 0}`` is collected literally
  over all triples.  This is the census object itself: it proves the SET equality with
  ``mu_n`` for the isolated pair and reproduces the neighbour-pencil counts that the main
  probe prints, without any shape normalisation or ``h`` closed form.
* ROUTE C (unfolded certificates in Z[y,z]).  ``y z N_(n-1) - N_2``, ``N_0`` and ``N_1``
  are divided by ``y^n - 1`` in (Z[z])[y] and then by ``z^n - 1`` in (Z[y])[z]; the
  ideal-membership certificate ``Q1*(y^n-1) + Q2*(z^n-1)`` is re-expanded by plain integer
  polynomial multiplication and compared term by term, with zero remainder.  A different
  algorithm from exponent folding, and it shows the identities need no root-of-unity
  hypothesis.
* ROUTE D (merged anchors, triple-sum route).  The merged ``(x^3, x^2)`` ceiling integers
  are recomputed as literal negated triple sums over ``mu_8`` and ``mu_16`` (the semantics
  of the merged PR #267 probe), with no determinant and no ``h`` row anywhere.

Stdlib only, deterministic, integer arithmetic only.  It checks the same objects as the
main probe at the same parameters and agrees on every integer printed there; it adds no
claim of its own.  Same scope limits: the ``t = 3`` ceiling monomial-pencil census on
smooth domains ``mu_n`` in prime fields -- no ``t >= 4``, no global maximum, no production
regime, no ``delta*``, no prize statement.
"""

import hashlib
import time
from itertools import combinations
from math import gcd, isqrt

GRID_RUNGS = (4, 8, 16, 32, 64)
LITERAL_RUNGS = (8, 16, 32)
CERT_RUNGS = tuple(2 ** k for k in range(2, 11))
LIMIT = 20_000
FERMAT = 65537

# Merged PR #267 anchors used by ROUTE D.  This is the complete published
# 34-prime ceiling-exception table of scripts/probes/probe_n16_below_ceiling_max.py
# (CEILING_EXCEPTIONS), transcribed unchanged.
MERGED_N16 = {17: 17, 97: 96, 113: 112, 193: 192, 241: 240, 257: 224, 337: 272,
              353: 272, 401: 320, 433: 352, 449: 336, 577: 304, 593: 416, 641: 368,
              673: 416, 769: 416, 881: 416, 929: 416, 977: 416, 1153: 448,
              1217: 448, 1249: 448, 1297: 416, 1361: 416, 1409: 416, 1489: 416,
              1777: 448, 2129: 448, 2273: 448, 2689: 448, 2833: 448, 3089: 448,
              4001: 448, 4049: 448}
N8_CEILING = {17: 16, 41: 40, 257: 40}


def is_prime(value):
    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    divisor = 3
    while divisor * divisor <= value:
        if value % divisor == 0:
            return False
        divisor += 2
    return True


def primes_one_mod(p_mod, limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for divisor in range(2, isqrt(limit) + 1):
        if sieve[divisor]:
            start = divisor * divisor
            sieve[start:limit + 1:divisor] = b"\x00" * len(sieve[start:limit + 1:divisor])
    return [p for p in range(p_mod, limit + 1) if sieve[p] and p % p_mod == 1]


def order_element(p, n):
    assert (p - 1) % n == 0, (n, p)
    for candidate in range(2, p):
        generator = pow(candidate, (p - 1) // n, p)
        if pow(generator, n // 2, p) == p - 1:
            assert pow(generator, n, p) == 1
            return generator
    raise AssertionError(f"no element of order {n} modulo {p}")


def three_smallest(n):
    found = []
    candidate = n + 1
    while len(found) < 3 and candidate < 4_000_000:
        if is_prime(candidate) and candidate % n == 1:
            found.append(candidate)
        candidate += n
    assert len(found) == 3, n
    return found


def batch_inverse(values, p):
    prefix = [1] * (len(values) + 1)
    for index, value in enumerate(values):
        prefix[index + 1] = prefix[index] * (value if value else 1) % p
    inverse = pow(prefix[-1], -1, p)
    out = [0] * len(values)
    for index in range(len(values) - 1, -1, -1):
        value = values[index]
        if value:
            out[index] = inverse * prefix[index] % p
            inverse = inverse * value % p
    return out


# ---------------------------------------------------------------------------
# ROUTE A: field evaluation on the full grid mu_n x mu_n.
# ---------------------------------------------------------------------------

def grid_rows(n, p):
    """V[e][u][v] = N_e(g^u, g^v), evaluated directly from the definition."""
    generator = order_element(p, n)
    xs = [pow(generator, u, p) for u in range(n)]
    assert len(set(xs)) == n == len(xs)
    powers = [[pow(x, e, p) for x in xs] for e in range(n)]
    rows = []
    for e in range(n):
        pe = powers[e]
        table = []
        for u in range(n):
            y = xs[u]
            one_minus_y = (1 - y) % p
            row_u = []
            for v in range(n):
                z = xs[v]
                row_u.append((y - z + pe[u] * (z - 1) + pe[v] * one_minus_y) % p)
            table.append(row_u)
        rows.append(table)
    return xs, powers, rows


def grid_classify(n, p):
    """Complete signed-monomial classification of the rows, by grid arithmetic only.

    For even n the sign is absorbed (``-1 = g^(n/2)`` is a monomial value), so searching
    monomials ``y^i z^j`` covers ``c = +-1``.  Every pair of rows gets a conclusive answer:

    * different zero sets -- no identity (a monomial never vanishes);
    * equal zero sets and ``N_a/N_b`` outside ``mu_n`` at the anchor point -- no identity;
    * equal zero sets and a pinned ``(i, j)`` -- verify at every grid point; because the
      pin's exponent determinant is coprime to ``n`` the pin is unique, so a failed
      verification is conclusive (a true identity would have been pinned correctly);
    * equal zero sets with every admissible second point giving a ratio outside ``mu_n``
      -- no identity.
    """
    xs, powers, rows = grid_rows(n, p)
    masks = []
    for e in range(n):
        mask = 0
        table = rows[e]
        for u in range(n):
            for v in range(n):
                if table[u][v] == 0:
                    mask |= 1 << (u * n + v)
        masks.append(mask)
    log_of = {value: u for u, value in enumerate(xs)}
    related = []
    certificates = {}
    outcomes = {"zero_sets_differ": 0, "ratio_outside_mu_n": 0,
                "pinned_and_rejected": 0, "pinned_and_verified": 0}
    total_pairs = 0
    for a in range(2, n):
        for b in range(a + 1, n):
            total_pairs += 1
            if masks[a] != masks[b]:
                outcomes["zero_sets_differ"] += 1
                continue
            anchor = None
            for u in range(n):
                for v in range(n):
                    if rows[b][u][v]:
                        anchor = (u, v)
                        break
                if anchor:
                    break
            assert anchor, (n, p, a, b)
            u1, v1 = anchor
            ratio1 = rows[a][u1][v1] * pow(rows[b][u1][v1], -1, p) % p
            if ratio1 not in log_of:
                outcomes["ratio_outside_mu_n"] += 1
                continue
            settled = False
            admissible = 0
            for u2 in range(n):
                if settled:
                    break
                for v2 in range(n):
                    if (u2, v2) == anchor or not rows[b][u2][v2]:
                        continue
                    det = (u1 * v2 - u2 * v1) % n
                    if det == 0 or gcd(det, n) != 1:
                        continue
                    admissible += 1
                    ratio2 = rows[a][u2][v2] * pow(rows[b][u2][v2], -1, p) % p
                    if ratio2 not in log_of:
                        continue
                    l1, l2 = log_of[ratio1], log_of[ratio2]
                    inv_det = pow(det, -1, n)
                    i = (v2 * l1 - v1 * l2) % n * inv_det % n
                    j = (u1 * l2 - u2 * l1) % n * inv_det % n
                    verified = True
                    for u in range(n):
                        yi = powers[i][u]
                        for v in range(n):
                            if rows[a][u][v] != yi * powers[j][v] % p * rows[b][u][v] % p:
                                verified = False
                                break
                        if not verified:
                            break
                    settled = True
                    if verified:
                        related.append((a, b))
                        certificates[(a, b)] = (i, j)
                        outcomes["pinned_and_verified"] += 1
                    else:
                        # Conclusive: a true identity is pinned correctly by THIS pair,
                        # because the pin determinant is invertible modulo n.
                        outcomes["pinned_and_rejected"] += 1
                    break
            if not settled:
                assert admissible, (n, p, a, b, "no admissible second grid point")
                outcomes["ratio_outside_mu_n"] += 1
    return related, certificates, total_pairs, outcomes


def run_grid_route():
    cells = []
    for n in GRID_RUNGS:
        primes = three_smallest(n)
        if (FERMAT - 1) % n == 0:
            primes = primes + [FERMAT]
        for p in primes:
            related, certificates, total_pairs, outcomes = grid_classify(n, p)
            assert related == [(2, n - 1)], (n, p, related)
            assert certificates[(2, n - 1)] == (1, 1), (n, p, certificates)
            assert sum(outcomes.values()) == total_pairs, (n, p, outcomes, total_pairs)
            cells.append((n, p, len(related), total_pairs, 1, 1, outcomes))
            print(f"  route A n={n} p={p}: {total_pairs} unordered pairs of nonzero rows "
                  f"settled on the {n}x{n} grid -- "
                  + ", ".join(f"{key}={value}" for key, value in sorted(outcomes.items()))
                  + f"; the ONLY related pair is {related[0]} with monomial y^1 z^1",
                  flush=True)
    sha = hashlib.sha256(";".join(f"{n},{p},{r},{t}"
                                  for n, p, r, t, _, _, _ in cells).encode()).hexdigest()
    print(f"route A: complete grid classification at {len(cells)} (n, p) cells, "
          f"{sum(c[3] for c in cells)} pairs settled with field arithmetic alone -- in "
          f"every cell exactly one related pair, always {{2, n-1}}, always with monomial "
          f"y z, vector sha256 {sha}", flush=True)
    return cells


# ---------------------------------------------------------------------------
# ROUTE B: literal triples, raw determinants.
# ---------------------------------------------------------------------------

def det3(x, y, z, exponent, p):
    """Collinearity determinant of (1, t, t^exponent) on the triple, by elimination."""
    a = pow(x, exponent, p)
    b = pow(y, exponent, p)
    c = pow(z, exponent, p)
    # det [[1,x,a],[1,y,b],[1,z,c]]
    return ((y - x) * (c - a) - (z - x) * (b - a)) % p


def literal_bad_sets(n, p, exponents):
    """{exponent: value table} then the literal bad set for every pair among exponents."""
    generator = order_element(p, n)
    domain = [pow(generator, u, p) for u in range(n)]
    assert len(set(domain)) == n
    powers = {e: [pow(x, e, p) for x in domain] for e in exponents}
    bad = {(a, b): set() for a in exponents for b in exponents if a != b}
    triples = 0
    singular = 0
    for (i, j, k) in combinations(range(n), 3):
        triples += 1
        x, y, z = domain[i], domain[j], domain[k]
        row = {}
        for e in exponents:
            pe = powers[e]
            a, b, c = pe[i], pe[j], pe[k]
            row[e] = ((y - x) * (c - a) - (z - x) * (b - a)) % p
        nonzero = [e for e in exponents if row[e]]
        if not nonzero:
            singular += 1
            continue
        inv = {e: pow(row[e], -1, p) for e in nonzero}
        for a in exponents:
            for b in nonzero:
                if a == b:
                    continue
                bad[(a, b)].add((-row[a] * inv[b]) % p)
    return domain, bad, triples, singular


def run_literal_route():
    cells = []
    for n in LITERAL_RUNGS:
        primes = three_smallest(n)
        if (FERMAT - 1) % n == 0:
            primes = primes + [FERMAT]
        for p in primes:
            exponents = [2, n - 1, n - 2, n - 3, 4]
            exponents = sorted({e for e in exponents if 0 <= e < n})
            domain, bad, triples, singular = literal_bad_sets(n, p, exponents)
            domain_set = set(domain)
            closed = bad[(2, n - 1)]
            assert closed == domain_set, (n, p, len(closed))
            counts = {(a, b): len(bad[(a, b)]) for a in exponents
                          for b in exponents if a != b}
            cells.append((n, p, triples, singular, counts))
            assert 0 not in closed, (n, p)
            print(f"  route B n={n} p={p}: {triples} literal triples of distinct domain "
                  f"points, bad set of (x^2, x^{n-1}) SET-equal to mu_{n} (count "
                  f"{len(closed)}) and 0 is not bad; the pencils the classification "
                  f"separates count "
                  + ", ".join(f"|bad(x^2, x^{key[1]})| = {counts[key]}"
                              for key in sorted(counts)
                              if key[0] == 2 and key[1] != n - 1),
                  flush=True)
    return cells


# ---------------------------------------------------------------------------
# ROUTE C: unfolded ideal-membership certificates in Z[y, z].
# ---------------------------------------------------------------------------

def poly_mul(a, b):
    out = {}
    for ka, ca in a.items():
        for kb, cb in b.items():
            key = (ka[0] + kb[0], ka[1] + kb[1])
            out[key] = out.get(key, 0) + ca * cb
    return {k: v for k, v in out.items() if v}


def poly_add(*terms):
    out = {}
    for term in terms:
        for key, coeff in term.items():
            out[key] = out.get(key, 0) + coeff
    return {k: v for k, v in out.items() if v}


def poly_neg(term):
    return {k: -v for k, v in term.items()}


def poly_sub(a, b):
    return poly_add(a, poly_neg(b))


def divide_by_monomial_minus_one(poly, variable, power):
    """Exact division by (y^power - 1) or (z^power - 1) in (Z[other])[variable].

    Returns (quotient, remainder) with remainder of degree < power in `variable`, so that
    poly == quotient * (variable^power - 1) + remainder as ordinary polynomials.  The
    fold x^d = x^(d-power) * (x^power - 1) + x^(d-power) is applied from the top degree
    down, which is a different algorithm from reducing exponents modulo n.
    """
    index = 0 if variable == "y" else 1
    groups = {}
    for key, coeff in poly.items():
        fixed = key[1 - index]
        degree = key[index]
        groups.setdefault(fixed, {})
        groups[fixed][degree] = groups[fixed].get(degree, 0) + coeff
    quotient = {}
    remainder = {}
    for fixed, degrees in groups.items():
        carry = {d: c for d, c in degrees.items() if c}
        for d in range(max(carry), power - 1, -1):
            coeff = carry.get(d, 0)
            if not coeff:
                continue
            del carry[d]
            target = d - power
            carry[target] = carry.get(target, 0) + coeff
            qkey = (target, fixed) if variable == "y" else (fixed, target)
            quotient[qkey] = quotient.get(qkey, 0) + coeff
        for d, coeff in carry.items():
            if coeff:
                rkey = (d, fixed) if variable == "y" else (fixed, d)
                remainder[rkey] = remainder.get(rkey, 0) + coeff
    return ({k: v for k, v in quotient.items() if v},
            {k: v for k, v in remainder.items() if v})


def n_e_unfolded(exponent):
    return poly_add({(1, 0): 1, (0, 1): -1},
                    poly_mul({(exponent, 0): 1}, {(0, 1): 1, (0, 0): -1}),
                    poly_mul({(0, exponent): 1}, {(0, 0): 1, (1, 0): -1}))


def denominator_unfolded():
    return poly_mul(poly_mul({(0, 0): 1, (1, 0): -1}, {(0, 0): 1, (0, 1): -1}),
                   {(1, 0): 1, (0, 1): -1})


def normal_form(poly, n):
    """Remainder of poly modulo <y^n - 1, z^n - 1>, by two unfoldings (no folding)."""
    _, rest_y = divide_by_monomial_minus_one(poly, "y", n)
    _, rest_z = divide_by_monomial_minus_one(rest_y, "z", n)
    return rest_z


def run_certificate_route():
    report = []
    exhaustive = []
    for n in CERT_RUNGS:
        den = denominator_unfolded()
        for e in (0, 1):
            assert n_e_unfolded(e) == {}, (n, e)
        assert n_e_unfolded(2) == den, n
        difference = poly_sub(poly_mul({(1, 1): 1}, n_e_unfolded(n - 1)), den)
        q1, rest = divide_by_monomial_minus_one(difference, "y", n)
        q2, rest2 = divide_by_monomial_minus_one(rest, "z", n)
        assert rest2 == {}, (n, sorted(rest2.items())[:4])
        rebuilt = poly_add(poly_mul(q1, {(n, 0): 1, (0, 0): -1}),
                           poly_mul(q2, {(0, n): 1, (0, 0): -1}))
        assert rebuilt == difference, (n, sorted(rebuilt.items())[:4],
                                       sorted(difference.items())[:4])
        assert normal_form(difference, n) == {}, n
        report.append((n, len(q1), len(q2), len(difference)))
        # Negative side, unfolded: at the rungs where it is affordable, EVERY multiplier
        # y^i z^j and sign must leave a NONZERO normal form against the neighbouring
        # pencil (x^2, x^(n-2)) -- the certificate really is available for one pair only.
        if 4 < n <= 16:  # at n = 4 the neighbour exponent n-2 IS 2: no pair to separate
            failures = 0
            for i in range(n):
                for j in range(n):
                    for c in (1, -1):
                        candidate = poly_sub(poly_mul({(i, j): c}, n_e_unfolded(n - 2)),
                                             den)
                        if normal_form(candidate, n) == {}:
                            failures += 1
            assert failures == 0, (n, failures)
            exhaustive.append((n, 2 * n * n, failures))
    print(f"route C: at every rung n in {CERT_RUNGS}: N_0 = N_1 = 0 and N_2 = den as "
          f"exact polynomials in Z[y, z]; y z N_(n-1) - den = Q1*(y^n-1) + Q2*(z^n-1) "
          f"with the certificate re-expanded term by term and zero remainder "
          f"(per-rung (n, #Q1 terms, #Q2 terms, #difference terms) = {report}); and for "
          f"the neighbouring pencil (x^2, x^(n-2)) the unfolded normal form of "
          f"c*y^i z^j*N_(n-2) - N_2 is NONZERO for every (i, j, c): "
          f"{exhaustive} as (n, multipliers tested, identities found)", flush=True)


# ---------------------------------------------------------------------------
# ROUTE D: merged anchors by negated triple sums.
# ---------------------------------------------------------------------------

def merged_anchor_route():
    eight = primes_one_mod(8, LIMIT)
    profile8 = {}
    for p in eight:
        generator = order_element(p, 8)
        domain = {pow(generator, u, p) for u in range(8)}
        sums = {(-(x + y + z)) % p for x, y, z in combinations(sorted(domain), 3)}
        profile8[p] = len(sums)
    assert profile8[17] == 16
    assert all(profile8[p] == 40 for p in eight if p != 17)
    sixteen = primes_one_mod(16, LIMIT)
    profile16 = {}
    for p in sixteen:
        generator = order_element(p, 16)
        domain = {pow(generator, u, p) for u in range(16)}
        sums = {(-(x + y + z)) % p for x, y, z in combinations(sorted(domain), 3)}
        profile16[p] = len(sums)
    for p, expected in sorted(MERGED_N16.items()):
        assert p in profile16, ("published anchor prime outside the scan", p)
        assert profile16[p] == expected, (p, profile16[p], expected)
    exceptions = sorted(p for p, count in profile16.items() if count != 464)
    assert exceptions == sorted(MERGED_N16), (exceptions, sorted(MERGED_N16))
    fermat_generator = order_element(FERMAT, 16)
    fermat_domain = {pow(fermat_generator, u, FERMAT) for u in range(16)}
    above = len({(-(x + y + z)) % FERMAT
                 for x, y, z in combinations(sorted(fermat_domain), 3)})
    assert above == 464, above
    print(f"route D: merged anchors from literal negated triple sums -- n=8 gives 40 at "
          f"every one of the {len(eight)} primes p = 1 (mod 8) in [17, {LIMIT}] except "
          f"p=17 ({profile8[17]}); n=16 gives 464 at {len(sixteen) - len(exceptions)} of "
          f"the {len(sixteen)} primes p = 1 (mod 16) in [17, {LIMIT}], and the full "
          f"{len(exceptions)}-prime exception set EQUALS the published merged table as a "
          f"set, entry by entry: "
          f"{[(p, profile16[p]) for p in exceptions]}; at n=16, p={FERMAT} the same "
          f"literal route gives {above}", flush=True)
    return profile8, profile16


def main():
    start = time.time()
    assert FERMAT == 2 ** 16 + 1 and is_prime(FERMAT)
    cells = run_grid_route()
    literal = run_literal_route()
    run_certificate_route()
    merged_anchor_route()
    vector = ";".join(f"{n},{p},{r},{t},{i},{j}" for n, p, r, t, i, j, _ in cells)
    print(f"PASS: the grid route, the literal-triple route, the unfolded certificates and "
          f"the triple-sum anchors agree with the group-ring classification -- one related "
          f"pair {{2, n-1}} with monomial y z at all {len(cells)} grid cells; bad set of "
          f"(x^2, x^(n-1)) SET-equal to mu_n at all {len(literal)} literal cells; no "
          f"t>=4, global-maximum, production-regime, delta* or prize claim", flush=True)
    print(f"crosscheck vector sha256 "
          f"{hashlib.sha256(vector.encode()).hexdigest()} over {len(cells)} grid cells",
          flush=True)
    print(f"elapsed {time.time() - start:.1f}s", flush=True)


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without Python optimization to enable the certificate checks.")
    main()

#!/usr/bin/env python3
"""G330: exact-boundary certificate for the order-eight weight-{1,3} spectrum.

Executable cross-check of ``Frontier/_G330SpectrumExactBoundary.lean``:

1. rebuilds the 40 signed weight-{1,3} spectrum data on the half-window h = 4;
2. computes the quartic norm of all 780 pairwise differences by TWO independent
   methods — the Lean file's antipodal-squaring ladder and a 4x4 integer
   multiplication-matrix determinant in Z[zeta_8] — and asserts they agree;
3. asserts the norm value set is exactly the Lean ``normOkSet``
   {2, 4, 8, 16, 18, 32, 34, 36, 50, 64, 68, 98, 144}, that its only divisors
   congruent to 1 (mod 8) are {1, 9, 17, 25, 49}, and that 17 is the only prime
   among them — the finite certificate behind the boundary theorem;
4. consistency scan: for every prime p = 1 (mod 8) in [17, 20000], the spectrum
   image at an order-eight element has exactly 40 distinct values except the
   single collapse to 16 at p = 17.  (For p != 17 this is now a THEOREM —
   ``spectrum_card_eq_forty``; the scan is a redundant executable witness and
   deliberately extends past the G328 scan bound 10000.)

Stdlib only; exact integer arithmetic; every check is a hard assert.
"""

from itertools import combinations

OK_SET = {2, 4, 8, 16, 18, 32, 34, 36, 50, 64, 68, 98, 144}
MOD8_DIVISORS = {1, 9, 17, 25, 49}
LIMIT = 20_000


# ---------------------------------------------------------------- data

def spectrum_data():
    """The 40 signed data of weights {1, 3} on h = 4 as coefficient 4-tuples."""
    data = []
    for i in range(4):
        for sign in (1, -1):
            c = [0, 0, 0, 0]
            c[i] = sign
            data.append(tuple(c))
    for U in combinations(range(4), 3):
        for size in range(4):
            for T in combinations(U, size):
                c = [0, 0, 0, 0]
                for i in U:
                    c[i] = 1 if i in T else -1
                data.append(tuple(c))
    return data


# ------------------------------------------------- method 1: the Lean ladder

def quartic_norm_ladder(c0, c1, c2, c3):
    """Two antipodal-squaring steps evaluated at -1 (the Lean definition)."""
    a0, a1, a2, a3 = c0 * c0, 2 * c0 * c2 - c1 * c1, c2 * c2 - 2 * c1 * c3, -(c3 * c3)
    b0, b1, b2, b3 = a0 * a0, 2 * a0 * a2 - a1 * a1, a2 * a2 - 2 * a1 * a3, -(a3 * a3)
    return b0 - b1 + b2 - b3


# ---------------------------------- method 2: multiplication-matrix determinant

def zmul(a, b):
    out = [0, 0, 0, 0]
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                k, s = i + j, ai * bj
                if k >= 4:
                    out[k - 4] -= s
                else:
                    out[k] += s
    return tuple(out)


def quartic_norm_det(d):
    """Determinant of multiplication-by-d on the basis 1, z, z^2, z^3 (z^4 = -1)."""
    basis = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    cols = [zmul(d, e) for e in basis]
    m = [[cols[c][r] for c in range(4)] for r in range(4)]

    def det3(a):
        return (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
                - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
                + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0]))

    total = 0
    for col in range(4):
        minor = [[m[r][c] for c in range(4) if c != col] for r in range(1, 4)]
        total += (1 if col % 2 == 0 else -1) * m[0][col] * det3(minor)
    return total


# ---------------------------------------------------------------- checks

def main():
    data = spectrum_data()
    assert len(data) == 40 and len(set(data)) == 40

    norms = set()
    for a, b in combinations(data, 2):
        d = tuple(x - y for x, y in zip(a, b))
        n_ladder = quartic_norm_ladder(*d)
        n_det = quartic_norm_det(d)
        assert n_ladder == n_det, (d, n_ladder, n_det)
        norms.add(abs(n_ladder))
    assert norms == OK_SET, sorted(norms)

    divisors_1mod8 = {q for n in OK_SET for q in range(1, n + 1)
                      if n % q == 0 and q % 8 == 1}
    assert divisors_1mod8 == MOD8_DIVISORS, sorted(divisors_1mod8)
    primes_among = {q for q in MOD8_DIVISORS
                    if q > 1 and all(q % r for r in range(2, q))}
    assert primes_among == {17}, primes_among

    # consistency scan past the G328 bound
    sieve = bytearray(b"\x01") * (LIMIT + 1)
    sieve[:2] = b"\x00\x00"
    for i in range(2, int(LIMIT ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i:: i] = b"\x00" * len(sieve[i * i:: i])
    primes = [p for p in range(17, LIMIT + 1) if sieve[p] and p % 8 == 1]
    profile = {}
    for p in primes:
        g = next(x for x in range(2, p)
                 if pow(x, 4, p) == p - 1 and pow(x, 8, p) == 1)
        images = {(c[0] + c[1] * g + c[2] * g * g + c[3] * g * g * g) % p
                  for c in data}
        profile[p] = len(images)
    assert profile[17] == 16
    assert all(profile[p] == 40 for p in primes if p != 17), \
        {p: v for p, v in profile.items() if p != 17 and v != 40}

    print("G330 exact-boundary certificate")
    print(f"norm value set (780 pairs, two methods agree): {sorted(norms)}")
    print(f"divisors = 1 (mod 8): {sorted(divisors_1mod8)}; only prime: 17")
    print(f"scan: {len(primes)} primes p = 1 (mod 8) in [17, {LIMIT}]; "
          f"p=17 -> 16 values; all others -> 40")
    print("PASS: the weight-{1,3} spectrum collision boundary is exactly {17}")


if __name__ == "__main__":
    main()

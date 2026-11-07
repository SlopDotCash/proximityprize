#!/usr/bin/env python3
"""#466 R305c: census of the depth-3 bad-prime set for n = 2^k (n >= 2).

Every bad prime (nonzero depth-3 excess) divides |Norm(z)| for some nonzero difference z of
two char-0 3-sum vectors (if z(g) = 0 mod p for an order-n element g, a prime of Z[zeta_n]
above p divides z, so p | Norm(z)).  This probe enumerates ALL difference classes, computes
their cyclotomic norms EXACTLY in integer arithmetic (the 2-power tower
N(a(x^2) + x b(x^2)) = N(a(y)^2 - y b(y)^2), i.e. the resultant Res(x^{n/2} + 1, z)), factors
them (trial division + Pollard rho), and evaluates the certified candidate primes p = 1 (mod n),
giving the table {(p, excess(p))} with exact-Wick violations
(excess > 45n^2 - 40n) flagged.

Certification status: the table is complete for ALL p exactly when (a) the norms are exact
(guaranteed: int64 is used only under a proved no-overflow bound, Python integers otherwise),
(b) every factorization multiplies back to its norm (checked), and (c) every reported prime
factor is below MR_DETERMINISTIC_BOUND, where Miller-Rabin with the prime bases 2..41 is a
deterministic primality test.  If (c) fails the probe says so and exits with status 2: the
table then covers only the certified candidates.  (An earlier version rounded complex128
products and cast to int64 — overflowing for n = 64 — and so certified nothing.)
"""

from __future__ import annotations

import argparse
import math
import operator
import random
import sys
from collections import defaultdict

import numpy as np


def build_n3(n: int) -> tuple[np.ndarray, np.ndarray]:
    m = n // 2
    N3: dict[tuple[int, ...], int] = defaultdict(int)
    for a in range(n):
        sa, ia = (1, a) if a < m else (-1, a - m)
        for b in range(n):
            sb, ib = (1, b) if b < m else (-1, b - m)
            for c in range(n):
                sc, ic = (1, c) if c < m else (-1, c - m)
                v = [0] * m
                v[ia] += sa
                v[ib] += sb
                v[ic] += sc
                N3[tuple(v)] += 1
    keys = np.array(list(N3.keys()), dtype=np.int8)
    cnts = np.array([N3[tuple(k)] for k in keys], dtype=np.int64)
    return keys, cnts


def distinct_differences(keys: np.ndarray) -> np.ndarray:
    """All distinct nonzero differences keys[j] - keys[i] (as int8 rows)."""
    K, m = keys.shape
    seen = set()
    for i in range(K):
        diffs = keys - keys[i]
        for row in diffs.view(f"V{m}").ravel():
            seen.add(row.tobytes())
    zero = bytes(m)
    seen.discard(zero)
    out = np.frombuffer(b"".join(sorted(seen)), dtype=np.int8).reshape(-1, m)
    return out


INT64_SAFE = 2**62  # strict bound on every intermediate magnitude allowed in int64

# Miller-Rabin with the first 13 prime bases (2..41) is deterministic below this bound
# (Sorenson-Webster 2015, psi_13 = 3317044064679887385961981).
MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
MR_DETERMINISTIC_BOUND = 3317044064679887385961981


def validate_n(n: int) -> None:
    """The tower norm and antipodal reduction need a power of two n >= 2."""
    try:
        n = operator.index(n)
    except TypeError as exc:
        raise ValueError(f"n must be a power of two >= 2, got {n!r}") from exc
    if n < 2 or n & (n - 1):
        raise ValueError(f"n must be a power of two >= 2, got {n!r}")


def _negacyclic_square_step(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    """Rows of a(y)^2 - y*b(y)^2 reduced modulo y^L + 1 (L = a.shape[1])."""
    rows, L = a.shape
    a2 = np.zeros((rows, 2 * L - 1), dtype=a.dtype)
    b2 = np.zeros((rows, 2 * L - 1), dtype=a.dtype)
    for i in range(L):
        a2[:, i:i + L] += a[:, i:i + 1] * a
        b2[:, i:i + L] += b[:, i:i + 1] * b
    a2r = a2[:, :L].copy()
    a2r[:, :L - 1] -= a2[:, L:]
    b2r = b2[:, :L].copy()
    b2r[:, :L - 1] -= b2[:, L:]
    yb2 = np.empty_like(b2r)
    yb2[:, 1:] = b2r[:, :-1]
    yb2[:, 0] = -b2r[:, -1]
    return a2r - yb2


def norms_of(zs: np.ndarray, n: int) -> np.ndarray:
    """Exact norms of integer rows in Z[X]/(X^(n/2)+1).

    Each tower step squares the l1 bound. The int64 fast path is used only
    after bounding both the initial row sums and all convolution intermediates.
    Object rows are normalized to Python integers before multiplication.
    """
    validate_n(n)
    m = operator.index(n) // 2
    zs = np.asarray(zs)
    if zs.ndim != 2 or zs.shape[1] != m:
        raise ValueError(f"expected rows of length n/2 = {m}, got shape {zs.shape}")
    if len(zs) == 0:
        return np.empty(0, dtype=object)

    cur = None
    if zs.dtype.kind in "iu":
        max_entry = max(abs(int(zs.min())), abs(int(zs.max())))
        if m * max_entry < INT64_SAFE:
            int_rows = zs.astype(np.int64, copy=False)
            l1_max = int(np.max(np.sum(np.abs(int_rows), axis=1)))
            if l1_max ** m < INT64_SAFE:
                cur = int_rows
    if cur is None:
        cur = np.empty(zs.shape, dtype=object)
        for position, value in np.ndenumerate(zs):
            cur[position] = operator.index(value)

    while cur.shape[1] > 1:
        cur = _negacyclic_square_step(cur[:, 0::2], cur[:, 1::2])
    return cur[:, 0].astype(object, copy=False)


def is_prime_certified(x: int) -> bool:
    """Deterministic primality for 0 <= x < MR_DETERMINISTIC_BOUND; raises beyond it."""
    if x >= MR_DETERMINISTIC_BOUND:
        raise ValueError(f"{x} is outside the deterministic Miller-Rabin range")
    if x < 2:
        return False
    for p in MR_BASES:
        if x % p == 0:
            return x == p
    d, s = x - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in MR_BASES:
        y = pow(a, d, x)
        if y in (1, x - 1):
            continue
        for _ in range(s - 1):
            y = y * y % x
            if y == x - 1:
                break
        else:
            return False
    return True


def _probable_prime_large(x: int) -> bool:
    """Probabilistic test used ONLY for factors beyond the certified range."""
    d, s = x - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    rng = random.Random(x)
    for a in list(MR_BASES) + [rng.randrange(2, x - 1) for _ in range(32)]:
        y = pow(a, d, x)
        if y in (1, x - 1):
            continue
        for _ in range(s - 1):
            y = y * y % x
            if y == x - 1:
                break
        else:
            return False
    return True


def pollard_rho(x: int) -> int:
    """A nontrivial factor of the odd composite x."""
    if x % 2 == 0:
        return 2
    while True:
        c = random.randrange(1, x)
        a = b = random.randrange(2, x)
        d = 1
        while d == 1:
            a = (a * a + c) % x
            b = (b * b + c) % x
            b = (b * b + c) % x
            d = math.gcd(abs(a - b), x)
        if d != x:
            return d


def factorize(x: int) -> tuple[list[int], bool]:
    """Prime factors of x >= 1 (with multiplicity) and whether every primality verdict
    is certified (all factors below MR_DETERMINISTIC_BOUND). The product is checked."""
    x = operator.index(x)
    if x < 1:
        raise ValueError(f"factorize expects a positive integer, got {x}")
    out: list[int] = []
    certified = True
    stack = [x]
    for p in MR_BASES:
        while stack[0] % p == 0:
            stack[0] //= p
            out.append(p)
    while stack:
        y = stack.pop()
        if y == 1:
            continue
        if y < MR_DETERMINISTIC_BOUND:
            prime = is_prime_certified(y)
        else:
            prime = _probable_prime_large(y)
            if prime:
                certified = False
        if prime:
            out.append(y)
        else:
            d = pollard_rho(y)
            stack += [d, y // d]
    if math.prod(out) != x:
        raise ArithmeticError("factorization does not multiply back to the norm")
    return sorted(out), certified


def exact_excess(p: int, n: int, keys: np.ndarray, cnts: np.ndarray, e3_char0: int) -> int:
    """Compute the excess over F_p for a caller-supplied prime p = 1 mod n.

    Primality is checked inside the deterministic range. For larger fields
    the caller supplies a known prime, as in the retained prize-field control.
    The census driver uses only certified prime factors.
    """
    validate_n(n)
    n, p = operator.index(n), operator.index(p)
    if p < 2 or p % n != 1 or (p < MR_DETERMINISTIC_BOUND and not is_prime_certified(p)):
        raise ValueError(f"p = {p} must be a prime = 1 (mod {n})")
    m = n // 2
    g0 = None
    for g in range(2, p):
        cand = pow(g, (p - 1) // n, p)
        if pow(cand, n // 2, p) == p - 1:
            g0 = cand
            break
    if g0 is None:
        raise ValueError(f"no element of order {n} found modulo {p}")
    powers = np.empty(m, dtype=object)
    x = 1
    for j in range(m):
        powers[j] = x
        x = x * g0 % p
    evals = (keys.astype(object) @ powers) % p
    order = np.argsort(evals, kind="stable")
    ev_sorted = evals[order]
    ct_sorted = cnts[order].astype(object)
    boundaries = np.nonzero(np.diff(ev_sorted))[0] + 1
    group_sums = np.add.reduceat(ct_sorted, np.concatenate(([0], boundaries)))
    return int(np.sum(group_sums**2)) - e3_char0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=32)
    args = ap.parse_args()
    n = args.n
    try:
        validate_n(n)
    except ValueError as exc:
        ap.error(str(exc))
    headroom = 45 * n**2 - 40 * n

    keys, cnts = build_n3(n)
    e3_char0 = sum(int(c) ** 2 for c in cnts)
    print(f"n={n}: K={len(keys)} vectors, char0={e3_char0}, headroom={headroom}", flush=True)

    zs = distinct_differences(keys)
    print(f"{len(zs)} distinct nonzero difference classes", flush=True)

    norms = norms_of(zs, n)
    if n == 2:
        # Q(zeta_2) = Q, so a nonzero class may have negative norm.
        norms = np.abs(norms)
    if not all(v > 0 for v in norms):
        raise ArithmeticError("nonpositive absolute norm on a nonzero class")
    distinct_norms = sorted(set(norms))
    print(f"{len(distinct_norms)} distinct exact Norm values, max={max(distinct_norms)}",
          flush=True)

    candidates: set[int] = set()
    certified = True
    for nv in distinct_norms:
        factors, ok = factorize(nv)
        certified = certified and ok
        for p in set(factors):
            if p % n == 1:
                candidates.add(p)
    checked_primes = sorted(p for p in candidates if p < MR_DETERMINISTIC_BOUND)
    print(f"{len(checked_primes)} certified candidate primes ≡ 1 mod {n} dividing some norm", flush=True)
    if not certified:
        print(f"WARNING: some norm factors are outside the deterministic Miller-Rabin range. "
              f"Skipped {len(candidates) - len(checked_primes)} unresolved candidates ≡ 1 mod {n}.",
              flush=True)

    rows = []
    for p in checked_primes:
        exc = exact_excess(p, n, keys, cnts, e3_char0)
        if exc:
            rows.append((p, exc))
    label = "COMPLETE (certified)" if certified else "DIAGNOSTIC (uncertified)"
    scope = "all beta" if certified else "certified factors only"
    print(f"\n{label} bad-prime table for n={n} ({len(rows)} primes with nonzero excess, "
          f"{scope}):", flush=True)
    quantum = 0
    for p, exc in rows:
        beta = math.log(p) / math.log(n)
        quantum = math.gcd(quantum, exc)
        print(f"  p={p:>14} beta={beta:.3f} excess={exc}"
              + ("  *** EXACT-WICK VIOLATION" if exc > headroom else ""), flush=True)
    viol = [(p, e) for p, e in rows if e > headroom]
    print(f"\nexact-Wick violations: {len(viol)}; largest violating prime: "
          f"{max(viol)[0] if viol else None} "
          f"(beta={math.log(max(viol)[0])/math.log(n):.3f})" if viol else "none", flush=True)
    print(f"excess quantum (gcd over all bad primes): {quantum}", flush=True)
    largest_scope = "overall" if certified else "among checked candidates"
    print(f"largest bad prime {largest_scope}: p={rows[-1][0]} "
          f"beta={math.log(rows[-1][0])/math.log(n):.3f}" if rows
          else f"no bad primes among checked candidates", flush=True)
    return 0 if certified else 2


if __name__ == "__main__":
    sys.exit(main())

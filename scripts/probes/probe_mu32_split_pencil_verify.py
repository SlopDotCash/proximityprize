#!/usr/bin/env python3
"""Exact verification of the candidates printed by the pencil and cycle C++ filters

    probe_mu32_three_split_pencils.cpp   (mode "pencil")
    probe_mu32_four_cycle_pencils.cpp    (mode "cycle")

Usage:
    c++ -O3 -std=c++17 scripts/probes/probe_mu32_three_split_pencils.cpp -o /tmp/pencil
    c++ -O3 -std=c++17 scripts/probes/probe_mu32_four_cycle_pencils.cpp -o /tmp/cycle
    c++ -O3 -std=c++17 scripts/probes/probe_mu32_star_cube_filter.cpp -o /tmp/cube
    /tmp/cube 32 8                       # expect: candidates=0
    /tmp/pencil 32 7 8 > p7.txt          # expect: candidates=748
    /tmp/pencil 32 8 8 > p8.txt          # expect: candidates=3736
    /tmp/cycle 32 8 > c.txt              # expect: candidates=4077
    python3 -O scripts/probes/probe_mu32_split_pencil_verify.py pencil 32 7 p7.txt   # 0 pencils
    python3 -O scripts/probes/probe_mu32_split_pencil_verify.py pencil 32 8 p8.txt   # 23, all antipodal
    python3 -O scripts/probes/probe_mu32_split_pencil_verify.py cycle 32 c.txt       # 33, all antipodal

The C++ filters test necessary conditions in characteristic zero (quadratic or cubic
residue characters modulo 14-16 small split primes).  This script decides each
surviving candidate exactly modulo the 61-bit split prime P below; a characteristic-zero
configuration reduces to one modulo P.  Details: PROGRESS.md, entry
"No four rate-half codewords within nine errors on the 32nd roots of unity".
"""
import argparse
import random
import re
from math import gcd, isqrt

P = 1332653270109928577  # prime, P = 1 mod 64


def verify_split_prime():
    """Check the factorization and a Lucas witness for the recorded split prime."""
    odd_factors = (283, 36_789_235_592_699)
    if P - 1 != 2**7 * odd_factors[0] * odd_factors[1]:
        raise ArithmeticError("Split-prime factorization does not match")
    for factor in odd_factors:
        if any(factor % divisor == 0 for divisor in range(3, isqrt(factor) + 1, 2)):
            raise ArithmeticError(f"Composite factor in split-prime certificate: {factor}")
    if pow(3, P - 1, P) != 1 or any(
        gcd(pow(3, (P - 1) // factor, P) - 1, P) != 1
        for factor in (2, *odd_factors)
    ):
        raise ArithmeticError("Invalid split-prime Lucas witness")


def gen(n):
    rng = random.Random(5)
    while True:
        g = pow(rng.randrange(2, P), (P - 1) // n, P)
        if pow(g, n // 2, P) == P - 1:
            return g


def poly(roots):
    c = [1]
    for r in roots:
        nxt = [0] * (len(c) + 1)
        for i, a in enumerate(c):
            nxt[i + 1] = (nxt[i + 1] + a) % P
            nxt[i] = (nxt[i] - a * r) % P
        c = nxt
    return c


def collinear(a, b, c):
    u = [(x - y) % P for x, y in zip(a, b)]
    v = [(x - y) % P for x, y in zip(c, b)]
    i = next((i for i, x in enumerate(u) if x), None)
    if i is None or v[i] == 0:
        return False
    f = v[i] * pow(u[i], P - 2, P) % P
    return all((x * f - y) % P == 0 for x, y in zip(u, v))


def half_splits(r, tot, size):
    """Index sets A containing 0 with prod(r[A])^2 == tot."""
    hits = []

    def dfs(i, left, acc, chosen):
        if left == 0:
            if acc * acc % P == tot:
                hits.append(tuple(chosen))
            return
        for j in range(i, len(r) - left + 1):
            dfs(j + 1, left - 1, acc * r[j] % P, chosen + [j])

    dfs(1, size - 1, r[0], [0])
    return hits


CANDIDATE = re.compile(r"CAND B=([0-9a-f]{16}) D=([0-9a-f]{16})")
PENCIL_DONE = re.compile(r"DONE N=(\d+) m=(\d+) B-orbits=(\d+) candidates=(\d+)")
CYCLE_DONE = re.compile(r"DONE N=(\d+) Q0-orbits=(\d+) candidates=(\d+)")
EXPECTED = {
    ("pencil", 32, 7): (748, 0),
    ("pencil", 32, 8): (3736, 23),
    ("cycle", 32, None): (4077, 33),
}


def candidates(path, mode, n, m):
    anchor_size = m if mode == "pencil" else n // 4 - 1
    remainder_size = n - anchor_size - 2 * (m if mode == "pencil" else n // 4)
    footer = PENCIL_DONE if mode == "pencil" else CYCLE_DONE
    records = []
    seen = set()
    done = False
    with open(path, encoding="ascii") as stream:
        for line_number, line in enumerate(stream, 1):
            line = line.strip()
            if not line:
                continue
            if done:
                raise ValueError(f"{path}:{line_number}: data after DONE")
            if match := CANDIDATE.fullmatch(line):
                anchor, remainder = record = tuple(int(mask, 16) for mask in match.groups())
                if (
                    (anchor | remainder) >> n
                    or anchor & remainder
                    or anchor.bit_count() != anchor_size
                    or remainder.bit_count() != remainder_size
                    or record in seen
                ):
                    raise ValueError(f"{path}:{line_number}: invalid or duplicate candidate masks")
                seen.add(record)
                records.append(record)
            elif match := footer.fullmatch(line):
                values = tuple(map(int, match.groups()))
                if values[:-2] != ((n, m) if mode == "pencil" else (n,)):
                    raise ValueError(f"{path}:{line_number}: DONE parameters do not match")
                if values[-2] == 0 or values[-1] != len(records):
                    raise ValueError(f"{path}:{line_number}: incomplete candidate log")
                done = True
            else:
                raise ValueError(f"{path}:{line_number}: unexpected record")
    if not done:
        raise ValueError(f"{path}: missing DONE footer")
    if (expected := EXPECTED.get((mode, n, m))) is not None and len(records) != expected[0]:
        raise ValueError(f"{path}: expected {expected[0]} candidates, got {len(records)}")
    return records


def antipodal(s, n):
    return all((x + n // 2) % n in s for x in s)


def main():
    args_parser = argparse.ArgumentParser(description="Verify a complete finite-pencil candidate scan")
    modes = args_parser.add_subparsers(dest="mode", required=True)
    pencil = modes.add_parser("pencil")
    pencil.add_argument("n", type=int, choices=(8, 16, 32))
    pencil.add_argument("m", type=int, choices=range(2, 9))
    pencil.add_argument("path")
    cycle = modes.add_parser("cycle")
    cycle.add_argument("n", type=int, choices=(16, 32))
    cycle.add_argument("path")
    args = args_parser.parse_args()
    mode, n = args.mode, args.n
    m = getattr(args, "m", None)
    if m is not None and 3 * m > n:
        args_parser.error("pencil degree requires 3*M <= N")
    try:
        records = candidates(args.path, mode, n, m)
    except (OSError, ValueError) as error:
        args_parser.error(str(error))

    verify_split_prime()
    g = gen(n)
    pts = [pow(g, i, P) for i in range(n)]
    found = []
    if mode == "pencil":
        for bm, dm in records:
            bs = [i for i in range(n) if bm >> i & 1]
            s = [i for i in range(n) if not (bm >> i & 1) and not (dm >> i & 1)]
            b0, b1 = pts[bs[0]], pts[bs[1]]
            r = [(b0 - pts[x]) * pow(b1 - pts[x], P - 2, P) % P for x in s]
            tot = 1
            for x in r:
                tot = tot * x % P
            pb = poly([pts[i] for i in bs])
            for idx in half_splits(r, tot, m):
                a = [s[j] for j in idx]
                c = [x for x in s if x not in a]
                if collinear(poly([pts[i] for i in a]), pb, poly([pts[i] for i in c])):
                    found.append((tuple(bs), tuple(a), tuple(c)))
        print(f"three-split pencils of degree {m} on mu_{n}: {len(found)}")
    else:
        b = n // 4
        for tm, dm in records:
            ts = [i for i in range(n) if tm >> i & 1]
            s = [i for i in range(n) if not (tm >> i & 1) and not (dm >> i & 1)]
            x0 = pts[ts[0]]
            rs = [[(x0 - pts[x]) * pow(pts[t] - pts[x], P - 2, P) % P for x in s] for t in ts[1:]]
            tots = []
            for r in rs:
                t = 1
                for x in r:
                    t = t * x % P
                tots.append(t)
            for idx in half_splits(rs[0], tots[0], b):
                ok = True
                for r, t in zip(rs[1:], tots[1:]):
                    acc = 1
                    for j in idx:
                        acc = acc * r[j] % P
                    if acc * acc % P != t:
                        ok = False
                        break
                if ok:
                    a = tuple(s[j] for j in idx)
                    found.append((tuple(ts), a, tuple(x for x in s if x not in a)))
        print(f"(Q0, A, C) with L_A/L_C constant on Q0 on mu_{n}: {len(found)}")
    sym = all(antipodal(set(x), n) for row in found for x in row[1:])
    if (expected := EXPECTED.get((mode, n, m))) is not None:
        if len(found) != expected[1] or not sym:
            raise ArithmeticError(f"Unexpected census for {mode} n={n}: {len(found)} results, antipodal={sym}")
    print("every listed A and C is antipodally symmetric:", sym)
    for row in found:
        print(" ", row)


if __name__ == "__main__":
    main()

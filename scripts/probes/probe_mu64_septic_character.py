#!/usr/bin/env python3
"""Enumerate exact sextic and septic fibers on μ64 in the second production field.

Run with Python 3 and a C++17 compiler. A worker requires about 3.6 GB. Use
--anchor A B for just the test exponents 0,A,B and --workers N for parallelism.
The default checks three full septics. --minimum-fiber 6 checks a partial third
septic, and --degree 6 classifies all full sextics against cubic orbits on μ32.
"""
import argparse
import os
from concurrent.futures import ThreadPoolExecutor
from functools import lru_cache
from itertools import combinations
from collections import defaultdict
from hashlib import sha256
from math import prod
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory

from probe_many_head_locator_attack import require
from probe_smooth_four_head_attack import GENERATOR, PRIME

ORDER = 2**30
OMEGA = pow(GENERATOR, ORDER//64, PRIME)
SITES = tuple(pow(OMEGA, i, PRIME) for i in range(64))
def anchors_for(size):
    return [(a, span) for span in range(2, 128//size+1) for a in range(1, span//2+1)]


@lru_cache(maxsize=None)
def character(value):
    """Log to base g of the projection to μ_(2^30), bit by bit."""
    require(value % PRIME != 0, "character domain")
    image = pow(value, (PRIME-1)//ORDER, PRIME)
    residual, inverse, exponent = image, pow(GENERATOR, -1, PRIME), 0
    for bit in range(30):
        sign = pow(residual, 1 << (29-bit), PRIME)
        require(sign in (1, PRIME-1), "projected order")
        if sign != 1:
            exponent += 1 << bit
            residual = residual*inverse % PRIME
        inverse = inverse*inverse % PRIME
    require(residual == 1 and pow(GENERATOR, exponent, PRIME) == image, "discrete log")
    return exponent


def weights(a, b):
    rows = []
    for j, x in enumerate(SITES):
        if j in (0, a, b):
            continue
        ref = character((1-x) % PRIME)
        left = (character((SITES[a]-x) % PRIME)-ref) % ORDER
        right = (character((SITES[b]-x) % PRIME)-ref) % ORDER
        rows.append(f"{j} {left} {right}\n")
    return "".join(rows)


def check(a, b, output, degree=7, minimum=7):
    """Recompute every surviving proportionality and the full fiber in F_p."""
    pairs = []
    maximum = 0
    full = []
    anchor_mask = 1 | 1 << a | 1 << b
    lines = output.splitlines()
    for line in lines:
        s, t = sorted(int(entry, 16) for entry in line.split())
        require(s.bit_count() == t.bit_count() == degree and not s&t and not (s|t)&anchor_mask,
                "disjoint seven-site supports")
        sr = [SITES[j] for j in range(64) if s>>j&1]
        tr = [SITES[j] for j in range(64) if t>>j&1]
        def value(roots, x):
            return prod(x-r for r in roots) % PRIME
        ls, lt = value(sr, 1), value(tr, 1)
        def same(j):
            return (lt*value(sr, SITES[j])-ls*value(tr, SITES[j])) % PRIME == 0
        if not same(a) or not same(b):
            continue
        fiber = sum(1 << j for j in range(64) if not (s|t)>>j&1 and same(j))
        maximum = max(maximum, fiber.bit_count())
        pairs.append((s, t, fiber))
        if fiber.bit_count() >= minimum:
            full.append((s, t, fiber))
    require(len(pairs) == len(set(pairs)), "each unordered pair occurs once")
    data = "".join(f"{s:016x} {t:016x} {f:016x}\n" for s,t,f in sorted(pairs))
    return (a, b, len(lines), len(pairs), maximum, sha256(data.encode()).hexdigest()), full


def cubic_orbit(triple):
    """Normalize by the dihedral action and by permutation of the three fibers."""
    return min(tuple(sorted(tuple(sorted((eps*x+shift) % 32 for x in fiber))
                            for fiber in triple))
               for eps in (1,-1) for shift in range(32))


def cubic_orbits():
    """Enumerate the cubic pencils separately on the 32-site quotient by exact evaluation."""
    h = SITES[::2]
    anchors = {cubic_orbit((t,))[0] for t in combinations(range(32), 3)}
    require(len(anchors) == 85, "cubic anchor orbits")
    result = set()
    for u in sorted(anchors):
        buckets = defaultdict(list)
        for support in combinations([i for i in range(32) if i not in u], 3):
            values = [prod(h[i]-h[j] for j in support) % PRIME for i in u]
            inverse = pow(values[0], -1, PRIME)
            buckets[tuple(v*inverse % PRIME for v in values[1:])].append(support)
        for group in buckets.values():
            for a,b in combinations(group, 2):
                if set(a).isdisjoint(b):
                    result.add(cubic_orbit((u,a,b)))
    return result


def verify_sextics(hits):
    orbits = set()
    for triple in hits:
        require(all(m >> 32 == m & 0xffffffff for m in triple), "antipodal sextics")
        small = [tuple(i for i in range(32) if m >> i & 1) for m in triple]
        orbits.add(cubic_orbit(small))
    require(len(orbits) == 33 and orbits == cubic_orbits(), "all cubic quotient orbits")
    rows = "".join(" ".join(f"{sum(1 << i for i in fiber):08x}" for fiber in t)+"\n"
                   for t in sorted(orbits))
    digest = sha256(rows.encode()).hexdigest()
    require(digest == "93256283d406fd78e831301a3f966b3a74f6f8fd390dd5f9d653fd5776ed68d2", "cubic orbit receipt")
    print(f"{len(orbits)} cubic orbits, SHA-256 {digest}; every split sextic descends through X^2")


def main():
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument("--workers", type=int, default=1)
    args.add_argument("--anchor", type=int, nargs=2)
    args.add_argument("--degree", type=int, choices=(6,7), default=7)
    args.add_argument("--minimum-fiber", type=int, choices=(6,7))
    args = args.parse_args()
    require(args.workers > 0, "positive worker count")
    require(pow(GENERATOR, ORDER//2, PRIME)==PRIME-1 and SITES[32]==PRIME-1,
            "named generator and μ64")
    minimum = args.minimum_fiber or args.degree
    require(minimum <= args.degree, "fiber size at most polynomial degree")
    all_anchors = anchors_for(minimum)
    anchors = [tuple(args.anchor)] if args.anchor else all_anchors
    require(all(t in all_anchors for t in anchors), "valid anchor")
    source = Path(__file__).with_suffix(".cpp")
    combined = sha256()
    total_screened = total_exact = maximum = 0
    hits = []
    with TemporaryDirectory() as directory:
        binary = Path(directory)/"septic"
        run([os.environ.get("CXX", "c++"), "-O3", "-std=c++17", str(source), "-o", str(binary)], check=True)
        def one(anchor):
            a, b = anchor
            output = run([str(binary), str(args.degree)], input=weights(a,b), text=True, capture_output=True,
                         check=True).stdout
            return check(a, b, output, args.degree, minimum)
        with ThreadPoolExecutor(max_workers=args.workers) as workers:
            for row, full in workers.map(one, anchors):
                record = " ".join(map(str,row))
                print(record, flush=True)
                combined.update((record+"\n").encode())
                total_screened += row[2]
                total_exact += row[3]
                maximum = max(maximum,row[4])
                hits.extend(full)
    print(f"{len(anchors)} anchors, {total_screened} disjoint character candidates, "
          f"{total_exact} exact ratio matches, maximum fiber {maximum}, "
          f"{len(hits)} fibers of size at least {minimum}, SHA-256 {combined.hexdigest()}")
    if not args.anchor and minimum == 7:
        require((total_screened, total_exact, maximum, len(hits)) == (35139, 35075, 4, 0) and
                combined.hexdigest() == "c88ce93b45844b4842081799ebd765a34873994c050674be13fa759f926ee8e5",
                "complete production-field census")
    if not args.anchor and args.degree == 7 and minimum == 6:
        require((total_screened, total_exact, maximum, len(hits)) == (44542, 44454, 4, 0) and
                combined.hexdigest() == "70659ce920f12397da72012d8f31f0f0f7edead2408b89adc64a3bc78a3e363d",
                "extended partial-septic enumeration")
    if not args.anchor and args.degree == 6:
        require((total_screened, total_exact, maximum, len(hits)) == (31139, 31133, 6, 144) and
                combined.hexdigest() == "753cbe918af5407d6a809953740119f7874b21aa33bc84239744f9944d961c18",
                "complete sextic enumeration")
        verify_sextics(hits)
    if args.anchor:
        for hit in hits:
            print("FIBER", *(f"{mask:016x}" for mask in hit))


if __name__ == "__main__":
    main()

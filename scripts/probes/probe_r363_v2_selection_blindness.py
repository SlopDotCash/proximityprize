#!/usr/bin/env python3
"""#466 R363: is depth-3 census badness correlated with v2(p-1) (deployment shape)?

Parses the r305 complete census (n=32) and cross-tabulates bad/violating rates against
the 2-adic valuation of p-1 over all primes ≡ 1 mod 32 up to 2e5.
Result (2026-07-09): NO correlation — badrate ~0.52-0.68, violrate ~0.13-0.17, flat in v2;
the single v2=16 prime (F4=65537) violates. v2-based good-prime selection is dead at depth 3.
"""
import re
from collections import defaultdict

bad = {}
for line in open('scripts/probes/_out_466_r305_census_n32.txt'):
    m = re.match(r'\s+p=\s*(\d+) beta=([\d.]+) excess=(\d+)(.*)', line)
    if m:
        bad[int(m.group(1))] = (int(m.group(3)), 'VIOLATION' in m.group(4))

def v2(x):
    v = 0
    while x % 2 == 0:
        x //= 2
        v += 1
    return v

N = 200000
sieve = bytearray([1]) * (N + 1)
sieve[0:2] = b'\x00\x00'
for i in range(2, int(N**0.5) + 1):
    if sieve[i]:
        sieve[i*i::i] = b'\x00' * len(sieve[i*i::i])
allp = [p for p in range(33, N, 32) if sieve[p]]
stats = defaultdict(lambda: [0, 0, 0])
for p in allp:
    v = v2(p - 1)
    stats[v][0] += 1
    if p in bad:
        stats[v][1] += 1
        if bad[p][1]:
            stats[v][2] += 1
print("v2 | all | bad | badrate | viol | violrate")
for v in sorted(stats):
    a, b, c = stats[v]
    print(f"{v:3d}| {a:5d}| {b:4d}| {b/a:.4f}  | {c:4d}| {c/a:.4f}")

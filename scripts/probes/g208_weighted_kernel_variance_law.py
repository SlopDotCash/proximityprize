#!/usr/bin/env python3
"""Exact checks for G208's collision-free weighted-kernel variance law."""

CELLS = [
    (113, 8, 354368),
    (449, 8, 11063360),
    (2593, 16, None),
    (3617, 32, None),
]

for q, n, recorded in CELLS:
    assert (q - 1) % n == 0
    m = (q - 1) // n
    quotient_centered = n * (m - n)
    qw = q * n * n * (q - n * n)
    assert m >= n
    if recorded is not None:
        assert qw == recorded, (q, n, qw, recorded)
    print(
        f"q={q:5d} n={n:2d} m={m:4d} classEnergy={quotient_centered:6d} "
        f"RMS2_nonprincipal={quotient_centered / (m - 1):.9f} QW={qw}"
    )

print("\nfixed n=8 threshold/asymptotic ladder")
for q in [113, 257, 449, 1009, 1601, 4001, 8009, 16001]:
    if (q - 1) % 8:
        continue
    m = (q - 1) // 8
    if m < 8:
        continue
    energy = 8 * (m - 8)
    print(f"q={q:5d} m={m:4d} E_nontriv={energy:6d} avg={energy / (m - 1):.9f}")

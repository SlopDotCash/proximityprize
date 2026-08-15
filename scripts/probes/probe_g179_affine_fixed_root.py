#!/usr/bin/env python3
"""Exact G179 audit: affine norm orbit versus one fixed deployed root."""
from math import gcd

P = 17318209
N = 64
OMEGA = 7937154
BASE = {8: 1, 13: 1, 14: -1, 20: -1}
UNITS = [a for a in range(N) if gcd(a, N) == 1]


def transform(a: int, b: int) -> dict[int, int]:
    out: dict[int, int] = {}
    for exponent, coefficient in BASE.items():
        target = (a * exponent + b) % N
        out[target] = out.get(target, 0) + coefficient
    return out


def canonical(poly: dict[int, int]) -> tuple[int, ...]:
    values = [0] * N
    for exponent, coefficient in poly.items():
        values[exponent] += coefficient
    return tuple(values)


def evaluate(poly: dict[int, int]) -> int:
    return sum(coefficient * pow(OMEGA, exponent, P)
               for exponent, coefficient in poly.items()) % P


affine = {canonical(transform(a, b)) for a in UNITS for b in range(N)}
vanishing = {(a, b, canonical(transform(a, b)))
             for a in UNITS for b in range(N)
             if evaluate(transform(a, b)) == 0}
vanishing_polys = {poly for _, _, poly in vanishing}
vanishing_multipliers = sorted({a for a, _, _ in vanishing})

assert len(UNITS) == 32
assert len(affine) == 2048
assert len(vanishing) == 64
assert len(vanishing_polys) == 64
assert vanishing_multipliers == [1]
assert evaluate(BASE) == 0

print("PASS G179 affine fixed-root collapse")
print(f"n={N} phi={len(UNITS)} affine={len(affine)}")
print(f"fixed_root_vanishing={len(vanishing_polys)} multipliers={vanishing_multipliers}")
print(f"certificate_to_fixed_root_loss={len(affine) // len(vanishing_polys)}")

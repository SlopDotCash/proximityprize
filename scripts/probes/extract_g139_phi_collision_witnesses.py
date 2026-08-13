#!/usr/bin/env python3
"""Extract exact subgroup witnesses from G139 Phi collisions.

For a collision

    (g^r - 1)^n = (g^s - 1)^n,

the quotient

    u = (g^r - 1) / (g^s - 1)

has `u^n = 1`, and therefore gives the additive relation

    g^r + u = 1 + u*g^s

inside the generated order-`n` subgroup.  This companion makes failed
`PhiWindowInjective` checks auditable as compact exact witnesses.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import json

import probe_g139_phi_certificate as phi


CONTROL_CELLS = (
    (64, 17318209, "G173-accident"),
    (512, 138027521, "n512-offdiag-accident"),
)


@dataclass(frozen=True)
class RelationValues:
    a: int
    b: int
    c: int
    d: int


@dataclass(frozen=True)
class RelationExponents:
    a: int
    b: int
    c: int
    d: int


@dataclass(frozen=True)
class CollisionWitness:
    label: str
    n: int
    p: int
    generator: int
    r: int
    s: int
    phi_value: int
    u: int
    u_exponent: int
    relation_values: RelationValues
    relation_exponents: RelationExponents
    relation_holds: bool
    phi_collision_holds: bool
    u_is_root: bool
    sidon_same_branch: bool
    sidon_swap_branch: bool
    sidon_zero_branch: bool
    normalized_g139_lawful: bool


def subgroup_table(g: int, n: int, p: int) -> dict[int, int]:
    table: dict[int, int] = {}
    x = 1
    for exponent in range(n):
        table[x] = exponent
        x = (x * g) % p
    assert x == 1
    assert len(table) == n
    return table


def extract_witness(row: phi.PhiRow, r: int, s: int) -> CollisionWitness:
    p = row.p
    n = row.n
    g = row.generator
    assert 1 <= r <= n // 2
    assert 1 <= s <= n // 2
    powers = subgroup_table(g, n, p)

    gr = pow(g, r, p)
    gs = pow(g, s, p)
    numerator = (gr - 1) % p
    denominator = (gs - 1) % p
    assert denominator != 0

    u = numerator * pow(denominator, -1, p) % p
    u_exponent = powers[u]
    d_value = u * gs % p
    d_exponent = powers[d_value]

    left_phi = pow(numerator, n, p)
    right_phi = pow(denominator, n, p)
    relation_holds = (gr + u) % p == (1 + d_value) % p
    phi_collision_holds = left_phi == right_phi
    u_is_root = pow(u, n, p) == 1

    values = RelationValues(a=gr, b=u, c=1, d=d_value)
    exponents = RelationExponents(a=r % n, b=u_exponent, c=0, d=d_exponent)
    sidon_same = values.a == values.c and values.b == values.d
    sidon_swap = values.a == values.d and values.b == values.c
    sidon_zero = (values.a + values.b) % p == 0
    normalized_lawful = (
        (values.a == 1 and values.b == values.d)
        or (values.b == 1 and values.a == values.d)
        or (sidon_zero and values.d == p - 1)
    )

    return CollisionWitness(
        label=row.label,
        n=n,
        p=p,
        generator=g,
        r=r,
        s=s,
        phi_value=left_phi,
        u=u,
        u_exponent=u_exponent,
        relation_values=values,
        relation_exponents=exponents,
        relation_holds=relation_holds,
        phi_collision_holds=phi_collision_holds,
        u_is_root=u_is_root,
        sidon_same_branch=sidon_same,
        sidon_swap_branch=sidon_swap,
        sidon_zero_branch=sidon_zero,
        normalized_g139_lawful=normalized_lawful,
    )


def control_rows() -> list[phi.PhiRow]:
    rows = []
    for n, p, label in CONTROL_CELLS:
        rows.append(phi.phi_certificate(n, p, label))
    return rows


def custom_row(args: argparse.Namespace) -> tuple[phi.PhiRow, tuple[tuple[int, int], ...]]:
    missing = [
        name
        for name in ("n", "p", "r", "s")
        if getattr(args, name) is None
    ]
    if missing:
        missing_flags = ", ".join("--" + name for name in missing)
        raise SystemExit(f"custom extraction requires: {missing_flags}")
    label = args.label or "custom"
    row = phi.phi_certificate(args.n, args.p, label)
    return row, ((args.r, args.s),)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, help="Subgroup order for a custom cell.")
    parser.add_argument("--p", type=int, help="Prime modulus for a custom cell.")
    parser.add_argument("--r", type=int, help="First half-window exponent for a custom collision.")
    parser.add_argument("--s", type=int, help="Second half-window exponent for a custom collision.")
    parser.add_argument("--label", help="Optional label for a custom cell.")
    args = parser.parse_args()

    witnesses: list[CollisionWitness] = []
    if any(getattr(args, name) is not None for name in ("n", "p", "r", "s", "label")):
        rows_and_collisions = [(custom_row(args), False)]
    else:
        rows_and_collisions = [
            ((row, row.collisions), True) for row in control_rows()
        ]

    for (row, collisions), expect_nonlawful in rows_and_collisions:
        assert collisions
        for r, s in collisions:
            witness = extract_witness(row, r, s)
            assert witness.relation_holds
            assert witness.phi_collision_holds
            assert witness.u_is_root
            if expect_nonlawful:
                assert not witness.normalized_g139_lawful
            witnesses.append(witness)

    print(json.dumps([asdict(witness) for witness in witnesses], sort_keys=True, indent=2))


if __name__ == "__main__":
    main()

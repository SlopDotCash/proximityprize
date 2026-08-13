#!/usr/bin/env python3
"""Verify a G139 Phi-collision witness without enumerating the subgroup.

This is the production-scale companion to `extract_g139_phi_collision_witnesses.py`.
Given a proposed collision and either `u` or an exponent `k` with `u = g^k`,
it checks the exact finite-field identities

    (g^r - 1)^n = (g^s - 1)^n,
    u = (g^r - 1) / (g^s - 1),
    g^r + u = 1 + u*g^s,
    u^n = 1.

For power-of-two orders, it also verifies the lightweight exact-order contract
`g^n = 1` and `g^(n/2) = -1`.  The verifier never constructs the full subgroup,
so the same code path is suitable for proposed production-scale witnesses.  It
assumes the supplied modulus is prime; for the retained production row, pair it
with `verify_g139_n2e30_arithmetic_contract.py`, which verifies primality.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import json
from pathlib import Path


DEFAULT_WITNESS_JSON = Path("scripts/probes/_out_g139_phi_collision_witnesses.json")


@dataclass(frozen=True)
class RelationValues:
    a: int
    b: int
    c: int
    d: int


@dataclass(frozen=True)
class RelationExponents:
    a: int
    b: int | None
    c: int
    d: int | None


@dataclass(frozen=True)
class WitnessVerification:
    label: str
    n: int
    p: int
    generator: int
    r: int
    s: int
    u: int
    u_exponent: int | None
    phi_value: int
    prime_modulus_assumed: bool
    exact_order_power2: bool
    window_bounds: bool
    denominator_nonzero: bool
    quotient_matches: bool
    relation_holds: bool
    phi_collision_holds: bool
    u_is_root: bool
    u_matches_exponent: bool | None
    relation_values: RelationValues
    relation_exponents: RelationExponents
    sidon_same_branch: bool
    sidon_swap_branch: bool
    sidon_zero_branch: bool
    normalized_g139_lawful: bool
    verified: bool


def is_power_of_two(n: int) -> bool:
    return n > 0 and n & (n - 1) == 0


def exact_order_power2(g: int, n: int, p: int) -> bool:
    return n > 1 and is_power_of_two(n) and pow(g, n, p) == 1 and pow(g, n // 2, p) == p - 1


def compute_u(g: int, n: int, p: int, r: int, s: int, u_exp: int | None) -> int:
    if u_exp is not None:
        return pow(g, u_exp % n, p)
    gr = pow(g, r, p)
    gs = pow(g, s, p)
    denominator = (gs - 1) % p
    if denominator == 0:
        raise ValueError("cannot derive u: g^s - 1 is zero")
    return (gr - 1) * pow(denominator, -1, p) % p


def verify_witness(
    *,
    label: str,
    n: int,
    p: int,
    generator: int,
    r: int,
    s: int,
    u: int | None,
    u_exponent: int | None,
) -> WitnessVerification:
    g = generator
    if u is None:
        u = compute_u(g, n, p, r, s, u_exponent)

    gr = pow(g, r, p)
    gs = pow(g, s, p)
    numerator = (gr - 1) % p
    denominator = (gs - 1) % p
    denominator_nonzero = denominator != 0
    derived_u = None
    if denominator_nonzero:
        derived_u = numerator * pow(denominator, -1, p) % p

    d_value = u * gs % p
    left_phi = pow(numerator, n, p)
    right_phi = pow(denominator, n, p)
    relation_holds = (gr + u) % p == (1 + d_value) % p
    phi_collision_holds = left_phi == right_phi
    u_is_root = pow(u, n, p) == 1
    u_matches_exp = None if u_exponent is None else u == pow(g, u_exponent % n, p)

    values = RelationValues(a=gr, b=u, c=1, d=d_value)
    exponents = RelationExponents(
        a=r % n,
        b=None if u_exponent is None else u_exponent % n,
        c=0,
        d=None if u_exponent is None else (u_exponent + s) % n,
    )
    sidon_same = values.a == values.c and values.b == values.d
    sidon_swap = values.a == values.d and values.b == values.c
    sidon_zero = (values.a + values.b) % p == 0
    normalized_lawful = (
        (values.a == 1 and values.b == values.d)
        or (values.b == 1 and values.a == values.d)
        or (sidon_zero and values.d == p - 1)
    )
    quotient_matches = derived_u == u if derived_u is not None else False
    window_bounds = 1 <= r <= n // 2 and 1 <= s <= n // 2
    exact_order = exact_order_power2(g, n, p)
    verified = all(
        (
            exact_order,
            window_bounds,
            denominator_nonzero,
            quotient_matches,
            relation_holds,
            phi_collision_holds,
            u_is_root,
            True if u_matches_exp is None else u_matches_exp,
        )
    )

    return WitnessVerification(
        label=label,
        n=n,
        p=p,
        generator=g,
        r=r,
        s=s,
        u=u,
        u_exponent=None if u_exponent is None else u_exponent % n,
        phi_value=left_phi,
        prime_modulus_assumed=True,
        exact_order_power2=exact_order,
        window_bounds=window_bounds,
        denominator_nonzero=denominator_nonzero,
        quotient_matches=quotient_matches,
        relation_holds=relation_holds,
        phi_collision_holds=phi_collision_holds,
        u_is_root=u_is_root,
        u_matches_exponent=u_matches_exp,
        relation_values=values,
        relation_exponents=exponents,
        sidon_same_branch=sidon_same,
        sidon_swap_branch=sidon_swap,
        sidon_zero_branch=sidon_zero,
        normalized_g139_lawful=normalized_lawful,
        verified=verified,
    )


def verify_from_record(record: dict[str, object]) -> WitnessVerification:
    return verify_witness(
        label=str(record.get("label", "witness")),
        n=int(record["n"]),
        p=int(record["p"]),
        generator=int(record["generator"]),
        r=int(record["r"]),
        s=int(record["s"]),
        u=int(record["u"]) if record.get("u") is not None else None,
        u_exponent=(
            int(record["u_exponent"]) if record.get("u_exponent") is not None else None
        ),
    )


def load_witnesses(path: Path) -> list[dict[str, object]]:
    data = json.loads(path.read_text())
    if isinstance(data, dict):
        return [data]
    if isinstance(data, list):
        return data
    raise TypeError("expected a JSON witness object or list")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--witness-json", type=Path, default=DEFAULT_WITNESS_JSON)
    parser.add_argument("--n", type=int, help="Subgroup order for a custom witness.")
    parser.add_argument("--p", type=int, help="Prime modulus for a custom witness.")
    parser.add_argument("--g", type=int, help="Order-n generator for a custom witness.")
    parser.add_argument("--r", type=int, help="First half-window exponent.")
    parser.add_argument("--s", type=int, help="Second half-window exponent.")
    parser.add_argument("--u", type=int, help="Root multiplier value.")
    parser.add_argument("--u-exp", type=int, help="Exponent k with u = g^k.")
    parser.add_argument("--label", default="custom")
    args = parser.parse_args()

    custom_names = ("n", "p", "g", "r", "s", "u", "u_exp")
    if any(getattr(args, name) is not None for name in custom_names):
        missing = [
            name
            for name in ("n", "p", "g", "r", "s")
            if getattr(args, name) is None
        ]
        if missing:
            missing_flags = ", ".join("--" + name for name in missing)
            raise SystemExit(f"custom verification requires: {missing_flags}")
        if args.u is None and args.u_exp is None:
            raise SystemExit("custom verification requires --u or --u-exp")
        results = [
            verify_witness(
                label=args.label,
                n=args.n,
                p=args.p,
                generator=args.g,
                r=args.r,
                s=args.s,
                u=args.u,
                u_exponent=args.u_exp,
            )
        ]
    else:
        results = [verify_from_record(record) for record in load_witnesses(args.witness_json)]

    for result in results:
        assert result.verified
    print(json.dumps([asdict(result) for result in results], sort_keys=True, indent=2))


if __name__ == "__main__":
    main()

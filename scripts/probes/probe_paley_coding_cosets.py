#!/usr/bin/env python3
"""Verify Paley discrepancies on two dilates of the order-sixteen budget-two coding domain."""

P = 680564733906249808969588989158290882561
GENERATOR = 249631592359537775319900728087975376651
ROOT = 236023637409912314118267886612795304038
COMPLETE = 122764
BALANCED = 6


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def character(x):
    residue = pow(x % P, (P - 1) // 2, P)
    if residue == P - 1:
        return -1
    require(residue in (0, 1), "invalid Euler residue")
    return residue


def main():
    # For each prime divisor q of P, the order of 7 modulo q has 2-adic
    # valuation 92. Thus q >= 2^92 + 1, strictly above sqrt(P).
    require((P - 1) % (1 << 93) == 1 << 92, "wrong 2-adic valuation")
    require(pow(7, (P - 1) // 2, P) == P - 1, "invalid order witness")
    require(P < ((1 << 92) + 1) ** 2, "insufficient divisor bound")
    require(P // 2**128 == 2, "wrong coding budget")
    require(pow(GENERATOR, 2**26, P) == ROOT, "wrong coding subgroup")
    require(pow(ROOT, 8, P) == P - 1, "wrong generator order")
    domain = [pow(ROOT, i, P) for i in range(16)]
    require(len(set(domain)) == 16 and all(character(x) == 1 for x in domain),
            "coding domain must contain sixteen distinct squares")

    for factor, expected in ((COMPLETE, (16, 0)), (BALANCED, (8, 8))):
        coset = [factor * x % P for x in domain]
        require(set(domain).isdisjoint(coset), "intersecting cosets")
        row = [character(1 - y) for y in coset]
        require((row.count(1), row.count(-1)) == expected, "wrong Euler signs")
        matrix = [[character(x - y) for y in coset] for x in domain]
        require(all(sorted(entries) == sorted(row) for entries in matrix), "wrong row")
        discrepancy = sum(map(sum, matrix))
        require(discrepancy == 16 * sum(row), "wrong full discrepancy")
        print(f"factor={factor} positive={expected[0]} negative={expected[1]} "
              f"discrepancy={discrepancy}")


if __name__ == "__main__":
    main()

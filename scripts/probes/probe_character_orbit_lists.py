#!/usr/bin/env python3
"""Verify actual-prime monomial centers with full message orbits and their saturation bound."""

import json
from itertools import combinations
from math import comb
from pathlib import Path

from probe_mu64_unit_lattice import PRIMES, require
from probe_quarter_coset_lists import evaluate, fiber_polynomial

LENGTH = 2**30
CERTIFICATE = Path(__file__).with_name("character_orbit_zero_sums.json")


def check_template(prime, generator, order, exponents):
    root = pow(generator, (prime - 1) // order, prime)
    require(pow(root, order // 2, prime) == prime - 1, "wrong order for zero-sum template")
    require(all(0 <= j < order for j in exponents), "exponent outside the quotient")
    require(len(exponents) % 2 == 1 and len({j % (order // 4) for j in exponents})
            == len(exponents), "template must have odd size and occupy distinct fourth-root cosets")
    values = [pow(root, j, prime) for j in exponents]
    require(sum(values) % prime == 0, "template sum is nonzero")
    imaginary = pow(root, order // 4, prime)
    doubled = values + [(imaginary * x) % prime for x in values]
    require(len(set(doubled)) == 2 * len(exponents), "quarter turn overlaps the template")
    require(sum(doubled) % prime == 0 and sum(x * x for x in doubled) % prime == 0,
            "first two power sums must vanish")
    return root


def check_padding(order, dimension, template_size, budget, gain=2):
    block = 2 * gain
    available = order // block - template_size
    degree = dimension + gain
    remaining = degree - gain * template_size
    require(remaining >= 0 and remaining % block == 0, "padding does not have integral size")
    groups = remaining // block
    require(0 <= groups <= available, "insufficient spare cosets")
    m = min(groups, available - groups)
    require(m >= 2, "padding family too small")
    # Every middle binomial coefficient dominates the coefficients up to its depth.
    # Using four instead of two also certifies the smaller quotient families.
    exponent = min(4, m)
    bound = comb(available, exponent)
    require(bound > budget, "padding bound does not exceed the designated budget")
    return bound


def polynomial_control():
    p, order, dimension = 257, 256, 16
    template = (0, 1, 224)
    root = check_template(p, 3, order, template)
    xs = [pow(root, j, p) for j in range(order)]
    used = {j % (order // 4) for j in template}
    spare = [j for j in range(order // 4) if j not in used]
    degree = dimension + 2
    count = (degree - 2 * len(template)) // 4
    for groups in (spare[:count], spare[-count:]):
        exponents = {*template, *((j + order // 4) % order for j in template)}
        exponents.update(j + u * (order // 4) for j in groups for u in range(4))
        locator = fiber_polynomial([xs[j] for j in exponents], p)
        message = [(-c) % p for c in locator[:dimension]]
        require(locator[dimension:] == [0, 0, 1], "high coefficients did not cancel")
        actual = {j for j, x in enumerate(xs) if evaluate(message, x, p) == pow(x, degree, p)}
        require(actual == exponents, "agreement set mismatch")
        rotations = {tuple(c * pow(x, (i - degree) % order, p) % p
                           for i, c in enumerate(message)) for x in xs}
        require(len(rotations) == order, "message has a short orbit")
    require(check_padding(order, dimension, len(template), 2 * order) > 2 * order,
            "small field full-orbit count")
    print("F257: checked all 256 sites and all 256 rotations for two degree-15 messages.")

    quotient, dimension = 64, 64
    first, third = (0, 3, 42), (0, 1, 103)
    require(sum(pow(root, j * (order // quotient), p) for j in first) % p == 0
            and sum(pow(root, 3 * j, p) for j in third) % p == 0, "small moment templates")
    products = {(u * (order // quotient) + v) % order for u in first for v in third}
    used = {j % (order // 8) for j in products}
    require(len(used) == len(first) * len(third), "product eighth-root cosets overlap")
    template = {(j + r * (order // 8)) % order for j in products for r in range(4)}
    require(all(sum(pow(root, j * r, p) for j in template) % p == 0 for r in range(1, 5)),
            "first four moments")
    gain, degree = 4, dimension + 4
    spare = [j for j in range(order // 8) if j not in used]
    groups = (degree - len(template)) // 8
    for chosen in (spare[:groups], spare[-groups:]):
        exponents = template | {j + r * (order // 8) for j in chosen for r in range(8)}
        locator = fiber_polynomial([xs[j] for j in exponents], p)
        require(locator[dimension:] == [0] * gain + [1], "four high coefficients")
        message = [(-c) % p for c in locator[:dimension]]
        actual = {j for j, x in enumerate(xs) if evaluate(message, x, p) == pow(x, degree, p)}
        rotations = {tuple(c * pow(x, (i - degree) % order, p) % p
                           for i, c in enumerate(message)) for x in xs}
        require(actual == exponents and len(rotations) == order, "full four-gain orbit")
    check_padding(order, dimension, len(used), 2 * order, gain=4)
    print("F257: also verified 68 agreements and full orbits for two degree-63 messages.")


def saturation_control():
    order = 16
    for p, generator in zip(PRIMES, (3, 37)):
        root = pow(generator, (p - 1) // order, p)
        powers = [[pow(root, i * j, p) for j in range(order)] for i in range(1, order)]
        for k in (1, 2, 4, 8):
            for degree in range(k + 1, order):
                count = 0
                for subset in combinations(range(order), degree):
                    if all(sum(row[j] for j in subset) % p == 0 for row in powers[:degree - k]):
                        count += 1
                predicted = order // degree if order % degree == 0 else 0
                require(count == predicted, "saturated monomial count on the control domain")
    print("Both named primes: exact saturated monomial counts checked exhaustively at order 16.")


def main():
    polynomial_control()
    saturation_control()
    cert = json.loads(CERTIFICATE.read_text())
    order = cert["order"]
    require(order == 65536 and [row["prime"] for row in cert["fields"]] == list(PRIMES),
            "wrong template order or named fields")
    for i, row in enumerate(cert["fields"]):
        p = row["prime"]
        def decode(values, size):
            return [j if j >= 0 else size // 2 - j for j in values]
        template = decode(row["first_moment"], order)
        other = decode(row["third_moment"], LENGTH)
        generator = (3, 37)[i]
        require(row["generator"] == generator and len(template) == len(other) == 2049,
                "unexpected production certificate")
        quotient_root = check_template(p, generator, order, template)
        root = pow(generator, (p - 1) // LENGTH, p)
        require(pow(root, LENGTH // 2, p) == p - 1
                and pow(root, LENGTH // order, p) == quotient_root, "production generator")
        require(len({j % (order // 8) for j in template}) == len(template)
                and len({j % (LENGTH // order) for j in other}) == len(other),
                "product sites do not occupy distinct eighth-root cosets")
        require(all(0 <= j < LENGTH for j in other)
                and sum(pow(root, 3 * j, p) for j in other) % p == 0,
                "third power sum in the production field")
        budget = LENGTH << i
        for denominator in (2, 4, 8, 16):
            dimension = LENGTH // denominator
            check_padding(LENGTH, dimension, len(template), budget)
            check_padding(LENGTH, dimension, len(template) * len(other), budget, gain=4)
            quotient = order * (2 if denominator == 16 else 1)
            check_padding(quotient, quotient // denominator, len(template), budget)
        log_lower = p.bit_length() - 1
        gain = 29 * LENGTH // (2 * log_lower) + 1
        require(2 * (gain - 1) * log_lower <= 29 * LENGTH < 2 * gain * log_lower,
                "incorrect saturation cutoff")
        require(gain == (98_539_598, 97_919_852)[i], "unexpected saturation gain")
        print(f"Named prime {i + 1}: certified both 2,049-site templates, full-orbit "
              f"over-budget lists at k+4 agreements at all four rates, and the "
              f"constant-only saturated window from gain {gain:,}.")


if __name__ == "__main__":
    main()

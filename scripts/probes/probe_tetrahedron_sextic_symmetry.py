"""Test dihedrally equivariant sextic quotient candidates in the second prime field."""

from collections import Counter
from itertools import combinations, product
from math import prod

from probe_many_head_locator_attack import require
from probe_smooth_four_head_attack import GENERATOR, PRIME


def representatives(kind):
    """One input per pair {x,-x} after conjugating the given involution."""
    root = pow(GENERATOR, 2**30//32, PRIME)
    if kind == "turn":
        return [pow(root, j, PRIME) for j in range(16)], False
    u = 1 if kind == "vertex" else pow(GENERATOR, 2**30//64, PRIME)
    nodes = [pow(root, j, PRIME) for j in range(32)]
    transformed = {(x-u)*pow((x+u) % PRIME, -1, PRIME) % PRIME for x in nodes
                   if (x+u) % PRIME}
    fixed = 0 in transformed
    reps = sorted(x for x in transformed if 0 < x < PRIME-x)
    require(2*len(reps) + 2*fixed == 32, "pair and fixed-point count")
    return reps, fixed


def lagrange_table(nodes, size):
    table = {}
    for indices in combinations(range(len(nodes)), size):
        weights = []
        for i in indices:
            coefficients = [1]
            denominator = 1
            for j in indices:
                if i == j:
                    continue
                t = nodes[j]
                coefficients = ([-t*coefficients[0] % PRIME] +
                                [(a-b*t) % PRIME for a, b in zip(coefficients, coefficients[1:])] +
                                [coefficients[-1]])
                denominator = denominator*(nodes[i]-t) % PRIME
            scale = pow(denominator, -1, PRIME)
            weights.append(tuple(v*scale % PRIME for v in coefficients))
        table[indices] = weights
    return table


def canonical_turn(indices):
    return min(tuple(sorted((sign*i+j) % 16 for i in indices))
               for j in range(16) for sign in (1, -1))


def scan(kind, fixed_zeros, expected_count, expected_profiles):
    xs, fixed = representatives(kind)
    require(not fixed_zeros or fixed, "both fixed points belong to the zero fiber")
    ys = tuple(x*x % PRIME for x in xs)
    size = 4 if fixed_zeros else 3
    pairs = 2 if fixed_zeros else 3
    table = lagrange_table(ys, size)
    profiles = Counter()
    checked = 0
    for zeros in combinations(range(len(xs)), pairs):
        if kind == "turn" and zeros != canonical_turn(zeros):
            continue
        zero_set = set(zeros)
        factors = [prod(y-ys[j] for j in zeros) % PRIME for y in ys]
        numerators = [(t*x if fixed_zeros else t*pow(x, -1, PRIME)) % PRIME
                      for t, x in zip(factors, xs)]
        seen = set()
        for indices, weights in table.items():
            if zero_set.intersection(indices):
                continue
            for tail in product((1, -1), repeat=size-1):
                signs = (1,) + tail
                q = tuple(sum(signs[i]*numerators[indices[i]]*weights[i][j] for i in range(size)) % PRIME
                          for j in range(size))
                if q in seen:
                    continue
                seen.add(q)
                checked += 1
                if fixed_zeros and (q[0] == 0 or q[-1] == 0):
                    continue
                # Horner evaluation of a quadratic or cubic in the squared coordinate.
                high = q[3] if fixed_zeros else 0
                den = [(q[0]+y*(q[1]+y*(q[2]+y*high))) % PRIME for y in ys]
                if any(den[i] == 0 for i in zeros):
                    continue
                at_one = sum(n == d or (n+d) % PRIME == 0
                             for i, (n, d) in enumerate(zip(numerators, den)) if i not in zero_set)
                if at_one < 5:
                    continue
                values = Counter()
                for n, d in zip(numerators, den):
                    if d == 0:
                        values[-1] += 2
                    else:
                        t = n*pow(d, -1, PRIME) % PRIME
                        values[t] += 1
                        values[-t % PRIME] += 1
                if fixed:
                    values[0 if fixed_zeros else -1] += 2
                profile = tuple(sorted(values.values(), reverse=True)[:5])
                require(sum(values.values()) == 32 and profile[3] < 5, "four largest fibers")
                profiles[profile] += 1
    require((checked, profiles) == (expected_count, expected_profiles), "complete interpolation census")
    print(f"{kind} fixed_zeros={fixed_zeros} candidate denominators={checked} profiles={dict(profiles)}")


def main():
    scan("turn", False, 23491, {})
    scan("edge", False, 640640, {})
    scan("vertex", False, 399767, {(6, 6, 6, 2, 2): 3})
    scan("vertex", True, 600149, {(6, 5, 5, 1, 1): 175, (6, 6, 6, 2, 2): 4})


if __name__ == "__main__":
    main()

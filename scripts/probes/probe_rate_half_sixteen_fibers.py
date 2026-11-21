"""Verify the first-prime rate-half MCA ceiling 19/64."""

from itertools import combinations
from math import prod

from probe_rate_half_eight_fibers import G, N, P, check_explicit_witnesses, require


ROOTS = ((0, 1, 2, 3, 4, 9, 11),
         (0, 3, 5, 10, 11, 12, 13),
         (1, 4, 5, 9, 12, 13, 14))
PARTITIONS = (
    ("012", "3"), ("013", "2"), ("01", "23"), ("012", "3"),
    ("013", "2"), ("023", "1"), ("0", "12", "3"), ("0", "123"),
    ("0", "123"), ("013", "2"), ("02", "13"), ("012", "3"),
    ("023", "1"), ("023", "1"), ("03", "1", "2"), ("0", "123"),
)


def check_cyclotomic_partitions():
    """Compute in Z[T]/(T^8+1), cross-multiplying each pair equality."""
    one = (1,) + (0,) * 7
    zero = (0,) * 8
    powers = [tuple((1 if k < 8 else -1) * int(j == k % 8) for j in range(8))
              for k in range(16)]

    def multiply(a, b):
        c = [0] * 8
        for i, u in enumerate(a):
            for j, v in enumerate(b):
                c[(i + j) % 8] += (1 if i + j < 8 else -1) * u * v
        return tuple(c)

    def product_at(roots, j):
        acc = one
        for r in roots:
            acc = multiply(acc, tuple(u - v for u, v in zip(powers[j], powers[r])))
        return acc

    a, b, c = [[product_at(roots, j) for j in range(16)] for roots in ROOTS]
    numerators = [[zero] * 16, a, [multiply(a[6], y) for y in b],
                  [multiply(a[7], y) for y in c]]
    denominators = [one, one, b[6], c[7]]
    for i, k in combinations(range(4), 2):
        equal = [j for j in range(16)
                 if multiply(numerators[i][j], denominators[k]) ==
                 multiply(numerators[k][j], denominators[i])]
        expected = [j for j, groups in enumerate(PARTITIONS)
                    if any(str(i) in group and str(k) in group for group in groups)]
        require(equal == expected and len(equal) == 7, "cyclotomic pair equality")


def quotient_values():
    omega = pow(G, N // 16, P)
    require(pow(omega, 8, P) == P - 1, "quotient generator order")
    ys = [pow(omega, j, P) for j in range(16)]
    a, b, c = [[prod(y - ys[r] for r in roots) % P for y in ys] for roots in ROOTS]
    c2, c3 = a[6] * pow(b[6], -1, P), a[7] * pow(c[7], -1, P)
    values = [[0] * 16, a, [c2 * t % P for t in b], [c3 * t % P for t in c]]
    for j, groups in enumerate(PARTITIONS):
        by_value = {}
        for i, row in enumerate(values):
            by_value[row[j]] = by_value.get(row[j], "") + str(i)
        require(set(by_value.values()) == set(groups), "modular fiber partition")
    return values


def check_triple_rigidity():
    """Compute the rank on the 24 coefficients of three normalized degree-seven heads."""
    omega = pow(G, N // 16, P)
    matrix = []
    for j, groups in enumerate(PARTITIONS):
        triple = next((group for group in groups if len(group) == 3), None)
        if triple is None:
            continue
        y = pow(omega, j, P)
        powers = [pow(y, d, P) for d in range(8)]
        first, *others = map(int, triple)
        for other in others:
            matrix.append([((int(i == first) - int(i == other)) * a) % P
                           for i in range(1, 4) for a in powers])
    rank = 0
    for col in range(24):
        pivot = next((i for i in range(rank, len(matrix)) if matrix[i][col]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        inv = pow(matrix[rank][col], -1, P)
        matrix[rank] = [v * inv % P for v in matrix[rank]]
        for i in range(rank + 1, len(matrix)):
            multiple = matrix[i][col]
            matrix[i] = [(v - multiple*w) % P for v,w in zip(matrix[i], matrix[rank])]
        rank += 1
    require(len(matrix) == 24 and rank == 23, "twelve triple constraints have nullity one")


def allocation(n):
    s, rem = divmod(n, 16)
    require(not rem and s >= 4 and s % 4 == 0, "supported lengths")
    rows = []
    for j, groups in enumerate(PARTITIONS):
        if j in (2, 10):
            slots = [(groups[0], s // 2), (groups[1], s // 2)]
        elif j == 6:
            slots = [("root", s // 4 - 1), ("12", s // 4 + 1), ("off", s // 2)]
        elif j == 14:
            slots = [("root", 3 * s // 4 - 1), ("03", s // 4 + 1)]
        else:
            slots = [(max(groups, key=len), s)]
        require(sum(t for _, t in slots) == s, "full fiber allocation")
        rows.append(slots)

    cores = [0] * 4
    roots = labels = 0
    for groups, slots in zip(PARTITIONS, rows):
        for action, count in slots:
            if action == "root":
                roots += count
                matched = "0123"
            elif action == "off":
                labels += count * len(groups)
                matched = ""
            else:
                require(action in groups, "normal slot matches one class")
                labels += count
                matched = action
            for digit in matched:
                cores[int(digit)] += count

    require(roots == s - 2 and roots + 7 * s + 1 < n // 2, "head degree budget")
    require(cores == [45 * s // 4 - 1] * 4 and min(cores) >= n // 2, "joint cores")
    errors = n - min(cores) - 1
    require(errors * 64 == 19 * n and labels == n + 2, "bad radius and label supply")
    # E + L - R <= 60s for every choice of slots of this partition type.
    slot_caps = [max([3, len(groups)] + [len(group) + 1 for group in groups])
                 for groups in PARTITIONS]
    require(sum(slot_caps) == 60, "integer optimality certificate")

    def slot(j, within):
        for action, count in rows[j]:
            if within < count:
                return action if action in ("root", "off") else tuple(map(int, action))
            within -= count
        raise AssertionError("fiber index out of range")

    return slot, cores, errors, labels


def main():
    check_cyclotomic_partitions()
    values = quotient_values()
    check_triple_rigidity()
    _, cores, errors, labels = allocation(N)
    require(P // 2**128 == N and 6 * N**2 < P, "production field size checks")
    require(errors == 318767104 and labels == 1073741826, "production counts")
    print(f"production n={N} errors={errors} joint_cores={cores} bad_labels={labels}")
    for n in (64, 128, 256):
        slot, cores, errors, labels = allocation(n)
        check_explicit_witnesses(n, values, slot, cores, errors, labels)


if __name__ == "__main__":
    main()

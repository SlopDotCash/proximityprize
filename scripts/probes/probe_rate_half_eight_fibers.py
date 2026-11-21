"""Check the four-pencil MCA construction at the first rate-half prime.

The production check uses counts on eight fibers and exact modular arithmetic.
Checks at smaller lengths construct the received words and every bad-scalar
witness explicitly. No external packages are required.
"""

from collections import defaultdict
from math import prod


P = 365375409332725729550921208179070755120141565953
G = 303645430271030343624574566109998498685964493478
N = 2**30
POWER_ROOTS = ((3, 6, 7), (3, 5, 7), (4, 5, 6))
PARTITIONS = (
    ((0,), (1,), (2, 3)), ((0,), (2,), (1, 3)),
    ((0,), (1, 2, 3)), ((0, 1, 2), (3,)),
    ((1,), (2,), (0, 3)), ((1,), (0, 2, 3)),
    ((2,), (0, 1, 3)), ((0, 1, 2), (3,)),
)
NORMAL = ((2, 3), (1, 3), (1, 2, 3), (0, 1, 2),
          (0, 3), (0, 2, 3), (0, 1, 3), (0, 1, 2))


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def check_cyclotomic_identities():
    """Check the two extra pair equalities in Z[T]/(T^4+1)."""
    def multiply(a, b):
        c = [0] * 4
        for i, u in enumerate(a):
            for j, v in enumerate(b):
                c[(i + j) % 4] += (1 if i + j < 4 else -1) * u * v
        return tuple(c)

    powers = [tuple((1 if j < 4 else -1) * int(i == j % 4) for i in range(4))
              for j in range(8)]

    def numerator(row, j):
        acc = powers[0]
        for r in POWER_ROOTS[row - 1]:
            acc = multiply(acc, tuple(a - b for a, b in zip(powers[j], powers[r])))
        return acc

    for i, k, j in [(1, 3, 1), (2, 3, 0)]:
        require(multiply(numerator(i, j), numerator(k, 2)) ==
                multiply(numerator(k, j), numerator(i, 2)), "cyclotomic identity")


def cubic_values():
    omega = pow(G, N // 8, P)
    require(pow(omega, 4, P) == P - 1, "quotient generator order")
    ys = [pow(omega, j, P) for j in range(8)]
    values = [[0] * 8]
    for roots in POWER_ROOTS:
        row = [prod(y - ys[r] for r in roots) % P for y in ys]
        inverse = pow(row[2], -1, P)
        values.append([t * inverse % P for t in row])
    for j, partition in enumerate(PARTITIONS):
        classes = defaultdict(list)
        for i, row in enumerate(values):
            classes[row[j]].append(i)
        require(set(map(tuple, classes.values())) == set(partition), "fiber partition")
    return values


def counts(n):
    s, rem = divmod(n, 8)
    require(not rem and s >= 4 and s % 2 == 0, "supported lengths")
    roots = [s // 2 - 1, s // 2 - 1, 0, 0, 0, 0, 0, 0]
    offline = [0, 0, 0, 0, s // 2, 0, 0, 0]
    normal = [s - r - o for r, o in zip(roots, offline)]
    cores = [sum(roots) + sum(t for t, group in zip(normal, NORMAL) if i in group)
             for i in range(4)]
    labels = sum(normal) + sum(o * len(part) for o, part in zip(offline, PARTITIONS))
    require(sum(roots) + 3 * s + 1 < n // 2 <= min(cores), "polynomial degrees and uniqueness")
    require(cores == [11 * s // 2 - i for i in (2, 1, 1, 0)], "individual core sizes")
    require(labels == n + 2, "distinct label supply")
    errors = n - min(cores) - 1
    require(errors == 5 * s // 2 + 1, "bad Hamming error count")
    return s, roots, offline, cores, errors, labels


def check_allocation_upper_bound():
    # Slot triples are (coverage of the first three cores, label supply,
    # root usage). Checking all slots proves 2E + L - 3R <= 38s.
    fiber_bounds = []
    for classes in PARTITIONS:
        slots = [(len(set(group) & {0, 1, 2}), 1, 0) for group in classes]
        slots += [(0, len(classes), 0), (3, 0, 1)]
        fiber_bounds.append(max(2 * e + l - 3 * r for e, l, r in slots))
    require(fiber_bounds == [3, 3, 5, 7, 3, 5, 5, 7], "allocation inequalities")
    require(sum(fiber_bounds) == 38, "total allocation bound")


def check_small(n, cubics):
    _, root_counts, offline_counts, expected_cores, errors, labels = counts(n)

    def slot(j, within):
        if within < root_counts[j]:
            return "root"
        if within < root_counts[j] + offline_counts[j]:
            return "off"
        return NORMAL[j]

    check_explicit_witnesses(n, cubics, slot, expected_cores, errors, labels)


def check_explicit_witnesses(n, quotient_values, slot, expected_cores, errors, labels):
    """Expand a four-head fiber allocation and check each assigned witness."""
    m = len(quotient_values[0])
    g = pow(G, N // n, P)
    require(pow(g, n, P) == 1 and pow(g, n // 2, P) == P - 1, "subgroup order")
    xs = [pow(g, i, P) for i in range(n)]
    slots = [slot(i % m, i // m) for i in range(n)]
    roots = [x for x, action in zip(xs, slots) if action == "root"]
    h = [prod((x - z) % P for z in roots) % P for x in xs]
    heads = []
    for row in quotient_values:
        vertical = [value * row[i % m] % P for i, value in enumerate(h)]
        heads.append([(x * v % P, v) for x, v in zip(xs, vertical)])
    center = [None] * n
    witnesses = {}
    pending = []
    for i, x in enumerate(xs):
        action = slots[i]
        if action == "root":
            center[i] = (0, 0)
        elif action == "off":
            pending.append(i)
        else:
            center[i] = heads[action[0]][i]
            other = next(k for k in range(4) if k not in action)
            witnesses[-x % P] = (other, i)

    for i in pending:
        x = xs[i]
        by_value = {word[i][1]: k for k, word in enumerate(heads)}
        u1 = next(t for t in range(5) if t not in by_value)
        for u0 in range(3 * len(witnesses) + 2):
            if u0 == x * u1 % P:
                continue
            fresh = {(x * v - u0) * pow(u1 - v, -1, P) % P: (k, i)
                     for v, k in by_value.items()}
            if len(fresh) == len(by_value) and fresh.keys().isdisjoint(witnesses):
                witnesses.update(fresh)
                center[i] = (u0, u1)
                break
        require(center[i] is not None, "greedy offline labels")

    cores = [{i for i, (r, w) in enumerate(zip(center, head)) if r == w} for head in heads]
    require(list(map(len, cores)) == expected_cores, "computed joint cores")
    for gamma, (k, i) in witnesses.items():
        require(i not in cores[k], "fresh coordinate")
        require(len(cores[k]) >= n // 2 and len(cores[k]) + 1 >= n - errors,
                "uniqueness on the core and witness cardinality")
        for a in cores[k] | {i}:
            u0, u1 = center[a]
            v0, v1 = heads[k][a]
            require((u0 - v0 + gamma * (u1 - v1)) % P == 0, "mixed agreement")
    require(len(witnesses) == labels, "computed bad scalars")
    print(f"explicit n={n} errors={errors} joint_cores={list(map(len, cores))} bad_labels={labels}")


def main():
    check_cyclotomic_identities()
    cubics = cubic_values()
    check_allocation_upper_bound()
    s, _, _, cores, errors, labels = counts(N)
    require(pow(G, N, P) == 1 and pow(G, N // 2, P) == P - 1, "first-field domain")
    require(P // 2**128 == N and 3 * (N + 2) + 1 < P, "security and label budgets")
    require(errors == 335544321 and labels == 1073741826, "production endpoint")
    require(3 * (11 * s // 2 - 1) > (33 * s - 7) // 2, "integer optimality")
    print(f"production n={N} errors={errors} joint_cores={cores} bad_labels={labels}")
    for n in (32, 64, 256):
        check_small(n, cubics)


if __name__ == "__main__":
    main()

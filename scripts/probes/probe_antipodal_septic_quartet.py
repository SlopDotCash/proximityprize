#!/usr/bin/env python3
"""Count the possible antipodal quadratic factors in a degree-seven quartet on μ32."""

from itertools import combinations

from probe_many_head_locator_attack import require


def main():
    p = 65537
    w = pow(3, (p-1)//32, p)
    roots = [pow(w, j, p) for j in range(32)]
    require(roots[16] == p-1, "primitive 32nd root")
    # For a root of A in class j compute its contribution to A(t)/A(-t).
    # An occupied class is never evaluated.
    ratios = [[(t-x)*pow(-t-x, -1, p) % p if (-t-x) % p else 0
               for t in roots[:16]] for x in roots]
    must_c = [0]+[(-t-1)*pow(t-1, -1, p) % p for t in roots[1:16]]
    must_d = [0]+[(-t+1)*pow(t+1, -1, p) % p for t in roots[1:16]]
    total = maximum = 0
    for selected in combinations(range(1, 16), 7):
        free = [t for t in range(1, 16) if t not in selected]
        # Every stage makes both sign choices for one antipodal class.
        tables = [[1]*len(free)]
        for j in selected:
            next_tables = []
            for root in (j, j+16):
                factors = [ratios[root][t] for t in free]
                for values in tables:
                    next_tables.append([(v*a) % p for v, a in zip(values, factors)])
            tables = next_tables
        for table in tables:
            hits = sum(v in (must_c[t], must_d[t]) for t, v in zip(free, table))
            maximum = max(maximum, hits)
        total += len(tables)
    require(total == 823680 and maximum == 2, "antipodal degree-seven census")
    print(f"{total} choices for A; at most {maximum} eligible antipodal pairs; six required")


if __name__ == "__main__":
    main()

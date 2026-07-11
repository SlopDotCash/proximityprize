#!/usr/bin/env python3
"""
Probe for #466 G168: a scaling of multiplicative order d that fixes a minimal
zero-sum support confines the support to a single coset x*<g>, so |S| = d.

This is the general order-d ladder statement of which G167 (negation, d=2) is the
d=2 instance. It reproduces the two mechanism facts the Lean file encodes:

  (1) geometric-sum vanishing: for g of order d > 1 in F_p^*, sum_{i<d} g^i = 0,
      hence any coset x*<g> is itself a zero-sum set;
  (2) coset confinement: a *minimal* zero-sum support S fixed by scaling by g
      equals exactly one coset x*<g>, so |S| = d = ord(g).

We enumerate small primes, all elements g, and check both facts by brute force,
and confirm the ladder consequence: every minimal zero-sum support fixed by an
order-d scaling has size exactly d.

Exit non-zero on any violation.
"""
import sys
from itertools import combinations


def order(g, p):
    x = g % p
    if x == 0:
        return 0
    o = 1
    cur = x
    while cur != 1:
        cur = (cur * x) % p
        o += 1
    return o


def coset(x, g, p):
    """The multiplicative coset x*<g> as a frozenset of residues."""
    elems = set()
    cur = x % p
    while cur not in elems:
        elems.add(cur)
        cur = (cur * g) % p
    return frozenset(elems)


def is_zero_sum(S, p):
    return len(S) > 0 and 0 not in S and (sum(S) % p == 0)


def minimal_zero_sum_supports(p, max_size):
    """All minimal zero-sum supports of F_p (nonzero elements) up to max_size."""
    nz = list(range(1, p))
    out = []
    for s in range(1, max_size + 1):
        for comb in combinations(nz, s):
            S = set(comb)
            if sum(S) % p != 0:
                continue
            # minimality: no proper nonempty subset is zero-sum
            minimal = True
            for t in range(1, s):
                broke = False
                for sub in combinations(comb, t):
                    if sum(sub) % p == 0:
                        minimal = False
                        broke = True
                        break
                if broke:
                    break
            if minimal:
                out.append(frozenset(S))
    return out


def main():
    # (prime, max support size for the exhaustive minimal-support enumeration).
    # Larger primes use a smaller size cap to keep the brute force tractable; the
    # geometric-vanishing / coset checks run over ALL elements regardless.
    cells = [(7, 6), (11, 6), (13, 5), (17, 5), (41, 4), (97, 3)]
    fails = 0
    checked_geom = 0
    checked_confine = 0

    for p, max_size in cells:
        # (1) geometric-sum vanishing for every g of order d > 1
        for g in range(2, p):
            d = order(g, p)
            if d <= 1:
                continue
            s = 0
            cur = 1
            for _ in range(d):
                s = (s + cur) % p
                cur = (cur * g) % p
            checked_geom += 1
            if s != 0:
                print(f"FAIL geom: p={p} g={g} ord={d} sum_powers={s} != 0")
                fails += 1
            # each coset x*<g> must be zero-sum
            for x in range(1, p):
                C = coset(x, g, p)
                if len(C) != d:
                    print(f"FAIL cosetsize: p={p} g={g} x={x} |coset|={len(C)} != {d}")
                    fails += 1
                if not is_zero_sum(C, p):
                    print(f"FAIL cosetzs: p={p} g={g} x={x} coset not zero-sum")
                    fails += 1

        # (2) ladder consequence: every minimal zero-sum support fixed by an
        #     order-d scaling has |S| = d, and is a single coset.
        supports = minimal_zero_sum_supports(p, max_size)
        for S in supports:
            for g in range(2, p):
                d = order(g, p)
                if d <= 1:
                    continue
                # is S fixed by scaling by g?  (g*S == S as sets)
                gS = frozenset((g * y) % p for y in S)
                if gS != S:
                    continue
                checked_confine += 1
                # confinement: |S| must equal d, and S must be one coset
                if len(S) != d:
                    print(f"FAIL confine-card: p={p} g={g} ord={d} S={sorted(S)} |S|={len(S)} != {d}")
                    fails += 1
                x0 = next(iter(S))
                if coset(x0, g, p) != S:
                    print(f"FAIL confine-coset: p={p} g={g} S={sorted(S)} not a single coset")
                    fails += 1

    print(f"checked geom-vanishing cells: {checked_geom}")
    print(f"checked fixed-support confinement cells: {checked_confine}")
    if fails:
        print(f"RESULT: FAIL ({fails} violations)")
        sys.exit(1)
    print("RESULT: PASS — order-d scaling fixing a minimal zero-sum support forces |S| = ord(g); every fixed support is a single coset x*<g>.")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""#466 R314: summarize the c=3 template-family multiplicity law.

R313 exposes normalized collision templates for the dangerous `g^h = 3`
depth-3 relation web.  This probe compresses those templates to the data that a
formal enumeration theorem has to explain:

* template count and occurrence count in each signature stratum;
* occurrence-count distribution;
* the derived large/middle/small closed-form checks.

The output is deliberately small enough to keep as a KB-facing certificate.
"""

from __future__ import annotations

from collections import Counter, defaultdict

from probe_r313_c3_template_sampler import base_index, build_n3, order_n_element, shift_vec, sparse


CASES = (
    (32, 21523361),
    (64, 926510094425921),
    (128, 1716841910146256242328924544641),
)


def template_counter(n: int, p: int):
    keys, cnts = build_n3(n)
    g0 = order_n_element(p, n)
    powers = []
    x = 1
    for _ in range(n // 2):
        powers.append(x)
        x = (x * g0) % p

    groups: dict[int, list[tuple[int, int, dict[int, int]]]] = defaultdict(list)
    for idx, (row, cnt) in enumerate(zip(keys, cnts)):
        value = 0
        for j in row.nonzero()[0]:
            value += int(row[j]) * powers[int(j)]
        groups[value % p].append((idx, int(cnt), sparse(row)))

    out: dict[tuple[tuple[int, ...], int], Counter] = defaultdict(Counter)
    for fiber in groups.values():
        counts = [cnt for _, cnt, _ in fiber]
        if len(counts) <= 1:
            continue
        total = sum(counts)
        delta = total * total - sum(cnt * cnt for cnt in counts)
        if delta == 0:
            continue
        signature = tuple(sorted(counts, reverse=True))
        base = base_index(fiber)
        template = tuple(
            sorted([(cnt, shift_vec(vec, base, n)) for _, cnt, vec in fiber], reverse=True)
        )
        out[(signature, delta)][template] += 1
    return out


def signed_log_abs3(n: int, p: int) -> tuple[int, int]:
    g0 = order_n_element(p, n)
    x = 1
    for j in range(n // 2):
        if x == 3 % p:
            return (j, 1)
        if x == (-3) % p:
            return (j, -1)
        x = (x * g0) % p
    raise ValueError(f"±3 is not in the signed half basis for n={n}, p={p}")


def main() -> int:
    print("# R314 c=3 template-family multiplicity law")
    for n, p in CASES:
        h, h_sign = signed_log_abs3(n, p)
        m = n // 2
        counters = template_counter(n, p)
        print(f"\nn={n} p={p} m={m} abs3_offset={h} abs3_sign={h_sign} inv3_offset={m - h}")
        for (signature, delta), counter in sorted(counters.items(), key=lambda item: -item[0][1]):
            templates = len(counter)
            occurrences = sum(counter.values())
            dist = " ".join(f"{k}:{v}" for k, v in sorted(Counter(counter.values()).items()))
            print(
                f"  signature={signature} delta={delta} "
                f"templates={templates} occurrences={occurrences} dist={dist}"
            )

        large_ok = counters[((3 * n - 3, 3, 1), 24 * n - 18)]
        middle_ok = counters[((6, 3, 3), 90)]
        small_ok = counters[((6, 3), 36)]
        print(
            "  checks:"
            f" large_templates={len(large_ok)} large_occ={sum(large_ok.values())} expected={n};"
            f" middle_templates={len(middle_ok)} middle_occ={sum(middle_ok.values())} expected={2 * n};"
            f" small_templates={len(small_ok)} expected={6 * (n - 7)}"
            f" small_occ={sum(small_ok.values())} expected={n * (n - 7)}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

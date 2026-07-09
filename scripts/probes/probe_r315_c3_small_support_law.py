#!/usr/bin/env python3
"""#466 R315: support-pattern law for the small c=3 templates.

R314 left the `(6,3)` small class as the only nontrivial template-family
multiplicity law.  This probe forgets coefficient signs and counts only support
patterns.  In the checked dangerous c=3 samples, the small class has

* `3m - 9` support patterns, where `m = n/2`;
* three boundary support patterns lifting to two signed templates each;
* every other support pattern lifting to four signed templates.

Hence the number of signed templates is

    4 * ((3m - 9) - 3) + 2 * 3 = 12m - 42 = 6(n - 7).

This is the structural count missing from R314's small-family theorem.
"""

from __future__ import annotations

from collections import Counter

from probe_r314_c3_template_family_law import CASES, signed_log_abs3, template_counter


def support_pattern(template):
    return tuple(tuple(i for i, _ in vec) for _cnt, vec in template)


def main() -> int:
    print("# R315 c=3 small-template support-pattern law")
    for n, p in CASES:
        h, h_sign = signed_log_abs3(n, p)
        m = n // 2
        k = m - h
        two_h = (2 * h) % m
        counter = template_counter(n, p)[((6, 3), 36)]
        supports = Counter(support_pattern(template) for template in counter)
        lift_dist = Counter(supports.values())
        boundary = sorted(pattern for pattern, lifts in supports.items() if lifts == 2)
        print(f"\nn={n} p={p} m={m} abs3_offset={h} abs3_sign={h_sign} inv3_offset={k} two_h={two_h}")
        print(
            f"  signed_templates={len(counter)} expected={6 * (n - 7)} "
            f"support_patterns={len(supports)} expected={3 * m - 9}"
        )
        print(
            "  lift_distribution="
            + " ".join(f"{lifts}:{count}" for lifts, count in sorted(lift_dist.items()))
        )
        for pattern in boundary:
            print(f"  boundary_lift2={pattern}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""#466 R316: parametric families for the small c=3 support patterns.

R315 counted small `(6,3)` support patterns.  R316 classifies them into three
explicit one-parameter families.  Write `n = 2m`, let `h` be the signed half-basis
offset for `±3`, and set `k = m - h`.

The observed families are:

* H(t): `((0,t,h), (0,t))`, with `t notin {h,k}`;
* K(t): `((0,t,k), (t,k))`, with `t notin {k,h+1}`;
* D(t): `((0,t,t+h mod m), (0,t))`, with `t notin {h,k}`.

Each family has `m - 3` parameters, for a total of `3m - 9` support patterns.
"""

from __future__ import annotations

from collections import Counter

from probe_r314_c3_template_family_law import CASES, signed_log_abs3, template_counter


def support_pattern(template):
    return tuple(tuple(i for i, _ in vec) for _cnt, vec in template)


def classify(pattern, m: int, h: int):
    k = m - h
    a, b = pattern
    if len(a) != 3 or len(b) != 2 or a[0] != 0:
        return None
    x, y = a[1], a[2]
    if h in a and b[0] == 0:
        other = x if y == h else y if x == h else None
        if other is not None and b == (0, other):
            return ("H", other)
    if k in a:
        other = x if y == k else y if x == k else None
        if other is not None and b == tuple(sorted((other, k))):
            return ("K", other)
    if b[0] == 0:
        t = b[1]
        if set(a) == {0, t, (t + h) % m}:
            return ("D", t)
    return None


def main() -> int:
    print("# R316 c=3 small-support parametric families")
    for n, p in CASES:
        h, h_sign = signed_log_abs3(n, p)
        m = n // 2
        k = m - h
        supports = {support_pattern(template) for template in template_counter(n, p)[((6, 3), 36)]}
        buckets: dict[str, list[int]] = {"H": [], "K": [], "D": []}
        unknown = []
        for pattern in supports:
            cls = classify(pattern, m, h)
            if cls is None:
                unknown.append(pattern)
            else:
                family, parameter = cls
                buckets[family].append(parameter)

        print(f"\nn={n} p={p} m={m} abs3_offset={h} abs3_sign={h_sign} inv3_offset={k}")
        print(f"  support_patterns={len(supports)} expected={3 * m - 9} unknown={len(unknown)}")
        for family in ("H", "K", "D"):
            params = sorted(buckets[family])
            missing = [t for t in range(1, m) if t not in params]
            duplicate_count = len(params) - len(set(params))
            print(
                f"  family={family} count={len(params)} expected={m - 3} "
                f"missing={missing} duplicates={duplicate_count}"
            )
        if unknown:
            for pattern in sorted(unknown):
                print(f"  unknown={pattern}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

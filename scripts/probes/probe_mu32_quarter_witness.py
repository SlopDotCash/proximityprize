#!/usr/bin/env python3
"""Four degree-seven words with sixteen agreements on every smooth length-32 domain."""
from probe_mu32_four_cubics import ZERO, multiply, root, subtract, value

# The cubics in X^2 have the following root exponents relative to z^2.
SUPPORTS = ((0, 1, 2), (0, 3, 11), (0, 10, 13))
# Each key is a base fiber exponent modulo 16. A digit denotes an agreeing head.
PAIR_CLASSES = ("0123", "01", "01", "02", "12", "12", "", "",
                "13", "23", "03", "02", "23", "03", "13", "")


def verify():
    a, b, c = [tuple(2 * j for j in roots) for roots in SUPPORTS]
    # Scale the second nonzero cubic to tie the first at 4, the third at 8.
    common = multiply(value(b, 8), value(c, 16))
    scales = (common, multiply(value(a, 8), value(c, 16)),
              multiply(value(a, 16), value(b, 8)))
    heads = []
    tags = []
    for j in range(32):
        locator = subtract(root(j), root(17))
        row = [ZERO] + [multiply(locator, multiply(scale, value(roots, 2 * (j % 16))))
                        for roots, scale in zip((a, b, c), scales)]
        heads.append(row)
        tags.append("0123" if j == 17 else PAIR_CLASSES[j % 16])

    counts = [0] * 4
    free = []
    for j, tag in enumerate(tags):
        if not tag:
            free.append(j)
            continue
        indices = [int(h) for h in tag]
        if any(heads[j][h] != heads[j][indices[0]] for h in indices):
            raise ValueError(f"invalid integral coincidence at exponent {j}")
        for h in indices:
            counts[h] += 1
    deficits = [max(0, 16 - c) for c in counts]
    if sum(deficits) > len(free):
        raise ValueError(f"too few free sites for {deficits}")
    print(f"Secured agreements {counts}, free exponents {free}, deficits {deficits}")
    print("All listed equalities hold in Z[z]/(z^16+1).")


if __name__ == "__main__":
    verify()

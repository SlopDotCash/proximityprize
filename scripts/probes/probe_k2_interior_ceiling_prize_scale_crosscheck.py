#!/usr/bin/env python3
"""
Cross-check for G310: KKH26 r=3 (k=2) interior-ceiling counts at a prize-scale prime.

Uses a different algorithm from the main probe:
* main probe: collinearity determinant / slope-matching on triples;
* this probe: direct 2x2 elimination on three distinct positions, then count the
  full agreement set M and explicitly check the `pairJointAgreesOn` clause
  (u0 and u1 both affine on M).

Both start from the same `mcaEventNat` definition:
  gamma is bad  <=>  there exists a witness set S with |S| >= t,
                     an affine codeword w agreeing with u0 + gamma*u1 on S,
                     and NO pair of affine codewords agreeing with u0 and u1 on S.

The prime, generator, and exact expected integers are the same as the main probe:
  p = 21 * 2^128 + 1 (Proth witness a = 5),  omega = 5^((p-1)/8).
  ceiling (x^3, x^2) at t = 3  ->  40
  below-ceiling max over monomial pencils at t = 4  ->  9 at (a,b) = (4,3).
"""
import itertools
import sys

OUT_PATH = "scripts/probes/_out_k2_interior_prize_scale_crosscheck.txt"


def fail(msg):
    print("FAIL:", msg)
    sys.exit(1)


p = 21 * (2 ** 128) + 1

# Proth certificate
def is_proth_prime():
    return (21 % 2 == 1 and 21 < 2 ** 128 and
            pow(5, (p - 1) // 2, p) == p - 1)

if not is_proth_prime():
    fail("Proth primality certificate failed")

omega = pow(5, (p - 1) // 8, p)
if omega == 1 or pow(omega, 4, p) != p - 1:
    fail("omega is not order-8")

mu = [pow(omega, i, p) for i in range(8)]
n = len(mu)


def inv(x):
    return pow(x, -1, p)


def is_affine_on_subset(vals, idxs):
    """Return (True, c0, c1) if vals[idx] = c0 + c1*x[idx] for all idx in idxs; else (False, None, None)."""
    if len(idxs) < 2:
        return True, 0, 0
    i0, i1 = idxs[0], idxs[1]
    x0, x1 = mu[i0], mu[i1]
    y0, y1 = vals[i0], vals[i1]
    if x0 == x1:
        return False, None, None
    c1 = (y1 - y0) * inv(x1 - x0) % p
    c0 = (y0 - c1 * x0) % p
    for idx in idxs[2:]:
        if (c0 + c1 * mu[idx]) % p != vals[idx] % p:
            return False, None, None
    return True, c0, c1


def bad_scalars_mcaEventNat(a, b, threshold):
    """
    Implement mcaEventNat exactly.  A 3-subset of distinct domain points gives a
    linear system in (c0, c1, gamma).  If u1 is not affine on the 3-subset, the
    system has a unique solution.  We then count the full agreement set M of that
    affine line with u0 + gamma*u1; if |M| >= threshold and (u0,u1) is not a joint
    affine pair on M, gamma is bad.
    """
    bad = set()
    u0 = [pow(x, a, p) for x in mu]
    u1 = [pow(x, b, p) for x in mu]
    for i, j, k in itertools.combinations(range(n), 3):
        # If u1 is affine on the triple, any affine line u0+gamma*u1 being affine
        # on the triple would force u0 to also be affine there; the mcaEvent
        # joint-pair clause kills the whole family, so we skip.
        affine_u1, _, _ = is_affine_on_subset(u1, (i, j, k))
        if affine_u1:
            continue

        xi, xj, xk = mu[i], mu[j], mu[k]
        yi, yj, yk = u0[i], u0[j], u0[k]
        ui, uj, uk = u1[i], u1[j], u1[k]

        # Eliminate c0:  c1*(x_j - x_i) - gamma*(u_j - u_i) = y_j - y_i
        #                 c1*(x_k - x_i) - gamma*(u_k - u_i) = y_k - y_i
        a11 = (xj - xi) % p
        a12 = (-(uj - ui)) % p
        a21 = (xk - xi) % p
        a22 = (-(uk - ui)) % p
        b1 = (yj - yi) % p
        b2 = (yk - yi) % p

        det = (a11 * a22 - a12 * a21) % p
        if det == 0:
            continue  # should not happen when u1 is non-affine on the triple

        c1 = (b1 * a22 - a12 * b2) * inv(det) % p
        gamma = (a11 * b2 - b1 * a21) * inv(det) % p
        c0 = (yi + gamma * ui - c1 * xi) % p

        # Count agreement set M
        match_idxs = []
        for idx in range(n):
            if (c0 + c1 * mu[idx]) % p == (u0[idx] + gamma * u1[idx]) % p:
                match_idxs.append(idx)
        if len(match_idxs) < threshold:
            continue

        # pairJointAgreesOn C M u0 u1 : are there codewords v0,v1 with v0|_M=u0|_M, v1|_M=u1|_M?
        # This is exactly: u0 is affine on M and u1 is affine on M.
        u0_affine, _, _ = is_affine_on_subset(u0, match_idxs)
        u1_affine, _, _ = is_affine_on_subset(u1, match_idxs)
        if u0_affine and u1_affine:
            continue

        bad.add(gamma)
    return bad


def main():
    lines = []
    lines.append(f"crosscheck p = 21 * 2^128 + 1 = {p}")

    ceiling = bad_scalars_mcaEventNat(3, 2, 3)
    if len(ceiling) != 40:
        fail(f"ceiling (x^3,x^2) t=3: expected 40, got {len(ceiling)}")
    lines.append(f"[1] ceiling (x^3,x^2) t=3 #bad = {len(ceiling)} (expected 40)")

    max_bad = 0
    best_pair = None
    for a in range(8):
        for b in range(8):
            bad = bad_scalars_mcaEventNat(a, b, 4)
            if len(bad) > max_bad:
                max_bad = len(bad)
                best_pair = (a, b)
    if max_bad != 9:
        fail(f"below-ceiling max at t=4: expected 9, got {max_bad}")
    if best_pair != (4, 3):
        fail(f"below-ceiling max pair: expected (4,3), got {best_pair}")
    lines.append(f"[2] below-ceiling t=4 max #bad = {max_bad} at (a,b) = {best_pair} (expected 9)")
    lines.append("[3] crosscheck agrees with main probe; integers q-independent at prize scale.")

    summary = "\n".join(lines)
    print(summary)
    with open(OUT_PATH, "w") as f:
        f.write(summary + "\n")
    print(f"Wrote durable output to {OUT_PATH}")
    print("CROSSCHECK PASS.")


if __name__ == "__main__":
    main()

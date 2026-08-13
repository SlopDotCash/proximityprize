#!/usr/bin/env python3
"""
G310 probe: KKH26 r=3 (k=2) interior-ceiling counts at a prize-scale prime.

Extends sweep A07 / docs/kb/deltastar-sweep-A07-k2-interior-2026-06-14.md from the
small primes 257 / 12289 / 65537 to a prize-scale Proth prime

    p = 21 * 2^128 + 1

with explicit primality certificate (Proth witness a = 5).  The smooth domain is
mu_8 = <omega> with omega = 5^((p-1)/8) (order 8, omega^4 = -1).

The dimension-two code (rate 1/4, k=2, n=8) has two exact integers of interest:

- Ceiling stack (u0, u1) = (x^3, x^2) at threshold t = 3:
  #bad scalars = 40 (= KKH26 TwoPowerSubsetSumSpectrum N(3,3)).

- Below-ceiling maximum over all 64 monomial pencils (x^a, x^b), a,b in [0,7),
  at threshold t = 4:  #bad scalars = 9 (attained at (a,b) = (4,3)).

Both integers are exactly the same as those measured by A07 at the small primes,
confirming q-independence of the A07/KKH26 r=3 pin at prize field scale.

Pure integer arithmetic, stdlib only, no third-party imports, no float in any
load-bearing value.  Hard SystemExit(1) on any check failure.
"""
import sys

OUT_PATH = "scripts/probes/_out_k2_interior_prize_scale.txt"


def fail(msg):
    print("FAIL:", msg)
    sys.exit(1)


# --- exact prize-scale prime (Proth certificate) ---
K = 21
EXP = 128
p = K * (2 ** EXP) + 1

# Proth's theorem: for p = k*2^n+1 with k odd and k < 2^n, if a^((p-1)/2) == -1 (mod p)
# then p is prime.  Here k=21, n=128; a=5 is a Proth witness.
if not (K % 2 == 1 and K < 2 ** EXP):
    fail("Proth shape failed")
if pow(5, (p - 1) // 2, p) != p - 1:
    fail("Proth certificate failed")

# order-8 generator: 5^((p-1)/8) mod p
omega = pow(5, (p - 1) // 8, p)
if omega == 1 or pow(omega, 4, p) != p - 1:
    fail("omega is not an order-8 element")

# smooth domain mu_8 = {omega^i : i = 0..7}
mu = [pow(omega, i, p) for i in range(8)]
n = len(mu)


def D(m, i, j):
    """(x_j^m - x_i^m) / (x_j - x_i) over F_p."""
    num = (pow(mu[j], m, p) - pow(mu[i], m, p)) % p
    den = (mu[j] - mu[i]) % p
    return (num * pow(den, -1, p)) % p


def bad_scalars(a, b, threshold):
    """
    For the monomial pencil u0_i = x_i^a, u1_i = x_i^b, return the set of
    scalars gamma such that u0 + gamma*u1 agrees with some affine codeword
    (degree < 2) on at least `threshold` positions.

    Uses triples: any three distinct positions determine a unique candidate
    (c0, c1, gamma); we then count how many of the eight positions the line
    c0 + c1*x matches u0 + gamma*u1.
    """
    bad = set()
    u0 = [pow(x, a, p) for x in mu]
    u1 = [pow(x, b, p) for x in mu]
    for i in range(n):
        for j in range(n):
            if j == i:
                continue
            for k in range(n):
                if k in (i, j):
                    continue
                dx_ij = (mu[j] - mu[i]) % p
                dx_jk = (mu[k] - mu[j]) % p
                if dx_ij == 0 or dx_jk == 0:
                    continue
                den = (D(b, i, j) - D(b, j, k)) % p
                if den == 0:
                    continue
                g = (D(a, j, k) - D(a, i, j)) % p
                gamma = (g * pow(den, -1, p)) % p
                c1 = ((u0[j] + gamma * u1[j] - u0[i] - gamma * u1[i]) % p) * pow(dx_ij, -1, p) % p
                c0 = (u0[i] + gamma * u1[i] - c1 * mu[i]) % p
                matches = 0
                for idx in range(n):
                    if (c0 + c1 * mu[idx]) % p == (u0[idx] + gamma * u1[idx]) % p:
                        matches += 1
                if matches >= threshold:
                    bad.add(gamma)
    return bad


def ceiling_by_triple_sum():
    """
    Direct closed-form ceiling count for (x^3, x^2) using the fact that the
    collinearity condition gives gamma = -(x_i + x_j + x_k) for any triple of
    distinct domain points.  This is an independent derivation from bad_scalars.
    """
    gamma_set = set()
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                s = (mu[i] + mu[j] + mu[k]) % p
                gamma_set.add((-s) % p)
    return gamma_set


def main():
    lines = []
    lines.append(f"p = {K} * 2^{EXP} + 1 = {p}")
    lines.append(f"Proth witness: 5^((p-1)/2) mod p = {p-1}")
    lines.append(f"order-8 generator omega = {omega}")

    # (1) Ceiling stack at t = 3
    ceiling = bad_scalars(3, 2, 3)
    if len(ceiling) != 40:
        fail(f"ceiling (x^3,x^2) at t=3: expected 40, got {len(ceiling)}")
    lines.append(f"[1] ceiling (x^3,x^2) t=3 #bad = {len(ceiling)} (expected 40)")

    # (1a) cross-check by triple-sum formula
    ceiling_cross = ceiling_by_triple_sum()
    if ceiling != ceiling_cross:
        fail(f"ceiling sets disagree: determinant={len(ceiling)} triple-sum={len(ceiling_cross)}")
    lines.append(f"[1a] triple-sum crosscheck: {len(ceiling_cross)} distinct gamma values")

    # (2) Below-ceiling maximum over all monomial pencils at t = 4
    max_bad = 0
    best_pair = None
    for a in range(8):
        for b in range(8):
            bad = bad_scalars(a, b, 4)
            if len(bad) > max_bad:
                max_bad = len(bad)
                best_pair = (a, b)
    if max_bad != 9:
        fail(f"below-ceiling max at t=4: expected 9, got {max_bad}")
    if best_pair != (4, 3):
        fail(f"below-ceiling max pair: expected (4,3), got {best_pair}")
    lines.append(f"[2] below-ceiling t=4 max #bad = {max_bad} at (a,b) = {best_pair} (expected 9)")

    # (3) q-independence statement
    lines.append("[3] A07 integers reproduced exactly at prize-scale p; q-independent.")

    summary = "\n".join(lines)
    print(summary)
    with open(OUT_PATH, "w") as f:
        f.write(summary + "\n")
    print(f"Wrote durable output to {OUT_PATH}")
    print("ALL G310 CHECKS PASS: A07 r=3 k=2 interior ceiling pin survives at prize scale.")


if __name__ == "__main__":
    main()

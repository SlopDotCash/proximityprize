#!/usr/bin/env python3
import math
import numpy as np


def factors(n):
    out = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def proot(p):
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in factors(p - 1)):
            return g
    raise ValueError(p)


def row(n, p):
    m = (p - 1) // n
    g = proot(p)
    logs = {pow(g, j, p): j for j in range(p - 1)}
    N = np.zeros((m, m), dtype=float)
    for x in range(1, p):
        y = (2 - x) % p
        if y:
            N[logs[x] % m, logs[y] % m] += 1
    z = np.exp(2j * np.pi / m)
    indices = np.arange(m)
    U = z ** np.outer(indices, indices) / math.sqrt(m)
    # V[k,a] = (1/m) sum_AB N[A,B] z^(aA-kB).
    V = (U.T @ N @ np.conj(U)).T
    for k in range(min(m, 7)):
        for a in range(min(m, 7)):
            direct = sum(
                z ** (a * (logs[x] % m) - k * (logs[(2 - x) % p] % m))
                for x in range(1, p)
                if (2 - x) % p
            ) / m
            assert abs(V[k, a] - direct) < 2e-8
    svN = np.linalg.svd(N, compute_uv=False)
    svV = np.linalg.svd(V, compute_uv=False)
    assert np.max(np.abs(svN - svV)) < 2e-8
    Vnon = V[1:, :]
    svnon = np.linalg.svd(Vnon, compute_uv=False)[0]
    rows = N.sum(axis=1)
    cols = N.sum(axis=0)

    rng = np.random.default_rng(466 + n + p)
    a = rng.normal(size=m) + 1j * rng.normal(size=m)
    F = np.sqrt(m) * U @ a
    input_energy = n * np.sum(abs(F) ** 2)
    assert abs(input_energy - n * m * np.sum(abs(a) ** 2)) < 1e-7 * max(1, input_energy)
    T = np.zeros(m, complex)
    for Aidx in range(m):
        for Bidx in range(m):
            T[Bidx] += N[Aidx, Bidx] * F[Aidx]
    output_energy = np.sum(abs(V @ a) ** 2)
    assert abs(output_energy - np.sum(abs(T) ** 2) / m) < 1e-7 * max(1, output_energy)
    return (
        n,
        p,
        m,
        int(rows.max()),
        int(cols.max()),
        svN[0] ** 2 / n ** 2,
        svnon ** 2 / n ** 2,
        output_energy / (n * n * np.sum(abs(a) ** 2)),
    )


print(" n p m rowmax colmax fullop2/n2 nontrivop2/n2 random_ratio")
for n, p in [(8, 1009), (16, 1297), (16, 3617), (32, 2593), (32, 3617), (64, 4673)]:
    print(*row(n, p))

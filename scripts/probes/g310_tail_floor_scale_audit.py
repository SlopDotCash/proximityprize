#!/usr/bin/env python3
"""G310 exact scale audit for the G210 tail-floor collision certificate.

The G210 depth-two tail floor is attained exactly when the primitive labels

    2^n, (1 + g^d)^n for 1 <= d < n/2

are pairwise distinct. This probe does three small things, all with integer
arithmetic only:

1. Reproduces the recorded n=32 exceptional primes 50177 and 51137.
2. Sweeps the next n=32 primes up to 10^6 and records every exception.
3. Checks the same certificate at the large Proth prime p = 111*2^128 + 1.

The verdict is finite and per-prime. It does not prove eventual flatness and it
does not touch the production n=2^30 row.
"""
from __future__ import annotations

from collections import Counter
from pathlib import Path
from tempfile import gettempdir


N32_SWEEP_START = 51_138
N32_SWEEP_LIMIT = 1_000_000
EXPECTED_N32_EXCEPTIONS = [65_537, 68_449, 156_353, 194_977]
PROTH_K = 111
PROTH_M = 128
PROTH_WITNESS = 5
PROTH_P = PROTH_K * (1 << PROTH_M) + 1


def require(condition: bool, message: str) -> None:
    """Keep mathematical certificate checks active under ``python -O``."""
    if not condition:
        raise AssertionError(message)


def factor(x: int) -> dict[int, int]:
    out: dict[int, int] = {}
    d = 2
    while d * d <= x:
        while x % d == 0:
            out[d] = out.get(d, 0) + 1
            x //= d
        d += 1
    if x > 1:
        out[x] = out.get(x, 0) + 1
    return out


def is_prime_small(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    if n % 3 == 0:
        return n == 3
    d = 5
    step = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += step
        step = 6 - step
    return True


def primitive_n_root_small(p: int, n: int) -> int:
    require((p - 1) % n == 0, f"n={n} does not divide p-1 for p={p}")
    for g in range(2, p):
        if pow(g, n, p) != 1:
            continue
        if all(pow(g, n // ell, p) != 1 for ell in factor(n)):
            return g
    raise AssertionError("no primitive n-th root")


def certify_proth_prime() -> int:
    require(PROTH_K % 2 == 1, "Proth coefficient must be odd")
    require(PROTH_K < (1 << PROTH_M), "Proth coefficient must be below 2^m")
    p = PROTH_P
    # Proth theorem: this congruence proves p is prime.
    require(
        pow(PROTH_WITNESS, (p - 1) // 2, p) == p - 1,
        "Proth witness failed the primality certificate",
    )
    return p


def primitive_n_root_from_proth(n: int) -> int:
    p = certify_proth_prime()
    require(n & (n - 1) == 0, f"n={n} is not a power of two")
    require(n <= (1 << PROTH_M), f"n={n} exceeds the Proth 2-adic order")
    g = pow(PROTH_WITNESS, (p - 1) // n, p)
    require(pow(g, n, p) == 1, f"candidate root does not have order dividing {n}")
    require(pow(g, n // 2, p) != 1, f"candidate root has order dividing {n // 2}")
    return g


def label_pair_set(p: int, n: int, g: int) -> tuple[list[int], set[tuple[int, int]]]:
    half = n // 2
    atoms = [(pow(2, n, p), 1, 0)]
    atoms += [(pow((1 + pow(g, d, p)) % p, n, p), 2, d) for d in range(1, half)]

    merged: Counter[int] = Counter()
    locations: dict[int, list[int]] = {}
    for label, weight, d in atoms:
        merged[label] += weight
        locations.setdefault(label, []).append(d)

    pairs: set[tuple[int, int]] = set()
    for ds in locations.values():
        if len(ds) > 1:
            for i, d in enumerate(ds):
                for e in ds[i + 1 :]:
                    pairs.add((d, e))
    return sorted(merged.values(), reverse=True), pairs


def relation_pair_set(p: int, n: int, g: int) -> set[tuple[int, int]]:
    half = n // 2
    group = {pow(g, i, p) for i in range(n)}
    pairs: set[tuple[int, int]] = set()
    for d in range(half):
        xd = (1 + pow(g, d, p)) % p
        for e in range(d + 1, half):
            xe = (1 + pow(g, e, p)) % p
            a = xd * pow(xe, p - 2, p) % p
            if a in group:
                require((xd - a * xe) % p == 0, "group ratio did not certify the relation")
                pairs.add((d, e))
    return pairs


def analyze(p: int, n: int, g: int) -> dict[str, object]:
    ks, label_pairs = label_pair_set(p, n, g)
    relation_pairs = relation_pair_set(p, n, g)
    require(
        label_pairs == relation_pairs,
        f"label collisions disagree with subgroup relations at p={p}, n={n}",
    )
    floor = 2 * n - 3
    sumsq = sum(k * k for k in ks)
    floor_eq = sumsq == floor
    distinct = not label_pairs
    flat_hist = ks == [2] * (n // 2 - 1) + [1]
    require(
        floor_eq == distinct == flat_hist,
        f"tail-floor equivalence failed at p={p}, n={n}, g={g}",
    )
    return {
        "p": p,
        "n": n,
        "g": g,
        "ks": ks,
        "sumsq": sumsq,
        "floor": floor,
        "pairs": sorted(label_pairs),
    }


def emit(handle, line: str = "") -> None:
    print(line, flush=True)
    handle.write(line + "\n")
    handle.flush()


def main() -> None:
    out_dir = Path(gettempdir()) / "arklib-reports"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "g310_tail_floor_scale_audit.out"

    with out_path.open("w", encoding="utf-8") as out:
        emit(out, "G310 tail-floor scale audit")

        emit(out, "reproducing recorded n=32 exceptions")
        for p in (50_177, 51_137):
            row = analyze(p, 32, primitive_n_root_small(p, 32))
            require(row["sumsq"] == 73, f"p={p}: expected sumsq 73, got {row['sumsq']}")
            require(row["floor"] == 61, f"p={p}: expected floor 61, got {row['floor']}")
            require(bool(row["pairs"]), f"p={p}: expected a collision witness")
            emit(out, f"p={p} n=32 sumsq/floor=73/61 pairs={row['pairs']}")

        emit(out, f"sweeping n=32 primes from {N32_SWEEP_START} to {N32_SWEEP_LIMIT}")
        exceptions: list[int] = []
        checked = 0
        first = N32_SWEEP_START + ((1 - N32_SWEEP_START) % 32)
        for p in range(first, N32_SWEEP_LIMIT + 1, 32):
            if not is_prime_small(p):
                continue
            checked += 1
            row = analyze(p, 32, primitive_n_root_small(p, 32))
            if row["pairs"]:
                exceptions.append(p)
                emit(
                    out,
                    "exception "
                    f"p={p} g={row['g']} sumsq/floor={row['sumsq']}/{row['floor']} "
                    f"pairs={row['pairs']}",
                )
        require(checked == 4_578, f"expected 4578 n=32 primes, checked {checked}")
        require(
            exceptions == EXPECTED_N32_EXCEPTIONS,
            f"n=32 exceptions changed: {exceptions}",
        )
        emit(out, f"n=32 checked={checked} exceptions={exceptions}")

        proth_p = certify_proth_prime()
        emit(
            out,
            "large Proth prime certified by Proth theorem: "
            f"p={proth_p}=111*2^128+1 witness={PROTH_WITNESS}",
        )
        for n in (32, 64):
            row = analyze(proth_p, n, primitive_n_root_from_proth(n))
            require(
                row["sumsq"] == row["floor"],
                f"large-scale n={n} cell missed its floor: {row['sumsq']} != {row['floor']}",
            )
            require(not row["pairs"], f"large-scale n={n} cell has collisions: {row['pairs']}")
            require(proth_p > n * (1 << 128), f"p={proth_p} is not beyond the stated scale")
            emit(
                out,
                f"large-scale clean cell n={n} p={proth_p} "
                f"g={row['g']} sumsq/floor={row['sumsq']}/{row['floor']} pairs=[]",
            )

        emit(
            out,
            "PASS: extra n=32 exceptions are finite per-prime collisions; "
            "the same tail-floor certificate is clean at p=111*2^128+1 for n=32,64.",
        )

    print(f"wrote {out_path}", flush=True)


if __name__ == "__main__":
    main()

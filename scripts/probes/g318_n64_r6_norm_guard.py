#!/usr/bin/env python3
"""G318 norm-guard certificate for the n=64, rank-6 antipodal model.

G317 checked n=64,r=5 directly. The n=64,r=6 sparse histogram is too large for
a safe Python-dict audit, but the same conclusion has a short exact guard.

Let zeta be a primitive 64th root. Any relation counted by the coefficient-a
adjacent-rank dot has the form

    zeta^u + sum_{i in A} zeta^i - sum_{j in B} zeta^j - a = 0 mod p,

with |A|=6, |B|=5, and a in {1,2}. Its coefficient l1 norm is at most 14.
If the corresponding cyclotomic integer is nonzero, its algebraic norm is a
nonzero integer with absolute value at most 14^phi(64)=14^32. Because

    p = 111*2^128 + 1 > 14^32,

and p is prime, such a nonzero relation cannot vanish modulo p. Therefore every
finite-field relation in this n=64,r=6 audit is already a complex cyclotomic
relation. For 64th roots, those are exactly the antipodal pair cancellations.

The script verifies the exact numerical hypotheses and emits the G316
rank-six dot/A constants for coefficients 1 and 2. This is a finite n=64
certificate, not a production n=2^30 theorem.
"""
from __future__ import annotations

from math import comb
from pathlib import Path
from tempfile import gettempdir


N = 64
H = N // 2
RANK = 6
PHI_N = 32
L1_BOUND = 14
PROTH_K = 111
PROTH_M = 128
PROTH_WITNESS = 5
PROTH_P = PROTH_K * (1 << PROTH_M) + 1

EXPECTED_DOTS = {
    1: 0,
    2: 20_331_698_688,
}

EXPECTED_A = {
    1: -2_341_449_599_010_471_936,
    2: 767_955_559_391_433_686_463_300_268_059_000_302_726_608_177_666_560,
}


def certify_proth_prime() -> int:
    assert PROTH_K % 2 == 1
    assert PROTH_K < (1 << PROTH_M)
    # Proth theorem: this congruence proves PROTH_P is prime.
    assert pow(PROTH_WITNESS, (PROTH_P - 1) // 2, PROTH_P) == PROTH_P - 1
    return PROTH_P


def coeff2_r6_closed(h: int) -> int:
    return 2 * h * (
        comb(h - 1, 2)
        + 81 * comb(h - 1, 3)
        + 786 * comb(h - 1, 4)
        + 1722 * comb(h - 1, 5)
    )


def adjacent_total(n: int, r: int) -> int:
    return comb(n, r) * comb(n, r - 1)


def emit(handle, line: str = "") -> None:
    print(line, flush=True)
    handle.write(line + "\n")
    handle.flush()


def verify_norm_guard(handle) -> None:
    p = certify_proth_prime()
    norm_bound = L1_BOUND ** PHI_N
    assert p == PROTH_P
    assert p > norm_bound
    assert (p - 1) % N == 0
    root64 = pow(PROTH_WITNESS, (p - 1) // N, p)
    assert root64 != 1
    assert pow(root64, N, p) == 1
    assert pow(root64, N // 2, p) == p - 1
    emit(handle, f"p={p}=111*2^128+1 is Proth-prime certified by witness {PROTH_WITNESS}")
    emit(handle, f"phi(64)={PHI_N}, l1_bound={L1_BOUND}, norm_bound=14^32={norm_bound}")
    emit(handle, f"norm guard p > 14^32: margin={p - norm_bound}")
    emit(
        handle,
        "consequence: every n=64,r=6 coefficient-a relation with a in {1,2} "
        "that vanishes mod p must be an antipodal cyclotomic relation",
    )


def verify_rank_six_constants(handle) -> None:
    p = PROTH_P
    total = adjacent_total(N, RANK)
    dot1 = 0
    dot2 = coeff2_r6_closed(H)
    a1 = p * dot1 - N * N * total
    a2 = p * dot2 - N * N * total
    assert dot1 == EXPECTED_DOTS[1]
    assert dot2 == EXPECTED_DOTS[2]
    assert a1 == EXPECTED_A[1]
    assert a2 == EXPECTED_A[2]
    assert a1 < 0 < a2
    emit(handle, f"n={N} r={RANK} adjacent_total={total}")
    emit(handle, f"coefficient=1 dot={dot1} A={a1:+d}")
    emit(handle, f"coefficient=2 dot={dot2} A={a2:+d}")


def main() -> None:
    out_dir = Path(gettempdir()) / "arklib-reports"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "g318_n64_r6_norm_guard.out"

    with out_path.open("w", encoding="utf-8") as handle:
        emit(handle, "G318 n=64 rank-6 norm guard")
        verify_norm_guard(handle)
        verify_rank_six_constants(handle)
        emit(
            handle,
            "PASS: the n=64,r=6 finite-field relation count at the certified "
            "Proth prime is forced to equal the antipodal-model count.",
        )

    print(f"wrote {out_path}", flush=True)


if __name__ == "__main__":
    main()

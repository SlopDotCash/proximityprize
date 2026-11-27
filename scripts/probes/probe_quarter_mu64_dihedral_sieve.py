#!/usr/bin/env python3
"""Driver for the exhaustive characteristic-zero mu_64 dihedral reflection sieve.

Verifies:
1. Exact 16-generator cyclotomic factorization of |1 - zeta_64^d| and |s_x - s_a|.
2. Nonzero 16x16 regulator determinant for {log |1 - zeta_64^{2k+1}| : k=0..15}.
3. Exhaustive C++ modular rank sieve at BOTH primes 101 and 103 across:
   - ALL 28,336 odd-reflection Galois orbits (summing to C(32,6) = 906,192),
   - ALL 47,251 even-reflection Galois orbits in {1..31} (summing to C(31,6) = 736,281),
   confirming ZERO size-7 ternary kernel vectors and exact detection of all
   12 odd + 8 even Chebyshev T_8 degree-8 positive controls.
"""
from __future__ import annotations

from pathlib import Path
import subprocess
import tempfile
import numpy as np


def verify_cyclotomic_basis() -> None:
    n = 64
    exps = np.zeros((n, 16), dtype=np.int64)
    for d in range(1, n):
        mult = d & -d
        u = d // mult
        step = n // mult
        for j in range(mult):
            r = (u + j * step) % n
            r_rep = min(r, n - r)
            assert r_rep % 2 == 1
            exps[d, (r_rep - 1) // 2] += 1

    logs_odd = np.array([np.log(2.0 * np.sin(np.pi * (2 * k + 1) / n)) for k in range(16)])
    for d in range(1, n):
        lhs = np.log(2.0 * np.sin(np.pi * d / n))
        rhs = float(exps[d] @ logs_odd)
        assert abs(lhs - rhs) < 1e-12

    reg = np.array([
        [np.log(2.0 * np.sin(np.pi * (((2 * e + 1) * (2 * k + 1)) % n) / n)) for k in range(16)]
        for e in range(16)
    ])
    det = float(np.linalg.det(reg))
    assert abs(det) > 1e5
    print(f"Verified 16-generator factorization and regulator det = {det:.6e}", flush=True)


def main() -> None:
    verify_cyclotomic_basis()
    src = Path(__file__).with_name("probe_quarter_mu64_dihedral_sieve.cpp")
    with tempfile.TemporaryDirectory() as tmp:
        exe = Path(tmp) / "mu64_dihedral_sieve"
        subprocess.run(["c++", "-O3", "-std=c++17", str(src), "-o", str(exe)], check=True)
        subprocess.run([str(exe)], check=True)


if __name__ == "__main__":
    main()

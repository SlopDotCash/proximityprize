#!/usr/bin/env python3
"""G249 row-selection barrier for Cartesian Jacobi discrepancy.

A global Cartesian exceptional budget at density D cannot force every fixed row to be controlled
unless D < 1/m: one complete row has m bad points out of m^2.
"""
from math import log2

def sponsor(name, log2p, log2m, log2D):
    need = -log2m
    missing = log2D - need
    print(f"{name}: log2(p)={log2p:.6f} log2(m)={log2m:.6f} "
          f"best_log2D={log2D:.3f} need_log2D<{need:.3f} missing_bits={missing:.3f}")

print("=== exact finite row obstruction ===")
for m in [8, 16, 126, 2**20]:
    bad = m
    grid = m*m
    print(f"m={m}: one full row has bad={bad}, grid={grid}, density=1/{m}, "
          f"so any Cartesian budget allowing >= {bad} exceptions permits an uncontrolled row")
print("=== sponsor discrepancy/density barrier (from G248 LZZ audit) ===")
sponsor("P1", 158.0, 128.0, -14.748)
sponsor("P2", 159.0, 129.0, -14.915)
print("PASS: Cartesian discrepancy must beat row density 1/m before it can imply uniform fixed-row control")

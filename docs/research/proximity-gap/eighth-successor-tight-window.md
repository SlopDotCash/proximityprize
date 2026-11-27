# Tight eighth-rate successor windows and non-exceptional climb through 679,477,247 errors

At length $n = 2^{30} = 1{,}073{,}741{,}824$, dimension $k = 2^{27} = 134{,}217{,}728$, degree $d = k - 1 = 134{,}217{,}727$, and second-prime budget $2n = 2{,}147{,}483{,}648$, the earlier eighth-rate successor analysis ([`eighth-rich-head-safety.md`](eighth-rich-head-safety.md)) charged a four-head residual allowance of **$20{,}607{,}410$**, leaving $1{,}762{,}208$ labels of slack on ordinary configurations and a double-site orbit floor of $258{,}131{,}746$.

Combining the single noncommon resultant and shared companion total degree ([`quarter-common-factor-degrees.md`](quarter-common-factor-degrees.md)) with multi-tier projective Veronese polars ([`tangent-polar-windows.md`](tangent-polar-windows.md)) and sparse surface Gauss heights ([`half-sparse-gauss-window.md`](half-sparse-gauss-window.md)) dramatically tightens `671,088,640` and certifies non-exceptional safety across the open interval up to `679,477,247` (one error below the transverse attack [`EighthTransverseAttack.lean`](../../../ArkLib/Research/ProximityGap/Frontier/EighthTransverseAttack.lean)).

## Summary of verified production windows

| Window | Errors $e$ | Shapes (pri / comp) | $H$ | Model & polar tiers | $j=4$ residual | Max non-exceptional total | Saturated orbit floor $B$ |
|---|---:|---|---:|---|---:|---:|---:|
| Baseline (`main`) | `671,088,640` | `(6,16,335)` / `(9,26,128)` | `81,920` | Ordinary tangent | `20,607,410` | `2,145,721,440` | `258,131,746` |
| **W0 (Pure L1+L2)** | **`671,088,640`** | `(6,16,335)` / `(10,29,126)` | `1,000` | Log-deriv + 10 polars `(2,1)..(11,7)` | **`2,280,700`** (`9.0×`) | **`2,127,394,730`** (`20.09M` slack) | **`267,295,101`** |
| **W1 (Sparse-Gauss)** | **`671,088,640`** | `(6,16,335)` / `(10,29,126)` | `500` | Sparse-Gauss + 3 polars `(2,1),(3,2),(4,2)` | **`397,364`** (`51.8×`) | **`2,125,511,394`** (`21.97M` slack) | **`268,236,769`** |
| **W2 (Climb `+6.51M`)** | **`677,600,000`** | `(8,22,950)` / `(14,41,237)` | `1,000` | Sparse-Gauss + 3 polars `(2,1),(3,2),(4,2)` | **`1,492,569`** (`1,492,336` exact) | **`2,147,225,906`** ($D_3\ge 2$ or $D_4\ge 6$) | — |
| **W3 (Ceiling $-1$)** | **`679,477,247`** | `(9,25,887)` / `(15,44,297)` | `2,000` | Sparse-Gauss + 3 polars `(2,1),(3,2),(4,2)` | **`2,416,639`** | **`2,137,916,562`** ($D_3\ge 2$ or $D_4\ge 7$) | — |

## Key consequences

1. **Zero-Gauss-graph `9.0×` residual drop (W0)**: Using *only* the algebraic logarithmic-derivation height ($2 A G + 2 W m$) and projective Veronese polars — without invoking the sparse Gauss-graph Newton-volume estimate — drops the four-head residual at `671,088,640` to **$2{,}280{,}700$**.
2. **`51.8×` residual drop and sharpened double-site orbit floor (W1)**: Under Sparse-Gauss + just three polar tiers `(2,1)` ($m > 2$), `(3,2)` ($m > 6$), and `(4,2)` ($m > 12$), the four-head residual plunges to **$397{,}364$**:
   - Any saturated `(1,1,1,1)` overrun at `671,088,640` requires at least **$268{,}236{,}769$** distinct double-site direction orbits — within **$198{,}685$** of the 2-to-1 double-site threshold $2d = 268{,}435{,}454$ out of $4d = 536{,}870{,}908$ total double sites (`> 49.963%` of all double sites, tightened `51.8×` from `10,303,708` below `2d`).
   - Any `(1,1,1,5)` overrun at `671,088,640` (including the nonscalar antipode of [`EighthDyadicHeadDirections.lean`](../../../ArkLib/Research/ProximityGap/Frontier/EighthDyadicHeadDirections.lean)) can have at most **$397{,}367$** total fresh-label collisions across all four heads (`< 0.019%` of $2n$).
3. **Non-exceptional climb across the open bracket (W2 & W3)**:
   - On all four windows, $15c > 3n + 20d$ (`FiveHeadTrianglePacking.four_incidence`) and $13c > 3n + 13d$ (`EighthCollinearOutlier.cluster_cap`) force **every $j \ge 6$ rich family to be collinear** (`EighthCollinearOutlier.six`) and **every $j = 5$ rich family to contain $4$ collinear heads**. At $e = 671{,}088{,}640$ (W0 & W1), the resulting $4 + 1$ transverse-outlier family is explicitly capped at **$2{,}058{,}021{,}547$** by [`EighthFourPlusOne.lean`](../../../ArkLib/Research/ProximityGap/Frontier/EighthFourPlusOne.lean) (and included in `ordinaryHeadMass` at $j = 5$, fitting well below `ordBound`). Above $5k$ (W2 & W3), both $4 + 1$ and $3 + 1$ transverse-outlier families remain open.
   - Up through **$e = 677{,}600{,}000$** ($+6{,}511{,}360$ errors past $5k$, `77.6%` of the open bracket), every $j \le 3$, every $j \ge 6$ (collinear), collinear $j = 4, 5$, and every noncollinear four-head family with sorted deficits $D_3 \ge 2$ or $D_4 \ge 6$ fits strictly below $2n$.
   - All the way through **$e = 679{,}477{,}247$** (one error below the transverse attack), every $j \le 3$, every $j \ge 6$ (collinear), collinear $j = 4, 5$, and every noncollinear four-head family with $D_3 \ge 2$ or $D_4 \ge 7$ still fits strictly below $2n$.

## Verification ledger

- **Lean-checked (axiom-clean, zero `sorry`)**: [`ArkLib/Research/ProximityGap/Frontier/EighthSuccessorTightWindow.lean`](../../../ArkLib/Research/ProximityGap/Frontier/EighthSuccessorTightWindow.lean) proves `componentCap_mono_b` (reducing the 2D `(b, m)` grid to the maximal admissible `b = min (degree₁ - j) m`), `hypotheses`, `window_budgets`, `componentCap_le_mul_maxUnitPrice`, `linMult_le_maxUnitPrice`, `all_non_exceptional_allocations`, `surfaces` (genuine trivariate mixed-Hasse interpolants on any size-$2^{30}$ domain for all four windows), and `sharpened_orbit_and_collision_floors`, all verified with `#print axioms` $\subseteq \{\text{propext}, \text{Classical.choice}, \text{Quot.sound}\}$.
- **Reproducible probe**: [`scripts/probes/probe_eighth_successor_tight_window.py`](../../../scripts/probes/probe_eighth_successor_tight_window.py) independently evaluates the full 2D `(b, m)` grid without monotonicity reduction and matches every integer bound exactly.
- **Written-only geometric bridges**: logarithmic-derivation heights, projective plane-curve duality, and sparse Gauss-graph Newton volume remain written mathematics per [`tangent-polar-windows.md`](tangent-polar-windows.md) and [`half-sparse-gauss-window.md`](half-sparse-gauss-window.md).

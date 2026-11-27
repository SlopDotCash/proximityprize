# Exponential $O(\sqrt{N})$ Degree Bound for Non-Descending Dyadic Split Pencils

## Summary

This note accompanies [`DyadicSplitPencilSqrtBound.lean`](../../../ArkLib/Research/ProximityGap/Frontier/DyadicSplitPencilSqrtBound.lean) and [`probe_dyadic_split_pencil_sqrt.py`](../../../scripts/probes/probe_dyadic_split_pencil_sqrt.py).

Combining the **General Depth-$L$ Dyadic Fourier Parity Theorem** (`depthL_fourier_parity_zero` in [`QuarterMu64Mu128CyclicExclusion.lean`](../../../ArkLib/Research/ProximityGap/Frontier/QuarterMu64Mu128CyclicExclusion.lean)) with a **symmetric 3-fiber / 4-fiber Depth-$L$ induction** on `Finset (ZMod (2^k))` (requiring **zero** Galois-automorphism step and **zero** computer search!), we prove an **exponential $O(\sqrt{N})$ upper bound** on the degree $m$ of EVERY non-descending 3-split and 4-split polynomial pencil on $\mu_{2^k}$ ($k \ge 6$) in characteristic zero — and unconditionally over BOTH designated primes $p_1$ and $p_2$ on $\mu_{64}$ and $\mu_{128}$ via `mu64-unit-lattice-transfer.md` / `mu128-unit-ellipsoid-transfer.md`!

## Main Results

1. **Arbitrary Depth-$L$ Symmetry-Swap Induction (`three_split_depthL_induction`):**
   Let $S_0, S_1, S_2 \subset \mathbb{Z}/2^k\mathbb{Z}$ be pairwise disjoint sets of size $m$ obeying the Depth-$L$ Fourier forcing law `DepthLForcing` with no two fibers simultaneously antipodal. By induction on $L$ ($2 \le L \le k - 2$):
   - At $L = 1$: all three fibers concentrate in the same parity coset ($\le 2$ points each in the opposite parity).
   - At $L = 2$ ($m \ge 11$): symmetry-swapping the three fibers forces ALL THREE into the same mod-$4$ coset AND forces `ShellPeriodic k 2 r (S i)`, so `periodic_subset_card_dvd` gives $4 \mid |S_i \cap \text{shell}_0|$, automatically annihilating the odd shell ($|S_i \cap \text{shell}_0| = 0$) with no Galois step!
   - At $L \to L + 1$ ($m \ge 3 \cdot 2^{L+1} - 3$): if not all three fibers choose the same sub-coset mod $2^{L+1}$, then two choose one half and one chooses the other; applying Depth-$(L+1)$ forcing to all three pairs renders both fibers in the majority half **100% antipodal** (`isAntipodal_of_both_halves`), contradicting non-descent! Thus all three fibers put $\ge m - (2^{L+2} - 4)$ disjoint points inside the same coset of size $2^{k - (L + 1)}$.

2. **Master Depth-$L$ Degree Ceilings & Universal $m < \sqrt{3 N}$ Bound (`three_split_non_descending_bound`, `four_split_non_descending_bound`, `three_split_sqrt_bound`):**
   For every $2 \le L \le k - 2$:
   $$m \le \max\!\left(\text{depthEntry}(L) - 1,\; \left\lfloor\frac{2^{k - L}}{F}\right\rfloor + 2^{L + 1} - 4\right) \qquad (F \in \{3, 4\}).$$
   Optimizing at $L = \lfloor (k - 2) / 2 \rfloor$ proves the universal closed-form bound
   $$m^2 < 3 \cdot 2^k \qquad (\forall k \ge 6).$$

3. **Concrete Consequences (`concrete_dyadic_sqrt_caps`):**

| Domain | 3-Split Non-Descending Cap | 4-Split Non-Descending Cap | Field Scope |
|---|---:|---:|---|
| $\mu_{64}$ ($k = 6$) | $m \le 10$ ($L = 2$) | $m \le 10$ ($L = 2$) | **Exact $p_1$ & $p_2$** + char 0 (ZERO search!) |
| $\mu_{128}$ ($k = 7$) | $m \le 14$ ($L = 2$) | **$m \le 12$** ($L = 2$) | **Exact $p_1$ & $p_2$** + char 0 (KILLS `m₀ = 15, h = 1`!) |
| $\mu_{256}$ ($k = 8$) | $m \le 22$ ($L = 3$) | $m \le 20$ ($L = 3$) | Char 0 |
| $\mu_{2^{29}}$ ($k = 29$) | $m \le 38{,}225$ ($L = 13$) | $m \le 32{,}764$ ($L = 13$) | Char 0 ($2 \times 38{,}225 = 76{,}450 \ll D = 268{,}435{,}454$!) |
| $\mu_{2^{30}}$ ($k = 30$) | **$m \le 54{,}609$** ($L = 14$) | **$m \le 49{,}148$** ($L = 13$) | Char 0 (`3,511×` below $D$ after $v_2(D) = 1$ descent!) |

In particular, combining `four_split_non_descending_bound` at $k = 7$ ($m \le 12$) with `four_head_cyclic_pullback_exclusions` in [`QuarterFourHeadCrossRatioBarrier.lean`](../../../ArkLib/Research/ProximityGap/Frontier/QuarterFourHeadCrossRatioBarrier.lean) — given the written `DepthLForcing` and non-descent instantiation over $p_1$ and $p_2$ via `mu128-unit-ellipsoid-transfer.md` — eliminates all remaining constant-cross-ratio 4-head collinear pullbacks on $\mu_{128}$ (both $h = 0$ and $h = 1$).

## Honesty Boundary

- **100% axiom-clean Lean (`DyadicSplitPencilSqrtBound.lean`):** All 11 public theorems (`coset_card` through `concrete_dyadic_sqrt_caps`) are proved on actual `Finset (ZMod (2^k))` sets with Mathlib-only imports, 0 `sorry`, 0 warnings, and `#print axioms` $\subseteq \{\text{propext}, \text{Classical.choice}, \text{Quot.sound}\}$.
- **Scope:** Instantiating `DepthLForcing` from a polynomial pencil uses `depthL_fourier_parity_zero` (in `QuarterMu64Mu128CyclicExclusion.lean`) plus cyclotomic-unit multiplicative independence in characteristic zero (and transfers unconditionally to exact $p_1$ and $p_2$ on $\mu_{64}$ and $\mu_{128}$ via `mu64-unit-lattice-transfer.md` / `mu128-unit-ellipsoid-transfer.md`). It does NOT by itself rule out modular-only split pencils on $\mu_{2^{30}}$ over $p_1$ or $p_2$.

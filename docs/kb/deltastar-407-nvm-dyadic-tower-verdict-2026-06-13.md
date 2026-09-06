# δ* #407 — NVM-dyadic-tower verdict (2026-06-13)

**Angle:** `nvm-dyadic-tower` — close/partially-bound the prize Gauss-period house via the
nonvanishing-minors (NVM) route (Garcia–Karaali–Katz; Díaz Padilla–Ochoa Arango,
arXiv:2310.09992 *An uncertainty principle for small-index subgroups of finite fields*), exploiting
that the prize index `m = (q−1)/n = 2^128` is a pure power of 2 (a μ_n tower). Hypothesis tested: a
recursive/tower Chebotarev descent `index 2^k → 2^{k-1}` cracks NVM where general large index is open.

## VERDICT: tower descent FAILS for power-of-2 index — it is the WORST case, not a helpful one.

Honest. No closure. A precise structural localization of the open wall + new axiom-clean substrate.

## The structure (NEW, machine-verified)

Index-`m` subgroup `H` (`|H| = n = (q−1)/m`), char `χ` on `H`, `m` extensions `ϕ_i` to `𝔽_q^*`,
Gauss sums `G_i = G(ϕ_i)` (all `|G_i| = √q`). The compressed-Fourier (CFT) matrix is, up to
root-of-unity row/col scaling (preserves minor vanishing), the symmetric `M_{a,b} = T_{a+b}` with
`T_j = (1/m) ∑_i ω^{ij} G_i` (`ω = ζ_m`). **`T` IS the prize house object `η_b`** up to the `√q/m`
scale. NVM = *all* minors nonzero (= finite-field Biró–Meshulam–Tao uncertainty). Proven for index
`m = 2,3`; OPEN larger.

Key factorization (verified): `M = (1/m) F·diag(G)·Fᵀ`, `F_{a,i} = ω^{ai}`. Hence by Cauchy–Binet
every `k×k` minor is
```
minor_{I,J} = (1/m^k) ∑_{|K|=k} V_{I,K} · V_{J,K} · ∏_{i∈K} G_i
```
with `V_{I,K}` a generalized Vandermonde at roots of unity (each nonzero —
`RootsOfUnityVandermonde.genVandermonde_rootsOfUnity_det_ne_zero_iff`). So a minor is a *signed sum*
of `C(m,k)` nonzero terms; cancellation is the open phenomenon.

- `k = 1`: minors = `T_j` (the house values). NVM at `k=1` ⟺ house never vanishes.
- `k = m`: single Cauchy–Binet term `= (det F)² ∏ G_i / m^m`, **never 0** (since `|G_i| = √q ≠ 0`).
  NVM obstruction is NEVER at `k = m`.
- **intermediate `k` (worst at `k ≈ m/2`)**: the genuinely hard, open conditions.

## Why the tower descent fails (the obstruction, localized)

Radix-2 FFT butterfly: `T_j = ½(A_r + ω^j B_r)`, `A = DFT_{m/2}(G_even)`, `B = DFT_{m/2}(G_odd)` —
the index-`m/2` sub-tower transforms of `χ` and `χ·ψ`. Vanishing/near-vanishing of `T_j` needs the
**resonance** `A_r = −ω^j B_r`, which couples the two sub-towers via a **phase the descent does not
control**. The Davenport–Hasse duplication `G(χ)G(χη) = χ⁻²(2)G(η)G(χ²)` (verified to 1e-11) ties the
moduli (`√q`, already known) and a product across levels, but leaves the relative phase free; by
Chebotarev the Gauss-sum phases equidistribute ⟹ NO algebraic obstruction blocks the resonance.

Probe data (`scripts/probes/_407_nvm_dyadic_tower.py`):
- The clean "NVM ⟺ all `T_j` ≠ 0" reduction (which *solves* index 2,3) BREAKS at **m = 4 = 2²** and
  worsens for m=8,16: the smallest minor moves from `k=1` to `k≈m/2` (m=8,p=17: min 1×1 = 0.37 but
  min 3×3 = 0.011). **Power-of-2 index is the WORST index for NVM, not a recursive shortcut.**
- `T_j` reaches within `0.005·√q` of 0 (m=8, p=857): near-resonances abundant, no per-term floor.
- This is the same resonance as cross-parity framing 7 ("≈96–100% of defects satisfy A = −g·B").

## In-tree (axiom-clean, strict `lake build` EXIT 0)

`Research/ProximityPrize/Frontier/NVMDyadicTowerObstruction.lean`
(`[propext, Classical.choice, Quot.sound]`):
- `cftMat_apply`, `cftMat_apply_eq_houseVec` — entries = `T_{a+b}` (1×1 ⟺ house).
- `cft_det_eq`, `cft_top_minor_ne_zero` — full minor `= (det F)² ∏ G_i / m^m ≠ 0`.
- `cft_two_minor` — the 2×2 minor as the explicit Cauchy–Binet signed double-sum (the open
  cancellation made explicit). Bridges to `RootsOfUnityVandermonde`.

## Cross-path lever

The NVM minor decomposition is a **second independent route to the same house object** `B = max‖η_b‖`:
the `k=1` NVM condition is *exactly* house-nonvanishing, and the intermediate-`k` minors give a
*hierarchy of higher conditions* on the same Gauss-phase DFT `T`. Anyone proving the prize house
flatness `B ≲ √(n log(q/n))` simultaneously settles the `k=1` NVM layer; conversely an NVM proof for
power-of-2 index would yield house nonvanishing. The butterfly-resonance obstruction here is the
SAME phase-freedom that walls every other #407 route (Paley eigenvalue, deep-moment, cross-parity).
DO NOT spend effort on tower-Chebotarev descent for NVM — it provably cannot escape the phase wall.

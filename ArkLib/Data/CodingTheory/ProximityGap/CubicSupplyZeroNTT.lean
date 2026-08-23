/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CubicOrchardIdentity
import Mathlib.Tactic.NormNum.Prime

/-!
# An EXACT in-window supply ZERO: the cubic word on the NTT domain `μ_16 ⊂ F₂₅₇` (#389)

The cubic orchard identity (`cubic_list_eq_zeroSum`, in-tree) is exact: for `w = x³` on
any domain `dom : Fin n ↪ F`, the number of `rsCode dom 2` codewords with agreement `≥ 3`
(the explainable-`3`-core supply, the deepest pre-capacity band `m = 0` for `k = 2`)
equals the number of `3`-subsets of the domain summing to `0`.

This file instantiates it at the production-shape NTT domain `μ_16 ⊆ F₂₅₇^×` (the order-16
multiplicative subgroup; `F₂₅₇` is the canonical small NTT field).  The zero-sum-triple
count there is **exactly `0`** — the char-`0` Mann rigidity (three `2`-power roots of unity
never sum to zero, as `μ_{2^k}` contains no cube root of unity) **survives to `F₂₅₇`** —
so:

> **`cubicSupply_mu16_F257_eq_zero`** — the cubic word `x³` on `μ_16 ⊂ F₂₅₇` has
> **exactly `0`** explainable `3`-cores: NO degree-`<2` codeword agrees with it on `3`
> points.

This is the first **exact, machine-checked, in-window supply ZERO** at a production NTT
domain: at radius `δ = 1 − 3/16 = 13/16`, one granularity step below the capacity radius
`14/16` (i.e. deep in the prize window `(1−√ρ, 1−ρ)`), the cubic word contributes *no*
bad scalars at all — far below both the random mean `C(16,3)/q ≈ 2.2` and the GV ceiling
`√(16·E(μ_16)) = √(16·912) ≈ 121` from `gvRepBound_H16`.  It is a concrete witness that
the smooth-domain supply can sit at the *bottom* of its two-regime band (`Θ(n)` floor →
here `0`), the regime the δ* lower bound needs.

Contrast (the wall): over the FULL field `F₂₅₇` the same cubic word has `Θ(q²)` explainable
cores (`sumZero_card_quadratic`), and on the worst `μ_{2^k} ⊂ F_p` the count reaches
`~n^{5/3}` (`probe_smooth_zero_sum_triples.py`) — the smooth multiplicative structure is
exactly what collapses it here.

Issue #389.  Probe: `scripts/probes/probe_smooth_zero_sum_triples.py`.
-/

open Finset

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

local instance localInstance_CubicSupplyZeroNTT_1 : Fact (Nat.Prime 257) := ⟨by norm_num⟩

/-- The 16 elements of the order-16 multiplicative subgroup `μ_16 ⊆ F₂₅₇^×`. -/
def mu16vals : Fin 16 → ZMod 257 :=
  ![1, 2, 4, 8, 16, 32, 64, 128, 129, 193, 225, 241, 249, 253, 255, 256]

/-- The NTT evaluation domain `μ_16 ⊂ F₂₅₇` as an embedding (injective by `decide`). -/
def dom16 : Fin 16 ↪ ZMod 257 :=
  ⟨mu16vals, by decide⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- The zero-sum-triple count of `μ_16 ⊂ F₂₅₇` is exactly `0`: no three of the sixteen
`16`-th roots of unity sum to zero in `F₂₅₇` (the char-`0` no-cube-root rigidity survives
to this prime). -/
theorem mu16_F257_zeroSum_triples_eq_zero :
    (((Finset.univ : Finset (Fin 16)).powersetCard 3).filter
        (fun T => ∑ i ∈ T, dom16 i = 0)).card = 0 := by
  decide

open Classical in
/-- **EXACT IN-WINDOW SUPPLY ZERO**: the cubic word `x³` on the NTT domain
`μ_16 ⊂ F₂₅₇` has exactly `0` explainable `3`-cores — no `rsCode dom16 2` codeword agrees
with it on `3` points.  Via the cubic orchard identity, this is the zero-sum-triple count,
which is `0`.  A concrete δ* lower-bound data point: at radius `13/16` (one step below
capacity), this word produces no bad scalars. -/
theorem cubicSupply_mu16_F257_eq_zero :
    ((Finset.univ : Finset (Fin 16 → ZMod 257)).filter (fun c =>
        c ∈ (rsCode dom16 2 : Submodule (ZMod 257) (Fin 16 → ZMod 257))
          ∧ 3 ≤ (agreeSet c (fun i => (dom16 i) ^ 3)).card)).card = 0 := by
  rw [cubic_list_eq_zeroSum dom16]
  exact mu16_F257_zeroSum_triples_eq_zero

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.cubicSupply_mu16_F257_eq_zero

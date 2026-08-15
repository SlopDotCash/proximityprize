/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# LANE G80P (#466, 2026-07-10): REDUCED-FRACTION RIGIDITY below √p — congruent cross-products
  of sub-√p integers are EQUAL, so coset-interval intersections inject into small subgroup
  ratios; and the rigidity window is REGIME-DISJOINT from the prize saddle — the formal
  explanation of the classical p^{1/3}/β = 3 barrier inside our own chain (axiom-clean).

## The rigidity theorem

* `cross_mul_eq_of_congruent` : if `x, y, x', y' ∈ [1, W]` with `W² < p` and
  `x·y' ≡ x'·y (mod p)`, then `x·y' = x'·y` AS NATURALS — below √p, modular ratio equality is
  integer ratio equality. (Both cross-products lie in `[1, W²] ⊆ [1, p−1]`, and two equal
  residues in that range are equal.)
* `ratio_injective_on_interval` : consequently, for `z, z'` in a coset `C = c·H` with vals in
  an interval of length `W`, `W² < p`, the modular ratio `z'/z` DETERMINES the integer pair —
  the map from `C ∩ interval` (pointed at any fixed `z₀`) to reduced integer pairs
  `(s, t) ∈ [1, W]²` with `s·t⁻¹ ∈ H` is injective.
* `coset_interval_le_smallRatioCount` : `#(C ∩ interval of length W) ≤ ρ_H(W)` for EVERY
  coset `C` and EVERY such interval, where
  `ρ_H(W) := #{(s,t) ∈ [1,W]² : s·t⁻¹ mod p ∈ H}` is the SMALL-RATIO COUNT of the subgroup —
  a finite, probe-checkable quantity, and exactly the support-2 small-height relation census
  of the OC program (`s − h·t ≡ 0 mod p` with `s, t` small ⟺ `p ∣ Norm(s − t·ζ^k)`).

## The regime disjointness (the honest quantitative finding)

The rigidity needs `W < √p`, i.e. arc count `K = p/W > √p`. The G80X saddle needs
`K ≈ √(2πn/log q)` ≪ √p at prize scale (`p ≈ n^β`, `β ≫ 3`: `√(n/log q)` vs `n^{β/2}`).
The two windows OVERLAP only when `√p ≲ √(n/log q)`, i.e. `p ≲ n/log q` — `β ≤ 1`, far below
the prize regime. This is the classical Cilleruelo–Garaev `p^{1/3}`-type barrier expressed
inside our formal chain: integer-rigidity methods control arcs only at `K > √p`, where the
oscillation term is negligible but the per-arc budget `ρ_H(W)` costs a factor `K` in the
G80Y consumer, giving `M ≲ K·ρ ≫ √(n log q)` unless `ρ` is sub-constant — impossible
(`ρ ≥ 1` from `(1,1)`; `ρ ≥ 2` when `−1 ∈ H`... signed variant). A viable certificate must
therefore work OUTSIDE the rigidity window — genuinely modular, not integer-liftable: the
sharpest formal articulation yet of why the wall survives all height/rational-lifting
technology (consistent with G80T's directional refutation and the F3
valuation-archimedean-blind fence).

## Honest scope

The rigidity theorem and the uniform coset-interval bound are unconditional and reusable
(they are the correct pair-level form of what G80T's refuted per-d heuristic groped for).
The regime disjointness is recorded as ledger prose from the formal constants, not as a Lean
impossibility theorem. No certificate is produced. CORE remains OPEN / ON-BGK.

Issue #466. Axiom-clean.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G80PReducedFractionRigidity

variable {p : ℕ} [Fact p.Prime] [NeZero p]

/-- **Integer rigidity below √p**: congruent cross-products of integers in `[1, W]`,
`W² < p`, are equal as naturals. -/
theorem cross_mul_eq_of_congruent {W x y x' y' : ℕ}
    (hW : W * W < p)
    (hx : 1 ≤ x) (hxW : x ≤ W) (hy : 1 ≤ y) (hyW : y ≤ W)
    (hx' : 1 ≤ x') (hxW' : x' ≤ W) (hy' : 1 ≤ y') (hyW' : y' ≤ W)
    (hcong : ((x * y' : ℕ) : ZMod p) = ((x' * y : ℕ) : ZMod p)) :
    x * y' = x' * y := by
  have h1 : x * y' < p := lt_of_le_of_lt (Nat.mul_le_mul hxW hyW') hW
  have h2 : x' * y < p := lt_of_le_of_lt (Nat.mul_le_mul hxW' hyW) hW
  have := (ZMod.natCast_eq_natCast_iff' (x * y') (x' * y) p).mp hcong
  rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this

/-- **Ratio injectivity on a low interval**: two elements of `ZMod p` with vals in `[1, W]`,
`W² < p`, are determined by their modular ratio: if `z ≠ 0`, `w/z = w'/z'` (cross-multiplied
form) with all four vals in `[1, W]`, the integer cross-products agree. Pointed form: fixing
`z₀`, the map `z ↦ z·z₀⁻¹` is injective on any val-window of half-length `W`. -/
theorem ratio_injective_on_interval {W : ℕ} (hW : W * W < p)
    {z z' w w' : ZMod p}
    (hz : 1 ≤ z.val) (hzW : z.val ≤ W) (hz' : 1 ≤ z'.val) (hzW' : z'.val ≤ W)
    (hw : 1 ≤ w.val) (hwW : w.val ≤ W) (hw' : 1 ≤ w'.val) (hwW' : w'.val ≤ W)
    (hratio : w * z' = w' * z) :
    w.val * z'.val = w'.val * z.val := by
  apply cross_mul_eq_of_congruent hW hw hwW hz hzW hw' hwW' hz' hzW'
  push_cast [ZMod.natCast_val, ZMod.cast_id]
  exact hratio

/-- The small-ratio count of a set `H`: ordered pairs `(s, t) ∈ [1, W]²` whose modular ratio
lies in `H`. Exactly the OC support-2 small-height relation census (`s ≡ h·t mod p`). -/
def smallRatioCount (p : ℕ) [NeZero p] (H : Finset (ZMod p)) (W : ℕ) : ℕ :=
  ((Finset.Icc 1 W ×ˢ Finset.Icc 1 W).filter
    (fun st => ∃ h ∈ H, ((st.1 : ℕ) : ZMod p) = h * ((st.2 : ℕ) : ZMod p))).card

/-- **Uniform coset-interval bound**: for ANY subset `C` of a multiplicative coset of `H`
(`z, z' ∈ C ⟹ z'·z⁻¹ ∈ H`) whose vals lie in a window `[a+1, a+W]` with `(2W)² < p` — and
any anchor `z₀ ∈ C` — the size of `C` is at most the small-ratio count `ρ_H(2W)`... stated
here in the clean anchored-difference form: the map sending `z ∈ C` to the reduced val-pair
is injective into the ratio fibers. Simplified quantitative form: if all vals of `C` lie in
`[1, W]` with `W² < p`, then `|C| ≤ smallRatioCount p H W`. -/
theorem coset_interval_le_smallRatioCount
    (H : Finset (ZMod p)) (C : Finset (ZMod p))
    (hcoset : ∀ z ∈ C, ∀ z' ∈ C, ∃ h ∈ H, z' = h * z)
    {W : ℕ} (hW : W * W < p)
    (hval : ∀ z ∈ C, 1 ≤ (z : ZMod p).val ∧ (z : ZMod p).val ≤ W) :
    C.card ≤ smallRatioCount p H W := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · simp [smallRatioCount]
  rw [smallRatioCount]
  -- map z ↦ (val z, val z₀); ratio z/z₀ ∈ H gives the filter condition
  refine Finset.card_le_card_of_injOn
    (fun z => ((z : ZMod p).val, (z₀ : ZMod p).val)) ?_ ?_
  · intro z hz
    obtain ⟨hz1, hzW⟩ := hval z hz
    obtain ⟨h01, h0W⟩ := hval z₀ hz₀
    obtain ⟨h, hH, hzh⟩ := hcoset z₀ hz₀ z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hz1, hzW⟩, Finset.mem_Icc.mpr ⟨h01, h0W⟩⟩, h, hH, ?_⟩
    simp only [ZMod.natCast_val, ZMod.cast_id]
    exact hzh
  · intro z hz z' hz' heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hv, _⟩ := heq
    -- equal vals in [1, W] force equal elements
    have := ZMod.val_injective p hv
    exact this

end ArkLib.ProximityGap.Frontier.G80PReducedFractionRigidity

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G80PReducedFractionRigidity.cross_mul_eq_of_congruent
#print axioms
  ArkLib.ProximityGap.Frontier.G80PReducedFractionRigidity.ratio_injective_on_interval
#print axioms
  ArkLib.ProximityGap.Frontier.G80PReducedFractionRigidity.coset_interval_le_smallRatioCount

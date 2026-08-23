/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BSG_EX_E4d_Ruzsa

/-!
# BSG `E4e` — shape audit of `DRCRuzsaInput` (the corrected residual)

`DRCRuzsaInput` (in `_BSG_EX_E4d_Ruzsa`) is the **correct shape** for the Ruzsa-finish of BSG —
it is consistent with genuine small-doubling sets (unlike the refuted `DRCRefinedReps`) and feeds
the proven `card_diffSet_le_of_ruzsa`. But its *existence* clause has two honest gaps that the
post-averaging data of `_BSG_DRC1` does **not** yet bridge, and which the docstring of
`DRCRuzsaInput` mis-attributes:

1. **`B` is NOT a per-pair common neighbourhood.** The docstring says "`B` a common
   neighbourhood". A per-pair common neighbourhood `B = {b : (a,b),(a',b) ∈ G}` varies with the
   pair, has no fixed cardinality, and is exactly the object the `E4c` countermodel
   (`naiveDiffReps_REFUTED`) shows cannot carry a uniform bound. In the real Tao–Vu/Gowers
   argument `B` is a **single second popular fibre** `leftNbhd A G b₁` (a fixed set), linked to
   `A'' = leftNbhd A G b₀` by the dense cherry structure. The Ruzsa triangle then needs only the
   *cardinality* `#(A'' - B)`, not any per-pair count — which is why the shape is repairable where
   `DRCRefinedReps` was not.

2. **The one-sided bound `#(A'' - B) ≤ s · #A''` is a MOST-pairs → cardinality upgrade.** DRC
   delivers that for *most* `a ∈ A''`, the connection to `B` is good. Converting "most pairs are
   well-connected" into the **set-cardinality** bound `#(A'' - B) ≤ s·#A''` is the genuine deep
   core of BSG (Tao–Vu Lemma 2.30 / the Plünnecke–Petridis path-count). `_BSG_DRC1` proves the
   cherry double-count, the apex averaging, and the bad-pair Markov split — but NOT this upgrade.

This file states the **corrected residual** `DRCRuzsaInputFixed` that the real argument actually
supplies (with `B` an explicit fixed second fibre) and re-proves the consumer reduction from the
fixed residual to confirm the shape still discharges `BareDRCExtract`.

The naive *one-sided per-pair* core — "every pair in `fibre b₀ × fibre b₁` has `≥ #A/s` common
neighbours ⟹ `#(fibre b₀ − fibre b₁) ≤ s·#(fibre b₀)`" — is **machine-refuted** in
`_BSG_EX_E4e_PathCount` (`pathCountToDiffCard_REFUTED`: a tiny `N₀` against a large `N₁` produces
up to `#N₁` distinct differences that `s·#N₀` cannot bound). The genuine, *symmetric* and
**provable** path-count core `#(N₀−N₁)·#A ≤ s·#(N₀−A)·#(N₁−A)` is proven there
(`pathCount_card_bound`); the residual after it (calibrating the symmetric bound to the one-sided
Ruzsa input against the post-averaging sizes) is named `RelativeDiffCalibration`, definitionally
identical to `DRCRuzsaInputFixed`.

All declarations here are either `def … : Prop` (named obligations, NOT claimed proven) or the
consumer reduction `bareDRCExtract_of_ruzsaInputFixed` (genuinely proven, axiom-clean).

## References
* W. T. Gowers, *A new proof of Szemerédi's theorem for AP4* (1998), §6.
* T. Tao, V. Vu, *Additive Combinatorics*, Cambridge (2006), Theorem 2.29, Lemma 2.30.
-/

open Finset
open scoped BigOperators Pointwise

namespace Finset.BSG

/-! ## The corrected residual: `B` an explicit second popular fibre -/

/-- **`DRCRuzsaInputFixed` — the corrected-shape residual.** Identical Ruzsa-ready conclusion to
`DRCRuzsaInput`, but it *names the auxiliary set honestly*: `B` is a left-neighbourhood
`leftNbhd A G b₁` of a second vertex `b₁ ∈ A` (a fixed set, not a per-pair common neighbourhood).
This is exactly the object the real Tao–Vu/Gowers BSG argument produces. The two Ruzsa-ready facts
(`#(A'' - B) ≤ s·#A''`, `#A'' ≤ s·#B`) and the size bound are unchanged, so it still discharges
`BareDRCExtract` via `card_diffSet_le_of_ruzsa`. -/
def DRCRuzsaInputFixed (C₁ s_C s_c : ℕ) : Prop :=
  ∀ {α : Type} [inst : AddCommGroup α] [inst2 : DecidableEq α],
    ∀ (A : Finset α) (K : ℕ) (G : Finset (α × α)) (b₀ : α),
      0 < K → A.Nonempty → G ⊆ A ×ˢ A → b₀ ∈ A →
      #A ^ 2 ≤ 4 * K ^ 2 * #G →
      #A ^ 4 ≤ 16 * K ^ 4 * (#A * (∑ b ∈ A, rDeg A G b ^ 2)) →
      #A ≤ 4 * K ^ 2 * rDeg A G b₀ →
      ∃ (A'' : Finset α) (b₁ : α) (s : ℕ),
        b₁ ∈ A ∧
        A'' ⊆ leftNbhd A G b₀ ∧ A''.Nonempty ∧ (leftNbhd A G b₁).Nonempty ∧
        s ≤ s_C * K ^ s_c ∧
        C₁ * K * #A'' ≥ #A ∧
        #(A'' - leftNbhd A G b₁) ≤ s * #A'' ∧
        #A'' ≤ s * #(leftNbhd A G b₁)

/-- **`DRCRuzsaInputFixed → DRCRuzsaInput`.** The fixed-shape residual (explicit second fibre `B`)
trivially implies the abstract one: take `B := leftNbhd A G b₁`. Hence proving the corrected,
honestly-named residual suffices for the whole BGK chain. (Proven, axiom-clean.) -/
theorem drcRuzsaInput_of_fixed {C₁ s_C s_c : ℕ} (h : DRCRuzsaInputFixed C₁ s_C s_c) :
    DRCRuzsaInput C₁ s_C s_c := by
  intro α _ _ A K G b₀ hK hA hGsub hb₀ hdense hcherry hgood
  obtain ⟨A'', b₁, s, _hb₁, hsub, hne, hBne, hsbd, hsize, hdiff, hcomp⟩ :=
    h A K G b₀ hK hA hGsub hb₀ hdense hcherry hgood
  exact ⟨A'', leftNbhd A G b₁, s, hsub, hne, hBne, hsbd, hsize, hdiff, hcomp⟩

/-- **`BareDRCExtract` from the corrected residual** (composition; proven axiom-clean). -/
theorem bareDRCExtract_of_ruzsaInputFixed {C₁ s_C s_c : ℕ} (h : DRCRuzsaInputFixed C₁ s_C s_c) :
    BareDRCExtract C₁ (s_C ^ 3) (3 * s_c) :=
  bareDRCExtract_of_ruzsaInput (drcRuzsaInput_of_fixed h)

/-! ## The remaining core lives in `_BSG_EX_E4e_PathCount`

`_BSG_DRC1` already proves: the cherry double-count `∑_b deg² = ∑_{pairs} cn`
(`sum_rDeg_sq_eq_sum_commonNeighbors`), the apex averaging giving a large fibre
(`exists_rDeg_ge_avg`), and the Markov split isolating the good (well-connected) pairs
(`sum_commonNeighbors_goodPairs_ge`). The single deep step still missing is the conversion of the
good-pair richness into a **difference-set cardinality** bound. The *one-sided per-pair* form of
that conversion is **false** (`pathCountToDiffCard_REFUTED` in `_BSG_EX_E4e_PathCount`); the correct
*symmetric* path-count `#(N₀−N₁)·#A ≤ s·#(N₀−A)·#(N₁−A)` is **proven** there
(`pathCount_card_bound`), and the genuine remaining gap — calibrating it to the one-sided Ruzsa
input — is the named `RelativeDiffCalibration` (= `DRCRuzsaInputFixed`). -/

end Finset.BSG

-- Axiom audit (expected: propext, Classical.choice, Quot.sound — and NO sorryAx — for the
-- two PROVEN consumer reductions; the two `def`s are obligations, not theorems).
#print axioms Finset.BSG.drcRuzsaInput_of_fixed
#print axioms Finset.BSG.bareDRCExtract_of_ruzsaInputFixed

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZJLR26CapacityPinAssembly
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCount
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBoundsProofs

/-!
# ZT413: the T4.13 ε-packaging weld — `ε_mca ≤ m·n/q` from a degree-1 curve cover (#334/#466)

**The named gap this attacks.**  The T4.13 ε-packaging residual
`gg25_subspaceDesign_epsMCA_residual` (`CapacityBoundsProofs.lean:193`) asks, for every
τ-subspace-design code `C` and every `t > 0`, for the [GG25 Cor 4.9] budget shape

  `ε_mca(C, 1 − τ(t+1) − 3/(2t)) ≤ (t·n + 4t²)/|F|`.

The `_ZJLR26CapacityPinAssembly.lean` chain (landed earlier today) produces — conditional on
the ONE deep residual `CZ25SpanBound'` — the **curve list-size cover**
`CurveListSizeLe C ℓ δ (L + ℓ)` (`subspaceDesign_curveListSizeLe_capacity_of_spanBound`).
What was missing is the quantification bridge from that per-`(u,f)` curve cover to the
`epsMCA` sup over word stacks with per-`γ` witness sets (`mcaEvent`, ABF26 D4.3).  This file
builds that bridge and lands the ε-weld:

* `mcaBadCount_le_of_curveListSizeLe` — **the new arrow (unconditional, alphabet-generic)**:
  if `C` has degree-1 curve list-size `≤ m` at radius `δ`, then EVERY line stack `(u₀, u₁)`
  has at most `m·n` bad scalars: `mcaBadCount C δ u₀ u₁ ≤ m·|ι|`.  Proof: each bad `γ` has an
  `mcaEvent` witness set `S_γ` and codeword `w_γ` agreeing with the line on `S_γ`; the cover
  assignment forces `w_γ = cs_γ(γ)` for one of `≤ m` codeword lines `cs_γ`; the
  `¬pairJointAgreesOn` clause yields a position `i_γ ∈ S_γ` where the pair `cs_γ` does NOT
  match `(u₀, u₁)` yet the evaluated lines DO agree — and for a fixed codeword line and a
  fixed non-matching position, at most ONE scalar can make the evaluated lines agree there
  (degree-1 Vandermonde cancellation).  So `γ ↦ (cs_γ, i_γ)` is injective into
  `(≤ m curves) × (n positions)`.
* `epsMCA_le_of_curveListSizeLe` — the `ε_mca C δ ≤ m·n/q` packaging (unconditional).
* `subspaceDesign_epsMCA_le_capacity_of_spanBound` — composition with the ZJLR26 assembly:
  for every τ-subspace-design code, conditional ONLY on `CZ25SpanBound'` (plus the assembly's
  arithmetic side conditions `hL`/`hrad`/`hq`), `ε_mca(C, δ) ≤ (L+1)·n/q` with
  `L ≈ (1−τ)/η` the CZ25 capacity list cap.
* `subspaceDesign_epsMCA_gg25_of_spanBound` — **the T4.13 ε-packaging at any instance**:
  under the same conditions plus the budget comparison `(L+1)·n ≤ t·n + 4t²`, the LITERAL
  per-instance Prop `subspaceDesign_epsMCA_gg25 s τ C h t ht` holds — the exact statement
  the residual quantifies over, with the exact GG25 radius `(1 − τ(t+1) − 3/(2t)).toNNReal`
  and the exact `(t·n + 4t²)/|F|` bound.
* `gg25_residual_of_parameter_supply` — **the literal-residual reduction**: the named
  residual `gg25_subspaceDesign_epsMCA_residual` itself follows from a per-instance
  parameter supply (`η`, `L` with `CZ25SpanBound'` + the four arithmetic side conditions).
* `frs_epsMCA_capacity_gg25_of_spanBound_inter_eta` — **the folded-RS capacity pin,
  end-to-end**: for an order/inter-orbit admissible folded-RS code, the public T4.14 Prop
  `frs_epsMCA_capacity_gg25` conditional ONLY on `CZ25SpanBound'` at the sharp CZ25 profile
  plus explicit arithmetic side conditions — the first complete route from the deep residual
  to the public capacity endpoint with no `gg25_subspaceDesign_epsMCA_residual` hypothesis.

**Honest scope (read before citing).**
* `mcaBadCount_le_of_curveListSizeLe` and `epsMCA_le_of_curveListSizeLe` are UNCONDITIONAL
  in-tree theorems; the curve-cover hypothesis is genuine input (for plain RS above Johnson
  it is the OPEN `RSCurveListSizeResidual` / BCHKS Conj 1.12 list-size wall; nothing here
  touches the plain-RS δ* prize core).
* The design-arm results are conditional on `CZ25SpanBound'`
  (`ListDecoding/CZ25SpanDimension.lean`), consumed VISIBLY as `hSB` — never silently.
* The arithmetic side conditions are explicit hypotheses.  The radius-fit condition `hrad`
  inherits the ℓ = 1 peeling factor: `2·⌊δ_t·n⌋ ≤ (1 − τ(⌊1/η⌋) − η)·n`, i.e. the GG25
  radius `δ_t = 1 − τ(t+1) − 3/(2t)` must sit at or below HALF the CZ25 capacity radius.
  At parameter points where `δ_t` exceeds that, these side conditions are NOT dischargeable
  and the full-band T4.13 statement remains open.  This file is therefore a strict
  REDUCTION of the ε-packaging residual (to `CZ25SpanBound'` + explicit arithmetic), NOT a
  full discharge of `gg25_subspaceDesign_epsMCA_residual`; the remaining named gap beyond
  `CZ25SpanBound'` is the half-radius restriction (a sharper curve cover at radius `δ_t`
  itself — e.g. a peeling engine paying no `(ℓ+1)` factor — would lift it through the SAME
  weld proved here).
* No `sorry`, no new axioms; every `#print axioms` below must report exactly
  `[propext, Classical.choice, Quot.sound]`.

**Provenance.**  `CurveListSizeLe`/`CurveAssignment` (`GG25CurveDecodFromListSize.lean`),
`mcaEvent`/`pairJointAgreesOn` (`Errors.lean`), `mcaBadCount`/`epsMCA_eq_iSup_mcaBadCount`
(`MCABadCount.lean`), `subspaceDesign_curveListSizeLe_capacity_of_spanBound`
(`Frontier/_ZJLR26CapacityPinAssembly.lean`), `subspaceDesign_epsMCA_gg25(_of_bound)`
(`CapacityBounds.lean`), `frs_epsMCA_capacity_gg25_of_orderOf_ge_of_inter_eta`
(`CapacityBoundsAdmissible.lean`), `frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_inter`
(`ReedSolomon/AdmissibleSubspaceDesign.lean`).

## References
* [GG25] Guo–Guruswami, ePrint 2025/2054, Thm 3.3 / Cor 4.9.
* [ABF26] Arnon–Boneh–Fenzi, Definition 4.3, Theorem 4.13/4.14.
* [JLR26] Jeronimo–Liu–Rajpal, arXiv 2601.10047, §5.
Issue #334 (Tier-3 folded pin), campaign #466.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Finset Code
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.ZT413Packaging

open CodingTheory
open _root_.ProximityGap
open ArkLib.ProximityGap.Frontier.ZJLR26Assembly

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ### §0 Degree-1 curve arithmetic helpers -/

/-- Evaluating a two-row curve stack: `∑_{j<2} γ^j • v j = v 0 + γ • v 1` pointwise. -/
private theorem curve_eval_two (v : Fin (1 + 1) → ι → A) (γ : F) (i : ι) :
    (∑ j : Fin (1 + 1), γ ^ (j : ℕ) • v j i) = v 0 i + γ • v 1 i := by
  simp [Fin.sum_univ_succ, Fin.succ_zero_eq_one]

/-- The tested degree-1 curve of the stack `![u₀, u₁]` IS the affine line `u₀ + γ • u₁`. -/
private theorem line_curve_eq (u₀ u₁ : ι → A) (γ : F) :
    (fun i => ∑ j : Fin (1 + 1), γ ^ (j : ℕ) • (![u₀, u₁] : Fin (1 + 1) → ι → A) j i)
      = fun i => u₀ i + γ • u₁ i := by
  funext i
  rw [curve_eval_two]
  simp

/-- Agreement on a set of `≥ (1−δ)·n` positions forces relative Hamming distance `≤ δ`. -/
private theorem relHam_le_of_agree_on_large
    {δ : ℝ≥0} {S : Finset ι} {x w : ι → A}
    (hScard : ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ ((S.card : ℕ) : ℝ≥0))
    (hagree : ∀ i ∈ S, w i = x i) :
    ((relHammingDist x w : ℚ≥0) : ℝ≥0) ≤ δ := by
  classical
  by_cases hδ1 : (1 : ℝ≥0) ≤ δ
  · refine le_trans ?_ hδ1
    exact_mod_cast relHammingDist_le_one (u := x) (v := w)
  · push Not at hδ1
    have hnpos : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by exact_mod_cast Fintype.card_pos
    have hsub : Finset.univ.filter (fun i => x i ≠ w i) ⊆ Sᶜ := by
      intro i hi
      rcases Finset.mem_filter.mp hi with ⟨-, hne⟩
      rw [Finset.mem_compl]
      exact fun hiS => hne (hagree i hiS).symm
    have hint : hammingDist x w ≤ Fintype.card ι - S.card := by
      calc hammingDist x w
          = (Finset.univ.filter (fun i => x i ≠ w i)).card := rfl
        _ ≤ (Sᶜ).card := Finset.card_le_card hsub
        _ = Fintype.card ι - S.card := Finset.card_compl S
    have hcast : ((relHammingDist x w : ℚ≥0) : ℝ≥0)
        = (hammingDist x w : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
      simp only [relHammingDist, NNRat.cast_div, NNRat.cast_natCast]
    rw [hcast, div_le_iff₀ hnpos]
    calc (hammingDist x w : ℝ≥0)
        ≤ ((Fintype.card ι - S.card : ℕ) : ℝ≥0) := by exact_mod_cast hint
      _ = (Fintype.card ι : ℝ≥0) - ((S.card : ℕ) : ℝ≥0) :=
          Nat.cast_tsub (Fintype.card ι) S.card
      _ ≤ δ * (Fintype.card ι : ℝ≥0) := by
          rw [tsub_le_iff_right]
          calc (Fintype.card ι : ℝ≥0)
              = (1 : ℝ≥0) * (Fintype.card ι : ℝ≥0) := (one_mul _).symm
            _ = (δ + (1 - δ)) * (Fintype.card ι : ℝ≥0) := by
                rw [add_tsub_cancel_of_le (le_of_lt hδ1)]
            _ = δ * (Fintype.card ι : ℝ≥0) + ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) :=
                add_mul _ _ _
            _ ≤ δ * (Fintype.card ι : ℝ≥0) + ((S.card : ℕ) : ℝ≥0) :=
                add_le_add le_rfl hScard

/-! ### §1 The new arrow: line bad-count ≤ m·n from a degree-1 curve cover -/

open Classical in
/-- **The ε-weld core (unconditional, alphabet-generic).**  If the `F`-submodule code
`C ≤ (ι → A)` has degree-1 curve list-size `≤ m` at radius `δ` (`CurveListSizeLe`, the
abstracted [GG25]/[JLR26] cover), then EVERY line stack `(u₀, u₁)` carries at most `m·|ι|`
MCA-bad scalars.

Proof (the quantification bridge that was the open packaging step): for each bad `γ` the
`mcaEvent` witness gives `S_γ` (`|S_γ| ≥ (1−δ)n`) and a codeword `w_γ` agreeing with the
line `u₀ + γ•u₁` on `S_γ`, with NO codeword pair matching `(u₀, u₁)` on `S_γ`.  Feeding
`f := (γ ↦ w_γ)` to the cover produces an assignment `γ ↦ cs_γ` into `≤ m` codeword lines
with `w_γ = cs_γ 0 + γ • cs_γ 1` exactly.  The no-pair clause yields `i_γ ∈ S_γ` where
`(cs_γ 0, cs_γ 1) ≠ (u₀, u₁)` pointwise, yet the evaluated lines agree at `i_γ` (both equal
`w_γ i_γ`).  For a FIXED curve `cs` and FIXED position `i` with `(cs 0 i, cs 1 i) ≠
(u₀ i, u₁ i)`, at most one scalar `γ` satisfies `u₀ i + γ•u₁ i = cs 0 i + γ•cs 1 i`
(subtract two such scalar instances and cancel `(γ₁−γ₂)•`).  Hence `γ ↦ (cs_γ, i_γ)` is
injective into `(≤ m) × n` pairs. -/
theorem mcaBadCount_le_of_curveListSizeLe
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (m : ℕ)
    (hcover : CurveListSizeLe (F := F) ((C : Set (ι → A))) 1 δ m)
    (u₀ u₁ : ι → A) :
    mcaBadCount (F := F) ((C : Set (ι → A))) δ u₀ u₁ ≤ m * Fintype.card ι := by
  -- §a Choose per-scalar `mcaEvent` witness data (bad scalars get real data, others `(∅,0)`).
  have hex : ∀ γ : F, ∃ (S : Finset ι) (w : ι → A), w ∈ (C : Set (ι → A)) ∧
      (mcaEvent ((C : Set (ι → A))) δ u₀ u₁ γ →
        (((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ ((S.card : ℕ) : ℝ≥0) ∧
          (∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧
          ¬ pairJointAgreesOn ((C : Set (ι → A))) S u₀ u₁)) := by
    intro γ
    by_cases hγ : mcaEvent ((C : Set (ι → A))) δ u₀ u₁ γ
    · obtain ⟨S, hScard, ⟨w, hwC, hwS⟩, hno⟩ := hγ
      exact ⟨S, w, hwC, fun _ => ⟨hScard, hwS, hno⟩⟩
    · exact ⟨∅, 0, C.zero_mem, fun hev => absurd hev hγ⟩
  choose Sf wf hwfC hbad using hex
  -- §b Every bad scalar is a close seed of the stack `![u₀,u₁]` with plan `wf`.
  have hclose : ∀ γ : F, mcaEvent ((C : Set (ι → A))) δ u₀ u₁ γ →
      γ ∈ curveCloseSet δ (![u₀, u₁] : Fin (1 + 1) → ι → A) wf := by
    intro γ hγ
    obtain ⟨hScard, hagree, -⟩ := hbad γ hγ
    simp only [curveCloseSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [line_curve_eq u₀ u₁ γ]
    exact relHam_le_of_agree_on_large hScard hagree
  -- §c The cover assignment: `≤ m` distinct codeword lines explain `wf` on the close set.
  obtain ⟨asgn, hasgn⟩ := hcover (![u₀, u₁] : Fin (1 + 1) → ι → A) wf hwfC
  -- §d For each bad scalar, a witness position where the assigned pair does NOT match.
  have hex2 : ∀ γ : F, ∃ i : ι, mcaEvent ((C : Set (ι → A))) δ u₀ u₁ γ →
      (i ∈ Sf γ ∧
        ¬ (asgn.chooseCurve γ 0 i = u₀ i ∧ asgn.chooseCurve γ 1 i = u₁ i)) := by
    intro γ
    by_cases hγ : mcaEvent ((C : Set (ι → A))) δ u₀ u₁ γ
    · obtain ⟨-, -, hno⟩ := hbad γ hγ
      have hexi : ∃ i ∈ Sf γ,
          ¬ (asgn.chooseCurve γ 0 i = u₀ i ∧ asgn.chooseCurve γ 1 i = u₁ i) := by
        by_contra hcon
        push Not at hcon
        exact hno ⟨asgn.chooseCurve γ 0, asgn.mem_code γ 0,
          asgn.chooseCurve γ 1, asgn.mem_code γ 1, hcon⟩
      obtain ⟨i, hiS, hino⟩ := hexi
      exact ⟨i, fun _ => ⟨hiS, hino⟩⟩
    · exact ⟨Classical.arbitrary ι, fun hev => absurd hev hγ⟩
  choose pos hpos using hex2
  -- §e At the witness position the evaluated lines agree (both equal `wf γ` there).
  have hagreeAt : ∀ γ : F, mcaEvent ((C : Set (ι → A))) δ u₀ u₁ γ →
      u₀ (pos γ) + γ • u₁ (pos γ)
        = asgn.chooseCurve γ 0 (pos γ) + γ • asgn.chooseCurve γ 1 (pos γ) := by
    intro γ hγ
    obtain ⟨-, hagree, -⟩ := hbad γ hγ
    obtain ⟨hiS, -⟩ := hpos γ hγ
    have h1 : wf γ (pos γ) = u₀ (pos γ) + γ • u₁ (pos γ) := hagree _ hiS
    have h2 := congrFun (asgn.passes_through γ (hclose γ hγ)) (pos γ)
    rw [h1, curve_eval_two] at h2
    exact h2
  -- §f The injection `γ ↦ (cs_γ, i_γ)` and the final count.
  rw [mcaBadCount]
  have hmaps : ∀ γ ∈ Finset.univ.filter
      (fun γ : F => mcaEvent ((C : Set (ι → A))) δ u₀ u₁ γ),
      (asgn.chooseCurve γ, pos γ) ∈
        ((curveCloseSet δ (![u₀, u₁] : Fin (1 + 1) → ι → A) wf).image asgn.chooseCurve)
          ×ˢ (Finset.univ : Finset ι) := by
    intro γ hγ
    have hev := (Finset.mem_filter.mp hγ).2
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ (hclose γ hev), Finset.mem_univ _⟩
  have hinj : Set.InjOn (fun γ : F => (asgn.chooseCurve γ, pos γ))
      ↑(Finset.univ.filter (fun γ : F => mcaEvent ((C : Set (ι → A))) δ u₀ u₁ γ)) := by
    intro γ₁ hγ₁ γ₂ hγ₂ hEq
    have hev₁ := (Finset.mem_filter.mp (Finset.mem_coe.mp hγ₁)).2
    have hev₂ := (Finset.mem_filter.mp (Finset.mem_coe.mp hγ₂)).2
    by_contra hne12
    have hcs : asgn.chooseCurve γ₁ = asgn.chooseCurve γ₂ := congrArg Prod.fst hEq
    have hposEq : pos γ₁ = pos γ₂ := congrArg Prod.snd hEq
    obtain ⟨-, hino⟩ := hpos γ₁ hev₁
    have e1 := hagreeAt γ₁ hev₁
    have e2 := hagreeAt γ₂ hev₂
    rw [← hcs, ← hposEq] at e2
    set i := pos γ₁ with hi
    set c₀ := asgn.chooseCurve γ₁ 0 i with hc₀
    set c₁ := asgn.chooseCurve γ₁ 1 i with hc₁
    -- Subtract the two line agreements and cancel `(γ₁ − γ₂)•`.
    have e3 : (γ₁ - γ₂) • u₁ i = (γ₁ - γ₂) • c₁ := by
      have h12 := congrArg₂ (fun x y : A => x - y) e1 e2
      simpa [add_sub_add_left_eq_sub, ← sub_smul] using h12
    have hne' : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hne12
    have hu1 : u₁ i = c₁ := by
      have h4 := congrArg (fun x : A => (γ₁ - γ₂)⁻¹ • x) e3
      simpa [smul_smul, inv_mul_cancel₀ hne'] using h4
    have hu0 : u₀ i = c₀ := by
      have e1' : u₀ i + γ₁ • u₁ i = c₀ + γ₁ • u₁ i := by
        rw [e1, hu1]
      exact add_right_cancel e1'
    exact hino ⟨hu0.symm, hu1.symm⟩
  calc (Finset.univ.filter
        (fun γ : F => mcaEvent ((C : Set (ι → A))) δ u₀ u₁ γ)).card
      ≤ (((curveCloseSet δ (![u₀, u₁] : Fin (1 + 1) → ι → A) wf).image asgn.chooseCurve)
          ×ˢ (Finset.univ : Finset ι)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = ((curveCloseSet δ (![u₀, u₁] : Fin (1 + 1) → ι → A) wf).image
          asgn.chooseCurve).card * Fintype.card ι := by
        rw [Finset.card_product, Finset.card_univ]
    _ ≤ m * Fintype.card ι := Nat.mul_le_mul_right _ hasgn

open Classical in
/-- **The `ε_mca ≤ m·n/q` packaging (unconditional).**  A degree-1 curve list-size cover
`≤ m` at radius `δ` bounds the mutual-correlated-agreement error by `m·|ι| / |F|`.  This is
the [GG25 Cor 4.9]-shaped ε-weld: with `m = O(t)` it is the `t·n/q` leading term of the
T4.13 budget `(t·n + 4t²)/q`. -/
theorem epsMCA_le_of_curveListSizeLe
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (m : ℕ)
    (hcover : CurveListSizeLe (F := F) ((C : Set (ι → A))) 1 δ m) :
    epsMCA (F := F) ((C : Set (ι → A))) δ
      ≤ ((m * Fintype.card ι : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  rw [epsMCA_eq_iSup_mcaBadCount]
  refine ENNReal.div_le_div_right (iSup_le fun u => ?_) _
  exact_mod_cast mcaBadCount_le_of_curveListSizeLe C δ m hcover (u 0) (u 1)

/-! ### §2 Composition with the ZJLR26 capacity assembly (conditional on `CZ25SpanBound'`) -/

/-- **Design-code `ε_mca` at capacity, conditional ONLY on `CZ25SpanBound'`.**  For every
τ-subspace-design code `C`, radius `δ`, and CZ25 capacity parameters `(η, L)` satisfying the
assembly's arithmetic side conditions, `ε_mca(C, δ) ≤ (L+1)·n / q`.  The curve cover comes
from `subspaceDesign_curveListSizeLe_capacity_of_spanBound` at `ℓ = 1`; the weld is §1. -/
theorem subspaceDesign_epsMCA_le_capacity_of_spanBound
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hSB : CZ25SpanBound' s τ C h η hη)
    (δ : ℝ≥0) {L : ℕ}
    (hL : (1 - τ (Nat.floor (1 / η))) / η ≤ (L : ℝ))
    (hrad : (((1 + 1) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ : ℕ) : ℝ)
      ≤ (1 - τ (Nat.floor (1 / η)) - η) * Fintype.card ι)
    (hq : (L + 1) * L * 1 < Fintype.card F) :
    epsMCA (F := F) ((C : Set (ι → Fin s → F))) δ
      ≤ (((L + 1) * Fintype.card ι : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_of_curveListSizeLe C δ (L + 1)
    (subspaceDesign_curveListSizeLe_capacity_of_spanBound s τ C h η hη hSB 1 δ hL hrad hq)

/-! ### §3 The T4.13 ε-packaging at any instance -/

/-- **T4.13 [GG25 Cor 4.9] at any instance, from `CZ25SpanBound'` + arithmetic.**  For a
τ-subspace-design code `C` and `t > 0`: given the deep residual `CZ25SpanBound'` at some
capacity parameter `η` with list cap `L`, the radius fit `2·⌊δ_t·n⌋ ≤ (1−τ(⌊1/η⌋)−η)·n` at
the GG25 radius `δ_t = (1 − τ(t+1) − 3/(2t)).toNNReal`, the field-size condition, and the
budget comparison `(L+1)·n ≤ t·n + 4t²`, the LITERAL per-instance T4.13 Prop
`subspaceDesign_epsMCA_gg25 s τ C h t ht` holds:

  `ε_mca(C, 1 − τ(t+1) − 3/(2t)) ≤ (t·n + 4t²)/|F|`.

This is the exact statement quantified by `gg25_subspaceDesign_epsMCA_residual`
(`CapacityBoundsProofs.lean:193`), derived — for the first time in-tree — from the single
deep input `CZ25SpanBound'` plus explicit arithmetic side conditions.  See the module
docstring for the honest scope of `hrad` (the half-radius restriction). -/
theorem subspaceDesign_epsMCA_gg25_of_spanBound
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (t : ℕ) (ht : 0 < t)
    (η : ℝ) (hη : 0 < η) (hSB : CZ25SpanBound' s τ C h η hη)
    {L : ℕ}
    (hL : (1 - τ (Nat.floor (1 / η))) / η ≤ (L : ℝ))
    (hrad : (((1 + 1) * ⌊(1 - τ (t + 1) - 3 / (2 * t)).toNNReal
          * (Fintype.card ι : ℝ≥0)⌋₊ : ℕ) : ℝ)
      ≤ (1 - τ (Nat.floor (1 / η)) - η) * Fintype.card ι)
    (hq : (L + 1) * L * 1 < Fintype.card F)
    (hM : (((L + 1) * Fintype.card ι : ℕ) : ℝ)
      ≤ (t : ℝ) * Fintype.card ι + 4 * t ^ 2) :
    subspaceDesign_epsMCA_gg25 s τ C h t ht := by
  apply subspaceDesign_epsMCA_gg25_of_bound
  have h1 := subspaceDesign_epsMCA_le_capacity_of_spanBound s τ C h η hη hSB
    ((1 - τ (t + 1) - 3 / (2 * t)).toNNReal) hL hrad hq
  refine le_trans h1 ?_
  have hq0 : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [ENNReal.ofReal_div_of_pos hq0, ENNReal.ofReal_natCast]
  refine ENNReal.div_le_div_right ?_ _
  rw [← ENNReal.ofReal_natCast ((L + 1) * Fintype.card ι)]
  exact ENNReal.ofReal_le_ofReal hM

/-- **The literal-residual reduction.**  The named T4.13 ε-packaging residual
`gg25_subspaceDesign_epsMCA_residual` follows from a per-instance parameter supply: for
every design instance and every `t > 0`, SOME capacity parameter `η` and list cap `L`
satisfying `CZ25SpanBound'` and the four arithmetic side conditions.  This pins the residual
strictly below the deep input: everything except `CZ25SpanBound'` and the parameter
arithmetic is now a proven in-tree theorem. -/
theorem gg25_residual_of_parameter_supply
    (hsupply : ∀ (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
        (h : IsSubspaceDesign s τ C) (t : ℕ), 0 < t →
      ∃ (η : ℝ) (hη : 0 < η) (L : ℕ),
        CZ25SpanBound' s τ C h η hη ∧
        (1 - τ (Nat.floor (1 / η))) / η ≤ (L : ℝ) ∧
        (((1 + 1) * ⌊(1 - τ (t + 1) - 3 / (2 * t)).toNNReal
            * (Fintype.card ι : ℝ≥0)⌋₊ : ℕ) : ℝ)
          ≤ (1 - τ (Nat.floor (1 / η)) - η) * Fintype.card ι ∧
        (L + 1) * L * 1 < Fintype.card F ∧
        (((L + 1) * Fintype.card ι : ℕ) : ℝ)
          ≤ (t : ℝ) * Fintype.card ι + 4 * t ^ 2) :
    gg25_subspaceDesign_epsMCA_residual (ι := ι) (F := F) := by
  intro s τ C h t ht
  obtain ⟨η, hη, L, hSB, hL, hrad, hq, hM⟩ := hsupply s τ C h t ht
  exact subspaceDesign_epsMCA_gg25_of_spanBound s τ C h t ht η hη hSB hL hrad hq hM

/-! ### §4 The folded-RS capacity endpoint -/

/-- **The folded-RS capacity pin, end-to-end from `CZ25SpanBound'`.**  For an
order/inter-orbit admissible folded-RS code, the PUBLIC T4.14 Prop
`frs_epsMCA_capacity_gg25` (the `ε_mca(FRS, 1−ρ−η) ≤ 2n/(η|F|) + 24/(η³|F|)` capacity
statement) holds conditional ONLY on `CZ25SpanBound'` at the sharp CZ25 τ-profile, plus the
explicit arithmetic side conditions of the §3 weld and the standard T4.14 eta-route
identifications.  This replaces the previous route through the UNPROVEN global hypothesis
`gg25_subspaceDesign_epsMCA_residual` (`frs_epsMCA_capacity_gg25_proven_of_t413`): the T4.13
supply is now the §3 THEOREM at the FRS instance. -/
theorem frs_epsMCA_capacity_gg25_of_spanBound_inter_eta
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (ηg : ℝ) (hηg_pos : 0 < ηg) (hηg_lt : ηg < 1) (hs_gt : (s : ℝ) > 16 / ηg ^ 2)
    (P : Finset F) (hP_dom : ∀ i : ι, domain i ∈ P)
    (h0 : (0 : F) ∉ P) (hω0 : ω ≠ 0) (hs_order : s ≤ orderOf ω)
    (hinter : ∀ α ∈ P, ∀ β ∈ P, α ≠ β → ∀ i : ℕ, i < s → α * ω ^ i ≠ β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (ηc : ℝ) (hηc : 0 < ηc)
    (hSB : CZ25SpanBound' s
      (fun r : ℕ ↦ if r ∈ Finset.Icc 1 s then
          (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (r : ℝ) + 1) else 1)
      (ReedSolomon.Folded.frsCode domain k s ω)
      (frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_inter
        domain k s ω P hP_dom h0 hω0 hs_order hinter hkLs hkord) ηc hηc)
    {L : ℕ}
    (hL : (1 - (if Nat.floor (1 / ηc) ∈ Finset.Icc 1 s then
          (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (Nat.floor (1 / ηc) : ℝ) + 1)
        else 1)) / ηc ≤ (L : ℝ))
    (hrad : (((1 + 1) * ⌊(1 - (if t + 1 ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - ((t + 1 : ℕ) : ℝ) + 1)
          else 1) - 3 / (2 * t)).toNNReal * (Fintype.card ι : ℝ≥0)⌋₊ : ℕ) : ℝ)
      ≤ (1 - (if Nat.floor (1 / ηc) ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (Nat.floor (1 / ηc) : ℝ) + 1)
          else 1) - ηc) * Fintype.card ι)
    (hq : (L + 1) * L * 1 < Fintype.card F)
    (hM : (((L + 1) * Fintype.card ι : ℕ) : ℝ)
      ≤ (t : ℝ) * Fintype.card ι + 4 * t ^ 2)
    (hη : ηg = (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card ι + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / ηg) :
    frs_epsMCA_capacity_gg25 domain k s ω ηg hηg_pos hηg_lt hs_gt := by
  refine frs_epsMCA_capacity_gg25_of_orderOf_ge_of_inter_eta
    domain k s ω ηg hηg_pos hηg_lt hs_gt P hP_dom h0 hω0 hs_order hinter hkLs hkord
    t ht hts ?_ hη htη
  exact subspaceDesign_epsMCA_gg25_of_spanBound s
    (fun r : ℕ ↦ if r ∈ Finset.Icc 1 s then
        (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (r : ℝ) + 1) else 1)
    (ReedSolomon.Folded.frsCode domain k s ω)
    (frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_inter
      domain k s ω P hP_dom h0 hω0 hs_order hinter hkLs hkord)
    t ht ηc hηc hSB hL hrad hq hM

end ArkLib.ProximityGap.Frontier.ZT413Packaging

-- Axiom audit: every theorem must report exactly `[propext, Classical.choice, Quot.sound]`
-- (no `sorryAx`, no `native_decide`, no new axioms).
#print axioms ArkLib.ProximityGap.Frontier.ZT413Packaging.mcaBadCount_le_of_curveListSizeLe
#print axioms ArkLib.ProximityGap.Frontier.ZT413Packaging.epsMCA_le_of_curveListSizeLe
#print axioms
  ArkLib.ProximityGap.Frontier.ZT413Packaging.subspaceDesign_epsMCA_le_capacity_of_spanBound
#print axioms
  ArkLib.ProximityGap.Frontier.ZT413Packaging.subspaceDesign_epsMCA_gg25_of_spanBound
#print axioms ArkLib.ProximityGap.Frontier.ZT413Packaging.gg25_residual_of_parameter_supply
#print axioms
  ArkLib.ProximityGap.Frontier.ZT413Packaging.frs_epsMCA_capacity_gg25_of_spanBound_inter_eta

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCADeltaStarHighRateFamily

/-!
# The witness-counting upper engine (#357): every bad scalar owns a witness set

`MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set` is the campaign's *lower* engine:
`G` bad scalars price `ε_mca ≥ |G|/q`. This file builds the matching **upper engine** from
the structural obstruction `unique_bad_gamma_common_witness`: two distinct bad scalars can
never share a witness set, so the bad-scalar count of any stack is at most the number of
*admissible witness sets* at that radius:

  `ε_mca(C, δ) ≤ #{S ⊆ ι : |S| ≥ (1−δ)·n} / q`     (`epsMCA_le_witnessFamily_card_div`),

for **every** linear code over **every** finite field at **every** radius. The
witness-family count is a pure combinatorial quantity (a sum of binomials); the
`ε_mca`-bracket at every radius is therefore

  `(max witness-spread)/q  ≤  ε_mca(C, δ)  ≤  (witness-family count)/q`,

with both engines now formal. At the granularity radius the family has exactly `n + 1`
members (`witnessFamily_card_granularity`: the `n` single-point erasures plus `univ`), so
the raw witness-family count gives `ε_mca(C, 1/n) ≤ (n+1)/q`. The codimension-one
witness-spread injection from `MCAWitnessSpread` sharpens this by one, charging the universal
witness to an omitted coordinate:

  `ε_mca(C, 1/n) ≤ n/q`             (`epsMCA_le_card_div_at_granularity`).

Thus for distance-`≥ 3` RS codes the two-sided jump bracket tightens to

  `2/q ≤ ε_mca(RS[F,D,k], 1/n) ≤ n/q`            (`epsMCA_rs_jump_bracket_sharpUpper`)

which matches the measured flat-`n` upper shape. Closing the lower gap is the registered
per-excluded-point nondegeneracy question.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- Issue #357 (campaign round 2); `MCAWitnessSpread.lean` (the obstruction and the lower
  engine); `MCADeltaStarHighRateFamily.lean` (the family pin this brackets).
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAWitnessSpread

namespace ProximityGap.MCAWitnessCountEngine

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- The admissible witness family at radius `δ`: coordinate sets large enough to serve as
`mcaEvent` witnesses. -/
noncomputable def witnessFamily (ι : Type) [Fintype ι] (δ : ℝ≥0) : Finset (Finset ι) :=
  Finset.univ.filter
    (fun S : Finset ι => (S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι : ℝ≥0))

open Classical in
theorem mem_witnessFamily {δ : ℝ≥0} {S : Finset ι} :
    S ∈ witnessFamily ι δ ↔ (S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι : ℝ≥0) := by
  simp [witnessFamily]

open Classical in
/-- **The witness-counting bound.** Distinct bad scalars own distinct witness sets
(`unique_bad_gamma_common_witness`), so each stack has at most `|witnessFamily|` bad
scalars. -/
theorem badScalar_card_le_witnessFamily_card (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (u : WordStack A (Fin 2) ι) :
    (Finset.univ.filter
        (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ)).card
      ≤ (witnessFamily ι δ).card := by
  classical
  -- each bad scalar chooses a witness set
  apply Finset.card_le_card_of_injOn
    (fun γ => if h : mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ
      then h.choose else ∅)
  · -- the chosen witness is admissible
    intro γ hγ
    rw [Finset.mem_coe, Finset.mem_filter] at hγ
    obtain ⟨-, hev⟩ := hγ
    rw [Finset.mem_coe]
    simp only [dif_pos hev]
    rw [mem_witnessFamily]
    exact hev.choose_spec.1
  · -- distinct bad scalars cannot share the chosen witness
    intro γ hγ γ' hγ' heq
    rw [Finset.mem_coe, Finset.mem_filter] at hγ hγ'
    obtain ⟨-, hev⟩ := hγ
    obtain ⟨-, hev'⟩ := hγ'
    simp only [dif_pos hev, dif_pos hev'] at heq
    obtain ⟨-, hline, hno⟩ := hev.choose_spec
    obtain ⟨-, hline', -⟩ := hev'.choose_spec
    rw [heq] at hline hno
    exact unique_bad_gamma_common_witness C hev'.choose (u 0) (u 1) hno hline hline'

open Classical in
/-- **The upper engine:** for every linear code, every radius,
`ε_mca(C, δ) ≤ |witnessFamily(δ)| / q`. -/
theorem epsMCA_le_witnessFamily_card_div (C : Submodule F (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      ≤ ((witnessFamily ι δ).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast badScalar_card_le_witnessFamily_card C δ u

/-! ## The granularity instance: exactly `n + 1` witnesses -/

open Classical in
/-- At the granularity radius the witness family is exactly the `n` single-point erasures
plus `univ`: `n + 1` sets. -/
theorem witnessFamily_card_granularity (hn : 1 ≤ Fintype.card ι) :
    (witnessFamily ι (1 / (Fintype.card ι : ℝ≥0))).card = Fintype.card ι + 1 := by
  classical
  have hkey : witnessFamily ι (1 / (Fintype.card ι : ℝ≥0))
      = Finset.univ.filter (fun S : Finset ι => Fintype.card ι - 1 ≤ S.card) := by
    ext S
    rw [mem_witnessFamily, Finset.mem_filter]
    rw [ProximityGap.MCADeltaStarHighRateFamily.card_clause_arith Fintype.card_pos]
    constructor
    · intro h
      exact ⟨Finset.mem_univ S, by exact_mod_cast h⟩
    · rintro ⟨-, h⟩
      exact_mod_cast h
  rw [hkey]
  -- the sets of size ≥ n−1 are the n erasures and univ
  have hsplit : Finset.univ.filter (fun S : Finset ι => Fintype.card ι - 1 ≤ S.card)
      = insert (Finset.univ : Finset ι)
          (Finset.univ.image (fun b : ι => Finset.univ.erase b)) := by
    ext S
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro ⟨-, hcard⟩
      rcases eq_or_lt_of_le (Finset.card_le_univ S) with hfull | hlt
      · left
        exact Finset.eq_univ_of_card S hfull
      · right
        -- |S| = n − 1: S misses exactly one point
        have hScard : S.card = Fintype.card ι - 1 := by
          omega
        have hcompl : (Finset.univ \ S).card = 1 := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
            hScard]
          omega
        obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hcompl
        refine ⟨b, Finset.mem_univ b, ?_⟩
        have hbS : b ∉ S := by
          have : b ∈ Finset.univ \ S := by
            rw [hb]
            exact Finset.mem_singleton_self b
          exact (Finset.mem_sdiff.mp this).2
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          rcases eq_or_ne x b with rfl | hxb
          · exact absurd (Finset.mem_erase.mp hx).1 (by simp)
          · by_contra hxS
            have : x ∈ Finset.univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxS⟩
            rw [hb, Finset.mem_singleton] at this
            exact hxb this
        · rw [Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ, hScard]
    · rintro (rfl | ⟨b, -, rfl⟩)
      · exact ⟨Finset.mem_univ _, by rw [Finset.card_univ]; omega⟩
      · refine ⟨Finset.mem_univ _, ?_⟩
        rw [Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ]
  rw [hsplit]
  have hnotmem : (Finset.univ : Finset ι)
      ∉ Finset.univ.image (fun b : ι => Finset.univ.erase b) := by
    rw [Finset.mem_image]
    rintro ⟨b, -, hb⟩
    have : b ∈ Finset.univ.erase b := by
      rw [hb]
      exact Finset.mem_univ b
    exact (Finset.mem_erase.mp this).1 rfl
  rw [Finset.card_insert_of_notMem hnotmem, Finset.card_image_of_injective _ (by
    intro a b hab
    have hab' : Finset.univ.erase a = Finset.univ.erase b := hab
    by_contra hne
    have ha : a ∈ Finset.univ.erase b :=
      Finset.mem_erase.mpr ⟨hne, Finset.mem_univ a⟩
    rw [← hab'] at ha
    exact (Finset.mem_erase.mp ha).1 rfl), Finset.card_univ]

open Classical in
/-- **The granularity cap for every linear code:** `ε_mca(C, 1/n) ≤ (n+1)/q` — one step
beyond the sub-unit collapse. -/
theorem epsMCA_le_succ_div_at_granularity (C : Submodule F (ι → A)) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) (1 / (Fintype.card ι : ℝ≥0))
      ≤ ((Fintype.card ι + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  have h := epsMCA_le_witnessFamily_card_div C (1 / (Fintype.card ι : ℝ≥0))
  rwa [witnessFamily_card_granularity (Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero)]
    at h

open Classical in
/-- **Sharper granularity cap:** the universal witness in the raw `n + 1` witness-family count
does not cost an extra bad scalar. The codimension-one spread injection charges universal
witnesses to an arbitrary coordinate and proves `ε_mca(C, 1/n) ≤ n/q` for every linear code. -/
theorem epsMCA_le_card_div_at_granularity (C : Submodule F (ι → A)) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) (1 / (Fintype.card ι : ℝ≥0))
      ≤ (Fintype.card ι : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  ProximityGap.MCAWitnessSpread.epsMCA_le_card_div_of_granularity_radius C

open Classical in
/-- **The two-sided jump bracket for distance-`≥ 3` RS codes:**

  `2/q ≤ ε_mca(RS[F, D, k], 1/n) ≤ (n+1)/q`.

Both sides are engine outputs (witness-spread below, witness-count above); the probes
measure the truth at `n` (the flat-`n` law) — the residual factor is the registered
per-excluded-point nondegeneracy question. -/
theorem epsMCA_rs_jump_bracket (domain : ι ↪ F) {k : ℕ}
    (hk : k ≤ Fintype.card ι - 2) {b₁ b₂ : ι} (hb : b₁ ≠ b₂) :
    (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
        ≤ epsMCA (F := F) (A := F)
            (ReedSolomon.code domain k : Set (ι → F)) (1 / (Fintype.card ι : ℝ≥0))
      ∧ epsMCA (F := F) (A := F)
            (ReedSolomon.code domain k : Set (ι → F)) (1 / (Fintype.card ι : ℝ≥0))
          ≤ ((Fintype.card ι + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  ⟨ProximityGap.MCADeltaStarHighRateFamily.epsMCA_highRate_ge domain hk hb,
    epsMCA_le_succ_div_at_granularity (ReedSolomon.code domain k)⟩

open Classical in
/-- **Sharp-upper two-sided jump bracket for distance-`≥ 3` RS codes:**

  `2/q ≤ ε_mca(RS[F, D, k], 1/n) ≤ n/q`.

The upper half uses the codimension-one witness-spread injection rather than the raw
`n + 1` witness-family count. The remaining exact-jump task is the lower construction of
`n` bad scalars for the distance-three edge case. -/
theorem epsMCA_rs_jump_bracket_sharpUpper (domain : ι ↪ F) {k : ℕ}
    (hk : k ≤ Fintype.card ι - 2) {b₁ b₂ : ι} (hb : b₁ ≠ b₂) :
    (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
        ≤ epsMCA (F := F) (A := F)
            (ReedSolomon.code domain k : Set (ι → F)) (1 / (Fintype.card ι : ℝ≥0))
      ∧ epsMCA (F := F) (A := F)
            (ReedSolomon.code domain k : Set (ι → F)) (1 / (Fintype.card ι : ℝ≥0))
          ≤ (Fintype.card ι : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  ⟨ProximityGap.MCADeltaStarHighRateFamily.epsMCA_highRate_ge domain hk hb,
    epsMCA_le_card_div_at_granularity (ReedSolomon.code domain k)⟩

/-! ## Source audit -/

#print axioms badScalar_card_le_witnessFamily_card
#print axioms epsMCA_le_witnessFamily_card_div
#print axioms witnessFamily_card_granularity
#print axioms epsMCA_le_succ_div_at_granularity
#print axioms epsMCA_le_card_div_at_granularity
#print axioms epsMCA_rs_jump_bracket
#print axioms epsMCA_rs_jump_bracket_sharpUpper

end ProximityGap.MCAWitnessCountEngine

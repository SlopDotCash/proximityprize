/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAStaircaseExact
import ArkLib.Data.CodingTheory.ProximityGap.MCABandTwoRS

/-!
# Round 4 (#357): the exact staircase for every Reed–Solomon code

The production-facing instantiation of the exact staircase
(`MCAStaircaseMaster`/`MCAStaircaseExact`): a nonzero polynomial of degree `< k` has at
most `k − 1` roots, so RS codes satisfy every support-budget hypothesis up to `n − k`
(`rs_noWeightLE`), and the master theorems land with hypotheses only on `(n, k, b)`:

* `epsMCA_rs_le_div_card` — `ε_mca(RS[F, domain, k], δ) ≤ b/|F|` on `δ·n < b` whenever
  `k + 3(b−1) ≤ n`;
* `epsMCA_rs_eq_div_card` — **equality** on the band `b−1 ≤ δ·n < b` (the `b`-spike fits
  whenever additionally `b ≤ |F|`).

**In prize terms:** for every Reed–Solomon code of the prize statement, at every rate and
scale, `ε_mca(δ) = (⌊δn⌋ + 1)/|F|` is an exact theorem for all
`δ < (n − k + 3)/(3n) ≈ (1 − ρ)/3`. The first three strips of the δ*-landscape are now:
exact theory (`[0, (1−ρ)/3)`, this file), the explosion strip (`[(1−ρ)/3, (1−ρ)/2)`, where
the `(b−1)`-tupled witnesses live and the RS-specific threshold is the open matroid
question), and the UD→Johnson→window ascent above.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCAStaircaseRS

open ProximityGap.MCAStaircaseMaster ProximityGap.MCAStaircaseExact

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **RS codes meet every support budget below the distance**: a nonzero polynomial of
degree `< k` cannot vanish at `n − m ≥ k` distinct points, so no nonzero codeword is
supported on `≤ m` points whenever `k + m ≤ n`. -/
theorem rs_noWeightLE (domain : ι ↪ F) {k m : ℕ} (hm : k + m ≤ Fintype.card ι) :
    NoWeightLE (ReedSolomon.code domain k) m := by
  rintro w hw ⟨T, hTm, hsupp⟩
  obtain ⟨p, hp, rfl⟩ := hw
  have hp0 : p = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero (v := domain)
      (Finset.univ \ T) (Set.injOn_of_injective domain.injective) ?_ ?_
    · have hdeg : p.degree < (k : WithBot ℕ) := Polynomial.mem_degreeLT.mp hp
      refine lt_of_lt_of_le hdeg ?_
      have hsplit : (Finset.univ \ T).card + T.card = (Finset.univ : Finset ι).card :=
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
      rw [Finset.card_univ] at hsplit
      have hcard : k ≤ (Finset.univ \ T).card := by omega
      exact_mod_cast hcard
    · intro i hi
      exact hsupp i (Finset.mem_sdiff.mp hi).2
  rw [hp0, map_zero]

open Classical in
/-- **The RS staircase, upper half**: `ε_mca(RS, δ) ≤ b/|F|` on `δ·n < b` whenever
`k + 3(b−1) ≤ n`. -/
theorem epsMCA_rs_le_div_card (domain : ι ↪ F) {k b : ℕ} (hb : 1 ≤ b)
    (hkb : k + 3 * (b - 1) ≤ Fintype.card ι) (hk : 1 ≤ k) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < (b : ℝ≥0)) :
    epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ
      ≤ (b : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  refine epsMCA_le_div_card_of_dist (ReedSolomon.code domain k) b hb
    (rs_noWeightLE domain hkb) ?_ hδ
  omega

open Classical in
/-- **The exact RS staircase**: `ε_mca(RS[F, domain, k], δ) = b/|F|` on the band
`b−1 ≤ δ·n < b`, whenever `k + 3(b−1) ≤ n`, `2 ≤ b ≤ |F|`, `k ≥ 1` — for every
Reed–Solomon code of the prize statement, the MCA error is the spike count exactly through
every band below a third of the distance. -/
theorem epsMCA_rs_eq_div_card (domain : ι ↪ F) {k b : ℕ} (hb : 2 ≤ b)
    (hkb : k + 3 * (b - 1) ≤ Fintype.card ι) (hk : 1 ≤ k) (hbF : b ≤ Fintype.card F)
    {δ : ℝ≥0} (hδ1 : ((b - 1 : ℕ) : ℝ≥0) ≤ δ * (Fintype.card ι : ℝ≥0))
    (hδ2 : δ * (Fintype.card ι : ℝ≥0) < (b : ℝ≥0)) :
    epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ
      = (b : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  -- spike positions: b of the n ≥ b coordinates; spike scalars: b of the q ≥ b field elements
  have hbι : b ≤ Fintype.card ι := by omega
  obtain ⟨I, hIcard⟩ := Finset.exists_subset_card_eq
    (le_trans hbι (le_of_eq (Finset.card_univ (α := ι)).symm))
  obtain ⟨G, hGcard⟩ := Finset.exists_subset_card_eq
    (le_trans hbF (le_of_eq (Finset.card_univ (α := F)).symm))
  -- build injections Fin b → ι and Fin b → F
  set i : Fin b → ι := fun x => (I.equivFin.symm (Fin.cast hIcard.2.symm x) : ι) with hidef
  have hiinj : Function.Injective i := by
    intro x x' hxx'
    have h1 := I.equivFin.symm.injective (Subtype.ext hxx')
    exact Fin.cast_injective hIcard.2.symm h1
  set g : Fin b → F := fun x => (G.equivFin.symm (Fin.cast hGcard.2.symm x) : F) with hgdef
  have hginj : Function.Injective g := by
    intro x x' hxx'
    have h1 := G.equivFin.symm.injective (Subtype.ext hxx')
    exact Fin.cast_injective hGcard.2.symm h1
  exact epsMCA_eq_div_card_of_dist (ReedSolomon.code domain k) hb
    (rs_noWeightLE domain hkb) hbι hδ1 hδ2 hiinj hginj (one_ne_zero)

/-! ## Source audit -/

#print axioms rs_noWeightLE
#print axioms epsMCA_rs_le_div_card
#print axioms epsMCA_rs_eq_div_card

end ProximityGap.MCAStaircaseRS

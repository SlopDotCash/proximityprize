/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# The universal spike floor: `ε_mca ≥ j/q` on every granularity band (#357)

The staircase program's lower halves, all bands at once.  The band-1 floor is the
classical `1/q`; the band-2 floor is the sibling double-spike (`MCABandTwoExact`);
this file proves the **`j`-spike floor for every `j`**:

For any linear code with **no nonzero codeword of weight `≤ j`** (true for every code
of minimum distance `> j`, hence for RS at every `j ≤ n − k`), any `j` distinct
positions, `j` distinct scalars, and any radius `δ` with `δ·n ≥ j − 1`:

  `ε_mca(C, δ) ≥ j / |F|`.

**The construction** (`u₀ = Σ aₗ•b·e_{pₗ}`, `u₁ = Σ b·e_{pₗ}`): at `γ = −aₗ` the line
`u₀ + γ·u₁` vanishes at `pₗ` and off the spike support, so it agrees with the zero
codeword on a set of size `n − j + 1 ≥ (1−δ)·n`; the pair has no joint explanation
there because an explaining `v₁` would vanish off the `j` spike positions — weight
`≤ j`, hence zero — contradicting `v₁(pₗ) = u₁(pₗ) = b ≠ 0`.  The `j` scalars
`{−aₗ}` are distinct, so the bad mass is at least `j/q`.

**The universal δ\* bracket** (`mcaDeltaStar_le_granularity`): for every such code and
every `ε* < j/|F|`,

  `mcaDeltaStar C ε* ≤ (j − 1)/n`.

This is the complete bad side of the granularity ladder, for every linear code at
once: each pinned-value theorem's upper bracket (including both landed pins) is the
`j`-th instance, and any future pin needs only its good side.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap.SpikeFloor

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- No nonzero codeword is supported on `≤ j` positions (minimum distance `> j`). -/
def NoWeightLE (C : Submodule F (ι → A)) (j : ℕ) : Prop :=
  ∀ w ∈ C, (∃ T : Finset ι, T.card ≤ j ∧ ∀ i ∉ T, w i = 0) → w = 0

variable {j : ℕ}

/-- The `j`-spike first row: value `aₗ • b` at position `pₗ`, zero elsewhere. -/
def spike0 (p : Fin j ↪ ι) (a : Fin j → F) (b : A) : ι → A :=
  fun i => ∑ l, if i = p l then a l • b else 0

/-- The `j`-spike second row: value `b` at each `pₗ`, zero elsewhere. -/
def spike1 (p : Fin j ↪ ι) (b : A) : ι → A :=
  fun i => ∑ l, if i = p l then b else 0

theorem spike0_apply_mem (p : Fin j ↪ ι) (a : Fin j → F) (b : A) (m : Fin j) :
    spike0 p a b (p m) = a m • b := by
  unfold spike0
  rw [Finset.sum_eq_single m]
  · simp
  · intro l _ hl
    rw [if_neg]
    exact fun h => hl (p.injective h.symm)
  · intro h
    exact absurd (Finset.mem_univ m) h

theorem spike0_apply_notMem (p : Fin j ↪ ι) (a : Fin j → F) (b : A) {i : ι}
    (hi : ∀ l, i ≠ p l) : spike0 p a b i = 0 := by
  unfold spike0
  exact Finset.sum_eq_zero fun l _ => if_neg (hi l)

theorem spike1_apply_mem (p : Fin j ↪ ι) (b : A) (m : Fin j) :
    spike1 p b (p m) = b := by
  unfold spike1
  rw [Finset.sum_eq_single m]
  · simp
  · intro l _ hl
    rw [if_neg]
    exact fun h => hl (p.injective h.symm)
  · intro h
    exact absurd (Finset.mem_univ m) h

theorem spike1_apply_notMem (p : Fin j ↪ ι) (b : A) {i : ι}
    (hi : ∀ l, i ≠ p l) : spike1 p b i = 0 := by
  unfold spike1
  exact Finset.sum_eq_zero fun l _ => if_neg (hi l)

/-- The witness set for the `l`-th bad scalar: everything off the spike support,
plus `pₗ` itself. -/
def witnessAt (p : Fin j ↪ ι) (l : Fin j) : Finset ι :=
  (Finset.univ \ Finset.univ.image p) ∪ {p l}

theorem witnessAt_card (p : Fin j ↪ ι) (l : Fin j) :
    (witnessAt p l).card = Fintype.card ι - j + 1 := by
  unfold witnessAt
  have himg : (Finset.univ.image p).card = j := by
    rw [Finset.card_image_of_injective _ p.injective, Finset.card_univ,
      Fintype.card_fin]
  have hdisj : Disjoint (Finset.univ \ Finset.univ.image p) ({p l} : Finset ι) := by
    rw [Finset.disjoint_singleton_right]
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
    exact Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff, Finset.inter_univ,
    Finset.card_univ, himg, Finset.card_singleton]

/-- **The `j`-spike certificate.**  At `γ = −aₗ` the spike stack fires `mcaEvent`. -/
theorem mcaEvent_spike (C : Submodule F (ι → A)) (hC : NoWeightLE C j)
    {δ : ℝ≥0} (hδ : ((j - 1 : ℕ) : ℝ≥0) ≤ δ * Fintype.card ι)
    (hj1 : 1 ≤ j) (hjn : j ≤ Fintype.card ι)
    (p : Fin j ↪ ι) (a : Fin j → F) {b : A} (hb : b ≠ 0) (l : Fin j) :
    mcaEvent (F := F) (C : Set (ι → A)) δ (spike0 p a b) (spike1 p b) (-(a l)) := by
  refine ⟨witnessAt p l, ?_, ⟨0, C.zero_mem, ?_⟩, ?_⟩
  · -- size: n − j + 1 ≥ (1 − δ)·n
    rw [witnessAt_card]
    have hone : (1 - δ) * (Fintype.card ι : ℝ≥0)
        = (Fintype.card ι : ℝ≥0) - δ * Fintype.card ι := by
      rw [tsub_mul, one_mul]
    rw [hone]
    calc (Fintype.card ι : ℝ≥0) - δ * Fintype.card ι
        ≤ (Fintype.card ι : ℝ≥0) - ((j - 1 : ℕ) : ℝ≥0) := tsub_le_tsub_left hδ _
      _ ≤ ((Fintype.card ι - j + 1 : ℕ) : ℝ≥0) := by
          rw [← Nat.cast_tsub]
          exact_mod_cast Nat.le_of_eq (by omega)
  · -- the zero codeword explains the line on the witness
    intro i hi
    rcases Finset.mem_union.mp hi with hoff | hpl
    · obtain ⟨-, hnotimg⟩ := Finset.mem_sdiff.mp hoff
      have hno : ∀ m, i ≠ p m := by
        intro m h
        exact hnotimg (Finset.mem_image.mpr ⟨m, Finset.mem_univ m, h.symm⟩)
      rw [spike0_apply_notMem p a b hno, spike1_apply_notMem p b hno]
      simp
    · rw [Finset.mem_singleton.mp hpl, spike0_apply_mem, spike1_apply_mem]
      show (0 : ι → A) (p l) = a l • b + (-(a l)) • b
      rw [← add_smul]
      simp
  · -- no joint explanation: v₁ would be a weight-≤-j codeword equal to b ≠ 0 at pₗ
    rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    have hvz : v₁ = 0 := by
      refine hC v₁ hv₁ ⟨Finset.univ.image p, ?_, ?_⟩
      · rw [Finset.card_image_of_injective _ p.injective, Finset.card_univ,
          Fintype.card_fin]
      · intro i hi
        have hiT : i ∈ witnessAt p l := by
          unfold witnessAt
          exact Finset.mem_union_left _
            (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩)
        have hno : ∀ m, i ≠ p m := by
          intro m h
          exact hi (Finset.mem_image.mpr ⟨m, Finset.mem_univ m, h.symm⟩)
        rw [(hag i hiT).2, spike1_apply_notMem p b hno]
    have hpl : p l ∈ witnessAt p l := by
      unfold witnessAt
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    have h1 := (hag (p l) hpl).2
    rw [hvz, spike1_apply_mem] at h1
    exact hb h1.symm

open Classical in
/-- **The universal spike floor.**  `ε_mca(C, δ) ≥ j/|F|` on the `j`-th granularity
band and beyond (`δ·n ≥ j−1`), for every linear code with no nonzero codeword of
weight `≤ j`, given `j` distinct positions and `j` distinct scalars. -/
theorem epsMCA_ge_j_div_card (C : Submodule F (ι → A)) (hC : NoWeightLE C j)
    {δ : ℝ≥0} (hδ : ((j - 1 : ℕ) : ℝ≥0) ≤ δ * Fintype.card ι)
    (hj1 : 1 ≤ j) (hjn : j ≤ Fintype.card ι)
    (p : Fin j ↪ ι) (a : Fin j ↪ F) {b : A} (hb : b ≠ 0) :
    (j : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := A) (C : Set (ι → A)) δ := by
  have h := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (C : Set (ι → A)) δ ![spike0 p a b, spike1 p b]
    (Finset.univ.image (fun l => -(a l))) ?_
  · have hcard : (Finset.univ.image (fun l : Fin j => -(a l))).card = j := by
      rw [Finset.card_image_of_injective _ (fun x y hxy =>
        a.injective (neg_injective hxy)), Finset.card_univ, Fintype.card_fin]
    rwa [hcard] at h
  · intro γ hγ
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hγ
    simpa using mcaEvent_spike C hC hδ hj1 hjn p a hb l

open Classical in
/-- **The universal δ\* granularity bracket.**  For every linear code with no nonzero
codeword of weight `≤ j` and every `ε* < j/|F|`:

  `mcaDeltaStar C ε* ≤ (j−1)/n`.

The complete bad side of the granularity ladder, for every code at once. -/
theorem mcaDeltaStar_le_granularity (C : Submodule F (ι → A)) (hC : NoWeightLE C j)
    (hj1 : 1 ≤ j) (hjn : j ≤ Fintype.card ι) (hjF : j ≤ Fintype.card F)
    [Nontrivial A] {εstar : ℝ≥0∞}
    (hε : εstar < (j : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) (C : Set (ι → A)) εstar
      ≤ ((j - 1 : ℕ) : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
  obtain ⟨p⟩ : Nonempty (Fin j ↪ ι) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hjn)
  obtain ⟨a⟩ : Nonempty (Fin j ↪ F) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hjF)
  obtain ⟨b, hb⟩ := exists_ne (0 : A)
  have hn0 : (Fintype.card ι : ℝ≥0) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  refine MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _ ?_
  refine lt_of_lt_of_le hε ?_
  refine epsMCA_ge_j_div_card C hC ?_ hj1 hjn p a hb
  rw [div_mul_cancel₀ _ hn0]

end ProximityGap.SpikeFloor

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.SpikeFloor.mcaEvent_spike
#print axioms ProximityGap.SpikeFloor.epsMCA_ge_j_div_card
#print axioms ProximityGap.SpikeFloor.mcaDeltaStar_le_granularity

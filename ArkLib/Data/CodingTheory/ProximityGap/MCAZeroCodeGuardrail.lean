/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAZeroCodeExact
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-!
# Grand Challenge guardrails from the exact zero-code MCA value

`MCAZeroCodeExact.lean` proves that the zero code over a finite field has
`ε_mca(⊥, 0) = 1 / |F|`.  This file exposes the consumer-facing consequence for the Grand
Challenge witness API: whenever the target threshold is below `1 / |F|`, the zero code gives an
upper witness at radius `0`.

This is a guardrail for the refuted black-box line-decoding statement: it packages the exact
zero-code value as a one-sided obstruction, without asserting any Guruswami--Sudan extraction or
repairing ABF26 Theorem 4.21.
-/

namespace ProximityGap.MCAZeroCode

open scoped NNReal ENNReal

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

section General

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Zero-code upper witness from the exact value.** If the target `ε_star` is below `1 / |F|`,
then the zero code has already exceeded the target at radius `0`. -/
def MCAUpperWitness_bot_of_lt_inv_card (ε_star : ℝ≥0)
    (hε : (ε_star : ENNReal) < (1 : ENNReal) / (Fintype.card F : ENNReal)) :
    GrandChallenges.MCAUpperWitness (F := F)
      (Cbot (ι := ι) (F := F) : Set (ι → F)) ε_star :=
  GrandChallenges.MCAUpperWitness.ofGt
    (C := (Cbot (ι := ι) (F := F) : Set (ι → F))) (δ := (0 : ℝ≥0)) <| by
      rw [epsMCA_bot_eq_inv_card]
      exact hε

/-- Existential form of `MCAUpperWitness_bot_of_lt_inv_card`, preserving the certified radius. -/
theorem exists_MCAUpperWitness_bot_of_lt_inv_card (ε_star : ℝ≥0)
    (hε : (ε_star : ENNReal) < (1 : ENNReal) / (Fintype.card F : ENNReal)) :
    ∃ w : GrandChallenges.MCAUpperWitness (F := F)
        (Cbot (ι := ι) (F := F) : Set (ι → F)) ε_star,
      w.δ = 0 :=
  ⟨MCAUpperWitness_bot_of_lt_inv_card (ι := ι) (F := F) ε_star hε, rfl⟩

/-- `epsStar` specialization of the zero-code upper witness. -/
noncomputable def MCAUpperWitness_bot_epsStar_of_lt_inv_card
    (hε : (epsStar : ENNReal) < (1 : ENNReal) / (Fintype.card F : ENNReal)) :
    GrandChallenges.MCAUpperWitness (F := F)
      (Cbot (ι := ι) (F := F) : Set (ι → F)) epsStar :=
  MCAUpperWitness_bot_of_lt_inv_card (ι := ι) (F := F) epsStar hε

/-- Existential `epsStar` specialization, preserving the certified radius `0`. -/
theorem exists_MCAUpperWitness_bot_epsStar_of_lt_inv_card
    (hε : (epsStar : ENNReal) < (1 : ENNReal) / (Fintype.card F : ENNReal)) :
    ∃ w : GrandChallenges.MCAUpperWitness (F := F)
        (Cbot (ι := ι) (F := F) : Set (ι → F)) epsStar,
      w.δ = 0 :=
  ⟨MCAUpperWitness_bot_epsStar_of_lt_inv_card (ι := ι) (F := F) hε, rfl⟩

/-- Any supplied zero-code MCA resolution below `1 / |F|` has threshold exactly `0`. -/
theorem GrandMCAResolution_bot_deltaStar_eq_zero_of_lt_inv_card (ε_star : ℝ≥0)
    (hε : (ε_star : ENNReal) < (1 : ENNReal) / (Fintype.card F : ENNReal))
    (R : GrandChallenges.GrandMCAResolution (F := F)
      (Cbot (ι := ι) (F := F) : Set (ι → F)) ε_star) :
    R.δStar = 0 := by
  let w := MCAUpperWitness_bot_of_lt_inv_card (ι := ι) (F := F) ε_star hε
  have hle : R.δStar ≤ 0 := by
    change R.δStar ≤ w.δ
    exact w.δStar_le R
  exact le_antisymm hle (zero_le _)

/-- `epsStar` specialization: any supplied zero-code MCA resolution below `1 / |F|` has
threshold exactly `0`. -/
theorem GrandMCAResolution_bot_deltaStar_eq_zero_of_epsStar_lt_inv_card
    (hε : (epsStar : ENNReal) < (1 : ENNReal) / (Fintype.card F : ENNReal))
    (R : GrandChallenges.GrandMCAResolution (F := F)
      (Cbot (ι := ι) (F := F) : Set (ι → F)) epsStar) :
    R.δStar = 0 :=
  GrandMCAResolution_bot_deltaStar_eq_zero_of_lt_inv_card (ι := ι) (F := F) epsStar hε R

/-- Below `1 / |F|`, the zero code admits no MCA resolution: any resolution would first have
threshold `0` by the upper witness, but then its bound contradicts the exact zero-code value. -/
theorem not_GrandMCAResolution_bot_of_lt_inv_card (ε_star : ℝ≥0)
    (hε : (ε_star : ENNReal) < (1 : ENNReal) / (Fintype.card F : ENNReal)) :
    ¬ Nonempty (GrandChallenges.GrandMCAResolution (F := F)
      (Cbot (ι := ι) (F := F) : Set (ι → F)) ε_star) := by
  rintro ⟨R⟩
  have hδ :
      R.δStar = 0 :=
    GrandMCAResolution_bot_deltaStar_eq_zero_of_lt_inv_card
      (ι := ι) (F := F) ε_star hε R
  have hbound :
      epsMCA (F := F) (A := F) (Cbot (ι := ι) (F := F) : Set (ι → F)) 0 ≤
        (ε_star : ENNReal) := by
    simpa [hδ] using R.bound
  have hexceeds :
      (ε_star : ENNReal) <
        epsMCA (F := F) (A := F) (Cbot (ι := ι) (F := F) : Set (ι → F)) 0 := by
    rw [epsMCA_bot_eq_inv_card]
    exact hε
  exact (not_le_of_gt hexceeds) hbound

/-- `epsStar` specialization of the zero-code no-resolution guardrail. -/
theorem not_GrandMCAResolution_bot_epsStar_of_lt_inv_card
    (hε : (epsStar : ENNReal) < (1 : ENNReal) / (Fintype.card F : ENNReal)) :
    ¬ Nonempty (GrandChallenges.GrandMCAResolution (F := F)
      (Cbot (ι := ι) (F := F) : Set (ι → F)) epsStar) :=
  not_GrandMCAResolution_bot_of_lt_inv_card (ι := ι) (F := F) epsStar hε

/-- If the target is below the exact zero-code value `1 / |F|`, then the bottom linear code
does not satisfy the predicate-level Grand MCA challenge. -/
theorem not_grandMCAChallenge_bot_of_lt_inv_card (ε_star : ℝ≥0)
    (hε : (ε_star : ENNReal) < (1 : ENNReal) / (Fintype.card F : ENNReal)) :
    ¬ grandMCAChallenge (F := F) (ι := ι) (⊥ : LinearCode ι F) ε_star := by
  intro h
  rcases h with ⟨δStar, hle_one, hbound, hmaximal⟩
  let R : GrandChallenges.GrandMCAResolution (F := F)
      (Cbot (ι := ι) (F := F) : Set (ι → F)) ε_star :=
    { δStar := δStar
      le_one := hle_one
      bound := by simpa [Cbot] using hbound
      maximal := by simpa [Cbot] using hmaximal }
  exact not_GrandMCAResolution_bot_of_lt_inv_card (ι := ι) (F := F) ε_star hε ⟨R⟩

/-- `epsStar` specialization: below the exact zero-code value `1 / |F|`, the bottom linear code
does not satisfy the predicate-level Grand MCA challenge. -/
theorem not_grandMCAChallenge_bot_epsStar_of_lt_inv_card
    (hε : (epsStar : ENNReal) < (1 : ENNReal) / (Fintype.card F : ENNReal)) :
    ¬ grandMCAChallenge (F := F) (ι := ι) (⊥ : LinearCode ι F) epsStar :=
  not_grandMCAChallenge_bot_of_lt_inv_card (ι := ι) (F := F) epsStar hε

/-- Any zero-code MCA resolution forces the target error to be at least the exact zero-code value
`1 / |F|`. This is the contrapositive form of `not_GrandMCAResolution_bot_of_lt_inv_card`. -/
theorem inv_card_le_of_GrandMCAResolution_bot (ε_star : ℝ≥0)
    (h : Nonempty (GrandChallenges.GrandMCAResolution (F := F)
      (Cbot (ι := ι) (F := F) : Set (ι → F)) ε_star)) :
    (1 : ENNReal) / (Fintype.card F : ENNReal) ≤ (ε_star : ENNReal) :=
  le_of_not_gt fun hε =>
    not_GrandMCAResolution_bot_of_lt_inv_card (ι := ι) (F := F) ε_star hε h

/-- If the bottom linear code satisfies the Grand MCA predicate, then the target error is at least
the exact zero-code value `1 / |F|`. -/
theorem inv_card_le_of_grandMCAChallenge_bot (ε_star : ℝ≥0)
    (h : grandMCAChallenge (F := F) (ι := ι) (⊥ : LinearCode ι F) ε_star) :
    (1 : ENNReal) / (Fintype.card F : ENNReal) ≤ (ε_star : ENNReal) :=
  le_of_not_gt fun hε =>
    not_grandMCAChallenge_bot_of_lt_inv_card (ι := ι) (F := F) ε_star hε h

/-- **Zero-code lower witness from the exact value.** If the target `ε_star` is at least
`1 / |F|`, then the zero code satisfies the MCA bound at radius `0`. -/
def MCALowerWitness_bot_of_inv_card_le (ε_star : ℝ≥0)
    (hε : (1 : ENNReal) / (Fintype.card F : ENNReal) ≤ (ε_star : ENNReal)) :
    GrandChallenges.MCALowerWitness (F := F)
      (Cbot (ι := ι) (F := F) : Set (ι → F)) ε_star :=
  GrandChallenges.MCALowerWitness.ofLe
    (C := (Cbot (ι := ι) (F := F) : Set (ι → F))) (δ := 0) (by simp) <| by
      rw [epsMCA_bot_eq_inv_card]
      exact hε

/-- Existential form of `MCALowerWitness_bot_of_inv_card_le`, preserving the certified radius. -/
theorem exists_MCALowerWitness_bot_of_inv_card_le (ε_star : ℝ≥0)
    (hε : (1 : ENNReal) / (Fintype.card F : ENNReal) ≤ (ε_star : ENNReal)) :
    ∃ w : GrandChallenges.MCALowerWitness (F := F)
        (Cbot (ι := ι) (F := F) : Set (ι → F)) ε_star,
      w.δ = 0 :=
  ⟨MCALowerWitness_bot_of_inv_card_le (ι := ι) (F := F) ε_star hε, rfl⟩

/-- `epsStar` specialization of the zero-code lower witness. -/
noncomputable def MCALowerWitness_bot_epsStar_of_inv_card_le
    (hε : (1 : ENNReal) / (Fintype.card F : ENNReal) ≤ (epsStar : ENNReal)) :
    GrandChallenges.MCALowerWitness (F := F)
      (Cbot (ι := ι) (F := F) : Set (ι → F)) epsStar :=
  MCALowerWitness_bot_of_inv_card_le (ι := ι) (F := F) epsStar hε

/-- Existential `epsStar` specialization, preserving the certified radius `0`. -/
theorem exists_MCALowerWitness_bot_epsStar_of_inv_card_le
    (hε : (1 : ENNReal) / (Fintype.card F : ENNReal) ≤ (epsStar : ENNReal)) :
    ∃ w : GrandChallenges.MCALowerWitness (F := F)
        (Cbot (ι := ι) (F := F) : Set (ι → F)) epsStar,
      w.δ = 0 :=
  ⟨MCALowerWitness_bot_epsStar_of_inv_card_le (ι := ι) (F := F) hε, rfl⟩

omit [DecidableEq F] in
/-- Concrete `epsStar = 2^-128` specialization: if `|F| < 2^128`, then the formal threshold
is below the exact zero-code MCA value `1 / |F|`. -/
theorem epsStar_lt_inv_card_of_card_lt_two_pow
    (hcard : Fintype.card F < 2 ^ (128 : ℕ)) :
    (epsStar : ENNReal) < (1 : ENNReal) / (Fintype.card F : ENNReal) := by
  set q := Fintype.card F with hq_def
  have heps : (epsStar : ENNReal) = (2 ^ (128 : ℕ) : ENNReal)⁻¹ := by
    rw [epsStar]
    push_cast
    rw [one_div]
  rw [heps]
  have hq0 : (q : ENNReal) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    rw [hq_def]
    exact Fintype.card_ne_zero
  have hqtop : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hq0) (Or.inl hqtop)]
  have hpow_ne_zero : (2 ^ (128 : ℕ) : ENNReal) ≠ 0 := by positivity
  have hpow_ne_top : (2 ^ (128 : ℕ) : ENNReal) ≠ ⊤ := by finiteness
  rw [← ENNReal.div_eq_inv_mul]
  rw [ENNReal.div_lt_iff (Or.inl hpow_ne_zero) (Or.inl hpow_ne_top)]
  have hcast : (q : ENNReal) < ((2 ^ (128 : ℕ) : ℕ) : ENNReal) := by
    exact_mod_cast (by simpa [hq_def] using hcard)
  calc
    (q : ENNReal) < ((2 ^ (128 : ℕ) : ℕ) : ENNReal) := hcast
    _ = (2 ^ (128 : ℕ) : ENNReal) := by norm_num [Nat.cast_pow]
    _ = (1 : ENNReal) * (2 ^ (128 : ℕ) : ENNReal) := by simp

omit [DecidableEq F] in
/-- Concrete `epsStar = 2^-128` lower-witness specialization: if `2^128 ≤ |F|`, then the exact
zero-code MCA value is within the formal threshold. -/
theorem inv_card_le_epsStar_of_two_pow_le_card
    (hcard : 2 ^ (128 : ℕ) ≤ Fintype.card F) :
    (1 : ENNReal) / (Fintype.card F : ENNReal) ≤ (epsStar : ENNReal) := by
  set q := Fintype.card F with hq_def
  have heps : (epsStar : ENNReal) = (2 ^ (128 : ℕ) : ENNReal)⁻¹ := by
    rw [epsStar]
    push_cast
    rw [one_div]
  rw [heps]
  have hq0 : (q : ENNReal) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    rw [hq_def]
    exact Fintype.card_ne_zero
  have hqtop : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
  rw [ENNReal.div_le_iff hq0 hqtop]
  have hpow_ne_zero : (2 ^ (128 : ℕ) : ENNReal) ≠ 0 := by positivity
  have hpow_ne_top : (2 ^ (128 : ℕ) : ENNReal) ≠ ⊤ := by finiteness
  rw [← ENNReal.div_eq_inv_mul]
  rw [ENNReal.le_div_iff_mul_le (Or.inl hpow_ne_zero) (Or.inl hpow_ne_top)]
  have hcast : ((2 ^ (128 : ℕ) : ℕ) : ENNReal) ≤ (q : ENNReal) := by
    exact_mod_cast (by simpa [hq_def] using hcard)
  calc
    (1 : ENNReal) * (2 ^ (128 : ℕ) : ENNReal)
        = ((2 ^ (128 : ℕ) : ℕ) : ENNReal) := by norm_num [Nat.cast_pow]
    _ ≤ (q : ENNReal) := hcast

/-- Field-size specialization of the zero-code upper witness at `epsStar`. -/
noncomputable def MCAUpperWitness_bot_epsStar_of_card_lt_two_pow
    (hcard : Fintype.card F < 2 ^ (128 : ℕ)) :
    GrandChallenges.MCAUpperWitness (F := F)
      (Cbot (ι := ι) (F := F) : Set (ι → F)) epsStar :=
  MCAUpperWitness_bot_epsStar_of_lt_inv_card
    (ι := ι) (F := F) (epsStar_lt_inv_card_of_card_lt_two_pow (F := F) hcard)

/-- Existential field-size specialization, preserving the certified radius `0`. -/
theorem exists_MCAUpperWitness_bot_epsStar_of_card_lt_two_pow
    (hcard : Fintype.card F < 2 ^ (128 : ℕ)) :
    ∃ w : GrandChallenges.MCAUpperWitness (F := F)
        (Cbot (ι := ι) (F := F) : Set (ι → F)) epsStar,
      w.δ = 0 :=
  ⟨MCAUpperWitness_bot_epsStar_of_card_lt_two_pow (ι := ι) (F := F) hcard, rfl⟩

/-- Field-size specialization of the zero-code lower witness at `epsStar`. -/
noncomputable def MCALowerWitness_bot_epsStar_of_two_pow_le_card
    (hcard : 2 ^ (128 : ℕ) ≤ Fintype.card F) :
    GrandChallenges.MCALowerWitness (F := F)
      (Cbot (ι := ι) (F := F) : Set (ι → F)) epsStar :=
  MCALowerWitness_bot_epsStar_of_inv_card_le
    (ι := ι) (F := F) (inv_card_le_epsStar_of_two_pow_le_card (F := F) hcard)

/-- Existential field-size lower-witness specialization, preserving the certified radius `0`. -/
theorem exists_MCALowerWitness_bot_epsStar_of_two_pow_le_card
    (hcard : 2 ^ (128 : ℕ) ≤ Fintype.card F) :
    ∃ w : GrandChallenges.MCALowerWitness (F := F)
        (Cbot (ι := ι) (F := F) : Set (ι → F)) epsStar,
      w.δ = 0 :=
  ⟨MCALowerWitness_bot_epsStar_of_two_pow_le_card (ι := ι) (F := F) hcard, rfl⟩

/-- Field-size specialization: any supplied zero-code MCA resolution at `epsStar` has threshold
exactly `0`. -/
theorem GrandMCAResolution_bot_deltaStar_eq_zero_of_card_lt_two_pow
    (hcard : Fintype.card F < 2 ^ (128 : ℕ))
    (R : GrandChallenges.GrandMCAResolution (F := F)
      (Cbot (ι := ι) (F := F) : Set (ι → F)) epsStar) :
    R.δStar = 0 :=
  GrandMCAResolution_bot_deltaStar_eq_zero_of_epsStar_lt_inv_card
    (ι := ι) (F := F) (epsStar_lt_inv_card_of_card_lt_two_pow (F := F) hcard) R

/-- Field-size specialization of the zero-code no-resolution guardrail at `epsStar`. -/
theorem not_GrandMCAResolution_bot_epsStar_of_card_lt_two_pow
    (hcard : Fintype.card F < 2 ^ (128 : ℕ)) :
    ¬ Nonempty (GrandChallenges.GrandMCAResolution (F := F)
      (Cbot (ι := ι) (F := F) : Set (ι → F)) epsStar) :=
  not_GrandMCAResolution_bot_epsStar_of_lt_inv_card
    (ι := ι) (F := F) (epsStar_lt_inv_card_of_card_lt_two_pow (F := F) hcard)

/-- Field-size specialization of the bottom-code Grand MCA predicate refutation at `epsStar`. -/
theorem not_grandMCAChallenge_bot_epsStar_of_card_lt_two_pow
    (hcard : Fintype.card F < 2 ^ (128 : ℕ)) :
    ¬ grandMCAChallenge (F := F) (ι := ι) (⊥ : LinearCode ι F) epsStar :=
  not_grandMCAChallenge_bot_epsStar_of_lt_inv_card
    (ι := ι) (F := F) (epsStar_lt_inv_card_of_card_lt_two_pow (F := F) hcard)

/-- Any zero-code MCA resolution at `epsStar` forces the field to have at least `2^128`
elements. This is the contrapositive form of the numeric zero-code no-resolution guardrail. -/
theorem card_two_pow_le_of_GrandMCAResolution_bot_epsStar
    (h : Nonempty (GrandChallenges.GrandMCAResolution (F := F)
      (Cbot (ι := ι) (F := F) : Set (ι → F)) epsStar)) :
    2 ^ (128 : ℕ) ≤ Fintype.card F :=
  Nat.le_of_not_gt fun hcard =>
    not_GrandMCAResolution_bot_epsStar_of_card_lt_two_pow (ι := ι) (F := F) hcard h

/-- If the bottom linear code satisfies the Grand MCA predicate at `epsStar`, then the field must
have at least `2^128` elements. This packages the numeric zero-code predicate refutation in the
caller-facing lower-bound direction. -/
theorem card_two_pow_le_of_grandMCAChallenge_bot_epsStar
    (h : grandMCAChallenge (F := F) (ι := ι) (⊥ : LinearCode ι F) epsStar) :
    2 ^ (128 : ℕ) ≤ Fintype.card F :=
  Nat.le_of_not_gt fun hcard =>
    not_grandMCAChallenge_bot_epsStar_of_card_lt_two_pow (ι := ι) (F := F) hcard h

end General

/-! ## Source audit -/

#print axioms MCAUpperWitness_bot_of_lt_inv_card
#print axioms exists_MCAUpperWitness_bot_of_lt_inv_card
#print axioms MCAUpperWitness_bot_epsStar_of_lt_inv_card
#print axioms exists_MCAUpperWitness_bot_epsStar_of_lt_inv_card
#print axioms GrandMCAResolution_bot_deltaStar_eq_zero_of_lt_inv_card
#print axioms GrandMCAResolution_bot_deltaStar_eq_zero_of_epsStar_lt_inv_card
#print axioms not_GrandMCAResolution_bot_of_lt_inv_card
#print axioms not_GrandMCAResolution_bot_epsStar_of_lt_inv_card
#print axioms not_grandMCAChallenge_bot_of_lt_inv_card
#print axioms not_grandMCAChallenge_bot_epsStar_of_lt_inv_card
#print axioms inv_card_le_of_GrandMCAResolution_bot
#print axioms inv_card_le_of_grandMCAChallenge_bot
#print axioms MCALowerWitness_bot_of_inv_card_le
#print axioms exists_MCALowerWitness_bot_of_inv_card_le
#print axioms MCALowerWitness_bot_epsStar_of_inv_card_le
#print axioms exists_MCALowerWitness_bot_epsStar_of_inv_card_le
#print axioms epsStar_lt_inv_card_of_card_lt_two_pow
#print axioms inv_card_le_epsStar_of_two_pow_le_card
#print axioms MCAUpperWitness_bot_epsStar_of_card_lt_two_pow
#print axioms exists_MCAUpperWitness_bot_epsStar_of_card_lt_two_pow
#print axioms MCALowerWitness_bot_epsStar_of_two_pow_le_card
#print axioms exists_MCALowerWitness_bot_epsStar_of_two_pow_le_card
#print axioms GrandMCAResolution_bot_deltaStar_eq_zero_of_card_lt_two_pow
#print axioms not_GrandMCAResolution_bot_epsStar_of_card_lt_two_pow
#print axioms not_grandMCAChallenge_bot_epsStar_of_card_lt_two_pow
#print axioms card_two_pow_le_of_GrandMCAResolution_bot_epsStar
#print axioms card_two_pow_le_of_grandMCAChallenge_bot_epsStar

end ProximityGap.MCAZeroCode

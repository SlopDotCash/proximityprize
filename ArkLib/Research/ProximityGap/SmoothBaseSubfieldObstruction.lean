/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.SmoothReservedListBoundary
import ArkLib.Research.ProximityGap.Frontier.ListScalarExtension
import ArkLib.Research.ProximityGap.Frontier.SmoothDomainMcaEquivalence

/-! # Field-size obstructions to attaining the base-length list thresholds -/

namespace ProximityPrize.SmoothBaseSubfieldObstruction

open Code Polynomial Finset ProximityGap GrandChallenges SmoothPrizeCapacityTable
open SmoothReservedListBoundary
open scoped NNReal ENNReal

variable {F I K : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I]
variable [Field K] [Fintype K]

omit [Fintype F] [DecidableEq F] in
/-- All roots of the smaller field's Frobenius polynomial belong to the embedded field. -/
private theorem preimage_of_frobenius (f : K →+* F) {x : F} (hx : x ^ Fintype.card K = x) :
    ∃ w, f w = x := by
  classical
  by_contra! h
  let S := insert x (univ.image f)
  let P : F[X] := X ^ Fintype.card K - X
  have fresh : x ∉ univ.image f := fun mem => by
    obtain ⟨w, _, e⟩ := mem_image.mp mem
    exact h w e
  have count : S.card = Fintype.card K + 1 := by
    simp [S, fresh, card_image_of_injective _ f.injective]
  apply FiniteField.X_pow_card_sub_X_ne_zero F (Fintype.one_lt_card (α := K))
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (f := fun i : S => i.val)
    Subtype.val_injective
  · intro i
    have mem := i.property
    rcases mem_insert.mp mem with eq | hi
    · simp [P, eq, hx]
    · obtain ⟨w, _, ew⟩ := mem_image.mp hi
      simp [P, ← ew, ← map_pow, FiniteField.pow_card]
  · rw [Fintype.card_coe, count]
    exact Nat.lt_succ_of_le (FiniteField.X_pow_card_sub_X_natDegree_eq F
      (Fintype.one_lt_card (α := K))).le

omit [Fintype F] in
/-- For any smooth coset, fixing the product and one further coefficient over a subfield
already obstructs the ambient budget when the subgroup order divides the subfield unit order. -/
theorem subfield_product_fails (D : I ↪ F) [ReedSolomon.Smooth D] (f : K →+* F)
    (divides : Fintype.card I ∣ Fintype.card K - 1) {j B : ℕ} (hj : 0 < j)
    (count : Fintype.card I * Fintype.card K * B < (Fintype.card I).choose (j + 2))
    (width : ℕ) [NeZero width] :
    (B : ℕ∞) < Lambda (ListInterpolationBoundary.words D j width)
      (gridPt (ι := I) (Fintype.card I - (j + 2)) : ℝ) := by
  classical
  obtain ⟨z, hz⟩ := SmoothDomainMcaEquivalence.coset_equiv D
  let H := ReedSolomon.Smooth.H D
  let a := ReedSolomon.Smooth.a D
  let := Fintype.ofEquiv I z
  have cH := Fintype.card_congr z
  have groupRoots (i : I) : ((z i : Fˣ) : F) ^ Fintype.card I = 1 := by
    rw [cH]
    exact congrArg (fun v : H => ((v : Fˣ) : F))
      (show (z i) ^ Fintype.card H = 1 from pow_card_eq_one)
  obtain ⟨r, hr⟩ := divides
  have hK : Fintype.card K = Fintype.card I * r + 1 := by have := Fintype.card_pos (α := K); omega
  have lift (i : I) : ∃ w, f w = ((z i : Fˣ) : F) := by
    apply preimage_of_frobenius f
    rw [hK, pow_succ, pow_mul, groupRoots, one_pow, one_mul]
  choose w hw using lift
  let E : I ↪ K := ⟨w, fun i j eq => z.injective (Subtype.ext (Units.ext
    ((hw i).symm.trans ((congrArg f eq).trans (hw j)))))⟩
  have ne (i : I) : w i ≠ 0 := fun zero => (z i : Fˣ).ne_zero (by simpa [zero] using (hw i).symm)
  let G := rootsOfUnity (Fintype.card I) K
  let := Fintype.ofFinite G
  let site (i : I) : G := ⟨Units.mk0 (w i) (ne i), (mem_rootsOfUnity _ _).mpr (Units.ext
    (show w i ^ Fintype.card I = 1 by apply f.injective; simpa [hw] using groupRoots i))⟩
  have hn : 0 < Fintype.card I := by
    obtain ⟨b, hb⟩ := ReedSolomon.Smooth.h_card_pow2 (domain := D)
    rw [hb]
    positivity
  let : NeZero (Fintype.card I) := ⟨hn.ne'⟩
  have cG : Fintype.card G ≤ Fintype.card I := by
    rw [← Nat.card_eq_fintype_card]
    exact card_rootsOfUnity K _
  have low := PrescribedProductList.exceeds_budget_deeper E G site (fun _ => rfl) 1 hj (B := B)
    (by rw [pow_one]; exact (Nat.mul_le_mul_right B (Nat.mul_le_mul_right _ cG)).trans_lt count)
  let δ := (gridPt (ι := I) (Fintype.card I - (j + 2)) : ℝ)
  have embedded := ListScalarExtension.lambda_le f E j δ
  have scaled : (ReedSolomon.code (E.trans ⟨f, f.injective⟩) j : Set (I → F)) ⊆
      ReedSolomon.code D j := by
    intro u hu
    have scale (i : I) : D i = (a : F) * (E.trans ⟨f, f.injective⟩) (Equiv.refl I i) := by
      change D i = (a : F) * f (w i)
      rw [hw]
      exact hz i
    exact SmoothDomainMcaEquivalence.mem_code_scale (Equiv.refl I) a scale hu
  apply ((low.trans_le embedded).trans_le (Lambda_mono_code scaled _)).trans_le
  let rep (x : F) := fun _ : Fin width => x
  apply Lambda_le_of_injective_comp (e := rep)
  · exact fun _ _ eq => congrFun eq (0 : Fin width)
  · exact fun _ hc _ => hc

/-- Exact largest ambient size excluded by the base-length two-coefficient inequality
when the product construction is run over the full alphabet, in prize rate order. -/
def fieldLimit : Fin 4 → ℕ :=
  ![86213937619545769194079459098654278053482227923193557853,
    14710087252655939189338400178512396969702309494783,
    2025842497317941427856674411260371347037,
    309383378205371379825515213835666128450703903]

/-- The integer cutoffs include the floor in the prize budget. Their successors are
the first alphabet sizes for which this particular sufficient failure inequality fails. -/
theorem field_cutoff_iff (i : Fin 4) (q : ℕ) :
    failureLength i * q * (q / 2 ^ 128) <
      (failureLength i).choose (failureLength i / prizeDenominator i + 2) ↔ q ≤ fieldLimit i := by
  let h := failureLength i
  let C := h.choose (h / prizeDenominator i + 2)
  have mono {v w : ℕ} (hle : v ≤ w) :
      h * v * (v / 2 ^ 128) ≤ h * w * (w / 2 ^ 128) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hle) (Nat.div_le_div_right hle)
  have below : h * fieldLimit i * (fieldLimit i / 2 ^ 128) < C := by
    dsimp only [C]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    fin_cases i <;> (set_option maxRecDepth 8192 in decide)
  have above : C ≤ h * (fieldLimit i + 1) * ((fieldLimit i + 1) / 2 ^ 128) := by
    dsimp only [C]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    fin_cases i <;> (set_option maxRecDepth 8192 in decide)
  constructor
  · intro bound
    by_contra! big
    exact bound.not_ge (above.trans (mono big))
  · exact fun small => (mono small).trans_lt below

/-- Largest subfield size excluded by the two-coefficient count even at the maximum
possible 128-bit list budget. The order-256 subgroup cannot occur in the entry 29. -/
def subfieldLimit : Fin 4 → ℕ :=
  ![64191285335851377283423097335403748, 1868751729097317649889, 29, 826637396689]

/-- A necessary numerical condition for the predecessor at the smallest eligible
length to pass on any supplied smooth coset over an extension of the specified field. -/
theorem necessary_product_bound (D : I ↪ F) [ReedSolomon.Smooth D] (f : K →+* F)
    (i : Fin 4) (width : ℕ) [NeZero width] (hlen : Fintype.card I = failureLength i)
    (divides : failureLength i ∣ Fintype.card K - 1)
    (safe : (Lambda (ListInterpolationBoundary.words D (prizeDimension (ι := I) i) width)
      (gridPt (ι := I) (errorCoefficient i) : ℝ) : ℝ≥0∞) ≤
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) * Fintype.card F) :
    (failureLength i).choose (failureLength i / prizeDenominator i + 2) ≤
      failureLength i * Fintype.card K * (Fintype.card F / 2 ^ 128) := by
  by_contra! small
  let j := prizeDimension (ι := I) i
  have hj : j = failureLength i / prizeDenominator i := by simp [j, prizeDimension, hlen]
  have pos : 0 < j := hj ▸ (by fin_cases i <;> decide)
  have low := subfield_product_fails D f (hlen ▸ divides) pos (by simpa only [hlen, hj] using small)
    width
  have e : Fintype.card I - (j + 2) = errorCoefficient i := by
    rw [hlen, hj]
    fin_cases i <;> decide
  rw [e] at low
  have upper := (ListSupportRank.lambda_le_floor_iff (K := F) _ _ _).mp safe
  change _ ≤ (RankReview.budget F (prizeThreshold : ℝ≥0) : ℕ∞) at upper
  rw [RankExecutable.prizeBudget] at upper
  exact low.not_ge upper

/-- All sufficiently small full alphabets already fail at the base predecessor. -/
theorem base_predecessor_fails (D : I ↪ F) [ReedSolomon.Smooth D] (i : Fin 4) (width : ℕ)
    [NeZero width] (hlen : Fintype.card I = failureLength i)
    (field : Fintype.card F ≤ fieldLimit i) :
    ((prizeThreshold : ℝ≥0) : ℝ≥0∞) * Fintype.card F <
      (Lambda (ListInterpolationBoundary.words D (prizeDimension (ι := I) i) width)
        (gridPt (ι := I) (errorCoefficient i) : ℝ) : ℝ≥0∞) := by
  classical
  apply lt_of_not_ge
  intro safe
  let := Fintype.ofFinite (ReedSolomon.Smooth.H D)
  obtain ⟨z, _⟩ := SmoothDomainMcaEquivalence.coset_equiv D
  have dvd := Subgroup.card_subgroup_dvd_card (ReedSolomon.Smooth.H D)
  simp only [Nat.card_eq_fintype_card, ← Fintype.card_congr z, Fintype.card_units, hlen] at dvd
  have required := necessary_product_bound D (RingHom.id F) i width hlen dvd safe
  exact ((field_cutoff_iff i _).mpr field).not_ge required

/-- Any possible realization at the base length excludes every embedded subfield up to
the indicated order that contains the required roots of unity. -/
theorem subfield_predecessor_fails (D : I ↪ F) [ReedSolomon.Smooth D] (f : K →+* F)
    (i : Fin 4) (width : ℕ) [NeZero width] (hlen : Fintype.card I = failureLength i)
    (divides : failureLength i ∣ Fintype.card K - 1) (small : Fintype.card K ≤ subfieldLimit i)
    (field : Fintype.card F < 2 ^ 256) :
    ((prizeThreshold : ℝ≥0) : ℝ≥0∞) * Fintype.card F <
      (Lambda (ListInterpolationBoundary.words D (prizeDimension (ι := I) i) width)
        (gridPt (ι := I) (errorCoefficient i) : ℝ) : ℝ≥0∞) := by
  apply lt_of_not_ge
  intro safe
  have required := necessary_product_bound D f i width hlen divides safe
  have bound := Nat.mul_le_mul (Nat.mul_le_mul_left (failureLength i) small)
    (prize_budget Fintype.card_pos field).1.le
  have count : failureLength i * subfieldLimit i * 2 ^ 128 <
      (failureLength i).choose (failureLength i / prizeDenominator i + 2) := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    fin_cases i <;> (set_option maxRecDepth 8192 in decide)
  exact (bound.trans_lt count).not_ge required

/-- Any candidate attaining one of the original four uniform list bounds must have the
base length, exceed the full-alphabet cutoff, and avoid all excluded embedded fields.
This gives necessary conditions for the three open rates and applies to the sharp eighth. -/
theorem attainment_requires [Nonempty I] (D : I ↪ F) [ReedSolomon.Smooth D] (i : Fin 4)
    (width : ℕ) [NeZero width] (hlen : failureLength i ≤ Fintype.card I)
    (field : Fintype.card F < 2 ^ 256)
    (accept : ∀ δ : ℝ≥0, δ < failureRadius i →
      (Lambda (ListInterpolationBoundary.words D (prizeDimension (ι := I) i) width)
        (δ : ℝ) : ℝ≥0∞) ≤ ((prizeThreshold : ℝ≥0) : ℝ≥0∞) * Fintype.card F) :
    Fintype.card I = failureLength i ∧ fieldLimit i < Fintype.card F ∧
      ∀ (K : Type) [Field K] [Fintype K], (K →+* F) → failureLength i ∣ Fintype.card K - 1 →
        subfieldLimit i < Fintype.card K := by
  have len : Fintype.card I = failureLength i := by
    by_contra ne
    have bad := longer_failure D i width (lt_of_le_of_ne hlen (Ne.symm ne)) field
    let δ := ((2 * errorCoefficient i + 1 : ℕ) : ℝ≥0) / (2 * (failureLength i : ℝ≥0))
    have smaller : δ < failureRadius i := by
      fin_cases i <;> norm_num [δ, errorCoefficient, failureLength, failureRadius]
    have safe := accept δ smaller
    exact bad.not_ge (by simpa [δ] using safe)
  have smaller : gridPt (ι := I) (errorCoefficient i) < failureRadius i := by
    rw [gridPt, len]
    fin_cases i <;> norm_num [errorCoefficient, failureLength, failureRadius]
  have safe := accept _ smaller
  refine ⟨len, lt_of_not_ge (fun small => (base_predecessor_fails D i width len small).not_ge safe),
    ?_⟩
  intro K _ _ f divides
  exact lt_of_not_ge fun small => (subfield_predecessor_fails D f i width len divides small
    field).not_ge safe

/-- A passing predecessor limits the extension degree above every subfield containing
the domain's roots of unity. For the three open rates the limits are two, three and six. -/
theorem extension_degree_le [Algebra K F] (D : I ↪ F) [ReedSolomon.Smooth D]
    (i : Fin 4) (width : ℕ) [NeZero width] (hlen : Fintype.card I = failureLength i)
    (divides : failureLength i ∣ Fintype.card K - 1) (field : Fintype.card F < 2 ^ 256)
    (safe : (Lambda (ListInterpolationBoundary.words D (prizeDimension (ι := I) i) width)
      (gridPt (ι := I) (errorCoefficient i) : ℝ) : ℝ≥0∞) ≤
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) * Fintype.card F) :
    Module.finrank K F ≤ (![2, 3, 31, 6] : Fin 4 → ℕ) i := by
  let d := (![2, 3, 31, 6] : Fin 4 → ℕ) i
  let b := max (subfieldLimit i + 1) (failureLength i + 1)
  have avoid : subfieldLimit i < Fintype.card K := lt_of_not_ge fun small =>
    (subfield_predecessor_fails D (algebraMap K F) i width hlen divides small field).not_ge safe
  have pos := Fintype.one_lt_card (α := K)
  have group := Nat.le_of_dvd (show 0 < Fintype.card K - 1 by omega) divides
  have lower : b ≤ Fintype.card K := max_le avoid (by omega)
  have tooLarge : 2 ^ 256 ≤ b ^ (d + 1) := by fin_cases i <;> decide
  change Module.finrank K F ≤ d
  by_contra! large
  apply field.not_ge
  calc
    2 ^ 256 ≤ b ^ (d + 1) := tooLarge
    _ ≤ Fintype.card K ^ (d + 1) := Nat.pow_le_pow_left lower _
    _ ≤ Fintype.card K ^ Module.finrank K F := Nat.pow_le_pow_right pos.le large
    _ = Fintype.card F := Module.card_eq_pow_finrank.symm

end ProximityPrize.SmoothBaseSubfieldObstruction

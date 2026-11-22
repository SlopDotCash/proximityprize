/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.JohnsonQuarticDomain
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread

/-! # A quartic witness at the length-sixteen MCA Johnson radius

For four distinct abscissae with fixed product g, the monic vanishing quartic
has constant coefficient g. Dividing the quartic identity by an abscissa shows
that x³ + g/x minus the sum of the four abscissae times x² is affine on these
four sites. A quadratic cannot agree with a degree-below-two word there. -/

namespace ProximityGap.JohnsonQuarticMca

open Code Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

private abbrev Site := Fin 16
private abbrev Quartet := Site × Site × Site × Site

private def sites (T : Quartet) : Finset Site := {T.1, T.2.1, T.2.2.1, T.2.2.2}

private def scalar (T : Quartet) : K :=
  -(domain T.1 + domain T.2.1 + domain T.2.2.1 + domain T.2.2.2)

private def quartets : List Quartet := do
  let a ← List.finRange 16
  let b ← List.finRange 16
  guard (a < b)
  let c ← List.finRange 16
  guard (b < c)
  let d := (1 - a - b - c : Fin 16)
  guard (c < d)
  return (a,b,c,d)

private def u (i : Site) : K := domain i ^ 3 + (generator : K) / domain i
private def v (i : Site) : K := domain i ^ 2

private theorem quartic_affine {F : Type*} [Field F] (a b c d x : F)
    (hx : x ≠ 0) (hit : x = a ∨ x = b ∨ x = c ∨ x = d) :
    (a*b*c + a*b*d + a*c*d + b*c*d) - (a*b+a*c+a*d+b*c+b*d+c*d)*x =
      x^3 + a*b*c*d/x + (-(a+b+c+d))*x^2 := by
  field_simp
  rcases hit with rfl | rfl | rfl | rfl <;> ring

private def valid (T : Quartet) : Prop :=
  (sites T).card = 4 ∧ domain T.1 * domain T.2.1 * domain T.2.2.1 * domain T.2.2.2 =
    (generator : K)

private instance (T : Quartet) : Decidable (valid T) := inferInstanceAs (Decidable (_ ∧ _))

set_option maxRecDepth 20000 in
private theorem certified : quartets.all (fun T => decide (valid T)) = true := by decide

set_option maxRecDepth 20000 in
private theorem distinct_count : ((quartets.map scalar).toFinset).card = 112 := by decide

private theorem event {T : Quartet} (hT : valid T) :
    mcaEvent (F := K) (ReedSolomon.code domain 2 : Set (Site → K)) (12/16) u v (scalar T) := by
  let a := domain T.1
  let b := domain T.2.1
  let c := domain T.2.2.1
  let d := domain T.2.2.2
  let intercept := a*b*c + a*b*d + a*c*d + b*c*d
  let slope := a*b+a*c+a*d+b*c+b*d+c*d
  refine ⟨sites T, ?_, ?_, ?_⟩
  · rw [hT.1, Fintype.card_fin, tsub_mul, one_mul]
    norm_num [tsub_le_iff_right]
  · refine ⟨fun i => intercept - slope * domain i, ?_, ?_⟩
    · apply ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval
        (C intercept - C slope * X)
      · apply (natDegree_sub_le ..).trans_lt
        refine max_lt (by rw [natDegree_C]; decide) ?_
        exact (natDegree_C_mul_le ..).trans_lt (by rw [natDegree_X]; decide)
      · intro i
        simp
    · intro i hi
      have hit : domain i = a ∨ domain i = b ∨ domain i = c ∨ domain i = d := by
        simp only [sites, Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
      have hx : domain i ≠ 0 := Units.ne_zero (generator ^ i.val)
      have eqn := quartic_affine a b c d (domain i) hx hit
      have hp : a*b*c*d = (generator : K) := hT.2
      rw [hp] at eqn
      exact eqn
  · rintro ⟨_, _, w, hw, hag⟩
    obtain ⟨q, hq, eval⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hw
    have eqn : q = X^2 := by
      apply eq_of_natDegree_lt_card_of_eval_eq q (X^2)
        (domain.injective.comp (Subtype.val_injective (p := fun i => i ∈ sites T)))
      · intro i
        simpa [v] using (eval i.val).trans (hag i.val i.property).2
      · rw [Fintype.card_coe, hT.1, natDegree_X_pow]
        omega
    rw [eqn, natDegree_X_pow] at hq
    omega

/-- The lifted quartic gives at least 112 distinct bad challenges at four agreements.
The integer 128-bit security budget on the same smooth code is 111. -/
theorem lower : (112 : ℝ≥0∞) / Fintype.card K ≤ epsMCA (F := K)
    (ReedSolomon.code domain 2 : Set (Fin 16 → K)) (12/16) := by
  have cert : ∀ γ ∈ (quartets.map scalar).toFinset,
      mcaEvent (F := K) (ReedSolomon.code domain 2 : Set (Site → K)) (12/16)
        (Code.finMapTwoWords u v 0) (Code.finMapTwoWords u v 1) γ := by
    intro γ hγ
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hγ)
    exact event (of_decide_eq_true (List.all_eq_true.mp certified T hT))
  have bound := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (F := K) (A := K) (ReedSolomon.code domain 2 : Set (Site → K)) (12/16)
    (Code.finMapTwoWords u v) (quartets.map scalar).toFinset cert
  simpa only [distinct_count, Nat.cast_ofNat] using bound

end ProximityGap.JohnsonQuarticMca

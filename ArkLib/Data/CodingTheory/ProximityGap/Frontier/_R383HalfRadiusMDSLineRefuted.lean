/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# R383: the unrestricted half-radius MDS line conjecture is false

For the `[8,4]` Reed--Solomon syndrome geometry over `ZMod 17`, let

```text
v(x) = (1,x,x^2,x^3),        L(gamma) = (1,gamma,0,0).
```

The eight roots of `x^8=1` form an `[8,4]` MDS Vandermonde parity frame.  The fixed
base point `L(0)` is outside every domain support span of size at most three, so the
line is globally jointly far.  The displayed certificates then put nine projectively
distinct affine points of `L` in proper three-column spans.  Consequently the line
has more than `n=8` proper weight-three points.

This refutes the field-uniform conjecture under its stated assumptions
`2e<n` and `e+k+1<=n`: here `(n,k,e)=(8,4,3)`.  It does not refute the
production-rate restriction `k<=n/4`, which remains the live half-radius target.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace ArkLib.ProximityGap.Frontier.R383HalfRadiusMDSLineRefuted

abbrev F := ZMod 17

instance factPrime17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- The full dyadic evaluation domain: all eighth roots of unity in `F_17`. -/
def dyadicDomain : Finset F := Finset.univ.filter fun x => x ^ 8 = 1

@[simp]
theorem mem_dyadicDomain_iff (x : F) : x ∈ dyadicDomain ↔ x ^ 8 = 1 := by
  simp [dyadicDomain]

theorem dyadicDomain_card : dyadicDomain.card = 8 := by decide

theorem ne_zero_of_mem_dyadicDomain {x : F} (hx : x ∈ dyadicDomain) : x ≠ 0 := by
  rw [mem_dyadicDomain_iff] at hx
  rintro rfl
  exact zero_ne_one hx

/-- The projectively normalized parity-check column.  Nonzero GRS column
weights do not change any support span. -/
def column (x : F) : Fin 4 -> F := fun j => x ^ (j : Nat)

/-- The affine chart of the counterexample projective syndrome line. -/
def linePoint (gamma : F) : Fin 4 -> F := fun j =>
  if j = 0 then 1 else if j = 1 then gamma else 0

/-- The affine chart uses nonzero, normalized representatives. -/
theorem linePoint_ne_zero (gamma : F) : linePoint gamma ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  change (1 : F) = 0 at h0
  exact (one_ne_zero : (1 : F) ≠ 0) h0

/-- Distinct affine parameters give distinct vector representatives. -/
theorem linePoint_injective : Function.Injective linePoint := by
  intro gamma beta h
  have h1 := congrFun h 1
  simpa [linePoint] using h1

/-- Normalization in coordinate zero makes the affine representatives projectively honest:
two representatives are proportional only when both the scalar and parameter agree. -/
theorem linePoint_eq_smul_iff {gamma beta lambda : F} :
    linePoint gamma = lambda • linePoint beta ↔ lambda = 1 ∧ gamma = beta := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [linePoint, Pi.smul_apply, smul_eq_mul] at h0 h1
    norm_num at h0 h1
    subst lambda
    exact ⟨rfl, by simpa using h1⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- Any at most four distinct Vandermonde columns are linearly independent. -/
theorem columns_linearIndependent_of_injective
    {m : ℕ} (hm : m ≤ 4) (x : Fin m → F) (hx : Function.Injective x) :
    LinearIndependent F (fun i ↦ column (x i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hcoord : ∀ j : Fin 4, ∑ i, g i * (x i) ^ (j : ℕ) = 0 := by
    intro j
    have h := congrFun hg j
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, column] using h
  have hgzero : g = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hx fun j => by
      simpa [Fin.val_castLE] using hcoord (Fin.castLE hm j)
  intro i
  exact congrFun hgzero i

/-- The eight-root Vandermonde family is a genuine `[8,4]` MDS parity frame: every
enumerated family of at most four distinct domain columns is linearly independent. -/
def IsDyadicMDSParityFrame : Prop :=
  ∀ {m : ℕ}, m ≤ 4 → ∀ (x : Fin m → F),
    (∀ i, x i ∈ dyadicDomain) → Function.Injective x →
      LinearIndependent F (fun i ↦ column (x i))

theorem dyadicDomain_is_mdsParityFrame : IsDyadicMDSParityFrame := by
  intro m hm x _hxDomain hx
  exact columns_linearIndependent_of_injective hm x hx

/-- A proper three-column certificate for one point of the syndrome line. -/
def properThreeColumnCertificate
    (gamma x y z a b c : F) : Prop :=
  x ^ 8 = 1 ∧ y ^ 8 = 1 ∧ z ^ 8 = 1 ∧
  x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
  linePoint gamma = a • column x + b • column y + c • column z

private theorem certificate_of_decide
    (gamma x y z a b c : F)
    (hroots : x ^ 8 = 1 ∧ y ^ 8 = 1 ∧ z ^ 8 = 1)
    (hdistinct : x ≠ y ∧ x ≠ z ∧ y ≠ z)
    (hpoint : ∀ j, linePoint gamma j =
      (a • column x + b • column y + c • column z) j) :
    properThreeColumnCertificate gamma x y z a b c := by
  exact ⟨hroots.1, hroots.2.1, hroots.2.2,
    hdistinct.1, hdistinct.2.1, hdistinct.2.2, funext hpoint⟩

theorem gamma_one : properThreeColumnCertificate 1 1 9 8 11 2 5 := by
  apply certificate_of_decide <;> decide
theorem gamma_two : properThreeColumnCertificate 2 1 16 2 2 5 11 := by
  apply certificate_of_decide <;> decide
theorem gamma_three : properThreeColumnCertificate 3 1 4 2 8 13 14 := by
  apply certificate_of_decide <;> decide
theorem gamma_four : properThreeColumnCertificate 4 1 13 15 1 7 10 := by
  apply certificate_of_decide <;> decide
theorem gamma_five : properThreeColumnCertificate 5 1 9 13 13 14 8 := by
  apply certificate_of_decide <;> decide
theorem gamma_six : properThreeColumnCertificate 6 1 13 8 5 10 3 := by
  apply certificate_of_decide <;> decide
theorem gamma_seven : properThreeColumnCertificate 7 1 15 4 10 3 5 := by
  apply certificate_of_decide <;> decide
theorem gamma_eight : properThreeColumnCertificate 8 1 16 8 7 4 7 := by
  apply certificate_of_decide <;> decide
theorem gamma_nine : properThreeColumnCertificate 9 1 9 16 4 7 7 := by
  apply certificate_of_decide <;> decide

/-- The base point of the projective line is outside the span of any three
nonzero Vandermonde columns.  Pairing with
`(X-x)(X-y)(X-z)` leaves the nonzero constant term `-xyz`. -/
theorem linePoint_zero_not_mem_threeColumnSpan
    {x y z : F} (hxyz : x * y * z ≠ 0) :
    ¬ ∃ a b c : F,
      linePoint 0 = a • column x + b • column y + c • column z := by
  rintro ⟨a, b, c, h⟩
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp [linePoint, column] at h0 h1 h2 h3
  have hprod : x * y * z = 0 := by
    linear_combination
      -h3 + (x + y + z) * h2 - (x * y + x * z + y * z) * h1 + (x * y * z) * h0
  exact hxyz hprod

/-- Membership in the span of the columns indexed by a finite support. -/
def InColumnSpan (S : Finset F) (p : Fin 4 → F) : Prop :=
  ∃ coeff : F → F, p = ∑ x ∈ S, coeff x • column x

/-- The global joint-farness premise for the counterexample line.  It quantifies over every
support of size zero through three in the full dyadic domain, rather than only the nine witness
supports used below. -/
def LineJointlyFar : Prop :=
  ∀ S : Finset F, S ⊆ dyadicDomain → S.card ≤ 3 →
    ¬ ∀ gamma : F, InColumnSpan S (linePoint gamma)

/-- The fixed base point is outside every admissible support span of size at most three.
Smaller supports are padded by repeated nonzero roots before applying the generic
three-column exclusion lemma. -/
theorem linePoint_zero_not_mem_admissibleSupportSpan
    {S : Finset F} (hS : S ⊆ dyadicDomain) (hcard : S.card ≤ 3) :
    ¬ InColumnSpan S (linePoint 0) := by
  rintro ⟨coeff, hpoint⟩
  have hcases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
  rcases hcases with hzero | hone | htwo | hthree
  · have hEmpty : S = ∅ := Finset.card_eq_zero.mp hzero
    subst S
    exact linePoint_ne_zero 0 (by simpa using hpoint)
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hone
    have hx0 : x ≠ 0 := ne_zero_of_mem_dyadicDomain (hS (by simp))
    apply linePoint_zero_not_mem_threeColumnSpan
      (mul_ne_zero (mul_ne_zero hx0 hx0) hx0)
    exact ⟨coeff x, 0, 0, by simpa using hpoint⟩
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp htwo
    have hx0 : x ≠ 0 := ne_zero_of_mem_dyadicDomain (hS (by simp))
    have hy0 : y ≠ 0 := ne_zero_of_mem_dyadicDomain (hS (by simp))
    apply linePoint_zero_not_mem_threeColumnSpan
      (mul_ne_zero (mul_ne_zero hx0 hy0) hx0)
    exact ⟨coeff x, coeff y, 0, by simpa [hxy, add_assoc] using hpoint⟩
  · obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hthree
    have hx0 : x ≠ 0 := ne_zero_of_mem_dyadicDomain (hS (by simp))
    have hy0 : y ≠ 0 := ne_zero_of_mem_dyadicDomain (hS (by simp))
    have hz0 : z ≠ 0 := ne_zero_of_mem_dyadicDomain (hS (by simp))
    apply linePoint_zero_not_mem_threeColumnSpan
      (mul_ne_zero (mul_ne_zero hx0 hy0) hz0)
    exact ⟨coeff x, coeff y, coeff z,
      by simpa [hxy, hxz, hyz, add_assoc] using hpoint⟩

/-- The counterexample line is not contained in any admissible dyadic support span of size at
most three.  This is the global jointly-far hypothesis of the refuted MDS-line conjecture. -/
theorem line_not_contained_in_any_admissible_threeSupportSpan : LineJointlyFar := by
  intro S hS hcard hcontained
  exact linePoint_zero_not_mem_admissibleSupportSpan hS hcard (hcontained 0)

/-- A parameter has a proper weight-three witness on the fixed dyadic domain. -/
def ProperGamma (gamma : F) : Prop :=
  ∃ x y z a b c : F,
    properThreeColumnCertificate gamma x y z a b c ∧
    ¬ ∃ a' b' c' : F,
      linePoint 0 = a' • column x + b' • column y + c' • column z

private theorem properGamma_of_certificate
    {gamma x y z a b c : F}
    (hcert : properThreeColumnCertificate gamma x y z a b c)
    (hxyz : x * y * z ≠ 0) :
    ProperGamma gamma :=
  ⟨x, y, z, a, b, c, hcert,
    linePoint_zero_not_mem_threeColumnSpan hxyz⟩

/-- The nine certified affine parameters. -/
def certifiedGammas : Finset F := {1, 2, 3, 4, 5, 6, 7, 8, 9}

theorem certifiedGammas_card : certifiedGammas.card = 9 := by decide

theorem certifiedGammas_are_proper : ∀ gamma ∈ certifiedGammas, ProperGamma gamma := by
  intro gamma hgamma
  simp only [certifiedGammas, Finset.mem_insert, Finset.mem_singleton] at hgamma
  rcases hgamma with h | h | h | h | h | h | h | h | h
  · subst gamma
    exact properGamma_of_certificate gamma_one (by decide)
  · subst gamma
    exact properGamma_of_certificate gamma_two (by decide)
  · subst gamma
    exact properGamma_of_certificate gamma_three (by decide)
  · subst gamma
    exact properGamma_of_certificate gamma_four (by decide)
  · subst gamma
    exact properGamma_of_certificate gamma_five (by decide)
  · subst gamma
    exact properGamma_of_certificate gamma_six (by decide)
  · subst gamma
    exact properGamma_of_certificate gamma_seven (by decide)
  · subst gamma
    exact properGamma_of_certificate gamma_eight (by decide)
  · subst gamma
    exact properGamma_of_certificate gamma_nine (by decide)

/-- The unrestricted proposed ceiling `#proper points <= n` fails already at
`(n,k,e,q)=(8,4,3,17)`: this set contains nine distinct proper parameters. -/
theorem exists_more_than_eight_proper_points :
    ∃ G : Finset F, 8 < G.card ∧ ∀ gamma ∈ G, ProperGamma gamma := by
  refine ⟨certifiedGammas, ?_, certifiedGammas_are_proper⟩
  rw [certifiedGammas_card]
  omega

/-- The numerical hypotheses of the refuted conjecture are satisfied. -/
theorem conjecture_hypotheses_hold : 2 * 3 < 8 ∧ 3 + 4 + 1 ≤ 8 := by omega

/-- The certified projective incidence count is strictly larger than the dyadic domain. -/
theorem dyadicDomain_card_lt_certifiedGammas_card :
    dyadicDomain.card < certifiedGammas.card := by
  rw [dyadicDomain_card, certifiedGammas_card]
  omega

/-- **Bundled R383 refutation.**  A genuine eight-column dyadic RS MDS parity frame admits a
globally jointly-far, projectively honest syndrome line with nine distinct proper affine points,
while the numerical hypotheses `2e<n` and `e+k+1≤n` both hold at `(n,k,e)=(8,4,3)`. -/
theorem unrestricted_halfRadius_mds_line_refuted :
    dyadicDomain.card = 8 ∧
    IsDyadicMDSParityFrame ∧
    LineJointlyFar ∧
    (∀ gamma : F, linePoint gamma ≠ 0) ∧
    Function.Injective linePoint ∧
    (∀ gamma beta lambda : F,
      linePoint gamma = lambda • linePoint beta ↔ lambda = 1 ∧ gamma = beta) ∧
    (∃ G : Finset F, G.card = 9 ∧ dyadicDomain.card < G.card ∧
      ∀ gamma ∈ G, ProperGamma gamma) ∧
    (2 * 3 < 8 ∧ 3 + 4 + 1 ≤ 8) := by
  refine ⟨dyadicDomain_card, dyadicDomain_is_mdsParityFrame,
    line_not_contained_in_any_admissible_threeSupportSpan, linePoint_ne_zero,
    linePoint_injective, ?_, ?_, conjecture_hypotheses_hold⟩
  · intro gamma beta lambda
    exact linePoint_eq_smul_iff
  · exact ⟨certifiedGammas, certifiedGammas_card,
      dyadicDomain_card_lt_certifiedGammas_card, certifiedGammas_are_proper⟩

end ArkLib.ProximityGap.Frontier.R383HalfRadiusMDSLineRefuted

#print axioms ArkLib.ProximityGap.Frontier.R383HalfRadiusMDSLineRefuted.gamma_one
#print axioms
  ArkLib.ProximityGap.Frontier.R383HalfRadiusMDSLineRefuted.exists_more_than_eight_proper_points
#print axioms
  ArkLib.ProximityGap.Frontier.R383HalfRadiusMDSLineRefuted.unrestricted_halfRadius_mds_line_refuted

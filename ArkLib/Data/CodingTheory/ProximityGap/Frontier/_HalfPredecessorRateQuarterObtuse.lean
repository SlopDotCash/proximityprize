/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.QuadraticForm.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorBadEventRichPointBridge

/-!
# Rate-quarter half predecessor: an obtuse-vector bound

This file records a sharp finite set-system bound at the endpoint where the
ordinary Johnson denominator loses its strict slack.  If equally large subsets
of an `n`-point universe have pair intersections at most `s` and

```text
n * s <= t^2 - 1,
```

then there are at most `n` of them.  The proof sends a block `A` to the vector

```text
x |-> n * 1_A(x) - (t - 1).
```

Distinct vectors have nonpositive Euclidean inner product, while their
coordinate sums are the same positive number `n`.  Serre's obtuse-vector lemma
therefore makes them linearly independent in `R^n`.

For the MCA application, truncate every selected full agreement to exactly
`h+1` coordinates.  A direction agreement cap of `k+1`, together with
`n=2h` and `2k<=h`, gives the endpoint budget

```text
(2h)(k+1) <= (h+1)^2 - 1.
```

Thus the selected bad-scalar family has cardinality at most `2h`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open _root_.ProximityGap Code
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterObtuse

attribute [local instance] Classical.propDecidable

/-! ## The abstract obtuse set-system bound -/

variable {I U : Type} [Fintype I] [Fintype U] [DecidableEq U]

/-- The centered incidence vector used in the endpoint Rankin--Serre argument. -/
noncomputable def centeredIncidenceVector
    (A : Finset U) (n t : ℕ) : U → ℝ :=
  fun x => (n : ℝ) * (if x ∈ A then 1 else 0) - ((t : ℝ) - 1)

/-- The coordinate sum of a centered incidence vector of a `t`-set in an
`n`-point universe is exactly `n`. -/
theorem sum_centeredIncidenceVector
    (A : Finset U) {n t : ℕ} (hn : Fintype.card U = n)
    (hA : A.card = t) :
    (∑ x : U, centeredIncidenceVector A n t x) = n := by
  classical
  simp [centeredIncidenceVector, hA, hn]
  ring

/-- The dot product of two centered incidence vectors depends only on the
intersection size. -/
theorem dot_centeredIncidenceVector
    (A B : Finset U) {n t : ℕ} (hn : Fintype.card U = n)
    (hA : A.card = t) (hB : B.card = t) :
    dotProduct (centeredIncidenceVector A n t)
        (centeredIncidenceVector B n t) =
      (n : ℝ) * ((n : ℝ) * ((A ∩ B).card : ℝ) - ((t : ℝ) ^ 2 - 1)) := by
  classical
  simp only [dotProduct, centeredIncidenceVector]
  have hinter :
      (∑ x : U,
        (if x ∈ A then (1 : ℝ) else 0) *
          (if x ∈ B then (1 : ℝ) else 0)) = (A ∩ B).card := by
    simp [Finset.inter_comm]
  have hsumA :
      (∑ x : U, (if x ∈ A then (1 : ℝ) else 0)) = A.card := by simp
  have hsumB :
      (∑ x : U, (if x ∈ B then (1 : ℝ) else 0)) = B.card := by simp
  let c : ℝ := (t : ℝ) - 1
  have hpoint (x : U) :
      ((n : ℝ) * (if x ∈ A then 1 else 0) - c) *
          ((n : ℝ) * (if x ∈ B then 1 else 0) - c) =
        (n : ℝ) ^ 2 *
            ((if x ∈ A then 1 else 0) * (if x ∈ B then 1 else 0)) -
          (n : ℝ) * c * (if x ∈ A then 1 else 0) -
          (n : ℝ) * c * (if x ∈ B then 1 else 0) + c ^ 2 := by
    ring
  change (∑ x : U,
      ((n : ℝ) * (if x ∈ A then 1 else 0) - c) *
        ((n : ℝ) * (if x ∈ B then 1 else 0) - c)) = _
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hinter, hsumA, hsumB]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [hA, hB, hn]
  norm_num [c]
  ring

/-- **Endpoint obtuse set-system bound.**  Equal-size blocks with
`n*s <= t^2-1` and pair intersections at most `s` form a family of size at
most the universe size. -/
theorem card_le_universe_of_equal_card_pair_inter_le
    (S : I → Finset U) (n t s : ℕ)
    (hn : Fintype.card U = n) (ht : 1 ≤ t)
    (hsize : ∀ i, (S i).card = t)
    (hpair : Pairwise fun i j => (S i ∩ S j).card ≤ s)
    (hbudget : n * s ≤ t ^ 2 - 1) :
    Fintype.card I ≤ n := by
  by_cases hI : IsEmpty I
  · letI : IsEmpty I := hI
    simp
  letI : Nonempty I := not_isEmpty_iff.mp hI
  have hnpos : 0 < n := by
    have htu : t ≤ Fintype.card U := by
      simpa only [hsize (Classical.choice inferInstance)] using
        Finset.card_le_univ (S (Classical.choice inferInstance))
    omega
  let B : LinearMap.BilinForm ℝ (U → ℝ) := dotProductBilin ℝ ℝ
  have hB : B.toQuadraticMap.PosDef := by
    intro x hx
    change 0 < dotProduct x x
    obtain ⟨a, ha⟩ : ∃ a, x a ≠ 0 := by
      by_contra hnot
      simp only [not_exists, not_not] at hnot
      exact hx (funext hnot)
    exact Finset.sum_pos' (fun i _ => mul_self_nonneg (x i))
      ⟨a, by simpa [dotProduct, sq] using sq_pos_of_ne_zero ha⟩
  let f : Module.Dual ℝ (U → ℝ) :=
    { toFun := fun x => ∑ a, x a
      map_add' := by
        intro x y
        exact Finset.sum_add_distrib
      map_smul' := by
        intro c x
        simp [Finset.mul_sum] }
  let v : I → U → ℝ := fun i => centeredIncidenceVector (S i) n t
  have hp : ∀ i, 0 < f (v i) := by
    intro i
    change 0 < ∑ x : U, centeredIncidenceVector (S i) n t x
    rw [sum_centeredIncidenceVector (S i) hn (hsize i)]
    exact_mod_cast hnpos
  have hnonpos : Pairwise fun i j => B (v i) (v j) ≤ 0 := by
    intro i j hij
    change dotProduct (centeredIncidenceVector (S i) n t)
      (centeredIncidenceVector (S j) n t) ≤ 0
    rw [dot_centeredIncidenceVector (S i) (S j) hn (hsize i) (hsize j)]
    have hpairs := hpair hij
    have hnat : n * (S i ∩ S j).card ≤ t ^ 2 - 1 :=
      le_trans (Nat.mul_le_mul_left n hpairs) hbudget
    have ht2 : 1 ≤ t ^ 2 := by nlinarith
    have hreal :
        (n : ℝ) * (((S i ∩ S j).card : ℝ)) ≤ (t : ℝ) ^ 2 - 1 := by
      rw [← Nat.cast_pow, ← Nat.cast_one, ← Nat.cast_sub ht2]
      exact_mod_cast hnat
    nlinarith
  have hli : LinearIndependent ℝ v :=
    LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero
      B hB f v hp hnonpos
  have hcard := hli.fintype_card_le_finrank
  rw [Module.finrank_pi, hn] at hcard
  exact hcard

/-! ## MCA rate-quarter application -/

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- The received direction is allowed one coordinate beyond the generic
degree-`<k` root cap. -/
def DirectionAgreementCapSucc (dom : ι ↪ F) (u1 : ι → F) (k : ℕ) : Prop :=
  ∀ r : F[X], r.natDegree < k →
    (Finset.univ.filter fun i => r.eval (dom i) = u1 i).card ≤ k + 1

/-- Distinct selected full agreements meet in at most `k+1` coordinates under
the successor direction cap. -/
theorem pair_inter_card_le_of_directionAgreementCapSucc
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hdir : DirectionAgreementCapSucc dom (u 1) k)
    {gamma beta : F} (hgamma : gamma ∈ family.G)
    (hbeta : beta ∈ family.G) (hne : gamma ≠ beta) :
    (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
      fullAgreement dom (u 0) (u 1) beta (family.q beta)).card ≤ k + 1 := by
  let r := slopePolynomial gamma beta (family.q gamma) (family.q beta)
  let roots := Finset.univ.filter fun i => r.eval (dom i) = u 1 i
  have hrdeg : r.natDegree < k :=
    slopePolynomial_natDegree_lt
      (family.degree_lt gamma hgamma) (family.degree_lt beta hbeta)
  have hsub :
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
          fullAgreement dom (u 0) (u 1) beta (family.q beta) ⊆ roots := by
    intro i hi
    have hi' := Finset.mem_inter.mp hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ i, ?_⟩
    exact slopePolynomial_eval_eq_direction
      dom (u 0) (u 1) hne hi'.1 hi'.2
  exact (Finset.card_le_card hsub).trans (hdir r hrdeg)

/-- **General endpoint budget.**  Any uniform pair cap `s` satisfying
`2*s <= h+2` forces the sharp domain-size bound. -/
theorem card_le_two_mul_of_pair_inter_le_of_two_mul_cap_le
    {dom : ι ↪ F} {k h s : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hn : Fintype.card ι = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hcap : 2 * s ≤ h + 2)
    (hpair : ∀ gamma ∈ family.G, ∀ beta ∈ family.G, gamma ≠ beta →
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
        fullAgreement dom (u 0) (u 1) beta (family.q beta)).card ≤ s) :
    family.G.card ≤ 2 * h := by
  let K := {gamma // gamma ∈ family.G}
  let A : K → Finset ι := fun gamma =>
    fullAgreement dom (u 0) (u 1) gamma.1 (family.q gamma.1)
  have hlarge : ∀ gamma : K, h + 1 ≤ (A gamma).card := by
    intro gamma
    rw [← hthreshold]
    exact family.threshold_le gamma.1 gamma.2
  let T : K → Finset ι := fun gamma =>
    Classical.choose (Finset.exists_subset_card_eq (hlarge gamma))
  have hTsub : ∀ gamma : K, T gamma ⊆ A gamma := by
    intro gamma
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hlarge gamma))).1
  have hTcard : ∀ gamma : K, (T gamma).card = h + 1 := by
    intro gamma
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hlarge gamma))).2
  have hTpair : Pairwise fun gamma beta : K =>
      (T gamma ∩ T beta).card ≤ s := by
    intro gamma beta hne
    apply le_trans (Finset.card_le_card
      (Finset.inter_subset_inter (hTsub gamma) (hTsub beta)))
    apply hpair gamma.1 gamma.2 beta.1 beta.2
    intro heq
    exact hne (Subtype.ext heq)
  have hbudget : (2 * h) * s ≤ (h + 1) ^ 2 - 1 := by
    have hmul := Nat.mul_le_mul_left h hcap
    have hsquare : (h + 1) ^ 2 - 1 = h * (h + 2) := by
      rw [show (h + 1) ^ 2 = h * (h + 2) + 1 by ring]
      omega
    rw [hsquare]
    nlinarith
  have hcard := card_le_universe_of_equal_card_pair_inter_le
    T (2 * h) (h + 1) s hn (by omega) hTcard hTpair hbudget
  simpa only [K, Fintype.card_coe] using hcard

/-- **Exact family-level rate-quarter branch.**  Pair intersections at most
`k+1` already force the sharp domain-size bound; no global direction predicate
is needed once this pair cap is available. -/
theorem card_le_two_mul_of_pair_inter_le_succ
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hn : Fintype.card ι = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 2 * k ≤ h)
    (hpair : ∀ gamma ∈ family.G, ∀ beta ∈ family.G, gamma ≠ beta →
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
        fullAgreement dom (u 0) (u 1) beta (family.q beta)).card ≤ k + 1) :
    family.G.card ≤ 2 * h := by
  apply card_le_two_mul_of_pair_inter_le_of_two_mul_cap_le
    family hn hthreshold (s := k + 1) (by omega) hpair

/-- A rate-quarter family is already bounded by the domain size unless it
contains a concrete exceptional pair with agreement intersection at least
`k+2`.  This is the exact residual left by the obtuse-vector argument. -/
theorem card_le_two_mul_or_exists_large_pair
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hn : Fintype.card ι = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 2 * k ≤ h) :
    family.G.card ≤ 2 * h ∨
      ∃ gamma ∈ family.G, ∃ beta ∈ family.G, gamma ≠ beta ∧
        k + 2 ≤
          (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
            fullAgreement dom (u 0) (u 1) beta (family.q beta)).card := by
  by_cases hex :
      ∃ gamma ∈ family.G, ∃ beta ∈ family.G, gamma ≠ beta ∧
        k + 2 ≤
          (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
            fullAgreement dom (u 0) (u 1) beta (family.q beta)).card
  · exact Or.inr hex
  · apply Or.inl
    apply card_le_two_mul_of_pair_inter_le_succ family hn hthreshold hrate
    intro gamma hgamma beta hbeta hne
    by_contra hnot
    apply hex
    exact ⟨gamma, hgamma, beta, hbeta, hne, by omega⟩

/-- The strongest rate-independent endpoint localization: a family larger
than the domain forces a pair intersection of size at least
`floor(h/2)+2`. -/
theorem card_le_two_mul_or_exists_pair_core_ge_half_add_two
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hn : Fintype.card ι = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1) :
    family.G.card ≤ 2 * h ∨
      ∃ gamma ∈ family.G, ∃ beta ∈ family.G, gamma ≠ beta ∧
        h / 2 + 2 ≤
          (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
            fullAgreement dom (u 0) (u 1) beta (family.q beta)).card := by
  by_cases hex :
      ∃ gamma ∈ family.G, ∃ beta ∈ family.G, gamma ≠ beta ∧
        h / 2 + 2 ≤
          (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
            fullAgreement dom (u 0) (u 1) beta (family.q beta)).card
  · exact Or.inr hex
  · apply Or.inl
    apply card_le_two_mul_of_pair_inter_le_of_two_mul_cap_le
      family hn hthreshold (s := h / 2 + 1) (by omega)
    intro gamma hgamma beta hbeta hne
    by_contra hnot
    apply hex
    exact ⟨gamma, hgamma, beta, hbeta, hne, by omega⟩

/-- Two units of rate slack make the first exceptional band `k+2`
harmless. -/
theorem card_le_two_mul_of_pair_inter_le_k_add_two_of_rate_slack
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hn : Fintype.card ι = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 2 * k + 2 ≤ h)
    (hpair : ∀ gamma ∈ family.G, ∀ beta ∈ family.G, gamma ≠ beta →
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
        fullAgreement dom (u 0) (u 1) beta (family.q beta)).card ≤ k + 2) :
    family.G.card ≤ 2 * h := by
  apply card_le_two_mul_of_pair_inter_le_of_two_mul_cap_le
    family hn hthreshold (s := k + 2) (by omega) hpair

/-- Away from rate saturation, a family larger than the domain forces a pair
core at least `k+3`, not merely `k+2`. -/
theorem card_le_two_mul_or_exists_pair_core_ge_k_add_three_of_rate_slack
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hn : Fintype.card ι = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 2 * k + 2 ≤ h) :
    family.G.card ≤ 2 * h ∨
      ∃ gamma ∈ family.G, ∃ beta ∈ family.G, gamma ≠ beta ∧
        k + 3 ≤
          (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
            fullAgreement dom (u 0) (u 1) beta (family.q beta)).card := by
  by_cases hex :
      ∃ gamma ∈ family.G, ∃ beta ∈ family.G, gamma ≠ beta ∧
        k + 3 ≤
          (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
            fullAgreement dom (u 0) (u 1) beta (family.q beta)).card
  · exact Or.inr hex
  · apply Or.inl
    apply card_le_two_mul_of_pair_inter_le_k_add_two_of_rate_slack
      family hn hthreshold hrate
    intro gamma hgamma beta hbeta hne
    by_contra hnot
    apply hex
    exact ⟨gamma, hgamma, beta, hbeta, hne, by omega⟩

/-- **Obtuse-vector rate-quarter branch.**  At the half predecessor, the
successor direction cap bounds the selected bad-scalar family by the domain
size. -/
theorem card_le_two_mul_of_directionAgreementCapSucc
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hn : Fintype.card ι = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 2 * k ≤ h)
    (hdir : DirectionAgreementCapSucc dom (u 1) k) :
    family.G.card ≤ 2 * h := by
  apply card_le_two_mul_of_pair_inter_le_succ family hn hthreshold hrate
  intro gamma hgamma beta hbeta hne
  exact pair_inter_card_le_of_directionAgreementCapSucc
    family hdir hgamma hbeta hne

/-- Literal bad-event-filter form of the obtuse-vector rate-quarter branch. -/
theorem badScalar_count_le_two_mul_of_directionAgreementCapSucc
    (dom : ι ↪ F) {k h : ℕ} (delta : ℝ≥0)
    (u : WordStack F (Fin 2) ι)
    (hk : 1 ≤ k)
    (hn : Fintype.card ι = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 2 * k ≤ h)
    (hdir : DirectionAgreementCapSucc dom (u 1) k) :
    (Finset.univ.filter fun gamma : F =>
      mcaEvent ((ReedSolomon.code dom k : Set (ι → F)))
        delta (u 0) (u 1) gamma).card ≤ 2 * h := by
  obtain ⟨family, hcount⟩ :=
    exists_richPointFamily_with_badScalar_count dom delta u hk
  rw [hcount]
  exact card_le_two_mul_of_directionAgreementCapSucc
    family hn hthreshold hrate hdir

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterObtuse

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterObtuse
#print axioms card_le_universe_of_equal_card_pair_inter_le
#print axioms card_le_two_mul_of_pair_inter_le_of_two_mul_cap_le
#print axioms card_le_two_mul_of_pair_inter_le_succ
#print axioms card_le_two_mul_or_exists_large_pair
#print axioms card_le_two_mul_or_exists_pair_core_ge_half_add_two
#print axioms card_le_two_mul_of_pair_inter_le_k_add_two_of_rate_slack
#print axioms card_le_two_mul_or_exists_pair_core_ge_k_add_three_of_rate_slack
#print axioms card_le_two_mul_of_directionAgreementCapSucc
#print axioms badScalar_count_le_two_mul_of_directionAgreementCapSucc

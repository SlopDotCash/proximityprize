/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterSuccessorSplitCriterion
import ArkLib.Research.ProximityGap.Frontier._P1RateQuarterCanonicalCodeBridge

/-! # One divisibility test for the quarter-rate successor pencil

On an injective domain a nonzero polynomial divides the nodal product exactly when
its degree is exhausted by distinct domain roots. Applying this to the product
of the zero, pole and unit fibers detects their sizes and mutual disjointness.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
namespace ArkLib.ProximityGap.Frontier.QuarterSplitPencilProduct

open Finset Polynomial Lagrange QuarterSuccessorSplitCriterion
variable {I F : Type} [Fintype I] [Field F]

open scoped Classical in
/-- The coordinates on which a polynomial vanishes. -/
noncomputable def sites (D : I ↪ F) (P : F[X]) : Finset I := univ.filter (fun i => P.eval (D i) = 0)

private theorem sites_dvd (D : I ↪ F) (P : F[X]) : nodal (sites D P) D ∣ P := by
  classical
  exact prod_X_sub_C_dvd _ _ D.injective.injOn _ fun _ hi => (mem_filter.mp hi).2

private theorem sites_le (D : I ↪ F) {P : F[X]} (hP : P ≠ 0) :
    (sites D P).card ≤ P.natDegree := by
  simpa using natDegree_le_of_dvd (sites_dvd D P) hP

open scoped Classical in
private theorem sites_mul (D : I ↪ F) (P Q : F[X]) :
    sites D (P * Q) = sites D P ∪ sites D Q := by
  ext i
  simp [sites, eval_mul, mul_eq_zero]

/-- A divisor of a simple nodal product has exactly its degree many distinct domain roots.
Conversely those roots suffice to certify divisibility. -/
theorem dvd_nodal_iff_sites (D : I ↪ F) {P : F[X]} (hP : P ≠ 0) :
    P ∣ nodal univ D ↔ (sites D P).card = P.natDegree := by
  classical
  constructor
  · rintro ⟨Q, hQ⟩
    have hnQ : Q ≠ 0 := fun h => nodal_ne_zero (by simpa [h] using hQ)
    have hu : sites D P ∪ sites D Q = univ := by
      rw [← sites_mul, ← hQ]
      apply filter_true_of_mem
      exact fun i hi => eval_nodal_at_node hi
    have hcard := card_union_le (sites D P) (sites D Q)
    rw [hu, card_univ] at hcard
    have hdeg := congrArg natDegree hQ
    rw [natDegree_nodal, card_univ, natDegree_mul hP hnQ] at hdeg
    have hp := sites_le D hP
    have hq := sites_le D hnQ
    omega
  · intro he
    have hd := associated_of_dvd_of_natDegree_le (sites_dvd D P) hP
      (by rw [natDegree_nodal, he])
    exact hd.symm.dvd.trans (prod_dvd_prod_of_subset _ _ _ (subset_univ _))

/-- The criterion holds on every injective finite domain longer than the degree cap. -/
theorem three_fibers_iff_product (D : I ↪ F) {d : ℕ} (hn : d < Fintype.card I) (P Q : F[X]) :
    (P.natDegree ≤ d ∧ Q.natDegree ≤ d ∧ (sites D P).card = d ∧ (sites D Q).card = d ∧
      (sites D (P - Q)).card = d ∧ ∀ i, P.eval (D i) = 0 → Q.eval (D i) ≠ 0) ↔
    (P.natDegree = d ∧ Q.natDegree = d ∧ (P - Q).natDegree = d ∧
      P * Q * (P - Q) ∣ nodal univ D) := by
  classical
  have nz {f : F[X]} (hf : (sites D f).card = d) : f ≠ 0 := by
    rintro rfl
    simp [sites] at hf
    omega
  constructor
  · rintro ⟨hp, hq, hA, hB, hC, hab⟩
    have pn := nz hA
    have qn := nz hB
    have rn := nz hC
    have dP := sites_le D pn
    have dQ := sites_le D qn
    have dR := sites_le D rn
    have dr := natDegree_sub_le P Q
    have dp : P.natDegree = d := by omega
    have dq : Q.natDegree = d := by omega
    have dd : (P - Q).natDegree = d := by omega
    have hdis : Disjoint (sites D P) (sites D Q) := by
      apply Finset.disjoint_left.mpr
      exact fun _ hi hj => hab _ (mem_filter.mp hi).2 (mem_filter.mp hj).2
    have hdis' : Disjoint (sites D P ∪ sites D Q) (sites D (P - Q)) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      have eq : (P - Q).eval (D i) = 0 := (mem_filter.mp hj).2
      rw [eval_sub, sub_eq_zero] at eq
      rcases mem_union.mp hi with ha | hb
      · exact hab i (mem_filter.mp ha).2 (eq.symm.trans (mem_filter.mp ha).2)
      · exact hab i (eq.trans (mem_filter.mp hb).2) (mem_filter.mp hb).2
    refine ⟨dp, dq, dd, (dvd_nodal_iff_sites D (mul_ne_zero (mul_ne_zero pn qn) rn)).mpr ?_⟩
    rw [sites_mul, sites_mul, card_union_of_disjoint hdis', card_union_of_disjoint hdis,
      hA, hB, hC, natDegree_mul (mul_ne_zero pn qn) rn, natDegree_mul pn qn, dp, dq, dd]
  · rintro ⟨dp, dq, dd, dvd⟩
    have nW : P * Q * (P - Q) ≠ 0 := fun h => nodal_ne_zero (zero_dvd_iff.mp (h ▸ dvd))
    obtain ⟨hpq, hr⟩ := mul_ne_zero_iff.mp nW
    obtain ⟨hp, hq⟩ := mul_ne_zero_iff.mp hpq
    have card := (dvd_nodal_iff_sites D nW).mp dvd
    rw [sites_mul, sites_mul, natDegree_mul hpq hr, natDegree_mul hp hq, dp, dq, dd] at card
    have ha := sites_le D hp
    have hb := sites_le D hq
    have hc := sites_le D hr
    have hu := card_union_le (sites D P ∪ sites D Q) (sites D (P - Q))
    have hi := card_union_add_card_inter (sites D P) (sites D Q)
    have hz : (sites D P ∩ sites D Q).card = 0 := by omega
    refine ⟨dp.le, dq.le, by omega, by omega, by omega, ?_⟩
    intro i hi hj
    have hmem : i ∈ sites D P ∩ sites D Q := by simp [sites, hi, hj]
    rw [card_eq_zero.mp hz] at hmem
    exact notMem_empty _ hmem

/-- The quarter-rate pencil is equivalent to one divisibility by the domain nodal polynomial. -/
theorem splitPencil_iff_nodal (D : I ↪ F) (hn : 268435454 < Fintype.card I) :
    splitPencil D ↔ ∃ P Q : F[X], P.natDegree = 268435454 ∧ Q.natDegree = 268435454 ∧
      (P - Q).natDegree = 268435454 ∧ P * Q * (P - Q) ∣ nodal univ D := by
  classical
  unfold splitPencil
  refine exists_congr fun P => exists_congr fun Q => ?_
  simpa [sites, eval_sub, sub_eq_zero] using three_fibers_iff_product D hn P Q

/-- Every factor pair of the nodal product is coprime. -/
theorem isCoprime_of_mul_dvd_nodal (D : I ↪ F) {P Q : F[X]} (h : P * Q ∣ nodal univ D) :
    IsCoprime P Q := by
  have hsq : Squarefree (nodal univ D) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · exact fun i _ j _ hij => (pairwise_coprime_X_sub_C D.injective hij).isRelPrime
    · exact fun i _ => (irreducible_X_sub_C (D i)).squarefree
  exact isRelPrime_iff_isCoprime.mp (IsRelPrime.of_squarefree_mul (.squarefree_of_dvd h hsq))

/-- Distinct `n`th roots of unity indexed by a type of size `n` exhaust the
roots of `X^n - 1`. -/
theorem nodal_eq_power (D : I ↪ F) {n : ℕ} (hn : Fintype.card I = n) (hpos : 0 < n)
    (roots : ∀ i, D i ^ n = 1) : nodal univ D = (Polynomial.X : F[X]) ^ n - 1 := by
  symm
  apply eq_of_monic_of_dvd_of_natDegree_le (nodal_monic ..) (monic_X_pow_sub_one hpos.ne')
  · apply Polynomial.prod_X_sub_C_dvd _ _ D.injective.injOn
    intro i _
    simp [roots i]
  · rw [← map_one Polynomial.C, natDegree_X_pow_sub_C, natDegree_nodal, card_univ, hn]

/-- On an injective domain exhausting the `n`th roots, the nodal criterion becomes
one divisibility by the explicit binomial. -/
theorem splitPencil_iff_power (D : I ↪ F) {n : ℕ} (hn : Fintype.card I = n)
    (hlarge : 268435454 < n) (roots : ∀ i, D i ^ n = 1) :
    splitPencil D ↔ ∃ P Q : F[X], P.natDegree = 268435454 ∧ Q.natDegree = 268435454 ∧
      (P - Q).natDegree = 268435454 ∧ P * Q * (P - Q) ∣ (Polynomial.X : F[X]) ^ n - 1 := by
  rw [← nodal_eq_power D hn (by omega) roots]
  exact splitPencil_iff_nodal D (hn ▸ hlarge)

open P1RateQuarterCanonicalCodeBridge (canonicalDomain)
local instance : Fact (Nat.Prime PrizeShapePrimeP30.P) := ⟨PrizeShapePrimeP30.prime_P⟩

/-- On the first designated cyclic subgroup the entire pencil condition reduces to one
divisibility by `X^(2^30) - 1`, with all three degrees fixed. -/
theorem first_prime : splitPencil canonicalDomain ↔ ∃ P Q : (ZMod PrizeShapePrimeP30.P)[X],
    P.natDegree = 268435454 ∧ Q.natDegree = 268435454 ∧ (P - Q).natDegree = 268435454 ∧
      P * Q * (P - Q) ∣
        (Polynomial.X : (ZMod PrizeShapePrimeP30.P)[X]) ^ (2 ^ 30 : ℕ) - 1 := by
  have hN : Fintype.card (Fin P1RateQuarterScaleArithmetic.N) = 2 ^ 30 := Fintype.card_fin _
  have hlarge : 268435454 < 2 ^ 30 := by decide
  have roots (i : Fin P1RateQuarterScaleArithmetic.N) : canonicalDomain i ^ (2 ^ 30 : ℕ) = 1 := by
    change (PrizeShapePrimeP30.g ^ (i : ℕ)) ^ (2 ^ 30 : ℕ) = 1
    have hg := congrArg (fun n : ℕ => PrizeShapePrimeP30.g ^ n) PrizeShapePrimeP30.orderOf_g
    rw [← pow_mul, Nat.mul_comm, pow_mul, ← hg, pow_orderOf_eq_one, one_pow]
  exact @splitPencil_iff_power (Fin P1RateQuarterScaleArithmetic.N) (ZMod PrizeShapePrimeP30.P)
    _ _ canonicalDomain (2 ^ 30) hN hlarge roots

end ArkLib.ProximityGap.Frontier.QuarterSplitPencilProduct

#print axioms ArkLib.ProximityGap.Frontier.QuarterSplitPencilProduct.dvd_nodal_iff_sites
#print axioms ArkLib.ProximityGap.Frontier.QuarterSplitPencilProduct.three_fibers_iff_product
#print axioms ArkLib.ProximityGap.Frontier.QuarterSplitPencilProduct.isCoprime_of_mul_dvd_nodal
#print axioms ArkLib.ProximityGap.Frontier.QuarterSplitPencilProduct.first_prime

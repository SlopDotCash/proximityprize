/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Monic polynomials over a domain factor into monic irreducibles

`exists_monic_irreducible_factorization`: every monic polynomial of positive degree over a
commutative domain is a product of **monic irreducible** factors.  No unique-factorization
hypothesis is needed: the proof is strong induction on the degree — in a reducible monic
polynomial both cofactors have unit leading coefficients (their product is `1`), hence can be
normalized to monic, and a nonunit with unit leading coefficient has positive degree.

This repairs the `Y`-monicity defect of `UniqueFactorizationMonoid.factors` over a polynomial
base ring (normalization there is by base-ring units, which does not produce `Y`-monic
factors).
-/

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Every monic polynomial of positive degree over a domain is a product of monic
irreducible factors. -/
theorem exists_monic_irreducible_factorization (f : R[X]) (hf : f.Monic)
    (h0 : 0 < f.natDegree) :
    ∃ t : Multiset R[X], (∀ g ∈ t, g.Monic ∧ Irreducible g) ∧ t.prod = f := by
  generalize hn : f.natDegree = n at h0
  induction n using Nat.strong_induction_on generalizing f with
  | _ n ih =>
  by_cases hirr : Irreducible f
  · exact ⟨{f}, fun g hg => by rw [Multiset.mem_singleton.mp hg]; exact ⟨hf, hirr⟩,
      Multiset.prod_singleton f⟩
  · have hfu : ¬IsUnit f := by
      intro hu
      have := Polynomial.natDegree_eq_zero_of_isUnit hu
      omega
    rw [irreducible_iff] at hirr
    push_neg at hirr
    obtain ⟨a, b, hab, ha, hb⟩ := hirr hfu
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hab
      exact hf.ne_zero hab
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hab
      exact hf.ne_zero hab
    have hlc : a.leadingCoeff * b.leadingCoeff = 1 := by
      rw [← Polynomial.leadingCoeff_mul, ← hab, hf.leadingCoeff]
    have hua : IsUnit a.leadingCoeff := isUnit_of_dvd_one ⟨_, hlc.symm⟩
    have hub : IsUnit b.leadingCoeff :=
      isUnit_of_dvd_one ⟨_, by rw [mul_comm] at hlc; exact hlc.symm⟩
    have hdega : 0 < a.natDegree := by
      rcases Nat.eq_zero_or_pos a.natDegree with h | h
      · exfalso
        apply ha
        have : a = Polynomial.C a.leadingCoeff := by
          rw [Polynomial.leadingCoeff, h]
          exact Polynomial.eq_C_of_natDegree_eq_zero h
        rw [this]
        exact Polynomial.isUnit_C.mpr hua
      · exact h
    have hdegb : 0 < b.natDegree := by
      rcases Nat.eq_zero_or_pos b.natDegree with h | h
      · exfalso
        apply hb
        have : b = Polynomial.C b.leadingCoeff := by
          rw [Polynomial.leadingCoeff, h]
          exact Polynomial.eq_C_of_natDegree_eq_zero h
        rw [this]
        exact Polynomial.isUnit_C.mpr hub
      · exact h
    have hdeg : n = a.natDegree + b.natDegree := by
      rw [← hn, hab, Polynomial.natDegree_mul ha0 hb0]
    -- normalize the two cofactors to monic
    have huv : hua.unit * hub.unit = 1 :=
      Units.ext (by rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, hlc, Units.val_one])
    have hinv : (↑hua.unit⁻¹ : R) * ↑hub.unit⁻¹ = 1 := by
      rw [← Units.val_mul, show hua.unit⁻¹ * hub.unit⁻¹ = (hua.unit * hub.unit)⁻¹ from by
        rw [mul_inv_rev, mul_comm], huv, inv_one, Units.val_one]
    have hCa : (Polynomial.C (↑hua.unit⁻¹ : R)) ≠ 0 :=
      Polynomial.C_ne_zero.mpr (Units.ne_zero _)
    have hCb : (Polynomial.C (↑hub.unit⁻¹ : R)) ≠ 0 :=
      Polynomial.C_ne_zero.mpr (Units.ne_zero _)
    have ham : (Polynomial.C (↑hua.unit⁻¹ : R) * a).Monic := by
      unfold Polynomial.Monic
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      exact hua.val_inv_mul
    have hbm : (Polynomial.C (↑hub.unit⁻¹ : R) * b).Monic := by
      unfold Polynomial.Monic
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      exact hub.val_inv_mul
    have hdega' : (Polynomial.C (↑hua.unit⁻¹ : R) * a).natDegree = a.natDegree := by
      rw [Polynomial.natDegree_mul hCa ha0, Polynomial.natDegree_C, zero_add]
    have hdegb' : (Polynomial.C (↑hub.unit⁻¹ : R) * b).natDegree = b.natDegree := by
      rw [Polynomial.natDegree_mul hCb hb0, Polynomial.natDegree_C, zero_add]
    obtain ⟨ta, hta, hpa⟩ := ih a.natDegree (by omega) _ ham hdega' hdega
    obtain ⟨tb, htb, hpb⟩ := ih b.natDegree (by omega) _ hbm hdegb' hdegb
    refine ⟨ta + tb, fun g hg => ?_, ?_⟩
    · rcases Multiset.mem_add.mp hg with h | h
      · exact hta g h
      · exact htb g h
    · rw [Multiset.prod_add, hpa, hpb]
      calc Polynomial.C (↑hua.unit⁻¹ : R) * a * (Polynomial.C (↑hub.unit⁻¹ : R) * b)
          = Polynomial.C (↑hua.unit⁻¹ : R) * Polynomial.C (↑hub.unit⁻¹ : R) * (a * b) := by
            ring
        _ = Polynomial.C ((↑hua.unit⁻¹ : R) * ↑hub.unit⁻¹) * (a * b) := by
            rw [Polynomial.C_mul]
        _ = f := by rw [hinv, map_one, one_mul, ← hab]

/-- Fin-indexed form of `exists_monic_irreducible_factorization`. -/
theorem exists_monic_irreducible_factorization_fin (f : R[X]) (hf : f.Monic)
    (h0 : 0 < f.natDegree) :
    ∃ (m : ℕ) (Hf : Fin m → R[X]),
      (∀ i, (Hf i).Monic ∧ Irreducible (Hf i)) ∧ ∏ i, Hf i = f := by
  obtain ⟨t, hmem, hprod⟩ := exists_monic_irreducible_factorization f hf h0
  refine ⟨t.toList.length, fun i => t.toList[i.1],
    fun i => hmem _ (by rw [← Multiset.mem_toList]; exact List.getElem_mem _), ?_⟩
  rw [Fin.prod_univ_getElem, Multiset.prod_toList, hprod]

end Polynomial

/-! ## Axiom audit. -/
#print axioms Polynomial.exists_monic_irreducible_factorization
#print axioms Polynomial.exists_monic_irreducible_factorization_fin

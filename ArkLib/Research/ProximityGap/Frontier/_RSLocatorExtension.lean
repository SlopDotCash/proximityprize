/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Extensions.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ReedSolomon
import CompPoly.ToMathlib.Polynomial.Roots
import Mathlib.LinearAlgebra.Lagrange

/-!
# Extending a Reed–Solomon MCA witness by zero coordinates

Multiplying both received rows and their decoded polynomial by the locator of the new
coordinates preserves every old bad scalar. A joint explanation on the enlarged witness
must vanish at each new point, so division by the locator recovers a joint explanation
on the original witness.
-/

open Finset Polynomial ProximityGap
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.RSLocatorExtension

variable {F : Type} [Field F] {n N k : ℕ}

/-- New coordinates, indexed in the enlarged evaluation domain. -/
def fresh (old : Fin n ↪ Fin N) : Finset (Fin N) :=
  (Finset.univ.map old)ᶜ

private theorem fresh_card (old : Fin n ↪ Fin N) : (fresh old).card = N - n := by
  simp [fresh, Finset.card_compl]

private theorem old_not_fresh (old : Fin n ↪ Fin N) (i : Fin n) : old i ∉ fresh old := by
  intro hi
  exact (Finset.mem_compl.mp hi) (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/-- The monic polynomial whose simple roots are the new evaluation points. -/
noncomputable def locator (old : Fin n ↪ Fin N) (dom : Fin N ↪ F) : F[X] :=
  Lagrange.nodal (fresh old) dom

private theorem locator_natDegree (old : Fin n ↪ Fin N) (dom : Fin N ↪ F) :
    (locator old dom).natDegree = N - n := by
  rw [locator, Lagrange.natDegree_nodal, fresh_card]

private theorem locator_old_ne_zero (old : Fin n ↪ Fin N) (dom : Fin N ↪ F) (i : Fin n) :
    (locator old dom).eval (dom (old i)) ≠ 0 := by
  apply Lagrange.eval_nodal_not_at_node
  intro j hj heq
  apply old_not_fresh old i
  rwa [dom.injective heq]

private theorem locator_fresh_zero (old : Fin n ↪ Fin N) (dom : Fin N ↪ F)
    {j : Fin N} (hj : j ∈ fresh old) : (locator old dom).eval (dom j) = 0 :=
  Lagrange.eval_nodal_at_node (v := fun i => dom i) hj

variable [NeZero n]

/-- Evaluate the locator times the old word on the old domain and zero on all new points. -/
noncomputable def extendWord (old : Fin n ↪ Fin N) (dom : Fin N ↪ F) (u : Fin n → F)
    (j : Fin N) : F :=
  (locator old dom).eval (dom j) * u (Function.invFun old j)

private theorem extend_old (old : Fin n ↪ Fin N) (dom : Fin N ↪ F)
    (u : Fin n → F) (i : Fin n) :
    extendWord old dom u (old i) = (locator old dom).eval (dom (old i)) * u i := by
  rw [extendWord, Function.leftInverse_invFun old.injective i]

private theorem extend_fresh (old : Fin n ↪ Fin N) (dom : Fin N ↪ F)
    (u : Fin n → F) {j : Fin N} (hj : j ∈ fresh old) : extendWord old dom u j = 0 := by
  rw [extendWord, locator_fresh_zero old dom hj, zero_mul]

private theorem shorten_explanation (old : Fin n ↪ Fin N) (dom : Fin N ↪ F)
    (hk : 0 < k) (u : Fin n → F) (S : Finset (Fin n)) (v : Fin N → F)
    (hv : v ∈ ReedSolomon.code dom (k + (N - n)))
    (hmatch : ∀ j ∈ S.map old ∪ fresh old, v j = extendWord old dom u j) :
    ∃ w ∈ ReedSolomon.code (old.trans dom) k, ∀ i ∈ S, w i = u i := by
  classical
  let : NeZero (k + (N - n)) := ⟨by omega⟩
  obtain ⟨p, hp, heval⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hv
  have hzero (j : Fin N) (hj : j ∈ fresh old) : p.eval (dom j) = 0 := by
    rw [heval, hmatch j (Finset.mem_union_right _ hj), extend_fresh old dom u hj]
  have hdvd : locator old dom ∣ p := by
    simpa only [locator, Lagrange.nodal] using
      Polynomial.prod_X_sub_C_dvd (fresh old) dom dom.injective.injOn p hzero
  obtain ⟨q, hq⟩ := hdvd
  have hqdeg : q.natDegree < k := by
    by_cases hz : q = 0
    · simpa [hz] using hk
    · have hloc : locator old dom ≠ 0 := Lagrange.nodal_ne_zero
      rw [hq, Polynomial.natDegree_mul hloc hz, locator_natDegree] at hp
      omega
  refine ⟨fun i => q.eval (dom (old i)),
    ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval q hqdeg (fun _ => rfl), ?_⟩
  intro i hi
  have h := (heval (old i)).trans
    (hmatch (old i) (Finset.mem_union_left _ (Finset.mem_map.mpr ⟨i, hi, rfl⟩)))
  rw [hq, Polynomial.eval_mul, extend_old] at h
  exact mul_left_cancel₀ (locator_old_ne_zero old dom i) h

/-- Every bad scalar remains bad after locator extension, provided the new cardinality
threshold admits the old witness together with every new coordinate. -/
theorem mcaEvent_extend (old : Fin n ↪ Fin N) (dom : Fin N ↪ F) (hk : 0 < k)
    {δ δ' : ℝ≥0} (hsize : ∀ a : ℕ,
      (1 - δ) * n ≤ (a : ℝ≥0) → (1 - δ') * N ≤ ((a + (N - n) : ℕ) : ℝ≥0))
    (u₀ u₁ : Fin n → F) (γ : F)
    (hbad : mcaEvent (ReedSolomon.code (old.trans dom) k : Set (Fin n → F)) δ u₀ u₁ γ) :
    mcaEvent (ReedSolomon.code dom (k + (N - n)) : Set (Fin N → F)) δ'
      (extendWord old dom u₀) (extendWord old dom u₁) γ := by
  classical
  let : NeZero k := ⟨by omega⟩
  obtain ⟨S, hS, ⟨w, hw, hwS⟩, hno⟩ := hbad
  obtain ⟨p, hp, heval⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hw
  have hdis : Disjoint (S.map old) (fresh old) := by
    apply Finset.disjoint_left.mpr
    intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hj
    exact old_not_fresh old i
  have hcard : (S.map old ∪ fresh old).card = S.card + (N - n) := by
    rw [Finset.card_union_of_disjoint hdis, Finset.card_map, fresh_card]
  refine ⟨S.map old ∪ fresh old, ?_, ?_, ?_⟩
  · rw [hcard, Fintype.card_fin]
    apply hsize
    simpa only [Fintype.card_fin] using hS
  · let q := locator old dom * p
    have hdeg : q.natDegree < k + (N - n) := by
      have hle := Polynomial.natDegree_mul_le (p := locator old dom) (q := p)
      rw [locator_natDegree] at hle
      dsimp only [q]
      omega
    refine ⟨fun j => q.eval (dom j),
      ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval q hdeg (fun _ => rfl), ?_⟩
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
      change (locator old dom * p).eval (dom (old i)) = _
      rw [Polynomial.eval_mul, extend_old, extend_old]
      have hv : p.eval (dom (old i)) = u₀ i + γ * u₁ i := (heval i).trans (hwS i hi)
      rw [hv, smul_eq_mul]
      ring
    · change (locator old dom * p).eval (dom j) = _
      rw [Polynomial.eval_mul, locator_fresh_zero old dom hj, zero_mul,
        extend_fresh old dom u₀ hj, extend_fresh old dom u₁ hj, smul_zero, add_zero]
  · rintro ⟨v₀, hv₀, v₁, hv₁, hv⟩
    obtain ⟨w₀, hw₀, h₀⟩ := shorten_explanation old dom hk u₀ S v₀ hv₀
      (fun j hj => (hv j hj).1)
    obtain ⟨w₁, hw₁, h₁⟩ := shorten_explanation old dom hk u₁ S v₁ hv₁
      (fun j hj => (hv j hj).2)
    exact hno ⟨w₀, hw₀, w₁, hw₁, fun i hi => ⟨h₀ i hi, h₁ i hi⟩⟩

open Classical in
/-- The inclusion of bad scalars for a fixed pair of received words as a count. -/
theorem badScalar_card_le_extension [Fintype F] (old : Fin n ↪ Fin N) (dom : Fin N ↪ F)
    (hk : 0 < k) {δ δ' : ℝ≥0} (hsize : ∀ a : ℕ,
      (1 - δ) * n ≤ (a : ℝ≥0) → (1 - δ') * N ≤ ((a + (N - n) : ℕ) : ℝ≥0))
    (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter fun γ : F =>
      mcaEvent (ReedSolomon.code (old.trans dom) k : Set (Fin n → F)) δ u₀ u₁ γ).card ≤
    (Finset.univ.filter fun γ : F =>
      mcaEvent (ReedSolomon.code dom (k + (N - n)) : Set (Fin N → F)) δ'
        (extendWord old dom u₀) (extendWord old dom u₁) γ).card := by
  apply Finset.card_le_card
  intro γ hγ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    mcaEvent_extend old dom hk hsize u₀ u₁ γ (Finset.mem_filter.mp hγ).2⟩

end ArkLib.ProximityGap.Frontier.RSLocatorExtension

#print axioms ArkLib.ProximityGap.Frontier.RSLocatorExtension.mcaEvent_extend

#print axioms ArkLib.ProximityGap.Frontier.RSLocatorExtension.badScalar_card_le_extension

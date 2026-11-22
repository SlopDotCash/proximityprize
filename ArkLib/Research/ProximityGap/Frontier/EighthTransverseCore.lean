/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.EighthTransverseRows
import ArkLib.Research.ProximityGap.Frontier.EighthMobiusSites

/-! # Defining agreements and the linear label in the transverse eighth-rate attack -/

namespace ArkLib.ProximityGap.Frontier.EighthTransverseCore
open EighthMobiusSites EighthMobiusSites.Tag EighthTransverseRows EighthTransverseMobius
open SecondPrimeSmoothSeed PrizeShapePrimeP30Second
open Finset
set_option autoImplicit false
set_option maxRecDepth 10000
local instance : Fact P.Prime := ⟨prime_P⟩

/-- The two received symbols at a physical site come from its designated owner. -/
noncomputable def recvA (i : Site) : F := (rowA locator (owner i)).eval (dom i)
noncomputable def recvB (i : Site) : F := (rowB locator (owner i)).eval (dom i)

/-- The table of seed collisions uses the same physical tags as the site allocation. -/
theorem fiber_values (i : Site) :
    (pv (fiber i) = 0 ↔ tag i = p01) ∧ (qv (fiber i) = 0 ↔ tag i = p02) ∧
      (pv (fiber i) = qv (fiber i) ↔ tag i = p12) := by
  have table : ∀ j : Fin 32,
      (pv j = 0 ↔ j ∈ ({0, 2, 16} : Finset _)) ∧
      (qv j = 0 ↔ j ∈ ({4, 18, 20} : Finset _)) ∧
      (pv j = qv j ↔ j ∈ ({6, 10, 14} : Finset _)) := by decide
  obtain ⟨a, b, c⟩ := table (fiber i)
  obtain ⟨d, e, f⟩ := pair_tags i
  exact ⟨a.trans d.symm, b.trans e.symm, c.trans f.symm⟩

private theorem marked_values (i : Site) (ht : tag i = markU ∨ tag i = markV) :
    aVal (dom i) (pv (fiber i)) (qv (fiber i)) 3 = aVal (dom i) (pv (fiber i)) (qv (fiber i)) 2 ∧
    bVal (dom i) (pv (fiber i)) (qv (fiber i)) 3 =
      bVal (dom i) (pv (fiber i)) (qv (fiber i)) 2 := by
  rcases ht with h | h
  · have hi : i = 1 := Fin.ext (markU_iff.mp h)
    subst i
    have hf : fiber (1 : Site) = 1 := Fin.ext ((fiber_mod _).trans (by decide))
    have hx : dom (1 : Site) = u := by
      change PrizeShapePrimeP30Second.g ^ (1 : ℕ) = PrizeShapePrimeP30Second.g
      simp
    rw [hf, hx]
    exact marked_agreement (Or.inl rfl) marked.1
  · have hi : i = 3 := Fin.ext (markV_iff.mp h)
    subst i
    have hf : fiber (3 : Site) = 3 := Fin.ext ((fiber_mod _).trans (by decide))
    have hx : dom (3 : Site) = v := rfl
    rw [hf, hx]
    exact marked_agreement (Or.inr rfl) marked.2.1

private theorem same_values {z : Tag} {x p q : F} {h : Fin 4} (hh : owns z h)
    (h01 : z = p01 → p = 0) (h02 : z = p02 → q = 0) (h12 : z = p12 → p = q)
    (hm : z = markU ∨ z = markV →
      aVal x p q 3 = aVal x p q 2 ∧ bVal x p q 3 = bVal x p q 2) :
    z = root ∨ aVal x p q h = aVal x p q (ownerTag z) ∧ bVal x p q h = bVal x p q (ownerTag z) := by
  cases z with
  | root => exact Or.inl rfl
  | p01 => obtain rfl := h01 rfl; right; fin_cases h <;> simp_all [owns, ownerTag, aVal, bVal]
  | p02 => obtain rfl := h02 rfl; right; fin_cases h <;> simp_all [owns, ownerTag, aVal, bVal]
  | p12 => obtain rfl := h12 rfl; right; fin_cases h <;> simp_all [owns, ownerTag, aVal, bVal]
  | markU | markV =>
    obtain ⟨ha, hb⟩ := hm (by simp)
    right; fin_cases h <;> simp_all [owns, ownerTag]
  | solo0 | solo1 | solo2 | solo3 => right; fin_cases h <;> simp_all [owns, ownerTag]

/-- Every prescribed head matches both received row values on its full defining core. -/
theorem core_agrees {i : Site} {h : Fin 4} (hi : i ∈ core h) :
    (rowA locator h).eval (dom i) = recvA i ∧ (rowB locator h).eval (dom i) = recvB i := by
  obtain ⟨p, q, eq⟩ := fiber_values i
  have v := same_values (mem_core.mp hi) p.mpr q.mpr eq.mpr (marked_values i)
  obtain ⟨a, b⟩ := evals locator h i (fiber i) (fiber_mod i)
  obtain ⟨ao, bo⟩ := evals locator (owner i) i (fiber i) (fiber_mod i)
  rw [recvA, recvB, a, b, ao, bo]
  rcases v with r | ⟨va, vb⟩
  · simp [locator_eval.mpr (mem_roots.mpr r)]
  · exact ⟨congrArg (fun y : F => locator.eval (dom i) * y) va,
      congrArg (fun y : F => locator.eval (dom i) * y) vb⟩

/-- At a line-map source the foreign triple head has a different second row.
Both unscaled folds at the label `-x` are zero. -/
theorem minus_local {i : Site} (hi : i ∈ loci 0) :
    let x := dom i
    let p := pv (fiber i)
    let q := qv (fiber i)
    let h := foreign 0 i
    bVal x p q h ≠ bVal x p q (owner i) ∧
      aVal x p q h + (-x) * bVal x p q h = aVal x p q (owner i) + (-x) * bVal x p q (owner i) := by
  dsimp only
  have select := mem_loci.mp hi
  have values := fiber_values i
  have idx : ∀ (z : Tag) (j : Fin 32), scheduled 0 j z →
      (foreignTag 0 z).val < 3 ∧ (ownerTag z).val < 3 := by decide
  obtain ⟨hf, ho⟩ := idx (tag i) (fiber i) select
  constructor
  · change bVal _ _ _ (foreignTag 0 (tag i)) ≠ bVal _ _ _ (ownerTag (tag i))
    cases hz : tag i <;> simp_all [bVal, foreignTag, ownerTag, scheduled] <;> grind
  · exact (line _ _ _ _ hf).trans (line _ _ _ _ ho).symm

/-- The linear scheduled label gives an actual new folded agreement outside its head's core. -/
theorem minus_incidence {i : Site} (hi : i ∈ loci 0) :
    (rowB locator (foreign 0 i)).eval (dom i) ≠ recvB i ∧
    (rowA locator (foreign 0 i)).eval (dom i) +
        (-dom i) * (rowB locator (foreign 0 i)).eval (dom i) =
      recvA i + (-dom i) * recvB i := by
  obtain ⟨neq, eq⟩ := minus_local hi
  have hJ : locator.eval (dom i) ≠ 0 := fun hz => locus_nonroot hi (locator_eval.mp hz)
  obtain ⟨a, b⟩ := evals locator (foreign 0 i) i (fiber i) (fiber_mod i)
  obtain ⟨ao, bo⟩ := evals locator (owner i) i (fiber i) (fiber_mod i)
  rw [recvA, recvB, a, b, ao, bo]
  refine ⟨fun he => neq (mul_left_cancel₀ hJ he), ?_⟩
  linear_combination locator.eval (dom i) * eq

#print axioms core_agrees
#print axioms minus_incidence
end ArkLib.ProximityGap.Frontier.EighthTransverseCore

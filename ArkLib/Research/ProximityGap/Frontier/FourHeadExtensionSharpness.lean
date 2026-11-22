/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorCoreFreshDecode
import Mathlib.Data.Fin.VecNotation

/-! # Product heads and simultaneous attainment of the personal scalar capacities -/
set_option autoImplicit false
noncomputable section
open Finset Polynomial Code
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.FourHeadExtensionSharpness

variable {R : Type*} [CommRing R]

/-- Products of the three edges incident to each vertex. The edge order is
01, 02, 03, 23, 13, 12. -/
def first (p : Fin 6 → R) : Fin 4 → R :=
  ![p 0*p 1*p 2, p 0*p 4*p 5, p 1*p 3*p 5, p 2*p 3*p 4]

/-- Products of the three complementary edges. -/
def second (p : Fin 6 → R) : Fin 4 → R :=
  ![p 3*p 4*p 5, p 1*p 2*p 3, p 0*p 2*p 4, p 0*p 1*p 5]

def start : Fin 6 → Fin 4 := ![0,0,0,2,1,1]
def finish : Fin 6 → Fin 4 := ![1,2,3,3,3,2]
def opposite : Fin 6 → Fin 6 := ![3,4,5,0,1,2]

/-- The residual factor cuts out the physical double nodes for this edge. -/
def residual (p : Fin 6 → R) : Fin 6 → R :=
  ![p 1*p 2-p 4*p 5, p 0*p 2-p 3*p 5, p 0*p 1-p 3*p 4,
    p 1*p 5-p 2*p 4, p 0*p 5-p 2*p 3, p 0*p 4-p 1*p 3]

/-- Every side difference has one common factor, leaving the two opposite
edge entries as its direction coordinates. This includes characteristic two. -/
theorem sides (p : Fin 6 → R) (i : Fin 6) :
    first p (start i) - first p (finish i) = p i * residual p i ∧
    second p (start i) - second p (finish i) = -(p (opposite i)) * residual p i := by
  fin_cases i <;> dsimp [first, second, start, finish, opposite, residual] <;>
    constructor <;> ring

variable {F I : Type} [Field F] [DecidableEq F] [Fintype F]
variable [Fintype I] [DecidableEq I] [Nonempty I]

/-- A slot consists of a head and one site away from its joint core. -/
abbrev Slot {r : ℕ} (core : Fin r → Finset I) :=
  (i : Fin r) × ↥(univ \ core i)

/-- If all off-core slots have different finite folded labels, their full
number is attained by a single pair of received words. -/
theorem full_capacity {r k c : ℕ} (dom : I ↪ F) (δ : ℝ≥0)
    (u : WordStack F (Fin 2) I) (core : Fin r → Finset I)
    (A B : Fin r → F[X]) (degA : ∀ i, (A i).degree < k) (degB : ∀ i, (B i).degree < k)
    (size : ∀ i, (core i).card = c) (enough : k ≤ c)
    (threshold : (1 - δ) * (Fintype.card I : ℝ≥0) ≤ (c+1 : ℕ))
    (agree : ∀ i x, x ∈ core i → (A i).eval (dom x) = u 0 x ∧ (B i).eval (dom x) = u 1 x)
    (label : Slot core → F) (inj : Function.Injective label)
    (fresh : ∀ j : Slot core,
      (A j.1 + C (label j) * B j.1).eval (dom j.2.val) = u 0 j.2.val + label j * u 1 j.2.val)
    (mismatch : ∀ j : Slot core,
      ((A j.1).eval (dom j.2.val), (B j.1).eval (dom j.2.val)) ≠ (u 0 j.2.val, u 1 j.2.val)) :
    ∃ G : Finset F, G.card = r * (Fintype.card I - c) ∧
      ∀ γ ∈ G, _root_.ProximityGap.mcaEvent
        (ReedSolomon.code dom k : Set (I → F)) δ (u 0) (u 1) γ := by
  classical
  refine ⟨univ.image label, ?_, ?_⟩
  · rw [card_image_of_injective _ inj, card_univ]
    simp [Slot, Fintype.card_sigma, size]
  intro γ hγ
  obtain ⟨j, _, rfl⟩ := mem_image.mp hγ
  apply HalfPredecessorCoreFreshDecode.mcaEvent_of_affine_core_fresh
    dom k δ u (label j) (core j.1) j.2.val (A j.1) (B j.1)
    (mem_sdiff.mp j.2.property).2 (degA _) (degB _)
  · by_cases z : label j = 0
    · simpa [z] using degA j.1
    · exact (degree_add_le _ _).trans_lt (max_lt (degA _) ((degree_C_mul z).trans_lt (degB _)))
  · rw [size]; exact enough
  · simpa only [size] using threshold
  · exact agree j.1
  · exact fresh j
  · exact mismatch j

/-- The large-characteristic point-count estimate is positive for the named
fields at dimensions four through eight, given the uniform degree ceilings. -/
theorem named_size_check {q r Δ J : ℕ}
    (lower : 2^158 < q) (dim : r ≤ 2^30) (degree : Δ ≤ 2^37) (boundary : J ≤ 2^68) :
    2 * (r+1) * Δ^2 < q ∧ Δ^2 * 2^80 + 4*Δ^4 + Δ*J < q := by
  constructor
  · calc
      _ ≤ 2 * (2^30+1) * (2^37)^2 := by gcongr
      _ < q := lt_trans (by decide) lower
  · calc
      _ ≤ (2^37)^2 * 2^80 + 4*(2^37)^4 + 2^37*2^68 := by gcongr
      _ < q := lt_trans (by decide) lower

#print axioms named_size_check
#print axioms sides
#print axioms full_capacity
end ArkLib.ProximityGap.Frontier.FourHeadExtensionSharpness

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothFourHeadColored

/-! # Refining three pair-coincidence fibers into an MCA attack -/

open Finset Polynomial ProximityGap
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.SmoothFourHeadFibers
open SmoothFourHeadColored

/-- Partition a finite set into labeled parts of prescribed sizes. -/
theorem partition_fibers {I J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (s : Finset I) (w : J → ℕ) (h : s.card = ∑ j, w j) :
    ∃ f : I → J, ∀ j, (s.filter (fun x => f x = j)).card = w j := by
  classical
  let e : ↥s ≃ (j : J) × Fin (w j) := Fintype.equivOfCardEq (by simpa using h)
  let f (x : I) := if hx : x ∈ s then (e ⟨x,hx⟩).1 else Classical.choice ‹Nonempty J›
  refine ⟨f, fun j => ?_⟩
  let incl : Fin (w j) ↪ I :=
    ⟨fun y => (e.symm ⟨j,y⟩).1, fun y z he => by
      have he' := e.symm.injective (Subtype.ext he : e.symm ⟨j,y⟩ = e.symm ⟨j,z⟩)
      simpa using he'⟩
  have hf : s.filter (fun x => f x = j) = univ.map incl := by
    ext x
    constructor
    · intro hx
      obtain ⟨hs, hj⟩ := mem_filter.mp hx
      have h1 : (e ⟨x,hs⟩).1 = j := by simpa [f, hs] using hj
      let y : Fin (w j) := h1 ▸ (e ⟨x,hs⟩).2
      have heq : (⟨j,y⟩ : (j : J) × Fin (w j)) = e ⟨x,hs⟩ := by
        apply Sigma.ext h1.symm
        simp [y]
      refine mem_map.mpr ⟨y, mem_univ _, ?_⟩
      change (e.symm ⟨j,y⟩).val = x
      rw [heq, e.symm_apply_apply]
    · intro hx
      obtain ⟨y, _, rfl⟩ := mem_map.mp hx
      have hs := (e.symm ⟨j,y⟩).2
      refine mem_filter.mpr ⟨hs, ?_⟩
      change f (e.symm ⟨j,y⟩).val = j
      simp [f, hs]
  simp [hf]

/-- Initial pair fiber numbered by the single head excluded. Fiber three has three distinct heads. -/
def coarse : Fin 8 → Fin 4 := ![0,1,2,3,3,3,3,3]

private def merge (r : Fin 4) (j : Fin 5) : Fin 8 :=
  if r = 3 then ![3,4,5,6,7] j else ![0,1,2,3] r

/-- Partition the all-distinct sites into common, private and unused sets of prescribed sizes. -/
theorem refine_fibers {I : Type} [Fintype I] (raw : I → Fin 4)
    (D G P T : ℕ) (hc : ∀ j, (univ.filter (fun x => raw x = j)).card =
      (![D,D,D,G+3*P+T] : Fin 4 → ℕ) j) :
    ∃ f : I → Fin 8, (∀ x, coarse (f x) = raw x) ∧
      ∀ j, (univ.filter (fun x => f x = j)).card = weight D G P T j := by
  classical
  let s := univ.filter fun x => raw x = 3
  let w : Fin 5 → ℕ := ![G,P,P,P,T]
  obtain ⟨a, ha⟩ := partition_fibers s w (by
    change (univ.filter _).card = _
    rw [hc]
    simp [w, Fin.sum_univ_succ]
    omega)
  let f (x : I) := merge (raw x) (a x)
  refine ⟨f, fun x => (by decide : ∀ r j, coarse (merge r j) = r) _ _, fun j => ?_⟩
  have low (j : Fin 8) (r : Fin 4) (he : ∀ u v, merge u v = j ↔ u = r) :
      (univ.filter (fun x => f x = j)).card = (![D,D,D,G+3*P+T] : Fin 4 → ℕ) r := by
    simpa only [f, he] using hc r
  have high (j : Fin 8) (v : Fin 5) (he : ∀ r u, merge r u = j ↔ r = 3 ∧ u = v) :
      (univ.filter (fun x => f x = j)).card = w v := by
    convert ha v using 2
    ext x
    simp [s, f, he]
  fin_cases j
  · exact low _ 0 (by decide)
  · exact low _ 1 (by decide)
  · exact low _ 2 (by decide)
  · exact high _ 0 (by decide)
  · exact high _ 1 (by decide)
  · exact high _ 2 (by decide)
  · exact high _ 3 (by decide)
  · exact high _ 4 (by decide)

/-- Pair classes of the cubic pencil, indexed by the head absent from each pair. -/
def bucket (stride i : ℕ) : Fin 4 :=
  if i = 3*stride ∨ i = 5*stride ∨ i = 7*stride then 0
  else if i = 2*stride ∨ i = 9*stride ∨ i = 10*stride then 1
  else if i = 0 ∨ i = stride ∨ i = 8*stride then 2
  else 3

/-- A residue class in an index of size s times q has s lifts. -/
theorem count_blocks {J : Type} [DecidableEq J] {s q : ℕ} [NeZero q] (f : Fin q → J) (j : J) :
    (univ.filter (fun x : Fin (s*q) => f x.modNat = j)).card =
      s*(univ.filter (fun r : Fin q => f r = j)).card := by
  classical
  let e : Fin s × Fin q ≃ Fin (s*q) := finProdFinEquiv
  have he : (univ.filter (fun x : Fin (s*q) => f x.modNat = j)) =
      ((univ : Finset (Fin s)) ×ˢ (univ.filter (fun r : Fin q => f r = j))).map e.toEmbedding := by
    ext x
    rw [mem_map_equiv]
    simp [e, finProdFinEquiv]
  simp [he]

/-- The equality pattern of a pair-coincidence fiber at a single site. -/
def coincide (r : Fin 4) (i j : Fin 3) : Prop :=
  i = j ∨ (r ≠ 3 ∧ i.val ≠ r.val ∧ j.val ≠ r.val)

instance (r : Fin 4) (i j : Fin 3) : Decidable (coincide r i j) :=
  inferInstanceAs (Decidable (_ ∨ _))

variable {F I : Type} [Field F] [Fintype F] [Fintype I] [Nonempty I] [DecidableEq I]

/-- The original MCA attack from three seed polynomials with three prescribed pair-coincidence
classes and a complementary class of pairwise distinct evaluations. -/
theorem mass (dom : I ↪ F) (δ : ℝ≥0) (k D G P T S H : ℕ) (raw : I → Fin 4) (seed : Fin 3 → F[X])
    (hc : ∀ j, (univ.filter (fun x => raw x = j)).card = (![D,D,D,G+3*P+T] : Fin 4 → ℕ) j)
    (hseed : ∀ j, (seed j).natDegree ≤ D)
    (heq : ∀ x i j, (seed i).eval (dom x) = (seed j).eval (dom x) ↔ coincide (raw x) i j)
    (hdeg : G + D + 1 < k) (hkS : S + 2 ≤ k) (hS : S ≤ G + 3*D + 3*P)
    (hH : H ≤ T) (hkC : k ≤ G + 2*D + P) (hC₄ : G + 2*D + P ≤ S + (T-H))
    (hsize : (1 - δ) * (Fintype.card I : ℝ≥0) ≤ ((G + 2*D + P + 1 : ℕ) : ℝ≥0))
    (hq : 3 * Fintype.card I < Fintype.card F) (h16 : 16 < Fintype.card F)
    (hfield : (3*D+3*P + (G+3*D+3*P-S) + 3*(T-H) + 4*H).choose 2 ≤ Nat.card F) :
    ((3*D+3*P + (G+3*D+3*P-S) + 3*(T-H) + 4*H : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (I → F)) δ := by
  obtain ⟨f, hf, hc'⟩ := refine_fibers raw D G P T hc
  apply SmoothFourHeadColored.mass dom δ k D G P T S H f seed hc' hseed ?_ ?_ ?_
    hdeg hkS hS hH hkC hC₄ hsize hq h16 hfield
  · intro x j hj hn
    rw [heq, ← hf]
    exact (by decide : ∀ c j, c ∈ coreClasses j → c ≠ 3 → coincide (coarse c) j (owner c))
      _ j hj hn
  · intro x hx h
    have he := (heq x _ _).mp h
    rw [← hf] at he
    exact (by decide : ∀ c, c ∈ ordinaryClasses → ¬coincide (coarse c) (miss c) (owner c)) _ hx he
  · intro x hx i j h
    have he := (heq x i j).mp h
    rw [← hf, hx] at he
    exact (by decide : ∀ i j, coincide (coarse 7) i j → i = j) _ _ he

end ArkLib.ProximityGap.Frontier.SmoothFourHeadFibers

#print axioms ArkLib.ProximityGap.Frontier.SmoothFourHeadFibers.mass

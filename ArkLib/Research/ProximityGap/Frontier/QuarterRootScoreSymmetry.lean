/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.MobiusSubgroupBound

/-! # Projective symmetries of three large partial fibers -/
namespace ArkLib.ProximityGap.Frontier.QuarterRootScoreSymmetry
open Finset

/-- A permutation of the three full geometric fibers forces many pairs of
marked subgroup sites in its graph. Only the marked points need a finite
coordinate, so the unmarked set may include the projective point at infinity. -/
theorem symmetry_score {T F : Type*} [DecidableEq T] [Field F]
    {p : ℕ} [CharP F p] (prime : p.Prime) (large : 2^40 < p)
    (m : ℕ) (U W : Finset T) (size : U.card ≤ 3*m) (marked : W ⊆ U) (e : T ≃ T)
    (x : T → F) (inj : Set.InjOn x ↑W) (root : ∀ t ∈ W, (x t)^(2^30 : ℕ)=1)
    {a b c d : F} (det : a*d-b*c≠0) (diagonal : b≠0 ∨ c≠0)
    (reciprocal : a≠0 ∨ d≠0)
    (graph : ∀ t ∈ W, e t ∈ W → a*x t+b=x (e t)*(c*x t+d)) :
    2*W.card ≤ 3*m+3960117+((U.map e.symm.toEmbedding) \ U).card := by
  classical
  let V := W.map e.symm.toEmbedding
  let A := W ∩ V
  have hv (t : T) : t ∈ V ↔ e t ∈ W := by simp [V]
  have fw (t : A) := (mem_inter.mp t.property).1
  have bw (t : A) := (hv _).mp (mem_inter.mp t.property).2
  have bound := _root_.ProximityGap.MobiusSubgroupBound.production_graph prime large
    (fun t : A => x t.val) (fun t : A => x (e t.val))
    (fun u v h => Subtype.ext (inj (fw u) (fw v) h))
    (fun t => root _ (fw t)) (fun t => root _ (bw t))
    det diagonal reciprocal (fun t => graph _ (fw t) (bw t))
  rw [Fintype.card_coe] at bound
  have h := card_union_add_card_inter W V
  let U' := U.map e.symm.toEmbedding
  have cover : (W ∪ V).card ≤ (U' ∪ U).card := card_le_card (by
    intro t ht
    cases mem_union.mp ht with
    | inl h => exact mem_union_right _ (marked h)
    | inr h =>
      obtain ⟨u,hu,eq⟩ := mem_map.mp h
      exact mem_union_left _ (mem_map.mpr ⟨u,marked hu,eq⟩))
  have union_card := card_union_add_card_inter U' U
  have diff_card := card_sdiff_add_card_inter U' U
  change _ ≤ 3*m+3960117+(U' \ U).card
  have mapped : V.card=W.card := card_map _
  change _+A.card=_ at h
  omega

/-- Lagrange's theorem on the normalizer puts a Galois degree below the next
dyadic divisor. This gives the exact maximum score available to Galois quotients. -/
theorem galois_cap {m x : ℕ} (subgroup : m ∣ 2^31) (cap : m≤268435454) (roots : x≤3*m) :
    m≤134217728 ∧ 2*x≤3*m+402653184 := by
  obtain ⟨b,_,rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp subgroup
  have hb : b≤27 := by
    by_contra! h
    have hh := Nat.pow_le_pow_right (by decide : 0<2) h
    change 268435456≤_ at hh
    omega
  have hh := Nat.pow_le_pow_right (by decide : 0<2) hb
  change _≤134217728 at hh
  omega

#print axioms symmetry_score
#print axioms galois_cap
end ArkLib.ProximityGap.Frontier.QuarterRootScoreSymmetry

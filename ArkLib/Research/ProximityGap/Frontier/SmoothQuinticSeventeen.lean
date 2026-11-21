/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.RationalFiberEndpoint
import ArkLib.Research.ProximityGap.Frontier.ApolarEndpointExact
import Mathlib.Tactic.ComputeDegree

/-! # A sharp rate-half example on the prescribed order-sixteen subgroup of the field of order seventeen

Three reduced fibers of one quintic pencil realize fifteen distinct bad scalars
for two explicit received rows. The general apolar upper bound is attained on this domain.
-/

set_option autoImplicit false
open Finset Polynomial ProximityGap Code
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.SmoothQuinticSeventeen

/-- The prime field for the example. -/
abbrev F := ZMod 17
local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

local instance : AddCommGroup F := (inferInstance : Field F).toDivisionRing.toAddCommGroup

local notation "X₁₇" => (Polynomial.X : F[X])

/-- The evaluation domain consists of all nonzero residues. -/
def sites : Finset F := univ.erase 0

/-- The subgroup has sixteen distinct sites. -/
theorem card_sites : sites.card = 16 := by decide

/-- These sites form the complete group of sixteenth roots of unity. -/
theorem sites_eq_roots : sites = nthRootsFinset 16 (1 : F) := by
  ext x
  rw [mem_nthRootsFinset (by decide)]
  exact (by decide : ∀ x : F, x ∈ sites ↔ x^16 = 1) x

/-- The common row denominator. -/
noncomputable def P : F[X] := X₁₇^5 + 4*X₁₇^4 + 14*X₁₇^3 + 11*X₁₇^2 + 5*X₁₇ + 11
/-- The degree-four term in the rational pencil. -/
noncomputable def B : F[X] := 16*X₁₇^4 + 2*X₁₇^3 + 16*X₁₇^2 + 10
/-- The numerator weight shared by the two rows. -/
noncomputable def W : F[X] := 12*X₁₇^4 + 12*X₁₇^3 + 3*X₁₇^2 + 10*X₁₇ + 15

private def first : Finset F := {10, 11, 12, 14, 16}
private def second : Finset F := {3, 5, 9, 13, 15}
private def third : Finset F := {2, 4, 6, 7, 8}

private theorem nodal_of_roots (A : Finset F) (f : F[X]) (hm : f.Monic)
    (hd : f.natDegree ≤ A.card) (hz : ∀ a ∈ A, f.eval a = 0) :
    Lagrange.nodal A id = f := by
  apply (eq_of_monic_of_dvd_of_natDegree_le (Lagrange.nodal_monic ..) hm ?_ ?_).symm
  · apply Finset.prod_dvd_of_coprime
    · intro a _ b _ hab
      exact pairwise_coprime_X_sub_C Function.injective_id hab
    · intro a ha
      exact dvd_iff_isRoot.mpr (hz a ha)
  · rwa [Lagrange.natDegree_nodal]

private theorem nodal_sites : Lagrange.nodal sites id = X₁₇^16-1 := by
  apply nodal_of_roots
  · simpa using monic_X_pow_sub_C (1 : F) (by decide : 16 ≠ 0)
  · rw [card_sites]
    compute_degree!
  · intro x hx
    have := (mem_nthRootsFinset (by decide : 0 < 16) _).mp (sites_eq_roots ▸ hx)
    simp [this]

private theorem pencil_monic (c : F) : (P - C c * B).Monic := by
  unfold P B
  monicity!

private theorem pencil_deg (c : F) : (P - C c * B).natDegree ≤ 5 := by
  unfold P B
  compute_degree!

private theorem fibers :
    Lagrange.nodal first id = P - C 1 * B ∧
    Lagrange.nodal second id = P - C 2 * B ∧
    Lagrange.nodal third id = P - C 3 * B := by
  refine ⟨nodal_of_roots first _ (pencil_monic 1) (pencil_deg 1) ?_,
    nodal_of_roots second _ (pencil_monic 2) (pencil_deg 2) ?_,
    nodal_of_roots third _ (pencil_monic 3) (pencil_deg 3) ?_⟩ <;>
    simp only [P,B,eval_sub,eval_mul,eval_add,eval_pow,eval_X,eval_ofNat,eval_C] <;> decide

private theorem nonvanishing : ∀ x : F, P.eval x ≠ 0 := by
  simp only [P,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat]
  decide

private theorem coprime_nodal : IsCoprime P (Lagrange.nodal sites id) := by
  apply IsCoprime.prod_right
  intro x _
  apply IsCoprime.symm
  apply (irreducible_X_sub_C x).coprime_iff_not_dvd.mpr
  exact fun h => nonvanishing x (dvd_iff_isRoot.mp h)

private noncomputable def bezP : F[X] := 10*X₁₇^3 + 2*X₁₇^2 + 10*X₁₇ + 6
private noncomputable def bezB : F[X] := 10*X₁₇^4 + 11*X₁₇^3 + 3*X₁₇ + 2
private noncomputable def quotient : F[X] :=
  16*X₁₇^11 + 4*X₁₇^10 + 15*X₁₇^9 + 14*X₁₇^8 + X₁₇^7 + 2*X₁₇^5 + X₁₇^4 + X₁₇^3 + 12*X₁₇^2 + 11*X₁₇ + 6

private theorem pencil_coprime : IsCoprime P B := by
  refine ⟨bezP,bezB,eq_of_natDegree_lt_card_of_eval_eq _ _ (f := @id F) Function.injective_id ?_ ?_⟩
  · simp only [id_eq,bezP,bezB,P,B,eval_add,eval_mul,eval_X,eval_pow,eval_ofNat,eval_one]
    decide
  · rw [ZMod.card]
    apply max_lt
    · simp only [bezP,bezB,P,B]
      compute_degree!
    · simp

private theorem weight_dvd : P ∣ W*B - Lagrange.nodal sites id := by
  rw [nodal_sites]
  refine ⟨quotient,eq_of_natDegree_lt_card_of_eval_eq _ _ (f := @id F) Function.injective_id ?_ ?_⟩
  · simp only [id_eq,P,B,W,quotient,eval_add,eval_mul,eval_X,eval_pow,eval_sub,eval_ofNat,eval_one]
    decide
  · rw [ZMod.card]
    apply max_lt <;> simp only [W,B,P,quotient] <;> compute_degree!

/-- The first received row. -/
noncomputable def u (x : sites) : F := (x.val * W.eval x.val) / P.eval x.val

/-- The second received row. -/
noncomputable def v (x : sites) : F := -(W.eval x.val / P.eval x.val)

/-- The prescribed Reed–Solomon code has length sixteen and dimension eight. -/
noncomputable def code : Set (sites → F) :=
  ReedSolomon.code (Function.Embedding.subtype (· ∈ sites)) 8

private instance : Nonempty sites := ⟨⟨1, by decide⟩⟩

open Classical in
private theorem upper (a b : sites → F) :
    (univ.filter fun t : F => mcaEvent code (4/16) a b t).card ≤ 15 := by
  exact ApolarEndpointExact.pair_bound (Function.Embedding.subtype (· ∈ sites)) a b
    (e := 4) (n := 16) ((Fintype.card_coe sites).trans card_sites) rfl (by decide) (by decide)

private theorem bad_on_fiber (A : Finset F) (c t : F) (hA : A.card = 5) (ht : t ∈ A)
    (hsub : A ⊆ sites) (hc : c ≠ 0) (hf : Lagrange.nodal A id = P - C c * B) :
    mcaEvent code (4/16) u v t := by
  have hP : P.Monic := by unfold P; monicity!
  have hd : P.natDegree = 5 := by unfold P; compute_degree!
  have hw : W.natDegree < P.natDegree := by rw [hd]; unfold W; compute_degree!
  have h := RationalFiberEndpoint.event_of_fiber sites A 8 4 (by decide) (by decide)
    card_sites hA ht ((erase_subset t A).trans hsub) hc P B W hP hd hw
    pencil_coprime coprime_nodal weight_dvd hf
  rw [card_sites,Nat.cast_ofNat] at h
  convert h using 1 <;> rfl

open Classical in
/-- On the two displayed rows the bad scalars are precisely the residues
2 through 16. -/
theorem bad_scalars :
    (univ.filter fun t : F => mcaEvent code (4/16) u v t) = sites.erase 1 := by
  apply Eq.symm
  apply eq_of_subset_of_card_le _ (upper u v)
  intro t ht
  apply mem_filter.mpr
  refine ⟨mem_univ t, ?_⟩
  have h := (by decide : ∀ x : F, x ∈ sites.erase 1 → x ∈ first ∨ x ∈ second ∨ x ∈ third) t ht
  rcases h with h | h | h
  · exact bad_on_fiber first 1 t (by decide) h (by decide) (by decide) fibers.1
  · exact bad_on_fiber second 2 t (by decide) h (by decide) (by decide) fibers.2.1
  · exact bad_on_fiber third 3 t (by decide) h (by decide) (by decide) fibers.2.2

/-- The worst-case scalar error probability on the prescribed subgroup is
exactly fifteen seventeenths at four errors. -/
theorem exact_probability :
    epsMCA (F := F) code (4/16) = (15 : ℝ≥0∞) / 17 := by
  classical
  apply le_antisymm
  · apply (epsMCA_le_of_badCount_le code _ 15 ?_).trans (by rw [ZMod.card]; rfl)
    intro w
    exact upper (w 0) (w 1)
  · rw [epsMCA_eq_iSup_badCount_div,ZMod.card]
    apply ENNReal.div_le_div_right
    let w : WordStack F (Fin 2) sites := ![u,v]
    apply LE.le.trans _ (le_iSup _ w)
    have h : (univ.filter fun t : F => mcaEvent code (4/16) u v t).card = 15 := by
      rw [bad_scalars]
      decide
    exact_mod_cast h.ge

#print axioms bad_scalars
#print axioms exact_probability

end ArkLib.ProximityGap.Frontier.SmoothQuinticSeventeen

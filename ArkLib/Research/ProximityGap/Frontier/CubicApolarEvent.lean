/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.CubicApolarWitness
import ArkLib.Extensions.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Algebra.Ring.GeomSum

/-! # The cubic locator supplies the actual Reed–Solomon MCA event -/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.CubicApolarEvent
open Polynomial Finset CubicApolarWitness
open scoped NNReal

/-- The cubic identity, complementary vanisher, and its degree certify MCA
badness on the same witness set at exact Hamming radius e/n. -/
theorem bad_at_locator {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι] (dom : ι ↪ F) (V Q : F[X]) (t : F) (e L : ℕ)
    (he : 2 ≤ e) (hn : Fintype.card ι = 4*(e+1)) (hV : V.natDegree=4*(e+1))
    (hQ : Q.natDegree=4*(e+1)-e) (hid : V*(X^3-C t)=Q*(X^(e+3)-C (t^L)))
    (S : Finset ι) (hS : S.card=4*(e+1)-e) (hz : ∀ i ∈ S, Q.eval (dom i)=0) :
    _root_.ProximityGap.mcaEvent (ReedSolomon.code dom (2*(e+1)) : Set (ι → F))
      ((e:ℝ≥0)/(Fintype.card ι)) (fun i => ((V*X^3) /ₘ X^(e+3)).eval (dom i))
      (fun i => -(V /ₘ X^(e+3)).eval (dom i)) t := by
  classical
  have hs' : (S.map dom).card=4*(e+1)-e := by simpa using hS
  obtain ⟨⟨P,hP,hagree⟩,hno⟩ := folding_without_joint V Q t e L he hV hQ hid
    (S.map dom) hs' (fun x hx => by obtain ⟨i,hi,rfl⟩ := mem_map.mp hx; exact hz i hi)
  refine ⟨S, ?_, ⟨fun i => P.eval (dom i),
    ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval P hP (fun _ => rfl), ?_⟩, ?_⟩
  · rw [tsub_mul, one_mul, div_mul_cancel₀ _ (by rw [hn]; positivity), hn, hS,
      Nat.cast_tsub]
  · intro i hi
    simpa only [smul_eq_mul, mul_neg, ← sub_eq_add_neg] using
      hagree (dom i) (mem_map.mpr ⟨i,hi,rfl⟩)
  · rintro ⟨_,_,row₁,hrow,joint⟩
    have : NeZero (2*(e+1)) := ⟨by omega⟩
    obtain ⟨P₁,h₁,hpoly⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hrow
    apply hno
    refine ⟨P₁,h₁,?_⟩
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_map.mp hx
    exact (hpoly i).trans (joint i hi).2

/-- The explicit cubic geometric sum is the locator for the construction. -/
noncomputable def locator {F : Type*} [Field F] (l : ℕ) (t : F) : F[X] :=
  ∑ i ∈ range (l+1), (X^3)^i * (C t)^(l-i)

/-- Multiplying the cubic locator by its three excluded roots recovers
the entire coset polynomial. -/
theorem locator_identity {F : Type*} [Field F] (l : ℕ) (t : F) :
    locator l t * (X^3-C t) = X^(3*l+3) - C (t^(l+1)) := by
  rw [show 3*l+3 = 3*(l+1) by omega, pow_mul, map_pow]
  simpa only [locator, Nat.add_sub_cancel] using geom_sum₂_mul (X^3 : F[X]) (C t) (l+1)

/-- A complementary factor for the explicit locator gives an MCA event on
every domain satisfying the stated complement cardinality and vanishing. -/
theorem bad_at_cubic_factor {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι] (dom : ι ↪ F) (V Q : F[X]) (t : F) (l : ℕ)
    (hl : 1 ≤ l) (hn : Fintype.card ι = 4*(3*l+1)) (hV : V.natDegree=4*(3*l+1))
    (hQ : Q.natDegree=4*(3*l+1)-3*l) (hfac : V = Q * locator l t)
    (S : Finset ι) (hS : S.card=4*(3*l+1)-3*l) (hz : ∀ i ∈ S, Q.eval (dom i)=0) :
    _root_.ProximityGap.mcaEvent (ReedSolomon.code dom (2*(3*l+1)) : Set (ι → F))
      (((3*l:ℕ):ℝ≥0) / (Fintype.card ι)) (fun i => ((V*X^3) /ₘ X^(3*l+3)).eval (dom i))
      (fun i => -(V /ₘ X^(3*l+3)).eval (dom i)) t := by
  apply bad_at_locator dom V Q t (3*l) (l+1) (by omega) hn hV hQ _ S hS hz
  rw [hfac, mul_assoc, locator_identity]

#print axioms locator_identity
#print axioms bad_at_cubic_factor
#print axioms bad_at_locator
end ArkLib.ProximityGap.Frontier.CubicApolarEvent

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothQuinticSeventeen
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-! # Every scalar can be bad at five errors on the order-sixteen subgroup of the field of order seventeen

The four degree-six polynomials each agree with the center on ten sites.
A scalar-specific eleventh match yields a witness, since ten shared sites
uniquely determine both component polynomials of degree below eight.
-/

set_option autoImplicit false
open Finset Polynomial ProximityGap Code
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.SmoothSeventeenFiveErrors

open SmoothQuinticSeventeen (F sites code card_sites)
local instance : Fact (Nat.Prime 17) := ⟨by decide⟩
local instance : AddCommGroup F := (inferInstance : Field F).toDivisionRing.toAddCommGroup
private instance : Nonempty sites := ⟨⟨1, by decide⟩⟩

/-- The four scalar heads in ascending coefficient order, evaluated by Horner's rule. -/
def head {A : Type*} [Ring A] (i : Fin 4) (x : A) : A :=
  match i with
  | 0 => 0
  | 1 => 12 + x * (15 + x * (8 + x * (8 + x * (x * (15 + x)))))
  | 2 => 6 + x * (9 + x * (16 + x * (11 + x * (3 + x * (16 + x * 11)))))
  | 3 => 10 + x * (11 + x * (11 + x * (15 + x * (16 + x * (11 + x * 5)))))

/-- The first received word, including the value zero at the puncture. -/
def first (i : sites) : F :=
  match i.val.val with
  | 2 => 2
  | 3 => 10
  | 4 => 4
  | 5 => 3
  | 14 => 1
  | _ => 0

/-- The second word uses the direction (1,X−1) and takes value eight at the puncture. -/
def second (i : sites) : F :=
  if i.val = 1 then 8 else (i.val-1) * first i

private def labelHead (t : F) : Fin 4 :=
  match t.val with
  | 1 | 2 | 6 | 10 | 14 => 1
  | 3 | 5 | 7 | 9 => 2
  | 12 | 15 => 3
  | _ => 0

private def core (i : Fin 4) : Finset sites :=
  univ.filter fun x => head i x.val = first x ∧ (x.val-1)*head i x.val = second x

private def witness (t : F) : Finset sites :=
  univ.filter fun x =>
    head (labelHead t) x.val + t * ((x.val-1)*head (labelHead t) x.val) =
      first x + t * second x

set_option maxRecDepth 8192 in
private theorem counts : (∀ i : Fin 4, (core i).card = 10) ∧ (∀ t : F, 11 ≤ (witness t).card) := by
  decide

private theorem core_subset (t : F) : core (labelHead t) ⊆ witness t := by
  intro x hx
  obtain ⟨h₁,h₂⟩ := (mem_filter.mp hx).2
  exact mem_filter.mpr ⟨mem_univ _, by rw [h₂, h₁]⟩

private theorem head_eval (i : Fin 4) (x : F) :
    (head i (Polynomial.X : F[X])).eval x = head i x := by
  fin_cases i <;> simp [head]

private theorem head_deg (i : Fin 4) : (head i (Polynomial.X : F[X])).natDegree ≤ 6 := by
  fin_cases i <;> simp only [head] <;> compute_degree!

/-- Each of the seventeen scalars has a literal bad-event witness of at least eleven sites. -/
theorem all_bad (t : F) : mcaEvent code (5/16) first second t := by
  let i := labelHead t
  let D := head i (Polynomial.X : F[X])
  let E := (Polynomial.X-1)*D
  have hD : D.natDegree ≤ 6 := head_deg i
  have hE : E.natDegree ≤ 7 := by
    dsimp only [E]
    have := natDegree_mul_le (p := (Polynomial.X-1 : F[X])) (q := D)
    have h : (Polynomial.X-1 : F[X]).natDegree ≤ 1 := by compute_degree!
    omega
  have evD (x : sites) : D.eval x.val = head i x.val := head_eval i x.val
  have evE (x : sites) : E.eval x.val = (x.val-1)*head i x.val := by simp [E,evD]
  have hd : (D+C t*E).natDegree < 8 := by
    have h₀ := natDegree_mul_le (p := C t) (q := E)
    simp only [natDegree_C,zero_add] at h₀
    have h₁ := natDegree_add_le D (C t*E)
    omega
  refine ⟨witness t, ?_, ⟨fun x => (D+C t*E).eval x.val,
    ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval _ hd (fun _ => rfl), ?_⟩, ?_⟩
  · rw [Fintype.card_coe,card_sites,Nat.cast_ofNat]
    rw [tsub_mul, one_mul, div_mul_cancel₀ _ (by norm_num),
      show (16 : ℝ≥0) - 5 = 11 from tsub_eq_of_eq_add (by norm_num)]
    exact_mod_cast counts.2 t
  · intro x hx
    simpa only [eval_add,eval_mul,eval_C,evD,evE,smul_eq_mul] using (mem_filter.mp hx).2
  · rintro ⟨u,hu,v,hv,hj⟩
    obtain ⟨P,hP,hpu⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hu
    obtain ⟨Q,hQ,hqv⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hv
    have pin (A B : F[X]) (ha : A.natDegree < 8) (hb : B.natDegree < 8)
        (h : ∀ x ∈ core i, A.eval x.val = B.eval x.val) : A = B := by
      apply eq_of_natDegree_lt_card_of_eval_eq A B (f := fun u : core i => u.val.val)
        (Subtype.val_injective.comp Subtype.val_injective) (fun u => h _ u.property)
      rw [Fintype.card_coe,counts.1 i]
      omega
    have pD : P = D := pin P D hP (by omega) fun x hx => by
      exact (hpu x).trans (((hj x (core_subset t hx)).1).trans ((mem_filter.mp hx).2.1.symm |>.trans (evD x).symm))
    have qE : Q = E := pin Q E hQ (by omega) fun x hx => by
      exact (hqv x).trans (((hj x (core_subset t hx)).2).trans ((mem_filter.mp hx).2.2.symm |>.trans (evE x).symm))
    have sub : witness t ⊆ core i := by
      intro x hx
      refine mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩
      · exact (evD x).symm.trans (pD ▸ (hpu x).trans (hj x hx).1)
      · exact (evE x).symm.trans (qE ▸ (hqv x).trans (hj x hx).2)
    have hh := card_le_card sub
    rw [counts.1 i] at hh
    have := counts.2 t
    omega

/-- The worst-case MCA probability on the full order-sixteen subgroup is one at five errors. -/
theorem exact_probability : epsMCA (F := F) code (5/16) = 1 := by
  exact epsMCA_eq_one_of_forall_mcaEvent code _ ![first,second] all_bad

#print axioms all_bad
#print axioms exact_probability
end ArkLib.ProximityGap.Frontier.SmoothSeventeenFiveErrors

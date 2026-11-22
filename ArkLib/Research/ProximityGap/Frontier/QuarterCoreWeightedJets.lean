/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TangentHeadWindows
import ArkLib.Data.Polynomial.SpecializationAvoidance

/-! # Lower jet orders on three rich cores at quarter rate

A polynomial section outside the three affine heads has at most d agreements
on each joint core. Lowering the order there reduces the dimension cost of
interpolation while preserving the weight needed to capture every such section.
-/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.QuarterCoreWeightedJets
open Finset Polynomial SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation

abbrev n : ℕ := 1073741824
abbrev d : ℕ := 268435455
abbrev e : ℕ := 525150000
abbrev t : ℕ := n-e
abbrev c : ℕ := t-255
abbrev weight : ℕ := 23*t-6*d

variable {I : Type*} [DecidableEq I]

private def mark (A : Finset I) (x : I) : ℕ := if x ∈ A then 1 else 0

/-- The unconditioned interpolants separate rich factors and affine heads. -/
theorem parameters : 2051368 = max (e/256+1) (21569*44+22*379+1) ∧
    21569*40+22*301 < 2051368 ∧ n+2*d < 3*c ∧ n*d < t^2 ∧
    d + 379*n/2051368 + 3*(379*n/(2051368-379)) < t := by decide

omit [DecidableEq I] in
/-- The two unconditioned surfaces contain the chosen section at every bad scalar. -/
theorem ordinary_surfaces {F : Type} [Field F] [Fintype I] (dom : I ↪ F) (u v : I → F)
    (hn : Fintype.card I = n) (companion : Bool) :
    let r := if companion then 22 else 11
    let b := if companion then 44 else 22
    let s := if companion then 379 else 21569
    ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
      (∀ j h x, ((Q.coeff j).coeff h).coeff x ≠ 0 → j ≤ b ∧ h+j ≤ s ∧ x+j*d < r*t) ∧
      ∀ g : F, ∀ q : F[X], q.natDegree ≤ d → ∀ S : Finset I, t ≤ S.card →
        (∀ x ∈ S, q.eval (dom x) = u x + g*v x) → Q.eval₂ (evalRingHom (Polynomial.C g)) q = 0 := by
  dsimp only
  let r := if companion then 22 else 11
  let b := if companion then 44 else 22
  let s := if companion then 379 else 21569
  have hnum : 0 < r ∧ 0 < t ∧ r ≤ s+1 ∧
      Fintype.card I * Fintype.card (JetRows s r) < Fintype.card (Monomials s b d (r*t)) := by
    rw [hn]
    cases companion <;>
      simp only [JetRows,Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin] <;>
      norm_num [Fin.sum_univ_succ,r,s,b,d,t,n,e] <;> decide +kernel
  obtain ⟨a,ha,_,hf⟩ := exists_surface dom u v hnum.1 hnum.2.1 hnum.2.2.1 hnum.2.2.2
  refine ⟨surface a,surface_ne_zero ha,fun _ _ _ h => surface_support a h,?_⟩
  intro g q hq S hs hg
  rw [surface_eval]
  exact hf g q hq S hs hg

/-- Each owned position saves two mixed-jet orders for every owning head. -/
def order (A B C : Finset I) (x : I) : ℕ := 23-2*(mark A x + mark B x + mark C x)

private theorem marks (T A : Finset I) : ∑ x ∈ T, mark A x = (T ∩ A).card := by
  classical
  unfold mark
  rw [← Finset.sum_filter]
  simp [Finset.filter_mem_eq_inter]

private def rows (b : ℕ) : ℕ := ∑ j ∈ range b, (b-j)*(302-j)

private theorem card_rows (b : ℕ) : Fintype.card (JetRows 301 b) = rows b := by
  simp only [JetRows,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,rows]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => (b-j)*(302-j)) b

private theorem local_rows (A B C : Finset I) (x : I) :
    rows (order A B C x) + 13106 * (mark A x + mark B x + mark C x) ≤
      81328 + 1208 * (mark (A ∩ B) x + mark (A ∩ C) x + mark (B ∩ C) x) := by
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> by_cases hc : x ∈ C <;>
    simp [order,mark,ha,hb,hc] <;> decide

/-- The actual collection of site-dependent jet constraints fits the monomial space. -/
theorem row_budget [Fintype I] (A B C : Finset I) (hn : Fintype.card I = n)
    (ha : c ≤ A.card) (hb : c ≤ B.card) (hc : c ≤ C.card)
    (hab : (A ∩ B).card ≤ d) (hac : (A ∩ C).card ≤ d) (hbc : (B ∩ C).card ≤ d) :
    Fintype.card ((x : I) × JetRows 301 (order A B C x)) <
      Fintype.card (Monomials 301 40 d weight) := by
  classical
  have h := sum_le_sum (s := (univ : Finset I)) (fun x _ => local_rows A B C x)
  simp only [sum_add_distrib,← mul_sum, marks,univ_inter,sum_const,card_univ,hn,nsmul_eq_mul,
    Nat.cast_id] at h
  have cols : Fintype.card (Monomials 301 40 d weight) = 66730729902264 := by
    simp only [Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
    norm_num [Fin.sum_univ_succ,weight,t,n,e,d]
  rw [cols,Fintype.card_sigma]
  simp only [card_rows]
  dsimp only [c,t,n,e,d] at *
  omega

/-- Every agreement set meeting each selected core in at most d sites has
enough total order to force identical vanishing of the specialized section. -/
theorem agreement_weight (A B C S : Finset I) (hs : t ≤ S.card)
    (ha : (S ∩ A).card ≤ d) (hb : (S ∩ B).card ≤ d) (hc : (S ∩ C).card ≤ d) :
    weight ≤ ∑ x ∈ S, order A B C x := by
  have h := sum_congr (s₁ := S) rfl (fun x _ =>
    show order A B C x + 2*(mark A x + mark B x + mark C x) = 23 by
      by_cases a : x ∈ A <;> by_cases b : x ∈ B <;> by_cases c : x ∈ C <;> simp [order,mark,a,b,c])
  simp only [sum_add_distrib,← mul_sum,marks,sum_const,nsmul_eq_mul,Nat.cast_id] at h
  dsimp only [weight,t,n,e,d] at *
  omega

/-- A single nonzero received-row surface captures every residual section for these cores. -/
theorem residual_surface {F : Type} [Field F] [Fintype I] (dom : I ↪ F) (u v : I → F)
    (A B C : Finset I) (hn : Fintype.card I = n) (ha : c ≤ A.card) (hb : c ≤ B.card)
    (hc : c ≤ C.card) (hab : (A ∩ B).card ≤ d) (hac : (A ∩ C).card ≤ d) (hbc : (B ∩ C).card ≤ d) :
    ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
      (∀ j h x, ((Q.coeff j).coeff h).coeff x ≠ 0 → j ≤ 40 ∧ h+j ≤ 301 ∧ x+j*d < weight) ∧
      ∀ g : F, ∀ q : F[X], q.natDegree ≤ d → ∀ S : Finset I, t ≤ S.card →
        (S ∩ A).card ≤ d → (S ∩ B).card ≤ d → (S ∩ C).card ≤ d →
        (∀ x ∈ S, q.eval (dom x) = u x + g*v x) → Q.eval₂ (evalRingHom (Polynomial.C g)) q = 0 := by
  obtain ⟨a,ha',_,hf⟩ := exists_order_surface dom u v (order A B C) (by decide : 0 < weight)
    (fun x => by unfold order; omega) (row_budget A B C hn ha hb hc hab hac hbc)
  refine ⟨surface a,surface_ne_zero ha',fun _ _ _ h => surface_support a h,?_⟩
  intro g q hq S hs h1 h2 h3 hg
  rw [surface_eval]
  exact hf g q hq S (agreement_weight A B C S hs h1 h2 h3) hg

/-- The difference from a fixed affine head pays at most d sites on its joint core. -/
theorem outside_overlap {F : Type} [Field F] (dom : I ↪ F) (u v : I → F)
    (A B q : F[X]) (g : F) (K S : Finset I)
    (hA : A.natDegree ≤ d) (hB : B.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (hne : q ≠ A + Polynomial.C g * B)
    (core : ∀ x ∈ K, A.eval (dom x) = u x ∧ B.eval (dom x) = v x)
    (ag : ∀ x ∈ S, q.eval (dom x) = u x + g*v x) : (S ∩ K).card ≤ d := by
  have hd : (A + Polynomial.C g * B).natDegree ≤ d :=
    (natDegree_add_le ..).trans (max_le hA ((natDegree_C_mul_le _ _).trans hB))
  apply le_trans (b := (q-(A+Polynomial.C g*B)).natDegree) _ ((natDegree_sub_le ..).trans (max_le hq hd))
  apply Polynomial.card_le_natDegree_of_injOn_of_eval_eq_zero (sub_ne_zero.mpr hne) dom.injective.injOn
  intro x hx
  obtain ⟨hs,hk⟩ := mem_inter.mp hx
  obtain ⟨ha,hb⟩ := core x hk
  simp [eval_sub,ag x hs,ha,hb]

/-- The reciprocal population bound and the union bound for collinear cores. -/
def headBound (j : ℕ) : ℕ :=
  if j < 3 then j*(e+1) else
    let denom := c+(j-1)*d
    let U := (j*c^2+denom-1)/denom
    min (j*(e+1)) (j*n-(j-1)*U)

/-- Nonlinear factors of a weighted residual surface have scalar/value degree at most 301. -/
def price (l j b : ℕ) : ℕ :=
  TangentHeadWindows.factorPrice n d t 2051368 (11*t-1-(l-b)*d)
    (if 3 ≤ j then min (379-j) 301 else 379-j) b

private theorem prices : ∀ l j b : Fin 23, j.val ≤ l.val →
    21569 + headBound j.val ≤ 2147483648 ∧ (0 < b.val → b.val ≤ l.val-j.val →
      (l.val-j.val)*price l.val j.val b.val ≤ b.val*(2147483648-(21569+headBound j.val))) := by
  set_option maxRecDepth 40000 in
  set_option maxHeartbeats 2500000 in
  decide

/-- All partitions of the positive value degrees, with scalar-only factors charged separately. -/
theorem allocation {α : Type*} (S : Finset α) (deg pop : α → ℕ) (l j : Fin 23)
    (hj : j.val ≤ l.val) (hpos : ∀ x ∈ S, 0 < deg x)
    (hdeg : ∑ x ∈ S, deg x = l.val-j.val) (hpop : ∀ x ∈ S, pop x ≤ price l.val j.val (deg x)) :
    21569 + headBound j.val + ∑ x ∈ S, pop x ≤ 2147483648 := by
  have base := (prices l j 0 hj).1
  by_cases hz : l.val-j.val = 0
  · have he : S = ∅ := by
      by_contra hn
      obtain ⟨x,hx⟩ := nonempty_iff_ne_empty.mpr hn
      have h := single_le_sum (f := deg) (fun _ _ => Nat.zero_le _) hx
      rw [hdeg,hz] at h
      exact (hpos x hx).not_ge h
    simpa [he] using base
  · apply TangentHeadWindows.sum_prices S deg pop (Nat.pos_of_ne_zero hz) base hdeg
    intro x hx
    have h := single_le_sum (f := deg) (fun _ _ => Nat.zero_le _) hx
    rw [hdeg] at h
    let b : Fin 23 := ⟨deg x,h.trans_lt ((Nat.sub_le _ _).trans_lt l.isLt)⟩
    exact (Nat.mul_le_mul_left _ (hpop x hx)).trans ((prices l j b hj).2 (hpos x hx) h)

#print axioms ordinary_surfaces
#print axioms outside_overlap
#print axioms allocation
#print axioms row_budget
#print axioms agreement_weight
#print axioms residual_surface
end ArkLib.ProximityGap.Frontier.QuarterCoreWeightedJets

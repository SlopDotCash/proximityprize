/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.LinearPencilFreshLabels
import Mathlib.LinearAlgebra.Lagrange

/-! # Noncollinear polynomial heads with a common locator -/
set_option autoImplicit false
noncomputable section
open Polynomial Finset
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.PlanarQuartetMass
open _root_.ProximityGap
variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Fintype F] [Field F]

/-- Every site outside a head's defining core supplies one fresh label. Locally the
distinct foreign directions are separated by their two-by-two determinants. -/
theorem mass {heads : ℕ} (dom : I ↪ F) (k d : ℕ) (δ : ℝ≥0) (U V : Fin heads → F[X]) (roots : Finset I)
    (owner : I → Fin heads) (core : Fin heads → Finset I) (hdeg : roots.card+d+1 < k)
    (hU : ∀ j, (U j).natDegree ≤ d) (hV : ∀ j, (V j).natDegree ≤ d)
    (hroot : ∀ j, roots ⊆ core j)
    (hcore : ∀ i x, x ∈ core i → x ∉ roots →
      (U i).eval (dom x)=(U (owner x)).eval (dom x) ∧ (V i).eval (dom x)=(V (owner x)).eval (dom x))
    (hmis : ∀ i x, x ∉ core i → (V i).eval (dom x)≠(V (owner x)).eval (dom x))
    (hdet : ∀ x i j, x ∉ core i → x ∉ core j → i≠j →
      ((U (owner x)).eval (dom x)-(U i).eval (dom x))*((V j).eval (dom x)-(V (owner x)).eval (dom x)) ≠
      ((U (owner x)).eval (dom x)-(U j).eval (dom x))*((V i).eval (dom x)-(V (owner x)).eval (dom x)))
    (hcard : ∀ j, k ≤ (core j).card)
    (hsize : ∀ j, (1-δ)*(Fintype.card I:ℝ≥0) ≤ (((core j).card+1 : ℕ):ℝ≥0))
    (hfield : (∑ j, (core j)ᶜ.card).choose 2 ≤ Nat.card F) :
    ((∑ j, (core j)ᶜ.card:ℕ):ℝ≥0∞)/(Fintype.card F:ℝ≥0∞) ≤
      epsMCA (F:=F) (ReedSolomon.code dom k : Set (I → F)) δ := by
  classical
  let J := Lagrange.nodal roots (fun x => dom x)
  let A (i : Fin heads) := J*U i
  let B (i : Fin heads) := J*V i
  let E := (i : Fin heads) × ↥(core i)ᶜ
  let site (e : E) : I := e.2.val
  let key (e : E) : Fin 2 → F :=
    let x := site e
    ![((U (owner x)).eval (dom x)-(U e.1).eval (dom x))/((V e.1).eval (dom x)-(V (owner x)).eval (dom x)),
      -dom x]
  have jc : J.natDegree=roots.card := Lagrange.natDegree_nodal
  have deg {f : F[X]} (h : f.natDegree ≤ d) : (J*f).natDegree ≤ roots.card+d :=
    natDegree_mul_le.trans (add_le_add jc.le h)
  have coreval (j : Fin heads) (x : I) (hx : x∈core j) :
      (A j).eval (dom x)=(A (owner x)).eval (dom x) ∧ (B j).eval (dom x)=(B (owner x)).eval (dom x) := by
    by_cases h : x∈roots
    · have hz : J.eval (dom x)=0 := Lagrange.eval_nodal_at_node h
      simp [A,B,hz]
    · obtain ⟨u,v⟩ := hcore j x hx h
      simp only [A,B,eval_mul,u,v,and_self]
  have hm (e : E) := hmis e.1 (site e) (mem_compl.mp e.2.property)
  have count : Fintype.card E = ∑ j, (core j)ᶜ.card := by simp only [E,Fintype.card_sigma,Fintype.card_coe]
  rw [← count]
  apply LinearPencilFreshLabels.mass_of_distinct_fresh_labels dom k δ (fun e : E => core e.1) site
    (fun e => A e.1) (fun e => Polynomial.X * B e.1) (fun e => B e.1)
    (fun x => (A (owner x)).eval (dom x)) (fun x => dom x*(B (owner x)).eval (dom x))
    (fun x => (B (owner x)).eval (dom x)) key
  · intro e
    exact degree_le_natDegree.trans_lt (by exact_mod_cast (deg (hU e.1)).trans_lt (by omega : roots.card+d<k))
  · intro e
    apply degree_le_natDegree.trans_lt
    have hd := natDegree_mul_le (p:=(Polynomial.X:F[X])) (q:=B e.1)
    rw [natDegree_X] at hd
    have h := deg (hV e.1)
    change (B e.1).natDegree ≤ _ at h
    exact_mod_cast (show (Polynomial.X*B e.1).natDegree<k by omega)
  · intro e
    exact degree_le_natDegree.trans_lt (by exact_mod_cast (deg (hV e.1)).trans_lt (by omega : roots.card+d<k))
  · intro e x hx
    obtain ⟨u,v⟩ := coreval e.1 x hx
    exact ⟨u,by rw [eval_mul,eval_X,v],v⟩
  · exact fun e => hcard e.1
  · exact fun e => hsize e.1
  · intro e
    have h : J.eval (dom (site e))≠0 := by
      apply Lagrange.eval_nodal_not_at_node
      intro y hy hxy
      have hx : site e∈core e.1 := (dom.injective hxy).symm ▸ hroot e.1 hy
      exact mem_compl.mp e.2.property hx
    simp only [B,eval_mul]
    exact fun h' => hm e (mul_left_cancel₀ h h')
  · intro e
    let x := site e
    have h := div_mul_cancel₀ ((U (owner x)).eval (dom x)-(U e.1).eval (dom x)) (sub_ne_zero.mpr (hm e))
    constructor
    · change _ * ((J*V e.1).eval (dom x)-(J*V (owner x)).eval (dom x)) =
          (J*U (owner x)).eval (dom x)-(J*U e.1).eval (dom x)
      simp only [eval_mul,← mul_sub]
      rw [mul_left_comm]
      exact congrArg (fun t => J.eval (dom x) * t) h
    · change (-dom x)*_ = _
      simp only [eval_mul,eval_X]
      ring
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    have hxy : x.val=y.val := dom.injective (neg_injective (congrFun h 1))
    obtain ⟨x,hx⟩ := x
    obtain ⟨y,hy⟩ := y
    change x=y at hxy
    subst y
    have h1 := hm ⟨i,⟨x,hx⟩⟩
    have h2 := hm ⟨j,⟨x,hy⟩⟩
    have hz := (div_eq_div_iff (sub_ne_zero.mpr h1) (sub_ne_zero.mpr h2)).mp (congrFun h 0)
    by_cases he : i=j
    · subst j; rfl
    · exact False.elim (hdet x i j (mem_compl.mp hx) (mem_compl.mp hy) he hz)
  · rwa [count]
#print axioms mass
end ArkLib.ProximityGap.Frontier.PlanarQuartetMass

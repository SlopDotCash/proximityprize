import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring

/-!
# Four simultaneous agreements for dimension-two Reed–Solomon codes

The coordinate type has four blocks of the same nonzero size. The upper bound
counts the six possible pairwise intersections. Four secants of the parabola
give the matching lower bound. The statement uses integer agreement counts.
-/

open Polynomial Finset

namespace ProximityGap.FourSecants

variable {F : Type*} [Field F] {h : ℕ} [NeZero h]

/-- Four distinct dimension-two Reed–Solomon message polynomials with a common
received word and at least `A` agreements each. -/
def FourAt (domain : (Fin h × Fin 4) ↪ F) (A : ℕ) : Prop := by
  classical
  exact ∃ (w : Fin h × Fin 4 → F) (P : Fin 4 → F[X]), Function.Injective P ∧
    ∀ j, (P j).natDegree < 2 ∧ A ≤ (univ.filter (fun x ↦ w x = (P j).eval (domain x))).card

private theorem four_set_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Fin 4 → Finset ι)
    (hp : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) :
    (S 0).card + (S 1).card + (S 2).card + (S 3).card ≤ Fintype.card ι + 6 := by
  classical
  have h₀ := card_union_add_card_inter (S 0) (S 1)
  have h₁ := card_union_add_card_inter (S 0 ∪ S 1) (S 2)
  have h₂ := card_union_add_card_inter (S 0 ∪ S 1 ∪ S 2) (S 3)
  have hcard : (S 0 ∪ S 1 ∪ S 2 ∪ S 3).card ≤ Fintype.card ι := card_le_univ _
  have h01 := hp 0 1 (by decide)
  have h02 := hp 0 2 (by decide)
  have h12 := hp 1 2 (by decide)
  have h03 := hp 0 3 (by decide)
  have h13 := hp 1 3 (by decide)
  have h23 := hp 2 3 (by decide)
  rw [union_inter_distrib_right] at h₁
  simp only [union_inter_distrib_right] at h₂
  have hsum2 := card_union_le (S 0 ∩ S 2) (S 1 ∩ S 2)
  have hsum3 := card_union_le (S 0 ∩ S 3) (S 1 ∩ S 3)
  have hsum4 := card_union_le ((S 0 ∩ S 3) ∪ (S 1 ∩ S 3)) (S 2 ∩ S 3)
  omega

private theorem secant_eval (a b x : F) :
    (C (a+b) * X - C (a*b)).eval x = x^2 - (x-a)*(x-b) := by simp; ring

/-- Sharp four-word agreement bound on every length `4*h` evaluation set. -/
theorem fourAt_iff (domain : (Fin h × Fin 4) ↪ F) (A : ℕ) :
    FourAt domain A ↔ A ≤ h+1 := by
  classical
  constructor
  · rintro ⟨w,P,hP,hA⟩
    let S (j : Fin 4) := univ.filter (fun x ↦ w x = (P j).eval (domain x))
    have hp (i j : Fin 4) (hne : i ≠ j) : (S i ∩ S j).card ≤ 1 := by
      by_contra! hcard
      apply hne (hP ?_)
      apply eq_of_natDegree_lt_card_of_eval_eq (P i) (P j)
        (f := fun x : (S i ∩ S j : Finset _) ↦ domain x.val)
        (domain.injective.comp Subtype.val_injective)
      · intro x
        have hboth := Finset.mem_inter.mp x.property
        exact (mem_filter.mp hboth.1).2.symm.trans (mem_filter.mp hboth.2).2
      · have hi := (hA i).1
        have hj := (hA j).1
        rw [Fintype.card_coe]
        omega
    have bound := four_set_bound S (fun i j hij ↦ hp i j hij)
    simp only [Fintype.card_prod, Fintype.card_fin] at bound
    have h0 : A ≤ (S 0).card := (hA 0).2
    have h1 : A ≤ (S 1).card := (hA 1).2
    have h2 : A ≤ (S 2).card := (hA 2).2
    have h3 : A ≤ (S 3).card := (hA 3).2
    omega
  · intro ha
    let a (i : Fin 4) := domain (0,i)
    have ai : Function.Injective a := by
      intro i j h'
      exact congrArg Prod.snd (domain.injective h')
    let P (i : Fin 4) : F[X] := C (a i+a (i+1)) * X - C (a i*a (i+1))
    have hsec (j : Fin 4) (x : F) : (P j).eval x = x^2 - (x-a j)*(x-a (j+1)) := secant_eval ..
    have pinj : Function.Injective P := by
      intro i j heq
      by_contra hij
      have hedges : ∀ i j : Fin 4, i ≠ j → ∃ u : Fin 4,
        (u=i ∨ u=i+1) ∧ u≠j ∧ u≠j+1 := by decide
      obtain ⟨u,hu,hu0,hu1⟩ := hedges i j hij
      have hroot := congrArg (fun p : F[X] ↦ p.eval (a u)) heq
      change (P i).eval (a u) = (P j).eval (a u) at hroot
      rw [hsec, hsec] at hroot
      have hz : (a u-a i)*(a u-a (i+1))=0 := by rcases hu with rfl | rfl <;> simp
      have hh : (a u-a j)*(a u-a (j+1))=0 := by simpa [hz] using hroot.symm
      rcases mul_eq_zero.mp hh with hh | hh
      · exact hu0 (ai (sub_eq_zero.mp hh))
      · exact hu1 (ai (sub_eq_zero.mp hh))
    let w (x : Fin h × Fin 4) := if x.1 = 0 then (a x.2)^2 else (P x.2).eval (domain x)
    refine ⟨w,P,pinj,fun j ↦ ⟨?_, ?_⟩⟩
    · dsimp [P]
      apply lt_of_le_of_lt (natDegree_sub_le _ _) _
      apply max_lt
      · exact lt_of_le_of_lt natDegree_mul_le (by simp)
      · simp only [natDegree_C]; omega
    · let block : Finset (Fin h × Fin 4) := univ ×ˢ {j}
      have hblock : block.card = h := by simp [block]
      have hnew : (0,j+1) ∉ block := by simp [block]
      have hs : insert (0,j+1) block ⊆ univ.filter (fun x ↦ w x = (P j).eval (domain x)) := by
        intro x hx
        refine mem_filter.mpr ⟨mem_univ _,?_⟩
        rcases mem_insert.mp hx with rfl | hxb
        · simp [w, hsec, a]
        · have hxj : x.2 = j := by
            exact Finset.mem_singleton.mp (Finset.mem_product.mp hxb).2
          rcases x with ⟨r,s⟩
          change s=j at hxj
          subst s
          by_cases hr : r=0
          · subst r; simp [w, hsec, a]
          · simp [w, hr]
      have hc := card_le_card hs
      rw [card_insert_of_notMem hnew, hblock] at hc
      exact ha.trans hc

#print axioms fourAt_iff
end ProximityGap.FourSecants

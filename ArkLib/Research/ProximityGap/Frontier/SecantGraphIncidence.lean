/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Powerset

/-! # Four secant heads with at least five distinct endpoints

At any multiply owned site outside the common roots, all owners are incident
to one vertex whose fiber contains the site. Count the excess over one owner
against that vertex's degree minus one. This argument allows arbitrary site
assignments and unequal vertex fibers.
-/

namespace ProximityGap.SecantGraphIncidence
open Finset

variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]

/-- From any set of selected edges, either the target vertex count has been
reached or one additional edge covers a new vertex. -/
private theorem grow {E : Type*} [Fintype E] [DecidableEq E] (ends : E → Finset V)
    (used : ∀ v, ∃ e, v ∈ ends e) (sel : Finset E) {a : ℕ}
    (hlt : a < Fintype.card V) (h : a ≤ (sel.biUnion ends).card) :
    ∃ T : Finset E, T.card ≤ sel.card+1 ∧ a+1 ≤ (T.biUnion ends).card := by
  classical
  by_cases done : a+1 ≤ (sel.biUnion ends).card
  · exact ⟨sel,by omega,done⟩
  obtain ⟨v,_,hv⟩ := exists_mem_notMem_of_card_lt_card
    (s := sel.biUnion ends) (t := univ) (by rw [card_univ]; omega)
  obtain ⟨e, he⟩ := used v
  have ne : e ∉ sel := fun he' => hv (subset_biUnion_of_mem ends he' he)
  have sub := biUnion_subset_biUnion_of_subset_left ends (subset_insert e sel)
  have hv' : v ∈ (insert e sel).biUnion ends := subset_biUnion_of_mem ends (mem_insert_self ..) he
  have strict := card_lt_card (ssubset_of_subset_of_ne sub (fun eq => hv (eq ▸ hv')))
  exact ⟨insert e sel, by simp [ne], by omega⟩

/-- Any graph with at least four edges using at least five vertices contains
four edges using at least five vertices. -/
theorem select_four {E : Type*} [Fintype E] [DecidableEq E] (ends : E → Finset V)
    (hedges : 4 ≤ Fintype.card E) (pair : ∀ e, 2 = (ends e).card)
    (used : ∀ v, ∃ e, v ∈ ends e) (hvertices : 5 ≤ Fintype.card V) :
    ∃ S : Finset E, S.card = 4 ∧ 5 ≤ (S.biUnion ends).card := by
  classical
  obtain ⟨e⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card E by omega)
  obtain ⟨s₂,c₂,v₂⟩ := grow ends used {e} (a := 2) (by omega) (by simp [← pair])
  obtain ⟨s₃,c₃,v₃⟩ := grow ends used s₂ (a := 3) (by omega) v₂
  obtain ⟨s₄,c₄,v₄⟩ := grow ends used s₃ (a := 4) (by omega) v₃
  simp only [card_singleton] at c₂
  obtain ⟨S, hS, _, hc⟩ := exists_subsuperset_card_eq (subset_univ s₄)
    (n := 4) (by omega) (by simpa)
  exact ⟨S, hc, v₄.trans (card_le_card (biUnion_subset_biUnion_of_subset_left ends hS))⟩

/-- Starting with any two vertex-disjoint edges, the same argument finds
four edges on at least six vertices whenever six vertices are used. -/
theorem select_four_of_disjoint {E : Type*} [Fintype E] [DecidableEq E] (ends : E → Finset V)
    (hedges : 4 ≤ Fintype.card E) (pair : ∀ e, (ends e).card = 2)
    (used : ∀ v, ∃ e, v ∈ ends e) (hvertices : 6 ≤ Fintype.card V)
    {e f : E} (disjoint : Disjoint (ends e) (ends f)) :
    ∃ S : Finset E, S.card = 4 ∧ 6 ≤ (S.biUnion ends).card := by
  classical
  have initial : 4 ≤ (({e,f} : Finset E).biUnion ends).card := by
    simp [biUnion_insert, card_union_of_disjoint disjoint, pair]
  obtain ⟨T,cT,vT⟩ := grow ends used {e,f} (a := 4) (by omega) initial
  obtain ⟨U,cU,vU⟩ := grow ends used T (a := 5) (by omega) vT
  have two : ({e,f} : Finset E).card ≤ 2 := card_le_two
  obtain ⟨S, hS, _, hc⟩ := exists_subsuperset_card_eq (subset_univ U)
    (n := 4) (by omega) (by simpa)
  exact ⟨S, hc, vU.trans (card_le_card (biUnion_subset_biUnion_of_subset_left ends hS))⟩

/-- At most five used vertices give at most ten distinct simple edge heads. -/
theorem at_most_ten {E : Type*} [Fintype E] (ends : E → Finset V)
    (simple : Function.Injective ends) (pair : ∀ e, (ends e).card = 2)
    (hvertices : Fintype.card V ≤ 5) : Fintype.card E ≤ 10 := by
  classical
  let edge (e : E) : (univ : Finset V).powersetCard 2 :=
    ⟨ends e, mem_powersetCard.mpr ⟨subset_univ _,pair e⟩⟩
  have hinj : Function.Injective edge := fun _ _ he => simple (congrArg Subtype.val he)
  calc Fintype.card E ≤ Fintype.card ((univ : Finset V).powersetCard 2) :=
         Fintype.card_le_of_injective edge hinj
       _ = (Fintype.card V).choose 2 := by simp
       _ ≤ (5 : ℕ).choose 2 := Nat.choose_le_choose 2 hvertices
       _ = 10 := by decide

/-- The total excess at vertices equals the endpoint degree sum minus the
number of used vertices. Each unit of excess costs at most one fiber. -/
theorem core_charge {m : ℕ} (hm : 0 < m) (ends : Fin m → Finset V) (fiber : V → Finset I)
    (roots : Finset I) (owners : I → Finset (Fin m)) {c d : ℕ}
    (hedge : ∀ e, (ends e).card ≤ 2) (hused : ∀ v, ∃ e, v ∈ ends e)
    (hsize : ∀ v, (fiber v).card ≤ d)
    (hcores : ∀ e, c ≤ (univ.filter fun x => e ∈ owners x).card)
    (hcollision : ∀ x ∉ roots, 1 < (owners x).card →
      ∃ v, x ∈ fiber v ∧ ∀ e ∈ owners x, v ∈ ends e) :
    m*c ≤ Fintype.card I + (m-1)*roots.card + (2*m-Fintype.card V)*d := by
  classical
  let inc (v : V) := univ.filter fun e => v ∈ ends e
  let excess (v : V) := (inc v).card - 1
  have sumdeg : ∑ v, (inc v).card ≤ 2*m := by
    calc ∑ v, (inc v).card = ∑ e, (ends e).card := by
           simpa [inc, bipartiteBelow, bipartiteAbove] using
             (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
               (s := (univ : Finset V)) (t := univ) (fun v e => v ∈ ends e))
         _ ≤ ∑ _ : Fin m, 2 := sum_le_sum fun e _ => hedge e
         _ = 2*m := by simp [Nat.mul_comm]
  have charge : ∑ v, excess v ≤ 2*m-Fintype.card V := by
    have h (v : V) : excess v + 1 = (inc v).card := by
      obtain ⟨e, he⟩ := hused v
      have hp : 0 < (inc v).card := card_pos.mpr ⟨e, mem_filter.mpr ⟨mem_univ _,he⟩⟩
      dsimp [excess]
      omega
    have hh : ∑ v, (excess v + 1) = ∑ v, (inc v).card := sum_congr rfl fun v _ => h v
    simp [sum_add_distrib] at hh
    omega
  have point (x : I) : (owners x).card ≤ 1 + (if x ∈ roots then m-1 else 0) +
      ∑ v, (if x ∈ fiber v then excess v else 0) := by
    by_cases hr : x ∈ roots
    · have bound : (owners x).card ≤ m := by simpa using (owners x).card_le_univ
      simp only [ite_eq_left hr]
      omega
    · simp only [ite_eq_right hr, Nat.add_zero]
      by_cases hsingle : (owners x).card ≤ 1
      · omega
      obtain ⟨v,hv,hshared⟩ := hcollision x hr (by omega)
      have hle : (owners x).card ≤ (inc v).card :=
        card_le_card fun e he => mem_filter.mpr ⟨mem_univ _,hshared e he⟩
      have one := single_le_sum (s := (univ : Finset V))
        (f := fun v => if x ∈ fiber v then excess v else 0) (fun _ _ => Nat.zero_le _) (mem_univ v)
      rw [ite_eq_left hv] at one
      have hdeg : (inc v).card ≤ excess v + 1 := by dsimp [excess]; omega
      omega
  have count (S : Finset I) (w : ℕ) : (∑ x, if x ∈ S then w else 0) = S.card*w := by
    rw [← sum_filter]
    simp
  calc
    m*c = ∑ _ : Fin m, c := by simp
    _ ≤ ∑ e, (univ.filter fun x => e ∈ owners x).card := sum_le_sum fun e _ => hcores e
    _ = ∑ x, (owners x).card := by
      simpa [bipartiteBelow, bipartiteAbove] using
        (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (s := (univ : Finset (Fin m))) (t := univ) (fun e x => e ∈ owners x))
    _ ≤ ∑ x, (1 + (if x ∈ roots then m-1 else 0) +
        ∑ v, if x ∈ fiber v then excess v else 0) := sum_le_sum fun x _ => point x
    _ = Fintype.card I + (m-1)*roots.card + ∑ v, (fiber v).card*excess v := by
      simp only [sum_add_distrib]
      rw [count, sum_comm]
      simp_rw [count]
      simp [Nat.mul_comm roots.card (m-1)]
    _ ≤ Fintype.card I + (m-1)*roots.card + ∑ v, d*excess v := by
      exact Nat.add_le_add_left (sum_le_sum fun v _ => Nat.mul_le_mul_right _ (hsize v)) _
    _ ≤ _ := by
      rw [← mul_sum, Nat.mul_comm (2*m-Fintype.card V) d]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ charge) _

/-- The half-rate degree budget gives an integer core cap independent of the
rational quotient degree and of the ambient field. -/
theorem half_rate {c d n r : ℕ} (hcores : 4*c ≤ n+3*r+3*d)
    (hdegree : 2*(r+d+2) ≤ n) : 8*c+12 ≤ 5*n := by omega

/-- At the named length one fresh agreement can only reach 671088639 sites. -/
theorem named {c d r : ℕ} (hcores : 4*c ≤ 1073741824+3*r+3*d)
    (hdegree : r+d+2 ≤ 536870912) : c ≤ 671088638 := by omega

/-- Four heads on six or more endpoints and six arbitrary heads cannot
all be active at the named step. The first count forces degree at most two. -/
theorem six_vertices {r d : ℕ} (hdegree : r+d+2 ≤ 536870912)
    (hfour : 4*671088638 ≤ 1073741824+3*r+2*d)
    (hsix : 6*671088638 ≤ 1073741824+5*r+12*d) : False := by omega

/-- A star's edges can have several owners only at their common vertex
and on the common locator. Six such edges cannot be active at this step. -/
theorem six_star {r d : ℕ} (hdegree : r+d+2 ≤ 536870912)
    (hsix : 6*671088638 ≤ 1073741824+5*(r+d)) : False := by omega

#print axioms select_four
#print axioms select_four_of_disjoint
#print axioms at_most_ten
#print axioms core_charge
#print axioms six_vertices
#print axioms six_star
#print axioms half_rate
#print axioms named
end ProximityGap.SecantGraphIncidence

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothFourHeadAssembly

/-! # The eight site classes in the smooth four-head count -/

open Finset Polynomial ProximityGap
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.SmoothFourHeadColored

/-- Three pair classes, the common roots, three private classes, and the remaining sites. -/
def weight (D G P T : ℕ) : Fin 8 → ℕ := ![D, D, D, G, P, P, P, T]

/-- The triple head received on a site of the indicated class. -/
def owner : Fin 8 → Fin 3 := ![1, 2, 0, 0, 0, 1, 2, 0]

/-- A foreign head at an ordinary triple-owned site. -/
def miss : Fin 8 → Fin 3 := ![0, 1, 2, 0, 1, 2, 0, 0]

def unionClasses : Finset (Fin 8) := {0, 1, 2, 3, 4, 5, 6}
def ordinaryClasses : Finset (Fin 8) := {0, 1, 2, 4, 5, 6}
def coreClasses : Fin 3 → Finset (Fin 8) := ![{1, 2, 3, 4}, {0, 2, 3, 5}, {0, 1, 3, 6}]

variable {F I : Type} [Field F] [Fintype F] [Fintype I] [Nonempty I] [DecidableEq I]

/-- The full numerical four-head mass follows from three degree-bounded seed polynomials
realizing the prescribed pair and singleton classes. -/
theorem mass (dom : I ↪ F) (δ : ℝ≥0) (k D G P T S H : ℕ) (col : I → Fin 8) (seed : Fin 3 → F[X])
    (hcol : ∀ j, (univ.filter (fun x => col x = j)).card = weight D G P T j)
    (hseed : ∀ j, (seed j).natDegree ≤ D)
    (hagree : ∀ x j, col x ∈ coreClasses j → col x ≠ 3 →
      (seed j).eval (dom x) = (seed (owner (col x))).eval (dom x))
    (hmiss : ∀ x, col x ∈ ordinaryClasses → (seed (miss (col x))).eval (dom x) ≠
      (seed (owner (col x))).eval (dom x))
    (hfree : ∀ x, col x = 7 → Function.Injective (fun j => (seed j).eval (dom x)))
    (hdeg : G + D + 1 < k) (hkS : S + 2 ≤ k) (hS : S ≤ G + 3*D + 3*P)
    (hH : H ≤ T) (hkC : k ≤ G + 2*D + P) (hC₄ : G + 2*D + P ≤ S + (T-H))
    (hsize : (1 - δ) * (Fintype.card I : ℝ≥0) ≤ ((G + 2*D + P + 1 : ℕ) : ℝ≥0))
    (hq : 3 * Fintype.card I < Fintype.card F) (h16 : 16 < Fintype.card F)
    (hfield : (3*D+3*P + (G+3*D+3*P-S) + 3*(T-H) + 4*H).choose 2 ≤ Nat.card F) :
    ((3*D+3*P + (G+3*D+3*P-S) + 3*(T-H) + 4*H : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (I → F)) δ := by
  classical
  let select (j : Finset (Fin 8)) := univ.filter (fun x => col x ∈ j)
  have sel_card (j : Finset (Fin 8)) : (select j).card = ∑ i ∈ j, weight D G P T i := by
    rw [← sum_card_fiberwise_eq_card_filter univ j col]
    exact Finset.sum_congr rfl (fun i _ => hcol i)
  have hsel {j t : Finset (Fin 8)} (h : j ⊆ t) : select j ⊆ select t := by
    intro x hx
    exact mem_filter.mpr ⟨mem_univ _, h (mem_filter.mp hx).2⟩
  let U := select unionClasses
  let O := select ordinaryClasses
  let Co (j : Fin 3) := select (coreClasses j)
  let Z := univ.filter fun x => col x = 3
  let J := Lagrange.nodal Z (fun x => dom x)
  have hJ : J.natDegree = G := by
    rw [show J.natDegree = Z.card from Lagrange.natDegree_nodal]
    exact hcol 3
  have hnJ {x : I} (hx : col x ≠ 3) : J.eval (dom x) ≠ 0 := by
    apply Lagrange.eval_nodal_not_at_node
    intro y hy he
    exact hx (dom.injective he ▸ (mem_filter.mp hy).2)
  have ucard : U.card = G + 3*D + 3*P := by
    change (select _).card = _
    rw [sel_card]
    simp [unionClasses, weight]
    omega
  have ocard : O.card = 3*D + 3*P := by
    change (select _).card = _
    rw [sel_card]
    simp [ordinaryClasses, weight]
    omega
  have ccard (j : Fin 3) : (Co j).card = G + 2*D + P := by
    change (select _).card = _
    rw [sel_card]
    fin_cases j <;> simp [coreClasses, weight] <;> omega
  have tcard : Uᶜ.card = T := by
    have he : Uᶜ = univ.filter (fun x => col x = 7) := by
      ext x
      simp only [U, select, mem_compl, mem_filter, mem_univ, true_and]
      generalize col x = z
      fin_cases z <;> decide
    rw [he]
    exact hcol 7
  obtain ⟨shared, hV, hvn⟩ := exists_subset_card_eq (ucard.symm ▸ hS)
  obtain ⟨holes, hHsub, hhn⟩ := exists_subset_card_eq (tcard.symm ▸ hH)
  have hdis : Disjoint U holes := disjoint_left.mpr (fun _ hu hh => mem_compl.mp (hHsub hh) hu)
  let f (j : Fin 3) := J * seed j
  let A : SmoothFourHeadAssembly.Arrangement dom k := {
    f := f, owner := fun x => owner (col x), miss := fun x => miss (col x),
    union := U, ordinary := O, shared := shared, holes := holes, core := Co
    degree := fun j => by
      have hle := natDegree_mul_le (p := J) (q := seed j)
      rw [hJ] at hle
      have := hseed j
      dsimp [f]
      omega
    core_owned := fun j => hsel (by fin_cases j <;> decide)
    agrees := fun j x hx => by
      have hz := (mem_filter.mp hx).2
      by_cases he : col x = 3
      · have hxZ : x ∈ Z := mem_filter.mpr ⟨mem_univ _, he⟩
        have hn : J.eval (dom x) = 0 := Lagrange.eval_nodal_at_node hxZ
        simp [f, hn]
      · simp [f, hagree x j hz he]
    ordinary_owned := hsel (by decide)
    misses := fun x hx => by
      have hclass := (mem_filter.mp hx).2
      have he : col x ≠ 3 := fun he => (by decide : (3 : Fin 8) ∉ ordinaryClasses) (he ▸ hclass)
      simp only [f, eval_mul]
      exact fun h => hmiss x hclass (mul_left_cancel₀ (hnJ he) h)
    shared_owned := hV
    shared_degree := hvn.symm ▸ hkS
    holes_outside := hdis
    outside_distinct := fun x hx => by
      have hclass : col x ∉ unionClasses := fun h => hx (mem_filter.mpr ⟨mem_univ _,h⟩)
      have he : col x = 7 := (by decide : ∀ z : Fin 8, z ∉ unionClasses → z = 7) _ hclass
      intro i j hij
      exact hfree x he (mul_left_cancel₀ (hnJ (he ▸ (by decide : (7 : Fin 8) ≠ 3)))
        (by simpa only [f, eval_mul] using hij)) }
  have hon : A.fourthOnly.card = T-H := by
    change (Uᶜ \ holes).card = _
    rw [card_sdiff_of_subset hHsub, tcard, hhn]
  have hsh : Disjoint shared A.fourthOnly := by
    apply disjoint_left.mpr
    intro x hx h
    exact mem_compl.mp (mem_sdiff.mp h).1 (hV hx)
  have hact : A.count = 3*D+3*P + (G+3*D+3*P-S) + 3*(T-H) + 4*H := by
    change O.card + (U \ shared).card + 3*A.fourthOnly.card + 4*holes.card = _
    rw [ocard, card_sdiff_of_subset hV, ucard, hvn, hon, hhn]
  have hmain := SmoothFourHeadAssembly.mass A δ (G + 2*D + P) (fun j => (ccard j).ge)
    (by change _ ≤ (shared ∪ A.fourthOnly).card; rw [card_union_of_disjoint hsh, hvn, hon]; exact hC₄)
    hkC hsize hq h16 (hact.symm ▸ hfield)
  simpa only [hact] using hmain

end ArkLib.ProximityGap.Frontier.SmoothFourHeadColored

#print axioms ArkLib.ProximityGap.Frontier.SmoothFourHeadColored.mass

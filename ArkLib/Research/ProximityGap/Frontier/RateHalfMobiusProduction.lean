/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize contributors
-/
import ArkLib.Research.ProximityGap.Frontier.MobiusSeamCoordinateSupply
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30

/-! # The six pair intersections and the ordinary-coordinate supply on the first sponsor field -/

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace ProximityGap.RateHalfMobiusProduction

open MobiusSeamCoordinateSupply ArkLib.ProximityGap.PrizeShapePrimeP30 Finset Polynomial

local instance primeFact : Fact P.Prime := ⟨prime_P⟩
abbrev F := ZMod P
abbrev n := 2^30
abbrev k := 2^29
abbrev b := 178956970

/-- The canonical ordering of the subgroup coordinates. -/
def dom : Fin n ↪ F where
  toFun i := g ^ (i : ℕ)
  inj' := by
    intro i j h
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (show (i : ℕ) < orderOf g by rw [orderOf_g]; exact i.isLt)
      (show (j : ℕ) < orderOf g by rw [orderOf_g]; exact j.isLt) h

def H : Finset F := univ.map dom

theorem H_card : H.card = n := by simp [H]
theorem H_pow (x : F) (hx : x ∈ H) : x ^ n = 1 := by
  obtain ⟨i,_,rfl⟩ := mem_map.mp hx
  change (g^(i:ℕ))^n = 1
  have ht : g^n = 1 := by simpa only [orderOf_g] using pow_orderOf_eq_one g
  rw [← pow_mul, Nat.mul_comm, pow_mul, ht, one_pow]

/-- Exponents of the two intersections for each of the three pairs of heads. -/
def exps : Fin 3 → Fin 2 → Fin n := ![![0,1],![3,6],![10,15]]
def rv (i : Fin 3) (h : Fin 2) : F := dom (exps i h)

noncomputable def L (i : Fin 3) : F[X] := (X-C (rv i 0))*(X-C (rv i 1))
private def low (i : Fin 3) : F := rv i 0 * rv i 1
private def mid (i : Fin 3) : F := -(rv i 0 + rv i 1)

def mapOf (i : Fin 3) : Mobius F :=
  let j := i+1
  let h := i+2
  ⟨mid h-mid j, low h-low j, low j-low h, low j*mid h-mid j*low h⟩

def rootPairs (i : Fin 3) : Finset F := {rv i 0, rv i 1}
def Y : Finset F := univ.biUnion rootPairs

def seamValue (i : Fin 3) (j : Fin 2) := (mapOf (i+1)).value (rv i j)
def T : Finset F := univ.image (fun a : Fin 3 × Fin 2 => seamValue a.1 a.2)

/-- Exact field certificates for the three matrices and their six ordered relative maps. -/
theorem matrices_nonsingular : ∀ i, (mapOf i).det ≠ 0 := by decide

theorem relative_coefficients : ∀ i j, i ≠ j → let M := (mapOf i).relative (mapOf j);
    M.a ≠ 0 ∧ M.b ≠ 0 ∧ M.c ≠ 0 := by decide

theorem seam_roots_distinct : Function.Injective (fun a : Fin 3 × Fin 2 => rv a.1 a.2) := by
  change ∀ i j : Fin 3 × Fin 2, rv i.1 i.2 = rv j.1 j.2 → i = j
  decide

theorem seam_directions : ∀ i j, let x := rv i j;
    (mapOf (i+1)).den x ≠ 0 ∧ (mapOf (i+2)).den x ≠ 0 ∧
    (mapOf (i+2)).value x = seamValue i j := by
  have cert : ∀ (i : Fin 3) (j : Fin 2), let x := rv i j; let u := mapOf (i+1); let v := mapOf (i+2);
      u.den x ≠ 0 ∧ v.den x ≠ 0 ∧ v.num x * u.den x = u.num x * v.den x := by decide
  intro i j
  obtain ⟨hu,hv,hc⟩ := cert i j
  exact ⟨hu,hv,(div_eq_div_iff hv hu).mpr hc⟩

theorem seam_values_distinct : Function.Injective (fun a : Fin 3 × Fin 2 => seamValue a.1 a.2) := by
  have cert : ∀ i j : Fin 3 × Fin 2, let x := rv i.1 i.2; let y := rv j.1 j.2;
      let u := mapOf (i.1+1); let v := mapOf (j.1+1);
      u.num x * v.den y = v.num y * u.den x → i = j := by decide
  intro i j hij
  exact cert i j ((div_eq_div_iff (seam_directions i.1 i.2).1 (seam_directions j.1 j.2).1).mp hij)

theorem Y_card : Y.card = 6 := by decide
theorem T_card : T.card = 6 := by
  rw [T, card_image_of_injective _ seam_values_distinct]
  decide

theorem Y_subset : Y ⊆ H := by
  intro x hx
  obtain ⟨i,_,hi⟩ := mem_biUnion.mp hx
  simp only [rootPairs, mem_insert, mem_singleton] at hi
  rcases hi with rfl|rfl
  all_goals exact mem_map.mpr ⟨_, mem_univ _, rfl⟩

/-- Ordinary coordinates at the exact sponsor field and generator. -/
noncomputable def available := ordinary mapOf H Y T

theorem available_card : 677380063 ≤ available.card :=
  ordinary_card prime_P (by decide) mapOf H Y T H_card H_pow Y_card.le T_card.le
    matrices_nonsingular relative_coefficients

theorem available_props :
    (∀ x ∈ available, x ∈ H ∧ x ∉ Y ∧ ∀ i, (mapOf i).den x ≠ 0 ∧ (mapOf i).value x ∉ T) ∧
    (∀ x ∈ available, ∀ y ∈ available, ∀ i j, (mapOf i).value x = (mapOf j).value y →
      i = j ∧ x = y) := ordinary_separation mapOf H Y T H_pow matrices_nonsingular

/-- Ordinary-coordinate assignments for all three heads, mutually disjoint by injectivity. -/
theorem exists_private_coordinates : ∃ f : (Fin 3 × Fin b) ↪ F, ∀ t, f t ∈ available := by
  classical
  have hc : Fintype.card (Fin 3 × Fin b) ≤ Fintype.card (↥available) := by
    simp [Fintype.card_coe]
    exact le_trans (by decide : 3*b ≤ 677380063) available_card
  let f : (Fin 3 × Fin b) ↪ ↥available := Classical.choice (Function.Embedding.nonempty_of_card_le hc)
  exact ⟨f.trans (Function.Embedding.subtype _), fun t => (f t).property⟩

#print axioms available_card
#print axioms available_props
#print axioms seam_directions
#print axioms exists_private_coordinates

/-- Row polynomial for one fractional linear direction. -/
noncomputable def row (u : Mobius F) (j : Fin 2) : F[X] :=
  if j = 0 then C u.a * X + C u.b else C u.c * X + C u.d

/-- Difference of successive source heads before multiplying by the common locator. -/
noncomputable def edge (i : Fin 3) (j : Fin 2) : F[X] := L i * row (mapOf i) j

/-- Both polynomial relations between the quadratic pair locators. -/
theorem edge_sum (j : Fin 2) : edge 0 j + edge 1 j + edge 2 j = 0 := by
  fin_cases j <;>
    norm_num [edge, row, L, mapOf, mid, low, Fin.reduceAdd, map_mul, map_sub, map_neg, map_add] <;>
    ring

noncomputable def V (i : Fin 3) (j : Fin 2) : F[X] := ![0,edge 0 j,edge 0 j+edge 1 j] i

/-- The edge polynomial really is the difference of the indicated pair of heads. -/
theorem edge_difference (i : Fin 3) (j : Fin 2) : V (i+1) j - V i j = edge i j := by
  fin_cases i <;> norm_num [V, Fin.reduceAdd]
  linear_combination -(edge_sum j)

private theorem row_degree (u : Mobius F) (j : Fin 2) : (row u j).natDegree ≤ 1 := by
  have hb (v w : F) : (C v * X + C w).natDegree ≤ 1 := by
    apply (natDegree_add_le _ _).trans
    apply max_le _ (by simp)
    exact natDegree_mul_le.trans (by simp)
  unfold row
  split <;> exact hb _ _

private theorem edge_degree (i : Fin 3) (j : Fin 2) : (edge i j).natDegree ≤ 3 := by
  have hq : (L i).natDegree ≤ 2 := natDegree_mul_le.trans (by simp)
  exact natDegree_mul_le.trans (Nat.add_le_add hq (row_degree _ _))

theorem head_degree (i : Fin 3) (j : Fin 2) : (V i j).natDegree ≤ 3 := by
  fin_cases i
  · change (0 : F[X]).natDegree ≤ 3
    simp
  · exact edge_degree 0 j
  · exact (natDegree_add_le _ _).trans (max_le (edge_degree 0 j) (edge_degree 1 j))

theorem edge_eval_zero_row (i : Fin 3) (x : F) :
    (edge i 0).eval x = (L i).eval x * (mapOf i).num x := by simp [edge,row,Mobius.num]

theorem edge_eval_one_row (i : Fin 3) (x : F) :
    (edge i 1).eval x = (L i).eval x * (mapOf i).den x := by simp [edge,row,Mobius.den]

theorem locator_eval_eq_zero (i : Fin 3) (x : F) : (L i).eval x = 0 ↔ x ∈ rootPairs i := by
  simp [L,rootPairs,sub_eq_zero]

#print axioms edge_sum
#print axioms edge_difference
#print axioms head_degree

end ProximityGap.RateHalfMobiusProduction

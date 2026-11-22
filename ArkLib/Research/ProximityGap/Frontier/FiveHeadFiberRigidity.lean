/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AgreementBounds
import ArkLib.Research.ProximityGap.Frontier.ReservedFiberList

/-! # Five punctured pairs of power fibers force equal Reed–Solomon words

The heads occupy the edges 02, 01, 03, 13 and 23 of a four-vertex graph.
Removing any one fiber still connects the five heads by their shared fibers. -/

namespace ProximityGap.FiveHeadFiberRigidity

open Polynomial Finset

/-- The incident power fibers for each head in the natural binary-index packing. -/
def edge : Fin 5 → Finset (Fin 4) := ![{0, 2}, {0, 1}, {0, 3}, {1, 3}, {2, 3}]

private theorem connected {α : Type*} (a : Fin 4) (v : Fin 5 → α)
    (shared : ∀ i j b, b ≠ a → b ∈ edge i → b ∈ edge j → v i = v j) :
    ∀ i, v i = v 0 := by
  classical
  let S := univ.filter fun i => v i = v 0
  have closed : ∀ i ∈ S, ∀ j b, b ≠ a → b ∈ edge i → b ∈ edge j → j ∈ S := by
    intro i hi j b ha hb hc
    exact mem_filter.mpr ⟨mem_univ _, (shared i j b ha hb hc).symm.trans (mem_filter.mp hi).2⟩
  have all : S = univ := (by decide : ∀ a : Fin 4, ∀ S : Finset (Fin 5), 0 ∈ S →
    (∀ i ∈ S, ∀ j b, b ≠ a → b ∈ edge i → b ∈ edge j → j ∈ S) → S = univ)
    a S (mem_filter.mpr ⟨mem_univ _, rfl⟩) closed
  exact fun i => (mem_filter.mp (all ▸ mem_univ i : i ∈ S)).2

private theorem eq_on_nodes {I F : Type*} [Field F] (D : I ↪ F) (S : Finset I)
    (P Q : F[X]) (hdeg : max P.natDegree Q.natDegree < S.card)
    (hag : ∀ i ∈ S, P.eval (D i) = Q.eval (D i)) : P = Q := by
  apply eq_of_natDegree_lt_card_of_eval_eq P Q
    (D.injective.comp (Subtype.val_injective (p := (· ∈ S))))
  · exact fun i => hag i.val i.property
  · simpa only [Fintype.card_coe] using hdeg

/-- A common received word on the five masks forces all five polynomials to agree.
The four fibers contain at least k sites each. Their union may have up to k erasures. -/
theorem polynomial_eq {I F : Type*} [Field F] (D : I ↪ F) {k : ℕ} (hk : 0 < k)
    (z : Fin 4 ↪ F) (T : Fin 4 → Finset I) (sizes : ∀ j, k ≤ (T j).card)
    (powers : ∀ j x, x ∈ T j → D x ^ k = z j)
    (E : Finset I) (erase : E.card ≤ k) (f : Fin 5 → F[X]) (deg : ∀ i, (f i).natDegree < k)
    (u : I → F) (agree : ∀ i j, j ∈ edge i → ∀ x ∈ T j, x ∉ E → (f i).eval (D x) = u x) :
    ∀ i, f i = f 0 := by
  classical
  let L := Lagrange.nodal E D
  let A (i : Fin 5) := (L * f i) %ₘ (X ^ k)
  let B (i : Fin 5) := (L * f i) /ₘ (X ^ k)
  have split (i : Fin 5) : A i + X ^ k * B i = L * f i := modByMonic_add_div _ _
  have xne : (X ^ k : F[X]) ≠ 1 := by
    intro h
    have bad := congrArg natDegree h
    simp only [natDegree_X_pow, natDegree_one] at bad
    omega
  have smallA (i : Fin 5) : (A i).natDegree < k := by
    simpa only [A, natDegree_X_pow] using natDegree_modByMonic_lt (L * f i) (monic_X_pow k) xne
  have degreeL : L.natDegree = E.card := Lagrange.natDegree_nodal
  have smallB (i : Fin 5) (he : 0 < E.card) : (B i).natDegree < E.card := by
    change ((L * f i) /ₘ (X ^ k)).natDegree < E.card
    rw [natDegree_divByMonic _ (monic_X_pow k), natDegree_X_pow]
    have bound := natDegree_mul_le (p := L) (q := f i)
    rw [degreeL] at bound
    have := deg i
    omega
  have emptyB (i : Fin 5) (he : E = ∅) : B i = 0 := by
    apply (divByMonic_eq_zero_iff (monic_X_pow k)).mpr
    simp only [L, he, Lagrange.nodal, prod_empty, one_mul, degree_X_pow]
    exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr (deg i))
  have boundB (i : Fin 5) : (B i).natDegree < k := by
    rcases E.eq_empty_or_nonempty with he | he
    · simpa only [emptyB i he, natDegree_zero] using hk
    · exact (smallB i he.card_pos).trans_le erase
  let G (i : Fin 5) (j : Fin 4) := A i + C (z j) * B i
  have dg (i : Fin 5) (j : Fin 4) : (G i j).natDegree < k :=
    (natDegree_add_le ..).trans_lt (max_lt (smallA i) ((natDegree_C_mul_le ..).trans_lt (boundB i)))
  have specialize (i : Fin 5) (j : Fin 4) (x : I) (hx : x ∈ T j) :
      (G i j).eval (D x) = (L * f i).eval (D x) := by
    rw [← split i]
    simp [G, powers j x hx]
  have shared (i h : Fin 5) (j : Fin 4) (hi : j ∈ edge i) (hh : j ∈ edge h) :
      G i j = G h j := by
    apply eq_on_nodes D (T j) _ _ ((max_lt (dg i j) (dg h j)).trans_le (sizes j))
    intro x hx
    rw [specialize i j x hx, specialize h j x hx, eval_mul, eval_mul]
    by_cases he : x ∈ E
    · have zero : L.eval (D x) = 0 := Lagrange.eval_nodal_at_node (v := D) he
      simp [zero]
    · rw [agree i j hi x hx he, agree h j hh x hx he]
  have Bnodes (x : I) (hx : x ∈ E) : ∀ i, (B i).eval (D x) = (B 0).eval (D x) := by
    obtain ⟨a, avoid⟩ : ∃ a : Fin 4, ∀ j ≠ a, z j ≠ D x ^ k := by
      by_cases hit : ∃ j, z j = D x ^ k
      · obtain ⟨a, ha⟩ := hit
        exact ⟨a, fun j h eq => h (z.injective (eq.trans ha.symm))⟩
      · exact ⟨0, fun j _ eq => hit ⟨j, eq⟩⟩
    have zero (i : Fin 5) : (A i).eval (D x) + D x ^ k * (B i).eval (D x) = 0 := by
      have fact := congrArg (eval (D x)) (split i)
      simpa only [eval_add, eval_mul, eval_pow, eval_X, Lagrange.eval_nodal_at_node (v := D) hx,
        L, zero_mul] using fact
    apply connected a
    intro i h j hj hi hh
    have eqn := congrArg (eval (D x)) (shared i h j hi hh)
    simp only [G, eval_add, eval_mul, eval_C] at eqn
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr (avoid j hj))
    linear_combination eqn - zero i + zero h
  have Beq (i : Fin 5) : B i = B 0 := by
    rcases E.eq_empty_or_nonempty with he | he
    · rw [emptyB i he, emptyB 0 he]
    · exact eq_on_nodes D E _ _ (max_lt (smallB i he.card_pos) (smallB 0 he.card_pos))
        (fun x hx => Bnodes x hx i)
  have Aeq : ∀ i, A i = A 0 := by
    apply connected 0
    intro i h j _ hi hh
    have eqn := shared i h j hi hh
    simpa only [G, Beq i, Beq h, add_left_inj] using eqn
  intro i
  apply mul_left_cancel₀ (Lagrange.nodal_ne_zero (s := E) (v := D))
  rw [← split i, ← split 0, Aeq i, Beq i]

/-- On the order-4k cyclic domain, site (j,a) has exponent j+4a. Puncturing each
two-fiber mask in up to two places cannot produce five distinct interleaved
codewords near one received word with these masks. In particular k = 2²⁸ is allowed. -/
theorem natural_words_eq {F κ : Type*} [Field F] {k : ℕ} (hk : 10 ≤ k)
    (g : Fˣ) (hg : orderOf g = k * 4) (holes : Fin 5 → Finset (Fin 4 × Fin k))
    (trim : ∀ i, (holes i).card ≤ 2) (w : Fin 5 → Matrix (Fin 4 × Fin k) κ F)
    (words : ∀ i, w i ∈ Code.interleavedCodeSet (κ := κ)
      (ReedSolomon.code (ReservedFiberList.cyclicDomain g hg) k : Set ((Fin 4 × Fin k) → F)))
    (u : (Fin 4 × Fin k) → κ → F)
    (agree : ∀ i x, x.1 ∈ edge i → x ∉ holes i → w i x = u x) :
    ∀ i, w i = w 0 := by
  classical
  have pos : 0 < k := by omega
  let : NeZero k := ⟨by omega⟩
  let D := ReservedFiberList.cyclicDomain g hg
  let T (j : Fin 4) : Finset (Fin 4 × Fin k) := {j} ×ˢ univ
  let E := univ.biUnion holes
  have erase : E.card ≤ k := calc
    E.card ≤ ∑ i ∈ (univ : Finset (Fin 5)), (holes i).card := card_biUnion_le
    _ ≤ ∑ _i ∈ (univ : Finset (Fin 5)), 2 := sum_le_sum (fun i _ => trim i)
    _ ≤ k := by simpa using hk
  have power (j x) (hx : x ∈ T j) :
      D x ^ k = ReservedFiberList.cyclicLabels pos g hg j := by
    have first : x.1 = j := mem_singleton.mp (mem_product.mp hx).1
    simpa only [D, Fintype.card_fin, first] using ReservedFiberList.cyclicDomain_pow pos g hg x
  intro i
  funext x b
  have row (a : Fin 5) := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp (words a b)
  choose f deg eval using row
  have all := polynomial_eq D pos (ReservedFiberList.cyclicLabels pos g hg) T
    (fun j => by simp [T]) power E erase f deg (fun x => u x b) (by
      intro a j hj y hy outside
      have first : y.1 = j := mem_singleton.mp (mem_product.mp hy).1
      have keep : y ∉ holes a := fun hit => outside (mem_biUnion.mpr ⟨a, mem_univ _, hit⟩)
      exact (eval a y).trans (congrFun (agree a y (first ▸ hj) keep) b))
  calc w i x b = (f i).eval (D x) := (eval i x).symm
    _ = (f 0).eval (D x) := congrArg (Polynomial.eval (D x)) (all i)
    _ = w 0 x b := eval 0 x

end ProximityGap.FiveHeadFiberRigidity

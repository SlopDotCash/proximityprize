/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The plane incidence bound: the dimension-2 case from order-2 MDS (#389)

The window-interior δ\* (the proximity-prize core) reduces to the interleaved-list **count** bound
beyond Johnson.  `reedSolomon_genpos_list_bound` handles affinely-*independent* families
unconditionally (Vandermonde MDS); `line_agreement_card_le` (see `LineListBound.lean`) handles the
affinely-*dependent* `affine-dim = 1` (line) slice unconditionally for any code.  This file takes
the next dimension: the `affine-dim = 2` (plane) slice.

In dimension 2 the slice is genuinely **conditional** — if many positions define the *same* line
in parameter space, a whole line's worth (`|F|` points) of parameters becomes heavy, so no
unconditional bound exists.  The exact non-degeneracy that rules this out is **order-2 MDS** of the
`2 × n` generator `[u ; v]`: every two columns independent, `u i · v j ≠ v i · u j` for `i ≠ j`.

`plane_incidence_card_le` proves, *from that order-2 MDS hypothesis alone*, the second-moment
incidence bound

`|Heavy| · C(k,2) ≤ C(n,2)`,  i.e.  `|Heavy| ≤ n(n−1) / (k(k−1))`,

for any set of parameters each agreeing on `≥ k` positions.  This is the dimension-2 instance of
"higher-order MDS ⟹ beyond-Johnson interleaved list decoding": the MDS hypothesis makes every two
position-lines transverse (they meet in one point), so each unordered pair of positions is charged
to at most one heavy parameter, and `∑ C(|fibre|,2) ≤ C(n,2)`.

The open part of the prize core is now sharply isolated: `affine-dim ≥ 2` *without* a clean
order-`d` MDS certificate for the explicit smooth evaluation points — the GM-MDS / higher-order-MDS
question.  Axiom-clean.
-/

open Finset

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [DecidableEq F]

omit [DecidableEq ι] in
/-- **The plane incidence list bound (dim-2 beyond-Johnson, from order-2 MDS).**
Parameterize a 2-dimensional affine family of codewords by `(s,t) ∈ F²`, position `i` agreeing
when `u i · s + v i · t = c i` (here `u = g₁`, `v = g₂`, `c = y − f₀`).  If the column matrix
`[u ; v]` is **order-2 MDS** — every two columns independent, `u i · v j ≠ v i · u j` for `i ≠ j` —
then any set of "heavy" parameters (each agreeing on `≥ k` positions) satisfies
`|Heavy| · C(k,2) ≤ C(n,2)`, i.e. `|Heavy| ≤ n(n−1)/(k(k−1))` (meaningful for `k ≥ 2`).

Mechanism: each position is an affine line in parameter space; order-2 MDS makes any two
position-lines **transverse** (they meet in one point), so each unordered pair of positions is
charged to at most one heavy parameter.  This is the dimension-2 instance of "higher-order MDS ⟹
beyond-Johnson interleaved list decoding", proven unconditionally from the MDS hypothesis. -/
theorem plane_incidence_card_le (u v c : ι → F) {k : ℕ}
    (hmds : ∀ i j, i ≠ j → u i * v j ≠ v i * u j)
    (Heavy : Finset (F × F))
    (hHeavy : ∀ p ∈ Heavy,
      k ≤ (univ.filter (fun i => u i * p.1 + v i * p.2 = c i)).card) :
    Heavy.card * k.choose 2 ≤ (Fintype.card ι).choose 2 := by
  classical
  set S : F × F → Finset ι := fun p => univ.filter (fun i => u i * p.1 + v i * p.2 = c i) with hS
  -- two transverse position-lines meet in at most one parameter
  have huniq : ∀ p p' : F × F, ∀ i j, i ≠ j →
      i ∈ S p → j ∈ S p → i ∈ S p' → j ∈ S p' → p = p' := by
    intro p p' i j hij hip hjp hip' hjp'
    simp only [hS, mem_filter, mem_univ, true_and] at hip hjp hip' hjp'
    have e1 : u i * (p.1 - p'.1) + v i * (p.2 - p'.2) = 0 := by linear_combination hip - hip'
    have e2 : u j * (p.1 - p'.1) + v j * (p.2 - p'.2) = 0 := by linear_combination hjp - hjp'
    have hdet : u i * v j - v i * u j ≠ 0 := sub_ne_zero.mpr (hmds i j hij)
    have hw1 : p.1 - p'.1 = 0 := by
      have h : (u i * v j - v i * u j) * (p.1 - p'.1) = 0 := by
        linear_combination v j * e1 - v i * e2
      exact (mul_eq_zero.mp h).resolve_left hdet
    have hw2 : p.2 - p'.2 = 0 := by
      have h : (u i * v j - v i * u j) * (p.2 - p'.2) = 0 := by
        linear_combination u i * e2 - u j * e1
      exact (mul_eq_zero.mp h).resolve_left hdet
    exact Prod.ext (sub_eq_zero.mp hw1) (sub_eq_zero.mp hw2)
  have htarget : (univ.powersetCard 2 : Finset (Finset ι)).card = (Fintype.card ι).choose 2 := by
    rw [Finset.card_powersetCard, Finset.card_univ]
  have hsig : (Heavy.sigma (fun p => (S p).powersetCard 2)).card
      = ∑ p ∈ Heavy, (S p).card.choose 2 := by
    rw [Finset.card_sigma]
    exact Finset.sum_congr rfl (fun p _ => Finset.card_powersetCard 2 (S p))
  -- charge each (heavy param, pair of agreeing positions) to it; the pair fixes the param
  have hcard_le : (∑ p ∈ Heavy, (S p).card.choose 2) ≤ (Fintype.card ι).choose 2 := by
    rw [← hsig, ← htarget]
    apply Finset.card_le_card_of_injOn (fun x => x.2)
    · rintro ⟨p, s⟩ hps
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_powersetCard, Finset.subset_univ,
        true_and] at hps ⊢
      exact hps.2.2
    · rintro ⟨p, s⟩ hps ⟨p', s'⟩ hps' heq
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_powersetCard] at hps hps'
      have hss : s = s' := heq
      subst hss
      obtain ⟨i, j, hij, hs⟩ := Finset.card_eq_two.mp hps.2.2
      have hmi : i ∈ s := by rw [hs]; exact mem_insert_self i {j}
      have hmj : j ∈ s := by rw [hs]; exact mem_insert_of_mem (mem_singleton_self j)
      have hpp : p = p' :=
        huniq p p' i j hij (hps.2.1 hmi) (hps.2.1 hmj) (hps'.2.1 hmi) (hps'.2.1 hmj)
      subst hpp; rfl
  have hlb : Heavy.card * k.choose 2 ≤ ∑ p ∈ Heavy, (S p).card.choose 2 := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    exact Nat.choose_le_choose 2 (hHeavy p hp)
  exact le_trans hlb hcard_le

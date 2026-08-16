/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvRem_BesselMfold
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvF1_BesselMfoldSymbolic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvX_LamLeungTwoPowerAntipodalBalan

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# `MutuallyDecoupled` (R1) — char-0 Wick made self-contained (#444, avenue CR)

This brick discharges the single named input `_AvF1.MutuallyDecoupled` that the symbolic-`m`
char-0 Bessel `m`-fold factorization (`zeroSumCount_iUnion_eq_natConv`) was reduced to: that each
antipodal direction of `μ_{2m}` is `AdditivelyDecoupled` from the union of the strictly-earlier
directions, with NO cross-direction cancellation.

## The mechanism (the PROVEN Lam–Leung two-power theorem)

`_AvX.antipodal_balance_root`: a vanishing signed sum of `2^μ`-th roots is **antipodally balanced**
— for every value `w`, `#{i : c i = w} = #{i : c i = -w}`.

The decoupling is then a one-line consequence of balance. Both blocks `G` and `H` of the union are
**negation-closed** (a single antipodal direction `{±w}` is, and an arbitrary union of antipodal
directions is). The `G`-block sum is `∑_{w ∈ G} w · #{i : c i = w}`. Group the negation-closed set
`G` into antipodal pairs `{w, -w}`: each pair contributes `w·#{c=w} + (-w)·#{c=-w}`, which is `0`
by balance. Hence the `G`-block (and symmetrically the `H`-block) **independently** sums to `0`.
No appeal to which direction a root sits in is needed beyond the block being negation-closed — that
is exactly why distinct antipodal directions cannot cross-cancel.

## What is FORMALIZED here (axiom-clean, no `sorry`)

1. **`block_sum_zero_of_balanced`** — the linear-algebra core: over a negation-closed value set `S`,
   if a tuple is antipodally balanced (`#{c=w} = #{c=-w}` ∀w), then `∑_{i : c i ∈ S} c i = 0`.
2. **`additivelyDecoupled_of_negClosed`** — for two disjoint negation-closed sets of `2^μ`-th roots,
   `AdditivelyDecoupled G H` holds. (The reverse direction of `separates` is trivial — block sums
   add to the total.)
3. **`unionUpto_negClosed`** — an arbitrary running union of negation-closed directions is
   negation-closed.
4. **`mutuallyDecoupled_of_antipodalDirections`** — **THE TARGET**: a family of negation-closed
   directions, each consisting of `2^μ`-th roots, pairwise disjoint, is `MutuallyDecoupled`. This is
   the exact Lam–Leung input `_AvF1` named, now PROVEN, making the char-0 Wick chain self-contained
   modulo only the symbolic-`d` numeric bridge `natConv negDirCount d (2r) = Edef r d` (R2).

## Honest scope (#444)

This LANDS R1 (`MutuallyDecoupled`) axiom-clean from the proven Lam–Leung two-power theorem, for the
clean and exactly-applicable hypothesis "each direction is negation-closed, disjoint, of `2^μ`-th
roots". For `μ_{2m}` the `m` antipodal directions `P_j = {ζ^j, -ζ^j}` satisfy this verbatim. It is a
char-0 brick (the prize is char-`p`, where wraparound excess `W_r` breaks the EGF off a finite
bad-prime set); the remaining R2 symbolic-`d` bridge is the only residual left in the char-0 chain.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset
open ArkLib.ProximityGap.NegationClosedWalk
open ArkLib.ProximityGap.Frontier.AvRem
open ArkLib.ProximityGap.Frontier.AvF1

namespace ArkLib.ProximityGap.Frontier.AvCR

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]

/-- A value set is **negation-closed** when it is closed under `w ↦ -w`. A single antipodal
direction `{±w}` is, and so is any union of them. -/
def NegClosed (S : Finset F) : Prop := ∀ w ∈ S, -w ∈ S

/-! ## The linear-algebra core: a balanced tuple has every negation-closed block sum to `0`. -/

/-- **The decoupling core.** Let `c : Fin N → F` be a tuple that is *antipodally balanced*: for every
value `w`, `#{i : c i = w} = #{i : c i = -w}`. Then for any negation-closed value set `S`, the block
sum over the positions landing in `S` vanishes:
`∑_{i : c i ∈ S} c i = 0`.

Proof: regroup the block sum by value, `∑_{i : c i ∈ S} c i = ∑_{w ∈ S} w · #{i : c i = w}`. Pair the
negation-closed `S` under `w ↦ -w`; the orbit `{w, -w}` contributes `w·#{c=w} + (-w)·#{c=-w} = 0` by
balance. Formally we show the sum equals its own negation (via the negation involution on `S`),
forcing it to `0`. -/
theorem block_sum_zero_of_balanced {N : ℕ} (c : Fin N → F) (S : Finset F)
    (hS : NegClosed S)
    (hbal : ∀ w : F, (univ.filter (fun i => c i = w)).card
                   = (univ.filter (fun i => c i = -w)).card) :
    ∑ i ∈ univ.filter (fun i => c i ∈ S), c i = 0 := by
  classical
  set B : Finset (Fin N) := univ.filter (fun i => c i ∈ S) with hB
  -- Step 1: regroup the block sum by value over `S` (fiberwise on `c`).
  have hmaps : ∀ i ∈ B, c i ∈ S := by
    intro i hi; rw [hB, Finset.mem_filter] at hi; exact hi.2
  have hgroup : ∑ i ∈ B, c i
      = ∑ w ∈ S, ∑ i ∈ B.filter (fun i => c i = w), c i :=
    (Finset.sum_fiberwise_of_maps_to hmaps c).symm
  -- inner fiber sum is `(#fiber) • w`, and the fiber equals the global value-fiber (since `w ∈ S`).
  have hinner : ∀ w ∈ S, ∑ i ∈ B.filter (fun i => c i = w), c i
      = (univ.filter (fun i => c i = w)).card • w := by
    intro w hw
    have hfeq : B.filter (fun i => c i = w) = univ.filter (fun i => c i = w) := by
      ext i
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨by rw [h]; exact hw, h⟩
    rw [hfeq]
    rw [Finset.sum_congr rfl (g := fun _ => w) (by intro i hi; exact (Finset.mem_filter.mp hi).2)]
    rw [Finset.sum_const]
  rw [hgroup, Finset.sum_congr rfl hinner]
  -- Step 2: the value-sum `F(w) := (#{c=w}) • w` over negation-closed `S` is its own negation.
  -- Pair `w ↦ -w`: `F(-w) = (#{c=-w}) • (-w) = (#{c=w}) • (-w) = -(F w)` using balance.
  set F' : F → F := fun w => (univ.filter (fun i => c i = w)).card • w with hF'
  have hnegmap : ∀ w ∈ S, F' (-w) = - F' w := by
    intro w hw
    simp only [hF']
    rw [← hbal w, neg_nsmul] -- #{c=-w}=#{c=w}; (#)•(-w) = -((#)•w)
  -- `∑_{w∈S} F' w`: apply the negation involution on `S` to get the sum equals its negation.
  have hinvol : ∑ w ∈ S, F' w = ∑ w ∈ S, F' (-w) := by
    apply Finset.sum_nbij' (i := fun w => -w) (j := fun w => -w)
    · intro w hw; exact hS w hw
    · intro w hw; exact hS w hw
    · intro w hw; simp
    · intro w hw; simp
    · intro w hw; simp
  have hsumneg : ∑ w ∈ S, F' w = - ∑ w ∈ S, F' w := by
    calc ∑ w ∈ S, F' w = ∑ w ∈ S, F' (-w) := hinvol
      _ = ∑ w ∈ S, - F' w := Finset.sum_congr rfl hnegmap
      _ = - ∑ w ∈ S, F' w := by rw [Finset.sum_neg_distrib]
  -- a value equal to its own negation is 0.
  have hzero : ∑ w ∈ S, F' w = 0 := by
    have h2 : (∑ w ∈ S, F' w) + (∑ w ∈ S, F' w) = 0 := by
      nth_rewrite 2 [hsumneg]; rw [add_neg_cancel]
    have htwo : (2 : F) * (∑ w ∈ S, F' w) = 0 := by rw [two_mul]; exact h2
    rcases mul_eq_zero.mp htwo with h | h
    · exact absurd h two_ne_zero
    · exact h
  exact hzero

/-! ## From balance to `AdditivelyDecoupled` for negation-closed root directions. -/

/-- **Two disjoint negation-closed sets of `2^k`-th roots are `AdditivelyDecoupled`.** The forward
("zero-sum ⟹ each block zero-sum") direction is `block_sum_zero_of_balanced` applied to each block,
fed by Lam–Leung antipodal balance (`_AvX.antipodal_balance_root`). The reverse is trivial: the two
block sums are exactly the two halves of the total (every position is in `G` or in `H`, disjointly),
so if each vanishes the total does. -/
theorem additivelyDecoupled_of_negClosed {k : ℕ} (G H : Finset F)
    (hGc : NegClosed G) (hHc : NegClosed H) (hdisj : Disjoint G H)
    (hroot : ∀ x ∈ G ∪ H, x ^ (2 ^ k) = 1) :
    AdditivelyDecoupled G H := by
  classical
  refine ⟨hdisj, ?_⟩
  intro N c hmem
  constructor
  · -- zero-sum ⟹ each block zero-sum, via antipodal balance
    intro hsum
    have hcroot : ∀ i, (c i) ^ (2 ^ k) = 1 := fun i => hroot (c i) (hmem i)
    have hbal := LamLeungTwoPowerAntipodalBalance.antipodal_balance_root c hcroot hsum
    exact ⟨block_sum_zero_of_balanced c G hGc hbal,
           block_sum_zero_of_balanced c H hHc hbal⟩
  · -- each block zero-sum ⟹ total zero-sum (the two filters partition `univ`)
    rintro ⟨hG, hH⟩
    have hpart : ∑ i, c i
        = (∑ i ∈ univ.filter (fun i => c i ∈ G), c i)
            + (∑ i ∈ univ.filter (fun i => c i ∈ H), c i) := by
      rw [← Finset.sum_filter_add_sum_filter_not univ (fun i => c i ∈ G)]
      congr 1
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hiNG
        rcases Finset.mem_union.mp (hmem i) with hg | hh
        · exact absurd hg hiNG
        · exact hh
      · intro hiH hiG
        exact (Finset.disjoint_left.mp hdisj hiG) hiH
    rw [hpart, hG, hH, add_zero]

/-! ## Negation-closure of antipodal pairs and their running unions. -/

omit [CharZero F] in
/-- A single antipodal direction `{w, -w}` is negation-closed. -/
theorem negClosed_antipodalPair (w : F) : NegClosed ({w, -w} : Finset F) := by
  intro x hx
  rw [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · simp
  · simp

omit [DecidableEq F] [CharZero F] in
/-- The empty set is negation-closed. -/
theorem negClosed_empty : NegClosed (∅ : Finset F) := by
  intro x hx; exact absurd hx (Finset.notMem_empty x)

omit [CharZero F] in
/-- The union of two negation-closed sets is negation-closed. -/
theorem negClosed_union {G H : Finset F} (hG : NegClosed G) (hH : NegClosed H) :
    NegClosed (G ∪ H) := by
  intro x hx
  rcases Finset.mem_union.mp hx with h | h
  · exact Finset.mem_union_left _ (hG x h)
  · exact Finset.mem_union_right _ (hH x h)

omit [CharZero F] in
/-- **A running union of negation-closed directions is negation-closed.** -/
theorem unionUpto_negClosed {d : ℕ} (D : Fin d → Finset F)
    (hD : ∀ j : Fin d, NegClosed (D j)) :
    ∀ k : ℕ, NegClosed (unionUpto D k)
  | 0 => by simpa [unionUpto] using (negClosed_empty (F := F))
  | k + 1 => by
      simp only [unionUpto]
      by_cases h : k < d
      · rw [dif_pos h]
        exact negClosed_union (unionUpto_negClosed D hD k) (hD ⟨k, h⟩)
      · rw [dif_neg h]
        simpa using negClosed_union (unionUpto_negClosed D hD k) (negClosed_empty (F := F))

/-! ## THE TARGET: `MutuallyDecoupled` for the antipodal directions of `μ_{2m}`. -/

/-- **R1, PROVEN.** A family `D` of pairwise-disjoint negation-closed directions, every element of
which is a `2^k`-th root of unity, is `MutuallyDecoupled` (each direction is `AdditivelyDecoupled`
from the union of the strictly-earlier ones). For `μ_{2m}` the `m` antipodal directions
`P_j = {ζ^j, -ζ^j}` satisfy these three hypotheses verbatim (negation-closed by
`negClosed_antipodalPair`, disjoint as distinct cosets of `{±1}`, all `2^μ`-th roots), so this
discharges exactly the `_AvF1.MutuallyDecoupled` input the symbolic-`m` char-0 Bessel factorization
was reduced to.

Mechanism: each `unionUpto D k` is negation-closed (`unionUpto_negClosed`) and disjoint from
`D ⟨k,h⟩` (the directions are pairwise disjoint), and all roots are `2^k`-th roots; so
`additivelyDecoupled_of_negClosed` applies — the Lam–Leung antipodal balance forces the per-direction
split. -/
theorem mutuallyDecoupled_of_antipodalDirections {k d : ℕ} (D : Fin d → Finset F)
    (hNC : ∀ j : Fin d, NegClosed (D j))
    (hdisj : ∀ i j : Fin d, i ≠ j → Disjoint (D i) (D j))
    (hroot : ∀ (j : Fin d), ∀ x ∈ D j, x ^ (2 ^ k) = 1) :
    MutuallyDecoupled D := by
  classical
  intro m hm
  -- The earlier union is negation-closed.
  have hUc : NegClosed (unionUpto D m) := unionUpto_negClosed D hNC m
  -- `unionUpto D m` is disjoint from `D ⟨m, hm⟩`: it is a union of earlier directions, each disjoint.
  have hUdisj : Disjoint (unionUpto D m) (D ⟨m, hm⟩) := by
    -- prove by induction that `unionUpto D k` (k ≤ m) is disjoint from `D ⟨m,hm⟩` when k ≤ m
    have key : ∀ kk : ℕ, kk ≤ m → Disjoint (unionUpto D kk) (D ⟨m, hm⟩) := by
      intro kk
      induction kk with
      | zero => intro _; simp [unionUpto]
      | succ j ihj =>
          intro hj
          have hjm : j < m := hj
          have hjd : j < d := lt_trans hjm hm
          simp only [unionUpto, dif_pos hjd]
          apply Finset.disjoint_union_left.mpr
          refine ⟨ihj (Nat.le_of_lt hjm), ?_⟩
          apply hdisj ⟨j, hjd⟩ ⟨m, hm⟩
          intro hcontra
          have : j = m := congrArg Fin.val hcontra
          omega
    exact key m (le_refl m)
  -- all elements of the union ∪ direction are `2^k`-th roots.
  have hUroot : ∀ x ∈ (unionUpto D m) ∪ D ⟨m, hm⟩, x ^ (2 ^ k) = 1 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxU | hxD
    · -- x in an earlier union; induct to find its host direction
      have hin : ∀ kk : ℕ, x ∈ unionUpto D kk → x ^ (2 ^ k) = 1 := by
        intro kk
        induction kk with
        | zero => intro h; exact absurd h (by simp [unionUpto])
        | succ j ihj =>
            intro h
            simp only [unionUpto] at h
            by_cases hjd : j < d
            · rw [dif_pos hjd] at h
              rcases Finset.mem_union.mp h with h1 | h2
              · exact ihj h1
              · exact hroot ⟨j, hjd⟩ x h2
            · rw [dif_neg hjd] at h
              simp only [Finset.union_empty] at h
              exact ihj h
      exact hin m hxU
    · exact hroot ⟨m, hm⟩ x hxD
  exact additivelyDecoupled_of_negClosed (unionUpto D m) (D ⟨m, hm⟩) hUc (hNC ⟨m, hm⟩) hUdisj hUroot

#print axioms block_sum_zero_of_balanced
#print axioms additivelyDecoupled_of_negClosed
#print axioms unionUpto_negClosed
#print axioms mutuallyDecoupled_of_antipodalDirections

end ArkLib.ProximityGap.Frontier.AvCR

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment

/-!
# The universal diagonal floor for the `r`-fold additive energy (#444, #389)

The in-tree `rEnergy G r = #{(v,w) ∈ (Fin r → G)² : ∑v = ∑w}` is the `r`-fold additive energy
(`SubgroupGaussSumMoment`), equal to the `2r`-th Gauss-sum moment `(1/q)·∑_b ‖η_b‖^{2r}`.  Every
exact char-0 closed form in the campaign (the `E_r = …` ladder, `r=2,…,9`) is a *value* that holds
only under a near-Sidon / `2^n < p` hypothesis.  This file records the one bound that needs **no**
hypothesis at all and holds for **every** `r`:

> **`rEnergy_ge_card_pow`.**  `rEnergy G r ≥ |G|^r`, for any finite `G` and any `r`.

The mechanism is the **diagonal** `w = v`: for each `v ∈ (Fin r → G)` the term `w = v` contributes
`1` to the inner indicator sum (since `∑ v = ∑ v`), so the inner sum is `≥ 1`, and summing the
constant `1` over the `|G|^r` choices of `v` gives `|G|^r`.  This is the `r`-fold generalization of
`E2CharFree.E2_ge_card_sq` (`r=2`), and the universal FLOOR beneath the entire moment ladder: it is
char-free, hypothesis-free, and sharp at `r=0,1` (where it is the exact value).

Axiom-clean (`propext, Classical.choice, Quot.sound`).  No CORE closure, no char-p transfer, no
capacity / beyond-Johnson / growth-law claim.  Issues #444, #389.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The universal diagonal floor.**  `rEnergy G r ≥ |G|^r` for any finite set `G` and any `r`,
via the diagonal `w = v` (hypothesis-free, char-free).  This is the floor beneath the entire
char-0 moment ladder `E_r = …`, generalizing `E2CharFree.E2_ge_card_sq`. -/
theorem rEnergy_ge_card_pow (G : Finset F) (r : ℕ) :
    G.card ^ r ≤ rEnergy G r := by
  classical
  unfold rEnergy
  -- The diagonal term `w = v` contributes `1` to each inner sum, so the inner sum is `≥ 1`.
  have hinner : ∀ v ∈ Fintype.piFinset (fun _ : Fin r => G),
      (1 : ℕ) ≤ ∑ w ∈ Fintype.piFinset (fun _ : Fin r => G),
        (if ∑ i, v i = ∑ i, w i then 1 else 0) := by
    intro v hv
    -- single out `w = v`: its summand is `1`.
    calc (1 : ℕ)
        = (if ∑ i, v i = ∑ i, v i then 1 else 0) := by simp
      _ ≤ ∑ w ∈ Fintype.piFinset (fun _ : Fin r => G),
            (if ∑ i, v i = ∑ i, w i then 1 else 0) :=
            Finset.single_le_sum (f := fun w => if ∑ i, v i = ∑ i, w i then (1 : ℕ) else 0)
              (fun w _ => by positivity) hv
  -- Sum the inner lower bound `1` over the `|G|^r` choices of `v`.
  calc G.card ^ r
      = ∑ _v ∈ Fintype.piFinset (fun _ : Fin r => G), (1 : ℕ) := by
        rw [Finset.sum_const, Fintype.card_piFinset]
        simp [Finset.prod_const, Finset.card_univ]
    _ ≤ ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G),
          ∑ w ∈ Fintype.piFinset (fun _ : Fin r => G),
            (if ∑ i, v i = ∑ i, w i then 1 else 0) :=
        Finset.sum_le_sum hinner

/-- The floor is **sharp at `r = 0`**: `rEnergy G 0 = 1 = |G|^0`.  There is a unique empty tuple
`(Fin 0 → G)`, and its (empty) sum equals itself. -/
theorem rEnergy_zero (G : Finset F) : rEnergy G 0 = 1 := by
  classical
  unfold rEnergy
  simp

/-- The floor is **sharp at `r = 1`**: `rEnergy G 1 ≤ |G|` (hence `= |G|` with the floor).  At
`r = 1` the energy counts pairs with `∑_{i:Fin 1} v i = ∑_{i:Fin 1} w i`, i.e. `v 0 = w 0`; for
each `v` the inner sum picks out exactly the single `w` with `w 0 = v 0`, contributing `1`. -/
theorem rEnergy_one_le (G : Finset F) : rEnergy G 1 ≤ G.card := by
  classical
  unfold rEnergy
  -- bound each inner sum by 1: at most one `w` (namely `w 0 = v 0`) satisfies the indicator.
  have hinner : ∀ v ∈ Fintype.piFinset (fun _ : Fin 1 => G),
      (∑ w ∈ Fintype.piFinset (fun _ : Fin 1 => G),
        (if ∑ i, v i = ∑ i, w i then 1 else 0)) ≤ 1 := by
    intro v _
    -- rewrite the indicator sum as the card of the filtered set
    rw [← Finset.card_filter]
    -- the filtered set has at most one element: `w ↦ w 0` is determined as `v 0`
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [Finset.mem_filter, Fin.sum_univ_one] at ha hb
    funext i; fin_cases i; exact ha.2.symm.trans hb.2
  calc (∑ v ∈ Fintype.piFinset (fun _ : Fin 1 => G),
          ∑ w ∈ Fintype.piFinset (fun _ : Fin 1 => G),
            (if ∑ i, v i = ∑ i, w i then 1 else 0))
      ≤ ∑ _v ∈ Fintype.piFinset (fun _ : Fin 1 => G), (1 : ℕ) := Finset.sum_le_sum hinner
    _ = G.card := by
        rw [Finset.sum_const, Fintype.card_piFinset]
        simp [Finset.prod_const, Finset.card_univ]

/-- **The floor is exactly attained at `r = 1`**: `rEnergy G 1 = |G|`.  Combines the universal
floor `rEnergy_ge_card_pow` (at `r = 1`, `|G|^1 = |G|`) with `rEnergy_one_le`. -/
theorem rEnergy_one (G : Finset F) : rEnergy G 1 = G.card := by
  refine le_antisymm (rEnergy_one_le G) ?_
  have h := rEnergy_ge_card_pow G 1
  simpa using h

end ArkLib.ProximityGap.SubgroupGaussSumMoment

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only (no sorryAx).
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy_ge_card_pow
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy_zero
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy_one_le
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy_one

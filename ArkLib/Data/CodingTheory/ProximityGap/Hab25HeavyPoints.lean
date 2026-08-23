/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! # Heavy-point selection: the Claim 5.11 double count (BCIKS20 §5 Step 7, #302 K4-prep)

The Guruswami–Sudan endgame of [BCIKS20] §5 (Steps 7–8, packaged there as Claim 5.11)
selects `k + 1` "heavy" evaluation points: coordinates `x` of the domain at which *many*
scalars `z ∈ S'` agree (`w(x, z) = P_z(x)`). At a heavy point two distinct agreeing scalars
pin the affine data `(v₀ x, v₁ x)` (a `2 × 2` Vandermonde solve), and `k + 1` pinned points
determine the degree-`k` interpolant — the entry into the Claim 5.9 `Z`-linearity assembly
`γ(x) = u₀(x) + Z·u₁(x)`.

This file proves the *combinatorial core* of that selection, in a reusable generic form, plus
the two-point Vandermonde brick.

## Main results

* `card_heavy_ge_of_sum_ge` — **the selection lemma.** For `f : ι → ℕ` with `f x ≤ S` and
  `Σ_x f x ≥ (n − e)·S` (`n := |ι|`): if `(n − k)·m < (n − e − k)·S` then at least `k + 1`
  coordinates satisfy `f x > m`. Proof: if at most `k` coordinates were heavy, then
  `Σ f ≤ k·S + (n − k)·m`, forcing `(n − e − k)·S ≤ (n − k)·m`.
* `sum_good_card_ge` — **the double-count feeder.** If for every `z ∈ S'` the set of bad
  coordinates `{x : Bad x z}` has card `≤ e` (the per-`z` agreement bound `|D_z| ≥ n − e`),
  then `Σ_x |S'_x| ≥ (n − e)·|S'|`, where `S'_x := {z ∈ S' : ¬ Bad x z}`. (Fubini on the
  good-pair indicator.)
* `card_heavy_points_ge` / `exists_heavy_subset` — **Claim 5.11 packaged**: combining the
  two, under `(n − k)·m < (n − e − k)·|S'|` there are `≥ k + 1` coordinates `x` with
  `|S'_x| > m` — and a `(k+1)`-subset of them.
* `affine_eq_of_two_points` / `affine_eq_of_two_scalars` — **the 2×2 Vandermonde brick**
  (Step 8 entry): two distinct scalars satisfying `v₀ + z·v₁ = u₀ + z·u₁` force
  `v₀ = u₀ ∧ v₁ = u₁`.
* `exists_pinned_points` — the composite Step-7→Step-8 hand-off: per-`z` bad-card `≤ e` and
  the `m = 1` gap inequality `n − k < (n − e − k)·|S'|` produce `k + 1` coordinates where
  the affine data is fully pinned.

Everything is `Finset`/ℕ combinatorics over an abstract coordinate type; no code or
polynomial structure is assumed, so the lemmas serve any instantiation of the §5 endgame
(the `Hab25K4*` cell-capture chain, and the Claim 5.9 assembly).

## References

* [BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, Shubhangi Saraf,
  *Proximity Gaps for Reed–Solomon Codes*, ePrint 2020/654 — §5 Steps 7–8, Claim 5.11.
* [Hab25] Ulrich Haböck, *A note on mutual correlated agreement for Reed–Solomon codes*,
  ePrint 2025/2110 — §3 (the mutual-CA generalization consuming the same endgame).
-/

namespace CodingTheory.ProximityGap.Hab25HeavyPoints

open Finset

variable {ι α : Type*} [Fintype ι]

/-! ## The selection lemma (generic threshold counting) -/

/-- **Heavy-point selection (BCIKS20 Claim 5.11, counting core).** Let `f : ι → ℕ` with
`f x ≤ S` for all `x` (think `f x = |S'_x|`, `S = |S'|`) and total mass
`Σ_x f x ≥ (n − e)·S` (the double-counted agreement supply). If the *gap inequality*

  `(n − k)·m < (n − e − k)·S`

holds, then **at least `k + 1` coordinates are `m`-heavy**: `|{x : f x > m}| ≥ k + 1`.

Contrapositive double count: were at most `k` coordinates heavy, then
`Σ f ≤ (#heavy)·S + (#light)·m ≤ k·S + (n − k)·m`, which with the supply bound forces
`(n − e − k)·S ≤ (n − k)·m` — contradicting the gap inequality. (The gap inequality also
silently forces `e + k < n` and `m < S`, which the proof extracts rather than assumes.) -/
theorem card_heavy_ge_of_sum_ge (f : ι → ℕ) (S e k m : ℕ)
    (hub : ∀ x, f x ≤ S)
    (hsum : (Fintype.card ι - e) * S ≤ ∑ x, f x)
    (hgap : (Fintype.card ι - k) * m < (Fintype.card ι - e - k) * S) :
    k + 1 ≤ (univ.filter (fun x => m < f x)).card := by
  classical
  set n := Fintype.card ι with hn
  -- the gap inequality forces `e + k < n` and `m < S`
  have hek : e + k < n := by
    by_contra h
    push Not at h
    have h0 : n - e - k = 0 := by omega
    rw [h0, zero_mul] at hgap
    exact Nat.not_lt_zero _ hgap
  have hmS : m < S := by
    by_contra h
    push Not at h
    exact absurd hgap (not_lt.mpr (Nat.mul_le_mul (by omega : n - e - k ≤ n - k) h))
  by_contra hcon
  push Not at hcon
  set H := (univ.filter (fun x => m < f x)).card with hH
  -- subtraction-free decomposition: `n = a + e + k`, `k = H + d`
  obtain ⟨a, hna⟩ : ∃ a, n = a + e + k := ⟨n - e - k, by omega⟩
  obtain ⟨d, hkd⟩ : ∃ d, k = H + d := ⟨k - H, by omega⟩
  -- split the total mass over heavy/light coordinates
  have hsplit : ∑ x ∈ univ.filter (fun x => m < f x), f x
      + ∑ x ∈ univ.filter (fun x => ¬ m < f x), f x = ∑ x, f x :=
    Finset.sum_filter_add_sum_filter_not univ _ f
  have hheavy : ∑ x ∈ univ.filter (fun x => m < f x), f x ≤ H * S := by
    calc ∑ x ∈ univ.filter (fun x => m < f x), f x
        ≤ ∑ _x ∈ univ.filter (fun x => m < f x), S :=
          Finset.sum_le_sum (fun x _ => hub x)
      _ = H * S := by rw [Finset.sum_const, smul_eq_mul]
  have hlight_card : (univ.filter (fun x => ¬ m < f x)).card = n - H := by
    have hsplitc := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset ι)) (fun x => m < f x)
    have hc : (univ : Finset ι).card = Fintype.card ι := Finset.card_univ
    omega
  have hlight : ∑ x ∈ univ.filter (fun x => ¬ m < f x), f x ≤ (n - H) * m := by
    calc ∑ x ∈ univ.filter (fun x => ¬ m < f x), f x
        ≤ ∑ _x ∈ univ.filter (fun x => ¬ m < f x), m :=
          Finset.sum_le_sum (fun x hx => by
            have hxm := (Finset.mem_filter.mp hx).2
            omega)
      _ = (n - H) * m := by rw [Finset.sum_const, smul_eq_mul, hlight_card]
  -- combine: `(n−e)·S ≤ H·S + (n−H)·m`
  have hmain : (n - e) * S ≤ H * S + (n - H) * m :=
    le_trans hsum (le_trans (le_of_eq hsplit.symm) (Nat.add_le_add hheavy hlight))
  -- rewrite all truncated subtractions via the decomposition
  have hsub1 : n - e = a + (H + d) := by omega
  have hsub2 : n - H = a + e + d := by omega
  have hsub3 : n - k = a + e := by omega
  have hsub4 : n - e - k = a := by omega
  rw [hsub1, hsub2] at hmain
  rw [hsub3, hsub4] at hgap
  -- pure subtraction-free arithmetic: cancel `H·S`, then `d·S`, contradict `hgap`
  have h4 : H * S + (a * S + d * S) ≤ H * S + (a * m + e * m + d * m) := by
    calc H * S + (a * S + d * S) = (a + (H + d)) * S := by ring
      _ ≤ H * S + (a + e + d) * m := hmain
      _ = H * S + (a * m + e * m + d * m) := by ring
  have h5 : a * S + d * S ≤ a * m + e * m + d * m := le_of_add_le_add_left h4
  have h6 : a * m + e * m < a * S := by
    calc a * m + e * m = (a + e) * m := by ring
      _ < a * S := hgap
  have h7 : d * m ≤ d * S := Nat.mul_le_mul_left d hmS.le
  have h8 : a * S + d * S ≤ (a * m + e * m) + d * S :=
    le_trans h5 (Nat.add_le_add_left h7 _)
  exact absurd h6 (not_lt.mpr (le_of_add_le_add_right h8))

/-! ## The double-count feeder (per-`z` agreement to total mass) -/

/-- **Double-count feeder.** If for every scalar `z ∈ S'` the bad set `{x : Bad x z}` has
card `≤ e` (i.e. each `z` agrees on `≥ n − e` coordinates), then the total good-pair count
satisfies `Σ_x |S'_x| ≥ (n − e)·|S'|`, where `S'_x := {z ∈ S' : ¬ Bad x z}`.

Fubini over the good-pair indicator: `Σ_x |S'_x| = Σ_{z ∈ S'} |{x : ¬ Bad x z}|`, and each
inner count is `n − |{x : Bad x z}| ≥ n − e`. -/
theorem sum_good_card_ge (Bad : ι → α → Prop) [∀ x z, Decidable (Bad x z)]
    (S' : Finset α) (e : ℕ)
    (hbad : ∀ z ∈ S', (univ.filter (fun x => Bad x z)).card ≤ e) :
    (Fintype.card ι - e) * S'.card
      ≤ ∑ x : ι, (S'.filter (fun z => ¬ Bad x z)).card := by
  classical
  have hswap : ∑ x : ι, (S'.filter (fun z => ¬ Bad x z)).card
      = ∑ z ∈ S', (univ.filter (fun x => ¬ Bad x z)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hgood : ∀ z ∈ S',
      Fintype.card ι - e ≤ (univ.filter (fun x => ¬ Bad x z)).card := by
    intro z hz
    have hsplitc := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset ι)) (fun x => Bad x z)
    have hc : (univ : Finset ι).card = Fintype.card ι := Finset.card_univ
    have hb := hbad z hz
    omega
  calc (Fintype.card ι - e) * S'.card
      = ∑ _z ∈ S', (Fintype.card ι - e) := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ z ∈ S', (univ.filter (fun x => ¬ Bad x z)).card := Finset.sum_le_sum hgood
    _ = ∑ x : ι, (S'.filter (fun z => ¬ Bad x z)).card := hswap.symm

/-! ## Claim 5.11 packaged: heavy points from per-`z` agreement -/

/-- **BCIKS20 Claim 5.11 (heavy-point count).** Per-`z` bad-card `≤ e` plus the gap
inequality `(n − k)·m < (n − e − k)·|S'|` give at least `k + 1` coordinates `x` with
`|S'_x| > m` (`S'_x := {z ∈ S' : ¬ Bad x z}`). -/
theorem card_heavy_points_ge (Bad : ι → α → Prop) [∀ x z, Decidable (Bad x z)]
    (S' : Finset α) (e k m : ℕ)
    (hbad : ∀ z ∈ S', (univ.filter (fun x => Bad x z)).card ≤ e)
    (hgap : (Fintype.card ι - k) * m < (Fintype.card ι - e - k) * S'.card) :
    k + 1 ≤ (univ.filter
      (fun x => m < (S'.filter (fun z => ¬ Bad x z)).card)).card :=
  card_heavy_ge_of_sum_ge (fun x => (S'.filter (fun z => ¬ Bad x z)).card)
    S'.card e k m (fun _ => Finset.card_filter_le _ _)
    (sum_good_card_ge Bad S' e hbad) hgap

/-- **BCIKS20 Claim 5.11 (selection form).** Under the same hypotheses, a `(k+1)`-element
set of coordinates each of which is `m`-heavy. -/
theorem exists_heavy_subset (Bad : ι → α → Prop) [∀ x z, Decidable (Bad x z)]
    (S' : Finset α) (e k m : ℕ)
    (hbad : ∀ z ∈ S', (univ.filter (fun x => Bad x z)).card ≤ e)
    (hgap : (Fintype.card ι - k) * m < (Fintype.card ι - e - k) * S'.card) :
    ∃ T : Finset ι, T.card = k + 1 ∧
      ∀ x ∈ T, m < (S'.filter (fun z => ¬ Bad x z)).card := by
  classical
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq
    (card_heavy_points_ge Bad S' e k m hbad hgap)
  exact ⟨T, hTcard, fun x hx => (Finset.mem_filter.mp (hTsub hx)).2⟩

/-! ## The 2×2 Vandermonde brick (Step 8 entry) -/

variable {F : Type*} [Field F]

/-- **Two-point Vandermonde.** Two *distinct* scalars at which the affine identities
`v₀ + zᵢ·v₁ = u₀ + zᵢ·u₁` hold pin both components: `v₀ = u₀` and `v₁ = u₁`. This is the
per-coordinate Step-8 solve of [BCIKS20] §5: a heavy point (`|S'_x| ≥ 2`) determines the
local data of the interpolant `γ(x) = u₀(x) + Z·u₁(x)`. -/
theorem affine_eq_of_two_points {v₀ v₁ u₀ u₁ z₁ z₂ : F} (hz : z₁ ≠ z₂)
    (h1 : v₀ + z₁ * v₁ = u₀ + z₁ * u₁)
    (h2 : v₀ + z₂ * v₁ = u₀ + z₂ * u₁) :
    v₀ = u₀ ∧ v₁ = u₁ := by
  have hv₁ : v₁ = u₁ := by
    have hcancel : (z₁ - z₂) * v₁ = (z₁ - z₂) * u₁ := by linear_combination h1 - h2
    exact mul_left_cancel₀ (sub_ne_zero.mpr hz) hcancel
  exact ⟨by linear_combination h1 - z₁ * hv₁, hv₁⟩

/-- **Two-scalar `Finset` form.** If at least two scalars of `S'` satisfy the affine
identity, the components are pinned. (`2 ≤ |S'_x|` is exactly `m = 1`-heaviness.) -/
theorem affine_eq_of_two_scalars [DecidableEq F] (S' : Finset F) {v₀ v₁ u₀ u₁ : F}
    (h2 : 2 ≤ (S'.filter (fun z => v₀ + z * v₁ = u₀ + z * u₁)).card) :
    v₀ = u₀ ∧ v₁ = u₁ := by
  obtain ⟨z₁, hz₁, z₂, hz₂, hne⟩ := Finset.one_lt_card.mp
    (by omega : 1 < (S'.filter (fun z => v₀ + z * v₁ = u₀ + z * u₁)).card)
  exact affine_eq_of_two_points hne (Finset.mem_filter.mp hz₁).2 (Finset.mem_filter.mp hz₂).2

/-! ## Composite hand-off: `k + 1` pinned coordinates -/

/-- **Steps 7–8 hand-off (Claim 5.11 → Claim 5.9 entry).** Suppose
* `(hid)` at every coordinate, each *good* scalar `z ∈ S'` (i.e. `¬ Bad x z`) certifies the
  affine identity `v₀ x + z·v₁ x = u₀ x + z·u₁ x`;
* `(hbad)` each `z ∈ S'` is bad at `≤ e` coordinates;
* `(hgap)` the `m = 1` gap inequality `n − k < (n − e − k)·|S'|`.

Then there are `k + 1` coordinates at which both components are pinned:
`v₀ x = u₀ x ∧ v₁ x = u₁ x`. Feeding these to a degree-`k` uniqueness argument
(`F`-Lagrange) is exactly the [BCIKS20] §5 Step-8 conclusion. -/
theorem exists_pinned_points [DecidableEq F]
    (Bad : ι → F → Prop) [∀ x z, Decidable (Bad x z)]
    (S' : Finset F) (v₀ v₁ u₀ u₁ : ι → F) (e k : ℕ)
    (hid : ∀ x, ∀ z ∈ S', ¬ Bad x z → v₀ x + z * v₁ x = u₀ x + z * u₁ x)
    (hbad : ∀ z ∈ S', (univ.filter (fun x => Bad x z)).card ≤ e)
    (hgap : Fintype.card ι - k < (Fintype.card ι - e - k) * S'.card) :
    ∃ T : Finset ι, T.card = k + 1 ∧ ∀ x ∈ T, v₀ x = u₀ x ∧ v₁ x = u₁ x := by
  classical
  obtain ⟨T, hTcard, hTheavy⟩ := exists_heavy_subset Bad S' e k 1 hbad (by simpa using hgap)
  refine ⟨T, hTcard, fun x hx => ?_⟩
  have hsub : S'.filter (fun z => ¬ Bad x z)
      ⊆ S'.filter (fun z => v₀ x + z * v₁ x = u₀ x + z * u₁ x) := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, hid x z hz.1 hz.2⟩
  have hheavy := hTheavy x hx
  have hle := Finset.card_le_card hsub
  exact affine_eq_of_two_scalars S' (by omega)

end CodingTheory.ProximityGap.Hab25HeavyPoints

/-! ## Axiom audit — kernel-clean. -/
#print axioms CodingTheory.ProximityGap.Hab25HeavyPoints.card_heavy_ge_of_sum_ge
#print axioms CodingTheory.ProximityGap.Hab25HeavyPoints.sum_good_card_ge
#print axioms CodingTheory.ProximityGap.Hab25HeavyPoints.card_heavy_points_ge
#print axioms CodingTheory.ProximityGap.Hab25HeavyPoints.exists_heavy_subset
#print axioms CodingTheory.ProximityGap.Hab25HeavyPoints.affine_eq_of_two_points
#print axioms CodingTheory.ProximityGap.Hab25HeavyPoints.affine_eq_of_two_scalars
#print axioms CodingTheory.ProximityGap.Hab25HeavyPoints.exists_pinned_points

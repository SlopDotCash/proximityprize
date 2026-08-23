/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GG25CurveDecodability
import ArkLib.Data.CodingTheory.ProximityGap.GG25SpreadBound

/-!
# [GG25] Theorem 3.3 — mutual correlated agreement from curve-decodability (issue #389 / #334 B2)

Wires the in-tree curve-decodability *definition* (`GG25CurveDecodability.CurveDecodable`,
`curveCloseSet`, using the relative-distance `δᵣ`) to the spread bound
(`GG25SpreadBound.all_seeds_close`) to obtain Goyal–Guruswami **Theorem 3.3**: a
`(ℓ, δ, a, t)`-curve-decodable code's tested curve is close to a *single* codeword curve at
**every** seed.

* `hammingDist_le_floor_of_relHam_le` — the `δᵣ` (relative Hamming, `= hammingDist/n` over `ℚ≥0`)
  ⟹ integer threshold `D = ⌊δ·n⌋` bridge, so the `curveCloseSet` (stated with `δᵣ ≤ δ`) feeds the
  integer-`hammingDist` close set of `GG25SpreadBound`.
* `all_seeds_close_of_curveDecodable` — **Theorem 3.3**: curve-decodability gives a codeword stack
  `cs` whose curve is within `(t − ℓ)·dist ≤ t·⌊δ·n⌋` of the tested curve at *every* seed `β` —
  the mutual-correlated-agreement conclusion.

The argument is exactly the paper's: `CurveDecodable.exists_curve_of_close` produces a codeword
curve agreeing with `f` on `≥ t` close seeds; on those seeds the tested curve is `δᵣ ≤ δ`-close to
the codeword curve, i.e. integer-close (`≤ ⌊δ·n⌋`); `all_seeds_close` then spreads that to every
seed via the degree-`ℓ` root bound. Axiom-clean `[propext, Classical.choice, Quot.sound]`.

**Scope.** This is the general curve-decodability ⟹ MCA mechanism (class-B2). GG25 supplies
curve-decodability for folded-RS / multiplicity / random-RS / subspace-design codes (not explicit
plain smooth-domain RS); the `δ*` open core is unaffected.
-/

open Finset Code
open scoped NNReal

namespace ProximityGap.GG25Lemma32

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The `δᵣ` → integer-`D` bridge.** Relative-Hamming closeness `δᵣ(u,v) ≤ δ` (cast to `ℝ≥0`)
forces the integer Hamming distance below the floor `⌊δ·n⌋` — the clean threshold consumed by
`GG25SpreadBound.all_seeds_close`. -/
theorem hammingDist_le_floor_of_relHam_le {u v : ι → A} {δ : ℝ≥0}
    (h : ((relHammingDist u v : ℚ≥0) : ℝ≥0) ≤ δ) :
    hammingDist u v ≤ ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ := by
  have hcard : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  have hcast : ((relHammingDist u v : ℚ≥0) : ℝ≥0)
      = (hammingDist u v : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
    simp only [relHammingDist, NNRat.cast_div, NNRat.cast_natCast]
  rw [hcast, div_le_iff₀ hcard] at h
  exact Nat.le_floor h

/-- **[GG25] Theorem 3.3 (mutual correlated agreement from curve-decodability).** If `C` is
`(ℓ, δ, a, t)`-curve-decodable with `ℓ < t`, then for every tested stack `u` and codeword-curve
`f` whose close set reaches the threshold `a`, there is a single codeword stack `cs` whose curve
agrees with the tested curve at *every* seed up to `(t − ℓ)·dist ≤ t·⌊δ·n⌋`. -/
theorem all_seeds_close_of_curveDecodable
    {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0} {a t : ℕ} (hlt : ℓ < t)
    (h : CurveDecodable (F := F) C ℓ δ a t)
    {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A} (hf : ∀ α, f α ∈ C)
    (hclose : a ≤ (curveCloseSet δ u f).card) :
    ∃ cs : Fin (ℓ + 1) → ι → A, (∀ j, cs j ∈ C) ∧
      ∀ β : F, (t - ℓ) * hammingDist (comb u β) (comb cs β)
            ≤ t * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ := by
  classical
  obtain ⟨cs, hcs, hcount⟩ := h.exists_curve_of_close hf hclose
  refine ⟨cs, hcs, fun β => ?_⟩
  set D := ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ with hD
  -- the explained close seeds inject into the integer close set of the tested vs codeword curve
  have hsub : ((curveCloseSet δ u f).filter
        (fun α => f α = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • cs j i))
      ⊆ univ.filter (fun α : F => hammingDist (comb u α) (comb cs α) ≤ D) := by
    intro α hα
    rw [mem_filter] at hα
    obtain ⟨hαC, hαeq⟩ := hα
    simp only [curveCloseSet, mem_filter, mem_univ, true_and] at hαC
    simp only [mem_filter, mem_univ, true_and]
    have hcomb_cs : f α = comb cs α := hαeq
    rw [hcomb_cs] at hαC
    exact hammingDist_le_floor_of_relHam_le hαC
  have ht : t ≤ (univ.filter (fun α : F => hammingDist (comb u α) (comb cs α) ≤ D)).card :=
    le_trans hcount (Finset.card_le_card hsub)
  exact all_seeds_close hlt u cs ht β

/-- **The relative-distance form of Theorem 3.3** (the literal [GG25] conclusion). At every seed
the tested curve is within relative Hamming distance `(t/(t−ℓ))·δ` of the codeword curve `cs` —
i.e. `δ·(1 + ℓ/(t−ℓ))`, the mutual-correlated-agreement spread radius. (`t−ℓ` is taken in `ℕ`
then cast, since `NNReal` subtraction is truncated.) -/
theorem all_seeds_relClose_of_curveDecodable
    {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0} {a t : ℕ} (hlt : ℓ < t)
    (h : CurveDecodable (F := F) C ℓ δ a t)
    {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A} (hf : ∀ α, f α ∈ C)
    (hclose : a ≤ (curveCloseSet δ u f).card) :
    ∃ cs : Fin (ℓ + 1) → ι → A, (∀ j, cs j ∈ C) ∧
      ∀ β : F, ((relHammingDist (comb u β) (comb cs β) : ℚ≥0) : ℝ≥0)
            ≤ ((t : ℝ≥0) / ((t - ℓ : ℕ) : ℝ≥0)) * δ := by
  obtain ⟨cs, hcs, hball⟩ := all_seeds_close_of_curveDecodable hlt h hf hclose
  refine ⟨cs, hcs, fun β => ?_⟩
  have hnpos : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  have htlpos : (0 : ℝ≥0) < ((t - ℓ : ℕ) : ℝ≥0) := by exact_mod_cast Nat.sub_pos_of_lt hlt
  -- cast hball to ℝ≥0 and weaken the floor: (t−ℓ)·H ≤ t·δ·n
  have hcastineq : ((t - ℓ : ℕ) : ℝ≥0) * (hammingDist (comb u β) (comb cs β) : ℝ≥0)
      ≤ (t : ℝ≥0) * δ * (Fintype.card ι : ℝ≥0) := by
    have key : ((t - ℓ : ℕ) : ℝ≥0) * (hammingDist (comb u β) (comb cs β) : ℝ≥0)
        ≤ (t : ℝ≥0) * ((⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ : ℕ) : ℝ≥0) := by exact_mod_cast hball β
    refine key.trans ?_
    rw [mul_assoc]
    gcongr
    exact Nat.floor_le (by positivity)
  -- δᵣ = H/n, divide back
  rw [show ((relHammingDist (comb u β) (comb cs β) : ℚ≥0) : ℝ≥0)
        = (hammingDist (comb u β) (comb cs β) : ℝ≥0) / (Fintype.card ι : ℝ≥0) by
      simp only [relHammingDist, NNRat.cast_div, NNRat.cast_natCast]]
  rw [div_le_iff₀ hnpos, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ htlpos]
  calc (hammingDist (comb u β) (comb cs β) : ℝ≥0) * ((t - ℓ : ℕ) : ℝ≥0)
      = ((t - ℓ : ℕ) : ℝ≥0) * (hammingDist (comb u β) (comb cs β) : ℝ≥0) := by ring
    _ ≤ (t : ℝ≥0) * δ * (Fintype.card ι : ℝ≥0) := hcastineq

/-- **[GG25] Lemma 3.2, relative-distance form (arbitrary stacks).** The general spread statement
(no curve-decodability): if two curves `∑ⱼ αʲ•uⱼ`, `∑ⱼ αʲ•cⱼ` are within relative Hamming distance
`δ` at `≥ t` seeds (`ℓ < t`), then at *every* seed they are within `(t/(t−ℓ))·δ` — i.e.
`δ·(1 + ℓ/(t−ℓ))`. `all_seeds_relClose_of_curveDecodable` is the curve-decodable specialization. -/
theorem all_seeds_relClose {ℓ t : ℕ} {δ : ℝ≥0} (hlt : ℓ < t)
    (u c : Fin (ℓ + 1) → ι → A)
    (hclose : t ≤ (univ.filter (fun α : F =>
      ((relHammingDist (comb u α) (comb c α) : ℚ≥0) : ℝ≥0) ≤ δ)).card) (β : F) :
    ((relHammingDist (comb u β) (comb c β) : ℚ≥0) : ℝ≥0)
      ≤ ((t : ℝ≥0) / ((t - ℓ : ℕ) : ℝ≥0)) * δ := by
  classical
  have hsub : (univ.filter (fun α : F =>
        ((relHammingDist (comb u α) (comb c α) : ℚ≥0) : ℝ≥0) ≤ δ))
      ⊆ univ.filter (fun α : F =>
        hammingDist (comb u α) (comb c α) ≤ ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊) := by
    intro α hα
    simp only [mem_filter, mem_univ, true_and] at hα ⊢
    exact hammingDist_le_floor_of_relHam_le hα
  have hint : t ≤ (univ.filter (fun α : F =>
      hammingDist (comb u α) (comb c α) ≤ ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊)).card :=
    le_trans hclose (Finset.card_le_card hsub)
  have hball := all_seeds_close hlt u c hint β
  have hnpos : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  have htlpos : (0 : ℝ≥0) < ((t - ℓ : ℕ) : ℝ≥0) := by exact_mod_cast Nat.sub_pos_of_lt hlt
  have hcastineq : ((t - ℓ : ℕ) : ℝ≥0) * (hammingDist (comb u β) (comb c β) : ℝ≥0)
      ≤ (t : ℝ≥0) * δ * (Fintype.card ι : ℝ≥0) := by
    have key : ((t - ℓ : ℕ) : ℝ≥0) * (hammingDist (comb u β) (comb c β) : ℝ≥0)
        ≤ (t : ℝ≥0) * ((⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ : ℕ) : ℝ≥0) := by exact_mod_cast hball
    refine key.trans ?_
    rw [mul_assoc]
    gcongr
    exact Nat.floor_le (by positivity)
  rw [show ((relHammingDist (comb u β) (comb c β) : ℚ≥0) : ℝ≥0)
        = (hammingDist (comb u β) (comb c β) : ℝ≥0) / (Fintype.card ι : ℝ≥0) by
      simp only [relHammingDist, NNRat.cast_div, NNRat.cast_natCast]]
  rw [div_le_iff₀ hnpos, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ htlpos]
  calc (hammingDist (comb u β) (comb c β) : ℝ≥0) * ((t - ℓ : ℕ) : ℝ≥0)
      = ((t - ℓ : ℕ) : ℝ≥0) * (hammingDist (comb u β) (comb c β) : ℝ≥0) := by ring
    _ ≤ (t : ℝ≥0) * δ * (Fintype.card ι : ℝ≥0) := hcastineq

end ProximityGap.GG25Lemma32

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.GG25Lemma32.all_seeds_close_of_curveDecodable
#print axioms ProximityGap.GG25Lemma32.all_seeds_relClose_of_curveDecodable
#print axioms ProximityGap.GG25Lemma32.all_seeds_relClose

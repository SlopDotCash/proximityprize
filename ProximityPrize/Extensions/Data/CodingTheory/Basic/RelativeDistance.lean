/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.Basic.RelativeDistance

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ProximityPrize.Extensions.Data.CodingTheory.Basic.Distance

/-!
# Relative Distances for Codes

This module contains relative Hamming distance, relative distance-to-code, and the
finite-range/computable variants used by the coding-theory development.
-/

variable {n : Type*} [Fintype n] {R : Type*} [DecidableEq R]

namespace Code

noncomputable section

open NNReal
open scoped NNReal
variable {ι : Type*} [Fintype ι]
         {F : Type*}
         {u v w c : ι → F}
         {C : Set (ι → F)}

section

variable [Nonempty ι] [DecidableEq F]

/-- **ABF26 Definition 2.3.** Restricted (fractional) Hamming distance:
`Δ_T(f, g) = Pr_{i ← T}[f i ≠ g i]`, equivalently the fraction of positions in `T` on
which `f` and `g` differ.

By `NNReal`'s `0 / 0 = 0` convention this returns `0` when `T = ∅`, matching the
intuition that "the empty distribution agrees vacuously".

Unlike `relHammingDist` (which divides by `Fintype.card ι` and requires `[Nonempty ι]`),
this version explicitly takes a Finset `T : Finset ι` and divides by `T.card`. -/
noncomputable def restrictedRelHammingDist
    {ι : Type*} [DecidableEq ι] {α : Type*} [DecidableEq α]
    (T : Finset ι) (f g : ι → α) : ℝ≥0 :=
  ((T.filter (fun i => f i ≠ g i)).card : ℝ≥0) / (T.card : ℝ≥0)

/-- Paper-style notation `Δ[T](f, g)` for `restrictedRelHammingDist T f g`. The
square-bracketed `T` distinguishes from the existing `Δ₀(u, v)` (absolute Hamming
distance) and `δᵣ(u, v)` (whole-domain relative Hamming distance) above. -/
scoped notation "Δ[" T "](" f ", " g ")" => restrictedRelHammingDist T f g

@[simp]
lemma restrictedRelHammingDist_self
    {ι : Type*} [DecidableEq ι] {α : Type*} [DecidableEq α]
    (T : Finset ι) (f : ι → α) : restrictedRelHammingDist T f f = 0 := by
  simp [restrictedRelHammingDist]

/-- **Bridge between `restrictedRelHammingDist` and `relHammingDist`.** When
`T = Finset.univ`, the restricted version coincides with the standard
`relHammingDist` (cast to `ℝ≥0`). Lets downstream theorems convert freely between
the ABF26 `Δ_T(f, g)` form and the existing `δᵣ(u, v)` notation. -/
lemma restrictedRelHammingDist_univ
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type*} [DecidableEq F] (f g : ι → F) :
    restrictedRelHammingDist Finset.univ f g
      = ((relHammingDist f g : ℚ≥0) : ℝ≥0) := by
  simp only [restrictedRelHammingDist, relHammingDist, hammingDist,
    Finset.card_univ]
  push_cast
  rfl

lemma NNReal.floor_ge_Nat_of_gt
    {r : ℝ≥0} {n : ℕ} (h : r > n) :
    Nat.floor r ≥ n := by
  apply (Nat.le_floor_iff (NNReal.coe_nonneg r)).mpr
  apply le_of_lt
  exact_mod_cast h

lemma NNReal.sub_eq_zero_of_le (x y : ℝ≥0) (h : x ≤ y) : x - y = 0 := by
  exact tsub_eq_zero_of_le h

end

section

variable [DecidableEq F]

variable [Nonempty ι]

end

end

end Code

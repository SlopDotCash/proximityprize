/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MomentCollisionSpectral
import Mathlib.Tactic

/-!
# Issue #232 (ABF26) — the bridge from the Plancherel off-diagonal to the per-element Weil factors.

`MomentCollisionSpectral.lean` proved `collision · |A| = ∑_ψ ‖T ψ‖²` with `T ψ = ∑_S ψ(stat S)`, and
flagged the off-diagonal `∑_{ψ≠0} ‖T ψ‖²` as the open Weil magnitude. The fleet's
`MixedGaussSumDiagonal` / `MixedGaussSumCompleteSquare` evaluate the relevant *per-element* (single
variable) character sum `‖∑_{x∈F} ψ(b₁x + b₂x²)‖ = √q`. This file is the **explicit bridge** between
the two: it shows each Fourier coefficient `T ψ` is built from exactly those per-element factors.

## The local-statistic factorization

A statistic is **local** (additive) when it sums a per-element contribution: `stat S = ∑_{x∈S} φ x`.
The moment statistic is local — `(∑x, ∑x²) = ∑_{x∈S} (x, x²)`, and the depth-`t` tower is
`∑_{x∈S} (x, …, xᵗ)`. For any local statistic,

  `T ψ  =  ∑_{|S|=a} ∏_{x∈S} ψ (φ x)`                       (`charSum_local_factor`)

— the Fourier coefficient is the **elementary symmetric polynomial of degree `a`** in the per-element
character values `ψ (φ x)`. In particular (`charSum_momentPair_factor`), for the prize's `(∑x, ∑x²)`
statistic,

  `T ψ  =  ∑_{|S|=a} ∏_{x∈S} ψ (x, x²)`,

whose `a = 1` term `∑_{x∈G} ψ (x, x²)` is precisely the **mixed Gauss sum** the fleet evaluates
(`norm_mixedGaussSum`: `√q` over the full field). So the Plancherel off-diagonal is governed by the
symmetric functions of the per-element mixed-character values, and the missing input is the
*subgroup-restricted* partial mixed Gauss sum — the Weil-on-curves gap, located exactly.

## Honest scope

`sorry`-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`). An exact factorization
connecting the two spectral surfaces; it does **not** evaluate the subgroup-restricted partial sum
(the open Weil content).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset BigOperators
open ArkLib.ProximityGap.MomentCollisionSpectral

namespace ArkLib.ProximityGap.MomentCollisionLocalFactor

variable {F : Type*} [DecidableEq F]
variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- A character of a finset sum factors as the product of character values
(`ψ` is a homomorphism `(A,+) → (ℂ,·)`). -/
theorem map_finset_sum (ψ : AddChar A ℂ) {ι : Type*} (S : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ S, f i) = ∏ i ∈ S, ψ (f i) := by
  classical
  induction S using Finset.cons_induction with
  | empty => simp [AddChar.map_zero_eq_one]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, AddChar.map_add_eq_mul, ih]

/-- **Local-statistic factorization of the Fourier coefficient.** For a *local* (additive) statistic
`stat S = ∑_{x∈S} φ x`, the Plancherel coefficient `T ψ` is the elementary symmetric polynomial of
degree `a` in the per-element character values `ψ (φ x)`:
`T ψ = ∑_{|S|=a} ∏_{x∈S} ψ (φ x)`. The per-element factor `ψ (φ x)` is the integrand of a generalized
(mixed) Gauss sum; its `a = 1` sum `∑_{x∈G} ψ (φ x)` is that Gauss sum. -/
theorem charSum_local_factor (G : Finset F) (a : ℕ) (φ : F → A) (ψ : AddChar A ℂ) :
    charSum G a (fun S => ∑ x ∈ S, φ x) ψ = ∑ S ∈ G.powersetCard a, ∏ x ∈ S, ψ (φ x) := by
  unfold charSum
  refine Finset.sum_congr rfl (fun S _ => ?_)
  exact map_finset_sum ψ S φ

variable [CommRing F] [Fintype F]

/-- The `(∑x, ∑x²)` moment statistic written as a local statistic `∑_{x∈S} (x, x²)`. -/
theorem momentPairStat_eq (S : Finset F) :
    ((∑ x ∈ S, x), (∑ x ∈ S, x ^ 2)) = ∑ x ∈ S, ((x, x ^ 2) : F × F) := by
  rw [Prod.ext_iff]
  refine ⟨?_, ?_⟩
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum]

/-- **The prize's `(∑x, ∑x²)` Fourier coefficient is the elementary symmetric polynomial in the
mixed per-element characters.** `T ψ = ∑_{|S|=a} ∏_{x∈S} ψ (x, x²)`, whose `a = 1` term
`∑_{x∈G} ψ (x, x²)` is precisely the mixed Gauss sum evaluated (over the subgroup) by the fleet's
`MixedGaussSum*`. The explicit bridge from the Plancherel off-diagonal to the Weil factors. -/
theorem charSum_momentPair_factor (G : Finset F) (a : ℕ) (ψ : AddChar (F × F) ℂ) :
    charSum G a (fun S => ((∑ x ∈ S, x), (∑ x ∈ S, x ^ 2))) ψ
      = ∑ S ∈ G.powersetCard a, ∏ x ∈ S, ψ ((x, x ^ 2) : F × F) := by
  have h : (fun S : Finset F => ((∑ x ∈ S, x), (∑ x ∈ S, x ^ 2)))
      = (fun S => ∑ x ∈ S, ((x, x ^ 2) : F × F)) := by
    funext S; exact momentPairStat_eq S
  rw [h]
  exact charSum_local_factor G a (fun x => (x, x ^ 2)) ψ

end ArkLib.ProximityGap.MomentCollisionLocalFactor

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.MomentCollisionLocalFactor.map_finset_sum
#print axioms ArkLib.ProximityGap.MomentCollisionLocalFactor.charSum_local_factor
#print axioms ArkLib.ProximityGap.MomentCollisionLocalFactor.charSum_momentPair_factor

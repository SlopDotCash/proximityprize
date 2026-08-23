/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SeedCensusDyadicChain

/-!
# Corollaries of the seed-census dyadic chain (#389)

Small, axiom-clean consequences of the dyadic level-chain primitives in `SeedCensusDyadicChain`:
per-rung power closure, monotonicity of `LevelSparse` in its bound, the two-rung (quartic) step, and
the single-orbit census in the `LevelSparse` language.  They document the dyadic tower and feed
downstream rung arithmetic; none touches the open `O(log n)` sparsity problem.
-/

set_option linter.unusedSectionVars false


open Polynomial Finset

namespace ArkLib.ProximityGap.Rigidity

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Per-rung power closure (recursive form).** Every element of the level set `levelStep S h r`
of a subset of `μ_n` is an `(n/(h·2^r))`-th root of unity.  Unpacks the subset condition
`levelStep_subset_subgroup` into the explicit per-rung power equation. -/
theorem levelStep_in_roots_recursive {n h : ℕ} (hn : 0 < n) (r : ℕ) (hdvd : (h * 2 ^ r) ∣ n)
    (S : Finset F) (hS : S ⊆ nthRootsFinset n (1 : F)) :
    ∀ c ∈ levelStep S h r, c ^ (n / (h * 2 ^ r)) = 1 := by
  intro c hc
  have hpos : 0 < n / (h * 2 ^ r) :=
    Nat.div_pos (Nat.le_of_dvd hn hdvd) (Nat.pos_of_dvd_of_pos hdvd hn)
  exact (mem_nthRootsFinset hpos (1 : F)).mp (levelStep_subset_subgroup hn r hdvd S hS hc)

/-- **Monotonicity of `LevelSparse` in the sparsity bound.** -/
theorem levelSparse_monotone_in_bound {S : Finset F} {h B₁ B₂ : ℕ} (hB : B₁ ≤ B₂)
    (h_sparse : LevelSparse S h B₁) : LevelSparse S h B₂ :=
  le_trans h_sparse hB

/-- **Two-rung (quartic) level step.** Advancing the dyadic chain by two rungs squares twice,
i.e. raises to the fourth power: `levelStep S h (r+2) = (levelStep S h r).image (·^4)`. -/
theorem levelStep_succ_quartic (S : Finset F) (h r : ℕ) :
    levelStep S h (r + 2) = (levelStep S h r).image (fun y => y ^ 4) := by
  have h1 := levelStep_succ S h (r + 1)
  have h2 := levelStep_succ S h r
  rw [h1, h2, Finset.image_image]
  have hfun : ((fun y : F => y ^ 2) ∘ fun y : F => y ^ 2) = (fun x : F => x ^ 4) := by
    funext x; simp only [Function.comp_apply]; ring
  rw [hfun]

/-- **Single-orbit census in `LevelSparse` language.** A full primitive-`h`-root orbit
`{g^k : k < h}` is `h`-level-sparse at bound `1` (all its elements are `h`-th roots of unity, so
their `h`-th powers collapse to `{1}`). -/
theorem single_orbit_census_via_level (g : F) (h : ℕ) (hg : IsPrimitiveRoot g h) :
    LevelSparse ((Finset.range h).image (fun k => g ^ k)) h 1 := by
  apply levelSparse_one_of_hth_roots
  intro x hx
  obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp hx
  rw [← pow_mul, mul_comm, pow_mul, hg.pow_eq_one, one_pow]

end ArkLib.ProximityGap.Rigidity

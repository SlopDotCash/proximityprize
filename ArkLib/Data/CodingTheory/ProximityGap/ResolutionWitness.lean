/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.RadiusOneExact

/-!
# Witness-carrying resolutions of the §1 Grand MCA Challenge in the large-field regime

`GrandChallengeRadiusOne.lean` proves the upper bound `ε_mca(RS, 1) ≤ C(n, k+1) / |F|`
(`epsMCA_one_le_choose_div`) and `GrandChallengeRadiusOneExact.lean` proves the matching
lower bound, hence the *exact* value `ε_mca(RS, 1) = C(n, k+1) / |F|`
(`epsMCA_one_eq_choose_div`) whenever `k + 1 ≤ n` and `|F| > C(C(n, k+1), 2)`.

`GrandChallenges.lean` defines `GrandMCAResolution C ε*` — the **full witness-carrying data**
the §1 Grand MCA Challenge asks for: a maximal threshold `δ* ∈ [0, 1]` with `ε_mca(C, δ*) ≤ ε*`
below it and strict failure `ε_mca(C, δ) > ε*` for every `δ ∈ (δ*, 1]`.

This file **constructs that data object** in the large-field regime. The key observation is
that the entire radius range collapses to its right endpoint: because `ε_mca` is monotone in
`δ` (`epsMCA_mono`), the radius-one bound dominates the whole interval, and `δ* := 1` is
forced to be maximal (the maximality clause quantifies over `δ ∈ (1, 1] = ∅`, so it is
vacuously true). Concretely:

* `epsMCA_le_choose_div_of_le_one` — for every `δ ≤ 1`, `ε_mca(RS, δ) ≤ C(n, k+1) / |F|`,
  by `epsMCA_mono` + `epsMCA_one_le_choose_div`.
* `grandMCAResolution_of_large_field` — under `k + 1 ≤ n`, `|F| > C(C(n, k+1), 2)`, and
  `C(n, k+1) / |F| ≤ ε*`, the literal `GrandMCAResolution (RS[F, domain, k]) ε*` with
  `δStar := 1`.
* `mcaPrize_resolutions_of_large_field` — at every prize rate `ρ ∈ {1/2,1/4,1/8,1/16}` and
  `ε* = 2^{-128}`, the analogous resolution, under the same numeric hypothesis shape as
  `mcaPrize_of_large_field`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators

section ResolutionWitness

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Polynomial ReedSolomon GrandChallenges

/-- **Radius-uniform MCA bound.** For `C := RS[F, domain, k]` and any radius `δ ≤ 1`, the
radius-one upper bound dominates: `ε_mca(C, δ) ≤ C(n, k+1) / |F|`. Immediate from
monotonicity of `ε_mca` in `δ` (`epsMCA_mono`) composed with the radius-one upper bound
(`epsMCA_one_le_choose_div`). -/
theorem epsMCA_le_choose_div_of_le_one (domain : ι ↪ F) (k : ℕ) {δ : ℝ≥0} (hδ : δ ≤ 1) :
    epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ ≤
      (Nat.choose (Fintype.card ι) (k + 1) : ENNReal) / (Fintype.card F : ENNReal) :=
  le_trans (epsMCA_mono (F := F) (ReedSolomon.code domain k : Set (ι → F)) hδ)
    (epsMCA_one_le_choose_div domain k)

/-- **Witness-carrying resolution of the §1 Grand MCA Challenge (large-field regime).**

Under `k + 1 ≤ n`, `|F| > C(C(n, k+1), 2)` (the `GrandChallengeRadiusOneExact` hypotheses),
and `C(n, k+1) / |F| ≤ ε*`, we construct the literal `GrandMCAResolution` data object for
`RS[F, domain, k]` at threshold `ε*`, with maximal threshold `δStar := 1`:

* the bound `ε_mca(C, 1) ≤ ε*` follows from the exact value `ε_mca(C, 1) = C(n, k+1) / |F|`
  (`epsMCA_one_eq_choose_div`) and the hypothesis `C(n, k+1) / |F| ≤ ε*`;
* maximality is vacuous: there is no `δ ∈ (1, 1]`, so the strict-failure clause holds for
  every such `δ` by contradiction (`1 < δ` and `δ ≤ 1` are incompatible).

This is the full data the challenge asks for, packaged as `GrandMCAResolution`. -/
noncomputable def grandMCAResolution_of_large_field
    (domain : ι ↪ F) {k : ℕ} (hk : k + 1 ≤ Fintype.card ι)
    (hq : (Nat.choose (Fintype.card ι) (k + 1)).choose 2 < Fintype.card F) {ε_star : ℝ≥0}
    (hle : (Nat.choose (Fintype.card ι) (k + 1) : ENNReal) / (Fintype.card F : ENNReal)
      ≤ (ε_star : ENNReal)) :
    GrandMCAResolution (ReedSolomon.code domain k : Set (ι → F)) ε_star where
  δStar := 1
  le_one := le_refl 1
  bound := by
    rw [epsMCA_one_eq_choose_div domain hk hq]
    exact hle
  maximal := by
    intro δ h1δ hδ1
    exact absurd (lt_of_lt_of_le h1δ hδ1) (lt_irrefl 1)

/-- **Resolutions at every prize rate (large-field regime).** Mirroring the hypothesis shape
of `mcaPrize_of_large_field`, but additionally supplying the exact-value lower-bound
hypotheses of `GrandChallengeRadiusOneExact`, we construct for *every* prize rate
`ρⱼ ∈ {1/2, 1/4, 1/8, 1/16}` (with `ε* = 2^{-128}`) the witness-carrying
`GrandMCAResolution` data object for the corresponding Reed–Solomon code, with maximal
threshold `δStar := 1`.

Write `kⱼ := ⌊ρⱼ · n⌋`. The three hypotheses per rate are:
* `hk j : kⱼ + 1 ≤ n` (so the exact value applies);
* `hq j : C(C(n, kⱼ+1), 2) < |F|` (the large-field separation from `epsMCA_one_eq_choose_div`);
* `hbound j : C(n, kⱼ+1) / |F| ≤ ε*` (the same numeric check as `mcaPrize_of_large_field`).

Each such resolution upgrades the corresponding `grandMCAChallengeRSrate` from a mere `Prop`
to a `δ*`-carrying term (cf. `grandMCAChallenge_of_resolution`). -/
noncomputable def mcaPrize_resolutions_of_large_field (domain : ι ↪ F)
    (hk : ∀ j : Fin 4,
      ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1 ≤ Fintype.card ι)
    (hq : ∀ j : Fin 4,
      (Nat.choose (Fintype.card ι) (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1)).choose 2
        < Fintype.card F)
    (hbound : ∀ j : Fin 4,
      (Nat.choose (Fintype.card ι) (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ENNReal)
        / (Fintype.card F : ENNReal) ≤ (epsStar : ENNReal)) :
    ∀ j : Fin 4,
      GrandMCAResolution
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar :=
  fun j => grandMCAResolution_of_large_field domain (hk j) (hq j) (hbound j)

end ResolutionWitness

end ProximityGap

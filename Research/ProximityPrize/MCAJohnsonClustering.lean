/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Research.ProximityPrize.MCAJohnsonAssembly
import ArkLib.Data.CodingTheory.ProximityGap.ReedSolomonUniqueDecode

/-!
# MCA → Johnson clustering (#232): the degree-1 decoding-curve discharge and the bivariate residual

`ProximityGap.MCAJohnson.LineWitnessClustering C δ ℓ` is the genuine open core isolated in
`MCAJohnsonAssembly.lean`: *every bad scalar's line-witness lives in one fixed finite list `L` of
size `≤ ℓ`, at a common active coordinate.* It directly yields the prize bound
`epsMCA C δ ≤ ℓ / |F|` (`MCAJohnson.epsMCA_le_of_lineWitnessClustering`). This file proves the
per-stack degree-1 collapse, derives `LineWitnessClustering C δ 0` from a *uniform* degree-1 curve
hypothesis, and names the Reed–Solomon Johnson-radius specialization of the residual.

**Scope caveat (audit CW-B21-05).** The uniform degree-1 curve hypothesis `hcurve` of
`lineWitnessClustering_of_degreeOne_curve` / `epsMCA_eq_zero_of_degreeOne_curve` is *not*
satisfiable for a proper code containing `0`: `degreeOne_curve_uniform_forces_univ` shows it forces
every word to be a codeword. These uniform statements are therefore only meaningful as conditional
wiring; they are not an unconditional instance of `LineWitnessClustering`.

## What is proven here (axiom-clean, no `sorry`, no vacuous `: True`, no fake axiom)

### Tier 1 — the degree-1 decoding-curve collapse (per stack)

The BCIKS20 Johnson-case mechanism, at its simplest degree, says: when the close codewords across
all scalars `γ` lie on a *single degree-1* decoding curve `g₀ + Z·g₁` — i.e. the witness codeword
of every `mcaEvent` is `g₀ + γ·g₁` for two **fixed** codewords `g₀, g₁ ∈ C` agreeing with the stack
`(u₀, u₁)` on the witness set — the bad event **cannot fire at all**: the joint pair `(g₀, g₁)`
disqualifies it (`pairJointAgreesOn` holds, contradicting the `mcaEvent` no-joint-pair clause). This
is the *full-radius collapse* of `ReedSolomonUniqueDecode.jointAgreement_of_common_locator`, read on
the MCA side.

* **`mcaEvent_false_of_degreeOne_curve`** — the collapse: under the fixed `(g₀, g₁)` degree-1 curve
  hypothesis, `mcaEvent C δ u₀ u₁ γ` is **false** for every `γ`.
* **`lineWitnessClustering_of_degreeOne_curve`** — under a *uniform* (all-stacks) curve
  hypothesis, `LineWitnessClustering C δ 0` holds (the bad set is empty, so the size-`0` list `∅`
  works).
* **`epsMCA_eq_zero_of_degreeOne_curve`** — and so `epsMCA C δ = 0` under that hypothesis.
* **`degreeOne_curve_uniform_forces_univ`** — but the uniform hypothesis forces `C = univ` whenever
  `0 ∈ C`, so for proper linear codes the two uniform statements above are vacuous. Only the
  per-stack collapse `mcaEvent_false_of_degreeOne_curve` has content for proper codes.

### Tier 2 — the Reed–Solomon Johnson-radius residual, as an explicit signature

Above degree 1 the witnesses no longer collapse; bounding their *number* is the bivariate
Guruswami–Sudan list size. `JohnsonRadiusListSize` is `LineWitnessClustering` specialized to
Reed–Solomon (a former definitional duplicate `BivariateDecodingCurve` was removed). Proving it
for a concrete `poly` list size is the external bivariate-GS prize, carried as a hypothesis, not a
`sorry`.

All theorems below are axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf. *Proximity Gaps for Reed–Solomon Codes*.
  §5 (Johnson-radius list-decoding chain).
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap

open scoped NNReal ENNReal BigOperators
open Finset Code MCAJohnson

namespace MCAJohnsonClustering

section Scalar

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Tier 1 — the degree-1 decoding-curve collapse -/

/-- **The degree-1 decoding-curve collapse: `mcaEvent` is false.**

Suppose the stack `(u₀, u₁)` has a *fixed* degree-1 decoding curve `g₀ + Z·g₁`: there are two
codewords `g₀, g₁ ∈ C` such that, whenever `mcaEvent` fires at some `γ` with witness set `S`, the
fixed pair `(g₀, g₁)` already agrees with `(u₀, u₁)` on `S` (the "the close codewords across all
scalars lie on one degree-1 curve" hypothesis of the BCIKS20 Johnson case, read at degree 1).

Then `mcaEvent C δ u₀ u₁ γ` is **false** for every `γ`: the pair `(g₀, g₁)` is exactly a
`pairJointAgreesOn` witness on the bad event's own set `S`, contradicting its no-joint-pair clause.

This is the MCA-side reading of the full-radius collapse
`ReedSolomonUniqueDecode.jointAgreement_of_common_locator`: a *shared* (here, degree-1, fixed)
decoder forces a *common* agreement set, which disqualifies the bad event. -/
theorem mcaEvent_false_of_degreeOne_curve
    (C : Set (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) (γ : F)
    (g₀ g₁ : ι → F) (hg₀ : g₀ ∈ C) (hg₁ : g₁ ∈ C)
    (hcurve : ∀ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
      (∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) →
      (∀ i ∈ S, g₀ i = u₀ i ∧ g₁ i = u₁ i)) :
    ¬ mcaEvent (A := F) C δ u₀ u₁ γ := by
  rintro ⟨S, hScard, hwit, hno⟩
  exact hno ⟨g₀, hg₀, g₁, hg₁, hcurve S hScard hwit⟩

/-- **The uniform degree-1 curve hypothesis forces `C = univ` (for `0 ∈ C`).**

If `0 ∈ C` and every stack `u` has codewords `g₀ u, g₁ u ∈ C` agreeing with `(u 0, u 1)` on every
witness set of size `≥ (1 − δ)n` (the hypothesis `hcurve` of
`lineWitnessClustering_of_degreeOne_curve`), then every word `v` is a codeword: take `u = (0, v)`,
`γ = 0`, `S = univ` and the witness `w = 0`; `hcurve` forces `g₁ u = v`. Hence the uniform
statements of Tier 1 are vacuous for every proper code containing `0` (audit CW-B21-05). -/
theorem degreeOne_curve_uniform_forces_univ
    (C : Set (ι → F)) (δ : ℝ≥0) (h0 : (0 : ι → F) ∈ C)
    (g₀ g₁ : WordStack F (Fin 2) ι → ι → F)
    (hg₁ : ∀ u, g₁ u ∈ C)
    (hcurve : ∀ u : WordStack F (Fin 2) ι, ∀ γ : F, ∀ S : Finset ι,
      (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
      (∃ w ∈ C, ∀ i ∈ S, w i = (u 0) i + γ • (u 1) i) →
      (∀ i ∈ S, g₀ u i = (u 0) i ∧ g₁ u i = (u 1) i))
    (v : ι → F) : v ∈ C := by
  set u : WordStack F (Fin 2) ι := ![0, v] with hu
  have hcard : ((Finset.univ : Finset ι).card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι := by
    rw [Finset.card_univ]
    calc (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ 1 * (Fintype.card ι : ℝ≥0) := by
          gcongr; exact tsub_le_self
      _ = _ := one_mul _
  have hagree := hcurve u 0 Finset.univ hcard ⟨0, h0, fun i _ => by simp [hu]⟩
  have hv : g₁ u = v := funext fun i => by
    simpa [hu] using (hagree i (Finset.mem_univ i)).2
  rw [← hv]
  exact hg₁ u

/-- **`LineWitnessClustering C δ 0` from a uniform degree-1 decoding curve (`ℓ = 0`).**

If *every* stack `u` has a fixed degree-1 decoding curve `g₀ u + Z·g₁ u` (codewords jointly agreeing
with `(u 0, u 1)` on every bad event's witness set), then `LineWitnessClustering C δ 0` holds: by
`mcaEvent_false_of_degreeOne_curve` there are no bad scalars, so the empty list `∅` works.

**Caveat.** By `degreeOne_curve_uniform_forces_univ` the hypothesis `hcurve` (together with
`0 ∈ C`) forces `C = univ`, so for a proper code this is conditional wiring with an unsatisfiable
hypothesis, not an unconditional instance. -/
theorem lineWitnessClustering_of_degreeOne_curve
    (C : Set (ι → F)) (δ : ℝ≥0)
    (g₀ g₁ : WordStack F (Fin 2) ι → ι → F)
    (hg₀ : ∀ u, g₀ u ∈ C) (hg₁ : ∀ u, g₁ u ∈ C)
    (hcurve : ∀ u : WordStack F (Fin 2) ι, ∀ γ : F, ∀ S : Finset ι,
      (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
      (∃ w ∈ C, ∀ i ∈ S, w i = (u 0) i + γ • (u 1) i) →
      (∀ i ∈ S, g₀ u i = (u 0) i ∧ g₁ u i = (u 1) i)) :
    LineWitnessClustering (F := F) C δ 0 := by
  intro u
  refine ⟨∅, Classical.arbitrary ι, by simp, ?_⟩
  intro γ hbad
  exact absurd hbad
    (mcaEvent_false_of_degreeOne_curve C δ (u 0) (u 1) γ (g₀ u) (g₁ u) (hg₀ u) (hg₁ u)
      (hcurve u γ))

/-- **MCA error vanishes under a uniform degree-1 decoding curve.**

Composing `lineWitnessClustering_of_degreeOne_curve` (with `ℓ = 0`) and the assembly bridge
`MCAJohnson.epsMCA_le_of_lineWitnessClustering`, the MCA error is bounded by `0 / |F| = 0`, hence is
exactly `0`. Same caveat as `lineWitnessClustering_of_degreeOne_curve`: for a proper code containing
`0` the uniform hypothesis is unsatisfiable (`degreeOne_curve_uniform_forces_univ`). -/
theorem epsMCA_eq_zero_of_degreeOne_curve
    (C : Set (ι → F)) (δ : ℝ≥0)
    (g₀ g₁ : WordStack F (Fin 2) ι → ι → F)
    (hg₀ : ∀ u, g₀ u ∈ C) (hg₁ : ∀ u, g₁ u ∈ C)
    (hcurve : ∀ u : WordStack F (Fin 2) ι, ∀ γ : F, ∀ S : Finset ι,
      (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
      (∃ w ∈ C, ∀ i ∈ S, w i = (u 0) i + γ • (u 1) i) →
      (∀ i ∈ S, g₀ u i = (u 0) i ∧ g₁ u i = (u 1) i)) :
    epsMCA (F := F) (A := F) C δ = 0 := by
  have h := MCAJohnson.epsMCA_le_of_lineWitnessClustering (F := F) C δ 0
    (lineWitnessClustering_of_degreeOne_curve C δ g₀ g₁ hg₀ hg₁ hcurve)
  simpa using h

end Scalar

/-! ## Tier 2 — the precise remaining residual for the full Johnson radius

For Reed–Solomon below the Johnson radius `1 − √ρ`, the bivariate GS decoder's list size is `poly`
(in `2^m, 1/ρ, 1/η`, *not* in `q`). The single open input is `JohnsonRadiusListSize`: that the
bivariate decoding curve exists with such a `poly` list size. It is stated below with an explicit
list-size function `ℓ` (the GS list-size bound a concrete construction supplies). Proving it for a
concrete `ℓ` is the external bivariate-GS prize; here we show it discharges the prize bound. -/

section JohnsonResidual

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The isolated Johnson-radius residual (the open prize input), as an explicit predicate.**

`JohnsonRadiusListSize α k δ ℓ` asserts that the Reed–Solomon code `RS[α, k]` at radius `δ` admits a
bivariate decoding curve with GS list size `≤ ℓ`. This is `MCAJohnson.LineWitnessClustering`
specialised to `C = ReedSolomon.code α k`, with the list-size parameter `ℓ` named so a concrete
bivariate-GS construction (Prop 5.5 of [BCIKS20], via `ArkLib.GS.exists_gs_interpolant` /
`GSFactorExtract.gs_list_size_le`) plugs in its `poly` value below the Johnson radius `1 − √ρ`.

This is an explicit, unproven hypothesis (no `sorry`); no instance at a nontrivial radius is
proved in-tree. Carrying it as an explicit predicate is the boundary between the proven assembly
(this file and `MCAJohnsonAssembly.lean`) and the open Johnson-radius GS prize. -/
def JohnsonRadiusListSize (α : ι ↪ F) (k : ℕ) (δ : ℝ≥0) (ℓ : ℕ) : Prop :=
  LineWitnessClustering (F := F) (ReedSolomon.code α k : Set (ι → F)) δ ℓ

/-- **The Reed–Solomon Johnson-radius MCA prize bound, from the isolated residual.**

`JohnsonRadiusListSize α k δ ℓ ⟹ epsMCA (RS[α,k]) δ ≤ ℓ / |F|`. This is the formal statement that
the *entire* BCIKS20 Johnson-radius MCA bound over Reed–Solomon follows from the bivariate GS
list-size residual: everything below the residual is proven (`MCAJohnsonAssembly.lean`);
the residual is the open bivariate Guruswami–Sudan core, carried as the explicit hypothesis. -/
theorem epsMCA_reedSolomon_le_of_johnsonRadiusListSize
    (α : ι ↪ F) (k : ℕ) (δ : ℝ≥0) (ℓ : ℕ)
    (h : JohnsonRadiusListSize (F := F) α k δ ℓ) :
    epsMCA (F := F) (A := F) (ReedSolomon.code α k : Set (ι → F)) δ
      ≤ (ℓ : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  MCAJohnson.epsMCA_le_of_lineWitnessClustering (ReedSolomon.code α k : Set (ι → F)) δ ℓ h

end JohnsonResidual

end MCAJohnsonClustering

end ProximityGap

#print axioms ProximityGap.MCAJohnsonClustering.mcaEvent_false_of_degreeOne_curve
#print axioms ProximityGap.MCAJohnsonClustering.lineWitnessClustering_of_degreeOne_curve
#print axioms ProximityGap.MCAJohnsonClustering.epsMCA_eq_zero_of_degreeOne_curve
#print axioms ProximityGap.MCAJohnsonClustering.degreeOne_curve_uniform_forces_univ
#print axioms ProximityGap.MCAJohnsonClustering.epsMCA_reedSolomon_le_of_johnsonRadiusListSize

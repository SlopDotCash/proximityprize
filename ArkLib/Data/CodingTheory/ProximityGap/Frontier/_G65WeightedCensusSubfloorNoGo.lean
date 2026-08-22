/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G63PrimitiveCensusPinnedAtDCFloor

/-!
# LANE G65: no nonnegative depth-reweighting yields a strict weighted census sub-floor

This file closes the one census-side hope that G63's *uniform* pinning left formally open, the
question the adversarial critic ranked as the last surface where the moment machinery could, in
principle, still beat Parseval:

> does the `wraparoundExcessR` weight admit ANY depth-dependent reweighting `w(r) ≥ 0` with
> `Σ_r w(r)·(q·census G r) < Σ_r w(r)·n^{2r}` — a strict sub-floor in a *weighted* sense that
> G63's per-depth pinning does not by itself rule out?

G63 proves the per-depth circularity core `n^{2r} ≤ q·census G r` at *every* depth `r`. A weighted
exponent gain would need a nonnegative weight family `w` and a finite depth window `S` on which the
weighted census total drops strictly below the weighted DC floor. This file proves that is
impossible: nonnegative combinations of pointwise-`≥` inequalities are `≥`, so

`Σ_{r∈S} w(r)·n^{2r} ≤ Σ_{r∈S} w(r)·(q·census G r) = q·(Σ_{r∈S} w(r)·census G r)`,

for every `Finset S ⊆ ℕ` and every `w : ℕ → ℝ` with `w r ≥ 0` on `S`. Hence no nonneg reweighting
produces a strict weighted sub-floor. G63 is exactly the `S = {r}`, `w = 1` instance; this is the
strictly stronger `r`-uniform statement, and it is the theorem-level closure of the weighted
census-side door.

## What is proved (all axiom-clean, built on G63 / G56 / DCEnergyEssential objects)

Write `q = |F|`, `n = 2m`, `G = Gset ζ m`, `census G r = negSymCount G (2r) + wraparoundExcessR`.

1. `weighted_dcFloor_le_q_mul_weighted_census` : **the weighted circularity core.** For any finite
   depth window `S` and any weights `w` with `0 ≤ w r` on `S`,
   `Σ_{r∈S} w r · n^{2r} ≤ Σ_{r∈S} w r · (q·census G r)`. Nonnegative depth combinations of the
   per-depth floor are still floors.
2. `weighted_dcFloor_le_q_mul_census_sum` : the pulled-out form,
   `Σ_{r∈S} w r · n^{2r} ≤ q · Σ_{r∈S} w r · census G r`, exhibiting the shared factor `q`.
3. `not_weighted_census_strict_subfloor` : **the no-go.** There is NO nonneg reweighting with a
   strict weighted sub-floor: `¬ (Σ_{r∈S} w r · (q·census G r) < Σ_{r∈S} w r · n^{2r})`. The one
   surface where a weighted moment argument could beat `n^{2r}/q` is closed: every nonneg-weighted
   census total is pinned at-or-above the correspondingly-weighted DC floor.
4. `weightedCensusIsStrictSubfloorCertificate` / `not_weightedCensusIsStrictSubfloorCertificate` :
   an honest scope marker naming the refuted route — no nonneg weight family makes the census a
   strict weighted sub-floor certificate. No axioms, no goal weakening.

This strictly strengthens G63 (recovered as `S = {r}`, `w = 1`) and is `r`-uniform: it does not
formalize a fixed depth, it quantifies over all finite depth windows and all nonnegative weightings
at once. It is a **precise route no-go**, not a closure and not a wrapper: it does not bound
`wraparoundExcessR`, and CORE (`M(μ_n) ≤ C√(n log(p/n))`) remains open / on-BGK. Its content is
that the entire nonnegative-weighting degree of freedom on the primitive-depth census — the last
census-side lever the moment machinery had — buys nothing below the Parseval floor.

Issue #466.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

open scoped Classical BigOperators

namespace ArkLib.ProximityGap.Frontier.G65WeightedCensusSubfloorNoGo

open ArkLib.ProximityGap.Frontier.G63PrimitiveCensusPinnedAtDCFloor (census q_mul_census_ge_dcFloor)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The weighted circularity core.**  For any finite depth window `S : Finset ℕ` and any weight
family `w : ℕ → ℝ` that is nonnegative on `S`, the `w`-weighted DC floor is at-or-below the
`w`-weighted `q·census` total:

`Σ_{r∈S} w r · n^{2r} ≤ Σ_{r∈S} w r · (q · census G r)`.

Nonnegative depth combinations of the per-depth pinning `n^{2r} ≤ q·census G r` (G63's circularity
core) are still pinnings.  This is `Finset.sum_le_sum` applied to the per-depth bound scaled by the
nonnegative weight `w r`. -/
theorem weighted_dcFloor_le_q_mul_weighted_census
    {ζ : F} {m : ℕ} (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ r ∈ S, 0 ≤ w r) :
    (∑ r ∈ S, w r * (((2 * m : ℕ) : ℝ) ^ (2 * r)))
      ≤ ∑ r ∈ S, w r * ((Fintype.card F : ℝ) * (census ζ m r : ℝ)) := by
  apply Finset.sum_le_sum
  intro r hr
  exact mul_le_mul_of_nonneg_left (q_mul_census_ge_dcFloor hm hprim hψ) (hw r hr)

/-- The pulled-out form of the weighted core, exhibiting the shared factor `q = |F|`:

`Σ_{r∈S} w r · n^{2r} ≤ q · Σ_{r∈S} w r · census G r`.

So even after moving the common `q` outside the depth sum, the weighted census total is at-or-above
the weighted DC floor. -/
theorem weighted_dcFloor_le_q_mul_census_sum
    {ζ : F} {m : ℕ} (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ r ∈ S, 0 ≤ w r) :
    (∑ r ∈ S, w r * (((2 * m : ℕ) : ℝ) ^ (2 * r)))
      ≤ (Fintype.card F : ℝ) * ∑ r ∈ S, w r * (census ζ m r : ℝ) := by
  have hmain := weighted_dcFloor_le_q_mul_weighted_census hm hprim hψ S w hw
  have hpull :
      ∑ r ∈ S, w r * ((Fintype.card F : ℝ) * (census ζ m r : ℝ))
        = (Fintype.card F : ℝ) * ∑ r ∈ S, w r * (census ζ m r : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hpull] at hmain
  exact hmain

/-- **The weighted no-go — no nonneg reweighting yields a strict weighted sub-floor.**

`¬ (Σ_{r∈S} w r · (q·census G r) < Σ_{r∈S} w r · n^{2r})`.

A weighted exponent gain would require a nonnegative weight family whose `q·census` total drops
strictly below the correspondingly-weighted DC floor `Σ w r · n^{2r}`.  The weighted
circularity core forbids exactly that, at every finite depth window and every nonnegative
weighting.  This closes
the last census-side degree of freedom the moment machinery had (weighted depth reweighting), the
one surface where it could in principle have beaten the Parseval floor. -/
theorem not_weighted_census_strict_subfloor
    {ζ : F} {m : ℕ} (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ r ∈ S, 0 ≤ w r) :
    ¬ (∑ r ∈ S, w r * ((Fintype.card F : ℝ) * (census ζ m r : ℝ))
        < ∑ r ∈ S, w r * (((2 * m : ℕ) : ℝ) ^ (2 * r))) :=
  not_lt.mpr (weighted_dcFloor_le_q_mul_weighted_census hm hprim hψ S w hw)

/-- The route the weighted no-go refutes: "some nonnegative depth reweighting `w` on a finite window
`S` makes the census a strict weighted sub-floor certificate", i.e.
`Σ_{r∈S} w r · (q·census G r) < Σ_{r∈S} w r · n^{2r}`.  A scope marker for honesty — the weighted
census-side circularity is a proven refutation of exactly this proposition, uniformly in `S` and
`w`. -/
def weightedCensusIsStrictSubfloorCertificate
    (ζ : F) (m : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) : Prop :=
  ∑ r ∈ S, w r * ((Fintype.card F : ℝ) * (census ζ m r : ℝ))
    < ∑ r ∈ S, w r * (((2 * m : ℕ) : ℝ) ^ (2 * r))

/-- The census is provably NOT a strict weighted sub-floor certificate under any nonnegative
reweighting.  Honest scope marker, no axioms. -/
theorem not_weightedCensusIsStrictSubfloorCertificate
    {ζ : F} {m : ℕ} (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ r ∈ S, 0 ≤ w r) :
    ¬ weightedCensusIsStrictSubfloorCertificate ζ m S w := by
  unfold weightedCensusIsStrictSubfloorCertificate
  exact not_weighted_census_strict_subfloor hm hprim hψ S w hw

#print axioms weighted_dcFloor_le_q_mul_weighted_census
#print axioms weighted_dcFloor_le_q_mul_census_sum
#print axioms not_weighted_census_strict_subfloor
#print axioms not_weightedCensusIsStrictSubfloorCertificate

end ArkLib.ProximityGap.Frontier.G65WeightedCensusSubfloorNoGo

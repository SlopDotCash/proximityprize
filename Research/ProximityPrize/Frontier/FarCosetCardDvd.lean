/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FarLineScalarDilation
import ArkLib.Data.CodingTheory.ProximityGap.MCAEigenstackOrbitLaw

/-!
# The coset structure forces an exact DIVISIBILITY law on the bad-scalar set (#444 census face / §R4)

`FarLineScalarDilation` proved (axiom-clean) that the RS monomial far-line bad-scalar set
`explainableScalars` is **invariant under multiplication by** `m := c₀⁻¹·c₁` (`= g^{A−B}` for a
monomial line on `μ_n`): `γ ∈ bad ↔ (c₀⁻¹·c₁)·γ ∈ bad`
(`explainableScalars_rs_scalar_dilation`).  `FarCosetCardLower` then landed the first **count**
consequence — the orbit *lower* bound `orderOf m ≤ #explainableScalars` whenever a nonzero scalar is
bad (`explainableScalars_orbit_card_le`) — but explicitly **deferred the strictly stronger
divisibility** (`orderOf m ∣ #explainableScalars`), which the probe
`scripts/probes/probe_coset_card_divis.py` had confirmed 8/8 for the *nonzero* part.

This file lands that deferred divisibility, in its cleanly-provable **`0`-free** form, by **reusing
the in-tree orbit-count engine** `MCAEigenstack.orderOf_dvd_card_of_mul_mem` (a finite scalar set
closed under multiplication by a unit `α` and avoiding `0` has cardinality divisible by `orderOf α`,
proved by peeling off one full `⟨α⟩`-orbit at a time):

* `explainableScalars_orderOf_dvd_card` (HEADLINE) — for the RS monomial far line, **if `0` is NOT a
  bad scalar** then the bad-scalar set's cardinality is **exactly divisible** by `orderOf m`:
  `orderOf (Units.mk0 (c₀⁻¹·c₁) …) ∣ #explainableScalars`.  The bad set is then a disjoint union of
  full `⟨m⟩`-orbits, each of size exactly `orderOf m = n / gcd(A−B, n)` for a thin monomial `μ_n`
  line — the exact residue constraint `#bad ≡ 0 (mod orderOf m)` the §R4 census quotients by.

This refines `explainableScalars_orbit_card_le` (a `Θ(n)` floor) into the full granularity law: any
`P`-cap (the open distinct-`γ` *upper* bound the census weld needs) is now forced to be a literal
multiple of `orderOf m`, not merely `≥ orderOf m`.  It is the `explainableScalars` analogue of the
already-landed `MCAEigenstackOrbitLaw.orderOf_dvd_badScalarSet_card_of_eigenstack`
(`badScalarSet`/`mcaEvent` formulation) and `MonomialGammaFibration.orderOf_dvd_card_badScalars_erase_zero`
(`badSet` formulation) — closing divisibility on the third, RS-scalar-dilation, bad-set formulation.

PROBE: `scripts/probes/probe_coset_card_full_dvd.py` — exact brute-force list-decode over THIN
proper `μ_n = 2^a` ((p−1)/n ≥ 2, NEVER n = q−1, primes incl. Fermat 17), `δ ∈ {0.375,0.5,0.625}`:
in **every** in-scope config (`0 ∉ bad`) the FULL bad-set cardinality is divisible by `orderOf m`
(6/6, non-vacuous: `|bad| ∈ {0,4,8,12,24}`, all genuine multiples), and the `0`-bad configs (where
the hypothesis fails) are correctly out of scope.

## Scope (rule 3 / rule 6, honesty contract)

This is a structural **divisibility** (granularity) law, NOT a magnitude bound: it constrains
`#explainableScalars` to a residue class, it does **not** cap it from above.  It therefore does not
by itself help the `δ*` ceiling.  The `0`-freeness hypothesis is genuine (mirrors the `h0bad` of the
in-tree eigenstack/monomial divisibility theorems); when `0` is bad the orbit of `0` is a fixed
point and the clean divisibility degenerates (the probe records this as out-of-scope, never a false
positive).  NOT a CORE / Conj-7.1 closure; the `M(μ_n) ≤ C√(n log(p/n))` CORE and the per-band
distinct-`γ` *upper* bound `P` both stay OPEN.  No capacity / cliff-at-n/2 / beyond-Johnson claim.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.FarCosetExplosion

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **HEADLINE — the orbit DIVISIBILITY law on the bad-scalar count.**  For the RS monomial far
line (with the scalar-dilation hypotheses of `explainableScalars_rs_scalar_dilation`), if the scalar
`0` is **not** bad, then the bad-scalar set's cardinality is divisible by `orderOf m`,
`m := c₀⁻¹·c₁`:

  `orderOf (Units.mk0 (c₀⁻¹·c₁) …) ∣ #explainableScalars`.

The bad set is a disjoint union of full `⟨m⟩`-orbits, each of size exactly
`orderOf m = n / gcd(A−B, n)` for a thin monomial `μ_n` line.  Mechanism: the single-step dilation
invariance (`explainableScalars_rs_scalar_dilation.mp`) makes the bad set closed under multiplication
by the unit `m`, and `0 ∉ bad` makes the action free, so the in-tree orbit-count engine
`MCAEigenstack.orderOf_dvd_card_of_mul_mem` applies. -/
theorem explainableScalars_orderOf_dvd_card
    (domain : ι ↪ F) (k : ℕ) (σ : Equiv.Perm ι) (g : F) (hg0 : g ≠ 0)
    (hg : ∀ i, domain (σ i) = g * domain i)
    (δ : ℝ≥0) (u₀ u₁ : ι → F) {c₀ c₁ : F} (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0)
    (hu₀ : u₀ ∘ σ = c₀ • u₀) (hu₁ : u₁ ∘ σ = c₁ • u₁)
    (h0 : (0 : F) ∉ explainableScalars (F := F) (A := F)
        (ReedSolomon.code domain k : Set (ι → F)) δ u₀ u₁) :
    orderOf (Units.mk0 (c₀⁻¹ * c₁) (mul_ne_zero (inv_ne_zero hc₀) hc₁))
      ∣ (explainableScalars (F := F) (A := F)
          (ReedSolomon.code domain k : Set (ι → F)) δ u₀ u₁).card := by
  classical
  set bad : Finset F := explainableScalars (F := F) (A := F)
      (ReedSolomon.code domain k : Set (ι → F)) δ u₀ u₁ with hbaddef
  -- closure under multiplication by the unit m := c₀⁻¹·c₁ (from the single-step dilation iff)
  refine ProximityGap.MCAEigenstack.orderOf_dvd_card_of_mul_mem
    (α := Units.mk0 (c₀⁻¹ * c₁) (mul_ne_zero (inv_ne_zero hc₀) hc₁)) bad
    (fun γ hγ => ?_) h0
  -- `(Units.mk0 (c₀⁻¹·c₁) …) • γ = (c₀⁻¹·c₁)·γ`, which is bad by the dilation invariance
  rw [Units.val_mk0]
  rw [hbaddef] at hγ ⊢
  exact (explainableScalars_rs_scalar_dilation domain k σ g hg0 hg δ u₀ u₁ hc₀ hc₁
    hu₀ hu₁ γ).mp hγ

end ProximityGap.FarCosetExplosion

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.FarCosetExplosion.explainableScalars_orderOf_dvd_card

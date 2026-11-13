/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FarLineScalarDilation

/-!
# The coset structure forces a quantitative count law on the bad-scalar set (#444 census face / §R4)

`FarLineScalarDilation` proved (axiom-clean) that the RS monomial far-line bad-scalar set
`explainableScalars` is **invariant under multiplication by every power** of `m := c₀⁻¹·c₁`
(`= g^{A−B}` for a monomial line on `μ_n`), i.e. it is a union of `⟨m⟩`-cosets.  That was the
*forcing* (a set symmetry).  Until now there was **no quantitative consequence**: the coset
symmetry was never turned into a statement about the cardinality `#explainableScalars` — which is
exactly the `δ*`-governing distinct-`γ` count
(`BadScalarsEqPinned.badScalars_card_eq_pinnedScalars_card`,
`CensusScalarPartition.pinnedScalars`) the census weld consumes.

This file lands the first **count** consequence of the coset structure: an orbit lower bound.

* `mulOrbit_subset_of_invariant` / `mulOrbit_card` — the `⟨m⟩`-orbit of a **nonzero** scalar `γ`
  has cardinality **exactly `orderOf m`** (the action `j ↦ mʲ·γ` is injective on `Iio (orderOf m)`
  because `· * γ` is injective for `γ ≠ 0` and `j ↦ mʲ` is injective there), and it is **contained**
  in any `m`-power-invariant set that contains `γ`.

* `explainableScalars_orbit_card_le` (HEADLINE) — hence **if a NONZERO scalar is bad, then the
  bad-scalar set has at least `orderOf m = n / gcd(A−B, n)` elements**:
  `orderOf (c₀⁻¹·c₁) ≤ #explainableScalars`.  For a thin monomial `μ_n` line this is a `Θ(n)`
  *lower* bound on the distinct-`γ` count, forced purely by the cyclotomic coset symmetry, with
  **no averaging**: the orbit-explosion the §R4 route predicts, now an axiom-clean theorem.

PROBE: `scripts/probes/probe_coset_card_divis.py` — exact brute-force list-decode over THIN proper
`μ_n = 2^a` ((p−1)/n ≥ 2, NEVER n = q−1, primes incl. Fermat 17): the nonzero part of the bad set
has cardinality **divisible by `orderOf m`** (8/8), confirming the orbit structure; this file lands
the (cleanly provable) lower-bound half of that observation.

## Scope (rule 3 / rule 6, honesty contract)

This is a `Θ(n)` **LOWER** bound on the distinct-`γ` count, NOT an upper bound — it makes the census
floor *larger*, not smaller, so it does **not** by itself help the `δ*` ceiling.  Its value is
structural: it is the first quantitative consequence of the (otherwise purely qualitative) coset
symmetry, and it pins the exact granularity (`orderOf m`) at which the `P`-cap (the open
distinct-`γ` *upper* bound the census weld needs) must live: any `P`-cap is automatically a
multiple-of-`orderOf m` statement once a nonzero scalar is bad.  NOT a CORE / Conj-7.1 closure; the
`M(μ_n) ≤ C√(n log(p/n))`
CORE and the per-band distinct-`γ` *upper* bound `P` both stay OPEN.  No capacity / cliff-at-n/2 /
beyond-Johnson claim (this is a lower bound on a count, not an asymptotic δ* lean).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.FarCosetExplosion

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The `⟨m⟩`-orbit of `γ`** as a `Finset`: `{ mʲ · γ : j < orderOf m }`. -/
noncomputable def mulOrbit (m γ : F) : Finset F :=
  (Finset.range (orderOf m)).image (fun j => m ^ j * γ)

/-- **Orbit containment.** If a `Finset` `T` is invariant under multiplication by every power of `m`
(`∀ j, γ ∈ T → mʲ·γ ∈ T`) and contains `γ`, then it contains the whole `⟨m⟩`-orbit of `γ`. -/
theorem mulOrbit_subset_of_invariant {m γ : F} {T : Finset F} (hγ : γ ∈ T)
    (hinv : ∀ j : ℕ, m ^ j * γ ∈ T) :
    mulOrbit m γ ⊆ T := by
  intro x hx
  rw [mulOrbit, Finset.mem_image] at hx
  obtain ⟨j, -, rfl⟩ := hx
  exact hinv j

/-- **Exact orbit size.** For `γ ≠ 0` and `m` of finite multiplicative order (`orderOf m ≠ 0`),
the `⟨m⟩`-orbit of `γ` has cardinality **exactly `orderOf m`**.  Engine: `· * γ` is injective
(`mul_left_injective₀`) and `j ↦ mʲ` is injective on `Iio (orderOf m)`
(`pow_injOn_Iio_orderOf`), so `j ↦ mʲ·γ` is injective on `range (orderOf m)`. -/
theorem mulOrbit_card {m γ : F} (hγ : γ ≠ 0) (hm : orderOf m ≠ 0) :
    (mulOrbit m γ).card = orderOf m := by
  rw [mulOrbit, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  rw [Finset.coe_range, Set.mem_Iio] at hi hj
  -- mᶦ·γ = mʲ·γ and γ ≠ 0 ⟹ mᶦ = mʲ ⟹ i = j (i,j < orderOf m)
  have hpow : m ^ i = m ^ j := mul_right_cancel₀ hγ hij
  exact pow_injOn_Iio_orderOf hi hj hpow

/-- **HEADLINE — the orbit lower bound on the bad-scalar count.**  If a **nonzero** scalar `γ` is
bad for the RS monomial far line (with the scalar-dilation hypotheses of
`explainableScalars_rs_scalar_dilation_pow`), and `m := c₀⁻¹·c₁` has finite multiplicative order,
then the bad-scalar set has at least `orderOf m` elements:

  `orderOf (c₀⁻¹·c₁) ≤ #explainableScalars`.

For a thin monomial `μ_n` line (`m = g^{A−B}`, `orderOf m = n / gcd(A−B, n)`) this is a `Θ(n)`
*lower* bound on the `δ*`-governing distinct-`γ` count, forced by the cyclotomic coset symmetry with
no averaging.  Mechanism: the `_pow` invariance puts the whole order-`orderOf m` orbit of `γ` inside
the bad set, and the orbit has exactly `orderOf m` elements because `γ ≠ 0`. -/
theorem explainableScalars_orbit_card_le
    (domain : ι ↪ F) (k : ℕ) (σ : Equiv.Perm ι) (g : F) (hg0 : g ≠ 0)
    (hg : ∀ i, domain (σ i) = g * domain i)
    (δ : ℝ≥0) (u₀ u₁ : ι → F) {c₀ c₁ : F} (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0)
    (hu₀ : u₀ ∘ σ = c₀ • u₀) (hu₁ : u₁ ∘ σ = c₁ • u₁)
    (hm : orderOf (c₀⁻¹ * c₁) ≠ 0) {γ : F} (hγ0 : γ ≠ 0)
    (hγ : γ ∈ explainableScalars (F := F) (A := F)
        (ReedSolomon.code domain k : Set (ι → F)) δ u₀ u₁) :
    orderOf (c₀⁻¹ * c₁)
      ≤ (explainableScalars (F := F) (A := F)
          (ReedSolomon.code domain k : Set (ι → F)) δ u₀ u₁).card := by
  classical
  set m : F := c₀⁻¹ * c₁ with hmdef
  set bad : Finset F := explainableScalars (F := F) (A := F)
      (ReedSolomon.code domain k : Set (ι → F)) δ u₀ u₁ with hbaddef
  -- the orbit of γ is contained in `bad` (each power maps γ back in by `_pow`)
  have hinv : ∀ j : ℕ, m ^ j * γ ∈ bad := by
    intro j
    rw [hbaddef]
    exact (explainableScalars_rs_scalar_dilation_pow domain k σ g hg0 hg δ u₀ u₁ hc₀ hc₁
      hu₀ hu₁ j γ).mp hγ
  have hsub : mulOrbit m γ ⊆ bad := mulOrbit_subset_of_invariant (by rw [hbaddef]; exact hγ) hinv
  -- the orbit has exactly orderOf m elements (γ ≠ 0)
  have hcard : (mulOrbit m γ).card = orderOf m := mulOrbit_card hγ0 hm
  calc orderOf m = (mulOrbit m γ).card := hcard.symm
    _ ≤ bad.card := Finset.card_le_card hsub

end ProximityGap.FarCosetExplosion

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.FarCosetExplosion.mulOrbit_subset_of_invariant
#print axioms ProximityGap.FarCosetExplosion.mulOrbit_card
#print axioms ProximityGap.FarCosetExplosion.explainableScalars_orbit_card_le

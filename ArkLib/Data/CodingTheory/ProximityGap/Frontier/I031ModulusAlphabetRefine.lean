/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.I031DistinctPeriodCount

/-!
# I031 — the modulus alphabet refines the value alphabet (#444)

`I031DistinctPeriodCount` proves two unconditional metric-entropy facts over `Fₚ*`:
the distinct Gauss-period **value** alphabet `|{η_b}|` and the distinct **modulus** alphabet
`|{‖η_b‖}|` are *each* bounded by the orbit/coset count `(q−1)/n`
(`card_distinct_eta_le_orbitCount`, `card_distinct_etaNorm_le_orbitCount`). Both bounds factor
through the *same* coset-label collapse, so they are **stated in parallel** but their mutual
relationship is never recorded.

This file adds the one structural link between them:

> `|{‖η_b‖ : b ≠ 0}| ≤ |{η_b : b ≠ 0}|` — the modulus alphabet is **no larger** than the value
> alphabet (the norm map `ℂ → ℝ` can only *merge* values, never split them).

Mechanism: `b ↦ ‖η_b‖` is the composite `‖·‖ ∘ (b ↦ η_b)`, so its image is the `‖·‖`-image of the
value image; `Finset.card_image_le` then gives the bound.

## Probe (validated before formalizing; rule 2, rule 4)

`scripts/probes/probe_alphabet_thickness_invariance.py` (EXACT `F_p`, PROPER thin `μ_n`, `n=2^a`,
`n ∣ p−1`, `(p−1)/n ≥ 2`, primes incl. `p ≫ n³` and Fermat 257, NEVER `n=q−1`) measures both alphabets
per coset representative:

* the **value** alphabet is `= (q−1)/n` *exactly* in every config (NO cross-coset value collision —
  the period map is injective on coset labels at every prime tested, 160/160);
* the **modulus** alphabet is `≤` the value alphabet and **occasionally strictly smaller** (`n=32`,
  `p=32801`: `#{η_b}=1025` but `#{‖η_b‖}=1024` — a conjugate pair `η, η̄` merges under `‖·‖`).

So the inequality this file proves is **genuinely sharp** (the in-tree parallel `≤ (q−1)/n` bounds do
not capture that the modulus alphabet can drop below the value alphabet).

## Honesty (rules 1, 3, 4, 6)

* NOT a CORE closure, NOT a refutation of CORE. A structural refinement of the I031 metric-entropy
  chain: `|{‖η_b‖}| ≤ |{η_b}| ≤ (q−1)/n`, with the first `≤` now in-tree and probe-shown sharp.
* **Constraint content (rule 4):** the alphabet *size* — value or modulus — is `(q−1)/n` (resp. one
  less) IDENTICALLY in the thin prize regime and the thick `β≈2.3` control (probe: thin and thick give
  the same `(q−1)/n`). The alphabet *count* is therefore **thickness-invariant** and carries **no
  thinness signal**; by rule 3 it cannot be a standalone prize lever. Any `log(q/n)` metric entropy
  the I031 union bound spends is the alphabet log `= log((q−1)/n)` exactly — there is no sub-`(q−1)/n`
  collapse to harvest (the only shrink is an `O(1)` conjugate merge in the modulus alphabet, which does
  not move `log`). The thinness signal must live in the *magnitudes* of the `(q−1)/n` distinct periods
  (the open sup-vs-`√n`-floor gap), not in their *count*. Logged to `DISPROOF_LOG.md`.
* NON-MOMENT (pure image-cardinality / composite-map fact), EXTEND-proven (sits directly on
  `card_distinct_etaNorm_le_orbitCount` + `card_distinct_eta_le_orbitCount`). ONE sweep, ONE commit.
  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. CORE
  `M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN.
-/

open Finset Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.I031DilationOrbitReduction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The modulus alphabet is no larger than the value alphabet.** The number of distinct
Gauss-period *moduli* `‖η_b‖` over the nonzero frequencies is at most the number of distinct
*values* `η_b`. The modulus map `b ↦ ‖η_b‖` factors as `‖·‖ ∘ (b ↦ η_b)`, so its image is the
`‖·‖`-image of the value image; `card_image_le` finishes. (Probe-shown sharp: the inequality can be
strict via a conjugate `η, η̄` merge under `‖·‖`.) -/
theorem card_distinct_etaNorm_le_card_distinct_eta (ψ : AddChar F ℂ) {n : ℕ} :
    ((nonzeroFreqs F).image (fun b => ‖eta ψ (nthRootsFinset n (1 : F)) b‖)).card
      ≤ ((nonzeroFreqs F).image (eta ψ (nthRootsFinset n (1 : F)))).card := by
  classical
  -- `(fun b => ‖η_b‖)` = `‖·‖ ∘ η`, so its image is the `‖·‖`-image of the value image.
  have hcomp :
      (nonzeroFreqs F).image (fun b => ‖eta ψ (nthRootsFinset n (1 : F)) b‖)
        = ((nonzeroFreqs F).image (eta ψ (nthRootsFinset n (1 : F)))).image (fun z : ℂ => ‖z‖) :=
    (Finset.image_image (g := fun z : ℂ => ‖z‖) (f := eta ψ (nthRootsFinset n (1 : F)))).symm
  rw [hcomp]
  exact Finset.card_image_le

/-- **The refined two-sided metric-entropy chain.** Combining the modulus-refinement with the
in-tree orbit-count bound: the distinct-modulus alphabet is `≤` the distinct-value alphabet, which is
`≤ (q−1)/n`. This makes `|{‖η_b‖}| ≤ |{η_b}| ≤ (q−1)/n` a single citable chain (the prize objective's
alphabet is bounded by the value alphabet, not just independently by the coset count). -/
theorem card_distinct_etaNorm_le_eta_le_orbitCount {ψ : AddChar F ℂ} {n : ℕ} {ζ : F}
    (hζprim : IsPrimitiveRoot ζ n) (hn : 0 < n) :
    ((nonzeroFreqs F).image (fun b => ‖eta ψ (nthRootsFinset n (1 : F)) b‖)).card
        ≤ ((nonzeroFreqs F).image (eta ψ (nthRootsFinset n (1 : F)))).card
      ∧ ((nonzeroFreqs F).image (eta ψ (nthRootsFinset n (1 : F)))).card
        ≤ (Fintype.card F - 1) / n :=
  ⟨card_distinct_etaNorm_le_card_distinct_eta ψ, card_distinct_eta_le_orbitCount hζprim hn⟩

end ArkLib.ProximityGap.I031DilationOrbitReduction

/-! ## Axiom audit -/
open ArkLib.ProximityGap.I031DilationOrbitReduction in
#print axioms card_distinct_etaNorm_le_card_distinct_eta
open ArkLib.ProximityGap.I031DilationOrbitReduction in
#print axioms card_distinct_etaNorm_le_eta_le_orbitCount

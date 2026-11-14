/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SchurLagrangeBridge
import Mathlib.Algebra.CharP.Frobenius

/-!
# Spec S3 — ring-hom / Galois / Frobenius naturality of the divided-difference power (#444)

⚠️ **STATUS — substrate, NOT a δ* pin** (same warning as the sibling `_SpecS1`). This file
re-derives a genuine, reusable STRUCTURAL FACT — the *functoriality* (naturality) of the
divided-difference power `dividedDifferencePow s v b` under a field homomorphism `σ : F →+* K`:

  `σ (dividedDifferencePow s v b) = dividedDifferencePow s (σ ∘ v) b`.

This is the lemma the BCHKS correct-object dossier
(`docs/kb/deltastar-444-BCHKS-correct-object-and-attack-2026-06-16.md` §D4) names as the lost
`_SpecS3` substrate — *"Galois/Frobenius equivariance `σ(h_b(R)) = h_b(σR)` via the hypothesis-free
`dividedDifferencePow_map` (lost to a concurrent-reset clobber; the naturality lemma is worth
re-deriving as substrate)."* It is the FUNCTORIAL counterpart of `_SpecS1`'s rotation-equivariance
`h_r(ζ·R) = ζ^r·h_r(R)` (which scales a single value); here we transport the WHOLE value across a
ring homomorphism. It powers the good-prime / cyclotomic-collision counting (reduction-mod-`p` is a
ring hom `ℤ[ζ] → F_p`; the Frobenius `x ↦ x^p` is the Galois generator), letting one push a
char-0 divided-difference identity to char-`p` and conjugate by Frobenius.

The headline (`dividedDifferencePow_ringHom`) is **HYPOTHESIS-FREE**: it needs neither injectivity
of `v` on `s` nor injectivity of `σ`, because the inverse-of-zero convention (`0⁻¹ = 0`, `map_inv₀`)
cancels consistently on both sides. The Galois/Frobenius corollaries are direct specializations.

## What it lands [PROVEN, axiom-clean]
* `dividedDifferencePow_ringHom` — naturality under any field hom `σ : F →+* K` (hypothesis-free).
* `dividedDifferencePow_comp` — the `(σ ∘ v)` packaging used by the reduction-mod-`p` counting.
* `dividedDifferencePow_galois` / `dividedDifferencePow_frobenius` — the Galois-automorphism and
  Frobenius (`x ↦ x^p` via `frobenius`) specializations.

## Honest scope
Substrate (functoriality of the in-tree symmetric-function value), NOT a lower bound on δ*. The
spectrum route it once fed is REFUTED as a δ* pin (§D4); this is kept as honest reusable algebra
for the good-prime / cyclotomic-collision residual, exactly as `_SpecS1` is kept. NON-MOMENT,
ASYMPTOTIC-GUARD-COMPLIANT (a structural functoriality fact; no capacity/beyond-Johnson claim;
cliff-at-n/2 untouched).

Probe: `scripts/probes/probe_dd_naturality.py` — `σ` = nontrivial Frobenius on `F_{p²}`,
distinct node sets, `b = 0..12`: **0 fails / 4000 tests**.
-/

set_option autoImplicit false
set_option linter.style.longLine false

open Finset

namespace ArkLib.ProximityGap.SpecS3

open ProximityGap.SchurLagrange

variable {F K : Type*} [Field F] [Field K] {ι : Type*} [DecidableEq ι]

/-- **Ring-hom naturality of the divided-difference power (the lost `_SpecS3` substrate).**
For any field homomorphism `σ : F →+* K`, a node set `s` and node-value map `v : ι → F`,

  `σ (dividedDifferencePow s v b) = dividedDifferencePow s (fun i => σ (v i)) b`.

This is the functoriality of the divided difference: applying `σ` to
`Σ_{i∈s} (v i)^b · (∏_{j∈erase i}(v i − v j))⁻¹` distributes through the sum (`map_sum`), the
product/power (`map_mul`, `map_pow`, `map_prod`), the subtraction (`map_sub`) and the inverse
(`map_inv₀`, the convention `0⁻¹ = 0` cancels on both sides), yielding the same expression with
each `v i` replaced by `σ (v i)`. **Hypothesis-free** — no injectivity of `v` or `σ` is needed. -/
theorem dividedDifferencePow_ringHom (σ : F →+* K) (s : Finset ι) (v : ι → F) (b : ℕ) :
    σ (dividedDifferencePow s v b) = dividedDifferencePow s (fun i => σ (v i)) b := by
  classical
  unfold dividedDifferencePow
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul, map_pow, map_inv₀, map_prod]
  refine congrArg (fun w => (σ (v i)) ^ b * w⁻¹) ?_
  exact Finset.prod_congr rfl (fun j _ => by rw [map_sub])

/-- **`(σ ∘ v)` packaging — the reduction-mod-`p` form.** Identical content with the composed map
written as `σ ∘ v`; this is the shape the good-prime counting (reduction `ℤ[ζ] → F_p` is a ring
hom) actually consumes. -/
theorem dividedDifferencePow_comp (σ : F →+* K) (s : Finset ι) (v : ι → F) (b : ℕ) :
    σ (dividedDifferencePow s v b) = dividedDifferencePow s (σ ∘ v) b :=
  dividedDifferencePow_ringHom σ s v b

/-- **Galois-automorphism equivariance.** For a field automorphism `σ : F ≃+* F` (a `RingEquiv`,
e.g. an element of `Gal(F/k)`), the divided difference is equivariant: conjugating the nodes by `σ`
conjugates the value by `σ`. This is the Galois-equivariance the cyclotomic-collision counting
uses (`σ` an element of `Gal(ℚ(ζ)/ℚ)` acting on the roots of unity). -/
theorem dividedDifferencePow_galois (σ : F ≃+* F) (s : Finset ι) (v : ι → F) (b : ℕ) :
    σ (dividedDifferencePow s v b) = dividedDifferencePow s (fun i => σ (v i)) b :=
  dividedDifferencePow_ringHom (σ : F →+* F) s v b

/-- **Frobenius equivariance (`x ↦ x^p`).** Over a field `F` with `ExpChar F p` (e.g. prime
characteristic `p`), the Frobenius endomorphism `frobenius F p : F →+* F` commutes with the divided
difference: `(dividedDifferencePow s v b)^p = dividedDifferencePow s (fun i => (v i)^p) b`. This is
the `σ = Frobenius` case of the naturality — the exact Galois generator of `F_{p^k}/F_p`. -/
theorem dividedDifferencePow_frobenius (p : ℕ) [ExpChar F p]
    (s : Finset ι) (v : ι → F) (b : ℕ) :
    (dividedDifferencePow s v b) ^ p = dividedDifferencePow s (fun i => (v i) ^ p) b := by
  have h := dividedDifferencePow_ringHom (frobenius F p) s v b
  simpa only [frobenius_def] using h

end ArkLib.ProximityGap.SpecS3

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SpecS3.dividedDifferencePow_ringHom
#print axioms ArkLib.ProximityGap.SpecS3.dividedDifferencePow_comp
#print axioms ArkLib.ProximityGap.SpecS3.dividedDifferencePow_galois
#print axioms ArkLib.ProximityGap.SpecS3.dividedDifferencePow_frobenius

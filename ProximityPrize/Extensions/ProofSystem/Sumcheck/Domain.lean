/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Sumcheck.Domain

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Logic.Embedding.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases

/-!
# Sum-check evaluation domains

The sum-check protocol reduces a claim about a sum of a polynomial over an evaluation domain. The
*domain* is, in general, a product `∏ᵢ Dᵢ` of per-coordinate evaluation sets `Dᵢ ⊆ R`, and —
crucially — **the `Dᵢ` may differ from one coordinate to the next**. This file defines that domain
abstraction once, so both the oracle-mode (`Sumcheck.Spec`) and witness-mode (`Sumcheck.Structured`)
sum-checks can consume it, so different protocols can pick the domain best suited to them on a
case-by-case basis (Boolean hypercube, SWIRL-style hyperprism, …).

## Main definitions

* `SumcheckDomain R k` — a per-coordinate evaluation-domain family over `k` coordinates: a size
  `mᵢ` and an injection `Fin mᵢ ↪ R` for each coordinate `i : Fin k`.
* `SumcheckDomain.points` / `SumcheckDomain.cube` — the per-coordinate domain as a `Finset R`, and
  the dependent product cube `∏ᵢ (univ.map (embed i))` as a `Finset (Fin k → R)`.
* `SumcheckDomain.uniform D₀ k` — the same `m`-point embedding in every coordinate. Its `cube` is
  *definitionally* the homogeneous `(univ.map D₀) ^ᶠ k` used today, so `Sumcheck.Spec` can migrate
  onto this abstraction with no semantic change.
* `SumcheckDomain.prepend` — prepend a coordinate (used to build heterogeneous domains).
* `boolDomain R k` — the Boolean hypercube `{0,1}^k` (the canonical `0 ↦ 0, 1 ↦ 1` embedding in
  every coordinate). The plain multilinear sum-check instance.
* `hyperprismDomain R Dskip k` — SWIRL's hyperprism `𝔻 = D × {0,1}^k`: coordinate `0` over a
  `2^ℓ`-point univariate "skip" domain `Dskip`, the remaining `k` coordinates Boolean.

The summation-domain abstraction is intentionally **degree-free**: the per-round polynomial degree
(`d`, or a per-variable / prismalinear bound) is a separate parameter, kept out of this module.
-/

universe u

namespace SumcheckDomain

variable {R : Type u} {k m : ℕ}

/-- Telescoping identity (the core sum-check completeness step): summing over the `(k+1)`-coordinate
cube equals summing coordinate `0` over its domain, then the rest over the tail cube. This is the
`piFinset` "cons decomposition" `𝔻^{k+1} ↔ 𝔻₀ × 𝔻^k`. -/
theorem sum_cube_succ {M : Type*} [AddCommMonoid M] (D : SumcheckDomain R (k + 1))
    (f : (Fin (k + 1) → R) → M) :
    ∑ x ∈ D.cube, f x = ∑ b ∈ D.points 0, ∑ y ∈ D.tail.cube, f (Fin.cons b y) := by
  rw [← Finset.sum_product']
  have hcube : D.cube
      = (D.points 0 ×ˢ D.tail.cube).map (Fin.consEquiv (fun _ : Fin (k + 1) => R)).toEmbedding := by
    have htail : Fin.tail D.points = D.tail.points := by funext i; rfl
    simpa [cube, htail] using
      Finset.filter_piFinset_eq_map_consEquiv (S := D.points) (fun _ => True)
  rw [hcube, Finset.sum_map]
  rfl

/-- Drop the *last* coordinate of a `(k+1)`-coordinate domain family. The dual of `tail`; used by
the structured per-round sum-check, whose round univariate keeps the **last** surviving variable as
the indeterminate, so the marginal sum splits off coordinate `Fin.last`. -/
def init (D : SumcheckDomain R (k + 1)) : SumcheckDomain R k where
  size := fun i => D.size i.castSucc
  embed := fun i => D.embed i.castSucc

@[simp] lemma points_init (D : SumcheckDomain R (k + 1)) (i : Fin k) :
    D.init.points i = D.points i.castSucc := rfl

@[simp] lemma init_uniform (D₀ : Fin m ↪ R) (k : ℕ) :
    (uniform D₀ (k + 1)).init = uniform D₀ k := rfl

@[simp] lemma points_last_uniform (D₀ : Fin m ↪ R) (k : ℕ) :
    (uniform D₀ (k + 1)).points (Fin.last k) = Finset.univ.map D₀ := rfl

/-- Telescoping identity splitting off the **last** coordinate (dual of `sum_cube_succ`): summing
over the `(k+1)`-coordinate cube equals summing coordinate `Fin.last` over its domain, then the rest
over the `init` cube, recombined via `Fin.snoc`. -/
theorem sum_cube_snoc {M : Type*} [AddCommMonoid M] (D : SumcheckDomain R (k + 1))
    (f : (Fin (k + 1) → R) → M) :
    ∑ z ∈ D.cube, f z
      = ∑ b ∈ D.points (Fin.last k), ∑ y ∈ D.init.cube, f (Fin.snoc y b) := by
  rw [← Finset.sum_product']
  have hcube : D.cube
      = (D.points (Fin.last k) ×ˢ D.init.cube).map
          (Fin.snocEquiv (fun _ : Fin (k + 1) => R)).toEmbedding := by
    have h := Finset.filter_piFinset_eq_map_snocEquiv (S := D.points) (fun _ => True)
    have hinit : Fin.init D.points = D.init.points := by funext i; rfl
    simpa [cube, hinit] using h
  rw [hcube, Finset.sum_map]
  rfl

end SumcheckDomain

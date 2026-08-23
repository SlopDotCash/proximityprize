/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# R4 lane F: the cross-parity split of a spurious config is a tautology (#407)

## Background

A **spurious config** in the m = 2 gap analysis is an antipodal-free `U ⊆ μ_n` with the two
power-sum relations
```
e₁(U) = ∑_{u∈U} u = 0   and   e₃(U) = ∑_{u∈U} u³ = 0   (in F).
```
Over `ℂ` no such `U` exists (Lam–Leung); over `F_p` they appear at small saturated primes (the
canonical data is the `64` configs at `n = 64, p = 2113`).

Lane F probes a conjectured *structural* feature of this defect locus: a **cross-parity relation**
`A ≡ -g·B` holding for `96–100%` of defects, where `A, B` are the two *halves* of `U` under some
splitting and `g` a fixed ring element. The hope was that `g` encodes nontrivial structure (a fixed
Galois/Frobenius element, an element of `μ_n`, …) that could be turned into an independent handle on
the open dyadic Gaussian-period sup-norm wall (`DyadicDeviationDecay`, the BGK cross-term).

## What this file proves (the honest verdict: the literal claim is VACUOUS)

The numeric probes (`scripts/probes/probe_407_laneF_crossparity_leak.py` and its `_nontrivial`
sibling) report, at **every** tested `(n, p)` including the canonical `n = 64, p = 2113`, that the
unique solving element is `g = 1` for **100%** of defects under every complementary splitting. This
file proves the exact reason, abstractly and axiom-clean:

* `splitSum_neg` / `crossParity_holds_g_one` — for **any** partition `U = A ⊔ B` of a config with
  `e₁(U) = 0`, the two part-sums satisfy `∑_A u = -(1 • ∑_B u)`, i.e. the relation `A = -g·B` holds
  with `g = 1`, **unconditionally** (no choice of `g`, no hypothesis beyond `e₁ = 0`).

* `crossParity_solving_g_eq_one_iff` — when `∑_B u ≠ 0`, the unique element `g` with
  `∑_A u = -g·(∑_B u)` (namely `g = -(∑_A u)/(∑_B u)`) equals `1` **iff** `e₁(U) = 0`. So the
  "cross-parity leak" is *logically equivalent to the defining relation* `e₁ = 0`: it carries
  **zero** information beyond the definition of a spurious config.

* `crossParity_vacuous` — packaging: on the spurious locus (`e₁ = 0`) the cross-parity relation with
  the empirically-observed `g = 1` is a **tautology** (always true), hence cannot be a nontrivial
  structural constraint.

## Consequence for the lane (gap localization, recorded in `DISPROOF_LOG.md`)

The literal `96–100%` "leak" is `g = 1`, i.e. `A = -B`, i.e. a restatement of `e₁ = 0`. The
*nontrivial* variants probed (a fixed `g` linking **different power-levels**, e.g.
`∑_A u³ = -g·∑_A u`, or the `e₂` bad-scalar ratio) are **refuted numerically**: the solving `g`
takes `Θ(#defects)` distinct values (`32` distinct over `64` defects at `n = 64`; top value covers
`3%`), so there is no fixed cross-parity element. Lane F therefore yields **no independent handle**
on the dyadic cross term `δ`; the only genuine structural object remains the butterfly
cross-correlation `2 Re(period · conj(period'))`, already named as the open
`ProximityGap.Frontier.DyadicDeviationDecay` / BGK sup-norm wall.

Everything here is proven, no `sorry`/`axiom`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- Lam, Leung. *On vanishing sums of roots of unity*. (no spurious config over `ℂ`).
- BGK: Bourgain–Glibichuk–Konyagin, character sums over subgroups (the open sup-norm wall).
-/

open Finset

namespace ProximityGap.Frontier.CrossParitySplit

variable {F : Type*}

section Ring

variable [CommRing F] [DecidableEq F]

/-- The sum of `f` over a config, indexed by a finite set `U`; this is `e₁` when `f = id`. -/
def configSum (f : F → F) (U : Finset F) : F := ∑ u ∈ U, f u

/-- **Split additivity.** For any partition `U = A ⊔ B` (`A, B` disjoint, union `U`), the config-sum
splits as `∑_U f = ∑_A f + ∑_B f`. The combinatorial backbone of every "two halves" splitting. -/
theorem configSum_split (f : F → F) {A B U : Finset F}
    (hdisj : Disjoint A B) (hunion : A ∪ B = U) :
    configSum f U = configSum f A + configSum f B := by
  unfold configSum
  rw [← hunion, Finset.sum_union hdisj]

/-- **The cross-parity relation holds with `g = 1`, unconditionally.** If the config has vanishing
power-sum `∑_U f = 0` (e.g. `f = id`, `e₁ = 0`), then for *any* split `U = A ⊔ B` the two part-sums
are negatives: `∑_A f = -(∑_B f)`. This is the abstract reason the probe sees the unique solving
element `g = 1` for 100% of defects under every complementary splitting. -/
theorem splitSum_neg (f : F → F) {A B U : Finset F}
    (hdisj : Disjoint A B) (hunion : A ∪ B = U) (hvanish : configSum f U = 0) :
    configSum f A = -(configSum f B) := by
  have h := configSum_split f hdisj hunion
  rw [hvanish] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- **The cross-parity relation `A = -g·B` with the empirically-observed `g = 1`.** Restates
`splitSum_neg` in the literal probe form `∑_A f = -(g · ∑_B f)` with `g = 1`. Holds for every split
of every config with `∑_U f = 0` — no hypothesis, no choice. This is the formal content of "the
relation holds for 100% of defects with `g = 1`". -/
theorem crossParity_holds_g_one (f : F → F) {A B U : Finset F}
    (hdisj : Disjoint A B) (hunion : A ∪ B = U) (hvanish : configSum f U = 0) :
    configSum f A = -((1 : F) * configSum f B) := by
  rw [one_mul]; exact splitSum_neg f hdisj hunion hvanish

end Ring

section Field

variable [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- **Uniqueness of the solving element.** Over a field, if `∑_B f ≠ 0`, there is a *unique* `g` with
`∑_A f = -(g · ∑_B f)`, namely `g = -(∑_A f) / (∑_B f)`. (The probe computes exactly this `g`.) -/
theorem crossParity_unique_g (f : F → F) {A B : Finset F} (hB : configSum f B ≠ 0) (g : F) :
    configSum f A = -(g * configSum f B) ↔ g = -(configSum f A) / configSum f B := by
  constructor
  · intro h
    rw [eq_div_iff hB]
    linear_combination h
  · intro h
    rw [h, div_mul_cancel₀ _ hB]
    ring

/-- **The leak is logically equivalent to the defining relation `e₁ = 0`.** Over a field, for any
split `U = A ⊔ B` with `∑_B f ≠ 0`, the unique solving element `g = -(∑_A f)/(∑_B f)` equals `1` **iff**
the config power-sum vanishes, `∑_U f = 0`. Hence the empirically-observed `g = 1` carries *no*
information beyond the spurious-config relation it is supposed to "leak": it is a restatement of it.
This is the precise machine-checked refutation of the lane F cross-parity-leak claim. -/
theorem crossParity_solving_g_eq_one_iff (f : F → F) {A B U : Finset F}
    (hdisj : Disjoint A B) (hunion : A ∪ B = U) (hB : configSum f B ≠ 0) :
    (-(configSum f A) / configSum f B = 1) ↔ configSum f U = 0 := by
  rw [div_eq_one_iff_eq hB, configSum_split f hdisj hunion]
  constructor
  · intro h; rw [← h]; ring
  · intro h; linear_combination -h

/-- **Vacuity package.** On the spurious locus (`∑_U f = 0`) the cross-parity relation with the
observed element `g = 1` is a *tautology*: it holds for every split, and its solving element is `1`
*precisely because* `e₁ = 0`. So lane F's `96–100%` "leak" is the defining relation in disguise — it
is not a nontrivial structural constraint and supplies no independent handle on the dyadic cross
term. -/
theorem crossParity_vacuous (f : F → F) {A B U : Finset F}
    (hdisj : Disjoint A B) (hunion : A ∪ B = U) (hvanish : configSum f U = 0) :
    -- the relation holds with g = 1 …
    configSum f A = -((1 : F) * configSum f B) ∧
    -- … and, whenever B is nondegenerate, g = 1 is *forced by* e₁ = 0 (equivalence)
    (configSum f B ≠ 0 → (-(configSum f A) / configSum f B = 1)) := by
  refine ⟨crossParity_holds_g_one f hdisj hunion hvanish, fun hB => ?_⟩
  exact (crossParity_solving_g_eq_one_iff f hdisj hunion hB).mpr hvanish

end Field

end ProximityGap.Frontier.CrossParitySplit

#print axioms ProximityGap.Frontier.CrossParitySplit.configSum_split
#print axioms ProximityGap.Frontier.CrossParitySplit.splitSum_neg
#print axioms ProximityGap.Frontier.CrossParitySplit.crossParity_holds_g_one
#print axioms ProximityGap.Frontier.CrossParitySplit.crossParity_unique_g
#print axioms ProximityGap.Frontier.CrossParitySplit.crossParity_solving_g_eq_one_iff
#print axioms ProximityGap.Frontier.CrossParitySplit.crossParity_vacuous

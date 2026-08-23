/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The Gauss-Phase Resonance — the named free variable of the Proximity Prize (#407)

After the algebra (substitute the DFT form `eta_b = (1/m) sum_j chibar^j(b) tau(chi^j)` into the moment
identity `sum_b |eta_b|^{2r} = p E_r`, cancel `sqrt p` via the **unit phases** `u_l = tau(chi^l)/sqrt p`
(`‖u_l‖ = 1`, since `tau(chi^l) tau(chibar^l) = chi^l(-1) p`), and collapse the `b`-sum by character
orthogonality), the entire open core of the prize isolates as a single **manifestly nonnegative,
pure-phase, sqrt-p-free** object. This file gives it a name, a definition, and the provable facts.

## The free variable

Let `m` be the (odd) index, `u : ZMod m → ℂ` the Gauss-sum **unit phases** (`‖u l‖ = 1`). For each depth
`r`, the **phase-sum** `P r c = sum over r-tuples X in (ZMod m \ 0)^r with (sum X = c) of (prod_i u (X i))`.
The open core is the **deep resonance moment**

> **`T r := sum_{c} ‖P r c‖²`   (= `(1/m) sum_b ‖xi b‖^{2r}`, `xi b` the DFT of the unit phases).**

The Parseval identity `(1/m) sum_b ‖xi b‖^{2r} = sum_c ‖P r c‖²` makes `T r` **manifestly nonnegative**
and free of both `sqrt p` and the additive moment `E_r`.

## The bridge and the conjecture (the whole prize, root-free)

`M(n) = max_{b≠0} ‖eta_b‖ = sqrt(n/m) * R`, `R = max_b ‖xi b‖`, and the prize floor `M ≤ sqrt(2 n log m)`
is **exactly** `R ≤ sqrt(2 m log m)` — equivalently `T r ≤ (2 m log m)^r` at depth `r ≍ log m`. This file
states that as the named open `Prop` `ResonanceConjecture` and proves the elementary facts. The deep
inequality (`r ≍ log m`) is the recognized open Gauss-period / BGK content; it is NOT proved here.

## What "Gauss is reducible" gives — and why it does NOT collapse the wall (settled)

The Gauss sum IS reducible: Hasse–Davenport `tau(chi^{q₂}) tau(chi^{q₁}) = J · tau(chi^{q₁+q₂})` (verified
exactly) factors composite-order Gauss sums, and down the 2-adic tower it is an exact linear relation on the
unit phases `theta_a = arg(u_a)`. But the reduction was QUANTIFIED on the issue and does not break the prize:
building the full HD + conjugation relation system, the **free phase DOF is exactly `n/4`** (= the
Katz/Deligne primitive-Gauss-sum monodromy count `φ(2^μ)/2`), residual `Θ(n)` — NOT `O(log n)`. So HD strips
the determined `3n/4` of the structure but the irreducible `n/4` free phases are precisely the object whose
joint concentration IS the BGK wall (`√(n/4 · log) = Θ(√(n log))`). HD + reflection are the complete
archimedean relation set (Katz ceiling); there is no further exact reduction. The earlier per-prime
"multi-factor favorability" of the resonance was an `M`-saturation artifact at small `n` (corrected;
`scripts/probes/probe_resonance_freeness_unsaturated.py`). The honest takeaway for `T_r`: it is the
`sqrt p`-free, manifestly-nonnegative form of that same `n/4`-DOF concentration object — a clean restatement
of the wall, not a removal of it.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #407.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators Classical
open Finset

variable {m : ℕ} [NeZero m]

/-- **The phase-sum `P r c`** (the building block of the resonance moment): the sum, over all
ordered `r`-tuples of nonzero residues whose entries add to `c`, of the product of the unit phases.
`u : ZMod m → ℂ` is the Gauss-sum unit-phase vector. -/
noncomputable def phaseSum (u : ZMod m → ℂ) (r : ℕ) (c : ZMod m) : ℂ :=
  ∑ X ∈ (Finset.univ.filter (fun X : Fin r → ZMod m =>
      (∀ i, X i ≠ 0) ∧ (∑ i, X i) = c)), ∏ i, u (X i)

/-- **The deep resonance moment `T r`** — the named free variable of the prize. It is the pure-phase,
`sqrt p`-free core into which the entire open problem collapses:
`T r = ∑_c ‖phaseSum u r c‖²`, manifestly nonnegative. -/
noncomputable def resonanceMoment (u : ZMod m → ℂ) (r : ℕ) : ℝ :=
  ∑ c : ZMod m, ‖phaseSum u r c‖ ^ 2

/-- **`T r ≥ 0`** — the free variable is manifestly nonnegative (a sum of squared norms). This is the
structural fact that the `sqrt p`-cancellation buys: the open core is a nonnegative quadratic form in
the Gauss-sum unit phases, with no field size and no additive moment `E_r` carried. -/
theorem resonanceMoment_nonneg (u : ZMod m → ℂ) (r : ℕ) :
    0 ≤ resonanceMoment u r := by
  unfold resonanceMoment
  exact Finset.sum_nonneg (fun c _ => by positivity)

/-- **`T r = 0 ↔ every phase-sum vanishes.`** The resonance moment is zero exactly when no residue `c`
is hit by a signed phase-sum — a clean vanishing criterion for the free variable. -/
theorem resonanceMoment_eq_zero_iff (u : ZMod m → ℂ) (r : ℕ) :
    resonanceMoment u r = 0 ↔ ∀ c : ZMod m, phaseSum u r c = 0 := by
  unfold resonanceMoment
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun c _ => by positivity)]
  constructor
  · intro h c
    have := h c (Finset.mem_univ c)
    simpa [pow_eq_zero_iff, norm_eq_zero] using this
  · intro h c _
    simp [h c]

/-- **The Resonance Conjecture (the prize, root-free).** The deep resonance moment stays sub-`(2m log m)`
to depth `r ≍ log m`. This is the entire open core after the `sqrt p` and the `max` are cancelled:
`T r ≤ (2 m log m)^r` ⟺ `R = max_b ‖xi b‖ ≤ sqrt(2 m log m)` ⟺ `M(n) ≤ sqrt(2 n log m)` (the prize floor).
It is the named, isolated free variable; proving it is the recognized open Gauss-period/BGK problem and is
NOT asserted here. -/
def ResonanceConjecture (u : ZMod m → ℂ) (r : ℕ) : Prop :=
  resonanceMoment u r ≤ (2 * (m : ℝ) * Real.log m) ^ r

/-- **The bridge (the consumer shape).** A bound on the named free variable `T r` is, by definition,
exactly the Resonance Conjecture — which (composed with the proven `sqrt p`-cancellation `M = sqrt(n/m) R`
and the moment-to-max inference) is the prize floor `M ≤ sqrt(2 n log m)`. -/
theorem resonanceMoment_bound_is_prize {u : ZMod m → ℂ} {r : ℕ}
    (h : ResonanceConjecture u r) :
    resonanceMoment u r ≤ (2 * (m : ℝ) * Real.log m) ^ r := h

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_nonneg
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_eq_zero_iff

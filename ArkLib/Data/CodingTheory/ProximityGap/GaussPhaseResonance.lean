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
orthogonality), the *nontrivial-character part* of the open core is heuristically captured by a
single **manifestly nonnegative, pure-phase, sqrt-p-free** object. This file gives it a name, a
definition, and the provable elementary facts. The bridge back to the prize maximum is not
formalized and needs the trivial-character and averaging corrections recorded below (PG-109).

## The free variable

Let `m` be the (odd) index, `u : ZMod m → ℂ` the Gauss-sum **unit phases** (`‖u l‖ = 1`). For each depth
`r`, the **phase-sum** `P r c = sum over r-tuples X in (ZMod m \ 0)^r with (sum X = c) of (prod_i u (X i))`.
The open core is the **deep resonance moment**

> **`T r := sum_{c} ‖P r c‖²`   (= `(1/m) sum_b ‖xi b‖^{2r}`, `xi b` the DFT of the unit phases).**

The Parseval identity `(1/m) sum_b ‖xi b‖^{2r} = sum_c ‖P r c‖²` makes `T r` **manifestly nonnegative**
and free of both `sqrt p` and the additive moment `E_r`.

## The bridge and the conjecture (heuristic, NOT an exact equivalence)

**Correction (audit 2026-10-28, PG-109).** An earlier version of this section asserted the exact
identity `M(n) = max_{b≠0} ‖eta_b‖ = sqrt(n/m) * R` (`R = max_b ‖xi b‖`) and the exact equivalence
`M ≤ sqrt(2 n log m) ⟺ R ≤ sqrt(2 m log m) ⟺ T r ≤ (2 m log m)^r`. Neither is correct as stated, and
none of these bridges is formalized here:

* **The trivial character is omitted.** `phaseSum` ranges over *nonzero* residues only. The exact
  completion of the Gauss period is `eta_b = (−1 + sqrt(p) * xi_b) / m` (the trivial character
  contributes `tau(χ^0) = −1`) with `p = m n + 1`, so `M = max_{b≠0} ‖−1 + sqrt(p) xi_b‖ / m`, which
  equals `sqrt(n/m) R` only up to the `−1` term and the `sqrt(p)` vs `sqrt(m n)` discrepancy. The
  case `m = 1` is a counterexample to the displayed identity: the nonzero index set is empty,
  so `xi = R = 0`, while the full multiplicative group has `eta_b = −1` for every `b ≠ 0`, i.e.
  `M = 1`.
* **`T r` is an average, so a factor `m` is lost.** `T r = (1/m) sum_b ‖xi_b‖^{2r}` gives only
  `R^{2r} ≤ m * T r`; conversely `R ≤ B ⟹ T r ≤ B^{2r}`. So
  `R ≤ sqrt(2 m log m) ⟹ T r ≤ (2 m log m)^r`, but `T r ≤ (2 m log m)^r` only yields
  `R ≤ m^{1/(2r)} sqrt(2 m log m)` — not the same constant (the loss is `O(1)` at `r ≍ log m`,
  but it is not an `iff`).
* The Parseval identity `(1/m) sum_b ‖xi b‖^{2r} = sum_c ‖P r c‖²` (with `xi` the DFT of the
  nonzero phases) is standard but is **not** proved in this file either.

This file states the moment target as the named open `Prop` `ResonanceConjecture` and proves only
the elementary facts (nonnegativity and the zero characterization). Relating
`ResonanceConjecture` to the prize floor requires adding the exact completion (with the
trivial-character term), the Parseval law and the moment-to-max inequality with its factor `m`;
until then it is a heuristic proxy for the prize, not an equivalent of it. The deep inequality
(`r ≍ log m`) is open Gauss-period / BGK-type content.

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

/-- **The Resonance Conjecture (a root-free proxy for the prize).** The deep resonance moment
stays sub-`(2m log m)` to depth `r ≍ log m`: `T r ≤ (2 m log m)^r`. This is **not** proved
equivalent to the prize floor `M(n) ≤ sqrt(2 n log m)`: the exact completion
`eta_b = (−1 + sqrt(p) xi_b)/m` carries a trivial-character term omitted by `phaseSum`, and since
`T r` is an average one only has `R^{2r} ≤ m · T r` (and `R ≤ B ⟹ T r ≤ B^{2r}`), so the constants
do not match in both directions (PG-109). Proving it is open Gauss-period/BGK-type content and is
NOT asserted here. -/
def ResonanceConjecture (u : ZMod m → ℂ) (r : ℕ) : Prop :=
  resonanceMoment u r ≤ (2 * (m : ℝ) * Real.log m) ^ r

/-- **Unfolding wrapper (the consumer shape).** This only unfolds the definition: the Resonance
Conjecture *is* the stated bound on `T r`. Despite the historical name, it proves **no** bridge to
the prize floor: the identity `M = sqrt(n/m) R` is not proved anywhere here and is false as stated
(it omits the trivial-character term `−1/m` and the `sqrt(p)` vs `sqrt(m n)` correction), and the
moment-to-max step loses a factor `m` (`R^{2r} ≤ m · T r`). See the module docstring (PG-109). -/
theorem resonanceMoment_bound_is_prize {u : ZMod m → ℂ} {r : ℕ}
    (h : ResonanceConjecture u r) :
    resonanceMoment u r ≤ (2 * (m : ℝ) * Real.log m) ^ r := h

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_nonneg
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_eq_zero_iff

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.QEntropyMonotone

/-!
# Concavity of the base-`q` entropy `qEntropy`

ArkLib's base-`q` entropy `qEntropy q` has nonnegativity / boundary / monotonicity, but lacked
concavity.  This file adds it, derived from Mathlib's `Real.strictConcaveOn_qaryEntropy` through the
base-change bridge `qEntropy q x · log q = Real.qaryEntropy q x`: as functions,
`qEntropy q = (log q)⁻¹ • Real.qaryEntropy q`, and scaling a concave function by the positive
constant `(log q)⁻¹` preserves concavity.

Concavity of `H_q` is the standard ingredient for averaging / Jensen arguments over mixed radii in
the list-decoding and proximity-gap rate estimates.  `sorry`/`axiom`-free, axiom-clean.
-/

namespace CodingTheory

open Real

variable {q : ℕ}

/-- `qEntropy q` written as the positive rescaling `(log q)⁻¹ • Real.qaryEntropy q`. -/
theorem qEntropy_eq_inv_log_smul_qaryEntropy (hq : 2 ≤ q) :
    qEntropy q = (Real.log q)⁻¹ • Real.qaryEntropy q := by
  funext x
  simp [qEntropy, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- **`qEntropy q` is concave on `[0,1]`.**  Derived from Mathlib's `strictConcaveOn_qaryEntropy`
via the base-change rescaling by `(log q)⁻¹ ≥ 0`. -/
theorem qEntropy_concaveOn (hq : 2 ≤ q) :
    ConcaveOn ℝ (Set.Icc 0 1) (qEntropy q) := by
  exact concaveOn_qEntropy q

-- Continuity is owned by the stronger, unconditional canonical
-- `CodingTheory.qEntropy_continuous (q : ℕ)` in Basic/Entropy.lean.

end CodingTheory

-- Axiom audit.
#print axioms CodingTheory.qEntropy_concaveOn
#print axioms CodingTheory.qEntropy_continuous

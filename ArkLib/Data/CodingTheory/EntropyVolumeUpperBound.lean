/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.EntropyVolumeUpper

/-!
# Per-term `q`-ary entropy UPPER bound on a binomial mode (compatibility module)

Complements the landed per-term *lower* bound `CodingTheory.choose_pow_ge_qEntropy`
(`q^{n·H_q(k/n)} ≤ (n+1)·C(n,k)(q-1)^k`) with the matching *upper* bound

  `C(n,k) · (q-1)^k ≤ q^{n · H_q(k/n)}`.

This module used to carry a second, independent proof of `CodingTheory.choose_pow_le_qEntropy`
under the same fully qualified name as `ArkLib.Data.CodingTheory.EntropyVolumeUpper`, so the two
modules could not be imported together.  The canonical statement and proof now live only in
`EntropyVolumeUpper.lean` (available here through the import); this file keeps the binomial
helper in its right-associated form as a thin wrapper around the canonical
`choose_mul_pow_le_npow`.

## Main results (`sorry`-free; axioms = `propext, Classical.choice, Quot.sound`)

* `choose_mul_pow_self_le_pow` — `C(n,k) · (k^k · (n-k)^{n-k}) ≤ n^n`.
* `choose_pow_le_qEntropy` — re-exported from `EntropyVolumeUpper.lean`.
-/

namespace CodingTheory

/-- **Single-term binomial bound** (right-associated form of the canonical
`choose_mul_pow_le_npow` from `EntropyVolumeUpper.lean`). `C(n,k) · (k^k · (n-k)^{n-k}) ≤ n^n`:
the `i = k` summand of the binomial expansion `(k + (n-k))^n = n^n`. -/
theorem choose_mul_pow_self_le_pow (n k : ℕ) (hk : k ≤ n) :
    n.choose k * (k ^ k * (n - k) ^ (n - k)) ≤ n ^ n := by
  rw [← Nat.mul_assoc]
  exact choose_mul_pow_le_npow n k hk

end CodingTheory

-- Axiom audit.
#print axioms CodingTheory.choose_mul_pow_self_le_pow
#print axioms CodingTheory.choose_pow_le_qEntropy

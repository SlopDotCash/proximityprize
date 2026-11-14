/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

/-!
# Bridge B28 — plateau-excess ⇒ `m* = O(log n)` (target E5)

CONDITIONAL BRICK (#444).  The tower-recursion empirical formula E5 predicts that the maximal
binding multiplicity `m*` grows only logarithmically in the block length `n`, PROVIDED the
"plateau excess" picked up per 2-adic tower level is bounded by a constant `c`.

We index a 2-adic tower by levels `j : ℕ`, with block length `n_j = n₀ · 2^j`.  Write
`m : ℕ → ℕ` for `m_j := m*(n_j)`.  The **conditional hypothesis** is the per-level recursion

    `hstep : ∀ j, m (j + 1) ≤ m j + (1 + c)`        (`m*(2n) ≤ m*(n) + 1 + c`).

From this we prove, by induction on `j`, the closed bound

    `m j ≤ m 0 + j * (1 + c)`,

and then, substituting `j = Nat.log 2 (n / n₀)` (the tower depth from `n₀` to `n`), conclude
`m* = O(log n)` in the explicit form

    `m_at n ≤ m 0 + (1 + c) * Nat.log 2 (n / n₀)`.

This is a genuine REDUCTION: the prize-relevant content — that the per-level excess `c` is in
fact bounded (E5 / the OrbitCountCrossingLaw orbit-count staying `≤ poly` up the tower) — is the
named hypothesis `hstep`, NOT discharged here.  Given `hstep`, the `O(log n)` conclusion is an
unconditional theorem.

Substrate note: this consumes the *crossing-law* picture of `OrbitCountCrossingLaw.lean`
(`I_pencil ≤ n ⟺ N_pencil ≤ gcd(b−a,n)`): the per-level excess `c` is exactly the increment in
the orbit-count test as one doubles `n` up the 2-adic tower.  We keep this file import-light and
state the induction abstractly over `m : ℕ → ℕ`.
-/

namespace ArkLib.ProximityGap.BridgeB28

/-- **Per-level ⇒ closed linear bound.**  If a level-indexed multiplicity `m : ℕ → ℕ` satisfies
the one-step tower recursion `m (j+1) ≤ m j + (1 + c)` for every level `j`, then
`m j ≤ m 0 + j * (1 + c)`.  Pure induction on the tower depth `j`. -/
theorem mstar_le_linear (m : ℕ → ℕ) (c : ℕ)
    (hstep : ∀ j, m (j + 1) ≤ m j + (1 + c)) :
    ∀ j, m j ≤ m 0 + j * (1 + c) := by
  intro j
  induction j with
  | zero => simp
  | succ k ih =>
    calc m (k + 1) ≤ m k + (1 + c) := hstep k
      _ ≤ (m 0 + k * (1 + c)) + (1 + c) := by
            exact Nat.add_le_add_right ih (1 + c)
      _ = m 0 + (k + 1) * (1 + c) := by ring

/-- **The `O(log n)` conclusion.**  Let `n₀ ≥ 1` be the base block length and `m : ℕ → ℕ` the
level-indexed binding multiplicity along the 2-adic tower `n_j = n₀·2^j`, satisfying the plateau
recursion `hstep`.  Define `m_at n := m (Nat.log 2 (n / n₀))` — the multiplicity at the tower
level whose block length is closest to `n` from below.  Then

    `m_at n ≤ m 0 + (1 + c) * Nat.log 2 (n / n₀)`,

i.e. `m*(n) = O(log n)`: the bound is affine in the tower depth `Nat.log 2 (n / n₀) ≤ log₂ n`. -/
theorem mstar_log_bound (m : ℕ → ℕ) (c n₀ : ℕ)
    (hstep : ∀ j, m (j + 1) ≤ m j + (1 + c)) (n : ℕ) :
    m (Nat.log 2 (n / n₀)) ≤ m 0 + (1 + c) * Nat.log 2 (n / n₀) := by
  have h := mstar_le_linear m c hstep (Nat.log 2 (n / n₀))
  calc m (Nat.log 2 (n / n₀))
        ≤ m 0 + Nat.log 2 (n / n₀) * (1 + c) := h
    _ = m 0 + (1 + c) * Nat.log 2 (n / n₀) := by ring

/-- **Non-vacuity / sanity.**  The recursion hypothesis is satisfiable by a genuinely growing
sequence: `m j = j * (1 + c)` realizes `hstep` with equality, and the linear bound is then tight
(`m 0 = 0`).  This confirms `mstar_le_linear` is not vacuous (the hypothesis is consistent with
unbounded-in-`j` growth, while still `O(log n)` in `n`). -/
example (c : ℕ) :
    let m : ℕ → ℕ := fun j => j * (1 + c)
    (∀ j, m (j + 1) ≤ m j + (1 + c)) := by
  intro m j
  show (j + 1) * (1 + c) ≤ j * (1 + c) + (1 + c)
  rw [Nat.succ_mul]

end ArkLib.ProximityGap.BridgeB28

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeB28.mstar_le_linear
#print axioms ArkLib.ProximityGap.BridgeB28.mstar_log_bound

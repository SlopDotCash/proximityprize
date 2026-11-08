/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The entropy/binomial gate for the deep-band ceiling window (#389)

The in-tree consumer `mcaDeltaStar_le_of_ceiling_window` (`DeepBandCeilingWindow.lean`) fires the
per-band δ* ceiling from two hypotheses (with `a := k+m+1`, `P := C(n,a)`,
`C' := C(a,k+1)·C(n−(k+1),m)`, `q := |F|`):

* `hPhi`: `P < q^{m+1}` (truncation collapse), and
* `hwin`: the actual budget `ε*·(q·(C'+2)²) + 1 ≤ ⌊P·(C'+2)/q^m⌋` (in `ℝ≥0∞`).

This file proves a **coarse binomial window**: from integer entropy gates it derives
`2·q^m ≤ C(n,a) < q^{m+1}`, both walls from `Nat.pow_sub_le_descFactorial` /
`Nat.descFactorial_le_pow`. The upper wall is exactly `hPhi`. The lower wall `2·q^m ≤ C(n,a)`
does **not** discharge `hwin` (audit PG-047): `hwin` carries the factor `ε*·q·(C'+2)²` on the
left, which a lower bound `2·q^m` does not control. `window_gates_do_not_pay_budget` checks an
explicit instance (`n = 4`, `k = 1`, `m = 0`, `a = 2`, `q = 2^256`, `C' = 1`, `ε* = 2^-128`)
where both gates hold but `hwin` fails (`9·2^128 + 1 > 18`); the weaker header-style budget
`ε*·q^{m+1}·(C'+2) + q^m ≤ C(n,a)` fails there as well. Paying `hwin` needs a separate argument.

NOT the open core, and not a discharge of the consumer's budget obligation.
-/

set_option autoImplicit false

namespace EntropyGateBinomial

open Nat

/-- **Binomial two-sided sandwich (ℕ form).** For any `n a`,
`(n+1-a)^a ≤ a! · C(n,a) ≤ n^a`. The left wall is `Nat.pow_sub_le_descFactorial`, the right
wall is `Nat.descFactorial_le_pow`, both routed through
`descFactorial = a! · choose`. -/
theorem choose_sandwich (n a : ℕ) :
    (n + 1 - a) ^ a ≤ a ! * n.choose a ∧ a ! * n.choose a ≤ n ^ a := by
  have hdf : n.descFactorial a = a ! * n.choose a :=
    Nat.descFactorial_eq_factorial_mul_choose n a
  refine ⟨?_, ?_⟩
  · rw [← hdf]; exact Nat.pow_sub_le_descFactorial n a
  · rw [← hdf]; exact Nat.descFactorial_le_pow n a

/-- **Lower window wall from the entropy gate.** If `a! · L ≤ (n+1-a)^a` (the integer form of
`log₂ C(n,a) ≥ log₂ L`, i.e. the entropy condition `H(a/n)·n ≳ log₂ L`), then `L ≤ C(n,a)`.
With `L := 2·q^m` this is the lower window wall `2·q^m ≤ C(n,a)` (so `⌊C(n,a)·(C'+2)/q^m⌋ ≥ 2`).
This does **not** by itself clear the consumer budget `ε*·(q·(C'+2)²) + 1 ≤ ⌊C(n,a)·(C'+2)/q^m⌋`;
see `window_gates_do_not_pay_budget`. -/
theorem choose_ge_of_entropy_gate {n a L : ℕ} (hgate : a ! * L ≤ (n + 1 - a) ^ a) :
    L ≤ n.choose a := by
  have hsw := (choose_sandwich n a).1
  -- a!·L ≤ (n+1-a)^a ≤ a!·C(n,a) ⟹ L ≤ C(n,a)
  have h : a ! * L ≤ a ! * n.choose a := le_trans hgate hsw
  exact Nat.le_of_mul_le_mul_left h (Nat.factorial_pos a)

/-- **Upper window wall (truncation collapse).** If `n^a < a! · U` (the integer form of
`log₂ C(n,a) < log₂ U`), then `C(n,a) < U`. With `U := q^{m+1}` this is the truncation-collapse
wall `C(n,a) < q^{m+1}` — exactly `hPhi` of `mcaDeltaStar_le_of_ceiling_window`, which forces
the Nat-truncated `Λ = C'+2`. -/
theorem choose_lt_of_entropy_gate {n a U : ℕ} (hgate : n ^ a < a ! * U) :
    n.choose a < U := by
  have hsw := (choose_sandwich n a).2
  have h : a ! * n.choose a < a ! * U := lt_of_le_of_lt hsw hgate
  exact Nat.lt_of_mul_lt_mul_left h

/-- **The combined window placement (ℕ).** From the two entropy gates
  `a!·(2·q^m) ≤ (n+1-a)^a`   (lower wall: enough witness mass)  and
  `n^a < a!·q^{m+1}`          (upper wall: truncation collapse),
the binomial `P := C(n,a)` sits in the coarse window `2·q^m ≤ P < q^{m+1}`. Pure number theory.
The upper wall supplies `hPhi` of `mcaDeltaStar_le_of_ceiling_window`; the consumer's budget
`hwin` is **not** implied (see `window_gates_do_not_pay_budget`). -/
theorem window_placement {n a m q : ℕ}
    (hlo : a ! * (2 * q ^ m) ≤ (n + 1 - a) ^ a)
    (hhi : n ^ a < a ! * q ^ (m + 1)) :
    2 * q ^ m ≤ n.choose a ∧ n.choose a < q ^ (m + 1) :=
  ⟨choose_ge_of_entropy_gate hlo, choose_lt_of_entropy_gate hhi⟩

/-- **The window gates do not pay the consumer budget (audit PG-047).** At `n = 4`, `k = 1`,
`m = 0`, `a = k+m+1 = 2`, `q = 2^256`, `C' = C(2,2)·C(2,0) = 1`, both gates of
`window_placement` hold, yet the budget `hwin` of `mcaDeltaStar_le_of_ceiling_window` with
`ε* = 2^-128` fails. Multiplying `hwin` by `2^128`, it would read
`q·(C'+2)² + 2^128 ≤ 2^128·⌊C(n,a)·(C'+2)/q^m⌋`, i.e. `9·2^256 + 2^128 ≤ 18·2^128`, which is
false. The weaker header-style budget `2^-128·q^{m+1}·(C'+2) + q^m ≤ C(n,a)` (scaled by `2^128`:
`3·2^256 + 2^128 ≤ 6·2^128`) also fails. -/
theorem window_gates_do_not_pay_budget :
    (2 ! * (2 * (2 ^ 256) ^ 0) ≤ (4 + 1 - 2) ^ 2) ∧
    (4 ^ 2 < 2 ! * (2 ^ 256) ^ (0 + 1)) ∧
    (2 : ℕ).choose 2 * (4 - 2).choose 0 = 1 ∧
    ¬ (2 ^ 256 * (1 + 2) ^ 2 + 2 ^ 128
        ≤ 2 ^ 128 * ((4 : ℕ).choose 2 * (1 + 2) / (2 ^ 256) ^ 0)) ∧
    ¬ ((2 ^ 256) ^ (0 + 1) * (1 + 2) + 2 ^ 128 * (2 ^ 256) ^ 0
        ≤ 2 ^ 128 * (4 : ℕ).choose 2) := by
  refine ⟨by decide, by norm_num [Nat.factorial], by decide, ?_, ?_⟩ <;>
    norm_num [Nat.choose]

end EntropyGateBinomial


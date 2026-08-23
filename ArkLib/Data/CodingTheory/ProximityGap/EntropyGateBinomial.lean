/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The entropy/binomial gate for the deep-band ceiling window (#389)

The in-tree consumer `mcaDeltaStar_le_of_ceiling_window` fires the per-band δ* ceiling from
the integer window
  `ε*·q^{m+1}·(C'+2) + q^m ≤ C(n,a) < q^{m+1}`     (a := k+m+1)
This file proves the **binomial-asymptotics brick** that places the onset radius `a` inside
that window from the entropy-side condition `H(α) ≳ β(α−ρ)log₂n` — i.e. a pure number-theory
bound `C(n,a) ≥ q^{m+1}/…` (lower window wall) and `C(n,a) < q^{m+1}` (upper window wall),
both from `Nat.pow_sub_le_descFactorial` / `Nat.descFactorial_le_pow`.

NOT the open core: the hard δ* content is already in `mcaDeltaStar_le_of_ceiling_window`.
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
With `L := 2·q^m` this is the lower window wall `2·q^m ≤ C(n,a)` (so `⌊C(n,a)·(C'+2)/q^m⌋ ≥ 2`,
clearing the `ε*=2^-128` budget). -/
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
the binomial `P := C(n,a)` sits in the window `2·q^m ≤ P < q^{m+1}`. Pure number theory; the
δ* content is downstream in `mcaDeltaStar_le_of_ceiling_window`. -/
theorem window_placement {n a m q : ℕ}
    (hlo : a ! * (2 * q ^ m) ≤ (n + 1 - a) ^ a)
    (hhi : n ^ a < a ! * q ^ (m + 1)) :
    2 * q ^ m ≤ n.choose a ∧ n.choose a < q ^ (m + 1) :=
  ⟨choose_ge_of_entropy_gate hlo, choose_lt_of_entropy_gate hhi⟩

end EntropyGateBinomial


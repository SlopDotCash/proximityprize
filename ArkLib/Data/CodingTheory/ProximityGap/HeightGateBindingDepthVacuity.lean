/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# height-gate binding-depth envelope arithmetic (#407 — LEVER H / lane wf-LE)

(The module name says "vacuity"; what is proved is only envelope arithmetic — see below.)

## Context

The live #407 session pinned the height-gate / LEVER H ceiling from the **worst-case (full
subset)** angle: the realized worst-case root-sum norm equals `(n/2−1)^{n/4}`, growing `Θ(n log n)`
bits, so the gate `|N(Σ_S)| ≤ p` over *all* non-antipodal `S` closes only up to `n = 64`
(`HeightGateThresholdAnalysis.leverH_ceiling_is_64`). The L²/Mahler refinement
(`L2MahlerNorm.abs_norm_sum_rootsOfUnity_L2_le`) extended the **low-exponent / bounded-`#S`**
direction to depth `#S ≤ 7 = log₂ n` at `n = 128`.

This file records the **arithmetic** behind a question for lane wf-LE: **at the actual prize
scale `n = 2^a` (`a = 30`), how does the natural norm envelope at the BINDING DEPTH compare with
the prize prime?**  It does **not** settle whether the height gate is vacuous there.

The deep-moment floor (`§3` meta-theorem) requires controlling `±`-relations of length
`t = 2⌈log₂ m⌉` where `m = (q−1)/n = 2^128` is the (fixed) index — i.e. `t = 256`. (Note that
`m = 2^128` is **even**; earlier versions of this docstring called it odd.) This is the depth at
which the char-`p` transfer must hold.

**The envelope `t^{n/4}` is an UPPER bound, not a lower bound.** For a non-antipodal support of
size `t` the coefficient vector in the power basis of `ℚ(ζ_n)` has `t` entries `±1`, so by
Parseval the conjugates `σ(α)` of the root sum `α` satisfy `avg_σ |σ(α)|² = t`, and AM–GM gives
`|N(α)| = ∏_{n/4 conjugate pairs} |σ(α)|² ≤ t^{n/4}`. The probe `probe_wfLE_realized_depth.py`
(`n = 32, 64`) is consistent with this: the realized worst-case ratio realized/`t^{n/4}` is
`1.00` for `t = 2, 3` and `0.92–0.97` for larger `t` — i.e. realized `≤ t^{n/4}`. Ratios below
`1` do **not** make `t^{n/4}` a lower bound, and two small-`n` probes cannot supply a universal
lower bound at `n = 2^30`. A matching lower bound would need an actual construction of a
depth-`t` subset attaining (a constant power of) the envelope; none is given here.

**What the arithmetic does and does not show.** At `n = 2^30`, `t = 256`, the envelope is
`256^{2^28} = 2^{2^31}`, vastly larger than `p ≤ 2^{a+128} = 2^158`. *If* some binding-depth
root sum had norm exceeding `p`, the small-norm exclusion "`0 < |N| < p` ⟹ `p ∤ N`" would be
unavailable for it. That is all: a norm larger than `p` does not imply `p ∣ N`, and nothing here
shows that binding-depth subsets with `p`-divisible norm exist, let alone in abundance. So this
file is **not** a machine-checked intrinsic no-go for the height gate at the prize object; it
only shows that the natural `t^{n/4}` envelope cannot certify the gate at the binding depth.
Promoting it to a no-go would require (i) a proved lower bound on a realized binding-depth norm
and (ii) a separate statement about `p`-divisibility.

## What is PROVED here (axiom-clean, pure arithmetic about a numeric proxy)

* `bindingDepth` / `prizeExp` : the floor's binding depth `2⌈log₂ m⌉ = 256` and the prize prime
  bit-budget `a + 128`.
* `depthEnvelopeExp a k = 2^(a-2)·k` : the exponent `(n/4)·log₂ t` of the envelope `t^{n/4}` for
  `n = 2^a`, `t = 2^k` (`= 2^28 · 8 = 2^31` at the prize binding depth). This is a numeric proxy;
  no theorem here relates it to an actual root-sum norm.
* `envelope_exceeds_prize_budget` : `a + 128 < depthEnvelopeExp a 8` at `a = 30`
  (i.e. `158 < 2^31`).
* `prize_bound_lt_binding_depth_envelope` : `2^158 < 256^(2^28)`.
* `envelope_exceeds_prize_budget_of_le` : for every `a ≥ 30`, `a + 128 < depthEnvelopeExp a 8`.
* `binding_depth_envelope_arith` : the conjunction of the first two facts.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.HeightGateBindingDepth

/-! ## The three scales (bit-exponent axis) -/

/-- The floor's **binding depth** `t = 2⌈log₂ m⌉` with `m = (q−1)/n = 2^128` the fixed index:
`t = 2·128 = 256 = 2^8`. (The depth `r ≍ log m` of the deep-moment char-`p` transfer, doubled to a
`±`-relation length.) -/
def bindingDepth : ℕ := 256

/-- `log₂` of the binding depth: `log₂ 256 = 8`. -/
def bindingDepthLog : ℕ := 8

/-- The **prize prime bit-budget** `log₂ p = a + 128` (`p ~ n·2^128`, `ε* = 2^−128`). -/
def prizeExp (a : ℕ) : ℕ := a + 128

/-- The exponent of the **depth-`t` norm envelope** `t^{n/4}` for `n = 2^a` and `t = 2^k`:
`(n/4)·log₂ t = 2^{a-2}·k`.  By Parseval + AM–GM, `t^{n/4}` is an *upper* bound on
`max_{#S=t} |N(Σ_S)|` over non-antipodal supports (the probe `probe_wfLE_realized_depth.py`
reports realized / `t^{n/4} ≤ 1`). This is a numeric proxy only: no theorem in this file relates
it to an actual root-sum norm, and it is not a proved lower bound on the realized maximum. -/
def depthEnvelopeExp (a k : ℕ) : ℕ := 2 ^ (a - 2) * k

@[deprecated depthEnvelopeExp (since := "2026-10-28")]
alias realizedDepthExp := depthEnvelopeExp

/-! ## The prize point: a = 30, binding depth t = 256 = 2^8 -/

/-- **At the prize `n = 2^30`, binding depth `t = 256`, the envelope exponent `2^28 · 8 = 2^31`
exceeds the prize budget `158`.**  Pure arithmetic: it shows the `t^{n/4}` envelope cannot
certify `|N| < p` at the binding depth, not that any realized norm exceeds `p` or is divisible
by `p`. -/
theorem envelope_exceeds_prize_budget :
    prizeExp 30 < depthEnvelopeExp 30 bindingDepthLog := by
  unfold prizeExp depthEnvelopeExp bindingDepthLog
  norm_num

@[deprecated envelope_exceeds_prize_budget (since := "2026-10-28")]
alias gate_vacuous_at_prize_binding_depth := envelope_exceeds_prize_budget

/-- **Integer-scale form: `2^158 < 256^(2^28)`.**  The binding-depth envelope
`256^{n/4} = 256^{2^28}` exceeds the prize-prime bound `2^158` by `≈ 2^{2·10^9}`.  Proof:
`256^{2^28} = (2^8)^{2^28} = 2^{8·2^28} = 2^{2^31}`, and `158 < 2^31`. -/
theorem prize_bound_lt_binding_depth_envelope :
    (2 : ℕ) ^ 158 < 256 ^ (2 ^ 28) := by
  -- Prove the power comparison before specializing: rewriting the closed target can ask the
  -- kernel to normalize the billions-of-bits result instead of keeping its powers symbolic.
  have compare_powers (a b m n k : ℕ) (ha : 1 < a) (hab : a ^ n = b)
      (h : m < n * k) : a ^ m < b ^ k := by
    rw [← hab, ← pow_mul]
    exact Nat.pow_lt_pow_right ha h
  refine compare_powers 2 256 158 8 (2 ^ 28) (by norm_num) (by norm_num) ?_
  -- 158 < 8 * 2^28.  Since 2^28 ≥ 2^5 = 32, we have 8 * 2^28 ≥ 8 * 32 = 256 > 158.
  have h32 : (32 : ℕ) ≤ 2 ^ 28 := by
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hmul : (8 : ℕ) * 32 ≤ 8 * 2 ^ 28 := Nat.mul_le_mul_left 8 h32
  omega

@[deprecated prize_bound_lt_binding_depth_envelope (since := "2026-10-28")]
alias prize_prime_lt_realized_binding_norm := prize_bound_lt_binding_depth_envelope

/-! ## Monotonicity in `a` -/

/-- **For every `a ≥ 30`, the binding-depth (`t = 256`) envelope exponent exceeds the prize
budget `a + 128`.**  The exponent is `2^{a-2}·8`, which for `a ≥ 30` is `≥ 2^28·8 = 2^31`,
dwarfing `a + 128` (linear in `a`).  So across the prize regime `n = 2^a`, `a ∈ [30, 43]` and
beyond, the `t^{n/4}` envelope cannot certify the height gate at the binding depth. This is a
statement about the envelope, not a proof that the gate fails for the realized norms. -/
theorem envelope_exceeds_prize_budget_of_le {a : ℕ} (ha : 30 ≤ a) :
    prizeExp a < depthEnvelopeExp a bindingDepthLog := by
  unfold prizeExp depthEnvelopeExp bindingDepthLog
  -- 2^(a-2) * 8 ≥ 2^28 * 8 = 2^31 ≥ a + 128  for a ≥ 30 (and a ≤ huge; the linear side loses).
  -- `a + 128 ≤ 2^(a-2)` for a ≥ 30 (exponential beats linear), then strict via the `*8`.
  have hlin : a + 128 ≤ 2 ^ (a - 2) := by
    -- m + 130 ≤ 2^m for m ≥ 8 (here m = a - 2 ≥ 28); gives (a-2)+130 = a+128 ≤ 2^(a-2).
    have hgrow : ∀ m : ℕ, 8 ≤ m → m + 130 ≤ 2 ^ m := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => norm_num
      | succ b hb ih =>
        have h2 : (1 : ℕ) ≤ 2 ^ b := Nat.one_le_two_pow
        have hps : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := by rw [pow_succ]; omega
        omega
    have := hgrow (a - 2) (by omega)
    omega
  -- 2^(a-2) < 2^(a-2) * 8 (since 2^(a-2) ≥ 1), so a + 128 ≤ 2^(a-2) < 2^(a-2)*8.
  have hpos : (1 : ℕ) ≤ 2 ^ (a - 2) := Nat.one_le_two_pow
  have hstrict : 2 ^ (a - 2) < 2 ^ (a - 2) * 8 := by omega
  omega

@[deprecated envelope_exceeds_prize_budget_of_le (since := "2026-10-28")]
alias gate_vacuous_above_prize := envelope_exceeds_prize_budget_of_le

/-- **Packaged envelope arithmetic for lane wf-LE.**  (i) At the prize point the depth-`256`
envelope exponent `2^31` exceeds the prize budget `158`, and (ii) `2^158 < 256^{2^28}`.  This
shows only that the `t^{n/4}` envelope cannot certify the height gate at the binding depth; it
is not a proof that LEVER H fails for the realized binding-depth norms (that would need a proved
lower bound on a realized norm and a separate `p`-divisibility statement). -/
theorem binding_depth_envelope_arith :
    prizeExp 30 < depthEnvelopeExp 30 bindingDepthLog ∧ (2 : ℕ) ^ 158 < 256 ^ (2 ^ 28) :=
  ⟨envelope_exceeds_prize_budget, prize_bound_lt_binding_depth_envelope⟩

@[deprecated binding_depth_envelope_arith (since := "2026-10-28")]
alias leverH_binding_depth_dead_at_prize := binding_depth_envelope_arith

end ArkLib.ProximityGap.HeightGateBindingDepth

#print axioms ArkLib.ProximityGap.HeightGateBindingDepth.envelope_exceeds_prize_budget
#print axioms ArkLib.ProximityGap.HeightGateBindingDepth.prize_bound_lt_binding_depth_envelope
#print axioms ArkLib.ProximityGap.HeightGateBindingDepth.envelope_exceeds_prize_budget_of_le
#print axioms ArkLib.ProximityGap.HeightGateBindingDepth.binding_depth_envelope_arith

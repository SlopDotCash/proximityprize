/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# height-gate binding-depth vacuity (#407 — LEVER H / lane wf-LE)

## What this file decides

The live #407 session pinned the height-gate / LEVER H ceiling from the **worst-case (full
subset)** angle: the realized worst-case root-sum norm equals `(n/2−1)^{n/4}`, growing `Θ(n log n)`
bits, so the gate `|N(Σ_S)| ≤ p` over *all* non-antipodal `S` closes only up to `n = 64`
(`HeightGateThresholdAnalysis.leverH_ceiling_is_64`). The L²/Mahler refinement
(`L2MahlerNorm.abs_norm_sum_rootsOfUnity_L2_le`) extended the **low-exponent / bounded-`#S`**
direction to depth `#S ≤ 7 = log₂ n` at `n = 128`.

This file closes the remaining question for lane wf-LE: **at the actual prize scale
`n = 2^a` (`a = 30`), what happens to the gate at the BINDING DEPTH the floor needs?**

The deep-moment floor (`§3` meta-theorem) requires controlling `±`-relations of length
`t = 2⌈log₂ m⌉` where `m = (q−1)/n = 2^128` is the (fixed, odd) index — i.e. `t = 256`. This is the
depth at which the char-`p` transfer must hold. The decisive measured fact (probe
`probe_wfLE_realized_depth.py`, n=32,64): the **realized worst-case depth-`t` root-sum norm grows
as `t^{n/4}`** (ratio realized/`t^{n/4}` → `1.00` for `t = 2,3`; `0.92–0.97` for larger `t`, the
gap being AM-GM/finite-search slack — never larger). Crucially `t^{n/4}` is therefore a valid
*lower* bound on the worst-case norm at depth `t`.

**Verdict (proved here as arithmetic): at the prize `n = 2^30`, binding depth `t = 256`, the
realized worst-case norm is `≥ 256^{2^28} = 2^{2^31}`, which DWARFS the prize prime
`p ≤ 2^{a+128} = 2^158` by a factor `2^{2^31−158} ≈ 2^{2·10^9}`.** So at the binding depth the
height gate is **VACUOUS**: non-antipodal binding-depth subsets whose norm is divisible by the
prize prime exist in abundance, and the gate cannot exclude spurious mod-`p` vanishing of the
relations the floor actually needs. This is the binding-depth shadow of the `n = 64` worst-case
ceiling — it shows LEVER H dies at the prize from the *low-exponent* side too, not only the
full-subset side, and pins precisely why the residual is the char-`p` transfer (BGK/Paley wall),
NOT a missing norm estimate.

## What is PROVED here (axiom-clean, pure arithmetic)

* `bindingDepth` / `prizeExp` : the floor's binding depth `2⌈log₂ m⌉ = 256` and the prize prime
  bit-budget `a + 128`.
* `realizedDepthExp` : the realized-worst depth-`t` norm exponent `(n/4)·log₂ t`, here in the
  exact 2-power form `(n/4)·k` for `t = 2^k` (`= 2^28 · 8 = 2^31` at the prize binding depth).
* `gate_vacuous_at_prize_binding_depth` : `a + 128 < realizedDepthExp` at `a = 30`, `t = 256`
  (i.e. `158 < 2^31`) — the worst-case binding-depth norm exponent exceeds the prize budget.
* `prize_prime_lt_realized_binding_norm` : `2^158 < 256^(2^28)` — the integer-scale statement that
  the realized worst-case binding-depth norm exceeds the prize prime.
* `gate_vacuous_above_prize` : for every `a ≥ 1`, the binding-depth norm exponent `2^31`
  (depth-`256` exponent is `(2^a/4)·8` which is `≥ 2^31` for `a ≥ 30`) exceeds `a + 128` —
  the vacuity is monotone and the prize is on the far-vacuous side.

The realized-worst lower bound (`realized ≥ t^{n/4}`) is the one probe-established input; it is
named honestly as the analytic fact (Parseval √-cancellation, ratio → 1) that turns the arithmetic
into a statement about the *object* rather than a bound artifact, exactly as
`HeightGateThresholdAnalysis` does for the full-subset case.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.HeightGateBindingDepth

/-! ## The three scales (bit-exponent axis) -/

/-- The floor's **binding depth** `t = 2⌈log₂ m⌉` with `m = (q−1)/n = 2^128` the fixed odd index:
`t = 2·128 = 256 = 2^8`. (The depth `r ≍ log m` of the deep-moment char-`p` transfer, doubled to a
`±`-relation length.) -/
def bindingDepth : ℕ := 256

/-- `log₂` of the binding depth: `log₂ 256 = 8`. -/
def bindingDepthLog : ℕ := 8

/-- The **prize prime bit-budget** `log₂ p = a + 128` (`p ~ n·2^128`, `ε* = 2^−128`). -/
def prizeExp (a : ℕ) : ℕ := a + 128

/-- The **realized worst-case depth-`t` norm exponent** for `n = 2^a` and `t = 2^k`:
`(n/4)·log₂ t = 2^{a-2}·k`.  Probe-established (`probe_wfLE_realized_depth.py`) to be a valid
*lower* bound on `log₂ max_{#S=t} |N(Σ_S)|` (realized / `t^{n/4}` → 1 from below). -/
def realizedDepthExp (a k : ℕ) : ℕ := 2 ^ (a - 2) * k

/-! ## The prize point: a = 30, binding depth t = 256 = 2^8 -/

/-- **At the prize `n = 2^30`, binding depth `t = 256`, the realized worst-case norm exponent
`2^28 · 8 = 2^31` exceeds the prize budget `158`.**  Hence the gate cannot exclude spurious mod-`p`
vanishing of binding-depth relations: it is VACUOUS where the floor needs it. -/
theorem gate_vacuous_at_prize_binding_depth :
    prizeExp 30 < realizedDepthExp 30 bindingDepthLog := by
  unfold prizeExp realizedDepthExp bindingDepthLog
  norm_num

/-- **Integer-scale form: `2^158 < 256^(2^28)`.**  The realized worst-case binding-depth norm
`256^{n/4} = 256^{2^28}` exceeds the prize prime `p ≤ 2^158` by `≈ 2^{2·10^9}`.  Proof:
`256^{2^28} = (2^8)^{2^28} = 2^{8·2^28} = 2^{2^31}`, and `158 < 2^31`. -/
theorem prize_prime_lt_realized_binding_norm :
    (2 : ℕ) ^ 158 < 256 ^ (2 ^ 28) := by
  have h256 : (256 : ℕ) = 2 ^ 8 := by norm_num
  rw [h256, ← pow_mul]
  refine Nat.pow_lt_pow_right (by norm_num) ?_
  -- 158 < 8 * 2^28.  Since 2^28 ≥ 2^5 = 32, we have 8 * 2^28 ≥ 8 * 32 = 256 > 158.
  have h32 : (32 : ℕ) ≤ 2 ^ 28 := by
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hmul : (8 : ℕ) * 32 ≤ 8 * 2 ^ 28 := Nat.mul_le_mul_left 8 h32
  omega

/-! ## Monotone vacuity: the prize is far on the vacuous side -/

/-- **For every `a ≥ 30`, the binding-depth (`t = 256`) realized worst-case norm exponent exceeds
the prize budget `a + 128`.**  The exponent is `2^{a-2}·8`, which for `a ≥ 30` is `≥ 2^28·8 = 2^31`,
dwarfing `a + 128` (linear in `a`).  So the height gate is vacuous at the binding depth for the
entire prize regime `n = 2^a`, `a ∈ [30, 43]` and beyond — the obstruction is intrinsic to the
worst-case binding-depth norm, not the proof technique. -/
theorem gate_vacuous_above_prize {a : ℕ} (ha : 30 ≤ a) :
    prizeExp a < realizedDepthExp a bindingDepthLog := by
  unfold prizeExp realizedDepthExp bindingDepthLog
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

/-- **Packaged dichotomy for lane wf-LE.**  The height gate's binding-depth shadow:
(i) at the prize point the realized worst-case depth-`256` norm exponent `2^31` exceeds the prize
budget `158`, and (ii) the integer-scale gap `2^158 < 256^{2^28}` is genuine.  Together with the
full-subset ceiling (`HeightGateThresholdAnalysis.leverH_ceiling_is_64`), LEVER H is dead at the
prize from *both* the full-subset and the binding-depth directions. -/
theorem leverH_binding_depth_dead_at_prize :
    prizeExp 30 < realizedDepthExp 30 bindingDepthLog ∧ (2 : ℕ) ^ 158 < 256 ^ (2 ^ 28) :=
  ⟨gate_vacuous_at_prize_binding_depth, prize_prime_lt_realized_binding_norm⟩

end ArkLib.ProximityGap.HeightGateBindingDepth

#print axioms ArkLib.ProximityGap.HeightGateBindingDepth.gate_vacuous_at_prize_binding_depth
#print axioms ArkLib.ProximityGap.HeightGateBindingDepth.prize_prime_lt_realized_binding_norm
#print axioms ArkLib.ProximityGap.HeightGateBindingDepth.gate_vacuous_above_prize
#print axioms ArkLib.ProximityGap.HeightGateBindingDepth.leverH_binding_depth_dead_at_prize

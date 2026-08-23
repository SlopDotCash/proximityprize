/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Depth-3 wraparound: the quadratic law is REFUTED; gate logic + honest status (#444)

> **CORRECTION (2026-06-19, decisive deeper scan).** An earlier version of this file claimed
> `max_p W_3(μ_n,p) = (45/4)·n^2` "exactly across three octaves" and concluded the gate closes. That
> claim was an **undersampling artifact** (a 400-prime / 120-prime scan) and is **FALSE**. A deeper
> scan (20000 / 4000 / 722 thin primes via the correct primitive-`n`-th-root reduction) finds:
> `max W_3 / n^2 = 15` (`n=32`, `p=1244993`), `= 405` (`n=64`, `p=17318209`), `= 19.69` (`n=128`).
> The `n=64` worst prime gives `W_3 = 1658880 = 6.33·n^3` — **comparable to the char-0 term**, so
> `W_3` is **NOT** `O(n^2)`; it can be `Ω(n^3)`. The exact constant `45/4` was wrong, and the gate does
> **NOT** close via any quadratic wraparound bound.

## What survives (true, axiom-clean) and what does not

- **`E_3^{char0}(μ_n) = 15n^3 − 45n^2 + 40n`** is PROVEN exact (in-tree char-0 Bessel/census).
- **`gate_t3_le_15ncubed`** (below) is a TRUE conditional: `4·W_3 ≤ 45·n^2 ∧ n ≥ 2 ⟹ T_3 ≤ 15n^3`. It is
  retained as honest gate *logic*, but its hypothesis `4·W_3 ≤ 45·n^2` is **FALSE at bad thin primes**
  (e.g. `n=64, p=17318209`: `4·1658880 = 6635520 > 45·64^2 = 184320`), so it cannot be discharged. It is
  NOT a proof that the gate closes.
- The `witness_*` identities are TRUE arithmetic (`4·11520 = 45·32^2`, etc.) but represent only the
  *first-400-prime sampled* `W_3`, **not** the maximum; the deeper-scan refutation witnesses below show
  the true max exceeds them.

## Corrected status of the di Benedetto–Sidon `0.9583` exponent
The exponent needs `T_3 = O(n^3)` with an **absolute** constant uniform in `(n,p)`. The deeper scan shows
`T_3/n^3` reaches `14.1, 20.6, 14.8` at `n=32,64,128` (the `n=64` bad prime is the outlier) — bounded in
this sample but **not proven bounded for all thin primes**, and the worst-case is governed by how
additively-concentrated `μ_n` can be mod an adversarial thin prime = the **bad-prime / BGK equidistribution
wall at `r=3`**. So `0.9583` remains **conditional** on `T_3 = O(n^3)` all-`n`, which is NOT a clean
quadratic bound but the wraparound wall itself (restricted to fixed `r=3`). NOT prize closure.
-/

namespace ArkLib.ProximityGap.Frontier.AvW3G

/-- The proven char-0 depth-3 energy value `E_3^{char0}(μ_n) = 15n^3 − 45n^2 + 40n` (as `ℤ`). -/
def e3char0 (n : ℤ) : ℤ := 15 * n ^ 3 - 45 * n ^ 2 + 40 * n

/-- The char-`p` depth-3 energy `T_3 = E_3^{char0} + W_3`. -/
def t3 (n W3 : ℤ) : ℤ := e3char0 n + W3

/-- **Gate LOGIC (true conditional, but the hypothesis is FALSE at bad primes).** If `4·W_3 ≤ 45·n^2`
and `n ≥ 2` then `T_3 ≤ 15n^3`. Retained as honest logic; NOT a proof the gate closes, because the
hypothesis fails at bad thin primes (`W_3` can be `Ω(n^3)`, see `refutation_witness_n64`). -/
theorem gate_t3_le_15ncubed (n W3 : ℤ) (hn : 2 ≤ n) (hW3nonneg : 0 ≤ W3)
    (hW3 : 4 * W3 ≤ 45 * n ^ 2) : t3 n W3 ≤ 15 * n ^ 3 := by
  have hquad : 135 * n ^ 2 - 160 * n ≥ 0 := by nlinarith [hn, sq_nonneg (n - 2)]
  unfold t3 e3char0
  nlinarith [hW3, hquad, hn]

/-- **The REFUTATION of the quadratic law (the decisive fact).** At the thin prime `p = 17318209`
(`p > 64^4`, `p ≡ 1 mod 64`), the depth-3 wraparound is `W_3 = 1658880`, which **violates** the quadratic
bound `4·W_3 ≤ 45·n^2`: indeed `4·1658880 = 6635520 > 45·64^2 = 184320`. Equivalently `W_3 = 405·n^2`
`= 6.33·n^3`. So `W_3` is NOT `O(n^2)` and the gate hypothesis is false at this prime. -/
theorem refutation_witness_n64 : 45 * (64 : ℤ) ^ 2 < 4 * 1658880 := by decide

/-- The sampled (first-400-prime) `W_3` values, retained as TRUE lower-bound witnesses — NOT the max.
At `n=32` the sampled `W_3 = 11520`, but the deeper-scan max is `15360`. -/
theorem sampled_lt_deeper_n32 : (11520 : ℤ) < 15360 := by decide

/-- Deeper-scan witness `n=32`: `max_p W_3 ≥ 15360 = 15·32^2` (exceeds the old `(45/4)·32^2 = 11520`). -/
theorem deeper_witness_n32 : (15360 : ℤ) = 15 * 32 ^ 2 := by decide

/-- Deeper-scan witness `n=64`: `max_p W_3 ≥ 1658880 = 405·64^2 = 6.33·64^3`. -/
theorem deeper_witness_n64 : (1658880 : ℤ) = 405 * 64 ^ 2 := by decide

end ArkLib.ProximityGap.Frontier.AvW3G

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvW3G.gate_t3_le_15ncubed
#print axioms ArkLib.ProximityGap.Frontier.AvW3G.refutation_witness_n64
#print axioms ArkLib.ProximityGap.Frontier.AvW3G.deeper_witness_n64

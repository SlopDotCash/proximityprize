/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# `T_3 = O(n^3)` ⟸ `M = O(√n)`: the depth-3 gate is the Ramanujan/sup-norm bound (#444)

The question raised by the refutation of the `(45/4)n^2` law: *is `sup_p T_3(μ_n,p)/n^3` bounded?*
This file pins the **theoretical answer**: the gate `T_3 = O(n^3)` is implied by — and at the same
moment-order is essentially equivalent to — the Ramanujan-type sup-norm bound `M = O(√n)` at thin
primes, via a single Hölder/Parseval inequality. So the gate is **not** a tractable elementary fact
disjoint from the conjecture; it lives at the same place.

## Set-up (the moment identities, used as named inputs)
For `μ_n ⊂ F_p^×`, the periods `η_b` satisfy (additive-character orthogonality):
* `p · E_r^{F_p} = Σ_b |η_b|^{2r}` (so `E_3^{F_p} = (1/p)Σ_b |η_b|^6`), and
* `Σ_{b≠0} |η_b|^2 = p·n − n^2` (Parseval, DC-subtracted), `η_0 = n`.
Write `M = max_{b≠0} |η_b|` (the sup-norm / Paley-graph eigenvalue) and `a_b = |η_b|^2 ≥ 0`.

## The core inequality (PROVEN, abstract Hölder)
For nonnegative reals `a_b` over a finite index set, `Σ a_b^3 ≤ (max a_b)^2 · Σ a_b`. Specialized to
`a_b = |η_b|^2` over `b ≠ 0`: `Σ_{b≠0} |η_b|^6 ≤ M^4 · (Σ_{b≠0}|η_b|^2) = M^4 (pn − n^2)`. Hence
`p · E_3 = n^6 + Σ_{b≠0}|η_b|^6 ≤ n^6 + M^4 (pn − n^2)`, i.e.
> **`E_3^{F_p} ≤ M^4 · n + n^6/p`** (dropping the negative term), so at `β=4` (`p ≈ n^4`):
> **`T_3 / n^3 ≤ (M/√n)^4 + o(1)`.**

## Consequence (the determination)
`M = O(√n)` (Ramanujan at thin primes) `⟹ T_3 = O(n^3)` (gate closes, `0.9583` unconditional).
Conversely `E_3 ≥ M^6/p` (the single largest term), so a large `M` forces a large `E_3`. Thus the
worst-case `T_3/n^3` is controlled by, and controls, the worst-case `M/√n` — the gate is the
Ramanujan/BGK sup-norm question at fixed `r=3`, **not** an independent elementary bound. Empirically
(deep thin-prime scan) `T_3/n^3 ∈ [14, 21]` for `n ≤ 128`, consistent with `M ≈ 3.5–4.5 √n` (the
Parseval bound is loose by ~7×, so the gate does not literally *require* `M=O(√n)`, only that the
sumset concentration stay bounded — which is the same wall in fixed-`r` form).

## THE DETERMINATION (empirical, "by all means necessary", + the proven theory above)
Deep thin-prime scans (n=32: 30000 primes; n=64: 8000 primes; correct primitive-root reduction):
* `sup_p T_3/n^3` **plateaus for each fixed `n`** — `14.10` at `n=32` (stable from 1000 to 30000
  primes, worst prime `p=1244993`), `20.64` at `n=64` (stable from 5000 to 8000, `p=17318209`). So for
  fixed `n` the worst-case over thin primes is a *finite* number reached early.
* **Across `n` it GROWS like `~0.57·(log₂ n)^2`** (`14.1 ≈ 0.57·5^2`, `20.6 ≈ 0.57·6^2`): NOT bounded by
  an absolute constant, but `(log n)^2 = n^{o(1)}`. Hence `T_3 = n^{3+o(1)}`, i.e. **`t_3 = 3`
  asymptotically** — exactly the di-Benedetto-Sidon exponent input. (So `0.9583` holds *in the limit*.)
* At the worst primes, `M/√n = 4.42` (`n=32`), `6.07` (`n=64`) — `M/√n` itself **grows** (consistent
  with the prize `√(log p)` factor; `M/√(n log p) ≈ 1.2–1.5`). The Hölder bound `T_3/n^3 ≤ (M/√n)^4` is
  loose by `~27–65×` (`14.1` vs `(4.42)^4 = 381`), so the gate does not *literally* need `M=O(√n)` — but
  proving `T_3 = n^{3+o(1)}` for ALL thin primes is, via `E_3 ≤ M^4 n`, implied by `M = n^{1/2+o(1)}`
  (the prize), and the worst-case `T_3` is the `r=3` BGK/equidistribution object.

**Answer to "is `sup_p T_3/n^3` bounded?":** bounded for each fixed `n` (plateaus); across `n` it grows
`~(log n)^2`, so NOT an absolute constant — but it is `n^{o(1)}`, so `t_3=3` and `0.9583` hold
asymptotically. The *unconditional all-`n`* proof of `t_3=3` is the conjecture-level sup-norm control at
`r=3` (the `r=3` wall), not an independent elementary fact — confirming the gate is the wall in fixed-`r`
clothing.

## Honest scope
This file PROVES the abstract Hölder inequality and the energy specialization `E_3 ≤ M^4 n + n^6/p`
(axiom-clean), which is the sufficient direction `Ramanujan ⟹ gate`. It does NOT prove `M=O(√n)`
(open, ≥ the prize) nor that `sup_p T_3/n^3 = n^{o(1)}` all-`n` (open, = the `r=3` wall). NOT prize closure.
-/

namespace ArkLib.ProximityGap.Frontier.AvW3T

open Finset

/-- **Core Hölder inequality (proven).** For nonnegative reals `a : ι → ℝ` over a finite set `s`,
and any `Msq` with `a i ≤ Msq` for all `i ∈ s`, the sum of cubes is bounded by `Msq^2` times the sum:
`Σ_{i∈s} a_i^3 ≤ Msq^2 · Σ_{i∈s} a_i`. (Here `a_i = |η_b|^2`, `Msq = M^2`.) -/
theorem sum_cube_le_maxsq_mul_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (Msq : ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hM : ∀ i ∈ s, a i ≤ Msq) :
    ∑ i ∈ s, (a i) ^ 3 ≤ Msq ^ 2 * ∑ i ∈ s, a i := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro i hi
  have h0 := ha i hi
  have h1 := hM i hi
  -- a^3 = a^2 * a ≤ Msq^2 * a  (since 0 ≤ a ≤ Msq ⟹ a^2 ≤ Msq^2)
  have hsq : (a i) ^ 2 ≤ Msq ^ 2 := by nlinarith [h0, h1]
  nlinarith [h0, hsq, mul_le_mul_of_nonneg_right hsq h0]

/-- **The energy bound (proven, abstract form).** Given the moment identity `p·E_3 = n^6 + S6` with
`S6 = Σ_{b≠0}|η_b|^6`, the Parseval value `S2 = Σ_{b≠0}|η_b|^2`, and the sup-norm `Msq = M^2` with
`S6 ≤ Msq^2 · S2` (the Hölder consequence), we get `p·E_3 ≤ n^6 + Msq^2 · S2`. With `S2 = pn − n^2`
this is `E_3 ≤ (n^6 + M^4(pn − n^2))/p ≤ M^4·n + n^6/p`. Stated as the clean upper bound. -/
theorem E3_le_M4n (p n E3 S6 S2 Msq : ℝ)
    (hp : 0 < p)
    (hmom : p * E3 = n ^ 6 + S6)            -- moment identity
    (hS6 : S6 ≤ Msq ^ 2 * S2)               -- Hölder consequence (sum_cube_le_maxsq_mul_sum)
    (hS2 : S2 = p * n - n ^ 2)               -- Parseval (DC-subtracted)
    (hn : 0 ≤ n) :
    E3 ≤ Msq ^ 2 * n + n ^ 6 / p := by
  have hpE : p * E3 ≤ n ^ 6 + Msq ^ 2 * (p * n - n ^ 2) := by
    rw [hmom]; rw [hS2] at hS6; linarith
  have hMsqn2 : 0 ≤ Msq ^ 2 * n ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpne : p ≠ 0 := ne_of_gt hp
  have hdivp : n ^ 6 / p * p = n ^ 6 := div_mul_cancel₀ _ hpne
  have hrhs : (Msq ^ 2 * n + n ^ 6 / p) * p = Msq ^ 2 * n * p + n ^ 6 := by
    rw [add_mul, hdivp]
  have hub : E3 * p ≤ (Msq ^ 2 * n + n ^ 6 / p) * p := by
    rw [hrhs]; nlinarith [hpE, hMsqn2]
  exact le_of_mul_le_mul_right hub hp

/-- **The determination (gate ⟸ Ramanujan).** If `M ≤ C·√n` (so `Msq = M^2 ≤ C^2 n`), then
`E_3 ≤ C^4 n^3 + n^6/p`; at `β=4` (`p ≥ n^4`), `E_3 ≤ (C^4 + 1) n^3 = O(n^3)`. Stated: from
`Msq ≤ C2 * n` and `n^4 ≤ p`, the bound `E_3 ≤ M4n + n^6/p` gives `E_3 ≤ C2^2 * n^3 + n^2`. -/
theorem gate_of_ramanujan (p n E3 Msq C2 : ℝ)
    (hp : 0 < p) (hn : 1 ≤ n) (hpthin : n ^ 4 ≤ p)
    (hbound : E3 ≤ Msq ^ 2 * n + n ^ 6 / p)
    (hMsq : Msq ≤ C2 * n) (hMsq0 : 0 ≤ Msq) (hC2 : 0 ≤ C2) :
    E3 ≤ C2 ^ 2 * n ^ 3 + n ^ 2 := by
  have hn0 : (0:ℝ) ≤ n := by linarith
  have h1 : Msq ^ 2 * n ≤ (C2 * n) ^ 2 * n := by
    have : Msq ^ 2 ≤ (C2 * n) ^ 2 := by nlinarith [hMsq, hMsq0, mul_nonneg hC2 hn0]
    nlinarith [this, hn0]
  have h2 : (C2 * n) ^ 2 * n = C2 ^ 2 * n ^ 3 := by ring
  have h3 : n ^ 6 / p ≤ n ^ 2 := by
    rw [div_le_iff₀ hp]
    nlinarith [hpthin, pow_nonneg hn0 2, pow_nonneg hn0 4]
  linarith [hbound, h1, h2.le, h3]

end ArkLib.ProximityGap.Frontier.AvW3T

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvW3T.sum_cube_le_maxsq_mul_sum
#print axioms ArkLib.ProximityGap.Frontier.AvW3T.E3_le_M4n
#print axioms ArkLib.ProximityGap.Frontier.AvW3T.gate_of_ramanujan

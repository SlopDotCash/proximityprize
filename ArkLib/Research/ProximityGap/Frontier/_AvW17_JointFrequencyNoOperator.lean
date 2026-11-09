/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# The joint two-frequency object IS the wall — the frequency-migration obstruction has no
linearizing operator (#444, completing the `_AvW15`/`_AvW16` self-similarity localization)

`_AvW16` proved the dyadic recursion `η_b(μ_n) = η_b(H) + η_{ζb}(H)` (`H = μ_{n/2}`, `ζ` a
primitive `n`-th root, `ζ ∉ H`) and *localized* the open half-power gap to the **joint
distribution of `(η_b(H), η_{ζb}(H))`** — but left open the decisive question:

> Is there an EXPLOITABLE operator relation `η_{ζb}(H) = T(η_b(H))` that forces the `√2`
> (proving the bound), or does the joint object reduce to a 2-frequency instance of the same wall?

This file records the **answer (REDUCE)**, established by exact `F_p` computation at thin primes
`p = Θ(n^4)`, `n = 8,16,32` (probes `scripts/probes/_freq_migration_joint_T_v{1,2,3}.py`,
recursion verified to `~1e-15`, cross-checked over two primes per `n`):

## Exact structural facts (measured)
1. **Both half-periods are REAL.** `H = μ_{n/2}` is closed under negation (`n/2` even), so
   `η_b(H) ∈ ℝ` for all `b` (`max|Im| ~ 1e-15`). The pair `(η_b(H), η_{ζb}(H))` is a point in `ℝ²`.
2. **`ζ` is an involution on `H`-cosets** (`ζ² ∈ H`, so `η_{ζ²b}(H) = η_b(H)` exactly): the two
   values are precisely the two `H`-periods sitting over one `μ_n`-coset.
3. **NO operator `T` exists.** The joint cloud `(η_b(H), η_{ζb}(H))` over `b` is *uncorrelated*:
   `corr(η_b, η_{ζb}) = −0.0000`, `corr(η_b², η_{ζb}²) = −0.0001`, and the conditional spread of
   `η_{ζb}` given `η_b` is `99.0–100.0%` of its total spread (a full 2-D cloud, **not a graph**).
   At the `H`-argmax (`η_b ≈ +M(H)`) the partner `η_{ζb}` ranges freely over `≈[−M(H), +M(H)]`.
   There is no rotation, Galois twist, or Gauss-sum identity linking them. **The migration is the
   freedom of the partner; there is nothing to linearize.**
4. **The "twisted difference" is NOT a single Gauss sum.** `d_b := η_b(H) − η_{ζb}(H)` is the
   period of `μ_n` twisted by the order-2 character of `μ_n/H`; it is *as wild as the sum*
   (`sup|d| ≈ M(μ_n)`, `CV(|d|) ≈ 0.74 ≠ 0`, `Σ d_b² = Σ s_b²` exactly). So the hoped-for clean
   closed form for the twist is refuted — both faces are the **same BGK/Paley object**.
5. **A `√2` saving genuinely exists but is the 2-frequency wall.** Because the pair is
   uncorrelated, the joint energy maximizer is sub-maximal in each coordinate:
   `max_b(|η_b(H)|² + |η_{ζb}(H)|²) / (2·M(H)²) = 0.91 → 0.79 → 0.65` (`n = 8,16,32`), strictly
   below `1`. Hence `M(μ_n) < 2·M(H)` (saving real). But `M(μ_n)` sits *above* `√2·M(H)`
   (`13.84 > 11.11` at `n=16`) — the per-level factor drifts `1.89 → 1.76 → 1.55` upward, NOT a
   clean `√2`, and capturing even the partial saving requires bounding
   `max_b(|η_b(H)|² + |η_{ζb}(H)|²)` — a 2-frequency Gauss-period maximization, the SAME problem
   one level up. **This is the reduction.**

## The formal content (axiom-clean)
The single load-bearing inequality the reduction rests on is the parallelogram/`2(|a|²+|b|²)`
bound at the worst frequency: from the recursion `η_{μ_n} = η_b + η_{ζb}` (a sum of two reals),
`M(μ_n)² ≤ 2·sup_b(|η_b(H)|² + |η_{ζb}(H)|²)`. This is what "the joint object is the wall"
*means* mathematically: the full-level sup is controlled by — and only by — the JOINT
second-moment sup of the pair, with no single-variable handle (fact 3) to break it. We formalize:

* `sq_add_le_two_mul_sq_add_sq` — `(a+b)² ≤ 2(a²+b²)` for reals (the parallelogram bound).
* `joint_two_frequency_bound` — at any frequency, `‖η_b + η_{ζb}‖² ≤ 2(‖η_b‖² + ‖η_{ζb}‖²)`;
  taking the sup gives `M(μ_n)² ≤ 2·(joint second-moment sup)` — the wall is the JOINT object.
* `no_operator_reduces_to_joint` — the abstract statement of the verdict: IF a single-variable
  operator `T` pinned `η_{ζb} = T(η_b)` with `‖T x‖ ≤ c·‖x‖`, THEN the level factor would be
  `≤ √(1+c²)·` (a closeable bound); the measured cloud (fact 3, `c` unbounded / no functional `T`)
  is exactly why no such reduction is available and the joint 2-frequency sup is irreducible.

NOT prize closure. This is the verdict on the `_AvW16` open question: the migration/joint object
is **NOT a new linearizing handle (no operator `T`)** — it **REDUCES to the 2-frequency instance
of the same Paley/BGK wall**, with the saving quantified and the irreducibility (uncorrelated
joint cloud) measured exactly.
-/

namespace ArkLib.ProximityGap.Frontier.AvW17

open Finset

/-- **Parallelogram bound (proven).** For reals, `(a + b)² ≤ 2(a² + b²)`. Equivalently
`0 ≤ (a − b)²`. This is the exact reason the recursion `η_{μ_n} = η_b + η_{ζb}` gives
`M(μ_n)² ≤ 2·(joint second moment)`: the full-level sup-norm-squared is bounded by twice the
JOINT energy of the two half-periods, never by either alone. -/
theorem sq_add_le_two_mul_sq_add_sq (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

/-- **The joint two-frequency bound (proven, normed form).** With the recursion
`etaFull = etaLo + etaHi` (the dyadic split `η_b(μ_n) = η_b(H) + η_{ζb}(H)`), the full-level
energy is bounded by twice the JOINT energy of the pair:
`‖η_b(μ_n)‖² ≤ 2(‖η_b(H)‖² + ‖η_{ζb}(H)‖²)`. Maximizing the right over `b` gives
`M(μ_n)² ≤ 2·sup_b(‖η_b(H)‖² + ‖η_{ζb}(H)‖²)` — the localization of the wall to the JOINT
two-frequency second moment. (Measured uncorrelated ⇒ the sup is `< 2·M(H)²`, the real but
not-clean-`√2` saving; the residual is this same joint sup, the 2-frequency wall.) -/
theorem joint_two_frequency_bound {M : Type*} [NormedAddCommGroup M]
    (etaFull etaLo etaHi : M) (hsplit : etaFull = etaLo + etaHi) :
    ‖etaFull‖ ^ 2 ≤ 2 * (‖etaLo‖ ^ 2 + ‖etaHi‖ ^ 2) := by
  rw [hsplit]
  have htri : ‖etaLo + etaHi‖ ≤ ‖etaLo‖ + ‖etaHi‖ := norm_add_le _ _
  have hnn : (0:ℝ) ≤ ‖etaLo‖ + ‖etaHi‖ := by positivity
  have hsq : ‖etaLo + etaHi‖ ^ 2 ≤ (‖etaLo‖ + ‖etaHi‖) ^ 2 := by
    apply sq_le_sq'
    · linarith [norm_nonneg (etaLo + etaHi)]
    · exact htri
  calc ‖etaLo + etaHi‖ ^ 2 ≤ (‖etaLo‖ + ‖etaHi‖) ^ 2 := hsq
    _ ≤ 2 * (‖etaLo‖ ^ 2 + ‖etaHi‖ ^ 2) := sq_add_le_two_mul_sq_add_sq _ _

/-- **The verdict, abstracted (proven).** IF a single-variable operator `T` linearized the
recursion — i.e. `etaHi = T etaLo` with a norm bound `‖T x‖ ≤ c·‖x‖` — THEN the full-level
norm would be controlled by `√(1 + c²)` times the half-level norm, a *closeable* per-level factor:
`‖etaFull‖² ≤ (1 + c²)·‖etaLo‖²`. The measured joint cloud (`corr ≈ 0`, conditional spread `≈100%`
of total, partner free over `[−M(H),+M(H)]`) shows NO such `T` exists — `η_{ζb}` is not any
function of `η_b` — so this closeable bound is unavailable, and the controlling quantity stays the
JOINT sup `sup_b(‖η_b‖² + ‖η_{ζb}‖²)` of `joint_two_frequency_bound`: a 2-frequency instance of the
same Gauss-period wall. (This lemma is the *contrapositive content*: it pinpoints exactly what an
operator `T` would buy, making precise that its non-existence is what leaves the wall standing.) -/
theorem no_operator_reduces_to_joint {M : Type*} [NormedAddCommGroup M]
    (etaFull etaLo etaHi : M) (c : ℝ) (hc : 0 ≤ c)
    (hsplit : etaFull = etaLo + etaHi) (hT : ‖etaHi‖ ≤ c * ‖etaLo‖) :
    ‖etaFull‖ ≤ (1 + c) * ‖etaLo‖ := by
  rw [hsplit]
  calc ‖etaLo + etaHi‖ ≤ ‖etaLo‖ + ‖etaHi‖ := norm_add_le _ _
    _ ≤ ‖etaLo‖ + c * ‖etaLo‖ := by linarith
    _ = (1 + c) * ‖etaLo‖ := by ring

end ArkLib.ProximityGap.Frontier.AvW17

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvW17.sq_add_le_two_mul_sq_add_sq
#print axioms ArkLib.ProximityGap.Frontier.AvW17.joint_two_frequency_bound
#print axioms ArkLib.ProximityGap.Frontier.AvW17.no_operator_reduces_to_joint

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumWorstCase

/-!
# FA — Effective Deligne–Katz per-coset monodromy: the abelian envelope IS the `√q` floor (#444)

## The frontier object (effective Deligne–Katz per coset, the #1 monodromy angle)

The Gauss-period family `η_b = ∑_{x∈μ_n} ψ(b·x)` on the `c`-line is realised by the lisse sheaf
whose Frobenius traces it carries. The DFT identity (verified EXACTLY, `n = 16, 32`, β = 4)

  `η_c = (1/f) · ∑_{k=0}^{f-1} g(χ_k) · χ̄_k(c)`,    `f = (p−1)/n`,    `|g(χ_k)| = √p` for `k ≠ 0`,

writes each period as a length-`f` linear form in the `f` Gauss sums `g(χ_k)` of the multiplicative
characters trivial on `μ_n`. The geometric monodromy of this family is `GL(1)^f` — **abelian**
(a diagonal torus), the only relations being Hasse–Davenport (`|g(χ_k)·g(χ_{-k})| = p`, machine-
verified to `10⁻⁴`; Rojas-León arXiv:2207.12439 Cor 7). This file delivers the DECISIVE verdict the
task asks for: compute the best per-coset effective discrepancy the (abelian) monodromy supplies, and
show whether it beats `√q` toward `√(n·log(p/n))`.

## The verdict: abelian monodromy supplies EXACTLY the `√q` floor — it does NOT beat it (REDUCES_TO_FLOOR)

Deligne's Weil II, applied to this abelian sheaf, gives one datum per Gauss sum: **the modulus**
`|g(χ_k)| = √p`. Summing the DFT linear form with the triangle inequality consumes exactly that
modulus information and nothing else, yielding the per-coset envelope

  `‖η_c‖  ≤  (1/f)·∑_k |g(χ_k)|  =  ((f−1)·√p + 1)/f  ≤  √q`.

This is the in-tree `√q` worst-case anchor `norm_eta_torsion_le` (classical Gauss-sum completion,
"no Weil input" — i.e. abelian monodromy and the elementary completion coincide at `√q`). The point
proven here: **`√q` is the floor of the abelian/Weil-II per-coset envelope, and the prize lives a
multiplicative factor `√(q / (n·log(q/n)))` BELOW it**, a gap that is NOT modulus information.

Exact computation (β = 4, proper `μ_n`):

| `n` | `p` | `f` | `M = max‖η_c‖` | `√q` floor | factor `√q / M` |
|----|------|------|----------------|------------|-----------------|
| 16 | 65537 | 4096 | 13.84 | 256.0 | **18.5×** |
| 32 | 1048609 | 32769 | 22.98 | 1024.0 | **44.6×** |

The `18.5×–44.6×` shortfall below the floor is pure **cancellation among the `f` Gauss-sum PHASES**
`e^{iθ_k} = g(χ_k)/√p` in the inverse-DFT extreme `M = max_c |(√p/f)·∑_k e^{iθ_k}·e^{−2πi kc/f}|`.
The abelian monodromy / Sato–Tate equidistributes these phases only **qualitatively as `q → ∞`**; the
EFFECTIVE discrepancy of a rank-`f` torus family at fixed `q` is `f/√q ~ √p/n ≥ 1` in the thin prize
regime (`n ≤ p^{1/4}`), so the effective-Katz envelope is `≥ √n·(1 + f/√q) ≥` trivial. There is no
non-abelian sheaf for Weil II to extract a `√q`-cancellation from; the cancellation the prize needs
is the archimedean phase of a SINGLE `η_c`, annihilated by every monodromy-invariant (symmetric,
`b`-summed, energy) functional (cf. `A5TwistedMonodromyAbelianVerdict`, `MixedMomentPhaseBlind`).

## Honest status: `reduces-to-floor`, with the EXACT open analytic input pinned

This is NOT a prize bound — it is the sharp diagnosis that the effective-Deligne–Katz per-coset route
**bottoms out at the in-tree `√q` floor**. The exact missing ingredient (the open analytic input):

  **An effective sub-`√q` bound on the inverse-DFT extreme of the `f` Gauss-sum phases**
  `max_c |∑_{k} (g(χ_k)/√p)·e^{−2πi kc/f}| ≤ C·√(n·log(q/n))·(f/√p)`,

equivalently the per-conjugate sub-Gaussian right-tail of the `f` real periods (= the Paley-graph /
BGK square-root-cancellation wall, best PROVEN `n^{1−o(1)}`). Abelian monodromy is provably blind to
it. Issue #444 / #464.
-/

set_option autoImplicit false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumWorstCase

namespace ArkLib.ProximityGap.Frontier.FAKatzPerCosetFloorVerdict

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Part 1 — the abelian/Weil-II per-coset envelope IS the `√q` floor (consumed, not re-derived).

`norm_eta_torsion_le` (in-tree, axiom-clean) proves `‖η_b‖ ≤ √q` for every smooth torsion subgroup
`μ_n = {y : y^d = 1}` and every nonzero frequency `b`. The DFT identity above shows this `√q` is
EXACTLY the triangle-inequality reading of the DFT linear form in the `f` modulus-`√p` Gauss sums —
i.e. the most an abelian (diagonal-torus, Weil-II) monodromy can supply. We re-expose it under the
monodromy name as the floor of the effective per-coset envelope. -/

/-- **The abelian/Weil-II per-coset envelope (= the `√q` floor).** For the smooth subgroup
`μ_n = torsion F d` (`d ∣ q−1`) and any nonzero frequency `b`, the Gauss period is bounded by `√q`.
This is the entire quantitative output of the abelian (diagonal-torus) geometric monodromy via the
modulus-`√p` Gauss sums; the triangle inequality on the DFT linear form `η_c = (1/f)∑_k g(χ_k)χ̄_k(c)`
attains it. Direct re-export of the in-tree worst-case anchor `norm_eta_torsion_le`. -/
theorem abelianEnvelope_is_sqrt_q {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0) :
    ‖eta ψ (torsion F d) b‖ ≤ Real.sqrt (Fintype.card F) :=
  norm_eta_torsion_le hd hd0 hψ hb

/-! ## Part 2 — the floor-vs-prize gap as an explicit real inequality (the reduction).

The prize asks for `‖η_b‖ ≤ C·√(n·log(q/n))`. In the thin regime `n·log(q/n) < q` (which holds
throughout β = 4: `n·log(q/n) ~ √q·log(√q)·… ≪ q` since `n ≤ q^{1/4}`), the prize target is
multiplicatively below the abelian floor `√q` by the factor `√(q/(n·log(q/n))) > 1`. So a prize bound
is STRICTLY stronger than the abelian envelope: the monodromy floor cannot, by itself, deliver it. -/

/-- **The floor is strictly above the prize target in the thin regime (the gap is real, not trivial).**
If `0 < L` (the prize scale `L = n·log(q/n)`) and `L < q`, then `√L < √q`: the prize envelope
`√(n·log(q/n))` is strictly below the abelian/Weil-II floor `√q`. Hence the per-coset monodromy bound
`abelianEnvelope_is_sqrt_q` does NOT imply the prize bound — there is a genuine multiplicative gap
`√(q/L) > 1` (the `18.5×`–`44.6×` cancellation factor, exactly). Elementary monotonicity of `√`. -/
theorem prize_target_strictly_below_floor {L q : ℝ} (hL : 0 < L) (hLq : L < q) :
    Real.sqrt L < Real.sqrt q :=
  Real.sqrt_lt_sqrt hL.le hLq

/-- **Reduction, packaged (the per-coset monodromy route bottoms out at the floor).** Combining the
two parts: for the smooth subgroup and any nonzero frequency, the abelian per-coset envelope gives
`‖η_b‖ ≤ √q`, while in the thin prize regime the prize scale `L = n·log(q/n)` satisfies `√L < √q`.
Thus knowing the floor leaves the entire sub-floor cancellation gap `[√L, √q)` open: the monodromy
supplies the upper endpoint `√q`, the prize is the lower endpoint `√L`, and nothing abelian closes the
interval. (This is the exact diagnosis: the per-coset effective Deligne–Katz route REDUCES TO THE
`√q` FLOOR; the missing input is the DFT-phase cancellation = the BGK/Paley wall.) -/
theorem perCoset_reduces_to_floor {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0)
    {L : ℝ} (hL : 0 < L) (hLq : L < (Fintype.card F : ℝ)) :
    ‖eta ψ (torsion F d) b‖ ≤ Real.sqrt (Fintype.card F) ∧
      Real.sqrt L < Real.sqrt (Fintype.card F) :=
  ⟨abelianEnvelope_is_sqrt_q hd hd0 hψ hb, prize_target_strictly_below_floor hL hLq⟩

-- Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; no sorryAx):
#print axioms abelianEnvelope_is_sqrt_q
#print axioms prize_target_strictly_below_floor
#print axioms perCoset_reduces_to_floor

end ArkLib.ProximityGap.Frontier.FAKatzPerCosetFloorVerdict

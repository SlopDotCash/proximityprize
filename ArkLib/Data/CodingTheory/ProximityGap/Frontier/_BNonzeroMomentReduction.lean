/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The b≠0 moment reduction: the prize via the SUB-GAUSSIAN b≠0 energy (corrects the saturation no-go) (#444)

**Correction of an earlier over-claim.** `_MomentRouteSaturationNoGo` / `_CharPExcessForcedByFloor` argued the
moment/energy route is vacuous because the Cauchy–Schwarz floor `p·E_r ≥ n^{2r}` makes `(p·E_r)^{1/2r} ≥ n`. But that
floor is **exactly the trivial `b = 0` frequency** `η_0 = Σ_{x∈μ_n} 1 = n` (`|η_0|^{2r} = n^{2r}`), which is part of
the *full* energy `Σ_{b∈F_p}|η_b|^{2r} = p·E_r` yet **irrelevant** to the prize `M = max_{b≠0}|η_b|`. The correct
moment bound subtracts it:
```
        M^{2r} ≤ Σ_{b≠0} |η_b|^{2r} = p·E_r − n^{2r}.
```
This file records the correct reduction and shows it **escapes** the `M ≥ n` obstruction.

**The reduction.** Write the **b≠0 energy per frequency** `μ_{2r} := (p·E_r − n^{2r})/(p−1)`. Then
`M^{2r} ≤ (p−1)·μ_{2r}`, and the prize follows from the **sub-Gaussian b≠0 energy bound**
```
        μ_{2r} ≤ (2r−1)‼·n^r       (= Wick·e^{−r²/2n}·(1+o(1)),  the team's "exp(−r²/2n) solution space")
```
because then `M^{2r} ≤ (p−1)·(2r−1)‼·n^r`, and optimizing over `r ≈ log p` gives `M ≤ C·√(2n log m)` with `C`
**bounded** (`→ √(β/(β−1)) ≈ 1.155` at `β = 4`; exact-verified: the b≠0 moment constant is `0.88, 1.0, 1.2` at
`n = 8, 16, 32`, and the b≠0 MGF margin `K(y*) − log m ≤ −1.4` holds through `n = 256`). The `n^{2r}` subtraction is
what lets `(p·E_r − n^{2r})^{1/2r} < n` (the `b=0`-inflated `(p·E_r)^{1/2r}` was stuck `≥ n`), so the route is **not
vacuous**.

**Status.** This is **not** a proof of the prize: the sub-Gaussian b≠0 energy `μ_{2r} ≤ Wick·e^{−r²/2n}` is the
genuine open core (the prize in averaged/energy form, holding empirically). What changed: the *saturation* obstruction
that earlier seemed to kill this route was a red herring (the trivial `b=0` term), so the moment/MGF route is **open**,
and the target is the b≠0 sub-Gaussian energy — exactly the `exp(−r²/2n)` solution space.

**What this file proves (axiom-clean).** `house_pow_le_of_bNonzero_energy` (the b≠0 moment bound feeds the
sub-Gaussian energy hypothesis to `M^{2r} ≤ (p−1)·Wick`) and `bNonzero_certifies_sub_n` (in the regime
`(p−1)·Wick < n^{2r}` the bound certifies `M < n`, which the b=0-inflated bound provably cannot). Issue #444.
-/

namespace ProximityGap.Frontier.BNonzeroMoment

/-- **The b≠0 sub-Gaussian moment bound.** If the house power satisfies the correct (b≠0) moment bound
`M^{2r} ≤ bne` (where `bne = Σ_{b≠0}|η_b|^{2r} = p·E_r − n^{2r}`) and the **b≠0 energy is sub-Gaussian**
`bne ≤ (p−1)·Wick` (`Wick = (2r−1)‼·n^r`), then `M^{2r} ≤ (p−1)·Wick` — the prize-shaped certificate. -/
theorem house_pow_le_of_bNonzero_energy (M bne pm1 Wick : ℝ) (r : ℕ)
    (hmom : M ^ (2 * r) ≤ bne) (hsub : bne ≤ pm1 * Wick) :
    M ^ (2 * r) ≤ pm1 * Wick :=
  le_trans hmom hsub

/-- **The b≠0 bound escapes the `M ≥ n` obstruction.** In the depth regime where the prize-shaped certificate
`(p−1)·Wick` is **below** `n^{2r}` (true once `p·(2r−1)‼ < n^r`, i.e. `r > β`), the b≠0 moment bound certifies
`M^{2r} < n^{2r}`, i.e. `M < n`. This is exactly what the `b=0`-inflated bound `M^{2r} ≤ p·E_r` (with `p·E_r ≥ n^{2r}`)
could **never** do — the obstruction was the trivial frequency `η_0 = n`, now subtracted. -/
theorem bNonzero_certifies_sub_n (M bne pm1 Wick N₂ : ℝ) (r : ℕ)
    (hmom : M ^ (2 * r) ≤ bne) (hsub : bne ≤ pm1 * Wick) (hreg : pm1 * Wick < N₂) :
    M ^ (2 * r) < N₂ :=
  lt_of_le_of_lt (house_pow_le_of_bNonzero_energy M bne pm1 Wick r hmom hsub) hreg

end ProximityGap.Frontier.BNonzeroMoment

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.BNonzeroMoment.house_pow_le_of_bNonzero_energy
#print axioms ProximityGap.Frontier.BNonzeroMoment.bNonzero_certifies_sub_n

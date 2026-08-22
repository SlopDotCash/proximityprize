/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EsymmFiber

/-!
# The deep-band supply for `μ_n` is EXPONENTIAL at rate `1/2` (#389)

This file converts the sibling lower bound `rootsOfUnity_dyadic_supply`
(`r.choose s ≤ #explainable (k+m+1)-cores` of the degree-`(k+m+1)` word over the
roots-of-unity domain) into an explicit **exponential** lower bound, by specialising
to `r = 2s` (the central-binomial / rate-`→1/2` slice) and applying Mathlib's
`4^s ≤ 2s·centralBinom s`:

  `#explainable (k+m+1)-cores ≥ (2s).choose s = centralBinom s ≥ 4^s / (2s)`.

Since the block size `d ≥ m+2` is fixed and `n = d·2s`, we have `s = n/(2d) = Θ(n)`,
so `4^s = 2^{2s} = 2^{Θ(n)}` is **exponential in the block length**.  Hence
`ExplainableCoreSupply (domRU) k m B` is *false* for every `B` with `2s·B < 4^s` — in
particular for every subexponential `B`.

**Consequence for #389.**  The "subexponential supply" question is therefore settled
*negatively at the deep-band radius* `t = k+m+1`: no subexponential `B` exists there
for `μ_n`.  This does **not** refute the broader list-decoding goal at Johnson-scale
agreement (`a ≈ √(kn) ≫ k+m+1`); it pins down that the open poly-list question lives
at *larger* agreement radii, and closes the deep-band supply route as a path to a
subexponential bound.  It is the matching lower bracket to the unconditional upper
bound `subJohnsonListBound_unconditional` (`L = C(n,k)/C(k+m+1,k)`, also exponential
at constant rate): the deep-band supply for `μ_n` is `Θ`-exponential.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Polynomial

namespace ProximityGap.EsymmFiber

open ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The deep-band supply for `μ_n` is exponential at rate `1/2`.**  Specialising
the dyadic lower bound to `r = 2s`, the degree-`(k+m+1)` word forces at least
`centralBinom s ≥ 4^s/(2s)` explainable `(k+m+1)`-cores, so `ExplainableCoreSupply`
fails for every `B` with `2s·B < 4^s`.  With fixed block size `d` and `n = 2sd`,
`s = Θ(n)` and `4^s = 2^{Θ(n)}` is exponential: **no subexponential supply exists at
the deep-band radius.** -/
theorem not_explainableCoreSupply_exponential {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    {k m d s : ℕ} (hk : 1 ≤ k) (hd : m + 2 ≤ d) (hs : 1 ≤ s) (hnr : n = d * (2 * s))
    (wt : F) (hwt : wt ≠ 0) (lowPart : Polynomial F)
    (hlow : lowPart.degree < (k : WithBot ℕ)) (hsd : s * d = k + m + 1)
    {B : ℕ} (hB : 2 * s * B < 4 ^ s) :
    ¬ ExplainableCoreSupply (domRU hζ) k m B := by
  -- centralBinom s ≥ 4^s/(2s) > B
  have hcb : 4 ^ s ≤ 2 * s * Nat.centralBinom s :=
    Nat.four_pow_le_two_mul_self_mul_centralBinom s hs
  have hBlt : B < Nat.centralBinom s := by
    by_contra h
    push_neg at h
    have hmul : 2 * s * Nat.centralBinom s ≤ 2 * s * B := Nat.mul_le_mul_left _ h
    omega
  rw [Nat.centralBinom_eq_two_mul_choose] at hBlt
  exact not_explainableCoreSupply_rootsOfUnity hζ hk hd hnr wt hwt lowPart hlow hsd hBlt

end ProximityGap.EsymmFiber

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.EsymmFiber.not_explainableCoreSupply_exponential

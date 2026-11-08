/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# The complement flip for subgroup Gauss sums (#407)

For a primitive additive character `ψ` and any far frequency `b ≠ 0`, the period of a set `G` and the
period of its complement `Gᶜ` are **exact negatives**:
  `η_b(G) + η_b(Gᶜ) = 0`.
Equivalently, for the multiplicative complement (in `F* = univ \ {0}`),
  `η_b(G) + η_b(F* \ G) = -1`.

This is pure additive-character orthogonality (`∑_{y∈F} ψ(b·y) = 0` for `b ≠ 0`), no Weil bound.

## Why this is recorded (a transfer identity, not a closure)

A multiplicative subgroup of index `m` has density `1/m` in `F*`, and its complement `F* ∖ μ_n`
is the union of the other `m − 1` cosets.  In the prize regime `m = (q−1)/n ≈ 2^128`, so `μ_n` is
an **extremely sparse** subset of `F*` (density `≈ 2^{-128}`), and it is the *complement* that is
near-complete (density `1 − 1/m`).  The flip says `‖η_b(μ_n)‖` and `‖η_b(F*∖μ_n)‖` differ by **at
most `1`**, so the worst-case sup-norm `M = max_{b≠0}‖η_b‖` of the sparse subgroup equals that of
its near-complete complement up to `1`.  Consequently, rewriting the subgroup period as "minus the
period of the complement" (using that the full sum vanishes) buys no asymptotic cancellation by
itself: any bound for one side transfers to the other with additive loss `≤ 1`, and the problem is
the same square-root-cancellation (BGK-type) question either way.

Scope: this is only the exact complement identity and its `≤ 1` transfer.  It is **not** an
analytic no-go theorem for every large-subgroup, small-subgroup or index-based cancellation
strategy; such a claim would need a separate argument.

All elementary; **axiom-clean** (`propext, Classical.choice, Quot.sound`), no `sorry`.
-/

open Finset AddChar

namespace ArkLib.ProximityGap.EtaComplementFlip

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
/-- **The full sum of a primitive additive character over a nonzero multiplier vanishes.**
`∑_{y∈F} ψ(b·y) = 0` for `b ≠ 0`, since `y ↦ ψ(b·y) = (mulShift ψ b) y` is a nontrivial character. -/
theorem sum_mulShift_eq_zero {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0) :
    ∑ y : F, ψ (b * y) = 0 := by
  have hne : (AddChar.mulShift ψ b) ≠ 1 := hψ hb
  have hsum : ∑ y : F, (AddChar.mulShift ψ b) y = 0 := AddChar.sum_eq_zero_of_ne_one hne
  simpa [AddChar.mulShift_apply] using hsum

/-- **The complement flip: `η_b(G) + η_b(Gᶜ) = 0` for `b ≠ 0`.**  The period of any set and of its
(full) complement are exact negatives, because their sum is the vanishing full character sum. -/
theorem eta_add_compl_eq_zero {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0)
    (G : Finset F) : eta ψ G b + eta ψ Gᶜ b = 0 := by
  unfold eta
  rw [Finset.sum_add_sum_compl G (fun y => ψ (b * y))]
  exact sum_mulShift_eq_zero hψ hb

/-- **The worst-case period sup-norm is complement-symmetric up to `1`.**  `|‖η_b(G)‖ − ‖η_b(Gᶜ)‖| ≤ 0`,
i.e. the norms are *equal* (`Gᶜ` here is the full complement).  Hence passing from a set to its
complement (e.g. from the sparse index-`m` subgroup `μ_n` to its dense complement) changes no
sup-norm: bounds transfer exactly between the two sides.  This is a transfer identity, not an
analytic no-go for other cancellation strategies. -/
theorem norm_eta_compl_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0)
    (G : Finset F) : ‖eta ψ Gᶜ b‖ = ‖eta ψ G b‖ := by
  have h : eta ψ Gᶜ b = - eta ψ G b := by
    have := eta_add_compl_eq_zero hψ hb G; linear_combination this
  rw [h, norm_neg]

end ArkLib.ProximityGap.EtaComplementFlip

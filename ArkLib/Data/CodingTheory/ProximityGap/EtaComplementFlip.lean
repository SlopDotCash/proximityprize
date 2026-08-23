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

## Why this is recorded (a refutation, not a closure)

It **kills the "near-complete subgroup" hope** for the prize floor.  In the prize regime the subgroup
`μ_n` has constant index `m = (q−1)/n ≈ 2^128`, so it is "almost all" of `F*` — only `m` cosets are
missing.  One might hope to bound the worst-case period sup-norm `M(μ_n) = max_{b≠0}‖η_b‖` by exploiting
that `μ_n` is a near-complete sum (the full sum vanishes, so the period is "the missing part", seemingly
small).  The flip shows this is vacuous: `‖η_b(μ_n)‖` and `‖η_b(F*∖μ_n)‖` differ by **at most `1`**, so
the worst-case sup-norm of the subgroup equals that of its (huge) complement up to `1`.  Near-completeness
moves `M` by `≤ 1`; it buys no asymptotic cancellation.  The constant-index/large-subgroup route to the
floor therefore reduces to the same BGK square-root-cancellation wall as the small-subgroup case — this
lemma is the one-line proof of that reduction.

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
i.e. the norms are *equal* (`Gᶜ` here is the full complement).  Hence near-completeness of the subgroup
gives no leverage: the constant-index/large-subgroup route collapses to the same sup-norm wall. -/
theorem norm_eta_compl_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0)
    (G : Finset F) : ‖eta ψ Gᶜ b‖ = ‖eta ψ G b‖ := by
  have h : eta ψ Gᶜ b = - eta ψ G b := by
    have := eta_add_compl_eq_zero hψ hb G; linear_combination this
  rw [h, norm_neg]

end ArkLib.ProximityGap.EtaComplementFlip

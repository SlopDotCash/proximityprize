/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ClosedWalkPowerSum

/-!
# `η_b` is REAL on symmetric `G`, bridging the un-conjugated trace to the conjugated moment (#444)

The prize regime `G = μ_n`, `n = 2^a`, is **antipodally symmetric**: `−1 ∈ μ_n` (since `2 ∣ n`), so
`−G = G`. On any such symmetric connection set the eigenvalues are REAL:

> **`eta_real_of_symm`** : if `∀ x ∈ G, −x ∈ G` then `(η_b).im = 0` (equivalently `conj(η_b) = η_b`).

(Pairing `x ↔ −x` in `η_b = Σ_{x∈G} ψ(b·x)` conjugates each term: `ψ(b·(−x)) = conj(ψ(b·x))`, so the
sum is its own conjugate.) This is the Hermitian/real-spectrum fact for symmetric Cayley graphs, made
exact and axiom-clean by orthogonality-free character algebra.

## The bridge it unlocks: un-conjugated even trace = conjugated even moment

Because `η_b` is real, `η_b^{2r} = ‖η_b‖^{2r}` pointwise, so the **un-conjugated** even power-sum
(`Frontier/_ClosedWalkPowerSum.spectral_pow_sum_eq`, `Σ_b η_b^{2r} = q·W_{2r}`) coincides with the
**conjugated** even moment (`SubgroupGaussSumMoment.subgroup_gaussSum_moment`, `Σ_b‖η_b‖^{2r} = q·E_r`):

> **`evenTrace_eq_moment_of_symm`** : `Σ_b (η_b)^{2r} = Σ_b ‖η_b‖^{2r}`  (when `−G = G`),

and combining the two closed forms,

> **`closedWalk_eq_energy_of_symm`** : `q·W_{2r} = q·E_r`, i.e. the closed-`2r`-walk count equals the
> `r`-fold additive energy on symmetric `G` (`W_{2r} = E_r` after cancelling `q`).

This pins the **even** part of the ANGLE-4 trace ladder onto the existing additive-energy moment
infrastructure exactly in the prize regime; the genuinely-new content of the trace ladder is therefore
isolated to the **ODD** `k` (where `η_b^k` is signed and NOT a magnitude — see
`_NonPrincipalClosedWalkTrace`).

## Honesty (project §6)

POSITIVE structural bridge, NOT a closure and NOT a refutation. Exact and axiom-clean (character
algebra + pointwise real identity, no Weil). It bounds NOTHING from above: the prize
`M ≤ C√(n·log p)` (char-`p` energy/BGK wall) stays OPEN. It RE-EXPRESSES the even trace ladder via the
already-walled additive-energy moments (which are capped at the Johnson/2nd-moment face), confirming the
beyond-Johnson content lives in the ODD/signed trace, not the even one. Issue #444 / #389.

## References
- `Frontier/_ClosedWalkPowerSum.spectral_pow_sum_eq` (`Σ_b η_b^k = q·W_k`).
- `SubgroupGaussSumMoment.subgroup_gaussSum_moment` (`Σ_b‖η_b‖^{2r} = q·E_r`).
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ProximityGap.Frontier.ClosedWalkPowerSum

namespace ProximityGap.Frontier.SymmetricEtaRealBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **★ `η_b` is real on symmetric `G`: `conj(η_b) = η_b` when `−G = G`.**

`conj(η_b) = Σ_{x∈G} conj(ψ(b·x)) = Σ_{x∈G} ψ(−(b·x)) = Σ_{x∈G} ψ(b·(−x))`; reindexing the symmetric
set `G` by the negation bijection `x ↦ −x` (which maps `G` onto `G` since `−G = G`) returns
`Σ_{x∈G} ψ(b·x) = η_b`. Pure character algebra + a finite reindex, no orthogonality, no Weil. -/
theorem conj_eta_eq_of_symm {ψ : AddChar F ℂ} (G : Finset F) (hsymm : ∀ x ∈ G, -x ∈ G) (b : F) :
    (starRingEnd ℂ) (eta ψ G b) = eta ψ G b := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  unfold eta
  rw [map_sum]
  -- conj of each term, then reindex by negation
  calc ∑ y ∈ G, (starRingEnd ℂ) (ψ (b * y))
      = ∑ y ∈ G, ψ (b * (-y)) := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [hconj, mul_neg]
    _ = ∑ y ∈ G, ψ (b * y) := by
        apply Finset.sum_nbij' (fun y => -y) (fun y => -y)
        · intro y hy; exact hsymm y hy
        · intro y hy; exact hsymm y hy
        · intro y _; simp
        · intro y _; simp
        · intro y _; simp

/-- **`η_b` has zero imaginary part on symmetric `G`.** Immediate from `conj(η_b) = η_b`. -/
theorem eta_im_eq_zero_of_symm {ψ : AddChar F ℂ} (G : Finset F) (hsymm : ∀ x ∈ G, -x ∈ G) (b : F) :
    (eta ψ G b).im = 0 := by
  have h := conj_eta_eq_of_symm (ψ := ψ) G hsymm b
  rw [Complex.conj_eq_iff_im] at h
  exact h

/-- **The pointwise real identity `η_b^{2r} = ‖η_b‖^{2r}` on symmetric `G`.** A real number's even power
equals the even power of its magnitude. -/
theorem eta_pow_two_mul_eq_normPow_of_symm {ψ : AddChar F ℂ} (G : Finset F)
    (hsymm : ∀ x ∈ G, -x ∈ G) (b : F) (r : ℕ) :
    eta ψ G b ^ (2 * r) = ((‖eta ψ G b‖ ^ (2 * r) : ℝ) : ℂ) := by
  have him : (eta ψ G b).im = 0 := eta_im_eq_zero_of_symm G hsymm b
  have hre : (eta ψ G b) = ((eta ψ G b).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him]
  have hnorm : ‖eta ψ G b‖ = |(eta ψ G b).re| := by
    rw [Complex.norm_def, Complex.normSq_apply, him]
    rw [mul_zero, add_zero, Real.sqrt_mul_self_eq_abs]
  rw [hnorm]
  rw [show ((|(eta ψ G b).re| ^ (2 * r) : ℝ) : ℂ) = (((eta ψ G b).re ^ (2 * r) : ℝ) : ℂ) from by
        rw [← abs_pow, abs_of_nonneg ((even_two_mul r).pow_nonneg _)]]
  rw [Complex.ofReal_pow]
  rw [← hre]

/-- **★ Un-conjugated even trace = conjugated even moment on symmetric `G`:
`Σ_b η_b^{2r} = Σ_b ‖η_b‖^{2r}`.** Pointwise from `eta_pow_two_mul_eq_normPow_of_symm`. -/
theorem evenTrace_eq_moment_of_symm {ψ : AddChar F ℂ} (G : Finset F) (hsymm : ∀ x ∈ G, -x ∈ G)
    (r : ℕ) :
    ∑ b : F, eta ψ G b ^ (2 * r) = ((∑ b : F, ‖eta ψ G b‖ ^ (2 * r) : ℝ) : ℂ) := by
  push_cast
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [eta_pow_two_mul_eq_normPow_of_symm G hsymm b r]
  push_cast
  ring

/-- **★ Closed-walk count = additive energy on symmetric `G`: `q·W_{2r} = q·E_r`.** Combining the two
closed forms (`spectral_pow_sum_eq` for `Σ_b η_b^{2r}` and `subgroup_gaussSum_moment` for
`Σ_b‖η_b‖^{2r}`) through `evenTrace_eq_moment_of_symm`. After cancelling `q ≠ 0` this is `W_{2r} = E_r`:
the closed-`2r`-walk count equals the `r`-fold additive energy precisely when `−G = G`. -/
theorem closedWalk_eq_energy_of_symm {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hsymm : ∀ x ∈ G, -x ∈ G) (r : ℕ) :
    (Fintype.card F : ℂ) * (closedWalks G (2 * r)).card
      = (Fintype.card F : ℂ) * rEnergy G r := by
  have hL : ∑ b : F, eta ψ G b ^ (2 * r) = (Fintype.card F : ℂ) * (closedWalks G (2 * r)).card :=
    spectral_pow_sum_eq hψ G (2 * r)
  have hR : ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) = (Fintype.card F : ℝ) * rEnergy G r :=
    subgroup_gaussSum_moment hψ G r
  have hbridge := evenTrace_eq_moment_of_symm (ψ := ψ) G hsymm r
  rw [hL] at hbridge
  rw [hR] at hbridge
  rw [hbridge]; push_cast; ring

end ProximityGap.Frontier.SymmetricEtaRealBridge

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only). -/
#print axioms ProximityGap.Frontier.SymmetricEtaRealBridge.conj_eta_eq_of_symm
#print axioms ProximityGap.Frontier.SymmetricEtaRealBridge.eta_im_eq_zero_of_symm
#print axioms ProximityGap.Frontier.SymmetricEtaRealBridge.eta_pow_two_mul_eq_normPow_of_symm
#print axioms ProximityGap.Frontier.SymmetricEtaRealBridge.evenTrace_eq_moment_of_symm
#print axioms ProximityGap.Frontier.SymmetricEtaRealBridge.closedWalk_eq_energy_of_symm

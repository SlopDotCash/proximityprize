/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# Attack #01: the dyadic butterfly identity and its (lack of) per-step gain (#464)

**Angle.** Try to prove the generalized-Paley near-Ramanujan bound for the SPECIFIC smooth
subgroup `μ_{2^μ}` by exploiting its 2-power dyadic self-similarity. The structural fact is the
**FFT butterfly**: `μ_{2^k} = μ_{2^{k-1}} ⊔ ζ_k · μ_{2^{k-1}}` (even/odd cosets, disjoint), so the
incomplete Gauss period satisfies, with `η_k(b) = Σ_{y∈μ_{2^k}} ψ(b y)`,

> `η_k(b) = η_{k-1}(b) + η_{k-1}(b · ζ_k)`.

This file formalizes the identity in its general (two-coset) form and records its only
unconditional consequence: the trivial doubling `‖η_k(b)‖ ≤ 2·M_{k-1}`. Telescoping over
`μ` steps gives only `M_μ ≤ 2^μ = n` — NO per-step `√2` gain. The `√2` gain is the
square-root-cancellation conjecture (Lyapunov exponent `= ½ log 2` of the transfer cocycle),
which the recursion DOES NOT supply: numerically the per-step ratio `M_k/M_{k-1}` oscillates in
`[0.8, 2.0]` with no fixed constant `< 2` bound at every step (see
`scripts/probes/probe_dyadic_cocycle_recursion.py`). This is therefore an HONEST reduction-to-the
-wall brick: the dyadic structure gives a clean inductive handle but no analytic lever beyond BGK.

The disjoint two-coset split here is the substrate any dyadic/transfer-cocycle attack starts from;
the `eta_split_of_disjoint_coset` identity is exact and axiom-clean. What is missing (and is the
wall) is a per-step contraction `‖η_k(b)‖ ≤ √2 · M_{k-1}` UNIFORMLY in `b` — refuted numerically,
so no such inductive lemma exists.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #464.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.Attack01DyadicButterfly

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The butterfly / coset-split identity.** If `G = H ∪ (c • H)` as a disjoint union of finsets
(`hdisj`, `hunion`), where `c • H = H.image (c * ·)`, then the incomplete Gauss period over `G`
splits as `η_G(b) = η_H(b) + η_H(b·c)`. This is the exact FFT butterfly for the dyadic tower:
take `H = μ_{2^{k-1}}`, `c = ζ_k` a primitive `2^k`-th root, `G = μ_{2^k}`. -/
theorem eta_split_of_disjoint_coset (ψ : AddChar F ℂ) (H : Finset F) (c : F) (b : F)
    (G : Finset F) (hunion : G = H ∪ H.image (fun y => c * y))
    (hdisj : Disjoint H (H.image (fun y => c * y)))
    (hinj : Set.InjOn (fun y => c * y) H) :
    eta ψ G b = eta ψ H b + eta ψ H (b * c) := by
  classical
  subst hunion
  have hcoset : eta ψ (H.image (fun y => c * y)) b = eta ψ H (b * c) := by
    rw [eta, eta, Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [mul_comm b c, mul_assoc]
  rw [← hcoset]
  show eta ψ (H ∪ H.image (fun y => c * y)) b = _
  rw [eta, Finset.sum_union hdisj]
  rfl

/-- **The only unconditional consequence: trivial doubling.** From the butterfly identity, the
worst-case modulus over `G` is at most twice that over `H`. If `Mprev` bounds `‖η_H(d)‖` for ALL
`d` (in particular `d = b` and `d = b·c`), then `‖η_G(b)‖ ≤ 2·Mprev`. Telescoping over `μ` levels
yields only `M_μ ≤ 2^μ = n`; there is no `√2` per-step gain available here. -/
theorem eta_le_two_mul_of_split (ψ : AddChar F ℂ) (H : Finset F) (c b : F)
    (G : Finset F) (hunion : G = H ∪ H.image (fun y => c * y))
    (hdisj : Disjoint H (H.image (fun y => c * y)))
    (hinj : Set.InjOn (fun y => c * y) H)
    (Mprev : ℝ) (hM : ∀ d : F, ‖eta ψ H d‖ ≤ Mprev) :
    ‖eta ψ G b‖ ≤ 2 * Mprev := by
  rw [eta_split_of_disjoint_coset ψ H c b G hunion hdisj hinj]
  calc ‖eta ψ H b + eta ψ H (b * c)‖
      ≤ ‖eta ψ H b‖ + ‖eta ψ H (b * c)‖ := norm_add_le _ _
    _ ≤ Mprev + Mprev := add_le_add (hM b) (hM (b * c))
    _ = 2 * Mprev := by ring

/-- **The wall, stated as the missing per-step contraction.** The square-root-cancellation /
near-Ramanujan bound requires, INDUCTIVELY, the per-step contraction
`‖η_G(b)‖ ≤ √2 · M_H` uniform in `b`. This predicate names exactly that obligation. It is OPEN
(equivalently the Paley-graph / BGK wall): numerically `‖η_G(b)‖/M_H` exceeds `√2` at many steps
(probe `probe_dyadic_cocycle_recursion.py`), so no soft argument from the butterfly identity proves
it. We record it as a named open `Prop`, not a theorem. -/
def DyadicPerStepContraction (ψ : AddChar F ℂ) (H G : Finset F) (Mprev : ℝ) : Prop :=
  ∀ b : F, ‖eta ψ G b‖ ≤ Real.sqrt 2 * Mprev

/-- The per-step contraction, if it held at every dyadic level, would telescope to the
near-Ramanujan scale. This is the conditional bridge — purely the inductive step, with the open
contraction as the named hypothesis. It demonstrates the contraction is the EXACT lever, and that
it is genuinely the wall (the hypothesis is the thing refuted numerically per-step). -/
theorem eta_le_of_perStepContraction (ψ : AddChar F ℂ) (H G : Finset F) (Mprev : ℝ)
    (h : DyadicPerStepContraction ψ H G Mprev) (b : F) :
    ‖eta ψ G b‖ ≤ Real.sqrt 2 * Mprev :=
  h b

end ArkLib.ProximityGap.Attack01DyadicButterfly

#print axioms ArkLib.ProximityGap.Attack01DyadicButterfly.eta_split_of_disjoint_coset
#print axioms ArkLib.ProximityGap.Attack01DyadicButterfly.eta_le_two_mul_of_split
#print axioms ArkLib.ProximityGap.Attack01DyadicButterfly.eta_le_of_perStepContraction

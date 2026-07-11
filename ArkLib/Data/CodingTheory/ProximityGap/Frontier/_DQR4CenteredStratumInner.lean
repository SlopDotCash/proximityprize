/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DQR4GeneralStratumRepCorrelation

/-!
# DQR-4 centered stratum form + the stratum-CS reconnection no-go — #466

Two closing bricks for the DQR-4 exact data layer.

**1. The centered inner-product form (exact).** In the general stratum law
`T_k := ∑_{b≠0} η_b^k·η_{b·a}^{14−k} = q·N_{k,14−k}(a) − n^{14}`, the subtracted term is
EXACTLY the mean-field part of the correlation: writing `f̂_d = f_d − n^d/q` (centered rep
function), `∑_c f_j(c)·f_k(−ac) = n^{j+k}/q + ⟨f̂_j, f̂_k ∘ dil_{−a}⟩`, so

  `T_k = q·⟨f̂_{14−k}, f̂_k ∘ dil_{−a}⟩`  —  no DC residue at any stratum.

Stated here in the division-free integer-friendly form
`q·N_{k,j}(a) − n^{k+j} = ∑_c (q·f_j(c) − n^j)·f_k(−ac) · (1/1)`-normalized as
`q·∑_c (q·f_j(c) − n^j)·(q·f_k(−ac) − n^k) = q²·(q·N − n^{j+k})` (both sides cleared of
denominators; `centeredStratum_identity` below).

**2. The stratum-CS reconnection no-go (falsify-first record).** Applying Cauchy–Schwarz to
the centered inner product gives `|T_k| ≤ √(Ŝ_{2k}·Ŝ_{2(14−k)})` (Parseval: count-side CS =
frequency-side CS), with `2(14−k)` up to 26 — DEPTH-INCREASING. This is precisely the
machine-refuted doubling/Hölder face (`_DoublingHolderWallCircular`): stratum-wise CS on the
centered ledger reproduces the known circular wall and MUST NOT be used as the contraction
input. Any viable DQR-4 argument must exploit the twist-point structure (which cosets of the
sparse `f̂_k` support the dilation `−a` sends onto the `f̂_{14−k}` support) rather than
stratum-wise norms. Issue #466. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.DQR4CrossMomentRepLocalization
open ArkLib.ProximityGap.Frontier.DQR4GeneralStratumRepCorrelation

namespace ArkLib.ProximityGap.Frontier.DQR4CenteredStratumInner

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The centered stratum identity (denominator-cleared, exact over ℤ-casts in ℂ)**: the
correlation of the CENTERED rep functions equals `q` times the centered mixed count:

  `∑_c (q·f_j(c) − n^j)·(q·f_k(−a·c) − n^k) = q·(q·N_{k,j}(a) − n^{j+k})`.

Hence the ledger stratum `T_k = q·N − n^{14}` is exactly `1/q` times a centered-centered
correlation: NO DC residue survives at any stratum. -/
theorem centeredStratum_identity (G : Finset F) (k j : ℕ) {a : F} (ha : a ≠ 0) :
    ∑ c : F, ((Fintype.card F : ℂ) * (repCount G j c : ℂ) - (G.card : ℂ) ^ j)
        * ((Fintype.card F : ℂ) * (repCount G k (-(a * c)) : ℂ) - (G.card : ℂ) ^ k)
      = (Fintype.card F : ℂ) *
          ((Fintype.card F : ℂ) * (mixedSolutionCount G k j a : ℂ)
            - (G.card : ℂ) ^ (k + j)) := by
  have hq : (0 : ℕ) < Fintype.card F := Fintype.card_pos
  -- expand the product; three of the four pieces are computable masses.
  have hmassj : ∑ c : F, (repCount G j c : ℂ) = (G.card : ℂ) ^ j := by
    rw [← Nat.cast_pow, ← sum_repCount G j]
    push_cast
    rfl
  have hmassk : ∑ c : F, (repCount G k (-(a * c)) : ℂ) = (G.card : ℂ) ^ k := by
    rw [← Nat.cast_pow, ← sum_repCount G k]
    push_cast
    -- `c ↦ −(a·c)` is a bijection of `F`.
    have hbij : Function.Bijective (fun c : F => -(a * c)) := by
      constructor
      · intro x y h
        exact mul_left_cancel₀ ha (neg_injective h)
      · intro y
        refine ⟨-(a⁻¹ * y), ?_⟩
        field_simp
    exact Fintype.sum_bijective _ hbij _ _ (fun c => rfl)
  have hcorr : ∑ c : F, (repCount G j c : ℂ) * (repCount G k (-(a * c)) : ℂ)
      = (mixedSolutionCount G k j a : ℂ) := by
    rw [mixedSolutionCount_eq_repCorrelation G k j a]
    push_cast
    rfl
  -- expand and collect.
  · have hexp : ∑ c : F, ((Fintype.card F : ℂ) * (repCount G j c : ℂ) - (G.card : ℂ) ^ j)
        * ((Fintype.card F : ℂ) * (repCount G k (-(a * c)) : ℂ) - (G.card : ℂ) ^ k)
        = (Fintype.card F : ℂ) ^ 2 * (mixedSolutionCount G k j a : ℂ)
          - (Fintype.card F : ℂ) * (G.card : ℂ) ^ k * (G.card : ℂ) ^ j
          - (Fintype.card F : ℂ) * (G.card : ℂ) ^ j * (G.card : ℂ) ^ k
          + (Fintype.card F : ℂ) * (G.card : ℂ) ^ j * (G.card : ℂ) ^ k := by
      have hcard : ∑ _c : F, ((G.card : ℂ) ^ j * (G.card : ℂ) ^ k)
          = (Fintype.card F : ℂ) * ((G.card : ℂ) ^ j * (G.card : ℂ) ^ k) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc ∑ c : F, ((Fintype.card F : ℂ) * (repCount G j c : ℂ) - (G.card : ℂ) ^ j)
          * ((Fintype.card F : ℂ) * (repCount G k (-(a * c)) : ℂ) - (G.card : ℂ) ^ k)
          = (Fintype.card F : ℂ) ^ 2 *
              ∑ c : F, (repCount G j c : ℂ) * (repCount G k (-(a * c)) : ℂ)
            - (Fintype.card F : ℂ) * (G.card : ℂ) ^ k * ∑ c : F, (repCount G j c : ℂ)
            - (Fintype.card F : ℂ) * (G.card : ℂ) ^ j *
                ∑ c : F, (repCount G k (-(a * c)) : ℂ)
            + ∑ _c : F, ((G.card : ℂ) ^ j * (G.card : ℂ) ^ k) := by
            rw [show (∑ c : F, ((Fintype.card F : ℂ) * (repCount G j c : ℂ)
                  - (G.card : ℂ) ^ j)
                * ((Fintype.card F : ℂ) * (repCount G k (-(a * c)) : ℂ)
                  - (G.card : ℂ) ^ k))
              = ∑ c : F, ((Fintype.card F : ℂ) ^ 2 *
                    ((repCount G j c : ℂ) * (repCount G k (-(a * c)) : ℂ))
                  - (Fintype.card F : ℂ) * (G.card : ℂ) ^ k * (repCount G j c : ℂ)
                  - (Fintype.card F : ℂ) * (G.card : ℂ) ^ j
                      * (repCount G k (-(a * c)) : ℂ)
                  + (G.card : ℂ) ^ j * (G.card : ℂ) ^ k)
              from Finset.sum_congr rfl (fun c _ => by ring)]
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
        _ = _ := by rw [hcorr, hmassj, hmassk, hcard]; ring
    rw [hexp, pow_add]
    ring

end ArkLib.ProximityGap.Frontier.DQR4CenteredStratumInner

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms
  ArkLib.ProximityGap.Frontier.DQR4CenteredStratumInner.centeredStratum_identity

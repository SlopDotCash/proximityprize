/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliza
-/

import ArkLib.Data.CodingTheory.ProximityGap.ProximityGapP
import ArkLib.ProofSystem.Whir.MCAJohnsonCurveExtract

/-!
# Full Vandermonde curve MCA: multi-slope joint extraction and the `epsMCAP` bound

This file deepens [`ProximityGapP.lean`](ProximityGapP.lean) for the **full Vandermonde curve
generator** `r ↦ (1, γ, …, γ^{parℓ−1})` — i.e. the canonical Reed–Solomon power generator with
`exp j = (j : ℕ)`, matching `RSGenerator.genRSC` (`ProximityGen.lean`) and
`MCAJohnson.curve_mutual_extract` (`MCAJohnsonCurveExtract.lean`).

`ProximityGapP.Pr_proximityConditionP_le_epsMCAP` already bounds the WHIR `proximityCondition`
probability by `epsMCAP` for a *general* exponent map via the structural "per-row failure ⟹ joint
failure" argument. That bound is one-directional in content: it never uses the algebraic structure
of the Vandermonde generator. This file supplies the missing algebraic direction for the *full
Vandermonde curve*, over Reed–Solomon codes:

> **Multi-slope joint extraction.** If, at `parℓ` *distinct* slopes `αs`, the Vandermonde curve
> combination `∑ⱼ (αs i)^j · fⱼ` is matched on a common witness set `S` by Reed–Solomon codewords,
> then the *entire* word stack `f` jointly agrees with a codeword tuple on `S`
> (`ProximityGapP.pairJointAgreesOnP`). This is exactly the joint structure whose *failure* is the
> defining clause of `ProximityGapP.mcaEventP`.

The bridge between the two layers is `MCAJohnson.curve_mutual_extract`: it inverts the
(distinct-node, hence invertible) Vandermonde system `c·eval = V *ᵥ f` to recover the tuple `p`
with `p j` interpolating `f j` on `S`.

## Main definitions

- `VandermondeMCA.vandermondeCurve` — the full Vandermonde combination `∑ⱼ γ^j • fⱼ`, i.e.
  `ProximityGapP.curveComb (Fin.val) f γ`.

## Main results

- `VandermondeMCA.vandermondeCurve_eq_curveComb` — `vandermondeCurve = curveComb Fin.val`.
- `VandermondeMCA.multislope_pairJointAgreesOnP` — **the keystone.** `parℓ` distinct slopes with
  RS-proximate Vandermonde combinations agreeing on `S` ⟹ `pairJointAgreesOnP` over the RS code.
  Built directly on `MCAJohnson.curve_mutual_extract`.
- `VandermondeMCA.multislope_excludes_mcaEventP` — contrapositive corollary: under the same
  multi-slope hypothesis, the curve combination at *any* extra slope cannot witness the MCA bad
  event `mcaEventP` (its joint-disagreement clause is refuted by the extracted tuple).
- `VandermondeMCA.Pr_proximityConditionVandermonde_le_epsMCAP` — the **full-Vandermonde
  specialization** of `ProximityGapP.Pr_proximityConditionP_le_epsMCAP`: the probability over
  `γ ←$ᵖ F` of WHIR's `proximityCondition` with the *honest* Vandermonde generator
  `r = fun j ↦ γ^(j : ℕ)` is bounded by `epsMCAP C (Fin.val) δ`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
- [ACFY24] Arnon, Chiesa, Fenzi, Yogev. *WHIR*. 2024.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace VandermondeMCA

open NNReal Code Polynomial
open scoped ProbabilityTheory BigOperators

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The **full Vandermonde curve** combination `∑ⱼ γ^j • fⱼ`, the honest Reed–Solomon power
generator `r ↦ (1, γ, …, γ^{parℓ−1})`. This is `ProximityGapP.curveComb` at the canonical
exponent `exp j = (j : ℕ)`. -/
def vandermondeCurve {parℓ : ℕ} (u : WordStack F (Fin parℓ) ι) (γ : F) : ι → F :=
  fun i => ∑ j : Fin parℓ, (γ ^ (j : ℕ)) • u j i

/-- `vandermondeCurve` is exactly `ProximityGapP.curveComb` at `exp = Fin.val`. -/
theorem vandermondeCurve_eq_curveComb {parℓ : ℕ} (u : WordStack F (Fin parℓ) ι) (γ : F) :
    vandermondeCurve u γ = ProximityGapP.curveComb (fun j : Fin parℓ => (j : ℕ)) u γ := rfl

end

/-! ## The keystone: multi-slope Vandermonde joint extraction over Reed–Solomon codes

We work with the Reed–Solomon code `ReedSolomon.code domain deg ⊆ (ι → F)`. A word `w` is in the
code iff there is a degree-`<deg` polynomial `p` with `p.eval (domain x) = w x` for all `x`. -/

section RS

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Membership in the Reed–Solomon code, unfolded to a degree-`<deg` polynomial that evaluates to
the word on every domain point. -/
theorem mem_rs_code_iff {deg : ℕ} (domain : ι ↪ F) (w : ι → F) :
    w ∈ (ReedSolomon.code domain deg : Set (ι → F)) ↔
      ∃ p : F[X], p ∈ Polynomial.degreeLT F deg ∧ ∀ x, p.eval (domain x) = w x := by
  constructor
  · rintro hw
    obtain ⟨p, hp_mem, hp_eq⟩ := hw
    exact ⟨p, hp_mem, fun x => congrFun hp_eq x⟩
  · rintro ⟨p, hp_mem, hp_eq⟩
    exact ⟨p, hp_mem, funext (fun x => hp_eq x)⟩

/-- **Keystone — multi-slope Vandermonde joint extraction.** Let `f : Fin parℓ → ι → F` be a word
stack and `αs : Fin parℓ → F` be `parℓ` *distinct* slopes. Suppose for each slope index `i` there
is a Reed–Solomon codeword `c i ∈ ReedSolomon.code domain deg` that agrees, on a common witness set
`S`, with the full Vandermonde curve combination `∑ⱼ (αs i)^j · fⱼ`. Then the *entire* stack `f`
jointly agrees with a tuple of RS-codewords on `S`, i.e. `ProximityGapP.pairJointAgreesOnP` holds.

This is the algebraic content of mutual correlated agreement for the full Vandermonde generator:
distinct slopes make the Vandermonde matrix invertible, so `MCAJohnson.curve_mutual_extract`
recovers a degree-`<deg` polynomial tuple `p` interpolating the whole stack on `S`. -/
theorem multislope_pairJointAgreesOnP {parℓ : ℕ} {deg : ℕ} (domain : ι ↪ F)
    (αs : Fin parℓ → F) (hα : Function.Injective αs)
    (f : Fin parℓ → ι → F) (S : Finset ι)
    (cw : Fin parℓ → ι → F)
    (hcw_mem : ∀ i, cw i ∈ (ReedSolomon.code domain deg : Set (ι → F)))
    (hcw_eq : ∀ i, ∀ x ∈ S, cw i x = vandermondeCurve f (αs i) x) :
    ProximityGapP.pairJointAgreesOnP (ReedSolomon.code domain deg : Set (ι → F)) S f := by
  classical
  -- Pull each codeword back to a degree-`<deg` polynomial.
  have hpoly : ∀ i, ∃ p : F[X], p ∈ Polynomial.degreeLT F deg ∧
      ∀ x, p.eval (domain x) = cw i x := fun i => (mem_rs_code_iff domain (cw i)).mp (hcw_mem i)
  choose c hc_mem hc_eval using hpoly
  -- The hypothesis of `curve_mutual_extract`: at every `x ∈ S` and slope `i`,
  -- `(c i).eval (domain x) = ∑ⱼ (αs i)^j * f j x`.
  have hcurve : ∀ x ∈ S, ∀ i,
      (c i).eval (domain x) = ∑ j : Fin parℓ, (αs i) ^ (j : ℕ) * f j x := by
    intro x hx i
    rw [hc_eval i x, hcw_eq i x hx]
    simp only [vandermondeCurve, smul_eq_mul]
  -- Invert the Vandermonde system to recover the whole-stack polynomial tuple.
  obtain ⟨p, hp_mem, hp_eq⟩ :=
    MCAJohnson.curve_mutual_extract domain αs hα c hc_mem f hcurve
  -- Repackage the polynomial tuple as a codeword tuple agreeing on `S`.
  refine ⟨fun j => fun x => (p j).eval (domain x), ?_, ?_⟩
  · intro j
    exact (mem_rs_code_iff domain _).mpr ⟨p j, hp_mem j, fun x => rfl⟩
  · intro x hx j
    exact hp_eq x hx j

/-- **Contrapositive corollary.** Under the multi-slope extraction hypothesis of
`multislope_pairJointAgreesOnP`, the MCA bad event `mcaEventP` at the full Vandermonde generator
(`exp = Fin.val`) can never hold *on this witness set `S`*, at any slope `γ`: the bad event's
joint-disagreement clause `¬ pairJointAgreesOnP C S f` is directly refuted by the extracted tuple.

We phrase this via the negation of a `mcaEventP`-style conjunction *pinned to `S`*: there is no
slope `γ` and codeword `w` agreeing with the Vandermonde curve on `S` together with joint
disagreement on `S`. Once `parℓ` distinct slopes admit RS-proximate Vandermonde combinations
agreeing on the common `S`, the joint-disagreement clause is impossible on `S`. -/
theorem multislope_excludes_mcaEventP {parℓ : ℕ} {deg : ℕ} (domain : ι ↪ F)
    (αs : Fin parℓ → F) (hα : Function.Injective αs)
    (f : Fin parℓ → ι → F) (S : Finset ι)
    (cw : Fin parℓ → ι → F)
    (hcw_mem : ∀ i, cw i ∈ (ReedSolomon.code domain deg : Set (ι → F)))
    (hcw_eq : ∀ i, ∀ x ∈ S, cw i x = vandermondeCurve f (αs i) x)
    (γ : F) :
    ¬ ((∃ w ∈ (ReedSolomon.code domain deg : Set (ι → F)),
          ∀ x ∈ S, w x = vandermondeCurve f γ x) ∧
        ¬ ProximityGapP.pairJointAgreesOnP
            (ReedSolomon.code domain deg : Set (ι → F)) S f) := by
  rintro ⟨_, hpair⟩
  exact hpair (multislope_pairJointAgreesOnP domain αs hα f S cw hcw_mem hcw_eq)

end RS

/-! ## WHIR `proximityCondition` (full Vandermonde generator) bound by `epsMCAP`

The full-Vandermonde specialization of `ProximityGapP.Pr_proximityConditionP_le_epsMCAP`, obtained
by instantiating the general exponent map at `exp = Fin.val`. The generator is now the honest
`r = fun j ↦ γ^(j : ℕ) = (1, γ, …, γ^{parℓ−1})`. -/

section WHIR

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {parℓ : ℕ}

/-- **Predicate bridge (full Vandermonde).** The `exp = Fin.val` specialization of
`ProximityGapP.proximityConditionP_imp_mcaEventP`: WHIR's `proximityCondition` with the honest
Vandermonde generator `r = fun j ↦ γ^(j : ℕ)` gives the `parℓ`-ary MCA event at
`exp = Fin.val`. -/
theorem proximityConditionVandermonde_imp_mcaEventP
    {C : LinearCode ι F} {δ : ℝ≥0} (hδ : δ < 1)
    (f : Fin parℓ → ι → F) (γ : F)
    (h : MutualCorrAgreement.proximityCondition (parℓ := Fin parℓ) f δ
        (fun j => γ ^ (j : ℕ)) C) :
    ProximityGapP.mcaEventP (F := F) (A := F) (C : Set (ι → F))
      (fun j : Fin parℓ => (j : ℕ)) δ f γ :=
  ProximityGapP.proximityConditionP_imp_mcaEventP hδ (fun j : Fin parℓ => (j : ℕ)) f γ h

/-- **Full-Vandermonde specialization of `Pr_proximityConditionP_le_epsMCAP`.** For any word stack
`f : Fin parℓ → ι → F`, the probability over `γ ←$ᵖ F` of WHIR's `proximityCondition` with the
honest Vandermonde generator `r = fun j ↦ γ^(j : ℕ) = (1, γ, …, γ^{parℓ−1})` is bounded by the
`parℓ`-ary MCA error `epsMCAP C (Fin.val) δ`.

This is the bound downstream WHIR proofs need to cite at the *true* `genRSC` generator
(`ProximityGen.lean`), not merely the affine line. -/
theorem Pr_proximityConditionVandermonde_le_epsMCAP
    {C : LinearCode ι F} {δ : ℝ≥0} (hδ : δ < 1)
    (f : Fin parℓ → ι → F) :
    Pr_{let γ ← $ᵖ F}[MutualCorrAgreement.proximityCondition (parℓ := Fin parℓ) f δ
        (fun j => γ ^ (j : ℕ)) C]
      ≤ ProximityGapP.epsMCAP (F := F) (A := F) (C : Set (ι → F))
          (fun j : Fin parℓ => (j : ℕ)) δ :=
  ProximityGapP.Pr_proximityConditionP_le_epsMCAP hδ (fun j : Fin parℓ => (j : ℕ)) f

end WHIR

end VandermondeMCA

-- Per-theorem axiom audit. Every theorem must reduce to exactly
-- `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no extra axioms).
#print axioms VandermondeMCA.vandermondeCurve_eq_curveComb
#print axioms VandermondeMCA.mem_rs_code_iff
#print axioms VandermondeMCA.multislope_pairJointAgreesOnP
#print axioms VandermondeMCA.multislope_excludes_mcaEventP
#print axioms VandermondeMCA.proximityConditionVandermonde_imp_mcaEventP
#print axioms VandermondeMCA.Pr_proximityConditionVandermonde_le_epsMCAP

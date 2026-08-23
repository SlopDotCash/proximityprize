/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StackJointAgreement
import Mathlib

/-!
# Generator-MCA: `ℓ`-ary mutual correlated agreement for an arbitrary generator

This file sets up the **generator MCA** framework of [Jo26] (ePrint 2026/891,
Definition 2.6) in the in-tree style of
[`Errors.lean`](Errors.lean) and
[`InterleavingStabilityMCA.lean`](InterleavingStabilityMCA.lean), toward the field-size
weighted interleaving bound of [Jo26] Theorem 4.2:

  `ε_G(C, δ) ≤ ε_G(C^≡s, δ) ≤ A(q,s) · ε_G(C, δ)`,  `A(q,s) = (q^s − 1)/(q^{s−1}(q−1))`.

## Main definitions

* `stackJointAgreesOn` — imported row-index-general joint agreement of a word stack with a
  tuple of codewords on a position set `S`; generalizes `pairJointAgreesOn` (the `ℓ = 2`
  case, bridged by `stackJointAgreesOn_two_iff`).
* `mcaWitnessG` / `mcaEventG` — [Jo26] Definition 2.6: `T ⊆ [n]` is a `G`-MCA witness for
  `(f, ω)` iff `|T| ≥ (1−δ)·n`, the combination `∑ⱼ Gⱼ(ω)·fⱼ` agrees with a codeword on
  `T`, and the stack does **not** jointly agree with codewords on `T`.  The combination
  coefficients enter as an abstract vector `coeffs : Fin ℓ → F` (instantiated at `G ω`).
* `epsMCAG` — the generator-MCA error: worst case over stacks `f` of
  `Pr_{ω ← $ᵖ Ω}[mcaEventG C δ f (G ω)]`.
* `jointStackSubmodule` — the `ℓ`-ary bad-combiner subspace `K ⊆ F^s` of [Jo26]
  Lemma 4.1: vectors `λ` whose row-combined base stack jointly agrees on `S`; a
  submodule by linearity, generalizing `jointPairSubmodule`.

## Main results

* `stackJointAgreesOn_two_iff` — `ℓ = 2` joint agreement coincides with
  `pairJointAgreesOn`.
* `mcaEventG_affineLine_iff` / `epsMCAG_affineLine_eq` — at `ℓ = 2`, `Ω = F`,
  `G γ = (1, γ)` (the affine-line generator), the generator MCA error **is** the in-tree
  `epsMCA` of [ABF26] Definition 4.3.
* `jointStackSubmodule_ne_top` — [Jo26] Lemma 4.1 core step, `ℓ`-ary: if the interleaved
  stack does not jointly agree over `C^⋈(Fin s)` on `S`, the bad-combiner subspace is
  proper (standard basis vectors would reconstruct interleaved agreement row by row).

## References

* [Jo26] S. Jo, *Interleaving Stability for Mutual Correlated Agreement and Curve
  Decodability*, ePrint 2026/891.
* [ABF26] G. Arnon, D. Boneh, G. Fenzi, *Open Problems in List Decoding and Correlated
  Agreement*, ePrint 2026/680.
-/

namespace ProximityGap

open Finset NNReal Code
open scoped ProbabilityTheory BigOperators

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ### Generator MCA ([Jo26] Definition 2.6) -/

/-- **[Jo26] Definition 2.6 (witness form).**  `T` is a `G`-MCA witness for the stack `f`
at combination coefficients `coeffs` (instantiated at `G ω` downstream): `T` has at least
`(1−δ)·n` positions, the combined word `i ↦ ∑ⱼ coeffsⱼ • fⱼ i` agrees with some codeword
of `C` on `T`, and the stack does **not** jointly agree with codewords of `C` on `T`. -/
def mcaWitnessG (C : Set (ι → A)) (δ : ℝ≥0) {l : ℕ} (f : Fin l → ι → A)
    (coeffs : Fin l → F) (T : Finset ι) : Prop :=
  (T.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
  (∃ w ∈ C, ∀ i ∈ T, w i = ∑ j, coeffs j • f j i) ∧
  ¬ stackJointAgreesOn C T f

/-- **[Jo26] Definition 2.6 (bad-seed event).**  Some witness set `T` exists; the seed
`ω` enters through `coeffs = G ω`.  At `ℓ = 2`, `coeffs = (1, γ)` this is `mcaEvent`
(`mcaEventG_affineLine_iff`). -/
def mcaEventG (C : Set (ι → A)) (δ : ℝ≥0) {l : ℕ} (f : Fin l → ι → A)
    (coeffs : Fin l → F) : Prop :=
  ∃ T : Finset ι, mcaWitnessG C δ f coeffs T

open Classical in
/-- **[Jo26] Definition 2.6 (generator MCA error).**  Worst case over word stacks
`f : Fin ℓ → (ι → A)` of the probability over a uniform seed `ω ← $ᵖ Ω` that the
combination coefficients `G ω` make the stack `G`-MCA-bad.  The affine-line generator
(`Ω = F`, `G γ = (1, γ)`) recovers `epsMCA` (`epsMCAG_affineLine_eq`). -/
noncomputable def epsMCAG (C : Set (ι → A)) (δ : ℝ≥0) {l : ℕ}
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (G : Ω → Fin l → F) : ENNReal :=
  ⨆ f : WordStack A (Fin l) ι,
    Pr_{let ω ← $ᵖ Ω}[mcaEventG C δ f (G ω)]

/-! ### The affine-line bridge: generator MCA at `G γ = (1, γ)` is `epsMCA` -/

/-- Pointwise event bridge: at `coeffs = ![1, γ]` the generator MCA event for the stack
`u` is exactly the in-tree `mcaEvent` for the pair `(u 0, u 1)` at `γ`.  The `Fin 2`
combination `∑ j, ![1, γ] j • u j i` unfolds to `u 0 i + γ • u 1 i` (via `one_smul`),
and stack joint agreement collapses to `pairJointAgreesOn`. -/
theorem mcaEventG_affineLine_iff (C : Set (ι → A)) (δ : ℝ≥0)
    (u : WordStack A (Fin 2) ι) (γ : F) :
    mcaEventG C δ u ![1, γ] ↔ mcaEvent C δ (u 0) (u 1) γ := by
  have hline : ∀ i : ι,
      (∑ j, (![1, γ] : Fin 2 → F) j • u j i) = u 0 i + γ • u 1 i := by
    intro i
    simp [Fin.sum_univ_two]
  constructor
  · rintro ⟨T, hcard, ⟨w, hw, hag⟩, hno⟩
    refine ⟨T, hcard, ⟨w, hw, fun i hi => ?_⟩, fun hpair =>
      hno ((stackJointAgreesOn_two_iff C T u).mpr hpair)⟩
    rw [hag i hi]
    exact hline i
  · rintro ⟨S, hcard, ⟨w, hw, hag⟩, hno⟩
    refine ⟨S, hcard, ⟨w, hw, fun i hi => ?_⟩, fun hstack =>
      hno ((stackJointAgreesOn_two_iff C S u).mp hstack)⟩
    rw [hag i hi]
    exact (hline i).symm

open Classical in
/-- **Affine-line bridge.**  The generator MCA error at `ℓ = 2`, `Ω = F`,
`G γ = (1, γ)` is exactly the [ABF26] mutual correlated agreement error `epsMCA`. -/
theorem epsMCAG_affineLine_eq (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCAG (A := A) C δ (fun γ : F => ![1, γ]) = epsMCA (F := F) C δ := by
  unfold epsMCAG epsMCA
  refine iSup_congr fun u => le_antisymm ?_ ?_
  · exact Pr_le_Pr_of_implies _ _ _ fun γ h =>
      (mcaEventG_affineLine_iff C δ u γ).mp h
  · exact Pr_le_Pr_of_implies _ _ _ fun γ h =>
      (mcaEventG_affineLine_iff C δ u γ).mpr h

/-! ### The `ℓ`-ary bad-combiner subspace ([Jo26] Lemma 4.1) -/

open Classical in
/-- The set of combination vectors `λ ∈ F^s` whose row-combined base stack
`(j, i) ↦ ∑ₖ λₖ • U j i k` jointly agrees with codewords of `C` on `S`.  Linearity of
`C` makes this a subspace: joint witnesses add, scale, and the zero combination is
witnessed by the zero tuple.  This is the `ℓ`-ary generalization of
`jointPairSubmodule` and the subspace `K_ω` of [Jo26] Lemma 4.1. -/
def jointStackSubmodule (C : Submodule F (ι → A)) (S : Finset ι) {l s : ℕ}
    (U : Fin l → ι → Fin s → A) : Submodule F (Fin s → F) where
  carrier := {lam | stackJointAgreesOn (C : Set (ι → A)) S
    (fun j i => ∑ k, lam k • U j i k)}
  zero_mem' := by
    refine ⟨fun _ => 0, fun j => C.zero_mem, fun i hi j => ?_⟩
    simp
  add_mem' := by
    rintro lam lam' ⟨cs, hcs, hag⟩ ⟨cs', hcs', hag'⟩
    refine ⟨fun j => cs j + cs' j, fun j => C.add_mem (hcs j) (hcs' j),
      fun i hi j => ?_⟩
    have h1 := hag i hi j
    have h2 := hag' i hi j
    dsimp only at h1 h2 ⊢
    calc (cs j + cs' j) i
        = (∑ k, lam k • U j i k) + ∑ k, lam' k • U j i k := by
          rw [Pi.add_apply, h1, h2]
      _ = ∑ k, (lam + lam') k • U j i k := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun k _ => by rw [Pi.add_apply, add_smul]
  smul_mem' := by
    rintro c lam ⟨cs, hcs, hag⟩
    refine ⟨fun j => c • cs j, fun j => C.smul_mem c (hcs j), fun i hi j => ?_⟩
    have h1 := hag i hi j
    dsimp only at h1 ⊢
    calc (c • cs j) i = c • ∑ k, lam k • U j i k := by rw [Pi.smul_apply, h1]
      _ = ∑ k, (c • lam) k • U j i k := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun k _ => by
            rw [Pi.smul_apply, smul_smul, smul_eq_mul]

open Classical in
/-- **Properness of the bad-combiner subspace** ([Jo26] Lemma 4.1, core step, `ℓ`-ary).
If every combination vector `λ ∈ F^s` admitted a joint codeword tuple on `S`, then in
particular every standard basis vector `e_k` would — i.e. every *column* `k` of the
interleaved stack would jointly agree on `S` — and the per-column witnesses assemble
into a joint codeword tuple for the interleaved stack over `C^⋈(Fin s)` on `S`,
contradicting the hypothesis. -/
theorem jointStackSubmodule_ne_top (C : Submodule F (ι → A)) {S : Finset ι} {l s : ℕ}
    (U : Fin l → ι → Fin s → A)
    (hnostack : ¬ stackJointAgreesOn ((C : Set (ι → A))^⋈ (Fin s)) S U) :
    jointStackSubmodule C S U ≠ ⊤ := by
  intro htop
  apply hnostack
  have hcol : ∀ k : Fin s, stackJointAgreesOn (C : Set (ι → A)) S
      (fun j i => U j i k) := by
    intro k
    have hmem : (Pi.single k (1 : F)) ∈ jointStackSubmodule C S U := by
      rw [htop]; trivial
    obtain ⟨cs, hcs, hag⟩ := hmem
    have hsum : ∀ (j : Fin l) (i : ι),
        (∑ k', (Pi.single k (1 : F) : Fin s → F) k' • U j i k') = U j i k := by
      intro j i
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, zero_smul]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    refine ⟨cs, hcs, fun i hi j => ?_⟩
    have h := hag i hi j
    dsimp only at h ⊢
    rw [hsum j i] at h
    exact h
  choose V hV hagree using hcol
  refine ⟨fun j i k => V k j i, ?_, fun i hi j => ?_⟩
  · intro j k
    exact hV k j
  · funext k
    exact hagree k i hi j

end ProximityGap

/-! ## Axiom audit -/
#print axioms ProximityGap.stackJointAgreesOn
#print axioms ProximityGap.stackJointAgreesOn_two_iff
#print axioms ProximityGap.mcaWitnessG
#print axioms ProximityGap.mcaEventG
#print axioms ProximityGap.epsMCAG
#print axioms ProximityGap.mcaEventG_affineLine_iff
#print axioms ProximityGap.epsMCAG_affineLine_eq
#print axioms ProximityGap.jointStackSubmodule
#print axioms ProximityGap.jointStackSubmodule_ne_top

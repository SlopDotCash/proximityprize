/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.Folding
import ArkLib.ProofSystem.Whir.MCARscPairUDR

/-!
# A unique-decoding-regime instance of `Fold.GenMutualCorrParams`

`Fold.GenMutualCorrParams` (`Folding.lean`) is the assumption-carrying class behind ABF26
Theorem 4.20 (`folding_listdecoding_if_genMutualCorrAgreement`): it packages, for each fold
level `i ≤ k`, a pair power proximity generator for `RS[F, ι^{2^i}, 2^{m−i}]` together with
the *assumption* (field `h`) that it has mutual correlated agreement. Like its RBR-soundness
sibling (`WhirIOP.GenMutualCorrParams`), it previously had **no instance anywhere** — the
`h` field at `BStar = √ρ` is ACFY24 Conjecture 4.12.

This file constructs the first honest instance, in the **unique-decoding regime**, with the
Corollary 4.11 bounds `BStar i = (1 + ρᵢ)/2` and `errStar i = 2^{m−i}/(ρᵢ·|F|) = |ιᵢ|/|F|`,
discharged per level by the unconditional `MutualCorrAgreement.mca_rsc_pair_holds`
(`MCARscPairUDR.lean`). The caller supplies exactly the data the class stores (the per-level
power-domain embeddings and their instances) plus the degree bounds
`2^{m−i} ≤ |ι^{2^i}|`; every propositional field is **proven**.

This makes the Theorem 4.20 surface consumable in the unique-decoding regime; the `√ρ`
(Johnson) regime remains open and is untouched.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at EOF).
-/

namespace Fold

open MutualCorrAgreement Generator ReedSolomon BlockRelDistance NNReal
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

variable {F : Type} [Field F] [DecidableEq F] [Fintype F]
         {ι : Type}

/-- The level-`i` pair power generator (`parℓ = Fin 2`, exponents `(0, 1)`) on the `i`-th
power domain. -/
noncomputable def pairUDRGenFold (S : Finset ι) (φ : ι ↪ F) (k m : ℕ)
    (φ_i : ∀ i : Fin (k + 1), indexPowT S φ (i : ℕ) ↪ F)
    (inst1 : ∀ i : Fin (k + 1), Fintype (indexPowT S φ (i : ℕ)))
    (inst2 : ∀ i : Fin (k + 1), Nonempty (indexPowT S φ (i : ℕ)))
    (inst3 : ∀ i : Fin (k + 1), DecidableEq (indexPowT S φ (i : ℕ)))
    (inst4 : ∀ i : Fin (k + 1), Smooth (φ_i i))
    (i : Fin (k + 1)) :
    ProximityGenerator (indexPowT S φ (i : ℕ)) F :=
  letI := inst1 i
  letI := inst2 i
  letI := inst3 i
  letI := inst4 i
  RSGenerator.genRSC (Fin 2) (φ_i i) (m - (i : ℕ)) Fin.valEmbedding

/-- **The unique-decoding-window instance of `Fold.GenMutualCorrParams`.**

Given the per-level power-domain data (embeddings `φ_i` with their instances) and the degree
bounds `2^{m−i} ≤ |ι^{2^i}|`, the folding mutual-correlated-agreement parameter class behind
ABF26 Theorem 4.20 is *constructible*, with the Corollary 4.11 unique-decoding bounds
`BStar = (1 + ρ)/2`, `errStar = 2^{m−i}/(ρ·|F|)`, all proven via `mca_rsc_pair_holds`. -/
@[reducible]
noncomputable def genMutualCorrParamsUDR (S : Finset ι) (φ : ι ↪ F) (k m : ℕ)
    (φ_i : ∀ i : Fin (k + 1), indexPowT S φ (i : ℕ) ↪ F)
    (inst1 : ∀ i : Fin (k + 1), Fintype (indexPowT S φ (i : ℕ)))
    (inst2 : ∀ i : Fin (k + 1), Nonempty (indexPowT S φ (i : ℕ)))
    (inst3 : ∀ i : Fin (k + 1), DecidableEq (indexPowT S φ (i : ℕ)))
    (inst4 : ∀ i : Fin (k + 1), Smooth (φ_i i))
    (hk : ∀ i : Fin (k + 1), 2 ^ (m - (i : ℕ)) ≤ @Fintype.card _ (inst1 i)) :
    GenMutualCorrParams S φ k := by
  classical
  have hrate_nonneg : ∀ i : Fin (k + 1),
      0 ≤ (pairUDRGenFold S φ k m φ_i inst1 inst2 inst3 inst4 i).rate := by
    intro i
    letI := inst1 i
    letI := inst2 i
    letI := inst3 i
    letI := inst4 i
    have h := rate_smoothCode_coe (φ_i i) (m - (i : ℕ)) (hk i)
    have hr : (pairUDRGenFold S φ k m φ_i inst1 inst2 inst3 inst4 i).rate
        = (2 : ℝ) ^ (m - (i : ℕ)) / (@Fintype.card _ (inst1 i) : ℝ) := by
      simpa [pairUDRGenFold, RSGenerator.genRSC] using h
    rw [hr]
    positivity
  refine
    { m := m,
      inst1 := inst1,
      inst2 := inst2,
      inst3 := inst3,
      φ_i := φ_i,
      inst4 := inst4,
      parℓ_type := fun _ => Fin 2,
      inst5 := fun _ => inferInstance,
      exp := fun _ => Fin.valEmbedding,
      Gen_α := pairUDRGenFold S φ k m φ_i inst1 inst2 inst3 inst4,
      inst6 := fun i => (pairUDRGenFold S φ k m φ_i inst1 inst2 inst3 inst4 i).hℓ,
      BStar := fun i _ _ =>
        Real.toNNReal ((1 + (pairUDRGenFold S φ k m φ_i inst1 inst2 inst3 inst4 i).rate) / 2),
      errStar := fun i _ _ => fun _δ : ℝ => ENNReal.ofReal
        ((Fintype.card (Fin 2) - 1) * (2 ^ (m - (i : ℕ)) /
          ((pairUDRGenFold S φ k m φ_i inst1 inst2 inst3 inst4 i).rate * (Fintype.card F)))),
      h := ?_,
      hcard := fun i => Fintype.card_fin 2,
      hcard' := fun _ => by simp }
  · -- the mutual correlated agreement field, from `mca_rsc_pair_holds`
    intro i
    letI := inst1 i
    letI := inst2 i
    letI := inst3 i
    letI := inst4 i
    have hmca := mca_rsc_pair_holds (0 : F) (φ_i i) (m - (i : ℕ))
      Fin.valEmbedding (hk i) (fun _ => rfl)
    unfold mca_rsc at hmca
    have h0 : 0 ≤ (1 + (pairUDRGenFold S φ k m φ_i inst1 inst2 inst3 inst4 i).rate) / 2 := by
      have := hrate_nonneg i
      linarith
    rw [Real.coe_toNNReal _ h0]
    exact hmca

end Fold

/-! ## Axiom audit — all kernel-clean. -/
#print axioms Fold.genMutualCorrParamsUDR

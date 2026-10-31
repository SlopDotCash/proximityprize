/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.General

/-!
# Finiteness/inhabitedness of challenge oracles and their propagation through composition

Sequential-composition perfect completeness requires finite, inhabited answer types for
its combined oracle `oSpec + [pSpec.Challenge]ₒ`. The Lean 4.34 VCVio interface expresses these
requirements pointwise as `∀ t, Fintype (spec.Range t)` and `∀ t, Inhabited (spec.Range t)`.
Challenge types may be infinite in general, so concrete protocols supply these hypotheses.

This module constructs the instances from finite, inhabited challenge families:

* `challengeOracle_fintype` / `challengeOracle_inhabited` expose the response instances of
  `[pSpec.Challenge]ₒ` through the default `OracleInterface`;
* `appendChallenge_fintype` / `appendChallenge_inhabited` transport the component instances
  through `ChallengeIdx.sumEquiv` and the appended challenge type equalities;
* the combined-oracle and `seqCompose` helpers propagate these instances across a whole protocol.

These are stated as `def`s returning the instance (rather than global `instance`s) so they can be
introduced locally via `haveI` exactly where a seam instance is needed, without changing global
instance resolution across the large oracle-reduction tree.
-/

open OracleComp OracleSpec ProtocolSpec

namespace ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}

/-- The challenge oracle `[pSpec.Challenge]ₒ` is `Fintype` whenever every challenge type is. This is
the `toOracleSpec`-level bridge missing from the core instance set: the response type of the `i`-th
challenge oracle is, via the default `OracleInterface`, the challenge type `pSpec.Challenge i`. -/
def challengeOracle_fintype {k : ℕ} (pSpec : ProtocolSpec k)
    [∀ i, Fintype (pSpec.Challenge i)] : ∀ t, Fintype ([pSpec.Challenge]ₒ.Range t) :=
  fun ⟨i, _q⟩ => (inferInstance : Fintype (pSpec.Challenge i))

/-- The challenge oracle `[pSpec.Challenge]ₒ` is `Inhabited` whenever every challenge type is. -/
def challengeOracle_inhabited {k : ℕ} (pSpec : ProtocolSpec k)
    [∀ i, Inhabited (pSpec.Challenge i)] : ∀ t, Inhabited ([pSpec.Challenge]ₒ.Range t) :=
  fun ⟨i, _q⟩ => (inferInstance : Inhabited (pSpec.Challenge i))

/-- Per-index finiteness of the appended challenge family: each `(pSpec₁ ++ₚ pSpec₂).Challenge j`
is `Fintype`, routed through `ChallengeIdx.sumEquiv` and the append challenge type equalities. -/
def appendChallenge_fintype {k₁ k₂ : ℕ} (pSpec₁ : ProtocolSpec k₁) (pSpec₂ : ProtocolSpec k₂)
    [∀ j, Fintype (pSpec₁.Challenge j)] [∀ j, Fintype (pSpec₂.Challenge j)] :
    ∀ j, Fintype ((pSpec₁ ++ₚ pSpec₂).Challenge j) := by
  intro j
  rcases hj : ChallengeIdx.sumEquiv.symm j with i | i
  · have hje : j = ChallengeIdx.inl i := by
      rw [← Equiv.apply_symm_apply ChallengeIdx.sumEquiv j, hj]; rfl
    rw [hje, show (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i) = pSpec₁.Challenge i by
      simp [ChallengeIdx.inl, ProtocolSpec.append, ProtocolSpec.Challenge]]
    infer_instance
  · have hje : j = ChallengeIdx.inr i := by
      rw [← Equiv.apply_symm_apply ChallengeIdx.sumEquiv j, hj]; rfl
    rw [hje, show (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i) = pSpec₂.Challenge i by
      simp [ChallengeIdx.inr, ProtocolSpec.append, ProtocolSpec.Challenge]]
    infer_instance

/-- Per-index inhabitedness of the appended challenge family. -/
def appendChallenge_inhabited {k₁ k₂ : ℕ} (pSpec₁ : ProtocolSpec k₁) (pSpec₂ : ProtocolSpec k₂)
    [∀ j, Inhabited (pSpec₁.Challenge j)] [∀ j, Inhabited (pSpec₂.Challenge j)] :
    ∀ j, Inhabited ((pSpec₁ ++ₚ pSpec₂).Challenge j) := by
  intro j
  rcases hj : ChallengeIdx.sumEquiv.symm j with i | i
  · have hje : j = ChallengeIdx.inl i := by
      rw [← Equiv.apply_symm_apply ChallengeIdx.sumEquiv j, hj]; rfl
    rw [hje, show (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i) = pSpec₁.Challenge i by
      simp [ChallengeIdx.inl, ProtocolSpec.append, ProtocolSpec.Challenge]]
    infer_instance
  · have hje : j = ChallengeIdx.inr i := by
      rw [← Equiv.apply_symm_apply ChallengeIdx.sumEquiv j, hj]; rfl
    rw [hje, show (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i) = pSpec₂.Challenge i by
      simp [ChallengeIdx.inr, ProtocolSpec.append, ProtocolSpec.Challenge]]
    infer_instance

/-- The combined oracle `oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ` is `Fintype` whenever `oSpec` is
and every challenge type of both phases is. This is exactly the seam instance demanded by the
append perfect-completeness keystones. -/
def appendCombinedOracle_fintype {k₁ k₂ : ℕ} (oSpec : OracleSpec ι)
    (pSpec₁ : ProtocolSpec k₁) (pSpec₂ : ProtocolSpec k₂) [∀ t, Fintype (oSpec.Range t)]
    [∀ j, Fintype (pSpec₁.Challenge j)] [∀ j, Fintype (pSpec₂.Challenge j)] :
    ∀ t, Fintype ((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Range t) := by
  haveI : ∀ j, Fintype ((pSpec₁ ++ₚ pSpec₂).Challenge j) :=
    appendChallenge_fintype pSpec₁ pSpec₂
  haveI := challengeOracle_fintype (pSpec₁ ++ₚ pSpec₂)
  infer_instance

/-- The combined oracle `oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ` is `Inhabited` under the same
hypotheses (inhabited form). -/
def appendCombinedOracle_inhabited {k₁ k₂ : ℕ} (oSpec : OracleSpec ι)
    (pSpec₁ : ProtocolSpec k₁) (pSpec₂ : ProtocolSpec k₂) [∀ t, Inhabited (oSpec.Range t)]
    [∀ j, Inhabited (pSpec₁.Challenge j)] [∀ j, Inhabited (pSpec₂.Challenge j)] :
    ∀ t, Inhabited ((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Range t) := by
  haveI : ∀ j, Inhabited ((pSpec₁ ++ₚ pSpec₂).Challenge j) :=
    appendChallenge_inhabited pSpec₁ pSpec₂
  haveI := challengeOracle_inhabited (pSpec₁ ++ₚ pSpec₂)
  infer_instance

/-- Per-index finiteness of the `seqCompose` challenge family, by induction on the number of
components: the empty composition has no challenge indices; the successor case is the append of the
head round with the `seqCompose` of the tail (`seqCompose_succ_eq_append`, definitional), discharged
by `appendChallenge_fintype` and the inductive hypothesis. -/
@[reducible]
def seqComposeChallenge_fintype : {m : ℕ} → {n : Fin m → ℕ} → (pSpec : ∀ i, ProtocolSpec (n i)) →
    [∀ i j, Fintype ((pSpec i).Challenge j)] → ∀ j, Fintype ((seqCompose pSpec).Challenge j)
  | 0, _, _, _ => fun j => j.1.elim0
  | _ + 1, _, pSpec, _ => by
      haveI : ∀ j, Fintype ((seqCompose (fun i => pSpec i.succ)).Challenge j) :=
        seqComposeChallenge_fintype (fun i => pSpec i.succ)
      exact appendChallenge_fintype (pSpec 0) (seqCompose (fun i => pSpec i.succ))

/-- Per-index inhabitedness of the `seqCompose` challenge family. -/
@[reducible]
def seqComposeChallenge_inhabited : {m : ℕ} → {n : Fin m → ℕ} → (pSpec : ∀ i, ProtocolSpec (n i)) →
    [∀ i j, Inhabited ((pSpec i).Challenge j)] → ∀ j, Inhabited ((seqCompose pSpec).Challenge j)
  | 0, _, _, _ => fun j => j.1.elim0
  | _ + 1, _, pSpec, _ => by
      haveI : ∀ j, Inhabited ((seqCompose (fun i => pSpec i.succ)).Challenge j) :=
        seqComposeChallenge_inhabited (fun i => pSpec i.succ)
      exact appendChallenge_inhabited (pSpec 0) (seqCompose (fun i => pSpec i.succ))

/-- The combined oracle `oSpec + [(seqCompose pSpec).Challenge]ₒ` is `Fintype` whenever `oSpec` is and
every challenge type of every component is. This is the seam instance for the full multi-round
composition (e.g. the whole sum-check protocol). -/
def seqComposeCombinedOracle_fintype {m : ℕ} {n : Fin m → ℕ} (oSpec : OracleSpec ι)
    (pSpec : ∀ i, ProtocolSpec (n i)) [∀ t, Fintype (oSpec.Range t)]
    [∀ i j, Fintype ((pSpec i).Challenge j)] :
    ∀ t, Fintype ((oSpec + [(seqCompose pSpec).Challenge]ₒ).Range t) := by
  haveI : ∀ j, Fintype ((seqCompose pSpec).Challenge j) := seqComposeChallenge_fintype pSpec
  haveI := challengeOracle_fintype (seqCompose pSpec)
  infer_instance

/-- The combined oracle `oSpec + [(seqCompose pSpec).Challenge]ₒ` is `Inhabited` under the same
hypotheses (inhabited form). -/
def seqComposeCombinedOracle_inhabited {m : ℕ} {n : Fin m → ℕ} (oSpec : OracleSpec ι)
    (pSpec : ∀ i, ProtocolSpec (n i)) [∀ t, Inhabited (oSpec.Range t)]
    [∀ i j, Inhabited ((pSpec i).Challenge j)] :
    ∀ t, Inhabited ((oSpec + [(seqCompose pSpec).Challenge]ₒ).Range t) := by
  haveI : ∀ j, Inhabited ((seqCompose pSpec).Challenge j) := seqComposeChallenge_inhabited pSpec
  haveI := challengeOracle_inhabited (seqCompose pSpec)
  infer_instance

end ProtocolSpec

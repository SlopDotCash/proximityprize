/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.General

/-!
# Finiteness/inhabitedness of challenge oracles and their propagation through composition

The sequential-composition perfect-completeness keystones
(`Reduction.append_perfectCompleteness_msg_proof` and `…_empty_proof`) require
`[(oSpec + [pSpec.Challenge]ₒ).Fintype]` and `[(oSpec + [pSpec.Challenge]ₒ).Inhabited]` on the
*combined* challenge oracle of each seam. These do **not** synthesize from `SampleableType` (nor even
from `[∀ i, Fintype (pSpec.Challenge i)]`) — there is no instance bridging per-challenge `Fintype` to
the challenge-oracle `Fintype`, and they are explicit hypotheses throughout `Completeness.lean` by
design (challenge types may be infinite in general).

This module supplies the bridge needed to *discharge* those hypotheses whenever every challenge type
is finite/inhabited — the situation for every concrete protocol (sum-check challenges are the field
`R`, etc.):

* `challengeOracle_fintype` / `challengeOracle_inhabited`: `[pSpec.Challenge]ₒ.Fintype` /
  `.Inhabited` from `[∀ i, Fintype/Inhabited (pSpec.Challenge i)]` (the missing
  `toOracleSpec`-level bridge);
* `appendChallenge_fintype` / `appendChallenge_inhabited`: per-index finiteness/inhabitedness of the
  *appended* challenge family `(pSpec₁ ++ₚ pSpec₂).Challenge`, routed through
  `ChallengeIdx.sumEquiv` and the `range_challenge_append_{inl,inr}` type equalities.

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
    [∀ i, Fintype (pSpec.Challenge i)] : [pSpec.Challenge]ₒ.Fintype where
  fintype_B := fun ⟨i, _q⟩ => (inferInstance : Fintype (pSpec.Challenge i))

/-- The challenge oracle `[pSpec.Challenge]ₒ` is `Inhabited` whenever every challenge type is. -/
def challengeOracle_inhabited {k : ℕ} (pSpec : ProtocolSpec k)
    [∀ i, Inhabited (pSpec.Challenge i)] : [pSpec.Challenge]ₒ.Inhabited where
  inhabited_B := fun ⟨i, _q⟩ => (inferInstance : Inhabited (pSpec.Challenge i))

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
    (pSpec₁ : ProtocolSpec k₁) (pSpec₂ : ProtocolSpec k₂) [oSpec.Fintype]
    [∀ j, Fintype (pSpec₁.Challenge j)] [∀ j, Fintype (pSpec₂.Challenge j)] :
    (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype := by
  haveI : ∀ j, Fintype ((pSpec₁ ++ₚ pSpec₂).Challenge j) :=
    appendChallenge_fintype pSpec₁ pSpec₂
  haveI := challengeOracle_fintype (pSpec₁ ++ₚ pSpec₂)
  infer_instance

/-- The combined oracle `oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ` is `Inhabited` under the same
hypotheses (inhabited form). -/
def appendCombinedOracle_inhabited {k₁ k₂ : ℕ} (oSpec : OracleSpec ι)
    (pSpec₁ : ProtocolSpec k₁) (pSpec₂ : ProtocolSpec k₂) [oSpec.Inhabited]
    [∀ j, Inhabited (pSpec₁.Challenge j)] [∀ j, Inhabited (pSpec₂.Challenge j)] :
    (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited := by
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
    (pSpec : ∀ i, ProtocolSpec (n i)) [oSpec.Fintype]
    [∀ i j, Fintype ((pSpec i).Challenge j)] :
    (oSpec + [(seqCompose pSpec).Challenge]ₒ).Fintype := by
  haveI : ∀ j, Fintype ((seqCompose pSpec).Challenge j) := seqComposeChallenge_fintype pSpec
  haveI := challengeOracle_fintype (seqCompose pSpec)
  infer_instance

/-- The combined oracle `oSpec + [(seqCompose pSpec).Challenge]ₒ` is `Inhabited` under the same
hypotheses (inhabited form). -/
def seqComposeCombinedOracle_inhabited {m : ℕ} {n : Fin m → ℕ} (oSpec : OracleSpec ι)
    (pSpec : ∀ i, ProtocolSpec (n i)) [oSpec.Inhabited]
    [∀ i j, Inhabited ((pSpec i).Challenge j)] :
    (oSpec + [(seqCompose pSpec).Challenge]ₒ).Inhabited := by
  haveI : ∀ j, Inhabited ((seqCompose pSpec).Challenge j) := seqComposeChallenge_inhabited pSpec
  haveI := challengeOracle_inhabited (seqCompose pSpec)
  infer_instance

end ProtocolSpec

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

/-
#314 probe — paper-faithful bad-event definitions (CO25 Defs. 5.5/5.7, Eqs. 21-27).

This file mirrors `ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean`
with exactly two repairs:

* **B2** (`redundantEntryDSPaper`, CO25 Def. 5.5): the swapped redundancy certificate for a
  permutation entry is the *opposite-direction* entry, not the same-direction one with the
  state pair reversed.
  - forward arm, 2nd disjunct: in-tree `log[j'] = ⟨.inr <|.inl stateOut, stateIn⟩`
    becomes `log[j'] = ⟨.inr <|.inr stateOut, stateIn⟩`  (`.inl ↦ .inr`);
  - inverse arm, 2nd disjunct: in-tree `log[j'] = ⟨.inr <|.inr stateIn, stateOut⟩`
    becomes `log[j'] = ⟨.inr <|.inl stateIn, stateOut⟩`  (`.inr ↦ .inl`).
  Hash arm unchanged.

* **B1** (`capacitySegmentDupPermInvPaper`, CO25 Eq. 26): the 5th disjunct of the `E_pinv`
  arm conditions on the capacity of the **query** component (`p⁻¹`'s input) of the earlier
  inverse entry, not on its answer component. In-tree (self-firing at `j' = j`):
      (∃ j' ≤ j, ∃ stateIn4 stateOut4,
        baseTrace[j'] = ⟨.inr <|.inr stateOut4, stateIn4⟩ ∧
        CanonicalSpongeState.capacitySegment stateIn4 = capSeg)
  becomes
      (∃ j' ≤ j, ∃ q a,
        baseTrace[j'] = ⟨.inr <|.inr q, a⟩ ∧
        CanonicalSpongeState.capacitySegment q = capSeg)

All other disjuncts are verbatim copies of the in-tree definitions (they were audited as
paper-faithful), and the dedup recursion/termination/fixpoint structure is copied verbatim
with `redundantEntryDS ↦ redundantEntryDSPaper`.
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEvents

open OracleComp OracleSpec ProtocolSpec
open OracleSpec.QueryLog

namespace DuplexSpongeFS.Paper

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]

/-- Paper-faithful CO25 Definition 5.5: an entry is redundant iff a prior entry answers
the same query — same direction with the same query/answer pair, or **opposite** direction
with the pair swapped. -/
def redundantEntryDSPaper (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (idx : Fin log.length) : Prop :=
  match log[idx] with
  /- Hash arm: unchanged from the in-tree definition. -/
  | ⟨.inl u, ⟨stmt, state⟩⟩ => ∃ j' < idx, log[j'] = ⟨.inl u, stmt, state⟩
  /- Forward entry `(p, sIn, sOut)`: redundant iff an earlier `(p, sIn, sOut)` or an
    earlier `(p⁻¹, sOut, sIn)` exists. -/
  | ⟨.inr (.inl stateIn), stateOut⟩ =>
    ∃ j' < idx, log[j'] = ⟨.inr (.inl stateIn), stateOut⟩ ∨
      log[j'] = ⟨.inr <|.inr stateOut, stateIn⟩
  /- Inverse entry `(p⁻¹, sOut, sIn)`: redundant iff an earlier `(p⁻¹, sOut, sIn)` or an
    earlier `(p, sIn, sOut)` exists. -/
  | ⟨.inr (.inr stateOut), stateIn⟩ =>
    ∃ j' < idx, log[j'] = ⟨.inr (.inr stateOut), stateIn⟩ ∨
      log[j'] = ⟨.inr <|.inl stateIn, stateOut⟩

/-- No entry of the trace is paper-redundant. -/
def NoRedundantEntryDSPaper (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∀ idx : Fin log.length, ¬ redundantEntryDSPaper log idx

/-- Paper-faithful dedup procedure: repeatedly erase a paper-redundant entry until none
remain (verbatim copy of the in-tree recursion with the paper redundancy predicate). -/
noncomputable def removeRedundantEntryDSPaper
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    {log : QueryLog (duplexSpongeChallengeOracle StmtIn U) | NoRedundantEntryDSPaper log} :=
  letI : Decidable (∃ idx : Fin log.length, redundantEntryDSPaper log idx) :=
    Classical.propDecidable _
  if h : ∃ idx : Fin log.length, redundantEntryDSPaper log idx then
    removeRedundantEntryDSPaper (log.eraseIdx (Classical.choose h).val)
  else
    ⟨log, fun idx => not_exists.mp h idx⟩
termination_by log.length
decreasing_by
  exact (by
    have hlt : (Classical.choose h).val < log.length := (Classical.choose h).isLt
    have heq : (log.eraseIdx (Classical.choose h).val).length + 1 = log.length :=
      List.length_eraseIdx_add_one hlt
    omega)

/-- `removeRedundantEntryDSPaper` is a fixpoint on traces already satisfying
`NoRedundantEntryDSPaper`. -/
theorem removeRedundantEntryDSPaper_eq_self_of_noRedundantEntryDSPaper
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : NoRedundantEntryDSPaper log) :
    removeRedundantEntryDSPaper log = ⟨log, h⟩ := by
  have hnone : ¬ ∃ idx : Fin log.length, redundantEntryDSPaper log idx := not_exists.mpr h
  rw [removeRedundantEntryDSPaper]
  simp [hnone]

/-- First-projection form of the fixpoint lemma. -/
theorem removeRedundantEntryDSPaper_fst_eq_self_of_noRedundantEntryDSPaper
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : NoRedundantEntryDSPaper log) :
    (removeRedundantEntryDSPaper log).1 = log := by
  rw [removeRedundantEntryDSPaper_eq_self_of_noRedundantEntryDSPaper log h]

/-- Subtype fixpoint form for the canonical output of `removeRedundantEntryDSPaper`. -/
theorem removeRedundantEntryDSPaper_eq_self
    (base : {log : QueryLog (duplexSpongeChallengeOracle StmtIn U) |
      NoRedundantEntryDSPaper log}) :
    removeRedundantEntryDSPaper base.1 = base := by
  cases base with
  | mk log h =>
      exact removeRedundantEntryDSPaper_eq_self_of_noRedundantEntryDSPaper log h

section BadEventDSPaper

variable (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))

/-- CO25 Eq. 24 (`E_h` arm) over the paper dedup; disjuncts verbatim from in-tree
`capacitySegmentDupHash`. -/
def capacitySegmentDupHashPaper : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDSPaper trace
  ∃ j : Fin baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    ∃ stmt : StmtIn, baseTrace[j] = ⟨.inl stmt, capSeg⟩ ∧
      ∃ j' < j,
        ∃ stmt', baseTrace[j'] = ⟨.inl stmt', capSeg⟩ ∨
        (∃ stateIn1 stateOut1, baseTrace[j'] = ⟨.inr <|.inl stateIn1, stateOut1⟩
          ∧ stateOut1.capacitySegment = capSeg) ∨
        (∃ stateOut2 stateIn2, baseTrace[j'] = ⟨.inr <|.inr stateOut2, stateIn2⟩
          ∧ stateIn2.capacitySegment = capSeg) ∨
        (∃ stateIn3 stateOut3, baseTrace[j'] = ⟨.inr <|.inl stateIn3, stateOut3⟩
          ∧ stateIn3.capacitySegment = capSeg) ∨
        (∃ stateOut4 stateIn4, baseTrace[j'] = ⟨.inr <|.inr stateOut4, stateIn4⟩
          ∧ stateOut4.capacitySegment = capSeg)

alias E_h_paper := capacitySegmentDupHashPaper

/-- CO25 Eq. 25 (`E_p` arm) over the paper dedup; disjuncts verbatim from in-tree
`capacitySegmentDupPerm`. -/
def capacitySegmentDupPermPaper : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDSPaper trace
  ∃ j : Fin baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stateIn stateOut, baseTrace[j] = ⟨.inr <|.inl stateIn, stateOut⟩ ∧
      stateOut.capacitySegment = capSeg) ∧
      (
        (∃ j' < j, ∃ stmt', baseTrace[j'] = ⟨.inl stmt', capSeg⟩) ∨
        (∃ j' < j, ∃ stateIn1 stateOut1, baseTrace[j'] = ⟨.inr <|.inl stateIn1, stateOut1⟩ ∧
          stateOut1.capacitySegment = capSeg) ∨
        (∃ j' ≤ j, ∃ stateOut2 stateIn2, baseTrace[j'] = ⟨.inr <|.inr stateOut2, stateIn2⟩ ∧
          stateIn2.capacitySegment = capSeg) ∨
        (∃ j' ≤ j, ∃ stateIn3 stateOut3, baseTrace[j'] = ⟨.inr <|.inl stateIn3, stateOut3⟩ ∧
          stateIn3.capacitySegment = capSeg) ∨
        (∃ j' ≤ j, ∃ stateOut4 stateIn4, baseTrace[j'] = ⟨.inr <|.inr stateOut4, stateIn4⟩ ∧
          stateOut4.capacitySegment = capSeg)
      )

alias E_p_paper := capacitySegmentDupPermPaper

/-- CO25 Eq. 26 (`E_pinv` arm) over the paper dedup. Disjuncts 1-4 verbatim from in-tree
`capacitySegmentDupPermInv`; disjunct 5 carries the **B1 repair**: it conditions on the
capacity of the *query* component (`p⁻¹`'s input) of the earlier inverse entry, mirroring
how the in-tree `E_p` disjunct 5 conditions on its query component. (The in-tree version
conditions on the answer component and is therefore self-firing at `j' = j`.) -/
def capacitySegmentDupPermInvPaper : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDSPaper trace
  ∃ j : Fin baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stateOut stateIn, baseTrace[j] = ⟨.inr <|.inr stateOut, stateIn⟩ ∧
      stateIn.capacitySegment = capSeg) ∧
      (
        (∃ j' < j, ∃ stmt', baseTrace[j'] = ⟨.inl stmt', capSeg⟩) ∨
        (∃ j' < j, ∃ stateIn1 stateOut1, baseTrace[j'] = ⟨.inr <|.inl stateIn1, stateOut1⟩ ∧
          stateOut1.capacitySegment = capSeg) ∨
        (∃ j' < j, ∃ stateIn2 stateOut2, baseTrace[j'] = ⟨.inr <|.inr stateOut2, stateIn2⟩ ∧
          CanonicalSpongeState.capacitySegment stateIn2 = capSeg) ∨
        (∃ j' ≤ j, ∃ stateIn3 stateOut3, baseTrace[j'] = ⟨.inr <|.inl stateIn3, stateOut3⟩ ∧
          stateIn3.capacitySegment = capSeg) ∨
        (∃ j' ≤ j, ∃ q a, baseTrace[j'] = ⟨.inr <|.inr q, a⟩ ∧
          CanonicalSpongeState.capacitySegment q = capSeg)
      )

alias E_pinv_paper := capacitySegmentDupPermInvPaper

/-- Paper combined capacity-collision event (CO25 Eq. 27, `E_dup` arm). -/
def capacitySegmentDupPaper : Prop :=
  capacitySegmentDupHashPaper trace ∨ capacitySegmentDupPermPaper trace ∨
    capacitySegmentDupPermInvPaper trace

alias E_dup_paper := capacitySegmentDupPaper

/-- Paper `E_func` over the paper dedup; verbatim from in-tree `notFunction`. -/
def notFunctionPaper : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDSPaper trace
  ∃ j : Fin baseTrace.length, ∃ stateIn _stateOut : CanonicalSpongeState U,
    baseTrace[j] = ⟨.inr <|.inl stateIn, _stateOut⟩ ∧
      ∃ j' < j,
        ∃ stateOut1 : CanonicalSpongeState U, baseTrace[j'] = ⟨.inr <|.inl stateIn, stateOut1⟩ ∨
        ∃ stateOut2 : CanonicalSpongeState U, baseTrace[j'] = ⟨.inr <|.inr stateOut2, stateIn⟩

alias E_func_paper := notFunctionPaper

/-- The paper-faithful combined bad event (CO25 Eq. 27). -/
def EPaper : Prop :=
  capacitySegmentDupPaper trace ∨ notFunctionPaper trace

end BadEventDSPaper

end DuplexSpongeFS.Paper

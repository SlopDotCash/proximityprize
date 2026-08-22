/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessMsg
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessEmpty

/-!
# n-ary message-seam `seqCompose` perfect completeness (issue #114)

`Reduction.seqCompose_perfectCompleteness_of_append` (in `General.lean`) reduces the n-ary
`seqCompose` perfect completeness to a binary `append` keystone — but it requires the binary keystone
to hold *unconditionally* (for every pair `R₁`, `R₂`). The proven binary keystone
`reduction_append_perfectCompleteness_msg` is only available for the **message seam** (its second
protocol starts with a `P_to_V` message), not for arbitrary seams.

This module supplies the variant `seqCompose_perfectCompleteness_of_append_msg` whose binary
hypothesis `hAppend` is restricted to "append-valid" seams: the trailing protocol is either *empty*
(0 rounds) or *starts with a `P_to_V` message*. Every component of the composition is required to be
nonempty and to start with `P_to_V` (`hValid`); this is exactly the shape of the sum-check protocol
(`Sumcheck.Spec.oracleReduction`), whose every round is a `SingleRound` starting with the prover's
univariate-polynomial message. The trailing `seqCompose` of such components is itself either empty
(when no rounds remain) or starts with `P_to_V`, discharged by `seqCompose_appendValid`.

Feeding `reduction_append_perfectCompleteness_msg` (for the nonempty message-seam case) and an
empty-trailing append-completeness lemma (for the 0-round tail) as `hAppend` then yields the full
multi-round completeness.
-/

open ProtocolSpec OracleComp
open scoped NNReal

namespace ProtocolSpec

/-- **Append-validity of a `seqCompose` of `P_to_V`-leading components.** If every component protocol
is nonempty and its first message is `P_to_V`, then their `seqCompose` is either empty (no
components) or itself nonempty with a leading `P_to_V` message. This is the side condition consumed by
the message-seam composition keystone at each induction step. -/
theorem seqCompose_appendValid {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (hValid : ∀ i, ∃ h : 0 < n i, (pSpec i).dir ⟨0, h⟩ = .P_to_V) :
    Fin.vsum n = 0 ∨ ∃ h : 0 < Fin.vsum n, (seqCompose pSpec).dir ⟨0, h⟩ = .P_to_V := by
  cases m with
  | zero => left; rfl
  | succ k =>
    right
    have h0 := hValid 0
    obtain ⟨hpos0, hdir0⟩ := h0
    have hvsum_pos : 0 < Fin.vsum n := by
      rw [Fin.vsum_succ]
      omega
    refine ⟨hvsum_pos, ?_⟩
    -- `(seqCompose pSpec).dir 0 = (pSpec 0).dir 0 = .P_to_V` via the `Fin.vflatten` at index 0
    rw [seqCompose_succ_eq_append]
    show (append (pSpec 0) (seqCompose fun i => pSpec (Fin.succ i))).dir ⟨0, hvsum_pos⟩ = .P_to_V
    rw [show (⟨0, hvsum_pos⟩ : Fin (n 0 + Fin.vsum fun i => n (Fin.succ i)))
          = (⟨0, hpos0⟩ : Fin (n 0)).castLE (by omega) from by ext; simp,
      Prover.append_dir_castLE]
    exact hdir0

/-- **General challenge-oracle finiteness.** If every challenge type of `pSpec` is finite, the
challenge oracle spec `[pSpec.Challenge]ₒ` is finite. (Individual protocols previously supplied this
by a manual per-round case split; this is the general form that lets the seqCompose/append
completeness keystones synthesize their probability instances for an arbitrary growing protocol.) -/
instance instChallengeOracleFintype {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, Fintype (pSpec.Challenge i)] : [pSpec.Challenge]ₒ.Fintype where
  fintype_B := fun q => inferInstanceAs (Fintype (pSpec.Challenge q.1))

/-- **General challenge-oracle inhabitedness.** The `Inhabited` analogue of
`instChallengeOracleFintype`. -/
instance instChallengeOracleInhabited {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, Inhabited (pSpec.Challenge i)] : [pSpec.Challenge]ₒ.Inhabited where
  inhabited_B := fun q => inferInstanceAs (Inhabited (pSpec.Challenge q.1))

end ProtocolSpec

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

set_option maxHeartbeats 1000000 in
/-- **Brick (issue #114): n-ary message-seam `seqCompose` perfect completeness.** Reduces the n-ary
`seqCompose` perfect completeness to a binary `append` keystone `hAppend` that need only hold for
*append-valid* seams (empty trailing protocol, or trailing protocol starting with `P_to_V`). Modeled
on the proven `seqCompose_perfectCompleteness_of_append`; the only addition is threading the
append-validity side condition (discharged at each step by `ProtocolSpec.seqCompose_appendValid`).
Every component is required to be nonempty and `P_to_V`-leading (`hValid`), the shape of the
sum-check protocol. -/
theorem seqCompose_perfectCompleteness_of_append_msg {m : ℕ}
    (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    (R : (i : Fin m) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i))
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (hAppend : ∀ {S₁ W₁ S₂ W₂ S₃ W₃ : Type} {k₁ k₂ : ℕ}
        {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
        [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
        (R₁ : Reduction oSpec S₁ W₁ S₂ W₂ p₁) (R₂ : Reduction oSpec S₂ W₂ S₃ W₃ p₂)
        {r₁ : Set (S₁ × W₁)} {r₂ : Set (S₂ × W₂)} {r₃ : Set (S₃ × W₃)},
        (k₂ = 0 ∨ ∃ h : 0 < k₂, p₂.dir ⟨0, h⟩ = .P_to_V) →
        R₁.perfectCompleteness init impl r₁ r₂ → R₂.perfectCompleteness init impl r₂ r₃ →
        (R₁.append R₂).perfectCompleteness init impl r₁ r₃)
    (hValid : ∀ i, ∃ h : 0 < n i, (pSpec i).dir ⟨0, h⟩ = .P_to_V)
    (h : ∀ i, (R i).perfectCompleteness init impl (rel i.castSucc) (rel i.succ)) :
    (seqCompose Stmt Wit R).perfectCompleteness init impl (rel 0) (rel (Fin.last m)) := by
  induction m with
  | zero =>
    rw [seqCompose_zero]
    simpa using
      (Reduction.id_perfectCompleteness (init := init) (impl := impl) (rel := rel 0))
  | succ m ih =>
    change ((R 0).append
        (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i))))
      |>.perfectCompleteness init impl (rel 0) (rel (Fin.succ (Fin.last m)))
    refine hAppend (R 0) _
      (ProtocolSpec.seqCompose_appendValid (fun i => hValid (Fin.succ i)))
      (h 0)
      (ih (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i))
        (fun i => rel (Fin.succ i)) (fun i => hValid (Fin.succ i)) (fun i => h (Fin.succ i)))

set_option maxHeartbeats 1000000 in
/-- Variant of `seqCompose_perfectCompleteness_of_append_msg` whose binary `hAppend` additionally
carries the challenge `Fintype`/`Inhabited` instances the binary keystones require (synthesized
per-level like the existing `SampleableType`). Crucially the induction stays *abstract* over
`hAppend`, so the heavy `OracleSpec`-sum instance synthesis is deferred to the (once, abstract)
`hAppend` proof rather than being re-run at every induction level. -/
theorem seqCompose_pc_of_append_msg' {m : ℕ}
    (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    [∀ i, ∀ j, Fintype ((pSpec i).Challenge j)]
    [∀ i, ∀ j, Inhabited ((pSpec i).Challenge j)]
    (R : (i : Fin m) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i))
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (hAppend : ∀ {S₁ W₁ S₂ W₂ S₃ W₃ : Type} {k₁ k₂ : ℕ}
        {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
        [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
        [∀ j, Fintype (p₁.Challenge j)] [∀ j, Fintype (p₂.Challenge j)]
        [∀ j, Inhabited (p₁.Challenge j)] [∀ j, Inhabited (p₂.Challenge j)]
        (R₁ : Reduction oSpec S₁ W₁ S₂ W₂ p₁) (R₂ : Reduction oSpec S₂ W₂ S₃ W₃ p₂)
        {r₁ : Set (S₁ × W₁)} {r₂ : Set (S₂ × W₂)} {r₃ : Set (S₃ × W₃)},
        (k₂ = 0 ∨ ∃ h : 0 < k₂, p₂.dir ⟨0, h⟩ = .P_to_V) →
        R₁.perfectCompleteness init impl r₁ r₂ → R₂.perfectCompleteness init impl r₂ r₃ →
        (R₁.append R₂).perfectCompleteness init impl r₁ r₃)
    (hValid : ∀ i, ∃ h : 0 < n i, (pSpec i).dir ⟨0, h⟩ = .P_to_V)
    (h : ∀ i, (R i).perfectCompleteness init impl (rel i.castSucc) (rel i.succ)) :
    (seqCompose Stmt Wit R).perfectCompleteness init impl (rel 0) (rel (Fin.last m)) := by
  induction m with
  | zero =>
    rw [seqCompose_zero]
    simpa using
      (Reduction.id_perfectCompleteness (init := init) (impl := impl) (rel := rel 0))
  | succ m ih =>
    change ((R 0).append
        (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i))))
      |>.perfectCompleteness init impl (rel 0) (rel (Fin.succ (Fin.last m)))
    refine hAppend (R 0) _
      (ProtocolSpec.seqCompose_appendValid (fun i => hValid (Fin.succ i)))
      (h 0)
      (ih (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i))
        (fun i => rel (Fin.succ i)) (fun i => hValid (Fin.succ i)) (fun i => h (Fin.succ i)))

/-- **Binary `append`-valid perfect-completeness keystone (proven once, abstract `p₁`/`p₂`).** The
trailing protocol is either empty (`append_perfectCompleteness_empty_proof`) or `P_to_V`-leading
(`reduction_append_perfectCompleteness_msg`). The heavy `OracleSpec`-sum probability-instance
synthesis happens here, abstractly, not per-level in the `seqCompose` induction. -/
theorem binary_append_valid_pc {S₁ W₁ S₂ W₂ S₃ W₃ : Type} {k₁ k₂ : ℕ}
    {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
    [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
    [∀ j, Fintype (p₁.Challenge j)] [∀ j, Fintype (p₂.Challenge j)]
    [∀ j, Inhabited (p₁.Challenge j)] [∀ j, Inhabited (p₂.Challenge j)]
    (R₁ : Reduction oSpec S₁ W₁ S₂ W₂ p₁) (R₂ : Reduction oSpec S₂ W₂ S₃ W₃ p₂)
    {r₁ : Set (S₁ × W₁)} {r₂ : Set (S₂ × W₂)} {r₃ : Set (S₃ × W₃)}
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (hv : k₂ = 0 ∨ ∃ h : 0 < k₂, p₂.dir ⟨0, h⟩ = .P_to_V)
    (h₁ : R₁.perfectCompleteness init impl r₁ r₂)
    (h₂ : R₂.perfectCompleteness init impl r₂ r₃) :
    (R₁.append R₂).perfectCompleteness init impl r₁ r₃ := by
  rcases hv with hk₂ | ⟨hpos, hdir⟩
  · subst hk₂
    exact append_perfectCompleteness_empty_proof R₁ R₂ h₁ h₂ hInit hImplSupp
  · have hDir : (p₁ ++ₚ p₂).dir (⟨k₁, by omega⟩ : Fin (k₁ + k₂)) = .P_to_V := by
      rw [show (⟨k₁, by omega⟩ : Fin (k₁ + k₂))
          = Fin.natAdd k₁ (⟨0, hpos⟩ : Fin k₂) from by ext; simp]
      rw [Prover.append_dir_natAdd]; exact hdir
    exact reduction_append_perfectCompleteness_msg R₁ R₂ h₁ h₂ hpos hDir hdir hInit hImplSupp

set_option maxHeartbeats 1000000 in
/-- **n-ary message-seam `seqCompose` perfect completeness — fully discharged (issue #114).**
Combines the abstract fast induction (`seqCompose_pc_of_append_msg'`) with the once-proven binary
keystone (`binary_append_valid_pc`). Every component protocol is nonempty and starts with a prover
message (`hValid`) — exactly the shape of `Sumcheck.Spec.oracleReduction` (a `seqCompose` of
`fun _ => SingleRound.pSpec`). No residual, no `sorry`. -/
theorem seqCompose_perfectCompleteness_msg {m : ℕ}
    (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    [∀ i, ∀ j, Fintype ((pSpec i).Challenge j)]
    [∀ i, ∀ j, Inhabited ((pSpec i).Challenge j)]
    (R : (i : Fin m) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i))
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (hValid : ∀ i, ∃ h : 0 < n i, (pSpec i).dir ⟨0, h⟩ = .P_to_V)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (h : ∀ i, (R i).perfectCompleteness init impl (rel i.castSucc) (rel i.succ)) :
    (seqCompose Stmt Wit R).perfectCompleteness init impl (rel 0) (rel (Fin.last m)) := by
  refine seqCompose_pc_of_append_msg' Stmt Wit R rel ?_ hValid h
  intro S₁ W₁ S₂ W₂ S₃ W₃ k₁ k₂ p₁ p₂ _ _ _ _ _ _ R₁ R₂ r₁ r₂ r₃ hv h₁ h₂
  exact binary_append_valid_pc R₁ R₂ hInit hImplSupp hv h₁ h₂

set_option maxHeartbeats 1000000 in
/-- **Explicit-instance form of `seqCompose_perfectCompleteness_msg`.** Takes the per-round challenge
`Fintype`/`Inhabited` as *explicit* arguments `hFin`/`hInh` (rather than instance-implicit), which is
the robust calling convention for concrete protocols whose per-round protocol is a literal `fun _ => p`
(there the instance search would otherwise fail to match the `(fun _ => p) i` redex against an
instance stated on the reduced `p`). Used by `Sumcheck.Spec.reduction_perfectCompleteness`. -/
theorem seqCompose_pc_msg' {m : ℕ}
    (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    (R : (i : Fin m) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i))
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (hFin : ∀ i, ∀ j, Fintype ((pSpec i).Challenge j))
    (hInh : ∀ i, ∀ j, Inhabited ((pSpec i).Challenge j))
    (hValid : ∀ i, ∃ h : 0 < n i, (pSpec i).dir ⟨0, h⟩ = .P_to_V)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (h : ∀ i, (R i).perfectCompleteness init impl (rel i.castSucc) (rel i.succ)) :
    (seqCompose Stmt Wit R).perfectCompleteness init impl (rel 0) (rel (Fin.last m)) := by
  haveI : ∀ i, ∀ j, Fintype ((pSpec i).Challenge j) := hFin
  haveI : ∀ i, ∀ j, Inhabited ((pSpec i).Challenge j) := hInh
  exact seqCompose_perfectCompleteness_msg Stmt Wit R rel hValid hInit hImplSupp h

end Reduction

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKeystone
import ArkLib.OracleReduction.Composition.Sequential.Append.GuardedRoundByRound
import ArkLib.OracleReduction.Composition.Sequential.SeamDecompositionRunWithLog
import ArkLib.OracleReduction.Composition.Sequential.SeamDecompositionRunPartial
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessProof
import ArkLib.ToVCVio.OracleComp.SimSemantics.SubsingletonState

/-!
# Compatibility for canonical sequential knowledge-state composition

The classic names in this module expose projections of the canonical appended extractor and
partial transcripts. `KnowledgeStateFunction.append` delegates to the completed canonical
`appendGuarded` construction with a true first guard and the supplied pure verdict. It supports
arbitrary `extractIn` maps; no intermediate witness type is identified with its input witness.
The historical reachable-initial-state parameter remains accepted by this compatibility API.
-/

open OracleComp OracleSpec ProtocolSpec SubSpec
open scoped ENNReal NNReal

universe u v

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- **Amnesiac phase-2 re-injection prover.** Given the appended prover `P` and a *concrete* realized
seam state `rSeam : P.PrvState (last m)`, this is `Prover.snd P` re-typed so its input *statement* is
`Stmt₂` (the intermediate statement type `V₂` quantifies over) and its input *witness* is `Wit₂` — but
both are **ignored**: the prover hardcodes `rSeam`, resuming `P`'s phase-2 interaction from the realized
seam state regardless of the supplied `(stmt₂, wit₂)`.

This is the "amnesiac re-injection" recast needed to apply the inner per-round knowledge bound
`hBound₂` (which quantifies over *all* `pSpec₂`-provers restarting from `input (stmt₂, wit₂)`) to
`Prover.snd P`'s seam-resumed run: `hBound₂` applied to `sndAmnesiac P rSeam` (at *any* `stmt₂`, `wit₂`)
controls exactly `Prover.snd P`'s run from `rSeam` (`sndAmnesiac_runToRound`). -/
def sndAmnesiac
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (rSeam : P.PrvState (Fin.castLE (show m + 1 ≤ m + n + 1 by omega) (Fin.last m))) :
    Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂ where
  PrvState := (Prover.snd P).PrvState
  input := fun _ => (Prover.snd P).input ⟨rSeam, ()⟩
  sendMessage := (Prover.snd P).sendMessage
  receiveChallenge := (Prover.snd P).receiveChallenge
  output := (Prover.snd P).output

/-- `sndAmnesiac P rSeam` reproduces `Prover.snd P`'s per-round run started from the realized seam
state `rSeam`, for *any* supplied input statement/witness (which it ignores). The interaction fields
are shared with `Prover.snd P`, and the hardcoded `input` injects `rSeam`. -/
@[simp] theorem sndAmnesiac_runToRound
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (rSeam : P.PrvState (Fin.castLE (show m + 1 ≤ m + n + 1 by omega) (Fin.last m)))
    (k : Fin (n + 1)) (stmt : Stmt₂) (wit : Wit₂) :
    (sndAmnesiac (Stmt₂ := Stmt₂) (Wit₂ := Wit₂) P rSeam).runToRound k stmt wit
      = (Prover.snd P).runToRound k rSeam () :=
  rfl

end Prover

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Phase-1 projection of the composite `WitMid` carrier.** For a round index `roundIdx.val ≤ m`,
the appended extractor's combined intermediate-witness type
`Fin.append WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast _` evaluated at `roundIdx` is `WitMid₁`'s leg at the
re-indexed `⟨roundIdx, _⟩ : Fin (m+1)`. -/
theorem appendWitMid_le {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    {roundIdx : Fin (m+n+1)} (h : roundIdx.val ≤ m) :
    (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) roundIdx
      = WitMid₁ ⟨roundIdx, by omega⟩ := by
  dsimp only [Function.comp_apply]
  rw [show (Fin.cast (by omega) roundIdx : Fin (m+1+n)) = Fin.castAdd n ⟨roundIdx, by omega⟩ from by
    ext; simp]
  rw [Fin.append_left]

/-- **Phase-2 projection of the composite `WitMid` carrier.** For a round index `¬ roundIdx.val ≤ m`,
the appended extractor's combined intermediate-witness type
`Fin.append WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast _` evaluated at `roundIdx` is `WitMid₂`'s leg at the
re-indexed `⟨roundIdx - m, _⟩ : Fin (n+1)`. -/
theorem appendWitMid_gt {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    {roundIdx : Fin (m+n+1)} (h : ¬ roundIdx.val ≤ m) :
    (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) roundIdx
      = WitMid₂ ⟨roundIdx - m, by omega⟩ := by
  dsimp only [Function.comp_apply]
  rw [show (Fin.cast (by omega) roundIdx : Fin (m+1+n))
        = Fin.natAdd (m+1) ⟨roundIdx-(m+1), by omega⟩ from by ext; simp; omega]
  rw [Fin.append_right]; show Fin.tail WitMid₂ _ = _; unfold Fin.tail; congr 1
  ext; simp only [Fin.val_succ]; omega

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
private theorem fstUpTo_heq_fst {k : Fin (m + n + 1)}
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript k) (j : Fin (m + 1))
    (hj : j.val = min k.val m) (hle : j.val ≤ k.val) :
    HEq (tr.fstUpTo j hle) tr.fst := by
  apply Transcript.heq_ext hj
  intro i hi hi'
  exact (cast_heq _ _).trans (cast_heq _ _).symm

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
private theorem sndUpTo_heq_snd {k : Fin (m + n + 1)}
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript k) (j : Fin (n + 1))
    (hj : j.val = k.val - m) (hle : m + j.val ≤ k.val) :
    HEq (tr.sndUpTo j hle) tr.snd := by
  apply Transcript.heq_ext hj
  intro i hi hi'
  exact (cast_heq _ _).trans (cast_heq _ _).symm

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Phase-1 projection of the composite `extractMid`.** For a round index `idx < m` (entirely in
phase 1), the appended extractor's `extractMid` defers — heterogeneously, up to the witness/transcript
type casts — to `E₁.extractMid ⟨idx,hi⟩` on the transcript's phase-1 truncation. -/
theorem appendExtractMid_le {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (idx : Fin (m+n)) (hi : (idx:ℕ) < m) (stmt₁ : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript idx.succ)
    (h : (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) idx.succ)
    (trf : pSpec₁.Transcript (⟨idx, hi⟩ : Fin m).succ) (htrf : HEq tr.fst trf)
    (hin : WitMid₁ (⟨idx, hi⟩ : Fin m).succ) (hheq : HEq h hin) :
    HEq ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid idx stmt₁ tr h)
        (E₁.extractMid ⟨idx, hi⟩ stmt₁ trf hin) := by
  unfold Extractor.RoundByRound.append
  dsimp only
  rw [dite_eq_left hi]
  refine (cast_heq _ _).trans ?_
  apply heq_of_eq
  congr 1
  · exact eq_of_heq ((fstUpTo_heq_fst tr (⟨idx, hi⟩ : Fin m).succ
      (by simp; omega) (by simp)).trans htrf)
  · exact eq_of_heq ((cast_heq _ _).trans hheq)

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Phase-2 (interior) projection of the composite `extractMid`.** For a round index `idx > m`
(strictly inside phase 2), the appended extractor's `extractMid` defers — heterogeneously — to
`E₂.extractMid ⟨idx-m,_⟩` on the `verify`-fed intermediate statement and the transcript's phase-2 tail. -/
theorem appendExtractMid_gt {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (idx : Fin (m+n)) (hi : m < (idx:ℕ)) (stmt₁ : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript idx.succ)
    (h : (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) idx.succ)
    (trf : pSpec₁.FullTranscript) (htrf : HEq tr.fst trf)
    (trs : pSpec₂.Transcript (⟨(idx:ℕ)-m, by omega⟩ : Fin n).succ) (htrs : HEq tr.snd trs)
    (hin : WitMid₂ (⟨(idx:ℕ)-m, by omega⟩ : Fin n).succ) (hheq : HEq h hin) :
    HEq ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid idx stmt₁ tr h)
        (E₂.extractMid ⟨(idx:ℕ)-m, by omega⟩ (verify stmt₁ trf) trs hin) := by
  unfold Extractor.RoundByRound.append
  dsimp only
  rw [dite_eq_right (show ¬ (idx : ℕ) < m by omega),
    dite_eq_right (show ¬ (idx : ℕ) = m by omega)]
  refine (cast_heq _ _).trans ?_
  apply heq_of_eq
  congr 1
  · exact congrArg (verify stmt₁) (eq_of_heq ((fstUpTo_heq_fst tr (Fin.last m)
      (by simp; omega) (by simp; omega)).trans htrf))
  · exact eq_of_heq ((sndUpTo_heq_snd tr (⟨(idx : ℕ) - m, by omega⟩ : Fin n).succ
      (by simp; omega) (by simp; omega)).trans htrs)
  · exact eq_of_heq ((cast_heq _ _).trans hheq)

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Crossing projection of the composite `extractMid`.** At the seam round `idx = m`, the appended
extractor peels one phase-2 round with `E₂.extractMid 0` (landing in `Wit₂` via `E₂.eqIn`) and crosses
into phase 1 with `E₁.extractOut` on the `verify`-fed intermediate statement. -/
theorem appendExtractMid_cross {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (idx : Fin (m+n)) (hi : (idx:ℕ) = m) (hn : 0 < n) (stmt₁ : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript idx.succ)
    (h : (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) idx.succ)
    (trf : pSpec₁.FullTranscript) (htrf : HEq tr.fst trf)
    (trs : pSpec₂.Transcript (⟨0, hn⟩ : Fin n).succ) (htrs : HEq tr.snd trs)
    (hin : WitMid₂ (⟨0, hn⟩ : Fin n).succ) (hheq : HEq h hin) :
    HEq ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid idx stmt₁ tr h)
        (E₁.extractOut stmt₁ trf
          (E₂.extractIn (verify stmt₁ trf) (E₂.extractMid ⟨0, hn⟩ (verify stmt₁ trf) trs hin))) := by
  unfold Extractor.RoundByRound.append
  dsimp only
  rw [dite_eq_right (show ¬ (idx : ℕ) < m by omega), dite_eq_left hi]
  refine (cast_heq _ _).trans ?_
  have hf := eq_of_heq ((fstUpTo_heq_fst tr (Fin.last m)
    (by simp; omega) (by simp; omega)).trans htrf)
  have hs := eq_of_heq ((sndUpTo_heq_snd tr (⟨0, hn⟩ : Fin n).succ
    (by simp; omega) (by simp; omega)).trans htrs)
  have hty : (Fin.append (m := m + 1) WitMid₁ (Fin.tail WitMid₂) ∘
      Fin.cast (by omega)) idx.succ = WitMid₂ (⟨0, hn⟩ : Fin n).succ := by
    rw [appendWitMid_gt (show ¬ idx.succ.val ≤ m by simp; omega)]
    congr 1
    apply Fin.ext
    simp
    omega
  have hw : cast hty h = hin := eq_of_heq ((cast_heq hty h).trans hheq)
  simp only [hw]
  apply heq_of_eq
  congr 1
  congr 1
  · exact congrArg (verify stmt₁) hf
  · apply eq_of_heq
    refine (cast_heq _ _).trans ?_
    apply heq_of_eq
    congr 1
    · exact congrArg (verify stmt₁) hf

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Phase-2 projection of the composite `extractOut`.** For `n > 0` the appended protocol's final
round is interior to phase 2, so the appended extractor's `extractOut` defers — heterogeneously, up
to the witness type cast — to `E₂.extractOut` on the `verify`-fed intermediate statement and the
transcript's phase-2 tail. The `extractOut` analogue of `appendExtractMid_gt`. -/
theorem appendExtractOut_gt {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hn : 0 < n) (stmt₁ : Stmt₁) (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) (witOut : Wit₃)
    (h : ¬ ((Fin.last (m + n) : Fin (m + n + 1)) : ℕ) ≤ m) :
    HEq (cast (appendWitMid_gt h)
          ((Extractor.RoundByRound.append E₁ E₂ verify).extractOut stmt₁ tr witOut))
        (E₂.extractOut (verify stmt₁ (FullTranscript.fst tr)) (FullTranscript.snd tr) witOut) := by
  exact (cast_heq _ _).trans (Extractor.RoundByRound.append_extractOut_of_pos
    E₁ E₂ verify hn stmt₁ tr witOut)

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Dependent congruence for a knowledge state function's `toFun`.** Two applications of a (raw)
round-by-round knowledge `toFun` family agree (as `Prop`s) when the round indices are equal and the
transcript and intermediate-witness arguments are heterogeneously equal. The protocol-independent
glue that lets the seam-transport HEq facts collapse into the `Prop`-level equalities consumed by
`kSF₁.toFun_next` / `kSF₂.toFun_next`. -/
theorem kToFun_congr {WitMid : Fin (n+1)→Type} {Stmt : Type}
    (f : (r : Fin (n+1)) → Stmt → pSpec₂.Transcript r → WitMid r → Prop)
    {r₁ r₂ : Fin (n+1)} (hr : r₁ = r₂) (stmt : Stmt)
    {t₁ : pSpec₂.Transcript r₁} {t₂ : pSpec₂.Transcript r₂} (ht : HEq t₁ t₂)
    {w₁ : WitMid r₁} {w₂ : WitMid r₂} (hw : HEq w₁ w₂) :
    f r₁ stmt t₁ w₁ = f r₂ stmt t₂ w₂ := by
  subst hr; rw [eq_of_heq ht, eq_of_heq hw]

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **`kToFun_congr` for the first (phase-1) protocol.** Same as `kToFun_congr` over `pSpec₁`. -/
theorem kToFun_congr₁ {WitMid : Fin (m+1)→Type} {Stmt : Type}
    (f : (r : Fin (m+1)) → Stmt → pSpec₁.Transcript r → WitMid r → Prop)
    {r₁ r₂ : Fin (m+1)} (hr : r₁ = r₂) (stmt : Stmt)
    {t₁ : pSpec₁.Transcript r₁} {t₂ : pSpec₁.Transcript r₂} (ht : HEq t₁ t₂)
    {w₁ : WitMid r₁} {w₂ : WitMid r₂} (hw : HEq w₁ w₂) :
    f r₁ stmt t₁ w₁ = f r₂ stmt t₂ w₂ := by
  subst hr; rw [eq_of_heq ht, eq_of_heq hw]

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Heterogeneous congruence for an extractor's `extractMid` (phase-1 protocol).** Equal round
indices and heterogeneously-equal transcript / output-witness arguments give heterogeneously-equal
extracted intermediate witnesses.  Lets `appendExtractMid_le`'s reindexed `E₁.extractMid` be
transported to the canonical `i₁`-indexed one consumed by `kSF₁`. -/
theorem extractMid₁_heq_congr {WitMid : Fin (m+1)→Type}
    (E : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid) (stmt : Stmt₁)
    {r₁ r₂ : Fin m} (hr : r₁ = r₂)
    {t₁ : pSpec₁.Transcript r₁.succ} {t₂ : pSpec₁.Transcript r₂.succ} (ht : HEq t₁ t₂)
    {w₁ : WitMid r₁.succ} {w₂ : WitMid r₂.succ} (hw : HEq w₁ w₂) :
    HEq (E.extractMid r₁ stmt t₁ w₁) (E.extractMid r₂ stmt t₂ w₂) := by
  subst hr; rw [eq_of_heq ht, eq_of_heq hw]

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **The phase-1 transcript-truncation seam.** For a phase-1 round (`roundIdx < m`), concatenating a
phase-1 message `msg` and taking the appended-spec transcript's phase-1 truncation is heterogeneously
equal to first truncating and then concatenating the recast message. Mirrors the inline computation in
`StateFunction.append.toFun_next`. -/
theorem concat_fst_heq_phase1 {roundIdx : Fin (m + n)} (hlt : (roundIdx : ℕ) < m)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript roundIdx.castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).Type roundIdx)
    (hmsgty : (pSpec₁ ++ₚ pSpec₂).Type roundIdx = pSpec₁.Type ⟨roundIdx, hlt⟩) :
    HEq (Transcript.concat msg tr).fst
        (Transcript.concat (cast hmsgty msg)
          (by simpa [show (roundIdx : ℕ) ≤ m from le_of_lt hlt] using tr.fst :
            pSpec₁.Transcript (⟨roundIdx, hlt⟩ : Fin m).castSucc)) := by
  have hcs : (roundIdx : ℕ) ≤ m := le_of_lt hlt
  apply Function.hfunext
  · congr 1; simp only [Fin.val_succ]; omega
  · intro a a' haa'
    have hav : a.val = a'.val := by
      have := Fin.heq_ext_iff (by simp only [Fin.val_succ]; omega) |>.mp haa'
      omega
    simp only [Transcript.concat, Transcript.fst]
    obtain ⟨av, hav_lt⟩ := a
    simp only [Fin.val_succ] at hav hav_lt ⊢
    rw [show min ((roundIdx : ℕ) + 1) m = (roundIdx : ℕ) + 1 from by omega] at hav_lt
    simp only [Fin.snoc]
    by_cases hlast : av = roundIdx
    · rw [dif_neg (show ¬ av < roundIdx from by omega),
          dif_neg (show ¬ (a' : ℕ) < roundIdx from by omega)]
      -- goal `cast (cast msg) ≍ cast (cast hmsgty msg)`; route both through `msg`.
      refine HEq.trans (b := msg) (HEq.trans (cast_heq _ _) (cast_heq _ _)) ?_
      exact HEq.symm (HEq.trans (cast_heq _ _) (cast_heq hmsgty msg))
    · have hlt' : av < roundIdx := by omega
      rw [dif_pos (show (a' : ℕ) < roundIdx from by omega),
          dif_pos (show av < roundIdx from hlt')]
      refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
      have hmincard : min (roundIdx : ℕ) m = (roundIdx : ℕ) := by omega
      refine HEq.trans ?_ (dcongr_heq (f₁ := Transcript.fst tr)
        (a₁ := (⟨av, by omega⟩ : Fin (min (roundIdx : ℕ) m)))
        (a₂ := (a'.castLT (show (a' : ℕ) < roundIdx from by omega)))
        (Fin.heq_ext_iff hmincard |>.mpr (by simpa using hav))
        (fun t₁ t₂ ht => by
          have hv : (t₁ : ℕ) = (t₂ : ℕ) := Fin.val_eq_val_of_heq ht
          show pSpec₁.Type _ = pSpec₁.Type _
          congr 1; ext; simpa using hv)
        (fun _ _ => HEq.symm (cast_heq _ _ :
          (by simpa [hcs] using tr.fst : pSpec₁.Transcript ⟨roundIdx, by omega⟩)
            ≍ Transcript.fst tr)))
      unfold Transcript.fst
      refine HEq.trans ?_ (cast_heq _ _).symm
      congr 1

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Phase-1 prefix is invariant under a phase-2 concat.** For a phase-2 round (`m ≤ roundIdx`),
concatenating a phase-2 message `msg` onto the transcript leaves the phase-1 truncation `fst`
unchanged (heterogeneously). Mirrors the `hfstHeq` computation in `StateFunction.append.toFun_next`
(`Append.lean:1407–1430`). -/
theorem concat_fst_heq_phase2 {roundIdx : Fin (m + n)} (hge : m ≤ (roundIdx : ℕ))
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript roundIdx.castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).Type roundIdx) :
    HEq (Transcript.concat msg tr).fst tr.fst := by
  have hcard : min ((roundIdx : Fin (m + n)).succ : ℕ) m
      = min ((roundIdx : Fin (m + n)).castSucc : ℕ) m := by
    simp only [Fin.val_succ, Fin.val_castSucc]; omega
  apply Function.hfunext
  · congr 1
  · intro a a' haa'
    have hav : (a : ℕ) = (a' : ℕ) := by
      have := Fin.heq_ext_iff hcard |>.mp haa'; omega
    simp only [Transcript.concat, Transcript.fst]
    obtain ⟨av, hav_lt⟩ := a
    simp only [Fin.val_succ] at hav hav_lt ⊢
    rw [show min ((roundIdx : ℕ) + 1) m = m from by omega] at hav_lt
    refine HEq.trans (cast_heq _ _) ?_
    refine HEq.trans ?_ (cast_heq _ _).symm
    simp only [Fin.snoc]
    rw [dif_pos (show av < roundIdx from by omega)]
    refine HEq.trans (cast_heq _ _) ?_
    congr 1
    ext; simp only [Fin.val_castLT]; omega

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
private theorem concat_heq_same {k l : Fin n} (hkl : k = l)
    {tr : pSpec₂.Transcript k.castSucc} {tr' : pSpec₂.Transcript l.castSucc}
    (htr : HEq tr tr') {msg : pSpec₂.Type k} {msg' : pSpec₂.Type l}
    (hm : HEq msg msg') : HEq (tr.concat msg) (tr'.concat msg') := by
  subst hkl
  rw [eq_of_heq htr, eq_of_heq hm]

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **The phase-2 transcript-tail seam.** For a phase-2 round (`m ≤ roundIdx`), concatenating a
phase-2 message `msg` and taking the appended-spec transcript's phase-2 tail is heterogeneously
equal to first taking the tail and then concatenating the recast message. The `.snd` analogue of
`concat_fst_heq_phase1`; mirrors the inline computation in `StateFunction.append.toFun_next`
(`Append.lean:1544–1583`). -/
theorem concat_snd_heq_phase2 {roundIdx : Fin (m + n)} (hge : m ≤ (roundIdx : ℕ))
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript roundIdx.castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).Type roundIdx)
    (hmsgty₂ : (pSpec₁ ++ₚ pSpec₂).Type roundIdx = pSpec₂.Type ⟨(roundIdx : ℕ) - m, by omega⟩) :
    HEq (Transcript.concat msg tr).snd
        (Transcript.concat (cast hmsgty₂ msg)
          (by simpa using tr.snd :
            pSpec₂.Transcript (⟨(roundIdx : ℕ) - m, by omega⟩ : Fin n).castSucc)) := by
  revert hge tr msg hmsgty₂
  refine Fin.addCases (fun j => ?_) (fun j => ?_) roundIdx
  · intro hge
    have hj := j.isLt
    simp only [Fin.val_castAdd] at hge
    omega
  · intro _ tr msg hmsgty₂
    have hc := Transcript.sndUpTo_concat_natAdd j tr msg
    refine (sndUpTo_heq_snd (tr.concat msg) j.succ
      (by simp; omega) (by simp; omega)).symm.trans ((heq_of_eq hc).trans ?_)
    exact concat_heq_same (by apply Fin.ext; simp)
      (sndUpTo_heq_snd tr j.castSucc (by simp) (by simp))
      ((cast_heq _ _).trans (cast_heq _ _).symm)

/-- **Membership lifts to positive probability for a deterministic verifier.** If the first verifier
is `V₁ = pure ∘ verify` with a reachable initial state (`∃ s, s ∈ support init`), and the
intermediate statement/witness pair `(verify stmt₁ trFst, witOut)` lies in `rel₂`, then the
`Pr[(·, witOut) ∈ rel₂ | …] > 0` hypothesis of `kSF₁.toFun_full` is met: the deterministic run
outputs `verify stmt₁ trFst`, which witnesses the positive probability. The positive-probability dual
of `StateFunction.verify_not_mem_lang_of_toFun_full_neg`; shared by the crossing case of
`toFun_next` and by `toFun_full`. -/
theorem run_pos_of_mem_rel
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {rel₂ : Set (Stmt₂ × Wit₂)}
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init)
    (stmt₁ : Stmt₁) (trFst : pSpec₁.FullTranscript) (witOut : Wit₂)
    (hMem : (verify stmt₁ trFst, witOut) ∈ rel₂) :
    probEvent (fun stmtOut => (stmtOut, witOut) ∈ rel₂) (OptionT.mk do (simulateQ impl (V₁.run stmt₁ trFst)).run' (← init)) > 0 := by
  rw [gt_iff_lt, OracleComp.OptionT.prEvent_mk_pos_iff]
  obtain ⟨s, hs⟩ := hInit
  refine ⟨verify stmt₁ trFst, ?_, hMem⟩
  simp only [OptionT.run_mk, support_bind, Set.mem_iUnion, exists_prop]
  refine ⟨s, hs, ?_⟩
  have hrun : (V₁.run stmt₁ trFst) = (pure (verify stmt₁ trFst) : OptionT (OracleComp oSpec) Stmt₂) := by
    subst hVerify; rfl
  rw [hrun]
  change some (verify stmt₁ trFst) ∈ MonadAttach.support
    (StateT.run' (simulateQ impl (pure (some (verify stmt₁ trFst)) :
      OracleComp oSpec (Option Stmt₂))) s)
  rw [simulateQ_pure]
  change some (verify stmt₁ trFst) ∈ MonadAttach.support
    (Prod.fst <$> (pure (some (verify stmt₁ trFst)) : StateT σ ProbComp _).run s)
  rw [StateT.run_pure]
  simp [LawfulApplicative.map_pure]

/-- The guarded presentation of a verifier with an explicitly supplied pure verdict. -/
private def pureFirstGuardedForm
    (V : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V = ⟨fun stmt tr => pure (verify stmt tr)⟩) : V.GuardedForm where
  check := fun _ _ => true
  out := verify
  verify_eq := by
    intro stmt tr
    subst hVerify
    rfl

/-- The sequential composition of two **knowledge** state functions, witness-threaded analogue of
`Verifier.StateFunction.append`. Built against the proven composite extractor
`Extractor.RoundByRound.append E₁ E₂ verify`. -/
def KnowledgeStateFunction.append {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init) :
    (V₁.append V₂).KnowledgeStateFunction init impl rel₁ rel₃
      (Extractor.RoundByRound.append E₁ E₂ verify) :=
  KnowledgeStateFunction.appendGuarded
    (pureFirstGuardedForm V₁ verify hVerify) kSF₁ kSF₂

/-- **Phase-1 projection of the composite knowledge state function.** On a round index lying in the
first protocol (`roundIdx.val ≤ m`), `KnowledgeStateFunction.append.toFun` is definitionally `kSF₁`
on the transcript's phase-1 truncation and the phase-1 leg of the combined intermediate witness — the
`dif_pos` branch.  The witness-threaded analogue of `StateFunction.append_toFun_le`. -/
theorem KnowledgeStateFunction.append_toFun_le {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init)
    {roundIdx : Fin (m + n + 1)} (h : roundIdx.val ≤ m) (stmt₁ : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript roundIdx)
    (witMid : (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) roundIdx) :
    (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun roundIdx stmt₁ tr witMid
      = kSF₁.toFun ⟨roundIdx, by omega⟩ stmt₁ (by simpa [h] using tr.fst)
          (cast (appendWitMid_le h) witMid) := by
  apply propext
  simp only [KnowledgeStateFunction.append, KnowledgeStateFunction.appendGuarded,
    KnowledgeStateFunction.appendGuardedToFun, pureFirstGuardedForm, h,
    ProtocolSpec.Transcript.fstUpTo, ProtocolSpec.Transcript.fst]
  apply Iff.of_eq
  apply kToFun_congr₁ _ rfl _
  · exact (fstUpTo_heq_fst tr ⟨roundIdx, by omega⟩ (by simp; omega) (by simp)).trans
      (cast_heq _ _).symm
  · exact (cast_heq _ _).trans (cast_heq _ _).symm

/-- **Phase-2 projection of the composite knowledge state function.** On a round index lying in the
second protocol (`¬ roundIdx.val ≤ m`), `KnowledgeStateFunction.append.toFun` is definitionally `kSF₂`
on the `verify`-fed intermediate statement, the transcript's phase-2 tail, and the phase-2 leg of the
combined intermediate witness — the `dif_neg` branch.  The witness-threaded analogue of
`StateFunction.append_toFun_gt`. -/
theorem KnowledgeStateFunction.append_toFun_gt {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init)
    {roundIdx : Fin (m + n + 1)} (h : ¬ roundIdx.val ≤ m) (stmt₁ : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript roundIdx)
    (witMid : (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) roundIdx) :
    (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun roundIdx stmt₁ tr witMid
      = kSF₂.toFun ⟨roundIdx - m, by omega⟩
          (verify stmt₁ (_root_.cast
            (show pSpec₁.Transcript ⟨min roundIdx.val m, by omega⟩ = pSpec₁.FullTranscript from
            congrArg pSpec₁.Transcript
              (show (⟨min roundIdx.val m, by omega⟩ : Fin (m + 1)) = Fin.last m from
                Fin.ext (show min roundIdx.val m = m by omega))) tr.fst))
          (by simpa [h] using tr.snd) (cast (appendWitMid_gt h) witMid) := by
  apply propext
  simp only [KnowledgeStateFunction.append, KnowledgeStateFunction.appendGuarded,
    KnowledgeStateFunction.appendGuardedToFun, pureFirstGuardedForm, h, dite_false, true_and]
  have hstmt : verify stmt₁ (tr.fstUpTo (Fin.last m) (by simp; omega)) =
      verify stmt₁ (_root_.cast
        (show pSpec₁.Transcript ⟨min roundIdx.val m, by omega⟩ = pSpec₁.FullTranscript from
        congrArg pSpec₁.Transcript
              (show (⟨min roundIdx.val m, by omega⟩ : Fin (m + 1)) = Fin.last m from
                Fin.ext (show min roundIdx.val m = m by omega))) tr.fst) := by
    apply congrArg (verify stmt₁)
    exact eq_of_heq ((fstUpTo_heq_fst tr (Fin.last m) (by simp; omega)
      (by simp; omega)).trans (cast_heq _ _).symm)
  rw [hstmt]
  apply Iff.of_eq
  apply kToFun_congr _ rfl _
  · exact sndUpTo_heq_snd tr ⟨roundIdx - m, by omega⟩ rfl (by simp; omega)
  · exact (cast_heq _ _).trans (cast_heq _ _).symm

end Verifier

#print axioms Verifier.KnowledgeStateFunction.append
#print axioms Verifier.appendExtractMid_cross
#print axioms Verifier.concat_snd_heq_phase2
#print axioms Verifier.KnowledgeStateFunction.append_toFun_le
#print axioms Verifier.KnowledgeStateFunction.append_toFun_gt

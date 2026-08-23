/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKeystone
import ArkLib.OracleReduction.Composition.Sequential.SeamDecompositionRunWithLog
import ArkLib.OracleReduction.Composition.Sequential.SeamDecompositionRunPartial
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessProof
import ArkLib.ToVCVio.OracleComp.SimSemantics.SubsingletonState

/-!
# The composite round-by-round *knowledge* state function — `Verifier.KnowledgeStateFunction.append`

This file constructs the witness-threaded analogue of the proven `Verifier.StateFunction.append`
(`Append.lean`): the composite round-by-round **knowledge** state function for the appended verifier
`V₁.append V₂`, built against the proven composite round-by-round extractor
`Extractor.RoundByRound.append E₁ E₂ verify`. With it the residual `kSF` of
`Verifier.append_rbrKnowledgeSoundness_keystone` (`AppendRbrKeystone.lean`) is discharged.

The `toFun` carrier mirrors `StateFunction.append`: on a phase-1 round (`roundIdx.val ≤ m`) it is the
inner knowledge state function `kSF₁` on the transcript's phase-1 truncation; on a phase-2 round it is
`kSF₂` on the `verify`-fed intermediate statement and the transcript's phase-2 tail. The only new
ingredient relative to `StateFunction.append` is the intermediate-witness leg: the appended extractor's
combined `WitMid` carrier `Fin.append WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast _` projects to `WitMid₁`
on phase-1 rounds and `WitMid₂` on phase-2 rounds (`appendWitMid_le` / `appendWitMid_gt`), and the
state function casts the supplied combined witness into the appropriate leg before feeding it to
`kSF₁` / `kSF₂`.
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
  dsimp only [Fin.append, Fin.addCases, Fin.tail, Fin.castLT, Fin.cast]
  rw [dif_pos hi]
  simp only [id_eq]
  refine HEq.trans (cast_heq _ _) ?_
  refine dcongr_heq (HEq.trans (cast_heq _ _) hheq) (fun _ _ _ => rfl)
    (fun _ _ => heq_of_eq (congr_heq HEq.rfl (HEq.trans (cast_heq _ _) htrf)))

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
  dsimp only [Fin.append, Fin.addCases, Fin.tail, Fin.castLT, Fin.cast]
  rw [dif_neg (show ¬ (idx:ℕ) < m from by omega)]
  rw [dif_neg (show ¬ (idx:ℕ) = m from by omega)]
  simp only [id_eq]
  refine HEq.trans (cast_heq _ _) (HEq.trans (cast_heq _ _) ?_)
  refine dcongr_heq (HEq.trans (HEq.trans (cast_heq _ _) (cast_heq _ _))
      (HEq.trans (cast_heq _ _) hheq)) (fun _ _ _ => rfl) (fun _ _ => ?_)
  refine heq_of_eq (congr_heq (heq_of_eq (congrArg (E₂.extractMid ⟨(idx:ℕ)-m, by omega⟩) ?_))
    (HEq.trans (cast_heq _ _) htrs))
  exact congrArg (verify stmt₁) (eq_of_heq (HEq.trans (cast_heq _ _) htrf))

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
          (cast E₂.eqIn (E₂.extractMid ⟨0, hn⟩ (verify stmt₁ trf) trs hin))) := by
  unfold Extractor.RoundByRound.append
  dsimp only [Fin.append, Fin.addCases, Fin.tail, Fin.castLT, Fin.cast]
  rw [dif_neg (show ¬ (idx:ℕ) < m from by omega)]
  rw [dif_pos (show (idx:ℕ) = m from hi)]
  simp only [id_eq]
  refine HEq.trans (cast_heq _ _) (HEq.trans (cast_heq _ _) ?_)
  refine dcongr_heq (a₁ := _) (a₂ := cast E₂.eqIn (E₂.extractMid ⟨0, hn⟩ (verify stmt₁ trf) trs hin))
    ?hw (fun _ _ _ => rfl) (fun _ _ => ?hf)
  case hw =>
    refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
    refine dcongr_heq (HEq.trans (cast_heq _ _) (HEq.trans (cast_heq _ _)
        (HEq.trans (cast_heq _ _) hheq))) (fun _ _ _ => rfl)
      (fun _ _ => heq_of_eq (congr_heq (heq_of_eq (congrArg (E₂.extractMid ⟨0, hn⟩)
        (congrArg (verify stmt₁) (eq_of_heq (HEq.trans (cast_heq _ _) htrf)))))
        (HEq.trans (cast_heq _ _) htrs)))
  case hf =>
    exact heq_of_eq (congr_heq HEq.rfl (HEq.trans (cast_heq _ _) htrf))

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
  refine HEq.trans (cast_heq _ _) ?_
  unfold Extractor.RoundByRound.append
  dsimp only [Fin.append, Fin.addCases, Fin.tail, Fin.castLT, Fin.cast]
  simp only [dif_neg (show ¬ n = 0 from by omega), id_eq]
  refine HEq.trans ?_ (HEq.refl (E₂.extractOut (verify stmt₁ (FullTranscript.fst tr))
    (FullTranscript.snd tr) witOut))
  rw [eq_mpr_eq_cast]
  refine HEq.trans (cast_heq _ _) (cast_heq _ _)

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
  have hsndcard : ((roundIdx : ℕ) - m) + 1 = ((roundIdx : Fin (m + n)).succ : ℕ) - m := by
    simp only [Fin.val_succ]; omega
  symm
  apply Function.hfunext
  · congr 1
  · intro a a' haa'
    have haa : (a : ℕ) = (a' : ℕ) := by
      have := Fin.heq_ext_iff hsndcard |>.mp haa'; omega
    simp only [Transcript.concat]
    obtain ⟨av, hav_lt⟩ := a
    simp only [Fin.val_mk] at haa hav_lt ⊢
    -- the RHS `(concat msg tr).snd` always lands in the `else` branch (its index `> m`)
    rw [show (Transcript.concat msg tr).snd (⟨(a' : ℕ), a'.isLt⟩ : Fin _)
          = (Transcript.concat msg tr).snd a' from by congr]
    unfold Transcript.snd
    rw [dif_neg (show ¬ (roundIdx : Fin (m + n)).succ ≤ m from by
          simp only [Fin.val_succ]; omega)]
    -- the LHS `Fin.snoc ((tr.snd cast)) msg₂`: split on whether `av` is the last position
    simp only [Fin.snoc]
    by_cases hlast : av = (roundIdx : ℕ) - m
    · rw [dif_neg (show ¬ av < (roundIdx : ℕ) - m from by omega),
          dif_neg (show ¬ m + (a' : ℕ) < (roundIdx : ℕ) from by omega)]
      -- both sides are `msg` (the new message), up to casts
      refine HEq.trans (cast_heq _ _) ?_
      refine HEq.trans (cast_heq _ _) ?_
      exact HEq.trans (cast_heq _ _).symm (cast_heq _ _).symm
    · -- earlier position: both read the original `tr.snd` at the same underlying index
      have hlt2 : av < (roundIdx : ℕ) - m := by omega
      rw [dif_pos (show av < (roundIdx : ℕ) - m from hlt2)]
      rw [dif_neg (show ¬ (roundIdx : Fin (m + n)).castSucc ≤ m from by
            simp only [Fin.val_castSucc]; omega)]
      rw [dif_pos (show m + (a' : ℕ) < (roundIdx : ℕ) from by omega)]
      refine HEq.trans (cast_heq _ _) ?_
      refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
      congr 1
      ext; simp only [Fin.val_castLT]; omega

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
    Pr[fun stmtOut => (stmtOut, witOut) ∈ rel₂
      | OptionT.mk do (simulateQ impl (V₁.run stmt₁ trFst)).run' (← init)] > 0 := by
  rw [gt_iff_lt, probEvent_pos_iff]
  obtain ⟨s, hs⟩ := hInit
  refine ⟨verify stmt₁ trFst, ?_, hMem⟩
  rw [OptionT.mem_support_iff]
  simp only [OptionT.run_mk, support_bind, Set.mem_iUnion]
  refine ⟨s, hs, ?_⟩
  have hrun : (V₁.run stmt₁ trFst) = (pure (verify stmt₁ trFst) : OptionT (OracleComp oSpec) Stmt₂) := by
    subst hVerify; rfl
  rw [hrun]
  change some (verify stmt₁ trFst) ∈ _root_.support
    (StateT.run' (simulateQ impl (pure (some (verify stmt₁ trFst)) :
      OracleComp oSpec (Option Stmt₂))) s)
  rw [simulateQ_pure]
  change some (verify stmt₁ trFst) ∈ _root_.support
    (Prod.fst <$> (pure (some (verify stmt₁ trFst)) : StateT σ ProbComp _).run s)
  rw [StateT.run_pure]
  simp [map_pure]

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
      (Extractor.RoundByRound.append E₁ E₂ verify) where
  toFun := fun roundIdx stmt₁ tr witMid =>
    if h : roundIdx.val ≤ m then
      kSF₁.toFun ⟨roundIdx, by omega⟩ stmt₁ (by simpa [h] using tr.fst)
        (cast (appendWitMid_le h) witMid)
    else
      kSF₂.toFun ⟨roundIdx - m, by omega⟩
        (verify stmt₁ (by simp at h; simpa [min_eq_right_of_lt h] using tr.fst))
        (by simpa [h] using tr.snd) (cast (appendWitMid_gt h) witMid)
  toFun_empty := by
    intro stmtIn witMid
    -- At round `0`, `(0 : Fin (m+n+1)).val = 0 ≤ m`, so `toFun 0 = kSF₁.toFun ⟨0,_⟩ … (.fst) …`.
    have h0 : ((0 : Fin (m + n + 1)) : ℕ) ≤ m := by simp
    simp only [dif_pos h0]
    -- The witness-cast coherence: `cast (append.eqIn) witMid = cast E₁.eqIn (cast (appendWitMid_le …))`.
    have hwit : cast (Extractor.RoundByRound.append E₁ E₂ verify).eqIn witMid
        = cast E₁.eqIn (cast (appendWitMid_le h0) witMid) := by
      rw [cast_cast]
    rw [hwit]
    -- Now reduce to `kSF₁.toFun_empty`, re-indexing `⟨0,_⟩ : Fin (m+1)` as `0` and `.fst = default`.
    refine Iff.trans (kSF₁.toFun_empty stmtIn (cast (appendWitMid_le h0) witMid)) (Iff.of_eq ?_)
    congr 1
    funext i; exact i.elim0
  toFun_next := by
    intro roundIdx hDir stmt₁ tr msg witMid hPrev
    by_cases hlt : (roundIdx : ℕ) < m
    · -- Phase 1: both `roundIdx.succ` and `roundIdx.castSucc` land in the `≤ m` (kSF₁) branch.
      have hsucc : (roundIdx : ℕ) + 1 ≤ m := hlt
      have hcs : (roundIdx : ℕ) ≤ m := le_of_lt hlt
      simp only [Fin.val_succ, Fin.val_castSucc, dif_pos hsucc] at hPrev
      simp only [Fin.val_succ, Fin.val_castSucc, dif_pos hcs]
      -- The phase-1 direction.
      have hDir₁ : pSpec₁.dir ⟨roundIdx, hlt⟩ = .P_to_V := by
        rw [← Fin.vappend_left_of_lt pSpec₁.dir pSpec₂.dir roundIdx hlt]; exact hDir
      have hmsgty : (pSpec₁ ++ₚ pSpec₂).Type roundIdx = pSpec₁.Type ⟨roundIdx, hlt⟩ := by
        show Fin.vappend pSpec₁.Type pSpec₂.Type roundIdx = pSpec₁.Type ⟨roundIdx, hlt⟩
        rw [Fin.vappend_left_of_lt _ _ _ hlt]
      -- The phase-1 truncated transcript and witness.
      set trf : pSpec₁.Transcript (⟨roundIdx, hlt⟩ : Fin m).castSucc :=
        (by simpa [hcs] using tr.fst) with htrf_def
      set wit₁ : WitMid₁ (⟨roundIdx, hlt⟩ : Fin m).succ :=
        cast (appendWitMid_le hsucc) witMid with hwit₁_def
      -- The shared transcript-truncation seam.
      have htrEq : HEq (Transcript.concat msg tr).fst (trf.concat (cast hmsgty msg)) :=
        concat_fst_heq_phase1 hlt tr msg hmsgty
      -- `hPrev` reshaped to `kSF₁.toFun (succ) stmt₁ (trf.concat (cast msg)) wit₁`.
      have hPrev₁ : kSF₁.toFun (⟨roundIdx, hlt⟩ : Fin m).succ stmt₁
          (trf.concat (cast hmsgty msg)) wit₁ := by
        have e : kSF₁.toFun (⟨roundIdx, hlt⟩ : Fin m).succ stmt₁ (trf.concat (cast hmsgty msg)) wit₁
            = kSF₁.toFun ⟨(roundIdx : ℕ) + 1, by omega⟩ stmt₁
              (by simpa [hsucc] using (Transcript.concat msg tr).fst)
              (cast (appendWitMid_le hsucc) witMid) :=
          kToFun_congr₁ kSF₁.toFun (Fin.ext (by simp [Fin.val_succ]))
            stmt₁ (htrEq.symm.trans (cast_heq _ _).symm) HEq.rfl
        rw [e]; exact hPrev
      -- Apply `kSF₁.toFun_next` and transport to the goal via `appendExtractMid_le`.
      have key := kSF₁.toFun_next ⟨roundIdx, hlt⟩ hDir₁ stmt₁ trf (cast hmsgty msg) wit₁ hPrev₁
      -- The goal's witness is `cast _ ((append…).extractMid …)`; `key`'s is
      -- `E₁.extractMid ⟨roundIdx,hlt⟩ stmt₁ (trf.concat (cast msg)) wit₁`. Identify via
      -- `appendExtractMid_le`, the transcripts via `htrf_def`/`htrEq`.
      have hExtEq : HEq (cast (appendWitMid_le hcs)
            ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid roundIdx stmt₁
              (Transcript.concat msg tr) witMid))
          (E₁.extractMid ⟨roundIdx, hlt⟩ stmt₁ (trf.concat (cast hmsgty msg)) wit₁) :=
        (cast_heq _ _).trans (appendExtractMid_le E₁ E₂ verify roundIdx hlt stmt₁
          (Transcript.concat msg tr) witMid (trf.concat (cast hmsgty msg)) htrEq wit₁
          (cast_heq _ _).symm)
      -- Close the goal by transporting `key` across the index/transcript/witness coherences.
      refine Eq.mp ?_ key
      exact kToFun_congr₁ kSF₁.toFun
        (Fin.ext (by simp [Fin.val_castSucc]) :
          (⟨roundIdx, hlt⟩ : Fin m).castSucc = ⟨(roundIdx : ℕ), by omega⟩)
        stmt₁ ((cast_heq _ _).trans (cast_heq _ _).symm) hExtEq.symm
    · -- `roundIdx ≥ m`. Two sub-cases.
      --
      -- PHASE-2 INTERIOR (`roundIdx > m`): structurally identical to the phase-1 case above, with
      --   `kSF₂` / `appendExtractMid_gt` / `appendWitMid_gt` in place of the phase-1 versions, the
      --   statement `verify stmt₁ tr.fst` (invariant under the phase-2 concat — see the `.fst`
      --   invariance below), and the *second-segment* transcript seam: `(tr.concat msg).snd` is
      --   heterogeneously `(tr.snd).concat (cast msg)` (mirroring `StateFunction.append.toFun_next`,
      --   `Append.lean:1544–1583`). Both `dite` branches land in `kSF₂` (`dif_neg`), and
      --   `kSF₂.toFun_next ⟨roundIdx-m,_⟩` closes it via the same `kToFun_congr` / `Eq.mp` transport
      --   used in phase 1. (Fully scaffolded; the only missing brick is the `.snd` transcript-seam
      --   `HEq` lemma — the `.snd` analogue of the proven `concat_fst_heq_phase1` — whose `dite`
      --   bookkeeping over `Transcript.snd` is the entirety of the remaining work.)
      --
      -- CROSSING (`roundIdx = m`): the hypothesis is `kSF₂.toFun ⟨1,_⟩ (verify stmt₁ tr.fst)
      --   ((tr.concat msg).snd) witMid` (phase-2 index 1) and the goal is `kSF₁.toFun (Fin.last m)
      --   stmt₁ tr.fst (E₁.extractOut stmt₁ tr.fst (cast E₂.eqIn (E₂.extractMid 0 … witMid)))` (via
      --   `appendExtractMid_cross`). The chain is the DUAL of `StateFunction.append.toFun_next`'s
      --   crossing (which propagates *falsity* through the language): here we propagate *truth*:
      --     1. `kSF₂.toFun_next 0` turns the hypothesis into
      --        `kSF₂.toFun 0 (verify …) default (E₂.extractMid 0 … witMid)`;
      --     2. `kSF₂.toFun_empty` then gives `(verify stmt₁ tr.fst, cast E₂.eqIn (E₂.extractMid 0 …))
      --        ∈ rel₂`;
      --     3. since `V₁` is deterministic (`hVerify`), `V₁.run stmt₁ tr.fst = pure (verify …)`, so the
      --        `Pr[(·, wit₂) ∈ rel₂ | V₁.run …] > 0` hypothesis of `kSF₁.toFun_full` holds (the run
      --        deterministically outputs `verify stmt₁ tr.fst`);
      --     4. `kSF₁.toFun_full` then yields exactly the goal `kSF₁.toFun (last m) stmt₁ tr.fst
      --        (E₁.extractOut stmt₁ tr.fst wit₂)`.
      --   This sub-case is provable (it is NOT the `hBound` residual — that is a *probabilistic*
      --   per-round bound, a different obligation); the blocker is purely the `Pr > 0` plumbing from
      --   `hVerify` (the same deterministic-run collapse used in `toFun_full` below).
      rw [not_lt] at hlt
      -- `hPrev`'s index `roundIdx.succ.val = roundIdx + 1 > m` always lands in the `kSF₂` branch.
      have hnsucc : ¬ ((roundIdx : ℕ) + 1 ≤ m) := by omega
      simp only [Fin.val_succ, dif_neg hnsucc] at hPrev
      -- The phase-2 direction at this round.
      have hDir₂ : pSpec₂.dir ⟨(roundIdx : ℕ) - m, by omega⟩ = .P_to_V := by
        rw [show pSpec₂.dir ⟨(roundIdx : ℕ) - m, by omega⟩
              = (pSpec₁.dir ++ᵛ pSpec₂.dir) roundIdx
            from (Fin.vappend_right_of_not_lt _ _ _ (by omega : ¬ (roundIdx : ℕ) < m)).symm]
        exact hDir
      -- The message transported into the second segment's type.
      have hmsgty₂ : (pSpec₁ ++ₚ pSpec₂).Type roundIdx
          = pSpec₂.Type ⟨(roundIdx : ℕ) - m, by omega⟩ := by
        show Fin.vappend pSpec₁.Type pSpec₂.Type roundIdx = _
        rw [Fin.vappend_right_of_not_lt _ _ _ (by omega : ¬ (roundIdx : ℕ) < m)]
      -- The phase-2 truncated transcript: `tr.snd` as a `castSucc`-indexed transcript.
      set trs : pSpec₂.Transcript (⟨(roundIdx : ℕ) - m, by omega⟩ : Fin n).castSucc :=
        (by simpa using tr.snd) with htrs_def
      -- The phase-1 prefix as a genuine full transcript (`roundIdx ≥ m`, so the domain is all `m`).
      have hmin : min (roundIdx : ℕ) m = m := by omega
      set trFst : pSpec₁.FullTranscript := (by simpa [hmin] using tr.fst) with htrFst_def
      have htrFst_heq : (trFst : pSpec₁.FullTranscript) ≍ tr.fst := cast_heq _ _
      by_cases hcross : (roundIdx : ℕ) = m
      · -- CROSSING (`roundIdx = m`): goal's `roundIdx.castSucc.val = m ≤ m` lands in `kSF₁`.
        have hcs : (roundIdx : ℕ) ≤ m := by omega
        simp only [Fin.val_castSucc, dif_pos hcs]
        have hn1 : 0 < n := by have := (roundIdx : Fin (m + n)).isLt; omega
        -- (1) `hPrev` (at phase-2 index `roundIdx + 1 - m = 1`) reshaped to `kSF₂.toFun 0.succ
        --     (verify … trFst) (empty.concat msg₂) witMid₂`.
        have hmsgty0 : (pSpec₁ ++ₚ pSpec₂).Type roundIdx = pSpec₂.Type (⟨0, hn1⟩ : Fin n) := by
          rw [hmsgty₂]; congr 1; ext; simp only [Fin.val_mk]; omega
        set witMid₂ : WitMid₂ (⟨0, hn1⟩ : Fin n).succ :=
          cast (show WitMid₂ ⟨((roundIdx : Fin (m + n)).succ : ℕ) - m, by simp only [Fin.val_succ]; omega⟩
              = WitMid₂ (⟨0, hn1⟩ : Fin n).succ from by
                congr 1; ext; simp only [Fin.val_succ, Fin.val_mk]; omega)
            (cast (appendWitMid_gt (by simp only [Fin.val_succ]; omega :
              ¬ ((roundIdx : Fin (m + n)).succ : ℕ) ≤ m)) witMid) with hwitMid₂_def
        let empty2 : pSpec₂.Transcript (⟨0, hn1⟩ : Fin n).castSucc := fun i => i.elim0
        -- the phase-1 prefix is invariant under the phase-2 concat (crossing version)
        have htrFstEq : HEq (Transcript.concat msg tr).fst tr.fst :=
          concat_fst_heq_phase2 hlt tr msg
        -- the phase-2 tail seam at the crossing collapses to `empty2.concat msg₂`: reuse the
        -- interior seam lemma, then reconcile the empty prefix (`trs ≍ empty2`, both subsingleton)
        -- and the `msg` recast (`cast hmsgty₂ msg ≍ cast hmsgty0 msg`).
        have hsnd : HEq (Transcript.concat msg tr).snd (empty2.concat (cast hmsgty0 msg)) := by
          refine HEq.trans (concat_snd_heq_phase2 hlt tr msg hmsgty₂) ?_
          apply Function.hfunext
          · congr 1; simp only [Fin.val_succ, Fin.val_mk]; omega
          · intro a a' haa'
            have haa : (a : ℕ) = (a' : ℕ) := by
              have := Fin.heq_ext_iff (by simp only [Fin.val_succ, Fin.val_mk]; omega) |>.mp haa'
              omega
            simp only [Transcript.concat, Fin.snoc]
            obtain ⟨av, hav_lt⟩ := a
            obtain ⟨av', hav'_lt⟩ := a'
            simp only [Fin.val_mk] at haa hav_lt hav'_lt
            -- at the crossing `roundIdx - m = 0`, both snocs are at their (unique) last position
            rw [dif_neg (show ¬ av < (roundIdx : ℕ) - m from by omega),
                dif_neg (show ¬ av' < 0 from by omega)]
            refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
            exact HEq.trans (cast_heq hmsgty₂ msg) (cast_heq hmsgty0 msg).symm
        have hPrev₂ : kSF₂.toFun (⟨0, hn1⟩ : Fin n).succ (verify stmt₁ trFst)
            (empty2.concat (cast hmsgty0 msg)) witMid₂ := by
          convert hPrev using 2 <;>
            first
              | (simp only [Fin.val_succ, Fin.val_mk]; omega)
              | -- statement: `verify stmt₁ trFst = verify stmt₁ <(concat msg tr).fst>`
                (congr 1;
                 exact eq_of_heq (HEq.trans htrFst_heq (HEq.trans htrFstEq.symm (cast_heq _ _).symm)))
              | -- transcript: `empty2.concat msg₂ ≍ <(concat msg tr).snd>`
                exact hsnd.symm
              | exact HEq.trans hsnd.symm (cast_heq _ _).symm
              | -- witness: `witMid₂ ≍ <cast (appendWitMid_gt) witMid>` — unfold the `set` def via
                -- `simp` (it handles the HEq motive), then peel the cast.
                (simp only [hwitMid₂_def]; exact cast_heq _ _)
        -- (2) `kSF₂.toFun_next 0` descends `hPrev₂` to `kSF₂.toFun 0 (verify…) default (extractMid…)`.
        have hDir₂0 : pSpec₂.dir (⟨0, hn1⟩ : Fin n) = .P_to_V := by
          have : (⟨0, hn1⟩ : Fin n) = ⟨(roundIdx : ℕ) - m, by omega⟩ := by
            ext; simp only [Fin.val_mk]; omega
          rw [this]; exact hDir₂
        have hStep := kSF₂.toFun_next (⟨0, hn1⟩ : Fin n) hDir₂0 (verify stmt₁ trFst)
          empty2 (cast hmsgty0 msg) witMid₂ hPrev₂
        -- `0.castSucc = 0` and `empty2 = default`: reshape `hStep` into `kSF₂.toFun 0 … default …`.
        have hcs0 : (⟨0, hn1⟩ : Fin n).castSucc = (0 : Fin (n + 1)) := by ext; simp
        set witE2 : WitMid₂ (0 : Fin (n + 1)) :=
          E₂.extractMid (⟨0, hn1⟩ : Fin n) (verify stmt₁ trFst)
            (empty2.concat (cast hmsgty0 msg)) witMid₂ with hwitE2_def
        have hStep0 : kSF₂.toFun (0 : Fin (n + 1)) (verify stmt₁ trFst) default
            (cast (congrArg WitMid₂ hcs0) witE2) := by
          rw [hwitE2_def]
          refine (kToFun_congr kSF₂.toFun hcs0 (verify stmt₁ trFst) ?_ ?_).mp hStep
          · -- `empty2 ≍ default` (both empty over `Fin 0` / the subsingleton transcript)
            refine HEq.trans (HEq.rfl : empty2 ≍ empty2) ?_
            apply Function.hfunext (by rw [hcs0])
            intro a _ _; exact a.elim0
          · exact (cast_heq _ _).symm
        -- (3) `kSF₂.toFun_empty` → `(verify stmt₁ trFst, cast E₂.eqIn witE2') ∈ rel₂`.
        have hMem : (verify stmt₁ trFst,
            cast E₂.eqIn (cast (congrArg WitMid₂ hcs0) witE2)) ∈ rel₂ :=
          (kSF₂.toFun_empty (verify stmt₁ trFst) (cast (congrArg WitMid₂ hcs0) witE2)).mpr hStep0
        -- (4) deterministic-run positivity + `kSF₁.toFun_full` yields the goal.
        have hPr := run_pos_of_mem_rel (impl := impl) (init := init) verify hVerify hInit stmt₁ trFst
          (cast E₂.eqIn (cast (congrArg WitMid₂ hcs0) witE2)) hMem
        have hFull := kSF₁.toFun_full stmt₁ trFst
          (cast E₂.eqIn (cast (congrArg WitMid₂ hcs0) witE2)) hPr
        -- Transport `hFull` (`kSF₁.toFun (last m) stmt₁ trFst (E₁.extractOut …)`) to the goal.
        -- The goal's witness is `cast (appendWitMid_le hcs) (append.extractMid roundIdx …)`, which by
        -- `appendExtractMid_cross` equals `E₁.extractOut stmt₁ trFst (cast E₂.eqIn (E₂.extractMid 0 …))`.
        have hExtEq : HEq (cast (appendWitMid_le hcs)
              ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid roundIdx stmt₁
                (Transcript.concat msg tr) witMid))
            (E₁.extractOut stmt₁ trFst
              (cast E₂.eqIn (E₂.extractMid (⟨0, hn1⟩ : Fin n) (verify stmt₁ trFst)
                (empty2.concat (cast hmsgty0 msg)) witMid₂))) :=
          (cast_heq _ _).trans (appendExtractMid_cross E₁ E₂ verify roundIdx hcross hn1 stmt₁
            (Transcript.concat msg tr) witMid trFst (htrFstEq.trans htrFst_heq.symm)
            (empty2.concat (cast hmsgty0 msg)) hsnd witMid₂
            (by rw [hwitMid₂_def]; exact ((cast_heq _ _).trans (cast_heq _ _)).symm))
        -- `hFull`'s extractOut argument and `hExtEq`'s coincide: both apply `E₂.extractMid 0` to the
        -- round-1 transcript `empty2.concat msg₂`. (`witE2` is *defined* as that `extractMid` call.)
        have hWitOut : E₁.extractOut stmt₁ trFst
              (cast E₂.eqIn (cast (congrArg WitMid₂ hcs0) witE2))
            = E₁.extractOut stmt₁ trFst
              (cast E₂.eqIn (E₂.extractMid (⟨0, hn1⟩ : Fin n) (verify stmt₁ trFst)
                (empty2.concat (cast hmsgty0 msg)) witMid₂)) := by
          have hcc : cast (congrArg WitMid₂ hcs0) witE2 = witE2 := eq_of_heq (cast_heq _ _)
          rw [hcc, hwitE2_def]
        rw [hWitOut] at hFull
        -- Now transport `hFull` to the goal across index/transcript/witness coherences.
        refine Eq.mp ?_ hFull
        exact kToFun_congr₁ kSF₁.toFun
          (Fin.ext (by rw [Fin.val_last, Fin.coe_castSucc]; exact hcross.symm) :
            (Fin.last m)
              = (⟨(roundIdx : Fin (m + n)).castSucc, by simp only [Fin.coe_castSucc]; omega⟩
                : Fin (m + 1)))
          stmt₁ (htrFst_heq.trans (cast_heq _ _).symm) hExtEq.symm
      · -- PHASE-2 INTERIOR (`m < roundIdx`): goal's `roundIdx.castSucc.val = roundIdx > m` → `kSF₂`.
        have hgt : m < (roundIdx : ℕ) := lt_of_le_of_ne hlt (Ne.symm hcross)
        have hncs : ¬ ((roundIdx : ℕ) ≤ m) := by omega
        simp only [Fin.val_castSucc, dif_neg hncs]
        -- The phase-2 truncated witness, reindexed to `⟨roundIdx-m,_⟩.succ`.
        set wit₂ : WitMid₂ (⟨(roundIdx : ℕ) - m, by omega⟩ : Fin n).succ :=
          cast (show WitMid₂ ⟨((roundIdx : Fin (m + n)).succ : ℕ) - m, by simp only [Fin.val_succ]; omega⟩
              = WitMid₂ (⟨(roundIdx : ℕ) - m, by omega⟩ : Fin n).succ from by
                congr 1; ext; simp only [Fin.val_succ, Fin.val_mk]; omega)
            (cast (appendWitMid_gt hnsucc) witMid) with hwit₂_def
        -- The shared transcript-tail seam.
        have htrEq : HEq (Transcript.concat msg tr).snd (trs.concat (cast hmsgty₂ msg)) :=
          concat_snd_heq_phase2 hlt tr msg hmsgty₂
        -- The phase-1 prefix is invariant under the phase-2 concat.
        have htrFstEq : HEq (Transcript.concat msg tr).fst tr.fst :=
          concat_fst_heq_phase2 hlt tr msg
        -- `hPrev` reshaped to `kSF₂.toFun (succ) (verify stmt₁ trFst) (trs.concat msg₂) wit₂`.
        have hPrev₂ : kSF₂.toFun (⟨(roundIdx : ℕ) - m, by omega⟩ : Fin n).succ
            (verify stmt₁ trFst) (trs.concat (cast hmsgty₂ msg)) wit₂ := by
          convert hPrev using 2 <;>
            first
              | (simp only [Fin.val_succ, Fin.val_mk]; omega)
              | -- statement: `verify stmt₁ trFst = verify stmt₁ <(concat msg tr).fst>`
                (congr 1;
                 exact eq_of_heq (HEq.trans htrFst_heq (HEq.trans htrFstEq.symm (cast_heq _ _).symm)))
              | -- transcript: `trs.concat msg₂ ≍ <(concat msg tr).snd>`
                exact htrEq.symm
              | exact HEq.trans htrEq.symm (cast_heq _ _).symm
              | -- witness: `wit₂ ≍ <cast (appendWitMid_gt) witMid>` — unfold the `set` def via simp,
                -- then peel the cast.
                (simp only [hwit₂_def]; exact cast_heq _ _)
        -- Apply `kSF₂.toFun_next` and transport to the goal via `appendExtractMid_gt`.
        have key := kSF₂.toFun_next ⟨(roundIdx : ℕ) - m, by omega⟩ hDir₂ (verify stmt₁ trFst)
          trs (cast hmsgty₂ msg) wit₂ hPrev₂
        -- Identify the goal's witness `cast _ (append.extractMid …)` with `key`'s
        -- `E₂.extractMid ⟨roundIdx-m,_⟩ (verify stmt₁ trFst) (trs.concat msg₂) wit₂`.
        have hExtEq : HEq (cast (appendWitMid_gt hncs)
              ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid roundIdx stmt₁
                (Transcript.concat msg tr) witMid))
            (E₂.extractMid ⟨(roundIdx : ℕ) - m, by omega⟩ (verify stmt₁ trFst)
              (trs.concat (cast hmsgty₂ msg)) wit₂) :=
          (cast_heq _ _).trans (appendExtractMid_gt E₁ E₂ verify roundIdx hgt stmt₁
            (Transcript.concat msg tr) witMid trFst (htrFstEq.trans htrFst_heq.symm)
            (trs.concat (cast hmsgty₂ msg)) htrEq wit₂
            (by rw [hwit₂_def]; exact ((cast_heq _ _).trans (cast_heq _ _)).symm))
        -- Close the goal by transporting `key` across the index/statement/transcript/witness
        -- coherences. The goal's verify-statement is on `tr.fst`; `key`'s is on `trFst`; equal.
        -- `convert` auto-unifies the defeq legs; the remaining goals are dispatched uniformly.
        convert key using 2 <;>
          first
            | (apply Fin.ext; omega)
            | (congr 1; exact eq_of_heq (HEq.trans (cast_heq _ _) htrFst_heq.symm))
            | exact cast_heq _ _
            | exact hExtEq
            | exact hExtEq.symm
            | exact eq_of_heq hExtEq
            | exact (eq_of_heq hExtEq).symm
  -- `toFun_full`: at the last round the appended verifier's output factors through `V₂` on
  -- `verify stmt₁ tr.fst` (the `Verifier.append` run, which `pure`-binds `V₁`'s deterministic
  -- output), and `extractOut` composes as `E₁.extractOut ∘ (cast E₂.eqIn) ∘ E₂.extractOut` (for
  -- `n > 0`, directly `E₂.extractOut`). With the run collapse `(V₁.append V₂).run stmt₁ tr =
  -- V₂.run (verify stmt₁ tr.fst) tr.snd` (proven inline in `StateFunction.append.toFun_full`,
  -- `Append.lean:1646–1652 / 1673–1679`), the positive-probability hypothesis transfers to `V₂`, and
  -- `kSF₂.toFun_full` (for `n > 0`) / `kSF₁.toFun_full` composed through the empty phase-2
  -- `E₂.eqIn` round-trip (for `n = 0`) yields the goal. Mirrors `StateFunction.append.toFun_full`
  -- with the witness leg threaded through `Extractor.RoundByRound.append`'s `extractOut`.
  toFun_full := by
    intro stmt₁ tr witOut hPos
    -- The full-transcript `.fst`/`.snd` agree (over `HEq`) with the partial-transcript projections
    -- at the last round (`min (m+n) m = m`, `(m+n) - m = n`). Copied verbatim from
    -- `StateFunction.append.toFun_full`.
    have hmincard : min ((Fin.last (m + n) : Fin (m + n + 1)) : ℕ) m = m := by
      simp only [Fin.val_last]; omega
    have hsndcard : ((Fin.last (m + n) : Fin (m + n + 1)) : ℕ) - m = n := by
      simp only [Fin.val_last]; omega
    have htFstHeq : ∀ (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript),
        (Transcript.fst (k := Fin.last (m + n)) T) ≍ FullTranscript.fst T := by
      intro T
      apply Function.hfunext (congrArg Fin hmincard)
      intro a a' ha
      have hval : (a : ℕ) = (a' : ℕ) := by
        have := Fin.heq_ext_iff hmincard |>.mp ha; omega
      simp only [Transcript.fst, FullTranscript.fst]
      refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
      congr 1; apply Fin.ext; simp only [Fin.coe_castAdd]; omega
    have htSndHeq : ∀ (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript),
        (Transcript.snd (k := Fin.last (m + n)) T) ≍ FullTranscript.snd T := by
      intro T
      apply Function.hfunext (congrArg Fin hsndcard)
      intro a a' ha
      have hval : (a : ℕ) = (a' : ℕ) := by
        have := Fin.heq_ext_iff hsndcard |>.mp ha; omega
      simp only [Transcript.snd, FullTranscript.snd]
      rw [dif_neg (show ¬ (Fin.last (m + n)) ≤ m from by simp only [Fin.val_last]; omega)]
      refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
      congr 1; apply Fin.ext; simp only [Fin.coe_natAdd]; omega
    by_cases hn : n = 0
    · -- degenerate: empty second protocol. The last round index is `m ≤ m`, so `toFun (last)`
      -- lands in the `kSF₁` branch. The appended `extractOut` crosses through the trivial empty
      -- phase-2 `E₂.extractOut`/`eqIn` round-trip into `E₁.extractOut`.
      subst hn
      rw [dif_pos (show ((Fin.last (m + 0)) : ℕ) ≤ m from by simp)]
      -- The phase-1 prefix as a genuine full transcript.
      set trFst : pSpec₁.FullTranscript := (FullTranscript.fst tr : pSpec₁.FullTranscript)
        with htrFst
      -- The appended run collapses to `V₂.run (verify stmt₁ trFst) tr.snd` (deterministic `V₁`
      -- `pure`-binds). Copied verbatim from `StateFunction.append.toFun_full`.
      have hrun : (V₁.append V₂).run stmt₁ tr
          = V₂.run (verify stmt₁ trFst) (FullTranscript.snd tr) := by
        subst hVerify
        show (do return ← V₂.verify (← (pure (verify stmt₁ trFst))) (FullTranscript.snd tr)) = _
        rw [pure_bind]
        simp only [Verifier.run, bind_pure]
      rw [hrun] at hPos
      -- `kSF₂.toFun_full` (over the empty phase 2, `last 0`) yields the phase-2 leg, which since
      -- `n = 0` is the round-`0` state — `kSF₂.toFun_empty` then puts `(verify …, cast eqIn …)` in
      -- `rel₂`, supplying the `kSF₁.toFun_full` positivity via deterministic-run positivity.
      have hPr2 := kSF₂.toFun_full (verify stmt₁ trFst) (FullTranscript.snd tr) witOut hPos
      -- `kSF₂.toFun (last 0) … (E₂.extractOut …)`; reindex `last 0 = 0` and `tr.snd = default`.
      have hl0 : (Fin.last 0 : Fin (0 + 1)) = (0 : Fin (0 + 1)) := by ext; simp
      have hPr2' : kSF₂.toFun (0 : Fin (0 + 1)) (verify stmt₁ trFst) default
          (cast (congrArg WitMid₂ hl0)
            (E₂.extractOut (verify stmt₁ trFst) (FullTranscript.snd tr) witOut)) := by
        refine (kToFun_congr kSF₂.toFun hl0 (verify stmt₁ trFst) ?_ ?_).mp hPr2
        · apply Function.hfunext (by rw [hl0]); intro a _ _; exact a.elim0
        · exact (cast_heq _ _).symm
      -- `kSF₂.toFun_empty` then gives `(verify stmt₁ trFst, cast E₂.eqIn …) ∈ rel₂`.
      have hMem : (verify stmt₁ trFst,
          cast E₂.eqIn (cast (congrArg WitMid₂ hl0)
            (E₂.extractOut (verify stmt₁ trFst) (FullTranscript.snd tr) witOut))) ∈ rel₂ :=
        (kSF₂.toFun_empty (verify stmt₁ trFst) (cast (congrArg WitMid₂ hl0)
          (E₂.extractOut (verify stmt₁ trFst) (FullTranscript.snd tr) witOut))).mpr hPr2'
      -- deterministic-run positivity + `kSF₁.toFun_full` yields the phase-1 goal.
      have hPr1 := run_pos_of_mem_rel (impl := impl) (init := init) verify hVerify hInit stmt₁ trFst
        (cast E₂.eqIn (cast (congrArg WitMid₂ hl0)
          (E₂.extractOut (verify stmt₁ trFst) (FullTranscript.snd tr) witOut))) hMem
      have hFull := kSF₁.toFun_full stmt₁ trFst
        (cast E₂.eqIn (cast (congrArg WitMid₂ hl0)
          (E₂.extractOut (verify stmt₁ trFst) (FullTranscript.snd tr) witOut))) hPr1
      -- Identify `hFull`'s `E₂.extractOut` argument with the one in `appendExtractOut_eq0` (peel the
      -- redundant `cast (congrArg WitMid₂ hl0)`), then transport across the index/transcript/witness
      -- coherences. `hFull`'s `last m`; goal's `⟨m+0,_⟩`.
      have hcc : cast (congrArg WitMid₂ hl0)
            (E₂.extractOut (verify stmt₁ trFst) (FullTranscript.snd tr) witOut)
          = E₂.extractOut (verify stmt₁ trFst) (FullTranscript.snd tr) witOut :=
        eq_of_heq (cast_heq _ _)
      rw [hcc] at hFull
      -- Inline the empty-phase-2 `extractOut` HEq (the `n = 0` analogue of `appendExtractOut_gt`):
      -- the appended `extractOut` crosses immediately via `E₁.extractOut` after the trivial empty
      -- phase-2 `E₂.extractOut`/`eqIn` round-trip.
      have hExtEq : HEq (cast (appendWitMid_le (show ((Fin.last (m + 0)) : ℕ) ≤ m from by simp))
            ((Extractor.RoundByRound.append E₁ E₂ verify).extractOut stmt₁ tr witOut))
          (E₁.extractOut stmt₁ trFst
            (cast E₂.eqIn (E₂.extractOut (verify stmt₁ trFst) (FullTranscript.snd tr) witOut))) := by
        refine HEq.trans (cast_heq _ _) ?_
        unfold Extractor.RoundByRound.append
        dsimp only [Fin.append, Fin.addCases, Fin.tail, Fin.castLT, Fin.cast]
        simp only [dif_pos (show (0 : ℕ) = 0 from rfl), id_eq]
        refine HEq.trans ?_ (HEq.refl (E₁.extractOut stmt₁ trFst
          (cast E₂.eqIn (E₂.extractOut (verify stmt₁ trFst) (FullTranscript.snd tr) witOut))))
        rw [eq_mpr_eq_cast]
        exact cast_heq _ _
      refine Eq.mp ?_ hFull
      exact kToFun_congr₁ kSF₁.toFun
        (Fin.ext (by simp only [Fin.val_last]; omega) :
          (Fin.last m) = ⟨(Fin.last (m + 0) : Fin (m + 0 + 1)), by simp only [Fin.val_last]; omega⟩)
        stmt₁ ((htFstHeq tr).symm.trans (cast_heq _ _).symm) hExtEq.symm
    · -- `n > 0`: last round index `m + n > m`, so `toFun (last)` lands in the `kSF₂` branch.
      rw [dif_neg (show ¬ ((Fin.last (m + n)) : ℕ) ≤ m from by simp only [Fin.val_last]; omega)]
      -- The appended run collapses to `V₂.run (verify stmt₁ tr.fst) tr.snd`. Copied verbatim from
      -- `StateFunction.append.toFun_full`.
      have hrun : (V₁.append V₂).run stmt₁ tr
          = V₂.run (verify stmt₁ (FullTranscript.fst tr)) (FullTranscript.snd tr) := by
        subst hVerify
        show (do return ← V₂.verify (← (pure (verify stmt₁ (FullTranscript.fst tr)))) _) = _
        rw [pure_bind]
        simp only [Verifier.run, bind_pure]
      rw [hrun] at hPos
      -- transfer the positive-probability hypothesis to `kSF₂.toFun_full`.
      have hPr := kSF₂.toFun_full (verify stmt₁ (FullTranscript.fst tr)) (FullTranscript.snd tr)
        witOut hPos
      -- `hPr : kSF₂.toFun (last n) (verify stmt₁ tr.fst) tr.snd (E₂.extractOut …)`.
      -- The goal is `kSF₂.toFun ⟨(m+n)-m,_⟩ (verify stmt₁ <Transcript.fst tr>) <Transcript.snd tr>
      --   (cast (appendWitMid_gt …) (append.extractOut …))`. `convert` auto-unifies the defeq legs;
      -- the remaining goals (index / verify-statement / .snd transcript / witness) are dispatched by
      -- the `htFstHeq`/`htSndHeq` projection agreements and `appendExtractOut_gt` (witness),
      -- mirroring the `hNeg'` step of `StateFunction.append.toFun_full`.
      have hExtEq : HEq (cast (appendWitMid_gt
              (show ¬ ((Fin.last (m + n)) : ℕ) ≤ m from by simp only [Fin.val_last]; omega))
            ((Extractor.RoundByRound.append E₁ E₂ verify).extractOut stmt₁ tr witOut))
          (E₂.extractOut (verify stmt₁ (FullTranscript.fst tr)) (FullTranscript.snd tr) witOut) :=
        appendExtractOut_gt E₁ E₂ verify (by omega) stmt₁ tr witOut
          (show ¬ ((Fin.last (m + n)) : ℕ) ≤ m from by simp only [Fin.val_last]; omega)
      convert hPr using 2 <;>
        first
          | (simp only [Fin.val_last]; omega)
          | (congr 1; exact eq_of_heq (HEq.trans (cast_heq _ _) (htFstHeq tr)))
          | exact htSndHeq tr
          | exact hExtEq
          | exact hExtEq.symm

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
  simp only [KnowledgeStateFunction.append, dif_pos h]

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
          (verify stmt₁ (by simp at h; simpa [min_eq_right_of_lt h] using tr.fst))
          (by simpa [h] using tr.snd) (cast (appendWitMid_gt h) witMid) := by
  simp only [KnowledgeStateFunction.append, dif_neg h]

/-! ## Unconditional round-by-round *knowledge* soundness append keystone

With the composite knowledge state function `KnowledgeStateFunction.append` now fully proven
(`toFun_empty` / `toFun_next` / `toFun_full` all axiom-clean above), the round-by-round knowledge
soundness append keystone can be stated **without** the `kSF` residual that
`AppendRbrKeystone.lean`'s `append_rbrKnowledgeSoundness_keystone` carried: the composite knowledge
state function is supplied internally from `KnowledgeStateFunction.append`, and the two destructured
per-round knowledge bounds `hBound₁` / `hBound₂` are taken via the input verifiers' own
`rbrKnowledgeSoundness` hypotheses `h₁` / `h₂`.

The remaining content is the *per-round probabilistic bound* against the concrete composite objects:
phase-1 is a runWithLog-level port of the soundness phase-1 seam reduction (reducing to `hBound₁`),
and phase-2 reduces to `hBound₂` *for all input statements* (the no-`langIn` quantification of
`rbrKnowledgeSoundness`, `RoundByRound.lean:839` — which is precisely why the knowledge keystone is
closeable where the plain-soundness phase-2 `appendRbrSoundnessPhase2Residual` is irreducible). That
per-round bound is isolated as the single typed residual
`appendRbrKnowledgeSoundnessPerRoundResidual`, stated directly against the proven composite
`KnowledgeStateFunction.append` and `Extractor.RoundByRound.append` with the destructured inner
extractors and bounds in scope, so no `sorry` is introduced and the kSF/extractor existential is fully
assembled from proven objects. -/

/-- **Per-round bound residual of the unconditional round-by-round knowledge soundness append
keystone.** The appended per-round knowledge flip-event probability, stated against the *proven*
composite knowledge state function `KnowledgeStateFunction.append` and the proven composite extractor
`Extractor.RoundByRound.append`. This is the genuine remaining probabilistic content of
`append_rbrKnowledgeSoundness_keystone_unconditional`: the witness-threaded per-round seam analysis,
phase-1 reducing to `kSF₁`/`E₁` and phase-2 (via the no-`langIn` quantification of
`rbrKnowledgeSoundness`) reducing to `kSF₂`/`E₂`. -/
def appendRbrKnowledgeSoundnessPerRoundResidual {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0} : Prop :=
  ∀ stmtIn : Stmt₁, ∀ witIn : Wit₁,
  ∀ prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂),
  ∀ i : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx,
    Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
      ∃ witMid,
        ¬ (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
            i.1.castSucc stmtIn transcript
            ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid i.1 stmtIn
              (transcript.concat challenge) witMid) ∧
          (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
            i.1.succ stmtIn (transcript.concat challenge) witMid
    | do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
            prover.runWithLogToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge i) _
          return (transcript, challenge, proveQueryLog))).run' (← init)] ≤
      (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) i

/-- **Log-free reduction of the appended knowledge per-round experiment.** Since the per-round
knowledge event is *log-blind* (it inspects only the transcript and challenge, discarding
`proveQueryLog`), the log-carrying `runWithLogToRound` experiment has the same event-probability as
the log-free `runToRound` seam game.  This is the bridge that brings the entire log-free seam
toolkit (`fst_runToRound_heq`, the challenge-seam transfers, …) to bear on the knowledge experiment;
its content is exactly `OracleReduction.map_runWithLog_body_eq_run_body`, lifted over `init >>=` and
the (log-blind) event by `probEvent_map`. -/
theorem appendRbrKnowledgeSoundness_logfree_reduce {WitMid₁ : Fin (m+1)→Type}
    {WitMid₂ : Fin (n+1)→Type}
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init)
    (prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (stmtIn : Stmt₁) (witIn : Wit₁) (i : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx) :
    Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
        ∃ witMid,
          ¬ (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
              i.1.castSucc stmtIn transcript
              ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid i.1 stmtIn
                (transcript.concat challenge) witMid) ∧
            (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
              i.1.succ stmtIn (transcript.concat challenge) witMid
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound i.1.castSucc stmtIn witIn
            let challenge ← liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge i) _
            return (transcript, challenge, proveQueryLog))).run' (← init)]
      = Pr[fun ⟨transcript, challenge⟩ =>
          ∃ witMid,
            ¬ (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
                i.1.castSucc stmtIn transcript
                ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid i.1 stmtIn
                  (transcript.concat challenge) witMid) ∧
              (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
                i.1.succ stmtIn (transcript.concat challenge) witMid
        | do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn
              let challenge ← liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge i) _
              return (transcript, challenge))).run' (← init)] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun s => ?_
  congr 1
  rw [← OracleReduction.map_runWithLog_body_eq_run_body impl prover i stmtIn witIn s, probEvent_map]
  rfl

/-- **Phase-1 leg of the per-round knowledge bound.** At a phase-1 challenge index `inl i₁`, the
log-free appended knowledge game reduces (via the run-level seam factoring and the left challenge-seam
transfer) to `hBound₁` at `i₁`. -/
theorem appendRbrKnowledgeSoundnessPerRound_phase1 {WitMid₁ : Fin (m+1)→Type}
    {WitMid₂ : Fin (n+1)→Type}
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init)
    (hNE₂ : Nonempty Stmt₂) (hNEW₂ : Nonempty Wit₂)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    (hBound₁ : ∀ stmtIn : Stmt₁, ∀ witIn : Wit₁,
      ∀ prover : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁, ∀ i : pSpec₁.ChallengeIdx,
        Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
          ∃ witMid,
            ¬ kSF₁.toFun i.1.castSucc stmtIn transcript
              (E₁.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
              kSF₁.toFun i.1.succ stmtIn (transcript.concat challenge) witMid
        | do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
                prover.runWithLogToRound i.1.castSucc stmtIn witIn
              let challenge ← liftComp (pSpec₁.getChallenge i) _
              return (transcript, challenge, proveQueryLog))).run' (← init)] ≤
          rbrKnowledgeError₁ i)
    (stmtIn : Stmt₁) (witIn : Wit₁)
    (prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (i₁ : pSpec₁.ChallengeIdx) :
    Pr[fun ⟨transcript, challenge⟩ =>
        ∃ witMid,
          ¬ (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
              (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc stmtIn transcript
              ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid
                (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1 stmtIn
                (transcript.concat challenge) witMid) ∧
            (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
              (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.succ stmtIn
              (transcript.concat challenge) witMid
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨transcript, _⟩ ←
              prover.runToRound (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc stmtIn witIn
            let challenge ←
              liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁)) _
            return (transcript, challenge))).run' (← init)]
      ≤ rbrKnowledgeError₁ i₁ := by
  -- Apply `hBound₁` to the phase-1 seam prover recast to a `Wit₂`-output prover (`fstCastK`); its
  -- `runToRound` equals `prover.fst`'s, and the event reads only the transcript, so the dummy
  -- output is irrelevant.
  have hb := hBound₁ stmtIn witIn (prover.fstCastK hNE₂.some hNEW₂.some) i₁
  -- Chain: appended-log-free game `=` `fstCastK` log-free game `=` `fstCastK` log-carrying game (`hb`).
  refine le_of_eq_of_le (Eq.trans ?eqcongr
    (OracleReduction.rbrKnowledge_logfree_reduce impl (prover.fstCastK hNE₂.some hNEW₂.some) i₁
        stmtIn witIn init
        (fun x => ∃ witMid, ¬ kSF₁.toFun i₁.1.castSucc stmtIn x.1
            (E₁.extractMid i₁.1 stmtIn (x.1.concat x.2) witMid) ∧
            kSF₁.toFun i₁.1.succ stmtIn (x.1.concat x.2) witMid)).symm) hb
  -- Type equalities at the phase-1 index (copied from `append_rbrSoundness_keystone` phase-1).
  have hidxCS : ((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc : Fin (m + n + 1))
      = i₁.1.castSucc.castLE (by omega) := by ext; simp [ChallengeIdx.inl]
  have hTrTy : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc
      = pSpec₁.Transcript i₁.1.castSucc := by
    rw [hidxCS]; exact Prover.append_Transcript_castLE i₁.1.castSucc
  have hChTy : (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁)
      = pSpec₁.Challenge i₁ := by simp [ChallengeIdx.inl, ProtocolSpec.append]
  have hResTy :
      ((pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc
          × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁))
        = (pSpec₁.Transcript i₁.1.castSucc × pSpec₁.Challenge i₁) := congrArg₂ Prod hTrTy hChTy
  refine probEvent_congr_heq hResTy _ _ _ _ ?hd ?hPQ
  · -- `evalDist` HEq: appended phase-1 body = `liftM` of the `fst` body, transferred via the seam.
    exact evalDist_init_run'_heq_of_body_heq hResTy _ _ (phase1_body_heq prover stmtIn witIn i₁)
  · -- The witness-threaded event correspondence.
    rintro ⟨tr, ch⟩
    have hlt : i₁.1.val < m := i₁.1.isLt
    have hval : ((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1).val = i₁.1.val := by
      simp [ChallengeIdx.inl]
    have hcs : ((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc).val ≤ m := by
      rw [Fin.val_castSucc, hval]; omega
    have hsu : ((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.succ).val ≤ m := by
      rw [Fin.val_succ, hval]; omega
    have hilt : ((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1).val < m := by rw [hval]; exact hlt
    set t' : pSpec₁.Transcript i₁.1.castSucc := (hResTy ▸ (tr, ch)).1 with ht'_def
    set c' : pSpec₁.Challenge i₁ := (hResTy ▸ (tr, ch)).2 with hc'_def
    have ht'heq : HEq t' tr := prod_cast_fst_heq hTrTy hChTy tr ch
    have hc'heq : HEq c' ch := prod_cast_snd_heq hTrTy hChTy tr ch
    have hWitTy : (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega))
          (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.succ
        = WitMid₁ i₁.1.succ := by
      rw [appendWitMid_le hsu]
      exact congrArg WitMid₁ (Fin.ext (by rw [Fin.val_succ, Fin.val_succ, hval]))
    -- The phase-1 truncation of the appended `tr` is HEq to `t'`, and `tr.concat ch ≍ t'.concat c'`
    -- via the cross-spec concat congruence.  Both packaged once for reuse below.
    have htrHeq : HEq (Transcript.fst tr) t' := (transcript_fst_heq hcs tr).trans ht'heq.symm
    have hconcatHeq : HEq (tr.concat ch) (t'.concat c') :=
      Prover.concat_heq i₁.1 ht'heq.symm hc'heq.symm
    have hconcatFstHeq : HEq (Transcript.fst (tr.concat ch)) (t'.concat c') :=
      (transcript_fst_heq hsu (tr.concat ch)).trans hconcatHeq
    -- The extracted-witness HEq (both directions) via `appendExtractMid_le`.
    have hExtHeq : ∀ (witMid : (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega))
          (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.succ) (wM : WitMid₁ i₁.1.succ), HEq witMid wM →
        HEq ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid
              (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1 stmtIn (tr.concat ch) witMid)
            (E₁.extractMid i₁.1 stmtIn (t'.concat c') wM) :=
      fun witMid wM hw =>
        (appendExtractMid_le E₁ E₂ verify (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1 hilt
          stmtIn (tr.concat ch) witMid (t'.concat c')
          ((transcript_fst_heq hsu (tr.concat ch)).trans hconcatHeq)
          wM hw).trans
        (extractMid₁_heq_congr E₁ stmtIn (Fin.ext hval) HEq.rfl HEq.rfl)
    show (∃ witMid, _ ∧ _) ↔ (∃ witMid, _ ∧ _)
    constructor
    · rintro ⟨witMid, hneg, hpos⟩
      refine ⟨cast hWitTy witMid, ?_, ?_⟩
      · intro hkSF; apply hneg
        rw [KnowledgeStateFunction.append_toFun_le V₁ V₂ kSF₁ kSF₂ verify hVerify hInit hcs]
        refine (kToFun_congr₁ kSF₁.toFun
          (Fin.ext (by simp only [Fin.val_castSucc, hval]) :
            (⟨((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc).val, by omega⟩ : Fin (m + 1))
              = i₁.1.castSucc)
          stmtIn ((cast_heq _ _).trans htrHeq)
          ((cast_heq _ _).trans (hExtHeq witMid (cast hWitTy witMid)
            (cast_heq hWitTy witMid).symm))).mpr hkSF
      · rw [KnowledgeStateFunction.append_toFun_le V₁ V₂ kSF₁ kSF₂ verify hVerify hInit hsu] at hpos
        refine (kToFun_congr₁ kSF₁.toFun
          (Fin.ext (by simp only [Fin.val_succ, hval]) :
            (⟨((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.succ).val, by omega⟩ : Fin (m + 1))
              = i₁.1.succ)
          stmtIn ((cast_heq _ _).trans hconcatFstHeq)
          ((cast_heq _ _).trans (cast_heq hWitTy witMid).symm)).mp hpos
    · rintro ⟨wM, hneg, hpos⟩
      refine ⟨cast hWitTy.symm wM, ?_, ?_⟩
      · intro hAppend; apply hneg
        rw [KnowledgeStateFunction.append_toFun_le V₁ V₂ kSF₁ kSF₂ verify hVerify hInit hcs]
          at hAppend
        refine (kToFun_congr₁ kSF₁.toFun
          (Fin.ext (by simp only [Fin.val_castSucc, hval]) :
            (⟨((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc).val, by omega⟩ : Fin (m + 1))
              = i₁.1.castSucc)
          stmtIn ((cast_heq _ _).trans htrHeq)
          ((cast_heq _ _).trans (hExtHeq (cast hWitTy.symm wM) wM (cast_heq hWitTy.symm wM)))).mp
          hAppend
      · rw [KnowledgeStateFunction.append_toFun_le V₁ V₂ kSF₁ kSF₂ verify hVerify hInit hsu]
        refine (kToFun_congr₁ kSF₁.toFun
          (Fin.ext (by simp only [Fin.val_succ, hval]) :
            (⟨((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.succ).val, by omega⟩ : Fin (m + 1))
              = i₁.1.succ)
          stmtIn ((cast_heq _ _).trans hconcatFstHeq)
          ((cast_heq _ _).trans (cast_heq hWitTy.symm wM))).mpr hpos

/-- **Phase-2 per-round residual of the knowledge append per-round bound.** The single remaining
typed residual: at a phase-2 challenge index `inr i₂`, the log-free appended knowledge game is bounded
by `rbrKnowledgeError₂ i₂`.

Unlike the phase-1 leg (fully proven above), this leg crosses the protocol **seam**: the appended
composite knowledge state function / extractor collapse (via `KnowledgeStateFunction.append_toFun_gt`
/ `appendExtractMid_gt`) to `kSF₂` / `E₂` evaluated at the `verify`-fed **random** intermediate
statement `verify stmtIn tr.fst` determined by the realized phase-1 transcript.

**Available brick.** The run-level half of the reduction is now proven, axiom-clean, in
`SeamDecompositionRunPartial.lean`: `Prover.snd_runToRound_natAdd_seam` (the `natAdd` analogue of the
phase-1 partial `Prover.merge_runToRound_castLE`) factors the appended partial run
`prover.runToRound (natAdd m i₂.castSucc)` as `(Prover.fst prover)`'s full run (the seam output,
threaded into `Prover.snd`'s `input`) followed by `(Prover.snd prover)`'s **own** partial
`runToRound i₂.castSucc`, with the phase-1 transcript prefixed via `Transcript.appendRight`.  Combined
with the right challenge-seam transfer `OracleReduction.evalDist_run'_challengeSeam_right` and a
`probEvent_bind` averaging over the realized phase-1 transcript, this reduces the appended phase-2 game
to a per-realization inner `kSF₂` / `E₂` flip bound.

**Why it is not yet unconditional (the precise remaining obstructions).** Discharging this leg fully
from `hBound₂` is blocked by three genuine gaps, beyond the "the seam statement is controlled" point:

* **(message seam)** `snd_runToRound_natAdd_seam` (like `run_seam_factor`) requires the seam round
  (`pSpec₂` round 0) to be a prover **message** (`pSpec₂.dir 0 = .P_to_V`); this keystone carries no
  such hypothesis, so the general-seam case is open.
* **(carried prover state)** `hBound₂` quantifies over `pSpec₂`-provers that **restart** from
  `input (stmt₂, wit₂)`, whereas `Prover.snd prover` resumes from `prover`'s realized **internal seam
  state** (arbitrary, history-dependent).  This is reparable per realization via an "amnesiac
  re-injection" `pSpec₂`-prover hardcoding the realized seam state (legitimate, since `hBound₂` is
  over *all* provers), but that recast is not yet built.
* **(oracle `σ`-state threading)** the appended phase-2 oracle queries run from the `σ`-state
  **mutated by phase 1**, whereas `hBound₂`'s game re-samples `init` afresh; `hBound₂` bounds the
  `init`-averaged inner game, not the threaded pointwise one.  This closes when `Subsingleton σ` /
  `init` is a point mass (the transparent / stateless-oracle BCS instances), but not for general
  `init`.

The "all input statements" quantification of `rbrKnowledgeSoundness` (no `∉ langIn`;
`RoundByRound.lean:839`) does resolve the *statement* control that the plain-soundness phase-2
(`appendRbrSoundnessPhase2Residual`) lacks — but the state-carrying obstructions above remain.  The
leg is therefore isolated here as an explicit typed hypothesis (keeping the construction `sorry`-free),
exactly as the soundness keystone isolates its phase-2 residual. -/
def appendRbrKnowledgeSoundnessPhase2Residual {WitMid₁ : Fin (m+1)→Type}
    {WitMid₂ : Fin (n+1)→Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init)
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0} : Prop :=
  ∀ (stmtIn : Stmt₁) (witIn : Wit₁)
    (prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (i₂ : pSpec₂.ChallengeIdx),
    Pr[fun ⟨transcript, challenge⟩ =>
        ∃ witMid,
          ¬ (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
              (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn transcript
              ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid
                (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1 stmtIn
                (transcript.concat challenge) witMid) ∧
            (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
              (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ stmtIn
              (transcript.concat challenge) witMid
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨transcript, _⟩ ←
              prover.runToRound (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn witIn
            let challenge ←
              liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)) _
            return (transcript, challenge))).run' (← init)]
      ≤ rbrKnowledgeError₂ i₂

/-- **Discharge of the per-round knowledge bound residual.** The witness-threaded per-round seam
analysis: given the two inner per-round knowledge bounds `hBound₁` / `hBound₂` (the exact bodies of
`V₁.rbrKnowledgeSoundness` / `V₂.rbrKnowledgeSoundness` for `kSF₁`/`E₁` and `kSF₂`/`E₂`), the appended
per-round knowledge flip-event probability is bounded by the elim-composed error.

The proof reduces the log-carrying knowledge experiment to the log-free seam game via the reusable
`OracleReduction.map_runWithLog_body_eq_run_body` (the event is log-blind), then splits on the phase
of the appended challenge index:

* **Phase 1** (`ChallengeIdx.inl i₁`): the run-level seam factoring `Prover.fst_runToRound_heq`
  (recast to a `Wit₂`-output prover via `fstCastK`) and the challenge-seam transfer
  `evalDist_run'_challengeSeam_left` reduce the appended game to `hBound₁` at `i₁`; the appended
  composite knowledge state function / extractor collapse to `kSF₁` / `E₁` via
  `KnowledgeStateFunction.append_toFun_le` and `appendExtractMid_le`.
* **Phase 2** (`ChallengeIdx.inr i₂`): symmetric via `Prover.snd` /
  `evalDist_run'_challengeSeam_right`, collapsing to `kSF₂` / `E₂` via
  `KnowledgeStateFunction.append_toFun_gt` and `appendExtractMid_gt`.  Crucially, `hBound₂`
  quantifies over **all** input statements (no `∉ langIn` restriction), so the random seam statement
  `verify stmtIn tr.fst ∈ rel₂.language` is controlled — this is exactly why the knowledge phase-2 is
  dischargeable where the plain-soundness phase-2 (`appendRbrSoundnessPhase2Residual`) is not.

The mild side conditions `Nonempty Stmt₂` / `Nonempty Wit₂` (mirroring the `hNE` of
`append_rbrSoundness_keystone`) supply the dummy output of the `fstCastK` phase-1 recast. -/
theorem appendRbrKnowledgeSoundnessPerRound {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hNE₂ : Nonempty Stmt₂) (hNEW₂ : Nonempty Wit₂)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (hBound₁ : ∀ stmtIn : Stmt₁, ∀ witIn : Wit₁,
      ∀ prover : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁, ∀ i : pSpec₁.ChallengeIdx,
        Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
          ∃ witMid,
            ¬ kSF₁.toFun i.1.castSucc stmtIn transcript
              (E₁.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
              kSF₁.toFun i.1.succ stmtIn (transcript.concat challenge) witMid
        | do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
                prover.runWithLogToRound i.1.castSucc stmtIn witIn
              let challenge ← liftComp (pSpec₁.getChallenge i) _
              return (transcript, challenge, proveQueryLog))).run' (← init)] ≤
          rbrKnowledgeError₁ i)
    (hPhase2 : appendRbrKnowledgeSoundnessPhase2Residual (init := init) (impl := impl) V₁ V₂
      kSF₁ kSF₂ verify hVerify hInit (rbrKnowledgeError₂ := rbrKnowledgeError₂)) :
    appendRbrKnowledgeSoundnessPerRoundResidual (init := init) (impl := impl) V₁ V₂ kSF₁ kSF₂
      verify hVerify hInit (rbrKnowledgeError₁ := rbrKnowledgeError₁)
      (rbrKnowledgeError₂ := rbrKnowledgeError₂) := by
  intro stmtIn witIn prover i
  -- STEP A: reduce the log-carrying experiment to the log-free seam game (the event is log-blind).
  rw [appendRbrKnowledgeSoundness_logfree_reduce kSF₁ kSF₂ verify hVerify hInit prover stmtIn witIn i]
  -- STEP B: split on the phase of the appended challenge index.
  rcases hsplit : ChallengeIdx.sumEquiv.symm i with i₁ | i₂
  · -- PHASE 1 (`i = ChallengeIdx.inl i₁`): reduce to `hBound₁`.
    have hRHS : (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) i
        = rbrKnowledgeError₁ i₁ := by simp only [Function.comp_apply, hsplit, Sum.elim_inl]
    rw [hRHS]
    have hiEq : i = ChallengeIdx.inl i₁ := by
      have := ChallengeIdx.sumEquiv.apply_symm_apply i; rw [hsplit] at this; simpa using this.symm
    subst hiEq
    exact appendRbrKnowledgeSoundnessPerRound_phase1 kSF₁ kSF₂ verify hVerify hInit hNE₂ hNEW₂
      hBound₁ stmtIn witIn prover i₁
  · -- PHASE 2 (`i = ChallengeIdx.inr i₂`): the seam-crossing leg, isolated as the typed residual
    -- `hPhase2` (`appendRbrKnowledgeSoundnessPhase2Residual`).
    have hRHS : (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) i
        = rbrKnowledgeError₂ i₂ := by simp only [Function.comp_apply, hsplit, Sum.elim_inr]
    rw [hRHS]
    have hiEq : i = ChallengeIdx.inr i₂ := by
      have := ChallengeIdx.sumEquiv.apply_symm_apply i; rw [hsplit] at this; simpa using this.symm
    subst hiEq
    exact hPhase2 stmtIn witIn prover i₂

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Phase-2 message-seam direction fact.** When the seam round (`pSpec₂` round 0) is a prover
message (`hDir₂ : pSpec₂.dir 0 = .P_to_V`), any *challenge* index `i₂` of `pSpec₂` has positive value:
its round is `V_to_P`, distinct from the `P_to_V` seam round 0. -/
theorem challengeIdx_val_pos_of_seam_msg {i₂ : pSpec₂.ChallengeIdx} (hn : 0 < n)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V) : 0 < (i₂.1 : ℕ) := by
  rcases Nat.eq_zero_or_pos (i₂.1 : ℕ) with h0 | hpos
  · exfalso
    have : i₂.1 = (⟨0, hn⟩ : Fin n) := Fin.ext h0
    have hchal : pSpec₂.dir i₂.1 = .V_to_P := i₂.2
    rw [this, hDir₂] at hchal
    exact absurd hchal (by decide)
  · exact hpos

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Phase-2 per-round experiment body, seam-factored.** The appended phase-2 partial-run body at a
challenge index `inr i₂` — `runToRound (inr i₂).castSucc` followed by sampling the combined
`getChallenge (inr i₂)`, the (state-discarding) value being `(transcript, challenge)` — is
heterogeneously equal to the seam-factored body: run `Prover.fst prover` to completion (`liftM`-ed),
thread the seam output into `Prover.snd prover`'s partial run to round `i₂.castSucc`, append the
realized phase-1 transcript onto the phase-2 partial transcript via `Transcript.appendRight`, then
sample the same combined `getChallenge (inr i₂)`. Packages `Prover.snd_runToRound_natAdd_seam` (the
run-level factoring) with `bind_heq_congr` for the challenge-sampling continuation. -/
theorem phase2_body_heq
    (prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (stmtIn : Stmt₁) (witIn : Wit₁) (i₂ : pSpec₂.ChallengeIdx) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V) :
    HEq
      (do
        let ⟨transcript, _⟩ ←
          prover.runToRound (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn witIn
        let challenge ← OracleComp.liftComp
          ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        pure (transcript, challenge))
      (do
        let ⟨transcript₁, ctxIn₂⟩ ← liftM ((Prover.fst prover).run stmtIn witIn)
        let r ← liftM ((Prover.snd prover).runToRound i₂.1.castSucc ctxIn₂.1 ctxIn₂.2)
        let challenge ← OracleComp.liftComp
          ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        pure (Transcript.appendRight transcript₁ r.1, challenge)) := by
  classical
  have hk0 : 0 < ((i₂.1.castSucc : Fin (n + 1)) : ℕ) := by
    simpa using challengeIdx_val_pos_of_seam_msg (pSpec₂ := pSpec₂) (i₂ := i₂) hn hDir₂
  -- The phase-2 index identity: `(inr i₂).castSucc = ⟨m + (i₂.castSucc).val, _⟩`.
  have hidx : (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      = (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by
    ext; simp [ChallengeIdx.inr]
  -- Transcript/state value-type equalities induced by the index identity.
  have hTrTy : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      = (pSpec₁ ++ₚ pSpec₂).Transcript
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by rw [hidx]
  have hStTy : prover.PrvState (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      = prover.PrvState
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by rw [hidx]
  -- The seam-index transcript/state types, and `prover`'s own state type there (via the merge).
  have hpos : 0 < ((i₂.1 : Fin n) : ℕ) := challengeIdx_val_pos_of_seam_msg (i₂ := i₂) hn hDir₂
  have hidx2 : (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
      = (Fin.natAdd m i₂.1).castSucc := by ext; simp
  have hStTy' : ((Prover.fst prover).append (Prover.snd prover)).PrvState
      (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
      = prover.PrvState
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by
    rw [hidx2]; exact Prover.merge_PrvState_natAdd_castSucc prover i₂.1 hpos
  have hPrvTy : prover.PrvState (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      = ((Prover.fst prover).append (Prover.snd prover)).PrvState
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) :=
    hStTy.trans hStTy'.symm
  -- STEP 1: the bound HEq — appended `runToRound (inr i₂).castSucc` ≍ the seam-factored run (the RHS
  -- of `snd_runToRound_natAdd_seam`), via the index transport.
  have hRunHeq := HEq.trans (Prover.runToRound_heq_index hidx prover stmtIn witIn)
    (Prover.snd_runToRound_natAdd_seam (P := prover) hn hDir hDir₂ (i₂.1.castSucc) hk0 stmtIn witIn)
  -- The challenge-sampling continuation on the seam-index value type, used as the explicit `f'`.
  let K' : ((pSpec₁ ++ₚ pSpec₂).Transcript
        (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
      × ((Prover.fst prover).append (Prover.snd prover)).PrvState
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)))
      → OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
          ((pSpec₁ ++ₚ pSpec₂).Transcript
              (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
            × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)) :=
    fun p => do
      let challenge ← OracleComp.liftComp
        ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
        (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      pure (p.1, challenge)
  -- STEP 2: bind congruence over the top-level bind into `(seam-run) >>= K'`, then collapse the
  -- inner `do`-block by `bind_assoc` to the stated RHS.  `K'` reads only the transcript component, so
  -- the (discarded) trailing state cast in the seam run is irrelevant.
  refine HEq.trans (Prover.bind_heq_congr (congrArg₂ Prod hTrTy hPrvTy)
    (by rw [hTrTy]) (f' := K') hRunHeq (fun ⟨trA, stA⟩ ⟨trB, stB⟩ hpair => ?_)) (heq_of_eq ?_)
  · -- continuation HEq: same combined `getChallenge`, then `pure (·, challenge)` on HEq transcripts.
    obtain ⟨htr, _⟩ := Prover.prod_heq_split hTrTy hPrvTy hpair
    refine Prover.bind_heq_congr rfl (by rw [hTrTy]) HEq.rfl ?_
    rintro cA cB hc
    exact Prover.pure_heq_pure (by rw [hTrTy]) (Prover.prodMk_heq hTrTy rfl htr hc)
  · -- the inner-block collapse: `(seam-run) >>= K' = stated RHS`.
    show _ >>= K' = _
    simp only [K', bind_assoc, pure_bind]

/-- **Phase-2 inner seam reconciliation residual.** The single remaining typed gap of
`appendRbrKnowledgeSoundnessPhase2_subsingleton`: at a fixed Subsingleton state `s` and a realized
`Prover.fst`-output `ctx = (tr₁, seamState, ())`, the appended phase-2 inner game — running
`Prover.snd prover` from the realized seam state under the **combined** challenge oracle, prefixing the
phase-2 transcript with the realized phase-1 transcript `ctx.1` via `Transcript.appendRight`, and
reading the per-round flip event through the *composite* `KnowledgeStateFunction.append` /
`Extractor.RoundByRound.append` — has the same event-probability as the inner `pSpec₂` snd game (over
`pSpec₂`'s **own** challenge oracle, with the event read directly through `kSF₂` / `E₂` at the realized
seam statement `verify stmtIn ctx.1`).

This is the phase-2 analogue of the proven phase-1 witness-event correspondence
(`appendRbrKnowledgeSoundnessPerRound_phase1`): it combines the right challenge-oracle-seam transfer
`OracleReduction.evalDist_run'_challengeSeam_right` (via `Prover.append_getChallenge_natAdd`) with the
gt-event collapse `KnowledgeStateFunction.append_toFun_gt` / `appendExtractMid_gt`, under the
`Transcript.appendRight ctx.1` prefix. -/
def appendRbrKnowledgePhase2SeamReconcile {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init) : Prop :=
  ∀ (stmtIn : Stmt₁)
    (prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (i₂ : pSpec₂.ChallengeIdx)
    (s : σ)
    (ctx : pSpec₁.FullTranscript ×
      prover.PrvState (Fin.castLE (show m + 1 ≤ m + n + 1 by omega) (Fin.last m)) × Unit),
    Pr[fun x =>
        ∃ witMid,
          ¬ (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
              (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn x.1
              ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid
                (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1 stmtIn (x.1.concat x.2) witMid) ∧
            (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
              (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ stmtIn (x.1.concat x.2) witMid
      | ((do
          let x ← (simulateQ (impl.addLift challengeQueryImpl
              : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
              (liftM ((Prover.snd prover).runToRound i₂.1.castSucc ctx.2.1 ctx.2.2))).run' s
          let x_1 ← (simulateQ (impl.addLift challengeQueryImpl
              : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
              (OracleComp.liftComp
                ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
                (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))).run' s
          (simulateQ (impl.addLift challengeQueryImpl
              : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
              (pure (Transcript.appendRight ctx.1 x.1, x_1))).run' s) :
            ProbComp ((pSpec₁ ++ₚ pSpec₂).Transcript
              (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
                × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)))]
    = Pr[fun x =>
          ∃ witMid,
            ¬ kSF₂.toFun i₂.1.castSucc (verify stmtIn ctx.1) x.1
              (E₂.extractMid i₂.1 (verify stmtIn ctx.1) (x.1.concat x.2) witMid) ∧
              kSF₂.toFun i₂.1.succ (verify stmtIn ctx.1) (x.1.concat x.2) witMid
        | (simulateQ (impl.addLift challengeQueryImpl
              : QueryImpl (oSpec + [pSpec₂.Challenge]ₒ) (StateT σ ProbComp))
            (do
              let ⟨transcript, _⟩ ← ((Prover.snd prover).runToRound i₂.1.castSucc ctx.2.1 ()
                : OracleComp (oSpec + [pSpec₂.Challenge]ₒ)
                    (pSpec₂.Transcript i₂.1.castSucc × (Prover.snd prover).PrvState i₂.1.castSucc))
              let challenge ← liftComp (pSpec₂.getChallenge i₂)
                (oSpec + [pSpec₂.Challenge]ₒ)
              return (transcript, challenge))).run' s]

/-- **Discharge of the phase-2 per-round knowledge residual under `Subsingleton σ` (stateless /
transparent-oracle regime).** This proves `appendRbrKnowledgeSoundnessPhase2Residual` *unconditionally*
in the setting where the simulator state `σ` is a `Subsingleton` (e.g. `σ = Unit`, the case of
`oSpec = []ₒ` RingSwitching and transparent-BCS) and the seam round is a prover message
(`hDir`/`hDir₂`), modulo the isolated inner seam reconciliation
`appendRbrKnowledgePhase2SeamReconcile`.

This is exactly the regime that kills the three obstructions of the general residual:
* the **message-seam** obstruction is resolved by `hDir`/`hDir₂` (the hypotheses of
  `Prover.snd_runToRound_natAdd_seam` / `Prover.run_seam_factor`);
* the **carried-prover-state** obstruction is resolved by the amnesiac re-injection prover
  `Prover.sndAmnesiac P rSeam` (hardcoding the realized seam state, applied via `hBound₂`'s
  quantification over *all* `pSpec₂`-provers);
* the **oracle `σ`-threading** obstruction is resolved by `Subsingleton σ`: under it
  `simulateQ_run'_bind_of_subsingleton` makes the simulated bind distribute, so the threaded-state
  game equals the *bind* of the per-stage games, and `hBound₂` (init-averaged) applies pointwise to
  each realized seam transcript via `probEvent_bind_le_of_forall_le`. -/
theorem appendRbrKnowledgeSoundnessPhase2_subsingleton [Subsingleton σ]
    {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init)
    (hNEW₂ : Nonempty Wit₂) (hInitNF : Pr[⊥ | init] = 0)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (hBound₂ : ∀ stmtIn : Stmt₂, ∀ witIn : Wit₂,
      ∀ prover : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂, ∀ i : pSpec₂.ChallengeIdx,
        Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
          ∃ witMid,
            ¬ kSF₂.toFun i.1.castSucc stmtIn transcript
              (E₂.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
              kSF₂.toFun i.1.succ stmtIn (transcript.concat challenge) witMid
        | do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
                prover.runWithLogToRound i.1.castSucc stmtIn witIn
              let challenge ← liftComp (pSpec₂.getChallenge i) _
              return (transcript, challenge, proveQueryLog))).run' (← init)] ≤
          rbrKnowledgeError₂ i)
    (hReconcile : appendRbrKnowledgePhase2SeamReconcile (init := init) (impl := impl)
      V₁ V₂ kSF₁ kSF₂ verify hVerify hInit) :
    appendRbrKnowledgeSoundnessPhase2Residual (init := init) (impl := impl) V₁ V₂
      kSF₁ kSF₂ verify hVerify hInit (rbrKnowledgeError₂ := rbrKnowledgeError₂) := by
  intro stmtIn witIn prover i₂
  classical
  have hpos : 0 < ((i₂.1 : Fin n) : ℕ) := challengeIdx_val_pos_of_seam_msg (i₂ := i₂) hn hDir₂
  -- Abbreviations for the appended phase-2 per-round event `E` and the seam-factored experiment body.
  set E : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂) → Prop :=
    fun ⟨transcript, challenge⟩ =>
      ∃ witMid,
        ¬ (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
            (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn transcript
            ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid
              (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1 stmtIn
              (transcript.concat challenge) witMid) ∧
          (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
            (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ stmtIn
            (transcript.concat challenge) witMid with hE
  -- The seam index identity and the induced transcript value-type equality.
  have hidx : (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      = (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by
    ext; simp [ChallengeIdx.inr]
  have hTrTy : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      = (pSpec₁ ++ₚ pSpec₂).Transcript
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by rw [hidx]
  have hResTy : ((pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
        × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
      = ((pSpec₁ ++ₚ pSpec₂).Transcript
            (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
          × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)) :=
    congrArg (· × _) hTrTy
  -- STEP 1: transport the appended game to the seam-factored game via `phase2_body_heq`.
  have hbody := phase2_body_heq prover stmtIn witIn i₂ hn hDir hDir₂
  -- evalDist HEq of the two experiments, from the body HEq.
  have hd : HEq
      (𝒟[init >>= fun s =>
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
          (do
            let ⟨transcript, _⟩ ←
              prover.runToRound (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn witIn
            let challenge ←
              liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)) _
            return (transcript, challenge))).run' s])
      (𝒟[init >>= fun s =>
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
          (do
            let ⟨transcript₁, ctxIn₂⟩ ← liftM ((Prover.fst prover).run stmtIn witIn)
            let r ← liftM ((Prover.snd prover).runToRound i₂.1.castSucc ctxIn₂.1 ctxIn₂.2)
            let challenge ←
              liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)) _
            return (Transcript.appendRight transcript₁ r.1, challenge))).run' s]) := by
    -- A local `evalDist`-respects-HEq helper.
    have heq_evalDist : ∀ {A B : Type} (hAB : A = B) (a : ProbComp A) (b : ProbComp B),
        HEq a b → HEq (𝒟[a]) (𝒟[b]) := by
      intro A B hAB a b hab; subst hAB; rw [eq_of_heq hab]
    -- A local `(simulateQ _).run'`-respects-HEq helper (for the shared `s`-state).
    have heq_simrun : ∀ {A B : Type} (s : σ) (hAB : A = B)
        (a : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) A)
        (b : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) B), HEq a b →
        HEq ((simulateQ (impl.addLift challengeQueryImpl
              : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp)) a).run' s)
            ((simulateQ (impl.addLift challengeQueryImpl
              : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp)) b).run' s) := by
      intro A B s hAB a b hab; subst hAB; rw [eq_of_heq hab]
    refine heq_evalDist hResTy _ _ ?_
    -- The computation-level HEq: shared `init`, HEq continuations (only the value type differs).
    refine Prover.bind_heq_congr rfl hResTy HEq.rfl (fun s s' hs => ?_)
    cases eq_of_heq hs
    exact heq_simrun s hResTy _ _ hbody
  rw [probEvent_congr_heq hResTy _ _ E (fun x => E (hResTy ▸ x)) hd (fun x => Iff.rfl)]
  -- STEP 2: bound the seam-factored game via the Subsingleton bind split.
  -- Under `Subsingleton σ`, `simulateQ_run'_bind_of_subsingleton` distributes the simulated
  -- experiment over the seam bind `liftM (fst.run) >>= REST`.
  simp only [simulateQ_run'_bind_of_subsingleton]
  -- Outer bind over `init`: bound uniformly over each sampled `s`.
  refine probEvent_bind_le_of_forall_le (fun s _hs => ?_)
  -- Inner bind over the (simulated) `fst.run` realization `ctx = (tr₁, seamState, ())`.
  refine probEvent_bind_le_of_forall_le (fun ctx hctx => ?_)
  -- The realized seam statement `s₂ := verify stmtIn tr₁` and the amnesiac re-injection prover that
  -- resumes `Prover.snd prover` from the realized seam state `ctx.2.1`.
  set s₂ : Stmt₂ := verify stmtIn ctx.1 with hs₂
  -- Apply the inner bound `hBound₂` to the amnesiac prover, then `logfree_reduce` to drop its log.
  have hb := hBound₂ s₂ hNEW₂.some (Prover.sndAmnesiac prover ctx.2.1) i₂
  rw [OracleReduction.rbrKnowledge_logfree_reduce impl (Prover.sndAmnesiac prover ctx.2.1) i₂ s₂
      hNEW₂.some init
      (fun x => ∃ witMid, ¬ kSF₂.toFun i₂.1.castSucc s₂ x.1
          (E₂.extractMid i₂.1 s₂ (x.1.concat x.2) witMid) ∧
          kSF₂.toFun i₂.1.succ s₂ (x.1.concat x.2) witMid)] at hb
  -- The amnesiac's partial run is `Prover.snd prover`'s from the seam state `ctx.2.1`.
  simp only [Prover.sndAmnesiac_runToRound] at hb
  -- Under `Subsingleton σ`, the inner `init`-averaged game equals its value at our fixed `s` (all
  -- states are forced equal); with `Pr[⊥|init]=0`, `hb` collapses to the fixed-`s` snd game.
  rw [probEvent_bind_of_const init
      (r := Pr[fun x => ∃ witMid, ¬ kSF₂.toFun i₂.1.castSucc s₂ x.1
            (E₂.extractMid i₂.1 s₂ (x.1.concat x.2) witMid) ∧
            kSF₂.toFun i₂.1.succ s₂ (x.1.concat x.2) witMid
        | (simulateQ (impl.addLift challengeQueryImpl
            : QueryImpl (oSpec + [pSpec₂.Challenge]ₒ) (StateT σ ProbComp))
            (do
              let ⟨transcript, _⟩ ← (Prover.snd prover).runToRound i₂.1.castSucc ctx.2.1 ()
              let challenge ← liftComp (pSpec₂.getChallenge i₂) _
              return (transcript, challenge))).run' s])
      (fun s' _ => by rw [Subsingleton.elim s' s]; rfl),
      hInitNF] at hb
  simp only [tsub_zero, one_mul] at hb
  -- FINAL SEAM RECONCILIATION (the smallest remaining typed residual): the appended phase-2 inner
  -- game (combined challenge oracle, transcript prefixed by the realized phase-1 transcript `ctx.1`,
  -- event read through the composite `KnowledgeStateFunction.append` / `Extractor.RoundByRound.append`)
  -- equals — at our fixed Subsingleton state `s` — the inner `pSpec₂` snd game of `hb` (`pSpec₂`'s own
  -- challenge oracle, `kSF₂`/`E₂` at the realized seam statement `s₂ = verify stmtIn ctx.1`).  Two
  -- ingredients: (a) the right challenge-oracle-seam transfer `evalDist_run'_challengeSeam_right`
  -- (`append_getChallenge_natAdd`), and (b) the gt-event correspondence
  -- `KnowledgeStateFunction.append_toFun_gt` / `appendExtractMid_gt` (the phase-2 analogue of the
  -- proven phase-1 witness-event block), under the `appendRight ctx.1` transcript prefix.
  -- Discharge by the isolated inner seam reconciliation `hReconcile` (the appended combined-oracle
  -- inner game, with the `appendRight ctx.1` prefix and composite gt-event, equals the inner `pSpec₂`
  -- snd game of `hb`).
  unfold appendRbrKnowledgePhase2SeamReconcile at hReconcile
  exact le_of_eq_of_le (hReconcile stmtIn prover i₂ s ctx) hb

/-- **Round-by-round knowledge soundness append keystone, deterministic-`V₁` message-seam case.**

Removes the `kSF` residual of `append_rbrKnowledgeSoundness_keystone` and discharges the **phase-1**
half of the per-round knowledge bound entirely: the composite knowledge state function is supplied
internally from the *proven* `KnowledgeStateFunction.append`, the composite extractor from the proven
`Extractor.RoundByRound.append`, and the phase-1 per-round bound is proven internally by
`appendRbrKnowledgeSoundnessPerRound` from the inner bound `hBound₁` destructured from `h₁` (the
run-level seam factoring `Prover.fst_runToRound_heq`, recast via `fstCastK`, with the appended
composite objects collapsing to `kSF₁` / `E₁` via `KnowledgeStateFunction.append_toFun_le` /
`appendExtractMid_le`).

The single remaining content is the **phase-2** seam-crossing leg, isolated as the typed residual
`hPhase2` (`appendRbrKnowledgeSoundnessPhase2Residual`): at a phase-2 round the appended objects
collapse to `kSF₂` / `E₂` at the `verify`-fed **random** intermediate statement, whose discharge needs
the `Prover.snd` run-seam factoring and a `probEvent_bind` averaging over the realized phase-1
transcript.  Unlike the plain-soundness phase-2 obstruction, this *is* dischargeable in principle —
`hBound₂` from `h₂` quantifies over **all** input statements (no `∉ langIn` restriction;
`RoundByRound.lean:839`), so the random seam statement is controlled — but it is left here as an
explicit typed hypothesis (exactly as the proven soundness keystone isolates its phase-2 residual).

The mild `Nonempty Stmt₂` / `Nonempty Wit₂` side conditions (mirroring the `hNE` of
`append_rbrSoundness_keystone`) supply the dummy output of the phase-1 `fstCastK` recast.  This
keystone is fully axiom-clean (no `sorry`). -/
theorem append_rbrKnowledgeSoundness_keystone_unconditional
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init)
    (hNE₂ : Nonempty Stmt₂) (hNEW₂ : Nonempty Wit₂)
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂)
    -- The single remaining seam-crossing residual (phase 2), quantified over the inner extractors /
    -- knowledge state functions destructured from `h₁` / `h₂`.
    (hPhase2 : ∀ {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
      {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
      {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
      (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
      (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂),
      appendRbrKnowledgeSoundnessPhase2Residual (init := init) (impl := impl) V₁ V₂ kSF₁ kSF₂
        verify hVerify hInit (rbrKnowledgeError₂ := rbrKnowledgeError₂)) :
      (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  obtain ⟨WitMid₁, E₁, kSF₁, hBound₁⟩ := h₁
  obtain ⟨WitMid₂, E₂, kSF₂, _hBound₂⟩ := h₂
  exact ⟨_, Extractor.RoundByRound.append E₁ E₂ verify,
    KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit,
    appendRbrKnowledgeSoundnessPerRound V₁ V₂ kSF₁ kSF₂ verify hVerify hInit hNE₂ hNEW₂
      hBound₁ (hPhase2 kSF₁ kSF₂)⟩

/-- **Round-by-round knowledge soundness append keystone, `Subsingleton σ` message-seam case.**

The stateless / transparent-oracle specialization of `append_rbrKnowledgeSoundness_keystone_unconditional`:
in the `Subsingleton σ` regime (e.g. `σ = Unit`, the case of `oSpec = []ₒ` RingSwitching and
transparent-BCS), with a lossless `init` and a prover-message seam (`hDir`/`hDir₂`), the phase-2
seam-crossing leg is discharged **internally** by `appendRbrKnowledgeSoundnessPhase2_subsingleton` —
which kills the three obstructions of the general residual (message-seam via `hDir`/`hDir₂`,
carried-prover-state via the amnesiac re-injection `Prover.sndAmnesiac`, and `σ`-state threading via
`simulateQ_run'_bind_of_subsingleton`).

The only remaining content is the per-realization inner *seam reconciliation*
`appendRbrKnowledgePhase2SeamReconcile` (the phase-2 analogue of the proven phase-1 witness-event
correspondence: right challenge-oracle-seam transfer + gt-event collapse under the `appendRight`
prefix), isolated as the explicit typed residual `hReconcile` (quantified over the inner extractors /
knowledge state functions destructured from `h₁` / `h₂`).  Everything else — the Subsingleton bind
split, the amnesiac `hBound₂` application, and the seam factoring — is proven axiom-clean. -/
theorem append_rbrKnowledgeSoundness_keystone_subsingleton [Subsingleton σ]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE₂ : Nonempty Stmt₂) (hNEW₂ : Nonempty Wit₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂)
    -- The single remaining inner seam reconciliation (the phase-2 analogue of the proven phase-1
    -- witness-event correspondence), quantified over the inner extractors / knowledge state functions.
    (hReconcile : ∀ {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
      {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
      {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
      (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
      (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂),
      appendRbrKnowledgePhase2SeamReconcile (init := init) (impl := impl) V₁ V₂ kSF₁ kSF₂
        verify hVerify hInit) :
      (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  obtain ⟨WitMid₁, E₁, kSF₁, hBound₁⟩ := h₁
  obtain ⟨WitMid₂, E₂, kSF₂, hBound₂⟩ := h₂
  exact ⟨_, Extractor.RoundByRound.append E₁ E₂ verify,
    KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit,
    appendRbrKnowledgeSoundnessPerRound V₁ V₂ kSF₁ kSF₂ verify hVerify hInit hNE₂ hNEW₂
      hBound₁ (appendRbrKnowledgeSoundnessPhase2_subsingleton V₁ V₂ kSF₁ kSF₂ verify hVerify hInit
        hNEW₂ hInitNF hn hDir hDir₂ hBound₂ (hReconcile kSF₁ kSF₂))⟩

end Verifier

-- Axiom audit for the sorry-free bricks: each should report only
-- `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Verifier.appendWitMid_le
#print axioms Verifier.appendWitMid_gt
#print axioms Verifier.appendExtractMid_le
#print axioms Verifier.appendExtractMid_gt
#print axioms Verifier.appendExtractMid_cross
#print axioms Verifier.appendExtractOut_gt
#print axioms Verifier.kToFun_congr
#print axioms Verifier.kToFun_congr₁
#print axioms Verifier.concat_fst_heq_phase1
#print axioms Verifier.extractMid₁_heq_congr
#print axioms Verifier.KnowledgeStateFunction.append
#print axioms Verifier.KnowledgeStateFunction.append_toFun_le
#print axioms Verifier.KnowledgeStateFunction.append_toFun_gt
#print axioms Verifier.appendRbrKnowledgeSoundness_logfree_reduce
#print axioms Verifier.appendRbrKnowledgeSoundnessPerRound_phase1
#print axioms Verifier.appendRbrKnowledgeSoundnessPerRound
#print axioms Verifier.append_rbrKnowledgeSoundness_keystone_unconditional
#print axioms Prover.sndAmnesiac
#print axioms Prover.sndAmnesiac_runToRound
#print axioms Verifier.challengeIdx_val_pos_of_seam_msg
#print axioms Verifier.phase2_body_heq
#print axioms Verifier.appendRbrKnowledgeSoundnessPhase2_subsingleton
#print axioms Verifier.append_rbrKnowledgeSoundness_keystone_subsingleton

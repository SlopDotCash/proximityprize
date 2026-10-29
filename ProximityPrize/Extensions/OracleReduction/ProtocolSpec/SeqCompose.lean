/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.OracleReduction.ProtocolSpec.SeqCompose

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ProximityPrize.Extensions.Data.Fin.Sigma
import ArkLib.OracleReduction.ProtocolSpec.Cast

/-! # Sequential Composition of Protocol Specifications

This file collects all definitions and theorems about sequentially composing `ProtocolSpec`s and
their associated data. -/

universe u v

open OracleComp OracleSpec

namespace ProtocolSpec

/-! ### Composition of Two Protocol Specifications -/

variable {m n : ℕ}

variable {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

namespace Transcript

variable {k : Fin (m + n + 1)}

end Transcript

namespace FullTranscript

/-- **Prefix/concat commutation for transcript append.**  Concatenating a final message onto a
right-appended transcript `T₁ ++ₜ T₂` agrees — heterogeneously, up to the `++ₚ`-associativity of the
underlying protocol specs (`((pSpec₁ ++ₚ pSpec₂) ++ₚ single)` vs `(pSpec₁ ++ₚ (pSpec₂ ++ₚ single))`)
— with appending `T₁` onto the *right* transcript with the message already concatenated.  Since
`concat = Fin.hconcat` and `++ₜ = Fin.happend`, this is the `FullTranscript`-level instance of the
prefix/snoc commutation `Fin.happend_hconcat_eq`. -/
theorem concat_append_right (T₁ : FullTranscript pSpec₁) (T₂ : FullTranscript pSpec₂)
    (dir : Direction) {NextMessage : Type} (msg : NextMessage) :
    HEq ((T₁ ++ₜ T₂).concat dir msg) (T₁ ++ₜ (T₂.concat dir msg)) := by
  unfold FullTranscript.concat FullTranscript.append
  show HEq (Fin.happend (Fin.happend T₁ T₂) (fun _ : Fin 1 => msg))
    (Fin.happend T₁ (Fin.happend T₂ (fun _ : Fin 1 => msg)))
  rw [Fin.happend_assoc]
  refine (Fin.heq_fun_iff' (by omega) ?_).mpr ?_
  · intro i; simp [Fin.vappend_assoc]
  · intro i; exact cast_heq _ _

-- @[simp]
-- theorem append_cast_left {n m : ℕ} {pSpec₁ pSpec₂ : ProtocolSpec n} {pSpec' : ProtocolSpec m}
--     {T₁ : FullTranscript pSpec₁} {T₂ : FullTranscript pSpec'} (n' : ℕ)
--     (h : n + m = n' + m) (hSpec : dcast h pSpec₁ = pSpec₂) :
--       dcast₂ h (by simp) (T₁ ++ₜ T₂) = (dcast₂ (Nat.add_right_cancel h) (by simp) T₁) ++ₜ T₂ :=
-- by
--   simp [append, dcast₂, ProtocolSpec.cast, Fin.append_cast_left]

-- @[simp]
-- theorem append_cast_right {n m : ℕ} (pSpec : ProtocolSpec n) (pSpec' : ProtocolSpec m) (m' : ℕ)
--     (h : n + m = n + m') :
--       dcast h (pSpec ++ₚ pSpec') = pSpec ++ₚ (dcast (Nat.add_left_cancel h) pSpec') := by
--   simp [append, dcast, ProtocolSpec.cast, Fin.append_cast_right]

end FullTranscript

/-- A joint-transcript message at an `inl` index is (heterogeneously) the first-half message. -/
theorem messages_inl (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) (k : pSpec₁.MessageIdx) :
    HEq (T.messages (MessageIdx.inl k)) (T.fst.messages k) := by
  unfold FullTranscript.messages FullTranscript.fst MessageIdx.inl
  exact (cast_heq _ _).symm

/-- A joint-transcript message at an `inr` index is (heterogeneously) the second-half message. -/
theorem messages_inr (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) (k : pSpec₂.MessageIdx) :
    HEq (T.messages (MessageIdx.inr k)) (T.snd.messages k) := by
  unfold FullTranscript.messages FullTranscript.snd MessageIdx.inr
  exact (cast_heq _ _).symm

/-- A joint-transcript challenge at an `inl` index is (heterogeneously) the first-half challenge. -/
theorem challenges_inl (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) (k : pSpec₁.ChallengeIdx) :
    HEq (T.challenges (ChallengeIdx.inl k)) (T.fst.challenges k) := by
  unfold FullTranscript.challenges FullTranscript.fst ChallengeIdx.inl
  exact (cast_heq _ _).symm

/-- A joint-transcript challenge at an `inr` index is (heterogeneously) the second-half one. -/
theorem challenges_inr (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) (k : pSpec₂.ChallengeIdx) :
    HEq (T.challenges (ChallengeIdx.inr k)) (T.snd.challenges k) := by
  unfold FullTranscript.challenges FullTranscript.snd ChallengeIdx.inr
  exact (cast_heq _ _).symm

namespace FullTranscript

end FullTranscript

section Append

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

variable [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]

-- instance instSubSpecOfProtocolSpecAppendChallenge :
--     SubSpec ([pSpec₁.Challenge]ₒ + [pSpec₂.Challenge]ₒ) ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) where
--   monadLift | q => match q.1 with
--     | Sum.inl j => by
--       simpa using query (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) ⟨j.2, ()⟩
--     | Sum.inr j => by
--       simpa using query (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) j.inr ()

-- instance : SubSpec [pSpec₁.Challenge]ₒ ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) where
--   monadLift | query i t => instSubSpecOfProtocolSpecAppendChallenge.monadLift (query (Sum.inl i) t)

-- instance : SubSpec [pSpec₂.Challenge]ₒ ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) where
--   monadLift | query i t => instSubSpecOfProtocolSpecAppendChallenge.monadLift (query (Sum.inr i) t)

end Append

section SeqCompose

end SeqCompose

end ProtocolSpec

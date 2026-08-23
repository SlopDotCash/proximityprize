/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.ProtocolSpec.Basic

/-!
# Dependent Casting for Protocol Specifications

This module formalizes dependent casting functions and equivalence relations for `ProtocolSpec` and
its associated components across round-count and specification equalities. In interactive oracle
proofs, reductions are often defined over varying parameterizations of the protocol structure (e.g.,
varying round counts or message spaces). Dependent casting allows safe transport of message indices
(`MessageIdx`), challenge indices (`ChallengeIdx`), and transcripts (`Transcript`, `FullTranscript`)
between structurally isomorphic specifications.
-/

open OracleComp

variable {n₁ n₂ : ℕ} (hn : n₁ = n₂)

namespace ProtocolSpec

/-! ### Casting Protocol Specifications -/

/-- Casting a `ProtocolSpec` across an equality of the number of rounds

One should use the type-class function `dcast` instead of this one. -/
protected def cast (pSpec : ProtocolSpec n₁) : ProtocolSpec n₂ :=
  ⟨pSpec.dir ∘ (Fin.cast hn.symm), pSpec.«Type» ∘ (Fin.cast hn.symm)⟩

@[simp]
theorem cast_id : ProtocolSpec.cast (Eq.refl n₁) = id := rfl

instance instDCast : DCast Nat ProtocolSpec where
  dcast h := ProtocolSpec.cast h
  dcast_id := cast_id

theorem cast_eq_dcast {h : n₁ = n₂} {pSpec : ProtocolSpec n₁} :
    pSpec.cast h = dcast h pSpec := rfl

/-! ### Casting (Partial) Transcripts -/

variable {pSpec₁ : ProtocolSpec n₁} {pSpec₂ : ProtocolSpec n₂}

@[simp]
theorem cast_dir_idx {hn} (hSpec : pSpec₁.cast hn = pSpec₂) {i : Fin n₁} :
    pSpec₂.dir (Fin.cast hn i) = pSpec₁.dir i := by
  simp [← hSpec, ProtocolSpec.cast]

theorem cast_Type_idx {hn} (hSpec : pSpec₁.cast hn = pSpec₂) {i : Fin n₁} :
    pSpec₂.«Type» (Fin.cast hn i) = pSpec₁.«Type» i := by
  simp [← hSpec, ProtocolSpec.cast]

@[simp]
theorem cast_dir_idx_symm {hn} (hSpec : pSpec₁.cast hn = pSpec₂) {i : Fin n₂} :
    pSpec₁.dir (Fin.cast hn.symm i) = pSpec₂.dir i := by
  simp [← hSpec, ProtocolSpec.cast]

theorem cast_Type_idx_symm {hn} (hSpec : pSpec₁.cast hn = pSpec₂) {i : Fin n₂} :
    pSpec₁.«Type» (Fin.cast hn.symm i) = pSpec₂.«Type» i := by
  simp [← hSpec, ProtocolSpec.cast]

theorem cast_symm {hn} (hSpec : pSpec₁.cast hn = pSpec₂) : pSpec₂.cast hn.symm = pSpec₁ := by
  rw [cast_eq_dcast] at hSpec ⊢
  exact dcast_symm hn hSpec

variable (hSpec : pSpec₁.cast hn = pSpec₂)

namespace MessageIdx

/-- Casting a message index across an equality of `ProtocolSpec`s. -/
protected def cast (i : MessageIdx pSpec₁) : MessageIdx pSpec₂ :=
  ⟨Fin.cast hn i.1, by simp [← hSpec, ProtocolSpec.cast, i.property]⟩

@[simp]
theorem cast_id : MessageIdx.cast (Eq.refl n₁) rfl = (id : pSpec₁.MessageIdx → _) := rfl

theorem cast_injective : Function.Injective (MessageIdx.cast hn hSpec) := by
  intro i j h'
  simp only [MessageIdx, MessageIdx.cast, Subtype.mk.injEq, Fin.cast_inj] at h'
  ext : 1
  exact h'

instance instDCast₂ : DCast₂ Nat ProtocolSpec (fun _ pSpec => MessageIdx pSpec) where
  dcast₂ h := MessageIdx.cast h
  dcast₂_id := cast_id

theorem cast_eq_dcast₂ {hn} {hSpec : pSpec₁.cast hn = pSpec₂} {i : MessageIdx pSpec₁} :
    i.cast hn hSpec = dcast₂ hn hSpec i := rfl

end MessageIdx

namespace Message

variable {hn}

@[simp]
theorem cast_idx_symm {i : MessageIdx pSpec₂} :
    pSpec₁.Message (i.cast hn.symm (cast_symm hSpec)) = pSpec₂.Message i :=
  cast_Type_idx_symm hSpec

theorem cast_idx {i : MessageIdx pSpec₁} :
    pSpec₂.Message (i.cast hn hSpec) = pSpec₁.Message i :=
  cast_Type_idx hSpec

end Message

namespace ChallengeIdx

/-- Casting a challenge index across an equality of `ProtocolSpec`s. -/
protected def cast (i : ChallengeIdx pSpec₁) : ChallengeIdx pSpec₂ :=
  ⟨Fin.cast hn i.1, by simp [← hSpec, ProtocolSpec.cast, i.property]⟩

@[simp]
theorem cast_id : ChallengeIdx.cast (Eq.refl n₁) rfl = (id : pSpec₁.ChallengeIdx → _) := rfl

theorem cast_injective : Function.Injective (ChallengeIdx.cast hn hSpec) := by
  intro i j h'
  simp only [ChallengeIdx, ChallengeIdx.cast, Subtype.mk.injEq, Fin.cast_inj] at h'
  ext : 1
  exact h'

instance instDCast₂ : DCast₂ Nat ProtocolSpec (fun _ pSpec => ChallengeIdx pSpec) where
  dcast₂ h := ChallengeIdx.cast h
  dcast₂_id := cast_id

theorem cast_eq_dcast₂ {hn} {hSpec : pSpec₁.cast hn = pSpec₂} {i : ChallengeIdx pSpec₁} :
    i.cast hn hSpec = dcast₂ hn hSpec i := rfl

end ChallengeIdx

namespace Challenge

variable {hn}

@[simp]
theorem cast_idx {i : ChallengeIdx pSpec₁} :
    pSpec₂.Challenge (i.cast hn hSpec) = pSpec₁.Challenge i :=
  cast_Type_idx hSpec

@[simp]
theorem cast_idx_symm {i : ChallengeIdx pSpec₂} :
    pSpec₁.Challenge (i.cast hn.symm (cast_symm hSpec)) = pSpec₂.Challenge i :=
  cast_Type_idx_symm hSpec

end Challenge

variable {k : Fin (n₁ + 1)} {l : Fin (n₂ + 1)}

namespace Transcript

/-- Casting two partial transcripts across an equality of `ProtocolSpec`s, where the cutoff indices
  are equal. -/
protected def cast (hIdx : k.val = l.val) (hSpec : pSpec₁.cast hn = pSpec₂)
    (T : pSpec₁.Transcript k) : pSpec₂.Transcript l :=
  fun i => _root_.cast (by rw [← hSpec]; rfl) (T (Fin.cast hIdx.symm i))

@[simp]
theorem cast_id : Transcript.cast rfl rfl rfl = (id : pSpec₁.Transcript k → _) := rfl

variable {hn} (hIdx : k.val = l.val) (hSpec : pSpec₁.cast hn = pSpec₂)

instance instDCast₃ : DCast₃ Nat (fun n => Fin (n + 1)) (fun n _ => ProtocolSpec n)
    (fun _ k pSpec => pSpec.Transcript k) where
  dcast₃ h h' h'' T := Transcript.cast h
    (by simp only [dcast] at h'; rw [← h']; subst h; rfl)
    (by simp only [ProtocolSpec.cast_eq_dcast, dcast_eq_root_cast]; exact h'')
    T
  dcast₃_id := cast_id

end Transcript

namespace FullTranscript

/-! ### Casting Full Transcripts -/

/-- Casting a transcript across an equality of `ProtocolSpec`s.

Internally invoke `Transcript.cast` with the last indices. -/
protected def cast (T : FullTranscript pSpec₁) :
    FullTranscript pSpec₂ :=
  Transcript.cast (k := Fin.last n₁) (l := Fin.last n₂) hn hn hSpec T

@[simp]
theorem cast_id : FullTranscript.cast rfl rfl = (id : pSpec₁.FullTranscript → _) := rfl

instance instDCast₂ : DCast₂ Nat ProtocolSpec (fun _ pSpec => FullTranscript pSpec) where
  dcast₂ h h' T := FullTranscript.cast h h' T
  dcast₂_id := cast_id

theorem cast_eq_dcast₂ {T : FullTranscript pSpec₁} :
    dcast₂ hn hSpec T = FullTranscript.cast hn hSpec T := rfl

end FullTranscript

section Instances

theorem challengeOracleInterface_cast {h : n₁ = n₂} {hSpec : pSpec₁.cast h = pSpec₂}
    {i : pSpec₁.ChallengeIdx} :
    pSpec₁.challengeOracleInterface i =
      dcast (by simp) (pSpec₂.challengeOracleInterface (i.cast hn hSpec)) := by
  subst h; subst hSpec; simp [challengeOracleInterface, ChallengeIdx.cast]; rfl

end Instances

end ProtocolSpec

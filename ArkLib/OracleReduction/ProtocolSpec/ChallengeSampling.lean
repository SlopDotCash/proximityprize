/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/
import ArkLib.OracleReduction.ProtocolSpec.GuardedTranscript
import ArkLib.ToMathlib.Logic.HEq

/-!
# Challenge sampling across sequential composition

Adapted from ArkLib reviewed head `9b0b5c962d97a9a0a9388c0bcc7e70d503e9ddd9`.
Transporting a sampled appended-protocol challenge to the selected component
preserves the distribution and the component's sampling instance.
-/
set_option autoImplicit false
open OracleComp OracleSpec ProtocolSpec
namespace ProtocolSpec
variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
/-- The challenge type of an appended protocol at a left-injected challenge index agrees with the
challenge type of the left component. This is the transport fact needed to move challenge data
across `++ₚ`; it is `append_Type_castAdd` at the underlying round index, since `ChallengeIdx.inl`
is `Fin.castAdd` on rounds. -/
theorem challenge_append_inl (i : ChallengeIdx pSpec₁) :
    (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i) = pSpec₁.Challenge i :=
  append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) i.1

/-- The challenge type of an appended protocol at a right-injected challenge index agrees with the
challenge type of the right component. Dually to `challenge_append_inl`, this is
`append_Type_natAdd` at the underlying round index. -/
theorem challenge_append_inr (i : ChallengeIdx pSpec₂) :
    (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i) = pSpec₂.Challenge i :=
  append_Type_natAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) i.1

end ProtocolSpec
section
variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
/-! ## Challenge-sampling transport across `++ₚ`

The security definitions draw challenges by `uniformSample`-ing the protocol's challenge type at a
given index, using the `SampleableType` instance found there. For an appended protocol that
instance is built by `Fin.fappend₂`, so it is not *syntactically* the component's instance — it is
the component's instance transported along `challenge_append_inl` / `challenge_append_inr`.

Every distributional comparison between an appended protocol and its components needs to know that
this transport is the identity on distributions. That is what the lemmas below establish. They are
the `SampleableType` analogue of `message_interface_inl` / `message_interface_inr` below, and are
proved the same way, by computing the `Fin.fappend₂` with `Fin.fappend₂_left` / `_right`. -/

section ChallengeSampling

variable [inst₁ : ∀ i, SampleableType (pSpec₁.Challenge i)]
    [inst₂ : ∀ i, SampleableType (pSpec₂.Challenge i)]

/-- Transporting a uniform sample along an equality of types, when the two `SampleableType`
instances correspond across that equality, leaves the distribution unchanged. -/
private theorem uniformSample_cast {α β : Type} (h : α = β)
    (instα : SampleableType α) (instβ : SampleableType β) (hI : HEq instα instβ) :
    cast h <$> (@uniformSample α instα) = (@uniformSample β instβ) := by
  subst h
  cases hI
  exact id_map _

/-- The appended protocol's `SampleableType` instance at a left-injected challenge index is the
first component's instance, transported along `challenge_append_inl`. -/
private theorem challenge_sampleable_inl (i : pSpec₁.ChallengeIdx) : HEq (inst₁ i)
    (inferInstance : SampleableType ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i))) := by
  rcases i with ⟨i, hi⟩
  let u : (i : Fin m) →
      (h : pSpec₁.dir i = .V_to_P) → SampleableType (pSpec₁.«Type» i) :=
    fun i h => inst₁ ⟨i, h⟩
  let v : (i : Fin n) →
      (h : pSpec₂.dir i = .V_to_P) → SampleableType (pSpec₂.«Type» i) :=
    fun i h => inst₂ ⟨i, h⟩
  have hf : HEq
      (Fin.fappend₂ (F := fun (dir : Direction) (type : Type) =>
        (_ : dir = Direction.V_to_P) → SampleableType type)
        u v (Fin.castAdd n i))
      (u i) := by
    rw [Fin.fappend₂_left]
    exact cast_heq _ _
  have hDomain : (pSpec₁.dir i = Direction.V_to_P) =
      ((Fin.vappend pSpec₁.dir pSpec₂.dir) (Fin.castAdd n i) = Direction.V_to_P) :=
    congrArg (· = Direction.V_to_P) (Fin.vappend_left pSpec₁.dir pSpec₂.dir i).symm
  have ha : HEq hi (ChallengeIdx.inl ⟨i, hi⟩).property :=
    (cast_heq hDomain hi).symm.trans (heq_of_eq (Subsingleton.elim _ _))
  change HEq (inst₁ ⟨i, hi⟩)
    ((Fin.fappend₂ (F := fun (dir : Direction) (type : Type) =>
      (_ : dir = Direction.V_to_P) → SampleableType type)
      u v (Fin.castAdd n i)) (ChallengeIdx.inl ⟨i, hi⟩).property)
  exact heq_apply hDomain
    (congrArg SampleableType (Fin.vappend_left pSpec₁.«Type» pSpec₂.«Type» i).symm)
    hf.symm ha

/-- The appended protocol's `SampleableType` instance at a right-injected challenge index is the
second component's instance, transported along `challenge_append_inr`. -/
private theorem challenge_sampleable_inr (i : pSpec₂.ChallengeIdx) : HEq (inst₂ i)
    (inferInstance : SampleableType ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i))) := by
  rcases i with ⟨i, hi⟩
  let u : (i : Fin m) →
      (h : pSpec₁.dir i = .V_to_P) → SampleableType (pSpec₁.«Type» i) :=
    fun i h => inst₁ ⟨i, h⟩
  let v : (i : Fin n) →
      (h : pSpec₂.dir i = .V_to_P) → SampleableType (pSpec₂.«Type» i) :=
    fun i h => inst₂ ⟨i, h⟩
  have hf : HEq
      (Fin.fappend₂ (F := fun (dir : Direction) (type : Type) =>
        (_ : dir = Direction.V_to_P) → SampleableType type)
        u v (Fin.natAdd m i))
      (v i) := by
    rw [Fin.fappend₂_right]
    exact cast_heq _ _
  have hDomain : (pSpec₂.dir i = Direction.V_to_P) =
      ((Fin.vappend pSpec₁.dir pSpec₂.dir) (Fin.natAdd m i) = Direction.V_to_P) :=
    congrArg (· = Direction.V_to_P) (Fin.vappend_right pSpec₁.dir pSpec₂.dir i).symm
  have ha : HEq hi (ChallengeIdx.inr ⟨i, hi⟩).property :=
    (cast_heq hDomain hi).symm.trans (heq_of_eq (Subsingleton.elim _ _))
  change HEq (inst₂ ⟨i, hi⟩)
    ((Fin.fappend₂ (F := fun (dir : Direction) (type : Type) =>
      (_ : dir = Direction.V_to_P) → SampleableType type)
      u v (Fin.natAdd m i)) (ChallengeIdx.inr ⟨i, hi⟩).property)
  exact heq_apply hDomain
    (congrArg SampleableType (Fin.vappend_right pSpec₁.«Type» pSpec₂.«Type» i).symm)
    hf.symm ha

/-- **Challenge transport, left.** Sampling the appended protocol's challenge at a left-injected
index and casting back along `challenge_append_inl` is exactly sampling the first component's
challenge. -/
theorem uniformSample_challenge_append_inl (i : pSpec₁.ChallengeIdx) :
    cast (challenge_append_inl (pSpec₂ := pSpec₂) i) <$>
        ($ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i)))
      = ($ᵗ (pSpec₁.Challenge i)) :=
  uniformSample_cast _ _ _ (challenge_sampleable_inl (pSpec₂ := pSpec₂) i).symm

/-- **Challenge transport, right.** The `challenge_append_inr` analogue of
`uniformSample_challenge_append_inl`. -/
theorem uniformSample_challenge_append_inr (i : pSpec₂.ChallengeIdx) :
    cast (challenge_append_inr (pSpec₁ := pSpec₁) i) <$>
        ($ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i)))
      = ($ᵗ (pSpec₂.Challenge i)) :=
  uniformSample_cast _ _ _ (challenge_sampleable_inr (pSpec₁ := pSpec₁) i).symm

end ChallengeSampling
end

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import Mathlib.Init
import Mathlib.Logic.Embedding.Basic
import Mathlib.Probability.Distributions.Uniform

/-!
  # Serialization and Deserialization

  This file contains simple APIs for serialization and deserialization of types in terms of other
  types.
-/

universe u v

/-- Type class for types that can be serialized to another type (most often `ByteArray` or
  `String`). -/
class Serialize (α : Type u) (β : Type v) where
  serialize : α → β

export Serialize (serialize)

/-- Type class for injective serialization. -/
class Serialize.IsInjective (α : Type u) (β : Type v) [inst : Serialize α β] : Prop where
  serialize_inj : Function.Injective inst.serialize

/-- Every type serializes to itself by the identity map. -/
instance instSerializeSelf (α : Type u) : Serialize α α where
  serialize := id

/-- Identity serialization is injective. -/
instance instSerializeIsInjectiveSelf (α : Type u) : Serialize.IsInjective α α where
  serialize_inj := fun _ _ h => h

/-- Type class for types that can be deserialized from another type (most often `ByteArray` or
  `String`), which _never_ fails. -/
class Deserialize (α : Type u) (β : Type v) where
  deserialize : β → α

/-- Every type deserializes from itself by the identity map. -/
instance instDeserializeSelf (α : Type u) : Deserialize α α where
  deserialize := id

-- Local instance using total-variation distance on finite PMFs.
instance {α : Type*} [Fintype α] : Dist (PMF α) where
  dist := fun a b => ∑ x, abs ((a x).toReal - (b x).toReal)

open NNReal in
/-- Type class for deserialization on two non-empty finite types `α`, `β`, which pushes forward the
  uniform distribution of `β` to the uniform distribution of `α`, up to some error -/
class Deserialize.CloseToUniform (α : Type u) (β : Type u)
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] [Deserialize α β] where
  ε : ℝ≥0
  ε_close : dist (PMF.uniformOfFintype α) (deserialize <$> PMF.uniformOfFintype β) ≤ ε


/-- Type class for types that can be deserialized from another type (most often `ByteArray` or
  `String`), returning an `Option` if the deserialization fails. -/
class DeserializeOption (α : Type u) (β : Type v) where
  deserialize : β → Option α

/-- Type class for types that can be serialized and deserialized (with potential failure) to/from
  another type (most often `ByteArray` or `String`). -/
class Serde (α : Type u) (β : Type v) extends Serialize α β, DeserializeOption α β

-- Note: for codecs into an alphabet `σ`, we basically want the following:
-- variable {α σ : Type*} {n : ℕ} [inst : Serialize α (Vector σ n)] [inst.IsInjective]

-- Note: for codecs out of an alphabet `σ`, we basically want the following:
-- variable {α σ : Type u} [Fintype α] [Nonempty α] [Fintype σ] [Nonempty σ] {n : ℕ} [NeZero n]
--   [inst : Deserialize α (Vector σ n)] [inst.CloseToUniform]

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.Data.Probability.Notation
import CompPoly.Data.Classes.Serialize
import ArkLib.Data.Classes.CloseToUniform
import Mathlib.Probability.Distributions.Uniform

/-!
  # Serialization and Deserialization

  Serialization classes are imported from CompPoly. Identity codecs and the PMF formulation
  of statistical closeness remain downstream extensions. The canonical measure formulation is
  `Deserialize.CloseToUniform`; `Deserialize.PMFCloseToUniform` records the historical PMF
  statement without redefining that canonical class.
-/

universe u v

/-- Every type serializes to itself by the identity map. -/
instance instSerializeSelf (α : Type u) : Serialize α α where
  serialize := id

/-- Identity serialization is injective. -/
instance instSerializeIsInjectiveSelf (α : Type u) : Serialize.IsInjective α α where
  serialize_inj := fun _ _ h => h

/-- Every type deserializes from itself by the identity map. -/
instance instDeserializeSelf (α : Type u) : Deserialize α α where
  deserialize := id

-- Local instance using total-variation distance on finite PMFs.
instance {α : Type*} [Fintype α] : Dist (PMF α) where
  dist := fun a b => ∑ x, abs ((a x).toReal - (b x).toReal)

open NNReal in
/-- Type class for deserialization on two non-empty finite types `α`, `β`, which pushes forward the
  uniform distribution of `β` to the uniform distribution of `α`, up to some error -/
class Deserialize.PMFCloseToUniform (α : Type u) (β : Type u)
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] [Deserialize α β] where
  ε : ℝ≥0
  ε_close : dist (ProximityPrize.Compatibility.uniformOfFintype α) (deserialize <$> ProximityPrize.Compatibility.uniformOfFintype β) ≤ ε

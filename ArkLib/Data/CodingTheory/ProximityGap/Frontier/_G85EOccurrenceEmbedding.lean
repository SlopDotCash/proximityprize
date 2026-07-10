/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# G85E: occurrence-correct embeddings from a core/padding permutation

If `(core ++ pad)` is a permutation of an endpoint list, `List.Perm.idxBij` matches every source
occurrence to a distinct endpoint position.  Restricting this bijection to the prefix and suffix
gives embeddings of core and padding occurrences, preserves their values, and yields disjoint
ranges—even when values repeat.

This is the occurrence-matching interface required to choose G84I's core embedding from G83M's
multiset reconstruction.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G85EOccurrenceEmbedding

variable {A : Type*} [DecidableEq A]

/-- Endpoint positions matched to the ordered core prefix. -/
def coreEmbedding {core pad endpoint : List A} (hp : (core ++ pad).Perm endpoint) :
    Fin core.length ↪ Fin endpoint.length where
  toFun i := hp.idxBij (Fin.castAdd pad.length i)
  inj' := hp.idxBij_injective.comp (Fin.castAdd_injective core.length pad.length)

/-- Endpoint positions matched to the ordered padding suffix. -/
def paddingEmbedding {core pad endpoint : List A} (hp : (core ++ pad).Perm endpoint) :
    Fin pad.length ↪ Fin endpoint.length where
  toFun j := hp.idxBij (Fin.natAdd core.length j)
  inj' := hp.idxBij_injective.comp (Fin.natAdd_injective pad.length core.length)

/-- The core embedding preserves every matched occurrence value. -/
theorem get_coreEmbedding {core pad endpoint : List A} (hp : (core ++ pad).Perm endpoint)
    (i : Fin core.length) :
    endpoint[(coreEmbedding hp i).val] = core[i.val] := by
  simpa [coreEmbedding] using hp.getElem_idxBij_eq_getElem (Fin.castAdd pad.length i)

/-- The padding embedding preserves every matched occurrence value. -/
theorem get_paddingEmbedding {core pad endpoint : List A} (hp : (core ++ pad).Perm endpoint)
    (j : Fin pad.length) :
    endpoint[(paddingEmbedding hp j).val] = pad[j.val] := by
  simpa [paddingEmbedding] using hp.getElem_idxBij_eq_getElem (Fin.natAdd core.length j)

/-- Prefix-core and suffix-padding occurrence ranges are disjoint in the endpoint. -/
theorem coreEmbedding_ne_paddingEmbedding {core pad endpoint : List A}
    (hp : (core ++ pad).Perm endpoint) (i : Fin core.length) (j : Fin pad.length) :
    coreEmbedding hp i ≠ paddingEmbedding hp j := by
  intro h
  have hsource : Fin.castAdd pad.length i = Fin.natAdd core.length j :=
    hp.idxBij_injective (Subtype.ext_iff.mp h)
  have hval := congrArg Fin.val hsource
  simp only [Fin.coe_castAdd, Fin.natAdd_val] at hval
  omega

end ArkLib.ProximityGap.Frontier.G85EOccurrenceEmbedding

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G85EOccurrenceEmbedding.get_coreEmbedding
#print axioms ArkLib.ProximityGap.Frontier.G85EOccurrenceEmbedding.get_paddingEmbedding
#print axioms ArkLib.ProximityGap.Frontier.G85EOccurrenceEmbedding.coreEmbedding_ne_paddingEmbedding

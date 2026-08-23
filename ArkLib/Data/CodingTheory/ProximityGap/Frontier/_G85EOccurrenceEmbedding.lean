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

def coreSourceIndex (core pad : List A) (i : Fin core.length) : Fin (core ++ pad).length :=
  Fin.cast List.length_append.symm (Fin.castAdd pad.length i)

def paddingSourceIndex (core pad : List A) (j : Fin pad.length) : Fin (core ++ pad).length :=
  Fin.cast List.length_append.symm (Fin.natAdd core.length j)

/-- Endpoint positions matched to the ordered core prefix. -/
def coreEmbedding {core pad endpoint : List A} (hp : (core ++ pad).Perm endpoint) :
    Fin core.length ↪ Fin endpoint.length where
  toFun i := hp.idxBij (coreSourceIndex core pad i)
  inj' := hp.idxBij_injective.comp
    ((Fin.cast_injective List.length_append.symm).comp
      (Fin.castAdd_injective core.length pad.length))

/-- Endpoint positions matched to the ordered padding suffix. -/
def paddingEmbedding {core pad endpoint : List A} (hp : (core ++ pad).Perm endpoint) :
    Fin pad.length ↪ Fin endpoint.length where
  toFun j := hp.idxBij (paddingSourceIndex core pad j)
  inj' := hp.idxBij_injective.comp
    ((Fin.cast_injective List.length_append.symm).comp
      (Fin.natAdd_injective pad.length core.length))

/-- The core embedding preserves every matched occurrence value. -/
theorem get_coreEmbedding {core pad endpoint : List A} (hp : (core ++ pad).Perm endpoint)
    (i : Fin core.length) :
    endpoint[(coreEmbedding hp i).val] = core[i.val] := by
  simpa [coreEmbedding, coreSourceIndex] using
    hp.getElem_idxBij_eq_getElem (coreSourceIndex core pad i)

/-- The padding embedding preserves every matched occurrence value. -/
theorem get_paddingEmbedding {core pad endpoint : List A} (hp : (core ++ pad).Perm endpoint)
    (j : Fin pad.length) :
    endpoint[(paddingEmbedding hp j).val] = pad[j.val] := by
  simpa [paddingEmbedding, paddingSourceIndex] using
    hp.getElem_idxBij_eq_getElem (paddingSourceIndex core pad j)

/-- Prefix-core and suffix-padding occurrence ranges are disjoint in the endpoint. -/
theorem coreEmbedding_ne_paddingEmbedding {core pad endpoint : List A}
    (hp : (core ++ pad).Perm endpoint) (i : Fin core.length) (j : Fin pad.length) :
    coreEmbedding hp i ≠ paddingEmbedding hp j := by
  intro h
  change hp.idxBij (coreSourceIndex core pad i) =
    hp.idxBij (paddingSourceIndex core pad j) at h
  have hsourceCast : coreSourceIndex core pad i = paddingSourceIndex core pad j :=
    hp.idxBij_injective h
  have hsource : Fin.castAdd pad.length i = Fin.natAdd core.length j := by
    apply Fin.cast_injective List.length_append.symm
    exact hsourceCast
  have hval := congrArg Fin.val hsource
  simp only [Fin.coe_castAdd, Fin.val_natAdd] at hval
  omega

end ArkLib.ProximityGap.Frontier.G85EOccurrenceEmbedding

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G85EOccurrenceEmbedding.get_coreEmbedding
#print axioms ArkLib.ProximityGap.Frontier.G85EOccurrenceEmbedding.get_paddingEmbedding
#print axioms ArkLib.ProximityGap.Frontier.G85EOccurrenceEmbedding.coreEmbedding_ne_paddingEmbedding

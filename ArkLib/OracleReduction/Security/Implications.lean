/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.StateRestoration
import ArkLib.OracleReduction.Salt
import ArkLib.OracleReduction.Security.SpecialSoundness
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Basic

/-!
# Implications between security notions

This compatibility module keeps the historical import target available. The primitive security
notions live in `Basic`, `RoundByRound`, and `StateRestoration`; the lattice of implications
between them (`knowledgeSoundness → soundness`, `roundByRound → soundness`, etc.) remains an open
formalization target rather than a closed proof surface in this build, so those statements are not
carried here as unproven declarations.

What this file *does* prove is the bridge between coordinate-wise special soundness and plain
special soundness (see the CWSS section below).
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

namespace Verifier

section Implications

/- TODO: establish the following results as a lattice of security notions, with `knowledge` and
`roundByRound` being two strengthenings of soundness:
- `knowledgeSoundness` implies `soundness`
- `roundByRoundSoundness` implies `soundness`
- `roundByRoundKnowledgeSoundness` implies `roundByRoundSoundness`
- `roundByRoundKnowledgeSoundness` implies `knowledgeSoundness`
- state-restoration soundness implies basic soundness (and the knowledge analogue)
-/

end Implications

end Verifier

/-! ## Coordinate-wise special soundness generalizes special soundness

Both `Verifier.specialSound` (`Security.SpecialSoundness`) and
`Verifier.coordinateWiseSpecialSound` (`Security.CoordinateWiseSpecialSoundness`) are *defined* as
instances of the shape-generic `Verifier.treeSpecialSound`, differing only in the challenge-tree
shape they fix:

* plain special soundness fixes `distinctShape k` — arity `kᵢ`, node predicate `Function.Injective`
  (the `kᵢ` sibling challenges are pairwise distinct);
* CWSS fixes `D.toShape` — arity `ℓᵢ·(kᵢ-1)+1`, node predicate `IsSpecialSoundFamily ℓᵢ kᵢ`.

For the canonical `ℓᵢ = 1` structure `CWSSStructure.ofSpecialSound k` the two shapes are *equal*
(`toShape_ofSpecialSound_eq_distinctShape`): the arity is `kᵢ` and `IsSpecialSoundFamily 1 kᵢ`
reduces to injectivity (`CoordinateWise.isSpecialSoundFamily_one_iff_injective`). The bridge
`Verifier.coordinateWiseSpecialSound_ofSpecialSound_iff` is then immediate from that shape
equality. -/

/-- Heterogeneous congruence for `Function.Injective`: injectivity transports across an equality of
the domain type together with a heterogeneous equality of the functions. -/
private theorem heq_injective {A A' β : Type} (h : A = A') {f : A → β} {g : A' → β}
    (hfg : HEq f g) : HEq (Function.Injective f) (Function.Injective g) := by
  subst h; obtain rfl := eq_of_heq hfg; exact HEq.rfl

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- The CWSS shape of the canonical `ℓᵢ = 1` structure `CWSSStructure.ofSpecialSound k` is exactly
the plain special-soundness shape `distinctShape k`. This is the structural heart of the equivalence
between CWSS and plain special soundness: both the arity (`1·(kᵢ-1)+1 = kᵢ`) and the node predicate
(`IsSpecialSoundFamily 1 kᵢ` vs. `Function.Injective`) agree. -/
theorem toShape_ofSpecialSound_eq_distinctShape (k : pSpec.ChallengeIdx → ℕ) (hk : ∀ i, 2 ≤ k i) :
    (CWSSStructure.ofSpecialSound k hk).toShape = distinctShape k := by
  have harity : (CWSSStructure.ofSpecialSound k hk).toShape.arity = (distinctShape k).arity := by
    funext i
    change 1 * (k i - 1) + 1 = k i
    have := hk i; omega
  refine ChallengeTreeShape.ext harity (Function.hfunext rfl (fun i i' hi => ?_))
  obtain rfl := eq_of_heq hi
  refine Function.hfunext (by rw [harity]) (fun c c' hc => ?_)
  refine HEq.trans (heq_of_eq (propext ?_)) (heq_injective (congrArg Fin (congrFun harity i)) hc)
  change CoordinateWise.IsSpecialSoundFamily 1 (k i)
      (fun j : Fin (1 * (k i - 1) + 1) =>
        (Equiv.funUnique (Fin 1) (pSpec.Challenge i)).symm (c j)) ↔ Function.Injective c
  rw [CoordinateWise.isSpecialSoundFamily_one_iff_injective]
  exact Equiv.comp_injective c (Equiv.funUnique (Fin 1) (pSpec.Challenge i)).symm

namespace Verifier

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **Coordinate-wise special soundness generalizes special soundness.** Coordinate-wise special
soundness for the canonical `ℓᵢ = 1` structure `CWSSStructure.ofSpecialSound k` is *equivalent* to
plain `(k)`-special soundness for the same input and output relations. Both unfold to
`Verifier.treeSpecialSound` of a shape, and the two shapes are equal
(`toShape_ofSpecialSound_eq_distinctShape`), so the bridge is immediate. This is the
`coordinateWiseSpecialSound (ofSpecialSound k) ↔ specialSound k` bridge promised in
`Security.SpecialSoundness`: CWSS recovers `k`-special soundness in the single-coordinate case. -/
theorem coordinateWiseSpecialSound_ofSpecialSound_iff (k : pSpec.ChallengeIdx → ℕ)
    (hk : ∀ i, 2 ≤ k i)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) :
    verifier.coordinateWiseSpecialSound init impl (CWSSStructure.ofSpecialSound k hk) relIn relOut
      ↔ verifier.specialSound init impl k relIn relOut := by
  unfold Verifier.coordinateWiseSpecialSound Verifier.specialSound
  rw [toShape_ofSpecialSound_eq_distinctShape]

end Verifier

namespace OracleVerifier

open ProtocolSpec

variable {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
  [∀ i, OracleInterface (pSpec.Message i)]

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **Coordinate-wise special soundness vs. plain special soundness, oracle form.** The oracle-
reduction analogue of `Verifier.coordinateWiseSpecialSound_ofSpecialSound_iff`, obtained by passing
to the underlying non-oracle verifier (both notions are defined via `OracleVerifier.toVerifier`). -/
theorem coordinateWiseSpecialSound_ofSpecialSound_iff (k : pSpec.ChallengeIdx → ℕ)
    (hk : ∀ i, 2 ≤ k i)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
    verifier.coordinateWiseSpecialSound init impl (CWSSStructure.ofSpecialSound k hk) relIn relOut
      ↔ verifier.specialSound init impl k relIn relOut :=
  Verifier.coordinateWiseSpecialSound_ofSpecialSound_iff init impl k hk relIn relOut
    verifier.toVerifier

end OracleVerifier

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G86RankCollapseDichotomy

/-!
# G103: replication no-go for the abstract syndrome-syzygy endpoint

G86/G87 localize any large family of bad scalars to a syzygy among witness functionals.  This
file red-teams that endpoint.  At the present abstract level, a syzygy is not a restrictive
event: one internally independent block of functionals annihilating a nonzero syndrome can be
replicated for arbitrarily many witness indices.  Every block remains independent and the common
syndrome remains plantable, while any two blocks force a global dependence.

This does **not** construct distinct bad scalars or concrete `mcaEvent` witnesses.  It proves that
the current abstract/per-block information alone cannot bound their number.  Any continuation of
the syndrome route must retain cross-witness structure, such as the dependence of the GRS rows on
the distinct scalar `γ`; merely producing a syzygy certificate is insufficient.  Issue #466/#507.
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.G103SyzygyReplicationNoGo

open Module
open G86RankCollapseDichotomy

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Replicate one constraint block across every witness index. -/
def replicatedBlock {r m : ℕ} (ψ : Fin m → Module.Dual F V) :
    Fin r × Fin m → Module.Dual F V := fun p => ψ p.2

/-- Replication preserves linear independence inside every witness block. -/
theorem replicatedBlock_block_linearIndependent {r m : ℕ}
    (ψ : Fin m → Module.Dual F V) (hψ : LinearIndependent F ψ) (i : Fin r) :
    LinearIndependent F (fun j : Fin m => replicatedBlock (r := r) ψ (i, j)) := by
  simpa [replicatedBlock] using hψ

/-- A common nonzero annihilated syndrome makes every replicated family plantable, independently
of the number of witness indices. -/
theorem replicatedBlock_plantable {r m : ℕ} (ψ : Fin m → Module.Dual F V)
    (v : V) (hv : v ≠ 0) (hann : ∀ j, ψ j v = 0) :
    Plantable (replicatedBlock (r := r) ψ) := by
  exact ⟨v, hv, fun p => hann p.2⟩

/-- Two replicated nonempty blocks are globally dependent even though each block may be internally
independent. -/
theorem replicatedBlock_not_linearIndependent {r m : ℕ} (hr : 2 ≤ r) (hm : 0 < m)
    (ψ : Fin m → Module.Dual F V) :
    ¬ LinearIndependent F (replicatedBlock (r := r) ψ) := by
  intro hli
  have hinj := hli.injective
  let i0 : Fin r := ⟨0, by omega⟩
  let i1 : Fin r := ⟨1, by omega⟩
  let j : Fin m := ⟨0, hm⟩
  have heq : replicatedBlock (r := r) ψ (i0, j) =
      replicatedBlock (r := r) ψ (i1, j) := by
    rfl
  have hpairs : (i0, j) = (i1, j) := hinj heq
  have : i0 = i1 := congrArg Prod.fst hpairs
  simpa [i0, i1] using congrArg Fin.val this

/-- The dependence can be returned in exactly the explicit coefficient-vector shape used by the
G86/G87 syzygy disjunct. -/
theorem replicatedBlock_syzygy {r m : ℕ} (hr : 2 ≤ r) (hm : 0 < m)
    (ψ : Fin m → Module.Dual F V) :
    ∃ c : Fin r × Fin m → F,
      (∑ p : Fin r × Fin m, c p • replicatedBlock (r := r) ψ p = 0) ∧
        ∃ p : Fin r × Fin m, c p ≠ 0 := by
  exact Fintype.not_linearIndependent_iff.mp
    (replicatedBlock_not_linearIndependent hr hm ψ)

/-- **Arbitrary-cardinality no-go.** One locally valid block generates, for every `r ≥ 2`, a
plantable `r`-witness abstract configuration whose blocks are all internally independent but whose
full family has an explicit syzygy.  Consequently those three properties imply no upper bound on
`r`. -/
theorem exists_abstract_configuration_of_one_block {r m : ℕ} (hr : 2 ≤ r) (hm : 0 < m)
    (ψ : Fin m → Module.Dual F V) (hψ : LinearIndependent F ψ)
    (v : V) (hv : v ≠ 0) (hann : ∀ j, ψ j v = 0) :
    ∃ φ : Fin r × Fin m → Module.Dual F V,
      Plantable φ ∧
      (∀ i : Fin r, LinearIndependent F (fun j : Fin m => φ (i, j))) ∧
      ∃ c : Fin r × Fin m → F,
        (∑ p : Fin r × Fin m, c p • φ p = 0) ∧
          ∃ p : Fin r × Fin m, c p ≠ 0 := by
  refine ⟨replicatedBlock ψ, replicatedBlock_plantable ψ v hv hann, ?_, ?_⟩
  · exact fun i => replicatedBlock_block_linearIndependent ψ hψ i
  · exact replicatedBlock_syzygy hr hm ψ

/-- Production-shaped calibration: the abstract endpoint is compatible with `2^30` witness
indices and the exact block width `2^24 + 1`, provided only the one-block data already used by the
bridge.  This is a logical calibration, not a concrete Reed--Solomon counterexample. -/
theorem production_abstract_syzygy_configuration
    (ψ : Fin (2 ^ 24 + 1) → Module.Dual F V) (hψ : LinearIndependent F ψ)
    (v : V) (hv : v ≠ 0) (hann : ∀ j, ψ j v = 0) :
    ∃ φ : Fin (2 ^ 30) × Fin (2 ^ 24 + 1) → Module.Dual F V,
      Plantable φ ∧
      (∀ i : Fin (2 ^ 30), LinearIndependent F (fun j => φ (i, j))) ∧
      ∃ c : Fin (2 ^ 30) × Fin (2 ^ 24 + 1) → F,
        (∑ p, c p • φ p = 0) ∧ ∃ p, c p ≠ 0 := by
  apply exists_abstract_configuration_of_one_block (r := 2 ^ 30) (m := 2 ^ 24 + 1)
      (by norm_num) (by norm_num) ψ hψ v hv hann

end ArkLib.ProximityGap.Frontier.G103SyzygyReplicationNoGo

#print axioms
  ArkLib.ProximityGap.Frontier.G103SyzygyReplicationNoGo.replicatedBlock_block_linearIndependent
#print axioms
  ArkLib.ProximityGap.Frontier.G103SyzygyReplicationNoGo.replicatedBlock_plantable
#print axioms
  ArkLib.ProximityGap.Frontier.G103SyzygyReplicationNoGo.replicatedBlock_syzygy
#print axioms
  ArkLib.ProximityGap.Frontier.G103SyzygyReplicationNoGo.exists_abstract_configuration_of_one_block
#print axioms
  ArkLib.ProximityGap.Frontier.G103SyzygyReplicationNoGo.production_abstract_syzygy_configuration

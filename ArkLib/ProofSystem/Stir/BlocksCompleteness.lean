/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.Round3Completeness
import ArkLib.OracleReduction.Composition.Sequential.SeqComposeOracleCompleteness

/-!
# Perfect completeness of the STIR chain middle phase (#301)

Perfect completeness of the M-block middle phase of the STIR chain, via the oracle-level
n-ary seqCompose completeness engine (`SeqComposeOracleCompleteness`). -/

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal StirIOP.Round OracleReduction

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- Per-challenge `Fintype` for the 3-slot spec (plain per-index form consumed by the n-ary
composition engine). -/
instance : ∀ j, Fintype ((pSpec3 ι F).Challenge j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => (inferInstance : Fintype F)
  | ⟨2, _⟩ => (inferInstance : Fintype F)

/-- Per-challenge `Inhabited` for the 3-slot spec. -/
instance : ∀ j, Inhabited ((pSpec3 ι F).Challenge j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => ⟨(0 : F)⟩
  | ⟨2, _⟩ => ⟨(0 : F)⟩

open scoped Classical in
/-- **Perfect completeness of the M-block middle phase** (`stirBlocksReduction`): the
`seqCompose` of `M` uniform-threading 3-slot blocks is perfectly complete against the
constant relation family `stirOStmtRel F φ deg δ`, by the oracle-level n-ary composition
engine fed with the per-block completeness `stirRound3Reduction'_perfectCompleteness`. -/
theorem stirBlocksReduction_perfectCompleteness (φ : ι ↪ F) (deg : ℕ) (M : ℕ) (δ : ℝ≥0)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery []ₒ β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp []ₒ β)) :
    (stirBlocksReduction φ deg M).perfectCompleteness init impl
      (stirOStmtRel F φ deg δ) (stirOStmtRel F φ deg δ) :=
  OracleReduction.seqCompose_perfectCompleteness_threaded
    (fun _ : Fin (M + 1) => F) (fun _ => OStmt ι F) (fun _ => Unit)
    (fun _ => stirRound3Reduction' φ deg)
    (coh := fun _ => instStirRound3Reduction'AppendCoherent φ deg)
    (fun _ => stirOStmtRel F φ deg δ)
    (fun _ => ⟨by omega, pSpec3_dir_zero⟩)
    hInit hImplSupp
    (fun _ => stirRound3Reduction'_perfectCompleteness init impl φ deg δ hInit)

end Round3

end StirIOP

#print axioms StirIOP.Round3.stirBlocksReduction_perfectCompleteness

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import VCVio

/-!
# Distributional bind-commutation for `OracleComp` (`evalDist`-level)

`OracleComp` is a free monad over oracle queries, so two **independent** computations do **not**
commute *syntactically*: `a >>= fun x => b >>= k x` and `b >>= fun y => a >>= fun x => k x y` are
different free-monad trees. They are, however, equal as **distributions**, because the underlying
sub-probability monad `SPMF` is commutative.

This file proves that commutation at the `evalDist` level. It is the exact tool needed to discharge
the sequential-composition run-factoring keystone (`Prover.appendRunRightResidual`, gating #13/#114)
in the **challenge** case, where the appended prover samples the round challenge *before* running
`P₁.output`, while the factored form `P₁.run ≫ P₂.run` runs `P₁.output` first — an
`output`/`getChallenge` commutation that is distributional, not syntactic. (See the analysis on the
keystone: the residual should be stated at `evalDist` level, where `SPMF.bind_comm` closes the gap.)
-/

open OracleComp

namespace SPMF

/-- **Sub-distributions commute.** For `SPMF` (`= OptionT PMF`), independent binds may be swapped:
`p >>= fun a => q >>= fun b => f a b = q >>= fun b => p >>= fun a => f a b`. The `none`-mass
(failure) accounting matches on both sides because failure of either factor zeroes the joint mass
symmetrically. -/
theorem bind_comm {α β γ : Type} (p : SPMF α) (q : SPMF β) (f : α → β → SPMF γ) :
    (p >>= fun a => q >>= fun b => f a b) = (q >>= fun b => p >>= fun a => f a b) := by
  ext z
  simp only [bind_apply_eq_tsum, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun b => tsum_congr fun a => ?_
  rw [mul_left_comm]

end SPMF

namespace OracleComp

/-- **Distributional bind-commutation for `OracleComp`.** Independent oracle computations commute
under `evalDist`: `𝒟[a >>= fun x => b >>= k x] = 𝒟[b >>= fun y => a >>= fun x => k x y]`. The
`OracleComp`-syntactic equality is false (free monad); this distribution-level one holds via
`SPMF.bind_comm`. -/
theorem evalDist_bind_comm {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    {α β γ : Type}
    (a : OracleComp spec α) (b : OracleComp spec β) (k : α → β → OracleComp spec γ) :
    (evalDist (a >>= fun x => b >>= fun y => k x y) : SPMF γ)
      = evalDist (b >>= fun y => a >>= fun x => k x y) := by
  simp only [evalDist_bind]
  exact SPMF.bind_comm _ _ _

end OracleComp

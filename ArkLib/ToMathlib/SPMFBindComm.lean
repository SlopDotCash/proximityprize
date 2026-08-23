/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ToMathlib.ProbabilityTheory.SPMF

/-!
# Commutativity of `SPMF` bind

`SPMF.bind_comm` is the sub-probability-mass-function analogue of `PMF.bind_comm`: binding two
independent sub-probability computations commutes. It is the foundational lemma underlying the
sequential-composition perfect-completeness keystone (`Reduction.append`): at the raw `OracleComp`
free-monad level the appended run executes both provers then both verifiers, while the sequential
form interleaves; the two distributions coincide only after interpreting into the commutative
`evalDist`/`SPMF` denotation, where the (independent) first verifier and second prover commute.
This is exactly that commutativity. Intended for upstreaming to VCVio's `SPMF` API.
-/

open scoped ENNReal

universe u

/-- **Commutativity of `SPMF` bind** (analogue of `PMF.bind_comm`). Binding two independent
sub-probability computations commutes:
`(p >>= fun a => q >>= fun b => f a b) = (q >>= fun b => p >>= fun a => f a b)`. -/
theorem SPMF.bind_comm {α β γ : Type u} (p : SPMF α) (q : SPMF β) (f : α → β → SPMF γ) :
    (p >>= fun a => q >>= fun b => f a b) = (q >>= fun b => p >>= fun a => f a b) := by
  ext y
  simp only [bind_apply_eq_tsum, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun b => tsum_congr fun a => ?_
  ring

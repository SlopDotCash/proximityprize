/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import VCVio.EvalDist.Defs.Basic

/-!
# Support laws from a compatible discrete semantics

A lawful lift into `SPMF` and `EvalDistCompatible` recover the support equations used by
older probability proofs. These lemmas do not require `ExactMonadAttach`: they derive the
set equations from the existing distribution semantics rather than adding operational laws.
-/

namespace SPMFSupport

universe u v

variable {m : Type u → Type v} [Monad m] [MonadAttach m]
  [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [EvalDistCompatible m]
  {α β : Type u}

/-- The support of a pure value follows from the pure law of the probability lift. -/
theorem support_pure (x : α) : support (pure x : m α) = {x} := by
  simp only [support_eq_SPMF_support, liftM, monadLift_pure, SPMF.support_pure]

/-- Compatible probability support decomposes through bind without extra attachment laws. -/
theorem support_bind (mx : m α) (my : α → m β) :
    support (mx >>= my) = ⋃ x ∈ support mx, support (my x) := by
  simp only [support_eq_SPMF_support, monadLift_bind, SPMF.support_bind]

/-- Membership form of the compatible probability bind law. -/
theorem mem_support_bind_iff (mx : m α) (my : α → m β) (y : β) :
    y ∈ support (mx >>= my) ↔ ∃ x ∈ support mx, y ∈ support (my x) := by
  simp only [support_bind, Set.mem_iUnion, exists_prop]

/-- Mapping sends compatible probability support to its image. -/
theorem support_map [LawfulMonad m] (f : α → β) (mx : m α) :
    support (f <$> mx) = f '' support mx := by
  rw [map_eq_bind_pure_comp, support_bind]
  simp only [Function.comp_apply, support_pure]
  ext y
  simp [Set.mem_image, eq_comm]

end SPMFSupport

#print axioms SPMFSupport.support_pure
#print axioms SPMFSupport.support_bind
#print axioms SPMFSupport.support_map

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ListDecoding.SubspacePolyGeneralSupport

/-!
# Bounded linearized support of the subspace polynomial

Sharpening `isQPowSupported_subspacePoly'`: every exponent in the support of `subspacePoly W`
(`W` a finite `𝔽_q`-subspace, `dim_𝔽 W = d`) is `q^i` with `i ≤ d` — the support sits exactly on
`{q^0, …, q^d}`.  This is the precise form BKR06's tight list-size count consumes: the "top
coefficients above the cutoff `q^u`" occupy only the `≤ d − u` linearized slots `q^{u+1}, …, q^d`,
giving the tight pattern count `q^{m(d−u)}` (vs. the generic window) — `BKR06Pigeonhole`'s `hexp`.
-/

open Polynomial BigOperators

namespace BKR06

variable {F : Type*} [Field F] [Fintype F]
variable {K : Type*} [Field K] [DecidableEq K] [Algebra F K]

/-- **Bounded linearized support.** Every exponent in `support (subspacePoly W)` is `q^i` for some
`i ≤ dim_𝔽 W`. -/
theorem subspacePoly_support_subset_qpow (W : Submodule F K) [Fintype W] :
    ∀ n ∈ (subspacePoly (subFinset W)).support,
      ∃ i ≤ Module.finrank F W, n = Fintype.card F ^ i := by
  intro n hn
  obtain ⟨i, hi⟩ := isQPowSupported_subspacePoly' W n hn
  refine ⟨i, ?_, hi⟩
  have hle : n ≤ (subspacePoly (subFinset W)).natDegree := le_natDegree_of_mem_supp n hn
  rw [subspacePoly_natDegree_eq_pow_finrank, hi] at hle
  exact (Nat.pow_le_pow_iff_right Fintype.one_lt_card).mp hle

end BKR06

-- Axiom audit.
#print axioms BKR06.subspacePoly_support_subset_qpow

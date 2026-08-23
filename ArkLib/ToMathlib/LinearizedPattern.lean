/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.LinearizedSupportStep

/-!
# Linearized top-pattern determines the low-degree part

For q-power-supported polynomials `P, Q` (`q = |F|`), the only exponents carrying coefficients are
the q-powers `q^i`.  Hence if `P` and `Q` agree on every "high" q-power coefficient `q^j` with
`j > u`, then `P - Q` is supported below `q^u` (all coefficients above `q^u` vanish).

This is the **tight** form of the BKR06 top-coefficient pattern argument: the "top pattern above the
cutoff `q^u`" lives in only the `d − u` linearized slots `q^{u+1}, …, q^d`, so equal patterns force
the difference into `degreeLT (q^u + 1)` — the slot economy behind BKR06's `q^{(u+1)m − v²}`
list-size count (`BKR06Pigeonhole` `hexp`).
-/

open Polynomial BigOperators

namespace ArkLib.LinearizedKernel

variable {F : Type*} [Field F] [Fintype F]
variable {K : Type*} [Field K] [Algebra F K]

/-- **Linearized top-pattern determines the low part.** If `P, Q` are q-power-supported and agree
on every high q-power coefficient (`P.coeff (q^j) = Q.coeff (q^j)` for `j > u`), then every
coefficient of `P - Q` above `q^u` vanishes. -/
theorem coeff_sub_eq_zero_of_qpow_pattern {P Q : K[X]}
    (hP : IsQPowSupported (F := F) P) (hQ : IsQPowSupported (F := F) Q) {u : ℕ}
    (hpat : ∀ j, u < j → P.coeff (Fintype.card F ^ j) = Q.coeff (Fintype.card F ^ j)) :
    ∀ n, Fintype.card F ^ u < n → (P - Q).coeff n = 0 := by
  classical
  intro n hn
  rw [coeff_sub]
  by_cases hqp : ∃ j, n = Fintype.card F ^ j
  · obtain ⟨j, rfl⟩ := hqp
    have hju : u < j := by
      by_contra hle
      push_neg at hle
      have : Fintype.card F ^ j ≤ Fintype.card F ^ u :=
        Nat.pow_le_pow_right Fintype.one_lt_card.le hle
      omega
    rw [hpat j hju, sub_self]
  · have hPn : P.coeff n = 0 := by
      by_contra h
      exact hqp (hP n (mem_support_iff.mpr h))
    have hQn : Q.coeff n = 0 := by
      by_contra h
      exact hqp (hQ n (mem_support_iff.mpr h))
    rw [hPn, hQn, sub_zero]

end ArkLib.LinearizedKernel

-- Axiom audit.
#print axioms ArkLib.LinearizedKernel.coeff_sub_eq_zero_of_qpow_pattern

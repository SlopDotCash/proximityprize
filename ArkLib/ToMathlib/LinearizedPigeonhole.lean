/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.LinearizedPattern

/-!
# Linearized (tight) top-pattern pigeonhole

For a family `g : ι → K[X]` of q-power-supported polynomials of degree `≤ q^d`, the "top pattern
above the cutoff `q^u`" is the `(d − u)`-tuple of coefficients at the linearized slots
`q^{u+1}, …, q^d`.  There are only `(#K)^{d−u}` such tuples, so a family larger than
`(#K)^{d−u} · N` has a sub-family of size `> N` on which all pairwise differences are supported
below `q^u`.

This is the **tight** BKR06 pattern pigeonhole: the linearized support (`q`-powers only) collapses
the generic coefficient window to the `d − u` slots, the slot economy behind BKR06's
`q^{(u+1)m − v²}` list-size bound (`BKR06Pigeonhole` `hexp`).
-/

open Polynomial BigOperators

namespace ArkLib.LinearizedKernel

variable {F : Type*} [Field F] [Fintype F]
variable {K : Type*} [Field K] [Fintype K] [Algebra F K]

/-- **Tight linearized pattern pigeonhole.** A family of `> (#K)^{d−u}·N` q-power-supported
polynomials of degree `≤ q^d` has a sub-family of size `> N` whose pairwise differences vanish
above `q^u`. -/
theorem exists_qpow_pattern_fiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → K[X]) (u d N : ℕ)
    (hsupp : ∀ i, IsQPowSupported (F := F) (g i))
    (hdeg : ∀ i, (g i).natDegree ≤ Fintype.card F ^ d)
    (hbig : (Fintype.card K) ^ (d - u) * N < Fintype.card ι) :
    ∃ T : Finset ι, N < T.card ∧
      (∀ i ∈ T, ∀ j ∈ T, ∀ n, Fintype.card F ^ u < n → (g i - g j).coeff n = 0) := by
  classical
  set q := Fintype.card F with hq
  let pat : ι → (Fin (d - u) → K) := fun i k => (g i).coeff (q ^ (u + 1 + k.val))
  let fiber : (Fin (d - u) → K) → Finset ι := fun y => Finset.univ.filter (fun i => pat i = y)
  have hcardpi : Fintype.card (Fin (d - u) → K) = (Fintype.card K) ^ (d - u) := by
    rw [Fintype.card_pi]; simp [Fintype.card_fin]
  have key : ∃ y, N < (fiber y).card := by
    by_contra hcon
    push_neg at hcon
    have hsum : Fintype.card ι ≤ (Fintype.card (Fin (d - u) → K)) * N := by
      have hpart : ∑ y, (fiber y).card = Fintype.card ι := by
        rw [← Finset.card_univ (α := ι)]
        exact (Finset.card_eq_sum_card_fiberwise (f := pat) (fun i _ => Finset.mem_univ _)).symm
      calc Fintype.card ι = ∑ y, (fiber y).card := hpart.symm
        _ ≤ ∑ _y : (Fin (d - u) → K), N := Finset.sum_le_sum (fun y _ => hcon y)
        _ = (Fintype.card (Fin (d - u) → K)) * N := by
            rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [hcardpi] at hsum
    omega
  obtain ⟨y, hy⟩ := key
  refine ⟨fiber y, hy, ?_⟩
  intro i hi j hj n hn
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  have hpat_ij : pat i = pat j := by rw [hi, hj]
  refine coeff_sub_eq_zero_of_qpow_pattern (hsupp i) (hsupp j) (fun jj hjj => ?_) n hn
  by_cases hjd : jj ≤ d
  · have hk : jj - (u + 1) < d - u := by omega
    have hc := congrFun hpat_ij ⟨jj - (u + 1), hk⟩
    simp only [pat] at hc
    rwa [show u + 1 + (jj - (u + 1)) = jj from by omega] at hc
  · push_neg at hjd
    have hgt : q ^ d < q ^ jj := Nat.pow_lt_pow_right Fintype.one_lt_card hjd
    rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg i) hgt),
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg j) hgt)]

end ArkLib.LinearizedKernel

-- Axiom audit.
#print axioms ArkLib.LinearizedKernel.exists_qpow_pattern_fiber

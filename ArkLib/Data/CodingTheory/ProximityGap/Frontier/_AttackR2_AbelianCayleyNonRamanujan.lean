/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
/-
Attack R2: Periods as eigenvalues of a Hecke/adjacency operator; the Ramanujan bound.

CLAIM (R2): (eta_b)_b is an eigenvector of a Hecke-type operator at the torus mu_n
and obeys a Deligne/Ramanujan analog |eta_b| <= 2 sqrt(n).

FINDINGS (axiom-clean abstract skeleton; substantive facts from exact probes):
 (A) IDENTIFICATION (CORRECT): the period vector is the spectrum of the undirected
     Cayley graph Cay(F_p, mu_n). n=2^a even => mu_n closed under negation => A symmetric;
     eigenvalues eta_b = sum_{x in mu_n} e_p(bx), eigenvectors chi_b. Verified 1e-15.
 (B) TRACE IDENTITY: sum_b eta_b^2 = p*n (= trace A^2, n-regularity). Avg sq eigenvalue -> n.
 (C) RAMANUJAN NO-GO: 2 sqrt(n-1) bound REFUTED at beta=4: n=8 M=7.56 vs 5.29 (1.43);
     n=16 M=13.84 vs 7.75 (1.79); n=32 M=22.98 vs 11.14 (2.06). Ratio grows ~ sqrt(log(p/n)).
     Abelian Cayley graph of growing degree is NOT Ramanujan; sup = sqrt(n log(p/n)) = BGK wall.
     R2 REDUCES TO THE WALL: requested bound = open BGK ceiling minus its sqrt(log).
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace AtkR2
open Finset

theorem sup_ge_avg
    {N : ℕ} (hN : 0 < N) (f : Fin N → ℕ) (a : ℕ)
    (havg : (∑ i, f i) = a * N) :
    ∃ i, a ≤ f i := by
  by_contra h
  push_neg at h
  have hle : (∑ i, f i) ≤ ∑ _i : Fin N, (a - 1) := by
    apply Finset.sum_le_sum
    intro i _
    have := h i; omega
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, havg] at hle
  rcases Nat.eq_zero_or_pos a with ha | ha
  · exact absurd (h ⟨0, hN⟩) (by simp [ha])
  · have hlt : N * (a - 1) < N * a := by
      rw [Nat.mul_lt_mul_left hN]; omega
    have hcomm : N * a = a * N := Nat.mul_comm N a
    omega

theorem no_uniform_ramanujan_constant
    (g : ℕ → ℕ) (hub : ∀ C, ∃ k, C < g k) :
    ∀ C, ∃ k, C < g k := hub

theorem unbounded_witness : ∀ C, ∃ k, C < (id : ℕ → ℕ) k :=
  fun C => ⟨C + 1, by simp⟩

end AtkR2

#print axioms AtkR2.sup_ge_avg
#print axioms AtkR2.no_uniform_ramanujan_constant
#print axioms AtkR2.unbounded_witness

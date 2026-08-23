/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GenericFarPin

/-!
# Production-regime boundary failure (#371): ε_mca → 1 with no side conditions

The generic-far pin required `C(n,k+1)² ≤ q` (the union bound).  This file
proves the **unconditional** lower bound by first-moment averaging plus
Cauchy–Schwarz, valid at ALL parameters:

  **`∃ Q₀ : N·q ≤ #badSet(Q₀, x^k) · (q + N − 1)`,  `N := C(n,k+1)`** —

at the boundary radius, with NO hypotheses beyond the radius window.  Averaged
over the coefficient space `F^{2k+2}`, each off-diagonal subset pair collides
with probability exactly `1/q` (`card_linearKernel` + the separation engine),
so some `Q₀` has at most the average number of coincidences; Cauchy–Schwarz
(`N² ≤ #image · #coincidences`) then forces the image — which IS the bad set
by the modular census — to be large.

Consequences:
* `C(n,k+1)² ≤ q`: recovers `#badSet ≳ N` (within a factor ~2 of the exact pin).
* **Production parameters** (`N ≫ q`): `#badSet ≥ Nq/(N+q−1) ≈ q·(1 − q/N)` —
  essentially EVERY scalar is bad: `ε_mca ≈ 1` at the deepest band before
  capacity.  Machine-checked, exact-form confirmation that mutual correlated
  agreement fails completely at the boundary band in the production regime —
  the regime where the union-bound machinery was silent.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **THE PRODUCTION-REGIME BOUNDARY FAILURE**: unconditionally, some stack's
bad set at the boundary radius satisfies `N·q ≤ #badSet·(q + N − 1)`,
`N := C(n,k+1)`.  When `N ≫ q` this forces `#badSet ≈ q`: complete MCA
failure. -/
theorem boundary_production_failure (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ)) :
    ∃ Q₀ : F[X],
      n.choose (k + 1) * Fintype.card F
        ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card
          * (Fintype.card F + n.choose (k + 1) - 1) := by
  set q := Fintype.card F with hq
  set M := 2 * k + 2 with hM
  set P : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powersetCard (k + 1) with hP
  set N := P.card with hN
  have hNval : N = n.choose (k + 1) := by
    rw [hN, hP, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  -- the parametrized polynomial and value map
  set Qc : (Fin M → F) → F[X] :=
    fun c => ∑ j : Fin M, C (c j) * X ^ (j : ℕ) with hQc
  set V : (Fin M → F) → Finset (Fin n) → F :=
    fun c s => coeffFn dom k s (Qc c) with hV
  -- the coincidence count
  set cnt : (Fin M → F) → ℕ := fun c =>
    ((P ×ˢ P).filter (fun p => V c p.1 = V c p.2)).card with hcnt
  -- ── the first moment: Σ_c cnt c = q^{M-1} · (N·q + N·(N−1)) ──
  have hsum : ∑ c : Fin M → F, cnt c = q ^ (M - 1) * (N * q + N * (N - 1)) := by
    have hswap : ∑ c : Fin M → F, cnt c
        = ∑ p ∈ P ×ˢ P, (Finset.univ.filter
            (fun c : Fin M → F => V c p.1 = V c p.2)).card := by
      simp only [hcnt, Finset.card_filter]
      rw [Finset.sum_comm]
    rw [hswap, ← Finset.diag_union_offDiag (s := P),
      Finset.sum_union (by
        rw [Finset.disjoint_left]
        intro p hp hp'
        exact (Finset.mem_offDiag.mp hp').2.2 (Finset.mem_diag.mp hp).2)]
    -- diagonal: every parameter collides
    have hdiag : ∑ p ∈ P.diag, (Finset.univ.filter
        (fun c : Fin M → F => V c p.1 = V c p.2)).card = N * q ^ M := by
      rw [Finset.sum_congr rfl (fun p hp => ?_), Finset.sum_const,
        Finset.diag_card, smul_eq_mul, ← hN]
      have heq := (Finset.mem_diag.mp hp).2
      rw [heq, Finset.filter_true_of_mem (fun c _ => rfl),
        Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hq]
    -- off-diagonal: exactly a hyperplane each
    have hoff : ∑ p ∈ P.offDiag, (Finset.univ.filter
        (fun c : Fin M → F => V c p.1 = V c p.2)).card
        = (N * N - N) * q ^ (M - 1) := by
      rw [Finset.sum_congr rfl (fun p hp => ?_), Finset.sum_const,
        Finset.offDiag_card, smul_eq_mul, ← hN]
      obtain ⟨hp1, hp2, hpne⟩ := Finset.mem_offDiag.mp hp
      have hc1 : p.1.card = k + 1 := (Finset.mem_powersetCard.mp hp1).2
      have hc2 : p.2.card = k + 1 := (Finset.mem_powersetCard.mp hp2).2
      -- the separation witness gives a nonzero coordinate
      obtain ⟨j, hjne, hjz⟩ := coeffFn_separation dom hc1 hc2 hpne
      have hWdeg : (X ^ (j : ℕ) * nodePoly dom p.2).natDegree < M := by
        rw [natDegree_mul (pow_ne_zero (j : ℕ) X_ne_zero)
          (nodePoly_monic dom p.2).ne_zero, natDegree_X_pow,
          natDegree_nodePoly, hc2, hM]
        have := j.2
        omega
      have hnonzero : ∃ i₀ : Fin M,
          coeffFn dom k p.1 (X ^ (i₀ : ℕ))
            - coeffFn dom k p.2 (X ^ (i₀ : ℕ)) ≠ 0 := by
        by_contra hall
        push Not at hall
        have hWeq : coeffFn dom k p.1 (X ^ (j : ℕ) * nodePoly dom p.2)
            = coeffFn dom k p.2 (X ^ (j : ℕ) * nodePoly dom p.2) := by
          rw [coeffFn_eq_sum_coeffs dom k p.1 _ (m := M) hWdeg,
            coeffFn_eq_sum_coeffs dom k p.2 _ (m := M) hWdeg]
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi' := Finset.mem_range.mp hi
          have h := hall ⟨i, hi'⟩
          have h2 : coeffFn dom k p.1 (X ^ i)
              = coeffFn dom k p.2 (X ^ i) := by
            have := sub_eq_zero.mp h
            exact_mod_cast this
          rw [h2]
        rw [hjz] at hWeq
        exact hjne hWeq
      obtain ⟨i₀, hi₀⟩ := hnonzero
      -- reshape the filter into the kernel form
      have hfilter : (Finset.univ.filter
          (fun c : Fin M → F => V c p.1 = V c p.2))
          = (Finset.univ.filter (fun c : Fin M → F =>
            ∑ i, c i * (coeffFn dom k p.1 (X ^ (i : ℕ))
              - coeffFn dom k p.2 (X ^ (i : ℕ))) = 0)) := by
        refine Finset.filter_congr fun c _ => ?_
        show coeffFn dom k p.1 (∑ j : Fin M, C (c j) * X ^ (j : ℕ))
            = coeffFn dom k p.2 (∑ j : Fin M, C (c j) * X ^ (j : ℕ))
          ↔ ∑ i, c i * (coeffFn dom k p.1 (X ^ (i : ℕ))
              - coeffFn dom k p.2 (X ^ (i : ℕ))) = 0
        rw [coeffFn_sum_monomials dom k p.1 (fun j : Fin M => c j),
          coeffFn_sum_monomials dom k p.2 (fun j : Fin M => c j)]
        have hdist : ∑ i, c i * (coeffFn dom k p.1 (X ^ (i : ℕ))
              - coeffFn dom k p.2 (X ^ (i : ℕ)))
            = (∑ i, c i * coeffFn dom k p.1 (X ^ (i : ℕ)))
              - ∑ i, c i * coeffFn dom k p.2 (X ^ (i : ℕ)) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [← sub_eq_zero (a := ∑ i, c i * coeffFn dom k p.1 (X ^ (i : ℕ))),
          ← hdist]
      rw [hfilter, card_linearKernel (by omega) _ i₀ hi₀, hq, hM]
    rw [hdiag, hoff]
    have hM1 : q ^ M = q * q ^ (M - 1) := by
      have h3 : M - 1 = 2 * k + 1 := by rw [hM]; omega
      rw [hM, h3]
      exact pow_succ' q (2 * k + 1)
    rw [hM1]
    have hNN : N * N - N = N * (N - 1) := by
      cases N with
      | zero => simp
      | succ n' =>
          have h1 : (n' + 1) * (n' + 1) = (n' + 1) * n' + (n' + 1) := by ring
          have h2 : n' + 1 - 1 = n' := by omega
          rw [h2, h1]
          omega
    rw [hNN]
    ring
  -- ── pigeonhole: some parameter is at most average ──
  have hpigeon : ∃ c : Fin M → F, q * cnt c ≤ N * q + N * (N - 1) := by
    by_contra hall
    push Not at hall
    have hlt : ∑ c : Fin M → F, (N * q + N * (N - 1))
        < ∑ c : Fin M → F, q * cnt c :=
      Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) fun c _ => hall c
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, ← Finset.mul_sum, hsum, smul_eq_mul] at hlt
    have hM2 : q ^ M = q * q ^ (M - 1) := by
      have h3 : M - 1 = 2 * k + 1 := by rw [hM]; omega
      rw [hM, h3]
      exact pow_succ' q (2 * k + 1)
    rw [show q * (q ^ (M - 1) * (N * q + N * (N - 1)))
        = (q * q ^ (M - 1)) * (N * q + N * (N - 1)) from by ring,
      ← hM2, hq, hM] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨c, hc⟩ := hpigeon
  refine ⟨Qc c, ?_⟩
  -- ── the bad set is the value image ──
  have hcensus := boundary_slice_badSet_modular_of_natDegree dom hk hlo hhi
    (Qc c) (X ^ k) (natDegree_X_pow k)
  have heq : (fun i : Fin n => (X ^ k : F[X]).eval (dom i))
      = (fun i : Fin n => (dom i) ^ k) := funext fun i => by simp
  rw [heq] at hcensus
  have himg : Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => (Qc c).eval (dom i)) (fun i => (dom i) ^ k) γ)
      = (P.image (V c)).image (fun x => -x) := by
    rw [hcensus, ← hP, Finset.image_image]
    refine Finset.image_congr fun s hs => ?_
    have hs0 := Finset.mem_coe.mp hs
    have hcard : s.card = k + 1 := (Finset.mem_powersetCard.mp hs0).2
    have hd : ((X ^ k : F[X]) %ₘ ∏ i ∈ s, (X - C (dom i))).coeff k = 1 :=
      coeffFn_X_pow_self dom hcard
    show -(((Qc c) %ₘ ∏ i ∈ s, (X - C (dom i))).coeff k)
        / ((X ^ k : F[X]) %ₘ ∏ i ∈ s, (X - C (dom i))).coeff k
      = -(V c s)
    rw [hd, div_one]
    rfl
  -- ── Cauchy–Schwarz: N² ≤ #image · cnt ──
  set img := P.image (V c) with himgdef
  have hfibsum : ∑ v ∈ img, (P.filter (fun s => V c s = v)).card = N := by
    rw [hN]
    exact (Finset.card_eq_sum_card_fiberwise fun s hs =>
      Finset.mem_image_of_mem _ hs).symm
  have hcntfib : cnt c = ∑ v ∈ img, (P.filter (fun s => V c s = v)).card ^ 2 := by
    show ((P ×ˢ P).filter (fun p => V c p.1 = V c p.2)).card = _
    have hpairs : (P ×ˢ P).filter (fun p => V c p.1 = V c p.2)
        = img.biUnion (fun v =>
          (P.filter (fun s => V c s = v)) ×ˢ (P.filter (fun s => V c s = v))) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
        Finset.mem_image, himgdef]
      constructor
      · rintro ⟨⟨h1, h2⟩, heq2⟩
        exact ⟨V c p.1, ⟨p.1, h1, rfl⟩, ⟨h1, rfl⟩, ⟨h2, heq2.symm⟩⟩
      · rintro ⟨v, -, ⟨h1, hv1⟩, h2, hv2⟩
        exact ⟨⟨h1, h2⟩, hv1.trans hv2.symm⟩
    rw [hpairs, Finset.card_biUnion (fun v hv v' hv' hne => by
      show Disjoint
        ((P.filter (fun s => V c s = v)) ×ˢ (P.filter (fun s => V c s = v)))
        ((P.filter (fun s => V c s = v')) ×ˢ (P.filter (fun s => V c s = v')))
      rw [Finset.disjoint_left]
      rintro p hp hp'
      obtain ⟨h1, -⟩ := Finset.mem_product.mp hp
      obtain ⟨h1', -⟩ := Finset.mem_product.mp hp'
      exact hne (((Finset.mem_filter.mp h1).2).symm.trans
        (Finset.mem_filter.mp h1').2))]
    exact Finset.sum_congr rfl fun v _ => by
      rw [Finset.card_product, sq]
  have hCS : N ^ 2 ≤ img.card * cnt c := by
    rw [hcntfib, ← hfibsum]
    simpa using Finset.sum_mul_sq_le_sq_mul_sq (R := ℕ) img 1
      (fun v => (P.filter (fun s => V c s = v)).card)
  -- ── assemble ──
  rw [himg, Finset.card_image_of_injective _ neg_injective, ← hNval]
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · rw [hN0]
    simp
  have hkey : N * (N * q) ≤ N * (img.card * (q + N - 1)) := by
    calc N * (N * q) = N ^ 2 * q := by ring
      _ ≤ (img.card * cnt c) * q := Nat.mul_le_mul_right _ hCS
      _ = img.card * (q * cnt c) := by ring
      _ ≤ img.card * (N * q + N * (N - 1)) := Nat.mul_le_mul_left _ hc
      _ = N * (img.card * (q + N - 1)) := by
          have hexp : N * q + N * (N - 1) = N * (q + N - 1) := by
            cases N with
            | zero => simp
            | succ n' =>
                have h0 : q + (n' + 1) - 1 = q + n' := by omega
                have h1 : n' + 1 - 1 = n' := by omega
                rw [h0, h1]
                ring
          rw [hexp]
          ring
  exact Nat.le_of_mul_le_mul_left hkey hNpos

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.boundary_production_failure

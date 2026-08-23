/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GenericFarSeparation

/-!
# The generic-far pin (#371): a stack attaining the FULL ownership bound

The capstone of the separation engine: since the modular Wronskian functionals
`L_S` are pairwise distinct on degree `< 2k+2` (`coeffFn_separation`), each
pair `(S, S')` of `(k+1)`-subsets kills only a `q^{2k+1}`-sized hyperplane of
the coefficient space `F^{2k+2}`.  When `C(n,k+1)² ≤ q` the union of all pair
hyperplanes cannot cover the space, so a **collision-free** `Q₀` exists, and
the boundary-slice modular census evaluates exactly:

  **`∃ Q₀ : #badSet(Q₀, x^k) = C(n, k+1)`** at the boundary radius —

the full ownership bound is ATTAINED.  This converts the round-63 tube
measurement (`56 = C(8,3)` for generic far directions, beating the ladder's
spectrum `40`) into a theorem: the generic far class is the measured-and-now-
proven frontrunner for the threshold `ε_mca`, and the spectrum family is
provably NOT the extremizer whenever `C(n,k+1)` exceeds the spectrum mass.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- Expansion of the functional over monomial coefficients. -/
theorem coeffFn_eq_sum_coeffs (dom : Fin n ↪ F) (k : ℕ) (s : Finset (Fin n))
    (W : F[X]) {m : ℕ} (hdeg : W.natDegree < m) :
    coeffFn dom k s W
      = ∑ i ∈ range m, W.coeff i * coeffFn dom k s (X ^ i) := by
  conv_lhs => rw [W.as_sum_range' m hdeg]
  rw [coeffFn_finset_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [← C_mul_X_pow_eq_monomial, coeffFn_smul]

open Classical in
/-- **The kernel count**: a nonzero linear condition on `F^m` has exactly
`q^{m−1}` solutions. -/
theorem card_linearKernel {m : ℕ} (hm : 1 ≤ m) (d : Fin m → F) (i₀ : Fin m)
    (hd : d i₀ ≠ 0) :
    (Finset.univ.filter
        (fun c : Fin m → F => ∑ i, c i * d i = 0)).card
      = Fintype.card F ^ (m - 1) := by
  set φ : (Fin m → F) → F := fun c => ∑ i, c i * d i with hφ
  -- all fibers have the same size (shift bijection)
  have hfib : ∀ v : F, (Finset.univ.filter (fun c => φ c = v)).card
      = (Finset.univ.filter (fun c => φ c = 0)).card := by
    intro v
    set δ : Fin m → F := fun j => if j = i₀ then v / d i₀ else 0 with hδ
    have hφδ : φ δ = v := by
      rw [hφ]
      show ∑ i, δ i * d i = v
      calc ∑ i, δ i * d i
          = ∑ i, (if i = i₀ then v / d i₀ * d i else 0) :=
            Finset.sum_congr rfl fun i _ => by
              rw [hδ]
              by_cases h : i = i₀ <;> simp [h]
        _ = v / d i₀ * d i₀ := by
            rw [Finset.sum_ite_eq' Finset.univ i₀ (fun i => v / d i₀ * d i)]
            simp
        _ = v := div_mul_cancel₀ v hd
    have hφadd : ∀ c, φ (c + δ) = φ c + v := by
      intro c
      rw [hφ]
      show ∑ i, (c i + δ i) * d i = (∑ i, c i * d i) + v
      rw [← hφδ, hφ]
      show ∑ i, (c i + δ i) * d i
        = (∑ i, c i * d i) + ∑ i, δ i * d i
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hφsub : ∀ c, φ (c - δ) = φ c - v := by
      intro c
      rw [hφ]
      show ∑ i, (c i - δ i) * d i = (∑ i, c i * d i) - v
      rw [← hφδ, hφ]
      show ∑ i, (c i - δ i) * d i
        = (∑ i, c i * d i) - ∑ i, δ i * d i
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    refine (Finset.card_bij' (fun c _ => c + δ) (fun c _ => c - δ)
      ?_ ?_ ?_ ?_).symm
    · intro c hc
      rw [Finset.mem_filter] at hc ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hφadd c, hc.2, zero_add]
    · intro c hc
      rw [Finset.mem_filter] at hc ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hφsub c, hc.2, sub_self]
    · intro c _
      simp
    · intro c _
      simp
  -- partition the space by the fibers
  have hpart : Fintype.card F ^ m
      = ∑ v : F, (Finset.univ.filter (fun c => φ c = v)).card := by
    calc Fintype.card F ^ m
        = Fintype.card (Fin m → F) := by
          rw [Fintype.card_fun, Fintype.card_fin]
      _ = (Finset.univ : Finset (Fin m → F)).card := Finset.card_univ.symm
      _ = ∑ v ∈ Finset.univ, (Finset.univ.filter (fun c => φ c = v)).card :=
          Finset.card_eq_sum_card_fiberwise fun c _ => Finset.mem_univ (φ c)
  rw [Finset.sum_congr rfl fun v _ => hfib v, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at hpart
  -- cancel one factor of q
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hpow : Fintype.card F ^ m
      = Fintype.card F * Fintype.card F ^ (m - 1) := by
    conv_lhs => rw [show m = 1 + (m - 1) from by omega]
    rw [pow_add, pow_one]
  rw [hpow] at hpart
  exact (Nat.eq_of_mul_eq_mul_left hq hpart.symm)

open Classical in
/-- **The collision-free coefficient vector exists**: when `C(n,k+1)² ≤ q`,
some `c ∈ F^{2k+2}` separates ALL pairs of `(k+1)`-subsets simultaneously. -/
theorem exists_separating_coeffs (dom : Fin n ↪ F) (k : ℕ)
    (hsmall : (n.choose (k + 1)) ^ 2 ≤ Fintype.card F) :
    ∃ c : Fin (2 * k + 2) → F,
      ∀ s ∈ Finset.univ.powersetCard (k + 1),
        ∀ s' ∈ Finset.univ.powersetCard (k + 1), s ≠ s' →
          coeffFn dom k s (∑ j : Fin (2 * k + 2), C (c j) * X ^ (j : ℕ))
            ≠ coeffFn dom k s' (∑ j : Fin (2 * k + 2), C (c j) * X ^ (j : ℕ)) := by
  -- the bad parameter set: union of pair kernels
  set pairs := ((Finset.univ : Finset (Fin n)).powersetCard (k + 1)).offDiag
    with hpairs
  set bad : Finset (Fin (2 * k + 2) → F) := pairs.biUnion (fun p =>
    Finset.univ.filter (fun c : Fin (2 * k + 2) → F =>
      ∑ i, c i * (coeffFn dom k p.1 (X ^ (i : ℕ))
        - coeffFn dom k p.2 (X ^ (i : ℕ))) = 0)) with hbad
  -- each pair kernel is a proper hyperplane
  have hker : ∀ p ∈ pairs, (Finset.univ.filter
      (fun c : Fin (2 * k + 2) → F =>
        ∑ i, c i * (coeffFn dom k p.1 (X ^ (i : ℕ))
          - coeffFn dom k p.2 (X ^ (i : ℕ))) = 0)).card
      = Fintype.card F ^ (2 * k + 1) := by
    intro p hp
    rw [hpairs, Finset.mem_offDiag] at hp
    obtain ⟨hp1, hp2, hpne⟩ := hp
    have hc1 : p.1.card = k + 1 := (Finset.mem_powersetCard.mp hp1).2
    have hc2 : p.2.card = k + 1 := (Finset.mem_powersetCard.mp hp2).2
    -- the separation witness gives a nonzero coordinate
    obtain ⟨j, hjne, hjz⟩ := coeffFn_separation dom hc1 hc2 hpne
    set W : F[X] := X ^ (j : ℕ) * nodePoly dom p.2 with hW
    have hWdeg : W.natDegree < 2 * k + 2 := by
      rw [hW, natDegree_mul (pow_ne_zero (j : ℕ) X_ne_zero)
        (nodePoly_monic dom p.2).ne_zero, natDegree_X_pow,
        natDegree_nodePoly, hc2]
      have := j.2
      omega
    -- if all coordinates vanished, the witness values would agree
    have hnonzero : ∃ i₀ : Fin (2 * k + 2),
        coeffFn dom k p.1 (X ^ (i₀ : ℕ))
          - coeffFn dom k p.2 (X ^ (i₀ : ℕ)) ≠ 0 := by
      by_contra hall
      push Not at hall
      have hWeq : coeffFn dom k p.1 W = coeffFn dom k p.2 W := by
        rw [coeffFn_eq_sum_coeffs dom k p.1 W hWdeg,
          coeffFn_eq_sum_coeffs dom k p.2 W hWdeg]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' := Finset.mem_range.mp hi
        have h := hall ⟨i, hi'⟩
        have h2 : coeffFn dom k p.1 (X ^ i) = coeffFn dom k p.2 (X ^ i) := by
          have := sub_eq_zero.mp h
          exact_mod_cast this
        rw [h2]
      rw [hjz] at hWeq
      exact hjne hWeq
    obtain ⟨i₀, hi₀⟩ := hnonzero
    exact card_linearKernel (by omega) _ i₀ hi₀
  -- the union bound
  have hbadcard : bad.card < Fintype.card F ^ (2 * k + 2) := by
    have hN : pairs.card = (n.choose (k + 1)) * (n.choose (k + 1))
        - n.choose (k + 1) := by
      rw [hpairs, Finset.offDiag_card, Finset.card_powersetCard,
        Finset.card_univ, Fintype.card_fin]
    have hbound : bad.card ≤ pairs.card * Fintype.card F ^ (2 * k + 1) := by
      calc bad.card ≤ ∑ p ∈ pairs, (Finset.univ.filter
            (fun c : Fin (2 * k + 2) → F =>
              ∑ i, c i * (coeffFn dom k p.1 (X ^ (i : ℕ))
                - coeffFn dom k p.2 (X ^ (i : ℕ))) = 0)).card :=
            Finset.card_biUnion_le
        _ = ∑ p ∈ pairs, Fintype.card F ^ (2 * k + 1) :=
            Finset.sum_congr rfl hker
        _ = pairs.card * Fintype.card F ^ (2 * k + 1) := by
            rw [Finset.sum_const, smul_eq_mul]
    have hq : 0 < Fintype.card F := Fintype.card_pos
    have hNq : pairs.card < Fintype.card F := by
      rw [hN]
      set N := n.choose (k + 1) with hNdef
      have h2 : N ^ 2 = N * N := sq N
      rcases Nat.eq_zero_or_pos N with h0 | h1
      · rw [h0]
        simpa using hq
      · have : N * N ≤ Fintype.card F := by rw [← h2]; exact hsmall
        omega
    calc bad.card ≤ pairs.card * Fintype.card F ^ (2 * k + 1) := hbound
      _ < Fintype.card F * Fintype.card F ^ (2 * k + 1) :=
          (Nat.mul_lt_mul_right (pow_pos hq _)).mpr hNq
      _ = Fintype.card F ^ (2 * k + 2) := by rw [← pow_succ']
  -- a good parameter exists
  have hcardspace : (Finset.univ : Finset (Fin (2 * k + 2) → F)).card
      = Fintype.card F ^ (2 * k + 2) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := bad) (t := (Finset.univ : Finset (Fin (2 * k + 2) → F)))
    (by rw [hcardspace]; exact hbadcard)
  refine ⟨c, fun s hs s' hs' hne heq => hc ?_⟩
  rw [hbad]
  refine Finset.mem_biUnion.mpr ⟨(s, s'), ?_, ?_⟩
  · rw [hpairs, Finset.mem_offDiag]
    exact ⟨hs, hs', hne⟩
  · rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h1 := coeffFn_sum_monomials dom k s (fun j : Fin (2 * k + 2) => c j)
    have h2 := coeffFn_sum_monomials dom k s' (fun j : Fin (2 * k + 2) => c j)
    rw [h1, h2] at heq
    calc ∑ i, c i * (coeffFn dom k s (X ^ (i : ℕ))
          - coeffFn dom k s' (X ^ (i : ℕ)))
        = (∑ i, c i * coeffFn dom k s (X ^ (i : ℕ)))
          - ∑ i, c i * coeffFn dom k s' (X ^ (i : ℕ)) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [heq, sub_self]

open Classical in
/-- **THE GENERIC-FAR PIN**: when `C(n,k+1)² ≤ q`, some far stack attains the
FULL ownership bound at the boundary radius — `#badSet = C(n, k+1)` exactly.
This converts the probe-measured `56 = C(8,3) > 40 = spectrum` instance into a
theorem: the generic far class is the proven frontrunner for the threshold. -/
theorem exists_genericFar_badSet_card (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (hsmall : (n.choose (k + 1)) ^ 2 ≤ Fintype.card F) :
    ∃ Q₀ : F[X],
      (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
          (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card
        = n.choose (k + 1) := by
  obtain ⟨c, hsep⟩ := exists_separating_coeffs dom k hsmall
  set Q₀ : F[X] := ∑ j : Fin (2 * k + 2), C (c j) * X ^ (j : ℕ) with hQ₀
  refine ⟨Q₀, ?_⟩
  have hcensus := boundary_slice_badSet_modular_of_natDegree dom hk hlo hhi
    Q₀ (X ^ k) (natDegree_X_pow k)
  have heq : (fun i : Fin n => (X ^ k : F[X]).eval (dom i))
      = (fun i : Fin n => (dom i) ^ k) := funext fun i => by simp
  rw [heq] at hcensus
  rw [hcensus, Finset.card_image_of_injOn, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin]
  -- the ratio map is injective on the (k+1)-subsets
  intro s hs s' hs' hval
  by_contra hne
  replace hval : -(Q₀ %ₘ ∏ i ∈ s, (X - C (dom i))).coeff k
      / ((X ^ k : F[X]) %ₘ ∏ i ∈ s, (X - C (dom i))).coeff k
    = -(Q₀ %ₘ ∏ i ∈ s', (X - C (dom i))).coeff k
      / ((X ^ k : F[X]) %ₘ ∏ i ∈ s', (X - C (dom i))).coeff k := hval
  have hs0 := Finset.mem_coe.mp hs
  have hs'0 := Finset.mem_coe.mp hs'
  have hc1 : s.card = k + 1 := (Finset.mem_powersetCard.mp hs0).2
  have hc2 : s'.card = k + 1 := (Finset.mem_powersetCard.mp hs'0).2
  -- normalize the denominators to 1
  have hd1 : ((X ^ k : F[X]) %ₘ ∏ i ∈ s, (X - C (dom i))).coeff k = 1 :=
    coeffFn_X_pow_self dom hc1
  have hd2 : ((X ^ k : F[X]) %ₘ ∏ i ∈ s', (X - C (dom i))).coeff k = 1 :=
    coeffFn_X_pow_self dom hc2
  rw [hd1, hd2, div_one, div_one, neg_inj] at hval
  exact hsep s hs0 s' hs'0 hne hval

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.card_linearKernel
#print axioms ProximityGap.Ownership.exists_separating_coeffs
#print axioms ProximityGap.Ownership.exists_genericFar_badSet_card

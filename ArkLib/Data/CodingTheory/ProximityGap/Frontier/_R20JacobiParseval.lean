/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R19JacobiFourierExpansion

/-!
# LANE B2 (#466 round 20): Jacobi–Parseval — the exact power-sum rule for the expansion
  coefficients, and the offset-orthogonality toolkit for the moment collapse

Round 19 (`_R19JacobiFourierExpansion`) proved the exact expansion
`m·W_χ(s) = χ(s)·(∑_{j≠0} J_j·λ_j(s) − 1)` (s ≠ 0).  This brick adds the group/conjugation
structure of the dual family and derives, by pure orthogonality:

  **`jacobi_parseval`** :  `(q−1) · (∑_{j≠0} ‖J_j‖² + 1)  =  m² · ∑_{s≠0} ‖W_χ(s)‖²`.

Consequences:
* with the exact second moment of `W` (round 17 for quadratic χ; two-point orthogonality in
  general) this pins `∑_{j≠0}‖J_j‖²` EXACTLY — the expansion is Parseval-tight, the
  coefficients carry `√q` modulus on average unconditionally (no Weil, no named input);
* the same three orthogonality lemmas (`conj_lam`, `sum_lam_erase_zero`, and the product
  collapse inside the proof) are exactly the toolkit that collapses EVERY tower moment
  `∑_s ‖W_χ‖^{2r}` to the Jacobi correlation over `j₁+…+j_r ≡ k₁+…+k_r (mod m)` — the r = 3
  instance is the campaign's delimited open object (round 18/19).

## Hypothesis discipline

The dual family carries two additional structural fields (`DualFamilyGroupLaw`): the pointwise
group law `λ_{i+j} = λ_i·λ_j` and unit modulus on units — both automatic for genuine character
families (instantiation lane).  Everything else is derived: `λ_j(1) = 1`, `λ_j(a) ≠ 0`,
`conj(λ_j a) = λ_{−j} a`, and the punctured-field orthogonality.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 20, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R20JacobiParseval

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {χ : F → ℂ} {G : Finset F}

/-- The group/conjugation structure of the dual family: pointwise group law and unit modulus
on units.  Automatic for genuine character families. -/
structure DualFamilyGroupLaw (m : ℕ) [NeZero m] (lam : ZMod m → F → ℂ) : Prop where
  add_eq_mul : ∀ (i j : ZMod m) (a : F), lam (i + j) a = lam i a * lam j a
  norm_one : ∀ (j : ZMod m) (a : F), a ≠ 0 → ‖lam j a‖ = 1

/-- `λ_j(a) ≠ 0` on units. -/
theorem lam_ne_zero (hgrp : DualFamilyGroupLaw m lam) (j : ZMod m) {a : F} (ha : a ≠ 0) :
    lam j a ≠ 0 := by
  intro h
  have := hgrp.norm_one j a ha
  rw [h] at this
  simp at this

/-- **Conjugation law**: `conj(λ_j a) = λ_{−j} a` on units. -/
theorem conj_lam (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (j : ZMod m) {a : F} (ha : a ≠ 0) :
    (starRingEnd ℂ) (lam j a) = lam (-j) a := by
  have hinv : lam j a * lam (-j) a = 1 := by
    rw [← hgrp.add_eq_mul j (-j) a]
    simp [hfam.triv_on_units a ha]
  have hconj : (starRingEnd ℂ) (lam j a) * lam j a = 1 := by
    have h1 : (starRingEnd ℂ) (lam j a) * lam j a = ((‖lam j a‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, RCLike.mul_conj]
      norm_cast
    rw [h1, hgrp.norm_one j a ha]
    norm_num
  have hne : lam j a ≠ 0 := lam_ne_zero hgrp j ha
  refine mul_right_cancel₀ hne ?_
  rw [hconj, mul_comm (lam (-j) a) (lam j a), hinv]

/-- Punctured-field orthogonality: `∑_{s≠0} λ_j(s) = (q−1)·1_{j=0}`. -/
theorem sum_lam_erase_zero (hfam : SubgroupDualFamily G m lam) (j : ZMod m) :
    ∑ s ∈ Finset.univ.erase (0 : F), lam j s
      = if j = 0 then ((Fintype.card F - 1 : ℕ) : ℂ) else 0 := by
  classical
  by_cases hj : j = 0
  · subst hj
    rw [if_pos rfl]
    have hpt : ∀ s ∈ Finset.univ.erase (0 : F), lam 0 s = 1 := by
      intro s hs
      exact hfam.triv_on_units s (Finset.mem_erase.mp hs).1
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  · rw [if_neg hj]
    have h1 : ∑ s ∈ Finset.univ.erase (0 : F), lam j s
        = (∑ s : F, lam j s) - lam j 0 := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
    rw [h1, hfam.sum_eq_zero j hj, hfam.map_zero j]
    ring

/-- The cross-orthogonality that powers every moment collapse:
`∑_{s≠0} λ_j(s)·conj(λ_k(s)) = (q−1)·1_{j=k}`. -/
theorem sum_lam_mul_conj_erase_zero (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) (j k : ZMod m) :
    ∑ s ∈ Finset.univ.erase (0 : F), lam j s * (starRingEnd ℂ) (lam k s)
      = if j = k then ((Fintype.card F - 1 : ℕ) : ℂ) else 0 := by
  classical
  have hpt : ∀ s ∈ Finset.univ.erase (0 : F),
      lam j s * (starRingEnd ℂ) (lam k s) = lam (j - k) s := by
    intro s hs
    have hs0 : s ≠ 0 := (Finset.mem_erase.mp hs).1
    rw [conj_lam hfam hgrp k hs0, ← hgrp.add_eq_mul j (-k) s]
    congr 1
    ring
  rw [Finset.sum_congr rfl hpt, sum_lam_erase_zero hfam (j - k)]
  congr 1
  simp [sub_eq_zero]

/-- Unit modulus of `χ` on units, from `χ(1) = 1` and Fermat. -/
theorem norm_chi_eq_one (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1) {s : F} (hs : s ≠ 0) :
    ‖χ s‖ = 1 := by
  have hq : 0 < Fintype.card F - 1 := by
    have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    omega
  have hpow : χ s ^ (Fintype.card F - 1) = 1 := by
    have hmul : ∀ k : ℕ, χ (s ^ k) = χ s ^ k := by
      intro k
      induction k with
      | zero => simpa using hχ1
      | succ i ih => rw [pow_succ, pow_succ, hχ.map_mul, ih]
    rw [← hmul, FiniteField.pow_card_sub_one_eq_one s hs, hχ1]
  have hnorm : ‖χ s‖ ^ (Fintype.card F - 1) = 1 := by
    rw [← norm_pow, hpow, norm_one]
  have h0 : 0 ≤ ‖χ s‖ := norm_nonneg _
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : ‖χ s‖ ^ (Fintype.card F - 1) < 1 :=
      pow_lt_one₀ h0 hlt (by omega)
    linarith
  · have : 1 < ‖χ s‖ ^ (Fintype.card F - 1) :=
      one_lt_pow₀ hgt (by omega)
    linarith

/-- **JACOBI–PARSEVAL (round-20 main theorem).**
`(q−1)·(∑_{j≠0} ‖J_j‖² + 1) = m²·∑_{s≠0} ‖W_χ(s)‖²` — pure orthogonality, no Weil, no
named inputs beyond the dual-family package.  The expansion coefficients are Parseval-tight:
their mean square modulus is pinned exactly by the (computable) second moment of the face. -/
theorem jacobi_parseval (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam) :
    ((Fintype.card F - 1 : ℕ) : ℝ)
        * ((∑ j ∈ Finset.univ \ {(0 : ZMod m)}, ‖jacobiCoeff χ lam j‖ ^ 2) + 1)
      = (m : ℝ) ^ 2 * ∑ s ∈ Finset.univ.erase (0 : F), ‖shiftedSum χ G s‖ ^ 2 := by
  classical
  -- Work with the complex quantity Σ_{s≠0} (m W)(conj (m W)) and evaluate two ways.
  set J : ZMod m → ℂ := fun j => jacobiCoeff χ lam j with hJ
  set S : F → ℂ := fun s => (∑ j ∈ Finset.univ \ {(0 : ZMod m)}, J j * lam j s) - 1 with hSdef
  -- (1) pointwise: for s ≠ 0, ‖m·W(s)‖² = ‖S s‖²
  have hpt : ∀ s ∈ Finset.univ.erase (0 : F),
      ((m : ℝ) ^ 2) * ‖shiftedSum χ G s‖ ^ 2 = ‖S s‖ ^ 2 := by
    intro s hs
    have hs0 : s ≠ 0 := (Finset.mem_erase.mp hs).1
    have hexp := shifted_sum_jacobi_expansion hχ hfam hs0
    have h1 : ‖(m : ℂ) * shiftedSum χ G s‖ = ‖χ s * S s‖ := by rw [hexp]
    have h2 : ‖(m : ℂ) * shiftedSum χ G s‖ = (m : ℝ) * ‖shiftedSum χ G s‖ := by
      rw [norm_mul, Complex.norm_natCast]
    have h3 : ‖χ s * S s‖ = ‖S s‖ := by
      rw [norm_mul, norm_chi_eq_one hχ hχ1 hs0, one_mul]
    have h4 : (m : ℝ) * ‖shiftedSum χ G s‖ = ‖S s‖ := by rw [← h2, h1, h3]
    calc ((m : ℝ) ^ 2) * ‖shiftedSum χ G s‖ ^ 2
        = ((m : ℝ) * ‖shiftedSum χ G s‖) ^ 2 := by ring
      _ = ‖S s‖ ^ 2 := by rw [h4]
  -- (2) Σ_{s≠0} ‖S s‖² as a complex sum, expanded by orthogonality
  have hcx : ((∑ s ∈ Finset.univ.erase (0 : F), ‖S s‖ ^ 2 : ℝ) : ℂ)
      = ((Fintype.card F - 1 : ℕ) : ℂ)
          * ((∑ j ∈ Finset.univ \ {(0 : ZMod m)}, ((‖J j‖ ^ 2 : ℝ) : ℂ)) + 1) := by
    have hzz : ∀ s : F, ((‖S s‖ ^ 2 : ℝ) : ℂ) = S s * (starRingEnd ℂ) (S s) := by
      intro s
      rw [RCLike.mul_conj]
      norm_cast
    rw [Complex.ofReal_sum]
    rw [Finset.sum_congr rfl (fun s _ => hzz s)]
    -- expand (Σ_j J_j λ_j − 1)(Σ_k conj J_k conj λ_k − 1)
    have hconjS : ∀ s ∈ Finset.univ.erase (0 : F), (starRingEnd ℂ) (S s)
        = (∑ k ∈ Finset.univ \ {(0 : ZMod m)}, (starRingEnd ℂ) (J k) * lam (-k) s) - 1 := by
      intro s hs
      have hs0 : s ≠ 0 := (Finset.mem_erase.mp hs).1
      rw [hSdef]
      simp only [map_sub, map_sum, map_mul, map_one]
      congr 1
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [conj_lam hfam hgrp k hs0]
    -- the four pieces
    have hexpand : ∀ s ∈ Finset.univ.erase (0 : F),
        S s * (starRingEnd ℂ) (S s)
          = (∑ j ∈ Finset.univ \ {(0 : ZMod m)}, ∑ k ∈ Finset.univ \ {(0 : ZMod m)},
              J j * (starRingEnd ℂ) (J k) * (lam j s * lam (-k) s))
            - (∑ j ∈ Finset.univ \ {(0 : ZMod m)}, J j * lam j s)
            - (∑ k ∈ Finset.univ \ {(0 : ZMod m)}, (starRingEnd ℂ) (J k) * lam (-k) s)
            + 1 := by
      intro s hs
      rw [hconjS s hs, hSdef]
      rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one]
      rw [Finset.sum_mul_sum]
      have : ∀ j ∈ Finset.univ \ {(0 : ZMod m)}, ∀ k ∈ Finset.univ \ {(0 : ZMod m)},
          (J j * lam j s) * ((starRingEnd ℂ) (J k) * lam (-k) s)
            = J j * (starRingEnd ℂ) (J k) * (lam j s * lam (-k) s) := by
        intro j _ k _; ring
      rw [Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun k hk => this j hj k hk))]
      ring
    rw [Finset.sum_congr rfl hexpand]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    -- piece A: the double sum collapses to the diagonal
    have hA : ∑ s ∈ Finset.univ.erase (0 : F),
        ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, ∑ k ∈ Finset.univ \ {(0 : ZMod m)},
          J j * (starRingEnd ℂ) (J k) * (lam j s * lam (-k) s)
        = ((Fintype.card F - 1 : ℕ) : ℂ)
            * ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, ((‖J j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Finset.sum_comm]
      have hjstep : ∀ j ∈ Finset.univ \ {(0 : ZMod m)},
          ∑ s ∈ Finset.univ.erase (0 : F), ∑ k ∈ Finset.univ \ {(0 : ZMod m)},
            J j * (starRingEnd ℂ) (J k) * (lam j s * lam (-k) s)
          = ((Fintype.card F - 1 : ℕ) : ℂ) * ((‖J j‖ ^ 2 : ℝ) : ℂ) := by
        intro j hjmem
        rw [Finset.sum_comm]
        have hk : ∀ k ∈ Finset.univ \ {(0 : ZMod m)},
            ∑ s ∈ Finset.univ.erase (0 : F),
              J j * (starRingEnd ℂ) (J k) * (lam j s * lam (-k) s)
            = (if k = j then ((Fintype.card F - 1 : ℕ) : ℂ) * ((‖J j‖ ^ 2 : ℝ) : ℂ) else 0) := by
          intro k _
          have hinner : ∑ s ∈ Finset.univ.erase (0 : F), lam j s * lam (-k) s
              = if j = k then ((Fintype.card F - 1 : ℕ) : ℂ) else 0 := by
            have hpt2 : ∀ s ∈ Finset.univ.erase (0 : F),
                lam j s * lam (-k) s = lam j s * (starRingEnd ℂ) (lam k s) := by
              intro s hs
              have hs0 : s ≠ 0 := (Finset.mem_erase.mp hs).1
              rw [conj_lam hfam hgrp k hs0]
            rw [Finset.sum_congr rfl hpt2]
            exact sum_lam_mul_conj_erase_zero hfam hgrp j k
          calc ∑ s ∈ Finset.univ.erase (0 : F),
              J j * (starRingEnd ℂ) (J k) * (lam j s * lam (-k) s)
              = J j * (starRingEnd ℂ) (J k)
                  * ∑ s ∈ Finset.univ.erase (0 : F), lam j s * lam (-k) s := by
                rw [Finset.mul_sum]
            _ = J j * (starRingEnd ℂ) (J k)
                  * (if j = k then ((Fintype.card F - 1 : ℕ) : ℂ) else 0) := by rw [hinner]
            _ = (if k = j then ((Fintype.card F - 1 : ℕ) : ℂ)
                  * ((‖J j‖ ^ 2 : ℝ) : ℂ) else 0) := by
                by_cases hkj : k = j
                · subst hkj
                  rw [if_pos rfl, if_pos rfl]
                  have : J k * (starRingEnd ℂ) (J k) = ((‖J k‖ ^ 2 : ℝ) : ℂ) := by
                    rw [RCLike.mul_conj]; norm_cast
                  rw [this]; ring
                · rw [if_neg (fun h => hkj h.symm), if_neg hkj, mul_zero]
        rw [Finset.sum_congr rfl hk]
        rw [Finset.sum_ite_eq' (Finset.univ \ {(0 : ZMod m)}) j
          (fun _ => ((Fintype.card F - 1 : ℕ) : ℂ) * ((‖J j‖ ^ 2 : ℝ) : ℂ))]
        rw [if_pos hjmem]
      rw [Finset.sum_congr rfl hjstep, ← Finset.mul_sum]
    -- pieces B, C: linear terms vanish by orthogonality (all indices nonzero)
    have hB : ∑ s ∈ Finset.univ.erase (0 : F),
        ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, J j * lam j s = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero (fun j hjmem => ?_)
      have hj0 : j ≠ 0 := by
        have := (Finset.mem_sdiff.mp hjmem).2; simpa using this
      rw [← Finset.mul_sum, sum_lam_erase_zero hfam j, if_neg hj0, mul_zero]
    have hC : ∑ s ∈ Finset.univ.erase (0 : F),
        ∑ k ∈ Finset.univ \ {(0 : ZMod m)}, (starRingEnd ℂ) (J k) * lam (-k) s = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero (fun k hkmem => ?_)
      have hk0 : (-k) ≠ 0 := by
        have := (Finset.mem_sdiff.mp hkmem).2
        simp only [Finset.mem_singleton] at this
        simpa using this
      rw [← Finset.mul_sum, sum_lam_erase_zero hfam (-k), if_neg hk0, mul_zero]
    have hD : ∑ _s ∈ Finset.univ.erase (0 : F), (1 : ℂ)
        = ((Fintype.card F - 1 : ℕ) : ℂ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 1
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    rw [hA, hB, hC, hD]
    ring
  -- (3) glue: real parts
  have hreal : ∑ s ∈ Finset.univ.erase (0 : F), ((m : ℝ) ^ 2) * ‖shiftedSum χ G s‖ ^ 2
      = ∑ s ∈ Finset.univ.erase (0 : F), ‖S s‖ ^ 2 :=
    Finset.sum_congr rfl hpt
  have hfinal : ((Fintype.card F - 1 : ℕ) : ℝ)
      * ((∑ j ∈ Finset.univ \ {(0 : ZMod m)}, ‖J j‖ ^ 2) + 1)
      = ∑ s ∈ Finset.univ.erase (0 : F), ‖S s‖ ^ 2 := by
    have := hcx
    have hcast : ((∑ s ∈ Finset.univ.erase (0 : F), ‖S s‖ ^ 2 : ℝ) : ℂ)
        = ((((Fintype.card F - 1 : ℕ) : ℝ)
            * ((∑ j ∈ Finset.univ \ {(0 : ZMod m)}, ‖J j‖ ^ 2) + 1) : ℝ) : ℂ) := by
      rw [this]
      push_cast
      ring
    exact_mod_cast hcast.symm
  calc ((Fintype.card F - 1 : ℕ) : ℝ)
      * ((∑ j ∈ Finset.univ \ {(0 : ZMod m)}, ‖jacobiCoeff χ lam j‖ ^ 2) + 1)
      = ∑ s ∈ Finset.univ.erase (0 : F), ‖S s‖ ^ 2 := hfinal
    _ = (m : ℝ) ^ 2 * ∑ s ∈ Finset.univ.erase (0 : F), ‖shiftedSum χ G s‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact hreal.symm

end ArkLib.ProximityGap.Frontier.R20JacobiParseval

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R20JacobiParseval.conj_lam
#print axioms ArkLib.ProximityGap.Frontier.R20JacobiParseval.sum_lam_mul_conj_erase_zero
#print axioms ArkLib.ProximityGap.Frontier.R20JacobiParseval.norm_chi_eq_one
#print axioms ArkLib.ProximityGap.Frontier.R20JacobiParseval.jacobi_parseval

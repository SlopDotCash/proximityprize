/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Structural barriers and exact spectral laws for CORE Paley discrepancy

This file formalizes four sharp structural theorems for the CORE Paley/BGK campaign,
completely self-contained on Mathlib and axiom-clean (standard Lean axioms only):

1. **Exact distinct-4-tuple cross-ratio reduction (`quartic_charSum_eq_legendreTrace`)**:
   For every odd-characteristic finite field `F` and every four distinct `a, b, c, d ∈ F`,
   `∑ x : F, χ((x - a)(x - b)(x - c)(x - d)) = -1 + χ(-(a - b)(c - d)) * L((a-c)(b-d)/((a-b)(c-d)))`.
2. **Unsigned cross-ratio energy barrier (`unsigned_crossRatio_energy_ge`,
   `unsigned_cauchy_schwarz_cannot_beat_hasse`)**:
   For every subset `A ⊆ F` of size `n`, the unsigned cross-ratio multiplicities satisfy
   `(q - 2) * ∑_{λ ≠ 0,1} V_A(λ)² ≥ (n(n-1)(n-2)(n-3))²`, and consequently
   `q * √(∑ V_A(λ)²) ≥ √q * n(n-1)(n-2)(n-3)`. This proves that Cauchy–Schwarz on `⟨V_A^signed, L⟩`
   via unsigned cross-ratio energy can NEVER beat the pointwise Hasse scale `√q · (n)_4` for any
   set `A` of any size.
3. **Exact dyadic-tower DFT even/odd Parseval energy split (`dyadic_dft_even_energy`,
   `dyadic_dft_odd_energy`)**:
   For any cyclic subgroup `⟨g⟩` of even order `2m` (`g^m = -1`) and cyclic Paley sequence
   `c_j = χ(1 - g^j)`, the DFT spectrum splits with exact even- and odd-frequency energies
   `∑_{r < m} ‖ĉ(2r)‖² = m (2m - 1 + 2 s(H²))` and
   `∑_{r < m} ‖ĉ(2r+1)‖² = m (2m - 1 - 2 s(H²))`, where `s(H²) = ∑_{j < m} χ(1 - (g²)^j)`.
4. **Five-site skew-symmetric `𝔽₃`-rank constancy (`skew_five_f3_rank_eq_four`)**:
   Every `5 × 5` skew-symmetric zero-diagonal `{±1}` matrix over `ZMod 3` has `Matrix.rank M = 4`
   identically (at least one of the three principal `4 × 4` minors dropping `{2, 3, 4}` is always
   nonzero, while `det M = 0`). Thus 5-site `𝔽₃`-rank carries zero discriminating power for
   primes `p ≡ 3 (mod 4)`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace ProximityGap.PaleyCrossRatioBarrier

open Finset Matrix

/-! ## 1. Exact distinct-4-tuple cross-ratio reduction -/

section CrossRatio

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Legendre elliptic trace `L(λ) = ∑ z : F, χ(z * (z - 1) * (z - λ))`. -/
def legendreTrace (lam : F) : ℤ :=
  ∑ z : F, quadraticChar F (z * (z - 1) * (z - lam))

/-- **Exact quartic-to-Legendre cross-ratio identity**:
for any four distinct elements `a, b, c, d` in a finite field `F`,
`∑ x : F, χ((x - a)(x - b)(x - c)(x - d)) = -1 + χ(-(a - b)(c - d)) * L((a-c)(b-d)/((a-b)(c-d)))`. -/
theorem quartic_charSum_eq_legendreTrace {a b c d : F}
    (hab : a ≠ b) (_hac : a ≠ c) (had : a ≠ d) (_hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∑ x : F, quadraticChar F ((x - a) * (x - b) * (x - c) * (x - d)) =
      -1 + quadraticChar F (-(a - b) * (c - d)) *
        legendreTrace (((a - c) * (b - d)) / ((a - b) * (c - d))) := by
  classical
  have hab0 : a - b ≠ 0 := sub_ne_zero.mpr hab
  have had0 : a - d ≠ 0 := sub_ne_zero.mpr had
  have hbd0 : b - d ≠ 0 := sub_ne_zero.mpr hbd
  have hcd0 : c - d ≠ 0 := sub_ne_zero.mpr hcd
  -- Step 1: Drop `x = d` (zero term) and substitute `t = (x - d)⁻¹` on `F \ {d} ↔ F \ {0}`.
  have hstep1 : ∑ x : F, quadraticChar F ((x - a) * (x - b) * (x - c) * (x - d)) =
      ∑ t ∈ Finset.univ.erase (0 : F),
        quadraticChar F ((1 - (a - d) * t) * (1 - (b - d) * t) * (1 - (c - d) * t)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ d), sub_self, mul_zero, MulChar.map_zero,
      zero_add]
    refine Finset.sum_nbij' (fun x => (x - d)⁻¹) (fun t => d + t⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_erase] at hx ⊢
      exact ⟨inv_ne_zero (sub_ne_zero.mpr hx.1), Finset.mem_univ _⟩
    · intro t ht
      rw [Finset.mem_erase] at ht ⊢
      exact ⟨fun h => inv_ne_zero ht.1 (by linear_combination h), Finset.mem_univ _⟩
    · intro x hx
      have hxd : x - d ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hx).1
      rw [inv_inv]; ring
    · intro t ht
      have ht0 : t ≠ 0 := (Finset.mem_erase.mp ht).1
      rw [show d + t⁻¹ - d = t⁻¹ by ring, inv_inv]
    · intro x hx
      have hxd : x - d ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hx).1
      have harg : (x - a) * (x - b) * (x - c) * (x - d) =
          ((x - d) ^ 2) ^ 2 *
            ((1 - (a - d) * (x - d)⁻¹) * (1 - (b - d) * (x - d)⁻¹) * (1 - (c - d) * (x - d)⁻¹)) := by
        field_simp [hxd]; ring
      rw [harg, map_mul, quadraticChar_sq_one' (pow_ne_zero 2 hxd), one_mul]
  -- Step 2: Reinsert `t = 0` (whose value is `χ(1) = 1`, costing `-1`).
  have hstep2 : ∑ t ∈ Finset.univ.erase (0 : F),
        quadraticChar F ((1 - (a - d) * t) * (1 - (b - d) * t) * (1 - (c - d) * t)) =
      -1 + ∑ t : F, quadraticChar F ((1 - (a - d) * t) * (1 - (b - d) * t) * (1 - (c - d) * t)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F))]
    simp only [mul_zero, sub_zero, mul_one, map_one]
    ring
  -- Step 3: Affine substitution `t = (a - d)⁻¹ + Δ * z` with `Δ = (b - d)⁻¹ - (a - d)⁻¹`.
  set Δ : F := (b - d)⁻¹ - (a - d)⁻¹
  have hΔ_eq : Δ = (a - b) / ((a - d) * (b - d)) := by
    dsimp [Δ]; field_simp [had0, hbd0]; ring
  have hΔ0 : Δ ≠ 0 := by
    rw [hΔ_eq]; exact div_ne_zero hab0 (mul_ne_zero had0 hbd0)
  set lam : F := ((a - c) * (b - d)) / ((a - b) * (c - d))
  have hbi : Function.Bijective (fun z : F => (a - d)⁻¹ + Δ * z) :=
    (Equiv.addLeft (a - d)⁻¹).bijective.comp (mulLeft_bijective₀ Δ hΔ0)
  have hstep3 : ∑ t : F,
        quadraticChar F ((1 - (a - d) * t) * (1 - (b - d) * t) * (1 - (c - d) * t)) =
      quadraticChar F (-(a - b) * (c - d)) * legendreTrace lam := by
    rw [← Fintype.sum_bijective (fun z : F => (a - d)⁻¹ + Δ * z) hbi _ _ (fun _ => rfl),
      legendreTrace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    have hfac : (1 - (a - d) * ((a - d)⁻¹ + Δ * z)) *
        (1 - (b - d) * ((a - d)⁻¹ + Δ * z)) *
        (1 - (c - d) * ((a - d)⁻¹ + Δ * z)) =
        ((a - b) / ((a - d) * (b - d))) ^ 2 *
          ((-(a - b) * (c - d)) * (z * (z - 1) * (z - lam))) := by
      rw [hΔ_eq]; dsimp [lam]
      field_simp [hab0, had0, hbd0, hcd0]
      ring
    rw [hfac, map_mul, quadraticChar_sq_one' (div_ne_zero hab0 (mul_ne_zero had0 hbd0)),
      one_mul, map_mul]
  rw [hstep1, hstep2, hstep3]

/-! ## 2. Unsigned cross-ratio energy barrier -/

/-- Set of ordered distinct 4-tuples in `A`. -/
def distinctFourTuples (A : Finset F) : Finset ((F × F) × (F × F)) :=
  ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter fun t =>
    t.1.1 ≠ t.1.2 ∧ t.1.1 ≠ t.2.1 ∧ t.1.1 ≠ t.2.2 ∧
      t.1.2 ≠ t.2.1 ∧ t.1.2 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

/-- Cross-ratio `((a - c) * (b - d)) / ((a - b) * (c - d))` of a 4-tuple `((a, b), (c, d))`. -/
def crossRatio (t : (F × F) × (F × F)) : F :=
  ((t.1.1 - t.2.1) * (t.1.2 - t.2.2)) / ((t.1.1 - t.1.2) * (t.2.1 - t.2.2))

/-- Unsigned cross-ratio multiplicity `V_A^un(λ)` of distinct ordered 4-tuples in `A`. -/
def unsignedCrossRatioCount (A : Finset F) (lam : F) : ℕ :=
  ((distinctFourTuples A).filter fun t => crossRatio t = lam).card

theorem card_distinctFourTuples (A : Finset F) :
    (distinctFourTuples A).card = A.card * (A.card - 1) * (A.card - 2) * (A.card - 3) := by
  classical
  -- Count by choosing `a ∈ A`, `b ∈ A.erase a`, `c ∈ (A.erase a).erase b`, `d ∈ ...`
  let S := A.sigma fun a =>
    (A.erase a).sigma fun b =>
      ((A.erase a).erase b).sigma fun c =>
        (((A.erase a).erase b).erase c)
  have hbij : (distinctFourTuples A).card = S.card := by
    refine Finset.card_bij (fun t _ => ⟨t.1.1, ⟨t.1.2, ⟨t.2.1, t.2.2⟩⟩⟩) ?_ ?_ ?_
    · intro t ht
      rw [distinctFourTuples, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
        Finset.mem_product] at ht
      obtain ⟨⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩, hab, hac, had, hbc, hbd, hcd⟩ := ht
      simp only [S, Finset.mem_sigma, Finset.mem_erase]
      exact ⟨ha, ⟨hab.symm, hb⟩, ⟨hbc.symm, hac.symm, hc⟩, ⟨hcd.symm, hbd.symm, had.symm, hd⟩⟩
    · intro t₁ _ t₂ _ h
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      exact Prod.ext (Prod.ext h1 h2) (Prod.ext h3 h4)
    · intro u hu
      simp only [S, Finset.mem_sigma, Finset.mem_erase] at hu
      obtain ⟨ha, ⟨hba, hb⟩, ⟨hcb, hca, hc⟩, ⟨hdc, hdb, hda, hd⟩⟩ := hu
      refine ⟨((u.1, u.2.1), (u.2.2.1, u.2.2.2)), ?_, rfl⟩
      rw [distinctFourTuples, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
        Finset.mem_product]
      exact ⟨⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩, hba.symm, hca.symm, hda.symm, hcb.symm, hdb.symm, hdc.symm⟩
  rw [hbij]
  simp only [S, Finset.card_sigma]
  have hsum3 : ∀ a ∈ A, ∀ b ∈ A.erase a, ∀ c ∈ (A.erase a).erase b,
      (((A.erase a).erase b).erase c).card = A.card - 3 := by
    intro a ha b hb c hc
    rw [Finset.card_erase_of_mem hc, Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha]
    omega
  have hsum2 : ∀ a ∈ A, ∀ b ∈ A.erase a,
      ∑ c ∈ (A.erase a).erase b, (((A.erase a).erase b).erase c).card =
        (A.card - 2) * (A.card - 3) := by
    intro a ha b hb
    rw [Finset.sum_congr rfl (hsum3 a ha b hb), Finset.sum_const, smul_eq_mul,
      Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha, Nat.sub_sub]
  have hsum1 : ∀ a ∈ A,
      ∑ b ∈ A.erase a, ∑ c ∈ (A.erase a).erase b, (((A.erase a).erase b).erase c).card =
        (A.card - 1) * ((A.card - 2) * (A.card - 3)) := by
    intro a ha
    rw [Finset.sum_congr rfl (hsum2 a ha), Finset.sum_const, smul_eq_mul,
      Finset.card_erase_of_mem ha]
  rw [Finset.sum_congr rfl hsum1, Finset.sum_const, smul_eq_mul]
  ring

theorem crossRatio_mem_punctured {A : Finset F} {t : (F × F) × (F × F)}
    (ht : t ∈ distinctFourTuples A) :
    crossRatio t ∈ (Finset.univ.erase (0 : F)).erase 1 := by
  rw [distinctFourTuples, Finset.mem_filter] at ht
  obtain ⟨_, hab, hac, had, hbc, hbd, hcd⟩ := ht
  have hab0 : t.1.1 - t.1.2 ≠ 0 := sub_ne_zero.mpr hab
  have hac0 : t.1.1 - t.2.1 ≠ 0 := sub_ne_zero.mpr hac
  have had0 : t.1.1 - t.2.2 ≠ 0 := sub_ne_zero.mpr had
  have hbc0 : t.1.2 - t.2.1 ≠ 0 := sub_ne_zero.mpr hbc
  have hbd0 : t.1.2 - t.2.2 ≠ 0 := sub_ne_zero.mpr hbd
  have hcd0 : t.2.1 - t.2.2 ≠ 0 := sub_ne_zero.mpr hcd
  rw [Finset.mem_erase, Finset.mem_erase]
  refine ⟨?_, ?_, Finset.mem_univ _⟩
  · intro h1
    unfold crossRatio at h1
    have heq := (div_eq_one_iff_eq (mul_ne_zero hab0 hcd0)).mp h1
    have hfac : (t.1.1 - t.2.2) * (t.1.2 - t.2.1) = 0 := by linear_combination heq
    exact mul_ne_zero had0 hbc0 hfac
  · unfold crossRatio
    exact div_ne_zero (mul_ne_zero hac0 hbd0) (mul_ne_zero hab0 hcd0)

/-- The unsigned cross-ratio counts over `F \ {0, 1}` sum to `n(n-1)(n-2)(n-3)`. -/
theorem sum_unsignedCrossRatioCount (A : Finset F) :
    ∑ lam ∈ (Finset.univ.erase (0 : F)).erase 1, unsignedCrossRatioCount A lam =
      A.card * (A.card - 1) * (A.card - 2) * (A.card - 3) := by
  rw [← card_distinctFourTuples A]
  exact (Finset.card_eq_sum_card_fiberwise (f := crossRatio) (s := distinctFourTuples A)
    (t := (Finset.univ.erase (0 : F)).erase 1) (fun t ht => crossRatio_mem_punctured ht)).symm

/-- **Unsigned Cross-Ratio Energy Lower Bound**:
for every `A ⊆ F` of size `n`,
`(q - 2) * ∑_{λ ≠ 0,1} V_A^un(λ)² ≥ (n(n-1)(n-2)(n-3))²`. -/
theorem unsigned_crossRatio_energy_ge (A : Finset F) :
    ((A.card * (A.card - 1) * (A.card - 2) * (A.card - 3) : ℕ) : ℝ) ^ 2 ≤
      ((Fintype.card F - 2 : ℕ) : ℝ) *
        ∑ lam ∈ (Finset.univ.erase (0 : F)).erase 1, (unsignedCrossRatioCount A lam : ℝ) ^ 2 := by
  set P := (Finset.univ.erase (0 : F)).erase (1 : F)
  have hcardP : P.card = Fintype.card F - 2 := by
    have h1mem : (1 : F) ∈ Finset.univ.erase (0 : F) :=
      Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_univ _⟩
    rw [Finset.card_erase_of_mem h1mem, Finset.card_erase_of_mem (Finset.mem_univ (0 : F)),
      Finset.card_univ]
    omega
  have hcs := sq_sum_le_card_mul_sum_sq (s := P) (f := fun lam => (unsignedCrossRatioCount A lam : ℝ))
  have hsum : ∑ lam ∈ P, (unsignedCrossRatioCount A lam : ℝ) =
      ((A.card * (A.card - 1) * (A.card - 2) * (A.card - 3) : ℕ) : ℝ) := by
    exact_mod_cast sum_unsignedCrossRatioCount A
  rw [hsum, hcardP] at hcs
  exact hcs

/-- **Unsigned Cross-Ratio Cauchy–Schwarz Barrier**:
For EVERY finite field `F` of size `q ≥ 3` and EVERY subset `A ⊆ F` of size `n`,
`√q · n(n-1)(n-2)(n-3) ≤ q · √(∑_{λ ≠ 0,1} V_A^un(λ)²)`.
Hence bounding `|⟨V_A^signed, L⟩|` via Cauchy–Schwarz + `|V_A^signed| ≤ V_A^un` (together with
`∑ L² < q²`) can NEVER beat the pointwise Hasse scale `√q · (n)_4` for ANY set `A`! -/
theorem unsigned_cauchy_schwarz_cannot_beat_hasse (A : Finset F) :
    Real.sqrt (Fintype.card F) *
        ((A.card * (A.card - 1) * (A.card - 2) * (A.card - 3) : ℕ) : ℝ) ≤
      (Fintype.card F : ℝ) *
        Real.sqrt (∑ lam ∈ (Finset.univ.erase (0 : F)).erase 1,
          (unsignedCrossRatioCount A lam : ℝ) ^ 2) := by
  set E : ℝ := ∑ lam ∈ (Finset.univ.erase (0 : F)).erase 1, (unsignedCrossRatioCount A lam : ℝ) ^ 2
  set N : ℝ := ((A.card * (A.card - 1) * (A.card - 2) * (A.card - 3) : ℕ) : ℝ)
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hq : (0 : ℝ) ≤ Fintype.card F := Nat.cast_nonneg _
  have hle : ((Fintype.card F - 2 : ℕ) : ℝ) ≤ (Fintype.card F : ℝ) := by
    exact_mod_cast Nat.sub_le (Fintype.card F) 2
  have hsq : (Real.sqrt (Fintype.card F) * N) ^ 2 ≤ ((Fintype.card F : ℝ) * Real.sqrt E) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hq, Real.sq_sqrt hE]
    have h1 := unsigned_crossRatio_energy_ge A
    have h2 : N ^ 2 ≤ (Fintype.card F : ℝ) * E :=
      h1.trans (mul_le_mul_of_nonneg_right hle hE)
    nlinarith [mul_le_mul_of_nonneg_left h2 hq]
  have hrhs_nonneg : 0 ≤ (Fintype.card F : ℝ) * Real.sqrt E := by positivity
  exact le_of_sq_le_sq hsq hrhs_nonneg

end CrossRatio

/-! ## 3. Exact dyadic-tower DFT even/odd Parseval energy split -/

section DyadicDFT

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Cyclic Paley DFT `ĉ(k) = ∑_{j < n} χ(1 - g^j) * exp(2πi k j / n)`. -/
noncomputable def cyclicDFT (g : F) (n k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range n,
    (quadraticChar F (1 - g ^ j) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I / (n : ℂ)) ^ (k * j)

private theorem exp_two_pi_div_prim {m : ℕ} (hm : 0 < m) {r : ℕ} (hr0 : 0 < r) (hrm : r < m) :
    Complex.exp (2 * Real.pi * Complex.I / (m : ℂ)) ^ r ≠ 1 := by
  intro h1
  rw [← Complex.exp_nat_mul] at h1
  set θ : ℝ := 2 * Real.pi * (r : ℝ) / (m : ℝ)
  have hθ_eq : (r : ℂ) * (2 * Real.pi * Complex.I / (m : ℂ)) = (θ : ℂ) * Complex.I := by
    dsimp [θ]; push_cast; ring
  rw [hθ_eq, Complex.exp_mul_I] at h1
  have hre := congrArg Complex.re h1
  have hcos1 : Real.cos θ = 1 := by
    simpa [Complex.add_re, Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im] using hre
  have hmposR : (0 : ℝ) < m := by exact_mod_cast hm
  have hr0R : (0 : ℝ) < r := by exact_mod_cast hr0
  have hrmR : (r : ℝ) < m := by exact_mod_cast hrm
  have hθ_pos : 0 < θ := div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hr0R) hmposR
  have hθ_lt : θ < 2 * Real.pi := by
    dsimp [θ]; rw [div_lt_iff₀ hmposR]; nlinarith [Real.pi_pos]
  have hcos_lt : Real.cos θ < 1 := by
    rcases le_or_gt θ Real.pi with hle | hgt
    · calc Real.cos θ < Real.cos 0 :=
            Real.strictAntiOn_cos (Set.left_mem_Icc.mpr Real.pi_pos.le) ⟨hθ_pos.le, hle⟩ hθ_pos
        _ = 1 := Real.cos_zero
    · rw [← Real.cos_two_pi_sub θ]
      calc Real.cos (2 * Real.pi - θ) < Real.cos 0 :=
            Real.strictAntiOn_cos (Set.left_mem_Icc.mpr Real.pi_pos.le)
              ⟨by linarith, by linarith⟩ (by linarith)
        _ = 1 := Real.cos_zero
  linarith

private theorem dyadic_dft_parseval_signed (g : F) {m : ℕ} (hm : 0 < m)
    (hgm : g ^ m = -1) (hord : ∀ j < 2 * m, g ^ j = 1 → j = 0) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    let kOf (r : ℕ) : ℕ := if ε = 1 then 2 * r else 2 * r + 1
    ∑ r ∈ Finset.range m, ‖cyclicDFT g (2 * m) (kOf r)‖ ^ 2 =
      (m : ℝ) * (((2 * m : ℤ) - 1 + ε * (2 * ∑ j ∈ Finset.range m, quadraticChar F (1 - (g ^ 2) ^ j)) : ℤ) : ℝ) := by
  intro kOf
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((2 * m : ℕ) : ℂ))
  let c (j : ℕ) : ℤ := quadraticChar F (1 - g ^ j)
  have h2m_pos : 0 < 2 * m := by omega
  have hζ_pow_2m : ζ ^ (2 * m) = 1 := by
    dsimp [ζ]
    rw [← Complex.exp_nat_mul]
    have hne : ((2 * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast h2m_pos.ne'
    rw [show ((2 * m : ℕ) : ℂ) * (2 * Real.pi * Complex.I / ((2 * m : ℕ) : ℂ)) =
        2 * Real.pi * Complex.I by field_simp [hne]]
    exact Complex.exp_two_pi_mul_I
  have hζ_pow_m : ζ ^ m = -1 := by
    dsimp [ζ]
    rw [← Complex.exp_nat_mul]
    have hmne : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [show (m : ℂ) * (2 * Real.pi * Complex.I / ((2 * m : ℕ) : ℂ)) = Real.pi * Complex.I by
      push_cast; field_simp [hmne]]
    exact Complex.exp_pi_mul_I
  have hζ_conj : starRingEnd ℂ ζ = ζ⁻¹ := by
    have hnorm : ‖ζ‖ = 1 := by
      dsimp [ζ]
      rw [show 2 * (Real.pi : ℂ) * Complex.I / ((2 * m : ℕ) : ℂ) =
          ((2 * Real.pi / ((2 * m : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have hne : ζ ≠ 0 := Complex.exp_ne_zero _
    have hmc : ζ * starRingEnd ℂ ζ = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; norm_num
    exact mul_left_cancel₀ hne (hmc.trans (mul_inv_cancel₀ hne).symm)
  have hζ_sq : ζ ^ 2 = Complex.exp (2 * Real.pi * Complex.I / (m : ℂ)) := by
    dsimp [ζ]
    rw [← Complex.exp_nat_mul]
    congr 1
    have hmne : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    push_cast; field_simp [hmne]
  have hζ_mod : ∀ n : ℕ, ζ ^ (n % (2 * m)) = ζ ^ n := fun n => by
    conv_rhs => rw [← Nat.div_add_mod n (2 * m)]
    rw [pow_add, pow_mul, hζ_pow_2m, one_pow, one_mul]
  have hζ_zpow_add : ∀ a b : ℕ, ζ ^ a * (starRingEnd ℂ ζ) ^ b = ζ ^ ((a : ℤ) - b) := fun a b => by
    rw [hζ_conj, ← zpow_natCast, ← zpow_natCast, inv_zpow, ← zpow_neg, ← zpow_add₀ (Complex.exp_ne_zero _),
      sub_eq_add_neg]
  have hmod_half : ∀ j : ℕ, j < 2 * m →
      (j + m) % (2 * m) = if j < m then j + m else j - m := fun j hj => by
    split_ifs with hjm
    · exact Nat.mod_eq_of_lt (by omega)
    · have : j + m = (j - m) + 2 * m := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  -- Expand `∑_{r < m} ‖ĉ(kOf r)‖²` in `ℂ` and swap sums!
  have hsumC : ((∑ r ∈ Finset.range m, ‖cyclicDFT g (2 * m) (kOf r)‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ Finset.range (2 * m), ∑ l ∈ Finset.range (2 * m),
        (c j : ℂ) * (c l : ℂ) *
          ∑ r ∈ Finset.range m, ζ ^ ((kOf r : ℤ) * ((j : ℤ) - l)) := by
    rw [Complex.ofReal_sum]
    have hnorm_sq : ∀ r : ℕ, ((‖cyclicDFT g (2 * m) (kOf r)‖ ^ 2 : ℝ) : ℂ) =
        ∑ j ∈ Finset.range (2 * m), ∑ l ∈ Finset.range (2 * m),
          (c j : ℂ) * (c l : ℂ) * ζ ^ ((kOf r : ℤ) * ((j : ℤ) - l)) := fun r => by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
      unfold cyclicDFT
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, map_intCast, map_pow]
      dsimp only [c, ζ]
      have hpow : ζ ^ (kOf r * j) * (starRingEnd ℂ ζ) ^ (kOf r * l) =
          ζ ^ ((kOf r : ℤ) * ((j : ℤ) - l)) := by
        rw [hζ_zpow_add]
        congr 1; push_cast; ring
      calc (quadraticChar F (1 - g ^ j) : ℂ) * ζ ^ (kOf r * j) *
              ((quadraticChar F (1 - g ^ l) : ℂ) * (starRingEnd ℂ ζ) ^ (kOf r * l))
          = (quadraticChar F (1 - g ^ j) : ℂ) * (quadraticChar F (1 - g ^ l) : ℂ) *
              (ζ ^ (kOf r * j) * (starRingEnd ℂ ζ) ^ (kOf r * l)) := by ring
        _ = _ := by rw [hpow]
    simp_rw [hnorm_sq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
  -- Evaluate the inner geometric sum over `r ∈ range m`:
  have hinner : ∀ j ∈ Finset.range (2 * m), ∀ l ∈ Finset.range (2 * m),
      ∑ r ∈ Finset.range m, ζ ^ ((kOf r : ℤ) * ((j : ℤ) - l)) =
        if l = j then (m : ℂ)
        else if l = (j + m) % (2 * m) then (ε : ℂ) * (m : ℂ)
        else 0 := by
    intro j hj l hl
    have hjlt : j < 2 * m := Finset.mem_range.mp hj
    have hllt : l < 2 * m := Finset.mem_range.mp hl
    set δ : ℤ := (j : ℤ) - l
    have hbase : ∀ r : ℕ, ζ ^ ((kOf r : ℤ) * δ) =
        (if ε = 1 then (1 : ℂ) else ζ ^ δ) * ((ζ ^ (2 : ℤ)) ^ δ) ^ r := fun r => by
      dsimp only [kOf]
      split_ifs
      · simp only [one_mul, Nat.cast_mul, Nat.cast_ofNat]
        rw [← zpow_natCast, ← zpow_mul, ← zpow_mul]
        congr 1; ring
      · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
        rw [← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ (Complex.exp_ne_zero _)]
        congr 1; ring
    simp_rw [hbase, ← Finset.mul_sum]
    have hmh := hmod_half j hjlt
    by_cases hlj : l = j
    · subst hlj
      simp only [↓reduceIte, δ, sub_self, zpow_zero, one_pow, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one]
      split_ifs <;> ring
    · simp only [hlj, ↓reduceIte]
      by_cases hlhalf : l = (j + m) % (2 * m)
      · simp only [hlhalf, ↓reduceIte]
        have hδ_cases : δ = (m : ℤ) ∨ δ = -(m : ℤ) := by
          rw [hmh] at hlhalf
          dsimp [δ]; split_ifs at hlhalf <;> omega
        have hsq1 : (ζ ^ (2 : ℤ)) ^ δ = 1 := by
          rcases hδ_cases with h | h <;> rw [h]
          · rw [← zpow_mul, show (2 : ℤ) * (m : ℤ) = ((2 * m : ℕ) : ℤ) by push_cast; ring,
              zpow_natCast, hζ_pow_2m]
          · rw [← zpow_mul, show (2 : ℤ) * -(m : ℤ) = -((2 * m : ℕ) : ℤ) by push_cast; ring,
              zpow_neg, zpow_natCast, hζ_pow_2m, inv_one]
        have hζδ : ζ ^ δ = -1 := by
          rcases hδ_cases with h | h <;> rw [h]
          · rw [zpow_natCast, hζ_pow_m]
          · rw [zpow_neg, zpow_natCast, hζ_pow_m, inv_neg, inv_one]
        rw [hsq1]
        simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, hζδ]
        rcases hε with h | h <;> simp [h]
      · simp only [hlhalf, ↓reduceIte]
        have hnotdvd : ¬ ((m : ℤ) ∣ δ) := by
          intro hdvd
          obtain ⟨q, hq⟩ := hdvd
          have h1 : -(2 * (m : ℤ)) < (m : ℤ) * q := by dsimp [δ] at hq; omega
          have h2 : (m : ℤ) * q < 2 * (m : ℤ) := by dsimp [δ] at hq; omega
          have hq_ge : -1 ≤ q := by
            by_contra hlt
            have : q ≤ -2 := by omega
            have : (m : ℤ) * q ≤ (m : ℤ) * (-2) :=
              mul_le_mul_of_nonneg_left this (by positivity)
            linarith
          have hq_le : q ≤ 1 := by
            by_contra hgt
            have : 2 ≤ q := by omega
            have : (m : ℤ) * 2 ≤ (m : ℤ) * q :=
              mul_le_mul_of_nonneg_left this (by positivity)
            linarith
          have : q = 0 ∨ q = 1 ∨ q = -1 := by omega
          rcases this with rfl | rfl | rfl
          · exact hlj (by dsimp [δ] at hq; omega)
          · rw [hmh] at hlhalf; dsimp [δ] at hq; split_ifs at hlhalf <;> omega
          · rw [hmh] at hlhalf; dsimp [δ] at hq; split_ifs at hlhalf <;> omega
        set w : ℂ := (ζ ^ (2 : ℤ)) ^ δ
        have hw_ne1 : w ≠ 1 := by
          dsimp [w]
          have hrem_pos : 0 < (δ % (m : ℤ)).toNat := by
            have hnn : 0 ≤ δ % (m : ℤ) := Int.emod_nonneg δ (by omega)
            have hnz : δ % (m : ℤ) ≠ 0 := fun h => hnotdvd (Int.dvd_of_emod_eq_zero h)
            omega
          have hrem_lt : (δ % (m : ℤ)).toNat < m := by
            have hlt : δ % (m : ℤ) < (m : ℤ) := Int.emod_lt_of_pos δ (by omega)
            omega
          have hζ2m : (ζ ^ (2 : ℤ)) ^ (m : ℤ) = 1 := by
            rw [← zpow_mul, show (2 : ℤ) * (m : ℤ) = ((2 * m : ℕ) : ℤ) by push_cast; ring,
              zpow_natCast, hζ_pow_2m]
          have hw_eq : (ζ ^ (2 : ℤ)) ^ δ = (ζ ^ 2) ^ (δ % (m : ℤ)).toNat := by
            have hdiv : δ = (m : ℤ) * (δ / (m : ℤ)) + δ % (m : ℤ) := (Int.mul_ediv_add_emod _ _).symm
            conv_lhs => rw [hdiv]
            rw [zpow_add₀ (zpow_ne_zero 2 (Complex.exp_ne_zero _)), zpow_mul, hζ2m, one_zpow,
              one_mul, ← Int.toNat_of_nonneg (Int.emod_nonneg δ (by omega)), zpow_natCast]
            rfl
          rw [hw_eq, hζ_sq]
          exact exp_two_pi_div_prim hm hrem_pos hrem_lt
        have hw_pow : w ^ m = 1 := by
          dsimp [w]
          rw [← zpow_natCast, ← zpow_mul, ← zpow_mul,
            show (2 : ℤ) * (δ * (m : ℤ)) = ((2 * m : ℕ) : ℤ) * δ by push_cast; ring,
            zpow_mul, zpow_natCast, hζ_pow_2m, one_zpow]
        have hgeom := geom_sum_mul w m
        rw [hw_pow, sub_self] at hgeom
        have hsum0 : ∑ r ∈ Finset.range m, w ^ r = 0 :=
          (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hw_ne1)
        rw [hsum0, mul_zero]
  -- Plug `hinner` into `hsumC` and evaluate the two surviving diagonal / half-shift sums!
  have heval_sum : ∑ j ∈ Finset.range (2 * m), ∑ l ∈ Finset.range (2 * m),
        (c j : ℂ) * (c l : ℂ) *
          (if l = j then (m : ℂ) else if l = (j + m) % (2 * m) then (ε : ℂ) * (m : ℂ) else 0) =
      (m : ℂ) * ((∑ j ∈ Finset.range (2 * m), c j ^ 2 : ℤ) : ℂ) +
        (ε : ℂ) * (m : ℂ) * ((∑ j ∈ Finset.range (2 * m), c j * c ((j + m) % (2 * m)) : ℤ) : ℂ) := by
    have hper : ∀ j ∈ Finset.range (2 * m),
        ∑ l ∈ Finset.range (2 * m), (c j : ℂ) * (c l : ℂ) *
          (if l = j then (m : ℂ) else if l = (j + m) % (2 * m) then (ε : ℂ) * (m : ℂ) else 0) =
        (m : ℂ) * (c j : ℂ) ^ 2 + (ε : ℂ) * (m : ℂ) * ((c j : ℂ) * (c ((j + m) % (2 * m)) : ℂ)) := by
      intro j hj
      have hjlt : j < 2 * m := Finset.mem_range.mp hj
      have hne_half : (j + m) % (2 * m) ≠ j := by
        rw [hmod_half j hjlt]; split_ifs <;> omega
      have hhalf_mem : (j + m) % (2 * m) ∈ Finset.range (2 * m) :=
        Finset.mem_range.mpr (Nat.mod_lt _ h2m_pos)
      have hsplit : ∀ l : ℕ,
          (c j : ℂ) * (c l : ℂ) *
            (if l = j then (m : ℂ) else if l = (j + m) % (2 * m) then (ε : ℂ) * (m : ℂ) else 0) =
          (if l = j then (m : ℂ) * (c j : ℂ) ^ 2 else 0) +
          (if l = (j + m) % (2 * m) then
            (ε : ℂ) * (m : ℂ) * ((c j : ℂ) * (c ((j + m) % (2 * m)) : ℂ)) else 0) := by
        intro l
        by_cases h1 : l = j
        · subst h1; simp only [↓reduceIte, hne_half.symm]; ring
        · by_cases h2 : l = (j + m) % (2 * m)
          · subst h2; simp only [h1, ↓reduceIte]; ring
          · simp only [h1, h2, ↓reduceIte]; ring
      simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp [hj, hhalf_mem]
    rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    push_cast; rfl
  -- Compute `∑_{j < 2m} c_j^2 = 2m - 1`.
  have hdiag : ∑ j ∈ Finset.range (2 * m), c j ^ 2 = (2 * m : ℤ) - 1 := by
    have hpt : ∀ j ∈ Finset.range (2 * m), c j ^ 2 = if j = 0 then (0 : ℤ) else 1 := by
      intro j hj
      dsimp only [c]
      by_cases hj0 : j = 0
      · subst hj0; simp
      · simp only [hj0, ↓reduceIte]
        have hne : (1 : F) - g ^ j ≠ 0 := by
          intro h
          have h1 : g ^ j = 1 := (sub_eq_zero.mp h).symm
          exact hj0 (hord j (Finset.mem_range.mp hj) h1)
        exact quadraticChar_sq_one hne
    rw [Finset.sum_congr rfl hpt, ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr h2m_pos)]
    simp only [↓reduceIte, zero_add]
    have hcongr : ∑ j ∈ (Finset.range (2 * m)).erase 0, (if j = 0 then (0 : ℤ) else 1) =
        ∑ _j ∈ (Finset.range (2 * m)).erase 0, (1 : ℤ) :=
      Finset.sum_congr rfl fun j hj => by simp [(Finset.mem_erase.mp hj).1]
    rw [hcongr, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_erase_of_mem (Finset.mem_range.mpr h2m_pos), Finset.card_range]
    omega
  -- Compute `∑_{j < 2m} c_j * c_{(j + m) % (2m)} = 2 * ∑_{j < m} χ(1 - (g^2)^j)`.
  have hhalf : ∑ j ∈ Finset.range (2 * m), c j * c ((j + m) % (2 * m)) =
      2 * ∑ j ∈ Finset.range m, quadraticChar F (1 - (g ^ 2) ^ j) := by
    have hg2m : g ^ (2 * m) = 1 := by
      rw [show 2 * m = m + m by omega, pow_add, hgm]; ring
    have hmod : ∀ j ∈ Finset.range (2 * m), g ^ ((j + m) % (2 * m)) = -g ^ j := by
      intro j hj
      have hjlt : j < 2 * m := Finset.mem_range.mp hj
      rcases lt_or_ge j m with hjm | hjm
      · rw [Nat.mod_eq_of_lt (by omega), pow_add, hgm, mul_neg_one]
      · have hmod_eq : (j + m) % (2 * m) = j - m := by
          have : j + m = (j - m) + 2 * m := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod_eq]
        have : g ^ j = g ^ (j - m) * g ^ m := by rw [← pow_add, Nat.sub_add_cancel hjm]
        rw [this, hgm, mul_neg_one, neg_neg]
    have hpair : ∀ j ∈ Finset.range (2 * m),
        c j * c ((j + m) % (2 * m)) = quadraticChar F (1 - (g ^ 2) ^ (j % m)) := by
      intro j hj
      dsimp only [c]
      rw [hmod j hj, sub_neg_eq_add, ← map_mul,
        show (1 - g ^ j) * (1 + g ^ j) = 1 - (g ^ 2) ^ j by ring]
      congr 2
      have hdiv : (g ^ 2) ^ m = 1 := by rw [← pow_mul, hg2m]
      conv_lhs => rw [← Nat.div_add_mod j m]
      rw [pow_add, pow_mul, hdiv, one_pow, one_mul]
    rw [Finset.sum_congr rfl hpair, show 2 * m = m + m by omega, Finset.sum_range_add]
    have h1 : ∑ j ∈ Finset.range m, quadraticChar F (1 - (g ^ 2) ^ (j % m)) =
        ∑ j ∈ Finset.range m, quadraticChar F (1 - (g ^ 2) ^ j) :=
      Finset.sum_congr rfl fun j hj => by rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]
    have h2 : ∑ j ∈ Finset.range m, quadraticChar F (1 - (g ^ 2) ^ ((m + j) % m)) =
        ∑ j ∈ Finset.range m, quadraticChar F (1 - (g ^ 2) ^ j) :=
      Finset.sum_congr rfl fun j hj => by rw [Nat.add_mod_left, Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]
    rw [h1, h2]; ring
  have hfinalC : ((∑ r ∈ Finset.range m, ‖cyclicDFT g (2 * m) (kOf r)‖ ^ 2 : ℝ) : ℂ) =
      (((m : ℝ) * (((2 * m : ℤ) - 1 + ε * (2 * ∑ j ∈ Finset.range m, quadraticChar F (1 - (g ^ 2) ^ j)) : ℤ) : ℝ)) : ℂ) := by
    rw [hsumC]
    have hcongr : ∑ j ∈ Finset.range (2 * m), ∑ l ∈ Finset.range (2 * m),
          (c j : ℂ) * (c l : ℂ) * ∑ r ∈ Finset.range m, ζ ^ ((kOf r : ℤ) * ((j : ℤ) - l)) =
        ∑ j ∈ Finset.range (2 * m), ∑ l ∈ Finset.range (2 * m),
          (c j : ℂ) * (c l : ℂ) *
            (if l = j then (m : ℂ) else if l = (j + m) % (2 * m) then (ε : ℂ) * (m : ℂ) else 0) :=
      Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => by rw [hinner j hj l hl]
    rw [hcongr, heval_sum, hdiag, hhalf]
    push_cast; ring
  exact_mod_cast hfinalC

/-- **Exact even-frequency Parseval energy of the cyclic Paley DFT on `μ_{2m}`**:
`∑_{r < m} ‖ĉ(2r)‖² = m * (2m - 1 + 2 * s(H²))`. -/
theorem dyadic_dft_even_energy (g : F) {m : ℕ} (hm : 0 < m)
    (hgm : g ^ m = -1) (hord : ∀ j < 2 * m, g ^ j = 1 → j = 0) :
    ∑ r ∈ Finset.range m, ‖cyclicDFT g (2 * m) (2 * r)‖ ^ 2 =
      (m : ℝ) * ((2 * m : ℝ) - 1 + 2 * ((∑ j ∈ Finset.range m, quadraticChar F (1 - (g ^ 2) ^ j) : ℤ) : ℝ)) := by
  have h := dyadic_dft_parseval_signed g hm hgm hord 1 (Or.inl rfl)
  simpa using h

/-- **Exact odd-frequency Parseval energy of the cyclic Paley DFT on `μ_{2m}`**:
`∑_{r < m} ‖ĉ(2r + 1)‖² = m * (2m - 1 - 2 * s(H²))`. -/
theorem dyadic_dft_odd_energy (g : F) {m : ℕ} (hm : 0 < m)
    (hgm : g ^ m = -1) (hord : ∀ j < 2 * m, g ^ j = 1 → j = 0) :
    ∑ r ∈ Finset.range m, ‖cyclicDFT g (2 * m) (2 * r + 1)‖ ^ 2 =
      (m : ℝ) * ((2 * m : ℝ) - 1 - 2 * ((∑ j ∈ Finset.range m, quadraticChar F (1 - (g ^ 2) ^ j) : ℤ) : ℝ)) := by
  have h := dyadic_dft_parseval_signed g hm hgm hord (-1) (Or.inr rfl)
  simp only [show (-1 : ℤ) ≠ 1 by decide, ↓reduceIte, neg_one_mul] at h
  push_cast at h ⊢
  linarith

end DyadicDFT

/-! ## 4. Five-site skew-symmetric `𝔽₃`-rank constancy (`rank = 4` identically!) -/

section SkewFiveRank

private theorem pfaffian_sq_eq_det_four (A : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hdiag : ∀ i, A i i = 0) (hskew : ∀ i j, A j i = -A i j) :
    A.det = (A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2) ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove]
  have h00 := hdiag 0; have h11 := hdiag 1; have h22 := hdiag 2; have h33 := hdiag 3
  have h10 := hskew 0 1; have h20 := hskew 0 2; have h30 := hskew 0 3
  have h21 := hskew 1 2; have h31 := hskew 1 3; have h32 := hskew 2 3
  simp [h00, h11, h22, h33, h10, h20, h30, h21, h31, h32]
  ring

private theorem zmod3_unit_sq (x : ZMod 3) (hx : x ≠ 0) : x * x = 1 := by
  revert x; decide

private theorem zmod3_eq_neg_zero (x : ZMod 3) (h : x = -x) : x = 0 := by
  revert x; decide

private theorem zmod3_cases (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = -1 := by
  revert x; decide

private theorem zmod3_unit_sum_zero (u v w : ZMod 3)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) (h : u - v + w = 0) :
    u = -v ∧ w = -v := by
  rcases zmod3_cases u with rfl | rfl | rfl <;>
    rcases zmod3_cases v with rfl | rfl | rfl <;>
    rcases zmod3_cases w with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hu
    | exact absurd rfl hv
    | exact absurd rfl hw
    | exact absurd h (by decide)
    | exact ⟨by decide, by decide⟩

/-- Pure-algebra proof that among the three principal `4 × 4` submatrices of any `5 × 5`
skew-symmetric zero-diagonal `{±1}` matrix over `ZMod 3` obtained by dropping index `2`, `3`, or `4`,
at least one has nonzero determinant. -/
theorem skew_five_f3_exists_nonzero_minor (M : Matrix (Fin 5) (Fin 5) (ZMod 3))
    (hdiag : ∀ i, M i i = 0) (hskew : ∀ i j, M j i = -M i j)
    (hoff : ∀ i j, i ≠ j → M i j ≠ 0) :
    ∃ k : Fin 5, (M.submatrix k.succAbove k.succAbove).det ≠ 0 := by
  -- Normalize row 0 by diagonal conjugation `N i j = d i * M i j * d j`, where `d 0 = 1`, `d i = M 0 i`.
  let d : Fin 5 → ZMod 3 := fun i => if i = 0 then 1 else M 0 i
  have hd_ne : ∀ i : Fin 5, d i ≠ 0 := fun i => by
    dsimp [d]; split_ifs with h
    · decide
    · exact hoff 0 i (Ne.symm h)
  have hd_sq : ∀ i : Fin 5, d i * d i = 1 := fun i => zmod3_unit_sq (d i) (hd_ne i)
  let N : Matrix (Fin 5) (Fin 5) (ZMod 3) := Matrix.of fun i j => d i * M i j * d j
  have hN_row0 : ∀ j : Fin 5, j ≠ 0 → N 0 j = 1 := fun j hj => by
    dsimp [N, d]
    simp only [↓reduceIte, hj, one_mul]
    exact hd_sq j |> fun h => by dsimp [d] at h; simpa [hj] using h
  have hN_diag : ∀ i, N i i = 0 := fun i => by dsimp [N]; rw [hdiag i]; ring
  have hN_skew : ∀ i j, N j i = -N i j := fun i j => by dsimp [N]; rw [hskew i j]; ring
  have hN_off : ∀ i j, i ≠ j → N i j ≠ 0 := fun i j hij =>
    mul_ne_zero (mul_ne_zero (hd_ne i) (hoff i j hij)) (hd_ne j)
  -- For any `k : Fin 5`, `det (N.submatrix k.succAbove k.succAbove) = (∏ i, d (k.succAbove i))² * det (M.submatrix ...)`.
  have hdet_eq : ∀ k : Fin 5,
      (N.submatrix k.succAbove k.succAbove).det = (M.submatrix k.succAbove k.succAbove).det := by
    intro k
    let D : Matrix (Fin 4) (Fin 4) (ZMod 3) := Matrix.diagonal fun i => d (k.succAbove i)
    have hmul : N.submatrix k.succAbove k.succAbove = D * M.submatrix k.succAbove k.succAbove * D := by
      ext i j
      simp [N, D, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [hmul, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    have hprod_sq : (∏ i : Fin 4, d (k.succAbove i)) * (∏ i : Fin 4, d (k.succAbove i)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun i _ => hd_sq (k.succAbove i)
    calc (∏ i : Fin 4, d (k.succAbove i)) * (M.submatrix k.succAbove k.succAbove).det *
            (∏ i : Fin 4, d (k.succAbove i))
        = ((∏ i : Fin 4, d (k.succAbove i)) * (∏ i : Fin 4, d (k.succAbove i))) *
            (M.submatrix k.succAbove k.succAbove).det := by ring
      _ = (M.submatrix k.succAbove k.succAbove).det := by rw [hprod_sq, one_mul]
  -- By contradiction, if the three principal minors dropping `4`, `3`, `2` all vanish:
  by_contra hnone
  push Not at hnone
  have h4 := hnone 4; rw [← hdet_eq 4] at h4
  have h3 := hnone 3; rw [← hdet_eq 3] at h3
  have h2 := hnone 2; rw [← hdet_eq 2] at h2
  have hpf : ∀ k : Fin 5, (N.submatrix k.succAbove k.succAbove).det = 0 →
      N (k.succAbove 0) (k.succAbove 1) * N (k.succAbove 2) (k.succAbove 3) -
      N (k.succAbove 0) (k.succAbove 2) * N (k.succAbove 1) (k.succAbove 3) +
      N (k.succAbove 0) (k.succAbove 3) * N (k.succAbove 1) (k.succAbove 2) = 0 := by
    intro k hk
    have hsq := pfaffian_sq_eq_det_four (N.submatrix k.succAbove k.succAbove)
      (fun i => hN_diag _) (fun i j => hN_skew _ _)
    rw [hk] at hsq
    exact sq_eq_zero_iff.mp hsq.symm
  have hp4 := hpf 4 h4
  have hp3 := hpf 3 h3
  have hp2 := hpf 2 h2
  have h01 : N 0 1 = 1 := hN_row0 1 (by decide)
  have h02 : N 0 2 = 1 := hN_row0 2 (by decide)
  have h03 : N 0 3 = 1 := hN_row0 3 (by decide)
  have h04 : N 0 4 = 1 := hN_row0 4 (by decide)
  change N 0 1 * N 2 3 - N 0 2 * N 1 3 + N 0 3 * N 1 2 = 0 at hp4
  change N 0 1 * N 2 4 - N 0 2 * N 1 4 + N 0 4 * N 1 2 = 0 at hp3
  change N 0 1 * N 3 4 - N 0 3 * N 1 4 + N 0 4 * N 1 3 = 0 at hp2
  rw [h01, h02, h03, one_mul, one_mul, one_mul] at hp4
  rw [h01, h02, h04, one_mul, one_mul, one_mul] at hp3
  rw [h01, h03, h04, one_mul, one_mul, one_mul] at hp2
  -- From `hp4`: `N 1 2 = -N 1 3`; from `hp3`: `N 1 2 = -N 1 4`; from `hp2`: `N 1 3 = -N 1 4`!
  have ⟨_, h12_13⟩ := zmod3_unit_sum_zero (N 2 3) (N 1 3) (N 1 2)
    (hN_off 2 3 (by decide)) (hN_off 1 3 (by decide)) (hN_off 1 2 (by decide)) hp4
  have ⟨_, h12_14⟩ := zmod3_unit_sum_zero (N 2 4) (N 1 4) (N 1 2)
    (hN_off 2 4 (by decide)) (hN_off 1 4 (by decide)) (hN_off 1 2 (by decide)) hp3
  have ⟨_, h13_14⟩ := zmod3_unit_sum_zero (N 3 4) (N 1 4) (N 1 3)
    (hN_off 3 4 (by decide)) (hN_off 1 4 (by decide)) (hN_off 1 3 (by decide)) hp2
  have heq : N 1 3 = N 1 4 := by
    have : -N 1 3 = -N 1 4 := h12_13.symm.trans h12_14
    exact neg_inj.mp this
  have hcontra : N 1 4 = -N 1 4 := heq.symm.trans h13_14
  exact hN_off 1 4 (by decide) (zmod3_eq_neg_zero (N 1 4) hcontra)

/-- **Five-site skew-symmetric `𝔽₃`-rank constancy theorem**:
EVERY `5 × 5` skew-symmetric zero-diagonal `{±1}` matrix over `ZMod 3` has `Matrix.rank M = 4`
identically (zero discriminating power for 5-site `𝔽₃`-rank when `p ≡ 3 (mod 4)`). -/
theorem skew_five_f3_rank_eq_four (M : Matrix (Fin 5) (Fin 5) (ZMod 3))
    (hdiag : ∀ i, M i i = 0) (hskew : ∀ i j, M j i = -M i j)
    (hoff : ∀ i j, i ≠ j → M i j ≠ 0) :
    M.rank = 4 := by
  have hdet0 : M.det = 0 := by
    have hT : Mᵀ = -M := by ext i j; exact hskew i j
    have h1 : M.det = -M.det := by
      calc M.det = Mᵀ.det := (Matrix.det_transpose M).symm
        _ = (-M).det := by rw [hT]
        _ = (-1 : ZMod 3) ^ 5 * M.det := by rw [Matrix.det_neg, Fintype.card_fin]
        _ = -M.det := by norm_num
    exact zmod3_eq_neg_zero M.det h1
  have hlt5 : M.rank < 5 := by
    obtain ⟨v, hv_ne, hv_zero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
    have hker_pos : 0 < Module.finrank (ZMod 3) (LinearMap.ker M.mulVecLin) := by
      refine Module.finrank_pos_iff_exists_ne_zero.mpr ?_
      exact ⟨⟨v, hv_zero⟩, fun h => hv_ne (congrArg Subtype.val h)⟩
    have hrn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_pi, Fintype.card_fin] at hrn
    change Module.finrank (ZMod 3) (LinearMap.range M.mulVecLin) < 5
    omega
  obtain ⟨k, hk⟩ := skew_five_f3_exists_nonzero_minor M hdiag hskew hoff
  have hsub_rank : (M.submatrix k.succAbove k.succAbove).rank = 4 := by
    have hunit : IsUnit (M.submatrix k.succAbove k.succAbove) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hk)
    simpa using Matrix.rank_of_isUnit _ hunit
  have hge4 : 4 ≤ M.rank := by
    rw [← hsub_rank]
    exact Matrix.rank_submatrix_le M k.succAbove k.succAbove
  omega

end SkewFiveRank

end ProximityGap.PaleyCrossRatioBarrier

#print axioms ProximityGap.PaleyCrossRatioBarrier.quartic_charSum_eq_legendreTrace
#print axioms ProximityGap.PaleyCrossRatioBarrier.sum_unsignedCrossRatioCount
#print axioms ProximityGap.PaleyCrossRatioBarrier.unsigned_crossRatio_energy_ge
#print axioms ProximityGap.PaleyCrossRatioBarrier.unsigned_cauchy_schwarz_cannot_beat_hasse
#print axioms ProximityGap.PaleyCrossRatioBarrier.dyadic_dft_even_energy
#print axioms ProximityGap.PaleyCrossRatioBarrier.dyadic_dft_odd_energy
#print axioms ProximityGap.PaleyCrossRatioBarrier.skew_five_f3_exists_nonzero_minor
#print axioms ProximityGap.PaleyCrossRatioBarrier.skew_five_f3_rank_eq_four

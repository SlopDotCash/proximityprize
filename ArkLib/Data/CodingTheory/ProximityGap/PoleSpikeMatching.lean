/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WindowFiberPencil

/-!
# Pole spike-matching (#371, P bricks): first-row pole-stratum bounds

For pole-stratum stacks — `ℓ₀ = m_Z·ℓ̃₀` vanishing on a nonempty pole set
`Z ⊆ D`, the row free ("spiked") at its poles — the window analysis gains
pointwise constraints the polynomial identity cannot see.  This file proves the
first-row (k = 1, `n = 3w`) pole laws:

* `witness_defect_dichotomy` — the stratum-agnostic core: every bad `γ` yields
  an agreement set `S` (`|S| ≥ n−w`), a constant codeword value `p` with
  pointwise agreement on `S`, and either the **zero-class** identity
  `R₀ℓ₁ + γR₁ℓ₀ = p·ℓ₀ℓ₁` or a nonzero-constant defect
  `… = g·m_S` with `|S| = n − w` (no reducedness assumed);
* `pole_witness_contains_poles` (P1) — in the defect branch, every witness
  contains every pole: at a pole all of `A`, `B`, `L` vanish, so `m_S` must;
* `pole_misaligned_pins_gamma` (P2) — if the witness contains two poles where
  the second row differs, the spike-matching equations pin
  `γ·(u₁ z − u₁ z') = u₀ z' − u₀ z`: a misaligned pole pair leaves at most ONE
  defect-bad scalar, and none when the first row misaligns alone.

Probe record: `probe_wb371_extremal_anatomy.py` — the deep-window extremal's
bad scalars decompose exactly into the zero-class (`γ = 0`), per-orbit
spike-matching solutions, and the both-orbit solution; alignment classes on the
pole set are the adversary's degrees of freedom (σ-orbit alignment).
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section PoleBricks

variable {dom : Fin n ↪ F} {w : ℕ}
variable {u₀ u₁ : Fin n → F} {ℓ₀ R₀ ℓ₁ R₁ : F[X]}

open Classical in
/-- **The stratum-agnostic defect dichotomy** (k = 1, first window row).  Every
bad `γ` yields an agreement set with pointwise codeword value `p`, and the
defect polynomial is either zero (the zero-class) or a nonzero constant multiple
of the vanishing polynomial of an exactly-`(n−w)`-point witness.  No
reducedness or coprimality is assumed. -/
theorem witness_defect_dichotomy
    (hw : 1 ≤ w) (hn : n = 3 * w)
    (hrel₀ : ∀ i, ℓ₀.eval (dom i) * u₀ i = R₀.eval (dom i))
    (hrel₁ : ∀ i, ℓ₁.eval (dom i) * u₁ i = R₁.eval (dom i))
    (hdℓ₀ : ℓ₀.natDegree ≤ w) (hdR₀ : R₀.natDegree ≤ w)
    (hdℓ₁ : ℓ₁.natDegree ≤ w) (hdR₁ : R₁.natDegree ≤ w)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w) {γ : F}
    (hbad : mcaEvent (F := F)
      ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ) :
    ∃ (S : Finset (Fin n)) (p : F), (n - w : ℕ) ≤ S.card ∧
      (∀ i ∈ S, p = u₀ i + γ * u₁ i) ∧
      (R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁) = 0 ∨
        ∃ g : F, g ≠ 0 ∧ S.card + w = n ∧
          R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁)
            = C g * vanishingPoly dom S) := by
  obtain ⟨S, hsz, ⟨wc, hwc, hag⟩, -⟩ := hbad
  obtain ⟨P, hPdeg, rfl⟩ := hwc
  have hPC : P = C (P.coeff 0) := by
    by_cases hP0 : P = 0
    · simp [hP0]
    · refine Polynomial.eq_C_of_natDegree_le_zero ?_
      have hnd : P.natDegree < 1 :=
        (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr (by exact_mod_cast hPdeg)
      omega
  set p := P.coeff 0 with hpdef
  have hagree : ∀ i ∈ S, p = u₀ i + γ * u₁ i := by
    intro i hi
    have hwci := hag i hi
    rw [hPC] at hwci
    simpa [smul_eq_mul] using hwci
  have hScard : n - w ≤ S.card := by
    have h1 : ((n - w : ℕ) : ℝ≥0) ≤ (S.card : ℝ≥0) := by
      have hnw : ((n - w : ℕ) : ℝ≥0) = (n : ℝ≥0) - (w : ℝ≥0) := by
        rw [Nat.cast_tsub]
      have hδ1 : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)
          = (Fintype.card (Fin n) : ℝ≥0) - δ * (Fintype.card (Fin n) : ℝ≥0) := by
        rw [tsub_mul, one_mul]
      have hcardn : (Fintype.card (Fin n) : ℝ≥0) = (n : ℝ≥0) := by
        rw [Fintype.card_fin]
      calc ((n - w : ℕ) : ℝ≥0) = (n : ℝ≥0) - (w : ℝ≥0) := hnw
        _ ≤ (n : ℝ≥0) - δ * (Fintype.card (Fin n) : ℝ≥0) := by
            exact tsub_le_tsub_left (by rw [hcardn] at hδn ⊢; exact hδn) _
        _ = (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) := by
            rw [hδ1, hcardn]
        _ ≤ (S.card : ℝ≥0) := hsz
    exact_mod_cast h1
  set Φ : F[X] := R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁) with hΦdef
  rcases eq_or_ne Φ 0 with hΦ0 | hΦne
  · exact ⟨S, p, hScard, hagree, Or.inl hΦ0⟩
  -- defect branch: m_S ∣ Φ, degree forces a constant quotient
  have hΦeval : ∀ i ∈ S, Φ.eval (dom i) = 0 := by
    intro i hi
    have h1 := hrel₀ i
    have h2 := hrel₁ i
    have h3 := hagree i hi
    simp only [hΦdef, eval_sub, eval_add, eval_mul, eval_C]
    rw [← h1, ← h2]
    linear_combination (-(ℓ₀.eval (dom i) * ℓ₁.eval (dom i))) * h3
  have hdvd : vanishingPoly dom S ∣ Φ := by
    rw [vanishingPoly]
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro i hi j hj hij
      exact isCoprime_X_sub_C_of_isUnit_sub
        (Ne.isUnit (sub_ne_zero.mpr (fun h => hij (dom.injective h))))
    · intro i hi
      rw [Polynomial.dvd_iff_isRoot]
      exact hΦeval i hi
  have hΦdeg : Φ.natDegree ≤ 2 * w := by
    have t1 : (R₀ * ℓ₁).natDegree ≤ 2 * w :=
      le_trans natDegree_mul_le (by omega)
    have t2 : (C γ * (R₁ * ℓ₀)).natDegree ≤ 2 * w := by
      refine le_trans natDegree_mul_le ?_
      have h2 : (R₁ * ℓ₀).natDegree ≤ 2 * w := le_trans natDegree_mul_le (by omega)
      have := natDegree_C γ
      omega
    have t3 : (C p * (ℓ₀ * ℓ₁)).natDegree ≤ 2 * w := by
      refine le_trans natDegree_mul_le ?_
      have h2 : (ℓ₀ * ℓ₁).natDegree ≤ 2 * w := le_trans natDegree_mul_le (by omega)
      have := natDegree_C p
      omega
    rw [hΦdef]
    exact le_trans (natDegree_sub_le _ _)
      (max_le (le_trans (natDegree_add_le _ _) (max_le t1 t2)) t3)
  have hSle : S.card ≤ 2 * w := by
    have h1 : (vanishingPoly dom S).natDegree ≤ Φ.natDegree :=
      Polynomial.natDegree_le_of_dvd hdvd hΦne
    rw [vanishingPoly_natDegree] at h1
    omega
  obtain ⟨cq, hcq⟩ := hdvd
  have hcqne : cq ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hcq
    exact hΦne hcq
  have hcqdeg : cq.natDegree = 0 := by
    have hmul := Polynomial.natDegree_mul (vanishingPoly_ne_zero dom S) hcqne
    rw [← hcq, vanishingPoly_natDegree] at hmul
    omega
  refine ⟨S, p, hScard, hagree, Or.inr ⟨cq.coeff 0, ?_, by omega, ?_⟩⟩
  · intro h0
    apply hcqne
    rw [Polynomial.eq_C_of_natDegree_le_zero (le_of_eq hcqdeg), h0, map_zero]
  · calc R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁)
        = vanishingPoly dom S * cq := by rw [← hΦdef]; exact hcq
      _ = C (cq.coeff 0) * vanishingPoly dom S := by
          conv_lhs => rw [Polynomial.eq_C_of_natDegree_le_zero (le_of_eq hcqdeg)]
          ring

/-- **P1: defect witnesses contain every pole.**  If the defect is a nonzero
constant multiple of `m_S` and all of `R₀`, `ℓ₀` vanish at a domain pole `z`,
then `z ∈ S`. -/
theorem pole_witness_contains_poles
    {γ g p : F} {S : Finset (Fin n)} (hg : g ≠ 0)
    (hid : R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁)
      = C g * vanishingPoly dom S)
    {z : Fin n} (hR₀z : R₀.eval (dom z) = 0) (hℓ₀z : ℓ₀.eval (dom z) = 0) :
    z ∈ S := by
  have hev := congrArg (Polynomial.eval (dom z)) hid
  simp only [eval_sub, eval_add, eval_mul, eval_C, hR₀z, hℓ₀z,
    zero_mul, mul_zero, add_zero, sub_zero, zero_add, zero_sub] at hev
  -- hev : 0 = g * (vanishingPoly dom S).eval (dom z)
  have hvz : (vanishingPoly dom S).eval (dom z) = 0 := by
    rcases mul_eq_zero.mp hev.symm with h | h
    · exact absurd h hg
    · exact h
  -- a vanishing polynomial vanishes at dom z iff z ∈ S (dom injective)
  rw [vanishingPoly, eval_prod, Finset.prod_eq_zero_iff] at hvz
  obtain ⟨j, hj, hjz⟩ := hvz
  simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hjz
  exact dom.injective hjz ▸ hj

/-- **P2: a misaligned pole pair pins γ.**  If the agreement set contains two
indices where the rows misalign, the pointwise codeword value cancels and
`γ·(u₁ z − u₁ z') = u₀ z' − u₀ z`.  In particular two poles with equal second
row but different first row admit no bad scalar through any witness containing
both, and a genuinely misaligned pair determines `γ` uniquely. -/
theorem pole_misaligned_pins_gamma
    {γ p : F} {S : Finset (Fin n)}
    (hagree : ∀ i ∈ S, p = u₀ i + γ * u₁ i)
    {z z' : Fin n} (hz : z ∈ S) (hz' : z' ∈ S) :
    γ * (u₁ z - u₁ z') = u₀ z' - u₀ z := by
  have h1 := hagree z hz
  have h2 := hagree z' hz'
  linear_combination h2 - h1

/-- The unique-γ corollary: with `u₁ z ≠ u₁ z'`, the pinned value is explicit. -/
theorem pole_misaligned_gamma_eq
    {γ p : F} {S : Finset (Fin n)}
    (hagree : ∀ i ∈ S, p = u₀ i + γ * u₁ i)
    {z z' : Fin n} (hz : z ∈ S) (hz' : z' ∈ S) (hmis : u₁ z ≠ u₁ z') :
    γ = (u₀ z' - u₀ z) / (u₁ z - u₁ z') := by
  have h := pole_misaligned_pins_gamma hagree hz hz'
  rw [eq_div_iff (sub_ne_zero.mpr hmis)]
  exact h

end PoleBricks

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.witness_defect_dichotomy
#print axioms ProximityGap.WBPencil.pole_witness_contains_poles
#print axioms ProximityGap.WBPencil.pole_misaligned_pins_gamma
#print axioms ProximityGap.WBPencil.pole_misaligned_gamma_eq

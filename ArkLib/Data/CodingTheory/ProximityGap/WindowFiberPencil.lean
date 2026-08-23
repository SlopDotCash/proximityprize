/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SplitPencilBound
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilRationalReduction

/-!
# The window fiber–pencil theorem (#371, G2 brick): stratum-G first-row bound

**For doubly-rational stacks with reduced, coprime, domain-nonvanishing locators at
the first window row (`n = 3w`, `k = 1`), the bad-scalar count is at most
`n/w`**.  The old `n/w + 1` statement remains as a compatibility wrapper.

The fiber linearization:
* `witness_division_identity` — every bad `γ` yields an **exact division identity**
  `R₀ℓ₁ + γ·R₁ℓ₀ − p·ℓ₀ℓ₁ = g·m_S` with `g ∈ F˟` and `S` the agreement set: the
  defect polynomial vanishes on `S`, has degree `≤ 2w ≤ |S|`, so it is a constant
  multiple of the vanishing polynomial; the zero-class `Φ = 0` would force
  `ℓ₀ ∣ R₀ℓ₁`, impossible for reduced coprime locators of positive degree;
* `witness_compl_splitMember` — multiplying the rearranged identity
  `g·m_S − R₀ℓ₁ = ℓ₀·(γR₁ − pℓ₁)` by the complement `m̂ = m_{Sᶜ}` (so
  `m_S·m̂ = m_D`) and cross-multiplying with a base witness **eliminates γ**: every
  witness complement is a `SplitMember` of the pencil `⟨m̂₀, ℓ₀⟩`;
* `witness_set_injective` — distinct bad scalars have distinct agreement sets
  (equal sets force `ℓ₁ ∣ C(γ−γ')` through reducedness of the second row);
* **`stratumG_firstRow_badScalars_card_le_div`** — the exact-size split-pencil
  bound caps the count at `n/w`.

Probe record: `probe_fiber_census.py` (f*(12,4) = 3 = n/w by a μ₁₂ partition);
`probe_deep_window.py` (G×G random max bad 0–2 at the tested window scales);
the μ_w-coset pencil `{X^w − a : aⁿᐟʷ = 1}` is the extremal configuration.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- A domain-nonvanishing polynomial is coprime to every vanishing polynomial. -/
theorem isCoprime_vanishingPoly (dom : Fin n ↪ F) {ℓ : F[X]}
    (h : ∀ i, ℓ.eval (dom i) ≠ 0) (T : Finset (Fin n)) :
    IsCoprime ℓ (vanishingPoly dom T) := by
  rw [vanishingPoly]
  refine IsCoprime.prod_right fun i _ => ?_
  have hnd : ¬ (X - C (dom i) ∣ ℓ) := by
    rw [Polynomial.dvd_iff_isRoot]
    exact fun hr => h i hr
  exact ((Polynomial.irreducible_X_sub_C (dom i)).coprime_iff_not_dvd.mpr hnd).symm

/-- Vanishing polynomials of complementary sets multiply to the domain polynomial. -/
theorem vanishingPoly_mul_compl (dom : Fin n ↪ F) (S : Finset (Fin n)) :
    vanishingPoly dom S * vanishingPoly dom Sᶜ = vanishingPoly dom Finset.univ := by
  rw [vanishingPoly, vanishingPoly, vanishingPoly,
    ← Finset.prod_union disjoint_compl_right, Finset.union_compl]

section FiberPencil

variable {dom : Fin n ↪ F} {w : ℕ}
variable {u₀ u₁ : Fin n → F} {ℓ₀ R₀ ℓ₁ R₁ : F[X]}

open Classical in
/-- **The division identity of a bad scalar** (k = 1, first window row `n = 3w`).
Every bad `γ` produces an agreement set `S` with `|S| = n − w` and a nonzero
constant `g` with `R₀ℓ₁ + γ·R₁ℓ₀ − p·ℓ₀ℓ₁ = g·m_S` for some field element `p`. -/
theorem witness_division_identity
    (hw : 1 ≤ w) (hn : n = 3 * w)
    (hrel₀ : ∀ i, ℓ₀.eval (dom i) * u₀ i = R₀.eval (dom i))
    (hrel₁ : ∀ i, ℓ₁.eval (dom i) * u₁ i = R₁.eval (dom i))
    (hdℓ₀ : ℓ₀.natDegree = w) (hdR₀ : R₀.natDegree ≤ w)
    (hdℓ₁ : ℓ₁.natDegree ≤ w) (hdR₁ : R₁.natDegree ≤ w)
    (hcop₀ : IsCoprime R₀ ℓ₀) (hcopℓ : IsCoprime ℓ₀ ℓ₁)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w) {γ : F}
    (hbad : mcaEvent (F := F)
      ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ) :
    ∃ (S : Finset (Fin n)) (g p : F), g ≠ 0 ∧ S.card + w = n ∧
      R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁)
        = C g * vanishingPoly dom S := by
  obtain ⟨S, hsz, ⟨wc, hwc, hag⟩, -⟩ := hbad
  obtain ⟨P, hPdeg, rfl⟩ := hwc
  -- the codeword is a constant
  have hPC : P = C (P.coeff 0) := by
    by_cases hP0 : P = 0
    · simp [hP0]
    · refine Polynomial.eq_C_of_natDegree_le_zero ?_
      have hnd : P.natDegree < 1 :=
        (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr (by exact_mod_cast hPdeg)
      omega
  set p := P.coeff 0 with hpdef
  -- size: n − w ≤ |S|
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
  -- Φ vanishes on S
  have hΦeval : ∀ i ∈ S, Φ.eval (dom i) = 0 := by
    intro i hi
    have h1 := hrel₀ i
    have h2 := hrel₁ i
    have h3 : p = u₀ i + γ * u₁ i := by
      have hwci := hag i hi
      rw [hPC] at hwci
      simpa [smul_eq_mul] using hwci
    simp only [hΦdef, eval_sub, eval_add, eval_mul, eval_C]
    rw [← h1, ← h2]
    linear_combination (-(ℓ₀.eval (dom i) * ℓ₁.eval (dom i))) * h3
  -- m_S ∣ Φ
  have hdvd : vanishingPoly dom S ∣ Φ := by
    rw [vanishingPoly]
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro i hi j hj hij
      exact isCoprime_X_sub_C_of_isUnit_sub
        (Ne.isUnit (sub_ne_zero.mpr (fun h => hij (dom.injective h))))
    · intro i hi
      rw [Polynomial.dvd_iff_isRoot]
      exact hΦeval i hi
  -- the zero-class is impossible
  have hℓ₀ne : ℓ₀ ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hdℓ₀
    omega
  have hΦne : Φ ≠ 0 := by
    intro hΦ0
    have h0 : R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁) = 0 := by
      rw [← hΦdef]
      exact hΦ0
    have hdvd₀ : ℓ₀ ∣ R₀ * ℓ₁ :=
      ⟨C p * ℓ₁ - C γ * R₁, by linear_combination h0⟩
    have hcop : IsCoprime ℓ₀ (R₀ * ℓ₁) := IsCoprime.mul_right hcop₀.symm hcopℓ
    obtain ⟨a, b, hab⟩ := hcop
    have hone : ℓ₀ ∣ 1 := by
      rw [← hab]
      exact dvd_add (Dvd.intro a (mul_comm ℓ₀ a ▸ rfl))
        (Dvd.dvd.mul_left hdvd₀ b)
    have hunit : IsUnit ℓ₀ := isUnit_of_dvd_one hone
    have := Polynomial.natDegree_eq_zero_of_isUnit hunit
    omega
  -- degree bookkeeping: deg Φ ≤ 2w, so |S| = n − w = 2w and the quotient is constant
  have hΦdeg : Φ.natDegree ≤ 2 * w := by
    have hCγ : (C γ : F[X]).natDegree = 0 := natDegree_C γ
    have hCp : (C p : F[X]).natDegree = 0 := natDegree_C p
    have t1 : (R₀ * ℓ₁).natDegree ≤ 2 * w :=
      le_trans natDegree_mul_le (by omega)
    have t2 : (C γ * (R₁ * ℓ₀)).natDegree ≤ 2 * w := by
      refine le_trans natDegree_mul_le ?_
      have : (R₁ * ℓ₀).natDegree ≤ 2 * w := le_trans natDegree_mul_le (by omega)
      omega
    have t3 : (C p * (ℓ₀ * ℓ₁)).natDegree ≤ 2 * w := by
      refine le_trans natDegree_mul_le ?_
      have : (ℓ₀ * ℓ₁).natDegree ≤ 2 * w := le_trans natDegree_mul_le (by omega)
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
  refine ⟨S, cq.coeff 0, p, ?_, by omega, ?_⟩
  · intro h0
    apply hcqne
    rw [Polynomial.eq_C_of_natDegree_le_zero (le_of_eq hcqdeg), h0, map_zero]
  · calc R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁)
        = vanishingPoly dom S * cq := by rw [← hΦdef]; exact hcq
      _ = C (cq.coeff 0) * vanishingPoly dom S := by
          conv_lhs => rw [Polynomial.eq_C_of_natDegree_le_zero (le_of_eq hcqdeg)]
          ring

/-- The rearranged identity, complement-multiplied: γ is confined to the
`ℓ₀`-multiple. -/
private theorem key_identity {γ g p : F} {S : Finset (Fin n)}
    (hid : R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁)
      = C g * vanishingPoly dom S) :
    R₀ * ℓ₁ * vanishingPoly dom Sᶜ
      = C g * vanishingPoly dom Finset.univ
        - ℓ₀ * ((C γ * R₁ - C p * ℓ₁) * vanishingPoly dom Sᶜ) := by
  have hmm := vanishingPoly_mul_compl dom S
  linear_combination (vanishingPoly dom Sᶜ) * hid + C g * hmm

open Classical in
/-- **The pencil membership of witness complements.**  Cross-multiplying the key
identities of two bad scalars eliminates `γ`: the complement of any witness is a
`SplitMember` of the pencil through the base complement and `ℓ₀`. -/
theorem witness_compl_splitMember
    (hG₀ : ∀ i, ℓ₀.eval (dom i) ≠ 0) (hcop₀ : IsCoprime R₀ ℓ₀)
    (hcopℓ : IsCoprime ℓ₀ ℓ₁) (hdℓ₀ : 1 ≤ ℓ₀.natDegree)
    {γ₀ g₀ p₀ : F} {S₀ : Finset (Fin n)} (hg₀ : g₀ ≠ 0)
    (hid₀ : R₀ * ℓ₁ + C γ₀ * (R₁ * ℓ₀) - C p₀ * (ℓ₀ * ℓ₁)
      = C g₀ * vanishingPoly dom S₀)
    (hS₀ : S₀.card + ℓ₀.natDegree = n)
    {γ g p : F} {S : Finset (Fin n)}
    (hid : R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁)
      = C g * vanishingPoly dom S)
    (hS : S.card + ℓ₀.natDegree = n) :
    SplitMember dom (vanishingPoly dom S₀ᶜ) ℓ₀ Sᶜ := by
  have hkey := key_identity (dom := dom) hid
  have hkey₀ := key_identity (dom := dom) hid₀
  -- cross-multiplied: R₀ℓ₁ · (g₀·m̂ − g·m̂₀) = ℓ₀ · (g·E₀ − g₀·E)
  have hcross : R₀ * ℓ₁ *
      (C g₀ * vanishingPoly dom Sᶜ - C g * vanishingPoly dom S₀ᶜ)
      = ℓ₀ * (C g * ((C γ₀ * R₁ - C p₀ * ℓ₁) * vanishingPoly dom S₀ᶜ)
          - C g₀ * ((C γ * R₁ - C p * ℓ₁) * vanishingPoly dom Sᶜ)) := by
    linear_combination C g₀ * hkey - C g * hkey₀
  have hcopRL : IsCoprime ℓ₀ (R₀ * ℓ₁) := IsCoprime.mul_right hcop₀.symm hcopℓ
  have hdvd2 : ℓ₀ ∣ C g₀ * vanishingPoly dom Sᶜ - C g * vanishingPoly dom S₀ᶜ := by
    refine hcopRL.dvd_of_dvd_mul_left ?_
    exact ⟨C g * ((C γ₀ * R₁ - C p₀ * ℓ₁) * vanishingPoly dom S₀ᶜ)
        - C g₀ * ((C γ * R₁ - C p * ℓ₁) * vanishingPoly dom Sᶜ),
      by linear_combination hcross⟩
  obtain ⟨e, he⟩ := hdvd2
  -- the quotient is a constant by degrees
  have hℓ₀ne : ℓ₀ ≠ 0 := fun h0 => by
    rw [h0, natDegree_zero] at hdℓ₀
    omega
  have heC : e = C (e.coeff 0) := by
    rcases eq_or_ne e 0 with h0 | hne
    · simp [h0]
    · refine Polynomial.eq_C_of_natDegree_le_zero ?_
      have hDdeg : (C g₀ * vanishingPoly dom Sᶜ
          - C g * vanishingPoly dom S₀ᶜ).natDegree ≤ ℓ₀.natDegree := by
        have d1 : (C g₀ * vanishingPoly dom Sᶜ).natDegree ≤ ℓ₀.natDegree := by
          refine le_trans (natDegree_C_mul_le _ _) ?_
          rw [vanishingPoly_natDegree, Finset.card_compl, Fintype.card_fin]
          omega
        have d2 : (C g * vanishingPoly dom S₀ᶜ).natDegree ≤ ℓ₀.natDegree := by
          refine le_trans (natDegree_C_mul_le _ _) ?_
          rw [vanishingPoly_natDegree, Finset.card_compl, Fintype.card_fin]
          omega
        exact le_trans (natDegree_sub_le _ _) (max_le d1 d2)
      have hmul := Polynomial.natDegree_mul hℓ₀ne hne
      rw [← he] at hmul
      omega
  exact ⟨g₀, hg₀, g, e.coeff 0, by linear_combination he + ℓ₀ * heC⟩

open Classical in
/-- **γ-injectivity**: two bad scalars sharing an agreement set coincide —
equal sets force `ℓ₁ ∣ C(γ₁ − γ₂)` through reducedness of the second row. -/
theorem witness_gamma_injective
    (hG₀ : ∀ i, ℓ₀.eval (dom i) ≠ 0)
    (hdℓ₀ : 1 ≤ ℓ₀.natDegree) (hdℓ₁ : 1 ≤ ℓ₁.natDegree)
    (hcop₁ : IsCoprime R₁ ℓ₁)
    {γ₁ g₁ p₁ γ₂ g₂ p₂ : F} {S : Finset (Fin n)}
    (hid₁ : R₀ * ℓ₁ + C γ₁ * (R₁ * ℓ₀) - C p₁ * (ℓ₀ * ℓ₁)
      = C g₁ * vanishingPoly dom S)
    (hid₂ : R₀ * ℓ₁ + C γ₂ * (R₁ * ℓ₀) - C p₂ * (ℓ₀ * ℓ₁)
      = C g₂ * vanishingPoly dom S) :
    γ₁ = γ₂ := by
  by_contra hne
  have hℓ₀ne : ℓ₀ ≠ 0 := fun h0 => by
    rw [h0, natDegree_zero] at hdℓ₀
    omega
  have hsub : (C γ₁ - C γ₂) * (R₁ * ℓ₀) - (C p₁ - C p₂) * (ℓ₀ * ℓ₁)
      = (C g₁ - C g₂) * vanishingPoly dom S := by
    linear_combination hid₁ - hid₂
  have hdvdg : ℓ₀ ∣ (C g₁ - C g₂) * vanishingPoly dom S :=
    ⟨(C γ₁ - C γ₂) * R₁ - (C p₁ - C p₂) * ℓ₁, by linear_combination -hsub⟩
  have hgeq : g₁ = g₂ := by
    have h1 : ℓ₀ ∣ C g₁ - C g₂ :=
      (isCoprime_vanishingPoly dom hG₀ S).dvd_of_dvd_mul_right hdvdg
    by_contra hgne
    have hCne : (C g₁ - C g₂ : F[X]) ≠ 0 := by
      rw [← C_sub]
      exact C_ne_zero.mpr (sub_ne_zero.mpr hgne)
    have hdeg := Polynomial.natDegree_le_of_dvd h1 hCne
    have hC0 : (C g₁ - C g₂ : F[X]).natDegree = 0 := by
      rw [← C_sub]
      exact natDegree_C _
    omega
  subst hgeq
  have hcancel : (C γ₁ - C γ₂) * R₁ = (C p₁ - C p₂) * ℓ₁ := by
    have h2 : ((C γ₁ - C γ₂) * R₁) * ℓ₀ = ((C p₁ - C p₂) * ℓ₁) * ℓ₀ := by
      linear_combination hsub
    exact mul_right_cancel₀ hℓ₀ne h2
  have hdvd₁ : ℓ₁ ∣ (C γ₁ - C γ₂) * R₁ :=
    ⟨C p₁ - C p₂, by linear_combination hcancel⟩
  have h3 : ℓ₁ ∣ C γ₁ - C γ₂ := hcop₁.symm.dvd_of_dvd_mul_right hdvd₁
  have hCγne : (C γ₁ - C γ₂ : F[X]) ≠ 0 := by
    rw [← C_sub]
    exact C_ne_zero.mpr (sub_ne_zero.mpr hne)
  have hdeg := Polynomial.natDegree_le_of_dvd h3 hCγne
  have hC0 : (C γ₁ - C γ₂ : F[X]).natDegree = 0 := by
    rw [← C_sub]
    exact natDegree_C _
  omega

omit [DecidableEq F] in
open Classical in
/-- **Exact stratum-G first-row bound (G2 capstone).**  For a doubly-rational stack
with reduced, mutually coprime locators — `ℓ₀` of exact degree `w` nonvanishing on
the domain, `ℓ₁` nonconstant — at the first window row `n = 3w` (`k = 1`) and any
radius `δ·n ≤ w`, the bad-scalar count is at most `n/w`.  The witness complements
all have exact size `w`, so the small-member exception in the general split-pencil
bound does not appear. -/
theorem stratumG_firstRow_badScalars_card_le_div
    (dom : Fin n ↪ F) {w : ℕ} (hw : 1 ≤ w) (hn : n = 3 * w)
    {u₀ u₁ : Fin n → F} {ℓ₀ R₀ ℓ₁ R₁ : F[X]}
    (hrel₀ : ∀ i, ℓ₀.eval (dom i) * u₀ i = R₀.eval (dom i))
    (hrel₁ : ∀ i, ℓ₁.eval (dom i) * u₁ i = R₁.eval (dom i))
    (hdℓ₀ : ℓ₀.natDegree = w) (hdR₀ : R₀.natDegree ≤ w)
    (hdℓ₁ : ℓ₁.natDegree ≤ w) (hdR₁ : R₁.natDegree ≤ w)
    (hℓ₁pos : 1 ≤ ℓ₁.natDegree)
    (hG₀ : ∀ i, ℓ₀.eval (dom i) ≠ 0)
    (hcop₀ : IsCoprime R₀ ℓ₀) (hcop₁ : IsCoprime R₁ ℓ₁) (hcopℓ : IsCoprime ℓ₀ ℓ₁)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ n / w := by
  classical
  set badSet := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
    ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)
    with hbadDef
  rcases Finset.eq_empty_or_nonempty badSet with h0 | hne
  · rw [h0]
    simp
  obtain ⟨γ₀, hγ₀⟩ := hne
  have hdata : ∀ γ ∈ badSet, ∃ (S : Finset (Fin n)) (g p : F), g ≠ 0 ∧
      S.card + w = n ∧
      R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁) = C g * vanishingPoly dom S :=
    fun γ hγ => witness_division_identity hw hn hrel₀ hrel₁ hdℓ₀ hdR₀ hdℓ₁ hdR₁
      hcop₀ hcopℓ hδn (Finset.mem_filter.mp hγ).2
  choose Sf gf pf hgne hcard hid using hdata
  have hinj : ∀ γ₁ (h₁ : γ₁ ∈ badSet) γ₂ (h₂ : γ₂ ∈ badSet),
      Sf γ₁ h₁ = Sf γ₂ h₂ → γ₁ = γ₂ := by
    intro γ₁ h₁ γ₂ h₂ hSeq
    have e₂ := hid γ₂ h₂
    rw [← hSeq] at e₂
    exact witness_gamma_injective hG₀ (by rw [hdℓ₀]; exact hw) hℓ₁pos hcop₁
      (hid γ₁ h₁) e₂
  set 𝒯 := badSet.attach.image
    (fun x : {γ // γ ∈ badSet} => (Sf x.1 x.2)ᶜ) with h𝒯
  have hmem : ∀ T ∈ 𝒯, SplitMember dom (vanishingPoly dom (Sf γ₀ hγ₀)ᶜ) ℓ₀ T := by
    intro T hT
    rw [h𝒯, Finset.mem_image] at hT
    obtain ⟨⟨γ, hγ⟩, -, rfl⟩ := hT
    exact witness_compl_splitMember hG₀ hcop₀ hcopℓ (by rw [hdℓ₀]; exact hw)
      (hgne γ₀ hγ₀) (hid γ₀ hγ₀) (by rw [hdℓ₀]; exact hcard γ₀ hγ₀)
      (hid γ hγ) (by rw [hdℓ₀]; exact hcard γ hγ)
  have hlarge : ∀ T ∈ 𝒯, ℓ₀.natDegree ≤ T.card := by
    intro T hT
    rw [h𝒯, Finset.mem_image] at hT
    obtain ⟨⟨γ, hγ⟩, -, rfl⟩ := hT
    have hc := hcard γ hγ
    rw [hdℓ₀, Finset.card_compl, Fintype.card_fin]
    exact Nat.le_sub_of_add_le (by rw [Nat.add_comm, hc])
  have hG1 := pencil_split_card_le_of_degree_le_card
    (f := vanishingPoly dom (Sf γ₀ hγ₀)ᶜ)
    (by rw [hdℓ₀]; exact hw) hG₀ 𝒯 hmem hlarge
  rw [hdℓ₀] at hG1
  have hinjOn : Set.InjOn (fun x : {γ // γ ∈ badSet} => (Sf x.1 x.2)ᶜ)
      badSet.attach := by
    intro x _ y _ hxy
    have hSS : Sf x.1 x.2 = Sf y.1 y.2 := by
      have h2 := congrArg (fun s : Finset (Fin n) => sᶜ) hxy
      simpa using h2
    exact Subtype.ext (hinj _ _ _ _ hSS)
  have hcardeq : 𝒯.card = badSet.card := by
    rw [h𝒯, Finset.card_image_of_injOn hinjOn, Finset.card_attach]
  rw [← hcardeq]
  exact hG1

omit [DecidableEq F] in
open Classical in
/-- Compatibility wrapper for the older G2 statement.  The exact theorem is
`stratumG_firstRow_badScalars_card_le_div`. -/
theorem stratumG_firstRow_badScalars_card_le
    (dom : Fin n ↪ F) {w : ℕ} (hw : 1 ≤ w) (hn : n = 3 * w)
    {u₀ u₁ : Fin n → F} {ℓ₀ R₀ ℓ₁ R₁ : F[X]}
    (hrel₀ : ∀ i, ℓ₀.eval (dom i) * u₀ i = R₀.eval (dom i))
    (hrel₁ : ∀ i, ℓ₁.eval (dom i) * u₁ i = R₁.eval (dom i))
    (hdℓ₀ : ℓ₀.natDegree = w) (hdR₀ : R₀.natDegree ≤ w)
    (hdℓ₁ : ℓ₁.natDegree ≤ w) (hdR₁ : R₁.natDegree ≤ w)
    (hℓ₁pos : 1 ≤ ℓ₁.natDegree)
    (hG₀ : ∀ i, ℓ₀.eval (dom i) ≠ 0)
    (hcop₀ : IsCoprime R₀ ℓ₀) (hcop₁ : IsCoprime R₁ ℓ₁) (hcopℓ : IsCoprime ℓ₀ ℓ₁)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ n / w + 1 := by
  exact le_trans
    (stratumG_firstRow_badScalars_card_le_div (dom := dom) hw hn hrel₀ hrel₁ hdℓ₀ hdR₀
      hdℓ₁ hdR₁ hℓ₁pos hG₀ hcop₀ hcop₁ hcopℓ hδn)
    (Nat.le_succ _)

open Classical in
/-- **Sharp first-row split-pencil bound.**  In the `n = 3w`, `k = 1` window row,
the witness complements all have exact size `w`; hence the small-member exception
in `pencil_split_card_le` cannot occur and the count is at most `n / w`. -/
theorem stratumG_firstRow_badScalars_card_le_sharp
    (dom : Fin n ↪ F) {w : ℕ} (hw : 1 ≤ w) (hn : n = 3 * w)
    {u₀ u₁ : Fin n → F} {ℓ₀ R₀ ℓ₁ R₁ : F[X]}
    (hrel₀ : ∀ i, ℓ₀.eval (dom i) * u₀ i = R₀.eval (dom i))
    (hrel₁ : ∀ i, ℓ₁.eval (dom i) * u₁ i = R₁.eval (dom i))
    (hdℓ₀ : ℓ₀.natDegree = w) (hdR₀ : R₀.natDegree ≤ w)
    (hdℓ₁ : ℓ₁.natDegree ≤ w) (hdR₁ : R₁.natDegree ≤ w)
    (hℓ₁pos : 1 ≤ ℓ₁.natDegree)
    (hG₀ : ∀ i, ℓ₀.eval (dom i) ≠ 0)
    (hcop₀ : IsCoprime R₀ ℓ₀) (hcop₁ : IsCoprime R₁ ℓ₁) (hcopℓ : IsCoprime ℓ₀ ℓ₁)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ n / w := by
  classical
  set badSet := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
    ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)
    with hbadDef
  rcases Finset.eq_empty_or_nonempty badSet with h0 | hne
  · rw [h0]
    simp
  obtain ⟨γ₀, hγ₀⟩ := hne
  have hdata : ∀ γ ∈ badSet, ∃ (S : Finset (Fin n)) (g p : F), g ≠ 0 ∧
      S.card + w = n ∧
      R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁) = C g * vanishingPoly dom S :=
    fun γ hγ => witness_division_identity hw hn hrel₀ hrel₁ hdℓ₀ hdR₀ hdℓ₁ hdR₁
      hcop₀ hcopℓ hδn (Finset.mem_filter.mp hγ).2
  choose Sf gf pf hgne hcard hid using hdata
  have hinj : ∀ γ₁ (h₁ : γ₁ ∈ badSet) γ₂ (h₂ : γ₂ ∈ badSet),
      Sf γ₁ h₁ = Sf γ₂ h₂ → γ₁ = γ₂ := by
    intro γ₁ h₁ γ₂ h₂ hSeq
    have e₂ := hid γ₂ h₂
    rw [← hSeq] at e₂
    exact witness_gamma_injective hG₀ (by rw [hdℓ₀]; exact hw) hℓ₁pos hcop₁
      (hid γ₁ h₁) e₂
  set 𝒯 := badSet.attach.image
    (fun x : {γ // γ ∈ badSet} => (Sf x.1 x.2)ᶜ) with h𝒯
  have hmem : ∀ T ∈ 𝒯, SplitMember dom (vanishingPoly dom (Sf γ₀ hγ₀)ᶜ) ℓ₀ T := by
    intro T hT
    rw [h𝒯, Finset.mem_image] at hT
    obtain ⟨⟨γ, hγ⟩, -, rfl⟩ := hT
    exact witness_compl_splitMember hG₀ hcop₀ hcopℓ (by rw [hdℓ₀]; exact hw)
      (hgne γ₀ hγ₀) (hid γ₀ hγ₀) (by rw [hdℓ₀]; exact hcard γ₀ hγ₀)
      (hid γ hγ) (by rw [hdℓ₀]; exact hcard γ hγ)
  have hTlarge : ∀ T ∈ 𝒯, ℓ₀.natDegree ≤ T.card := by
    intro T hT
    rw [h𝒯, Finset.mem_image] at hT
    obtain ⟨⟨γ, hγ⟩, -, rfl⟩ := hT
    have hTcard : ((Sf γ hγ)ᶜ : Finset (Fin n)).card = w := by
      rw [Finset.card_compl, Fintype.card_fin]
      have hSle : (Sf γ hγ).card ≤ n := by
        have := Finset.card_le_univ (Sf γ hγ)
        rwa [Fintype.card_fin] at this
      have hS := hcard γ hγ
      omega
    rw [hTcard, hdℓ₀]
  have hG1 := splitMember_count_le (f := vanishingPoly dom (Sf γ₀ hγ₀)ᶜ)
    (by rw [hdℓ₀]; exact hw) hG₀ 𝒯 hmem hTlarge
  rw [hdℓ₀] at hG1
  have hinjOn : Set.InjOn (fun x : {γ // γ ∈ badSet} => (Sf x.1 x.2)ᶜ)
      badSet.attach := by
    intro x _ y _ hxy
    have hSS : Sf x.1 x.2 = Sf y.1 y.2 := by
      have h2 := congrArg (fun s : Finset (Fin n) => sᶜ) hxy
      simpa using h2
    exact Subtype.ext (hinj _ _ _ _ hSS)
  have hcardeq : 𝒯.card = badSet.card := by
    rw [h𝒯, Finset.card_image_of_injOn hinjOn, Finset.card_attach]
  rw [← hcardeq]
  exact hG1

end FiberPencil

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.witness_division_identity
#print axioms ProximityGap.WBPencil.witness_compl_splitMember
#print axioms ProximityGap.WBPencil.witness_gamma_injective
#print axioms ProximityGap.WBPencil.stratumG_firstRow_badScalars_card_le_div
#print axioms ProximityGap.WBPencil.stratumG_firstRow_badScalars_card_le

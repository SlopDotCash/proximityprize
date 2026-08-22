/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WindowPackingLaw

/-!
# The coset family attains the packing bound: the j = 0 stratum is PINNED (#371)

The lower-bound half of the solved window stratum.  At the first beyond-ladder
slice `n = 3w + k − 1` with `n = m·w`, the stack

  `u₀ = 1/(x^w − e₀)`,  `u₁ = 1/(x^w − e₁)`     (`e₀ ≠ e₁`, `eᵢ^m ≠ 1`)

has at least `m = n/w` mca-bad scalars: for every `y` in the image `μ_m` of the
`w`-th-power map on the domain, the scalar

  `γ_y = −(e₀−y)·(e₁^m−1) / ((e₀^m−1)·(e₁−y))`

is bad with witness `S_y = {x : x^w ≠ y}` (the complement of one `μ_w`-coset) and
explainer `P_y = p_y(X^w)` of degree exactly `k − 1`.  The mechanism is a single
polynomial identity in the folded variable `Y = X^w`:

  `(Y−e₁) + γ_y·(Y−e₀) − λ_y·V_y = p_y·(Y−e₀)(Y−e₁)`,  `V_y := (Y^m−1)/(Y−y)`,

(`λ_y, γ_y` are pinned by evaluation at `e₀, e₁`), evaluated at `Y = x^w` where
`V_y` vanishes on `μ_m ∖ {y}`.  The no-joint clause is free
(`not_pairJointAgreesOn_of_genuine_fst`), and `γ_y` is a Möbius function of `y` —
injective.  Combined with `window_jzero_solved` (`#bad·w ≤ n`):

  **`#bad = n/w` EXACTLY — the first machine-checked two-sided pin of a window
  stratum** (probe record: `probe_coset_family_jzero.py`, 3 = 3, 4 = 4, 4 = 4).

Structurally this is a fold-pullback: with `Y := X^w` the construction descends to
the quotient domain `μ_m` at slack 1, where it is the granularity ladder's rung-1
spike family — the window's extremal adversaries are fold-pullbacks of ladder-edge
adversaries (the formal root of the campaign's Möbius/renormalization empirics).
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section CosetFamily

variable (dom : Fin n ↪ F) {k w m : ℕ}
variable {e₀ e₁ : F}

/-- The deleted-root quotient `V_y = (Y^m − 1)/(Y − y)`. -/
noncomputable def cosetV (m : ℕ) (y : F) : F[X] :=
  (X ^ m - 1) /ₘ (X - C y)

/-- The coset-family bad scalar at quotient point `y`. -/
noncomputable def cosetGamma (m : ℕ) (e₀ e₁ y : F) : F :=
  -((e₀ - y) * (e₁ ^ m - 1)) / ((e₀ ^ m - 1) * (e₁ - y))

theorem cosetV_mul (m : ℕ) {y : F} (hy : y ^ m = 1) :
    (X - C y) * cosetV m y = X ^ m - 1 := by
  have hdvd : (X - C y) ∣ (X ^ m - 1 : F[X]) := by
    have h := sub_dvd_pow_sub_pow (X : F[X]) (C y) m
    rwa [← C_pow, hy, C_1] at h
  rw [cosetV]
  have hmonic : (X - C y).Monic := monic_X_sub_C y
  have hmod : (X ^ m - 1 : F[X]) %ₘ (X - C y) = 0 :=
    (modByMonic_eq_zero_iff_dvd hmonic).mpr hdvd
  have hsum := modByMonic_add_div (X ^ m - 1 : F[X]) (X - C y)
  rw [hmod, zero_add] at hsum
  exact hsum

theorem cosetV_eval_zero (m : ℕ) {y z : F} (hy : y ^ m = 1) (hz : z ^ m = 1)
    (hne : z ≠ y) : (cosetV m y).eval z = 0 := by
  have h := congrArg (Polynomial.eval z) (cosetV_mul m hy)
  rw [eval_mul, eval_sub, eval_sub, eval_pow, eval_X, eval_C, eval_one, hz,
    sub_self] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)

theorem cosetV_eval_ne (m : ℕ) {y e : F} (hy : y ^ m = 1) (he : e ^ m ≠ 1) :
    (cosetV m y).eval e ≠ 0 ∧ (e - y) * (cosetV m y).eval e = e ^ m - 1 := by
  have h := congrArg (Polynomial.eval e) (cosetV_mul m hy)
  rw [eval_mul, eval_sub, eval_sub, eval_pow, eval_X, eval_C, eval_one] at h
  refine ⟨fun h0 => ?_, h⟩
  rw [h0, mul_zero] at h
  exact he (sub_eq_zero.mp h.symm)

theorem cosetV_natDegree (m : ℕ) {y : F} (hy : y ^ m = 1) (hm : 1 ≤ m) :
    (cosetV m y).natDegree = m - 1 := by
  have hmul := cosetV_mul m hy
  have hne : (cosetV m y) ≠ 0 := by
    intro h0
    have := hmul
    rw [h0, mul_zero] at this
    have h1 : (X ^ m - 1 : F[X]).natDegree = m := by
      have : ((X : F[X]) ^ m - 1).natDegree = (X ^ m : F[X]).natDegree := by
        refine natDegree_sub_eq_left_of_natDegree_lt ?_
        rw [natDegree_X_pow, natDegree_one]
        omega
      rw [this, natDegree_X_pow]
    rw [← this] at h1
    simp at h1
    omega
  have hdeg := congrArg Polynomial.natDegree hmul
  rw [natDegree_mul (X_sub_C_ne_zero y) hne, natDegree_X_sub_C] at hdeg
  have h1 : ((X : F[X]) ^ m - 1).natDegree = m := by
    have : ((X : F[X]) ^ m - 1).natDegree = (X ^ m : F[X]).natDegree := by
      refine natDegree_sub_eq_left_of_natDegree_lt ?_
      rw [natDegree_X_pow, natDegree_one]
      omega
    rw [this, natDegree_X_pow]
  omega

end CosetFamily

/-- The coset-family scaling constant. -/
noncomputable def cosetLambda (m : ℕ) (e₀ e₁ y : F) : F :=
  (e₀ - e₁) * (e₀ - y) / (e₀ ^ m - 1)

/-- The folded numerator whose exact division by `(Y−e₀)(Y−e₁)` produces the
explainer. -/
noncomputable def cosetN (m : ℕ) (e₀ e₁ y : F) : F[X] :=
  (X - C e₁) + C (cosetGamma m e₀ e₁ y) * (X - C e₀)
    - C (cosetLambda m e₀ e₁ y) * cosetV m y

/-- The folded explainer. -/
noncomputable def cosetP (m : ℕ) (e₀ e₁ y : F) : F[X] :=
  cosetN m e₀ e₁ y /ₘ ((X - C e₀) * (X - C e₁))

section CosetIdentity

variable {m : ℕ} {e₀ e₁ y : F}

theorem cosetN_eval_e₀ (hy : y ^ m = 1) (he₀ : e₀ ^ m ≠ 1) :
    (cosetN m e₀ e₁ y).eval e₀ = 0 := by
  obtain ⟨hv0, hv⟩ := cosetV_eval_ne m hy he₀
  have hy0 : e₀ - y ≠ 0 := by
    intro h
    exact he₀ (by rw [sub_eq_zero.mp h, hy])
  have hd : e₀ ^ m - 1 ≠ 0 := sub_ne_zero.mpr he₀
  have hv0' : (cosetV m y).eval e₀ = (e₀ ^ m - 1) / (e₀ - y) := by
    rw [eq_div_iff hy0, mul_comm]
    exact hv
  rw [cosetN]
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X]
  rw [hv0', cosetLambda]
  field_simp
  ring

theorem cosetN_eval_e₁ (hy : y ^ m = 1) (he₀ : e₀ ^ m ≠ 1) (he₁ : e₁ ^ m ≠ 1) :
    (cosetN m e₀ e₁ y).eval e₁ = 0 := by
  obtain ⟨hv1, hv⟩ := cosetV_eval_ne m hy he₁
  have hy1 : e₁ - y ≠ 0 := by
    intro h
    exact he₁ (by rw [sub_eq_zero.mp h, hy])
  have hd0 : e₀ ^ m - 1 ≠ 0 := sub_ne_zero.mpr he₀
  have hv1' : (cosetV m y).eval e₁ = (e₁ ^ m - 1) / (e₁ - y) := by
    rw [eq_div_iff hy1, mul_comm]
    exact hv
  rw [cosetN]
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X]
  rw [hv1', cosetLambda, cosetGamma]
  field_simp
  ring

/-- The exact-division identity: `(Y−e₀)(Y−e₁)·p_y = N_y`. -/
theorem cosetP_identity (hy : y ^ m = 1) (hne : e₀ ≠ e₁)
    (he₀ : e₀ ^ m ≠ 1) (he₁ : e₁ ^ m ≠ 1) :
    ((X - C e₀) * (X - C e₁)) * cosetP m e₀ e₁ y = cosetN m e₀ e₁ y := by
  have h₀ : (X - C e₀) ∣ cosetN m e₀ e₁ y :=
    dvd_iff_isRoot.mpr (cosetN_eval_e₀ hy he₀)
  have h₁ : (X - C e₁) ∣ cosetN m e₀ e₁ y :=
    dvd_iff_isRoot.mpr (cosetN_eval_e₁ hy he₀ he₁)
  have hcop : IsCoprime (X - C e₀) (X - C e₁ : F[X]) :=
    isCoprime_X_sub_C_of_isUnit_sub ((sub_ne_zero.mpr hne).isUnit)
  have hdvd : (X - C e₀) * (X - C e₁) ∣ cosetN m e₀ e₁ y :=
    hcop.mul_dvd h₀ h₁
  have hmonic : ((X - C e₀) * (X - C e₁) : F[X]).Monic :=
    (monic_X_sub_C e₀).mul (monic_X_sub_C e₁)
  rw [cosetP]
  have hmod : cosetN m e₀ e₁ y %ₘ ((X - C e₀) * (X - C e₁)) = 0 :=
    (modByMonic_eq_zero_iff_dvd hmonic).mpr hdvd
  have hsum := modByMonic_add_div (cosetN m e₀ e₁ y) ((X - C e₀) * (X - C e₁))
  rw [hmod, zero_add] at hsum
  exact hsum

theorem cosetN_natDegree_le (hy : y ^ m = 1) (hm : 3 ≤ m) :
    (cosetN m e₀ e₁ y).natDegree ≤ m - 1 := by
  rw [cosetN]
  refine le_trans (natDegree_sub_le _ _) (max_le (le_trans (natDegree_add_le _ _)
    (max_le ?_ ?_)) ?_)
  · calc (X - C e₁ : F[X]).natDegree ≤ 1 := natDegree_X_sub_C_le e₁
      _ ≤ m - 1 := by omega
  · calc (C (cosetGamma m e₀ e₁ y) * (X - C e₀)).natDegree
        ≤ (C (cosetGamma m e₀ e₁ y)).natDegree + (X - C e₀).natDegree :=
          natDegree_mul_le
      _ ≤ 0 + 1 := Nat.add_le_add (le_of_eq (natDegree_C _)) (natDegree_X_sub_C_le e₀)
      _ ≤ m - 1 := by omega
  · calc (C (cosetLambda m e₀ e₁ y) * cosetV m y).natDegree
        ≤ (C (cosetLambda m e₀ e₁ y)).natDegree + (cosetV m y).natDegree :=
          natDegree_mul_le
      _ ≤ 0 + (m - 1) := by
          refine Nat.add_le_add (le_of_eq (natDegree_C _)) ?_
          rw [cosetV_natDegree m hy (by omega)]
      _ = m - 1 := by omega

theorem cosetP_natDegree_le (hy : y ^ m = 1) (hne : e₀ ≠ e₁)
    (he₀ : e₀ ^ m ≠ 1) (he₁ : e₁ ^ m ≠ 1) (hm : 3 ≤ m) :
    (cosetP m e₀ e₁ y).natDegree ≤ m - 3 := by
  by_cases hP0 : cosetP m e₀ e₁ y = 0
  · rw [hP0]; simp
  have hid := cosetP_identity hy hne he₀ he₁
  have hdeg := congrArg Polynomial.natDegree hid
  have hprodne : ((X - C e₀) * (X - C e₁) : F[X]) ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero e₀) (X_sub_C_ne_zero e₁)
  rw [natDegree_mul hprodne hP0,
    natDegree_mul (X_sub_C_ne_zero e₀) (X_sub_C_ne_zero e₁),
    natDegree_X_sub_C, natDegree_X_sub_C] at hdeg
  have := cosetN_natDegree_le (e₀ := e₀) (e₁ := e₁) hy hm
  omega

end CosetIdentity

section Attainment

variable (dom : Fin n ↪ F) {k w m : ℕ} {e₀ e₁ : F}

open Classical in
/-- **The coset family attains**: at the `j = 0` slice, for every `y` in the image
of the `w`-th-power map on the domain, the scalar `γ_y` is mca-bad for the stack
`(1/(x^w−e₀), 1/(x^w−e₁))`. -/
theorem coset_family_mcaEvent (hk : 1 ≤ k) (hw : 1 ≤ w)
    (hkn : k + 3 * w = n + 1) (hnm : n = m * w)
    (hord : ∀ i : Fin n, (dom i) ^ n = 1)
    (hne : e₀ ≠ e₁) (he₀ : e₀ ^ m ≠ 1) (he₁ : e₁ ^ m ≠ 1)
    {δ : ℝ≥0}
    (hδw : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((n - w : ℕ) : ℝ≥0))
    {y : F} (hy : ∃ i : Fin n, (dom i) ^ w = y) :
    mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => (1 : F[X]).eval (dom i) / (X ^ w - C e₀).eval (dom i))
      (fun i => (1 : F[X]).eval (dom i) / (X ^ w - C e₁).eval (dom i))
      (cosetGamma m e₀ e₁ y) := by
  have hm3 : 3 ≤ m := by
    rcases Nat.lt_or_ge m 3 with h | h
    · exfalso
      interval_cases m <;> omega
    · exact h
  have hym : y ^ m = 1 := by
    obtain ⟨i, hi⟩ := hy
    rw [← hi, ← pow_mul, mul_comm w m, ← hnm]
    exact hord i
  -- the witness set: complement of the y-fiber
  set S : Finset (Fin n) := Finset.univ.filter (fun i => (dom i) ^ w ≠ y) with hS
  have hfiber : (Finset.univ.filter (fun i => (dom i) ^ w = y)).card ≤ w := by
    have hroots : ∀ i ∈ Finset.univ.filter (fun i => (dom i) ^ w = y),
        ((X ^ w - C y : F[X])).eval (dom i) = 0 := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [eval_sub, eval_pow, eval_X, eval_C, hi.2, sub_self]
    by_contra hbig
    push_neg at hbig
    have h0 : (X ^ w - C y : F[X]) = 0 := by
      refine eq_zero_of_vanishing_card_gt dom hroots ?_
      have : ((X ^ w - C y : F[X])).natDegree ≤ w := by
        refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
        · rw [natDegree_X_pow]
        · rw [natDegree_C]; omega
      omega
    have := congrArg (Polynomial.natDegree) h0
    rw [natDegree_X_pow_sub_C] at this
    simp at this
    omega
  have hScard : n - w ≤ S.card := by
    have hcompl : S.card
        = n - (Finset.univ.filter (fun i => (dom i) ^ w = y)).card := by
      rw [hS, ← Finset.compl_filter, Finset.card_compl, Fintype.card_fin]
    omega
  -- nonvanishing of the denominators on the domain
  have hzpow : ∀ i : Fin n, ((dom i) ^ w) ^ m = 1 := by
    intro i
    rw [← pow_mul, mul_comm w m, ← hnm]
    exact hord i
  have hℓ₀v : ∀ i : Fin n, (X ^ w - C e₀ : F[X]).eval (dom i) ≠ 0 := by
    intro i h
    rw [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at h
    exact he₀ (by rw [← h]; exact hzpow i)
  have hℓ₁v : ∀ i : Fin n, (X ^ w - C e₁ : F[X]).eval (dom i) ≠ 0 := by
    intro i h
    rw [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at h
    exact he₁ (by rw [← h]; exact hzpow i)
  -- the explainer
  set P : F[X] := (cosetP m e₀ e₁ y).comp (X ^ w) with hP
  have hPdeg : P.natDegree ≤ k - 1 := by
    rw [hP, natDegree_comp, natDegree_X_pow]
    have h1 := cosetP_natDegree_le (e₀ := e₀) (e₁ := e₁) hym hne he₀ he₁ hm3
    calc (cosetP m e₀ e₁ y).natDegree * w ≤ (m - 3) * w :=
          Nat.mul_le_mul_right w h1
      _ ≤ k - 1 := by
          have h2 : (m - 3) * w = m * w - 3 * w := Nat.sub_mul m 3 w
          have h3 : 3 * w ≤ m * w := Nat.mul_le_mul_right w hm3
          have h4 : m * w = n := hnm.symm
          omega
  refine ⟨S, ?_, ⟨fun i => P.eval (dom i), ⟨P, ?_, rfl⟩, ?_⟩, ?_⟩
  · -- witness size cast
    calc (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((n - w : ℕ) : ℝ≥0) := hδw
      _ ≤ (S.card : ℝ≥0) := by exact_mod_cast hScard
  · -- degree < k
    by_cases hP0 : P = 0
    · rw [hP0, degree_zero]
      exact bot_lt_iff_ne_bot.mpr (by simp)
    · calc P.degree = (P.natDegree : WithBot ℕ) := degree_eq_natDegree hP0
        _ ≤ ((k - 1 : ℕ) : WithBot ℕ) := by exact_mod_cast hPdeg
        _ < (k : WithBot ℕ) := by
            rw [Nat.cast_lt]
            omega
  · -- agreement on S
    intro i hi
    rw [hS, Finset.mem_filter] at hi
    set z : F := (dom i) ^ w with hz
    have hzm : z ^ m = 1 := hzpow i
    have hzy : z ≠ y := hi.2
    have hz0 : z - e₀ ≠ 0 := by
      intro h
      exact he₀ (by rw [← sub_eq_zero.mp h]; exact hzm)
    have hz1 : z - e₁ ≠ 0 := by
      intro h
      exact he₁ (by rw [← sub_eq_zero.mp h]; exact hzm)
    -- evaluate the exact-division identity at z
    have hid := congrArg (Polynomial.eval z) (cosetP_identity hym hne he₀ he₁)
    rw [eval_mul, eval_mul, eval_sub, eval_sub, eval_X, eval_C, eval_C] at hid
    have hNz : (cosetN m e₀ e₁ y).eval z
        = (z - e₁) + cosetGamma m e₀ e₁ y * (z - e₀) := by
      rw [cosetN]
      simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X]
      rw [cosetV_eval_zero m hym hzm hzy, mul_zero, sub_zero]
    rw [hNz] at hid
    -- the line value
    have hPz : P.eval (dom i) = (cosetP m e₀ e₁ y).eval z := by
      rw [hP, eval_comp, eval_pow, eval_X, hz]
    show P.eval (dom i)
        = (1 : F[X]).eval (dom i) / (X ^ w - C e₀).eval (dom i)
          + cosetGamma m e₀ e₁ y
            • ((1 : F[X]).eval (dom i) / (X ^ w - C e₁).eval (dom i))
    rw [hPz, smul_eq_mul, eval_one, eval_sub, eval_pow, eval_X, eval_C,
      eval_sub, eval_pow, eval_X, eval_C, ← hz]
    field_simp
    first
      | linear_combination hid
      | linear_combination -hid
      | linear_combination (z - e₀) * (z - e₁) * hid
      | linear_combination -((z - e₀) * (z - e₁)) * hid
  · -- no joint explanation: the first row is genuinely rational
    have hudr : 2 * w + k ≤ n := by omega
    have hℓd : (X ^ w - C e₀ : F[X]).natDegree ≤ w := by
      rw [natDegree_X_pow_sub_C]
    have hRd : (1 : F[X]).natDegree ≤ w + k - 1 := by
      rw [natDegree_one]
      omega
    have hgen : ¬ (X ^ w - C e₀ : F[X]) ∣ 1 := by
      intro h
      have hunit := isUnit_of_dvd_one h
      have := Polynomial.natDegree_eq_zero_of_isUnit hunit
      rw [natDegree_X_pow_sub_C] at this
      omega
    exact not_pairJointAgreesOn_of_genuine_fst dom hudr hk hℓd hRd hℓ₀v hgen
      hScard _

open Classical in
/-- Fibers of the `w`-th-power map on an embedded domain have size at most `w`. -/
theorem coset_fiber_card_le (hw : 1 ≤ w) (y : F) :
    (Finset.univ.filter (fun i : Fin n => (dom i) ^ w = y)).card ≤ w := by
  by_contra hbig
  push_neg at hbig
  have h0 : (X ^ w - C y : F[X]) = 0 := by
    refine eq_zero_of_vanishing_card_gt dom
      (S := Finset.univ.filter (fun i : Fin n => (dom i) ^ w = y))
      (fun i hi => ?_) ?_
    · rw [Finset.mem_filter] at hi
      rw [eval_sub, eval_pow, eval_X, eval_C, hi.2, sub_self]
    · have : ((X ^ w - C y : F[X])).natDegree ≤ w := by
        refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
        · rw [natDegree_X_pow]
        · rw [natDegree_C]; omega
      omega
  have := congrArg Polynomial.natDegree h0
  rw [natDegree_X_pow_sub_C] at this
  simp at this
  omega

/-- Möbius injectivity of the coset-family scalars. -/
theorem cosetGamma_injOn {m : ℕ} (hne : e₀ ≠ e₁) (he₀ : e₀ ^ m ≠ 1)
    (he₁ : e₁ ^ m ≠ 1) {y y' : F} (hy : y ^ m = 1) (hy' : y' ^ m = 1)
    (h : cosetGamma m e₀ e₁ y = cosetGamma m e₀ e₁ y') : y = y' := by
  have hd0 : e₀ ^ m - 1 ≠ 0 := sub_ne_zero.mpr he₀
  have hd1 : e₁ ^ m - 1 ≠ 0 := sub_ne_zero.mpr he₁
  have hy1 : e₁ - y ≠ 0 := fun hh => he₁ (by rw [sub_eq_zero.mp hh, hy])
  have hy1' : e₁ - y' ≠ 0 := fun hh => he₁ (by rw [sub_eq_zero.mp hh, hy'])
  rw [cosetGamma, cosetGamma,
    div_eq_div_iff (mul_ne_zero hd0 hy1) (mul_ne_zero hd0 hy1')] at h
  have key : (e₀ ^ m - 1) * ((e₁ ^ m - 1) * ((e₀ - e₁) * (y - y'))) = 0 := by
    first
      | linear_combination h
      | linear_combination -h
  rcases mul_eq_zero.mp key with h1 | h2
  · exact absurd h1 hd0
  rcases mul_eq_zero.mp h2 with h3 | h4
  · exact absurd h3 hd1
  rcases mul_eq_zero.mp h4 with h5 | h6
  · exact absurd h5 (sub_ne_zero.mpr hne)
  · exact sub_eq_zero.mp h6

open Classical in
/-- **The attainment count**: the coset family certifies at least `m = n/w` bad
scalars for the stack `(1/(x^w−e₀), 1/(x^w−e₁))`. -/
theorem coset_family_card_ge (hk : 1 ≤ k) (hw : 1 ≤ w)
    (hkn : k + 3 * w = n + 1) (hnm : n = m * w)
    (hord : ∀ i : Fin n, (dom i) ^ n = 1)
    (hne : e₀ ≠ e₁) (he₀ : e₀ ^ m ≠ 1) (he₁ : e₁ ^ m ≠ 1)
    {δ : ℝ≥0}
    (hδw : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((n - w : ℕ) : ℝ≥0)) :
    m ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => (1 : F[X]).eval (dom i) / (X ^ w - C e₀).eval (dom i))
      (fun i => (1 : F[X]).eval (dom i) / (X ^ w - C e₁).eval (dom i)) γ)).card := by
  set I : Finset F := Finset.univ.image (fun i : Fin n => (dom i) ^ w) with hI
  -- the image has at least m points (fibers are ≤ w)
  have hIcard : m ≤ I.card := by
    have hpart :=
      Finset.card_eq_sum_card_image (fun i : Fin n => (dom i) ^ w)
        (Finset.univ : Finset (Fin n))
    have hsum : (Finset.univ : Finset (Fin n)).card ≤ I.card * w := by
      rw [hpart]
      calc ∑ y ∈ I, (Finset.univ.filter (fun i : Fin n => (dom i) ^ w = y)).card
          ≤ ∑ _y ∈ I, w :=
            Finset.sum_le_sum (fun y _ => coset_fiber_card_le dom hw y)
        _ = I.card * w := by rw [Finset.sum_const, smul_eq_mul]
    rw [Finset.card_univ, Fintype.card_fin, hnm] at hsum
    exact Nat.le_of_mul_le_mul_right hsum (by omega)
  -- inject the image into the bad set via the (injective) Möbius scalar map
  have hzpow : ∀ y ∈ I, y ^ m = 1 := by
    intro y hy
    rw [hI, Finset.mem_image] at hy
    obtain ⟨i, -, rfl⟩ := hy
    rw [← pow_mul, mul_comm w m, ← hnm]
    exact hord i
  refine le_trans hIcard (Finset.card_le_card_of_injOn
    (fun y => cosetGamma m e₀ e₁ y) (fun y hy => ?_) ?_)
  · refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
    refine coset_family_mcaEvent dom hk hw hkn hnm hord hne he₀ he₁ hδw ?_
    have hy' := Finset.mem_coe.mp hy
    rw [hI, Finset.mem_image] at hy'
    obtain ⟨i, -, rfl⟩ := hy'
    exact ⟨i, rfl⟩
  · intro y hy y' hy' h
    exact cosetGamma_injOn hne he₀ he₁ (hzpow y (Finset.mem_coe.mp hy))
      (hzpow y' (Finset.mem_coe.mp hy')) h

open Classical in
/-- **THE j = 0 STRATUM IS PINNED, both sides machine-checked**: the coset stack
`(1/(x^w−e₀), 1/(x^w−e₁))` has EXACTLY `m = n/w` bad scalars at the slice
`n = 3w + k − 1` — the packing law (`window_jzero_solved`) from above, the coset
family from below, meeting exactly. -/
theorem window_jzero_pinned (hk : 1 ≤ k) (hw : 1 ≤ w)
    (hkn : k + 3 * w = n + 1) (hnm : n = m * w)
    (hord : ∀ i : Fin n, (dom i) ^ n = 1)
    (hne : e₀ ≠ e₁) (he₀ : e₀ ^ m ≠ 1) (he₁ : e₁ ^ m ≠ 1)
    {δ : ℝ≥0}
    (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (hδw : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((n - w : ℕ) : ℝ≥0)) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => (1 : F[X]).eval (dom i) / (X ^ w - C e₀).eval (dom i))
      (fun i => (1 : F[X]).eval (dom i) / (X ^ w - C e₁).eval (dom i)) γ)).card
      = m := by
  have hzpow : ∀ i : Fin n, ((dom i) ^ w) ^ m = 1 := by
    intro i
    rw [← pow_mul, mul_comm w m, ← hnm]
    exact hord i
  have hℓ₀v : ∀ i : Fin n, (X ^ w - C e₀ : F[X]).eval (dom i) ≠ 0 := by
    intro i h
    rw [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at h
    exact he₀ (by rw [← h]; exact hzpow i)
  have hℓ₁v : ∀ i : Fin n, (X ^ w - C e₁ : F[X]).eval (dom i) ≠ 0 := by
    intro i h
    rw [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at h
    exact he₁ (by rw [← h]; exact hzpow i)
  have hgen : ∀ e : F, ¬ (X ^ w - C e : F[X]) ∣ 1 := by
    intro e h
    have hunit := isUnit_of_dvd_one h
    have := Polynomial.natDegree_eq_zero_of_isUnit hunit
    rw [natDegree_X_pow_sub_C] at this
    omega
  have hcop : IsCoprime (X ^ w - C e₀ : F[X]) (X ^ w - C e₁) := by
    refine ⟨-(C ((e₀ - e₁)⁻¹)), C ((e₀ - e₁)⁻¹), ?_⟩
    have hsub : (X ^ w - C e₁ : F[X]) - (X ^ w - C e₀) = C (e₀ - e₁) := by
      rw [C_sub]
      ring
    calc -(C ((e₀ - e₁)⁻¹)) * (X ^ w - C e₀) + C ((e₀ - e₁)⁻¹) * (X ^ w - C e₁)
        = C ((e₀ - e₁)⁻¹) * ((X ^ w - C e₁) - (X ^ w - C e₀)) := by ring
      _ = C ((e₀ - e₁)⁻¹) * C (e₀ - e₁) := by rw [hsub]
      _ = C ((e₀ - e₁)⁻¹ * (e₀ - e₁)) := by rw [C_mul]
      _ = 1 := by
          rw [inv_mul_cancel₀ (sub_ne_zero.mpr hne), C_1]
  have hwn : w ≤ n := by
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
    have hm1 : 1 ≤ m := by
      by_contra h
      push_neg at h
      interval_cases m
      rw [Nat.zero_mul] at hnm
      omega
    calc w = 1 * w := (one_mul w).symm
      _ ≤ m * w := Nat.mul_le_mul_right w hm1
      _ = n := hnm.symm
  have hub := window_jzero_solved dom hk (by omega) hwn
    (le_of_eq natDegree_X_pow_sub_C)
    (le_of_eq natDegree_X_pow_sub_C)
    (by rw [natDegree_one]; omega) (by rw [natDegree_one]; omega)
    hℓ₀v hℓ₁v hcop (hgen e₀) (hgen e₁) hδn
  have hlb := coset_family_card_ge dom hk hw hkn hnm hord hne he₀ he₁ hδw
  refine le_antisymm ?_ hlb
  -- #bad · w ≤ n = m · w  ⟹  #bad ≤ m
  have hle : (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => (1 : F[X]).eval (dom i) / (X ^ w - C e₀).eval (dom i))
      (fun i => (1 : F[X]).eval (dom i) / (X ^ w - C e₁).eval (dom i)) γ)).card
        * w ≤ m * w := by
    calc _ ≤ n := hub
      _ = m * w := hnm
  exact Nat.le_of_mul_le_mul_right hle (by omega)

end Attainment

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.cosetV_mul
#print axioms ProximityGap.WBPencil.cosetV_eval_zero
#print axioms ProximityGap.WBPencil.cosetV_natDegree
#print axioms ProximityGap.WBPencil.cosetP_identity
#print axioms ProximityGap.WBPencil.cosetP_natDegree_le
#print axioms ProximityGap.WBPencil.coset_family_mcaEvent
#print axioms ProximityGap.WBPencil.coset_family_card_ge
#print axioms ProximityGap.WBPencil.window_jzero_pinned

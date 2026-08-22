/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.CellPinning
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CaptureKernel

/-!
# The Johnson-regime cell pencil (#348): `himpr` from the per-cell §5 package

The cell-dichotomy funnel (`exists_dichotomyData_of_cell_improvement`) consumes ONE
per-cell input — large cell ⟹ improving pair (`himpr`).  The window route discharges it
via the UD pencil (`cell_improvement_of_window`); this file lands the **Johnson-regime
mirror** through the landed pinning chain:

* `pencil_of_pinning_and_section` — the **Johnson pencil**: the cell-pinning output
  (every Taylor section of the surface is `v₀ + γ·v₁`) together with the **section link**
  (`hsec`: each decode IS the surface's Taylor section — the cell-vocabulary reading of
  `(Y′−C w) ∣ R` + irreducibility, mechanical) yields `(v₀', v₁')` with `natDegree < k`
  and `∀ γ ∈ E, P γ = v₀' + C γ·v₁'` (degrees recovered by the two-point trick, exactly
  as in the window pencil);
* **`cell_improvement_of_pinning_package`** — the funnel's `himpr` input discharged from
  the heavy-agreement package + the section link, via `McaDecode.affineCaptured` +
  `affineCaptured_improve` — the exact mirror of `cell_improvement_of_window`.

After this file, #348 item 1 ≡ producing, per large factor cell: the §5 package legs of
`exists_pinning_pair_of_heavy_agreement` (centre/branch/heavy-set selection — the GK1+GK3
composition) and the section link `hsec` (a mechanical monic-linear-divisibility + Taylor
computation from the cell's own divisibilities).  Every consumer below them is proven.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open scoped NNReal ENNReal
open ArkLib

namespace BCIKS20.CellPencilJohnson

variable {F₀ : Type} [Field F₀]
variable {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The Johnson pencil from pinning + section link.**  If every Taylor section of the
surface is `v₀ + γ·v₁` (the pinning-pair output) and every cell decode IS the surface's
Taylor section (`hsec`), then on any cell with two points the decodes form a pencil with
the RS degree bound — recovered by the two-point trick from the decodes' own degrees. -/
theorem pencil_of_pinning_and_section {n k : ℕ} (hk : 0 < k) {ι₀ : Type} [Fintype ι₀]
    {domain : ι₀ ↪ F₀} {δ : ℝ≥0} {u : WordStack F₀ (Fin 2) ι₀}
    (E : Finset F₀) (P : F₀ → F₀[X])
    (hdec : ∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ)
    {x₀ : F₀} {w : F₀[X][Y]}
    (v₀ v₁ : F₀[X])
    (hpin : ∀ γ : F₀,
      (∑ t ∈ Finset.range n,
        Polynomial.C (((Polynomial.taylor (Polynomial.C x₀) w).coeff t).eval γ)
          * (Polynomial.X - Polynomial.C x₀) ^ t)
      = v₀ + Polynomial.C γ * v₁)
    (hsec : ∀ γ ∈ E, P γ
      = ∑ t ∈ Finset.range n,
          Polynomial.C (((Polynomial.taylor (Polynomial.C x₀) w).coeff t).eval γ)
            * (Polynomial.X - Polynomial.C x₀) ^ t)
    (h2 : 1 < E.card) :
    ∃ v₀' v₁' : F₀[X], v₀'.natDegree < k ∧ v₁'.natDegree < k ∧
      ∀ γ ∈ E, P γ = v₀' + Polynomial.C γ * v₁' := by
  classical
  -- the raw pencil: decode = pinned section
  have hP : ∀ γ ∈ E, P γ = v₀ + Polynomial.C γ * v₁ := fun γ hγ =>
    (hsec γ hγ).trans (hpin γ)
  -- two-point degree recovery (the window-pencil trick)
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hne⟩ := Finset.one_lt_card.mp h2
  obtain ⟨d₁, hd₁⟩ := hdec γ₁ hγ₁
  obtain ⟨d₂, hd₂⟩ := hdec γ₂ hγ₂
  have hsub : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hne
  set v₁' : F₀[X] := Polynomial.C (γ₁ - γ₂)⁻¹ * (P γ₁ - P γ₂) with hv₁'
  set v₀' : F₀[X] := P γ₁ - Polynomial.C γ₁ * v₁' with hv₀'
  -- `v₁' = v₁` and `v₀' = v₀` from the raw pencil at the two points
  have hval₁ : P γ₁ = v₀ + Polynomial.C γ₁ * v₁ := hP γ₁ hγ₁
  have hval₂ : P γ₂ = v₀ + Polynomial.C γ₂ * v₁ := hP γ₂ hγ₂
  have hv₁'eq : v₁' = v₁ := by
    rw [hv₁', hval₁, hval₂]
    have : (v₀ + Polynomial.C γ₁ * v₁) - (v₀ + Polynomial.C γ₂ * v₁)
        = Polynomial.C (γ₁ - γ₂) * v₁ := by
      rw [Polynomial.C_sub]
      ring
    rw [this, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hsub, Polynomial.C_1,
      one_mul]
  have hv₀'eq : v₀' = v₀ := by
    rw [hv₀', hv₁'eq, hval₁]
    ring
  -- degree bounds from the decodes' degrees
  have hdegP₁ : (P γ₁).natDegree < k := by
    have h := d₁.hdeg
    rw [hd₁] at h
    rcases eq_or_ne (P γ₁) 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]
      exact hk
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr h
  have hdegP₂ : (P γ₂).natDegree < k := by
    have h := d₂.hdeg
    rw [hd₂] at h
    rcases eq_or_ne (P γ₂) 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]
      exact hk
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr h
  have hdv₁ : v₁'.natDegree < k := by
    rw [hv₁']
    refine lt_of_le_of_lt Polynomial.natDegree_mul_le ?_
    have h1 : (Polynomial.C (γ₁ - γ₂)⁻¹ : F₀[X]).natDegree = 0 := Polynomial.natDegree_C _
    have h2' : (P γ₁ - P γ₂).natDegree < k :=
      lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hdegP₁ hdegP₂)
    omega
  have hdv₀ : v₀'.natDegree < k := by
    rw [hv₀']
    refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hdegP₁ ?_)
    refine lt_of_le_of_lt Polynomial.natDegree_mul_le ?_
    have h1 : (Polynomial.C γ₁ : F₀[X]).natDegree = 0 := Polynomial.natDegree_C _
    omega
  refine ⟨v₀', v₁', hdv₀, hdv₁, fun γ hγ => ?_⟩
  rw [hv₀'eq, hv₁'eq]
  exact hP γ hγ

/-- **The funnel's `himpr` input, discharged from the heavy-agreement package + the
section link** — the Johnson-regime mirror of `cell_improvement_of_window`.  The
heavy-agreement legs produce the pinning pair (`exists_pinning_pair_of_heavy_agreement`);
the section link converts it into the decode pencil; the landed capture/improvement
lemmas finish. -/
theorem cell_improvement_of_pinning_package [Fintype F₀] [DecidableEq F₀]
    {n k : ℕ} (hn : 0 < n) [NeZero n] {domain : Fin n ↪ F₀} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)}
    {T : ℕ} (hT : 1 ≤ T) (hk : 0 < k)
    (R : (F₀[X])[X][Y]) (E : Finset F₀) (P : F₀ → F₀[X])
    (hdec : ∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ)
    -- the per-cell §5 package (the GK1+GK3 selection legs)
    (x₀ : F₀) (hHyp : Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hmonic : H.Monic)
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (e : Fin n → F₀) (he : Function.Injective e) (u₀ u₁ : Fin n → F₀)
    {D : ℕ} (hD : D ≥ Bivariate.totalDegree H)
    (matchingSet : Fin n → Finset F₀)
    (root : (z : F₀) → rationalRoot (H_tilde' H) z)
    {w : F₀[X][Y]} (hwdeg : w.natDegree < n)
    (hwdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbaseA : ∀ j, ∀ z ∈ matchingSet j, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepA : ∀ j, ∀ z ∈ matchingSet j,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
            hmonic.leadingCoeff z (root z))))).Separable)
    (hfold : ∀ j, ∀ z ∈ matchingSet j,
      (w.eval (Polynomial.C (e j) + Polynomial.C x₀)).eval z = u₀ j + z * u₁ j)
    {W : ℕ}
    (hweight : ∀ j, weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
        (Claim510Kill.killTarget H x₀ R hHyp n (e j) (u₀ j) (u₁ j)) D ≤ (W : WithBot ℕ))
    (hcard : ∀ j, W * H.natDegree < (matchingSet j).card)
    (S₀ : Finset F₀)
    (hbase₀ : ∀ z ∈ S₀, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsep₀ : ∀ z ∈ S₀,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
            hmonic.leadingCoeff z (root z))))).Separable)
    {Bw : ℕ} (hBw : ∀ t, ((Polynomial.taylor (Polynomial.C x₀) w).coeff t).natDegree ≤ Bw)
    (hS₀ : max Bw 1 < S₀.card)
    -- the section link (the cell-vocabulary reading of the surface divisibility)
    (hsec : ∀ γ ∈ E, P γ
      = ∑ t ∈ Finset.range n,
          Polynomial.C (((Polynomial.taylor (Polynomial.C x₀) w).coeff t).eval γ)
            * (Polynomial.X - Polynomial.C x₀) ^ t) :
    E.card ≤ T ∨ ∃ d₀ d₁ : Fin n → F₀, ∀ z ∈ E,
      ∃ x ∈ disagreeSet d₀ d₁, affineGap d₀ d₁ z x = 0 := by
  classical
  by_cases h2 : 1 < E.card
  · right
    -- the pinning pair from the heavy-agreement chain
    obtain ⟨v₀, v₁, hd0n, hd1n, hpin⟩ :=
      BCIKS20.Claim510CellPinning.exists_pinning_pair_of_heavy_agreement x₀ R hHyp hH
        hmonic hn htail e he u₀ u₁ hD matchingSet root hwdeg hwdvd hbaseA hsepA hfold
        hweight hcard S₀ hbase₀ hsep₀ hBw hS₀
    -- the decode pencil with RS degrees
    obtain ⟨v₀', v₁', hd0, hd1, hpencil⟩ :=
      pencil_of_pinning_and_section (n := n) (k := k) hk E P hdec v₀ v₁ hpin hsec h2
    refine ⟨fun i => v₀'.eval (domain i) - u 0 i,
      fun i => v₁'.eval (domain i) - u 1 i, fun z hz => ?_⟩
    obtain ⟨d, hdP⟩ := hdec z hz
    have hcap : AffineCaptured domain k δ u z (v₀', v₁') :=
      d.affineCaptured (by rw [hdP]; exact hpencil z hz)
    exact affineCaptured_improve hd0 hd1 hcap
  · exact Or.inl (le_trans (by omega) hT)

/-- **The section link, PROVEN**: cell divisibility + irreducibility + the surface
divisibility force each decode to be the surface's Taylor section.  Irreducibility makes
`R` an associate of `Y′ − C w`; the fiber is then a unit times `X − C w_γ`, monic-linear
divisibility pins `P = w_γ`, and Taylor's formula (mapped along `eval γ`) writes `w_γ` as
the range-`n` section sum. -/
theorem section_link {R : (F₀[X])[X][Y]} {n : ℕ}
    (hRirr : Irreducible R) {w : F₀[X][Y]} (hwdeg : w.natDegree < n)
    (hwdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (x₀ γ : F₀) (P : F₀[X])
    (hdvdP : (Polynomial.X - Polynomial.C P) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) :
    P = ∑ t ∈ Finset.range n,
      Polynomial.C (((Polynomial.taylor (Polynomial.C x₀) w).coeff t).eval γ)
        * (Polynomial.X - Polynomial.C x₀) ^ t := by
  classical
  -- step 1: `R` is an associate of the surface factor
  have hXw_nu : ¬ IsUnit (Polynomial.X - Polynomial.C w) := by
    intro hu
    have h1 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.natDegree_X_sub_C] at h1
    exact one_ne_zero h1
  obtain ⟨c, hc⟩ := hwdvd
  have hcu : IsUnit c := (hRirr.isUnit_or_isUnit hc).resolve_left hXw_nu
  -- step 2: the fiber splits as the linear section factor times a unit
  set φ : (F₀[X])[X] →+* F₀[X] := Polynomial.mapRingHom (Polynomial.evalRingHom γ) with hφ
  set wγ : F₀[X] := w.map (Polynomial.evalRingHom γ) with hwγ
  have hfiber : R.map φ = (Polynomial.X - Polynomial.C wγ) * c.map φ := by
    rw [hc, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  have hcuγ : IsUnit (c.map φ) := hcu.map (Polynomial.mapRingHom φ)
  -- step 3: strip the unit
  have hdvd2 : (Polynomial.X - Polynomial.C P) ∣ (Polynomial.X - Polynomial.C wγ) := by
    have h := hdvdP
    rw [hfiber] at h
    exact (IsUnit.dvd_mul_right hcuγ).mp h
  -- step 4: monic-linear divisibility pins `P = w_γ`
  have hPwγ : P = wγ := by
    obtain ⟨q, hq⟩ := hdvd2
    have hXw0 : (Polynomial.X - Polynomial.C wγ : F₀[X][Y]) ≠ 0 :=
      Polynomial.X_sub_C_ne_zero wγ
    have hq0 : q ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hq
      exact hXw0 hq
    have hdegq : q.natDegree = 0 := by
      have hdegs := congrArg Polynomial.natDegree hq
      rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero P) hq0,
        Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C] at hdegs
      omega
    have ha1 : q.leadingCoeff = 1 := by
      have hlc := congrArg Polynomial.leadingCoeff hq
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_X_sub_C,
        Polynomial.leadingCoeff_X_sub_C, one_mul] at hlc
      exact hlc.symm
    have hq1 : q = 1 := by
      have hC := Polynomial.eq_C_of_natDegree_eq_zero hdegq
      rw [hC] at ha1 ⊢
      rw [Polynomial.leadingCoeff_C] at ha1
      rw [ha1, Polynomial.C_1]
    rw [hq1, mul_one] at hq
    have hCC : Polynomial.C wγ = Polynomial.C P := by
      have h2 := sub_right_inj.mp hq
      exact h2
    exact (Polynomial.C_injective hCC).symm
  -- step 5: Taylor's formula for `w_γ`, mapped along `eval γ`
  rw [hPwγ, hwγ]
  have htay := Polynomial.sum_taylor_eq w (Polynomial.C x₀)
  rw [Polynomial.sum_def] at htay
  have hmap := congrArg (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) htay
  simp only [map_sum] at hmap
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.coe_evalRingHom, Polynomial.eval_C] at hmap
  -- extend the support sum to the range-`n` sum
  have hsupp : (Polynomial.taylor (Polynomial.C x₀) w).support ⊆ Finset.range n := by
    intro i hi
    rw [Finset.mem_range]
    have h1 := Polynomial.le_natDegree_of_mem_supp i hi
    rw [Polynomial.natDegree_taylor] at h1
    omega
  rw [← hmap]
  refine Finset.sum_subset hsupp fun i _ hni => ?_
  rw [Polynomial.notMem_support_iff.mp hni]
  simp

/-- **`himpr` from the package, section link DERIVED** — the cell-divisibility form: the
funnel's per-cell input with `hsec` replaced by the cell's own divisibilities. -/
theorem cell_improvement_of_pinning_package' [Fintype F₀] [DecidableEq F₀]
    {n k : ℕ} (hn : 0 < n) [NeZero n] {domain : Fin n ↪ F₀} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)}
    {T : ℕ} (hT : 1 ≤ T) (hk : 0 < k)
    (R : (F₀[X])[X][Y]) (hRirr : Irreducible R)
    (E : Finset F₀) (P : F₀ → F₀[X])
    (hdec : ∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ)
    (hdvdR : ∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    (x₀ : F₀) (hHyp : Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hmonic : H.Monic)
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (e : Fin n → F₀) (he : Function.Injective e) (u₀ u₁ : Fin n → F₀)
    {D : ℕ} (hD : D ≥ Bivariate.totalDegree H)
    (matchingSet : Fin n → Finset F₀)
    (root : (z : F₀) → rationalRoot (H_tilde' H) z)
    {w : F₀[X][Y]} (hwdeg : w.natDegree < n)
    (hwdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbaseA : ∀ j, ∀ z ∈ matchingSet j, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepA : ∀ j, ∀ z ∈ matchingSet j,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
            hmonic.leadingCoeff z (root z))))).Separable)
    (hfold : ∀ j, ∀ z ∈ matchingSet j,
      (w.eval (Polynomial.C (e j) + Polynomial.C x₀)).eval z = u₀ j + z * u₁ j)
    {W : ℕ}
    (hweight : ∀ j, weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
        (Claim510Kill.killTarget H x₀ R hHyp n (e j) (u₀ j) (u₁ j)) D ≤ (W : WithBot ℕ))
    (hcard : ∀ j, W * H.natDegree < (matchingSet j).card)
    (S₀ : Finset F₀)
    (hbase₀ : ∀ z ∈ S₀, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsep₀ : ∀ z ∈ S₀,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
            hmonic.leadingCoeff z (root z))))).Separable)
    {Bw : ℕ} (hBw : ∀ t, ((Polynomial.taylor (Polynomial.C x₀) w).coeff t).natDegree ≤ Bw)
    (hS₀ : max Bw 1 < S₀.card) :
    E.card ≤ T ∨ ∃ d₀ d₁ : Fin n → F₀, ∀ z ∈ E,
      ∃ x ∈ disagreeSet d₀ d₁, affineGap d₀ d₁ z x = 0 :=
  cell_improvement_of_pinning_package hn hT hk R E P hdec x₀ hHyp hH hmonic htail
    e he u₀ u₁ hD matchingSet root hwdeg hwdvd hbaseA hsepA hfold hweight hcard
    S₀ hbase₀ hsep₀ hBw hS₀
    (fun γ hγ => section_link hRirr hwdeg hwdvd x₀ γ (P γ) (hdvdR γ hγ))

end BCIKS20.CellPencilJohnson

/-! ## Axiom audit — all kernel-clean. -/
#print axioms BCIKS20.CellPencilJohnson.pencil_of_pinning_and_section
#print axioms BCIKS20.CellPencilJohnson.cell_improvement_of_pinning_package
#print axioms BCIKS20.CellPencilJohnson.section_link
#print axioms BCIKS20.CellPencilJohnson.cell_improvement_of_pinning_package'

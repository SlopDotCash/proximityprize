/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ShawValueCapstone

/-!
# Door IV index-factor overshoot: the naive incidence scale is `sqrt m` too large

This file formalizes the door-(iv) bookkeeping behind the current `hfloor` obstruction in
`PrizeConditionalPinCapstone`: the available naive `M -> epsMCA` incidence bridge carries an index
factor.  In Shaw-value units, replacing the prize scale `sqrt(n L)` by the naive incidence scale
`sqrt(n m L)` multiplies the normalized target by exactly `sqrt m`.

Scope: this is a Lane-2/Lane-3 constraint lemma.  It does **not** prove a character-sum bound, does
not discharge `hfloor`, and does not assert any cancellation.  It only records, axiom-clean, the
arithmetic loss that makes an L-infinity `M(n)` estimate insufficient for the realized-incidence
floor unless one also removes the index factor by a genuinely new door-(iv) argument.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot

open ArkLib.ProximityGap.Frontier.ShawValueCapstone

/-- The naive incidence scale after the index `m = (p-1)/n` has entered the bridge:
`sqrt(n * m * L)`, rather than the prize scale `sqrt(n * L)`. -/
noncomputable def naiveIncidenceScale (n m L : ℝ) : ℝ :=
  Real.sqrt (n * m * L)

/-- Closed-form comparison of scales: the naive incidence scale is exactly `sqrt m` times the
prize scale.  This is the formal version of the observed `sqrt m` index-factor overshoot. -/
theorem naiveIncidenceScale_eq_sqrt_mul_prizeScale {n m L : ℝ}
    (hm : 0 ≤ m) :
    naiveIncidenceScale n m L = Real.sqrt m * prizeScale n L := by
  unfold naiveIncidenceScale prizeScale
  rw [show n * m * L = m * (n * L) by ring]
  rw [Real.sqrt_mul hm]

/-- Ratio form: in the positive thin regime, dividing the naive incidence scale by the prize scale
leaves exactly the index factor `sqrt m`. -/
theorem naiveIncidenceScale_div_prizeScale_eq_sqrt {n m L : ℝ}
    (hn : 0 < n) (hm : 0 < m) (hL : 0 < L) :
    naiveIncidenceScale n m L / prizeScale n L = Real.sqrt m := by
  have hps : prizeScale n L ≠ 0 := ne_of_gt (prizeScale_pos hn hL)
  rw [naiveIncidenceScale_eq_sqrt_mul_prizeScale (n := n) (m := m) (L := L) (le_of_lt hm)]
  field_simp [hps]

/-- Shaw-value normalization of the naive bridge: a raw bound at the naive incidence scale is exactly
a Shaw-value bound with constant multiplied by `sqrt m`.  Thus any route that only reaches
`sqrt(n*m*L)` has already lost the index factor and cannot be a constant-Shaw/prize bound for
unbounded `m`. -/
theorem naiveIncidenceBound_iff_shawValue_le_scaled {M C n m L : ℝ}
    (hn : 0 < n) (hm : 0 ≤ m) (hL : 0 < L) :
    M ≤ C * naiveIncidenceScale n m L ↔
      shawValue M n L ≤ C * Real.sqrt m := by
  have hs : 0 < prizeScale n L := prizeScale_pos hn hL
  rw [naiveIncidenceScale_eq_sqrt_mul_prizeScale (n := n) (m := m) (L := L) hm]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (prizeBound_iff_shawValue_le (M := M) (C := C * Real.sqrt m) (n := n) (L := L) hs)

/-- If the index factor has size at least `R^2`, then the normalized naive constant is already
at least `C * R`.  Thus in a family with unbounded `m`, the naive bridge cannot supply a uniform
constant unless some separate argument removes the index factor. -/
theorem scaledConstant_ge_linear_floor {C m R : ℝ}
    (hC : 0 ≤ C) (hm : R ^ 2 ≤ m) :
    C * R ≤ C * Real.sqrt m := by
  have hRsqrt : R ≤ Real.sqrt m := Real.le_sqrt_of_sq_le hm
  exact mul_le_mul_of_nonneg_left hRsqrt hC

/-- Family form of the lower-floor obstruction: a pointwise lower bound `R i ^ 2 ≤ m i` forces
the normalized naive constant `C i * sqrt(m i)` to dominate the growing floor `C i * R i`. -/
theorem scaledConstantFamily_ge_linear_floor {ι : Type*} {C m R : ι → ℝ}
    (hC : ∀ i, 0 ≤ C i) (hm : ∀ i, R i ^ 2 ≤ m i) :
    ∀ i, C i * R i ≤ C i * Real.sqrt (m i) := by
  intro i
  exact scaledConstant_ge_linear_floor (hC i) (hm i)

/-- A bounded normalized naive constant forces the index itself to be bounded.  This is the
contrapositive-facing form of the `sqrt(m)` obstruction: with a fixed positive raw constant `C`, any
uniform cap `D` on `C sqrt(m)` implies `m ≤ (D/C)^2`.  Hence an unbounded-index family cannot have a
uniform Shaw constant through the naive bridge. -/
theorem index_le_sq_of_scaledConstant_le {C m D : ℝ}
    (hC : 0 < C) (hm : 0 ≤ m) (hbound : C * Real.sqrt m ≤ D) :
    m ≤ (D / C) ^ 2 := by
  have hsqrt_le : Real.sqrt m ≤ D / C := by
    rw [le_div_iff₀ hC]
    nlinarith
  have hsq : (Real.sqrt m) ^ 2 ≤ (D / C) ^ 2 := by
    exact pow_le_pow_left₀ (Real.sqrt_nonneg m) hsqrt_le 2
  rwa [Real.sq_sqrt hm] at hsq

/-- Family form of the bounded-index consequence: a uniform cap on the normalized naive constant
`C i * sqrt (m i)` gives a pointwise bound on every index `m i`.  This is the probe-facing
contrapositive of the overshoot wall: an unbounded-index family cannot pass through the naive bridge
with bounded Shaw constants. -/
theorem indexFamily_le_sq_of_scaledConstant_le {ι : Type*} {C m D : ι → ℝ}
    (hC : ∀ i, 0 < C i) (hm : ∀ i, 0 ≤ m i)
    (hbound : ∀ i, C i * Real.sqrt (m i) ≤ D i) :
    ∀ i, m i ≤ (D i / C i) ^ 2 := by
  intro i
  exact index_le_sq_of_scaledConstant_le (hC i) (hm i) (hbound i)

/-- Constant-raw-family specialization: with a fixed positive raw constant `C` and fixed uniform Shaw
cap `D`, every index in the family is bounded by the same number `(D/C)^2`.  Thus an actually
unbounded index parameter is incompatible with any proof that only normalizes the naive
`sqrt(n*m*L)` bridge. -/
theorem indexFamily_le_uniform_sq_of_scaledConstant_le {ι : Type*} {C D : ℝ} {m : ι → ℝ}
    (hC : 0 < C) (hm : ∀ i, 0 ≤ m i)
    (hbound : ∀ i, C * Real.sqrt (m i) ≤ D) :
    ∀ i, m i ≤ (D / C) ^ 2 := by
  intro i
  exact index_le_sq_of_scaledConstant_le hC (hm i) (hbound i)

/-- Contrapositive uniform-family obstruction: one index larger than `(D/C)^2` refutes any uniform cap
`C * sqrt(m i) ≤ D` on the naive normalized constant.  This is the exact finite witness form of the
unbounded-index wall. -/
theorem not_scaledConstantFamily_le_uniform_of_exists_index_gt_sq {ι : Type*} {C D : ℝ}
    {m : ι → ℝ} (hC : 0 < C) (hm : ∀ i, 0 ≤ m i)
    (hlarge : ∃ i, (D / C) ^ 2 < m i) :
    ¬ ∀ i, C * Real.sqrt (m i) ≤ D := by
  intro hbound
  rcases hlarge with ⟨i, hi⟩
  have hindex := indexFamily_le_uniform_sq_of_scaledConstant_le (C := C) (D := D) (m := m)
    hC hm hbound i
  exact (not_lt_of_ge hindex) hi

/-- Exact pointwise cap criterion for a nonnegative advertised Shaw cap.  With positive raw constant
`C`, nonnegative index `m`, and nonnegative uniform cap `D`, the naive normalized cap
`C sqrt(m) ≤ D` is equivalent to the finite index constraint `m ≤ (D/C)^2`.  Thus the index-factor
obstruction is not merely one-way: every proposed cap is exactly a bound on the hidden index. -/
theorem scaledConstant_le_iff_index_le_sq {C m D : ℝ}
    (hC : 0 < C) (hm : 0 ≤ m) (hD : 0 ≤ D) :
    C * Real.sqrt m ≤ D ↔ m ≤ (D / C) ^ 2 := by
  constructor
  · exact index_le_sq_of_scaledConstant_le hC hm
  · intro hindex
    have hDdiv : 0 ≤ D / C := div_nonneg hD (le_of_lt hC)
    have hsqrt_le : Real.sqrt m ≤ D / C := by
      have hsqrt_sq : Real.sqrt m ≤ Real.sqrt ((D / C) ^ 2) := Real.sqrt_le_sqrt hindex
      rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg hDdiv] at hsqrt_sq
    have hmul : C * Real.sqrt m ≤ C * (D / C) :=
      mul_le_mul_of_nonneg_left hsqrt_le (le_of_lt hC)
    have hright : C * (D / C) = D := by
      field_simp [ne_of_gt hC]
    simpa [hright] using hmul

/-- Family form of the exact cap criterion: for positive fixed raw constant `C` and nonnegative cap
`D`, a uniform naive normalized Shaw cap is equivalent to bounding every index by `(D/C)^2`.  This is
an axiom-clean audit hook for claims that the `sqrt(m)` loss has somehow disappeared. -/
theorem scaledConstantFamily_le_uniform_iff_indexFamily_le_sq {ι : Type*} {C D : ℝ}
    {m : ι → ℝ} (hC : 0 < C) (hm : ∀ i, 0 ≤ m i) (hD : 0 ≤ D) :
    (∀ i, C * Real.sqrt (m i) ≤ D) ↔ ∀ i, m i ≤ (D / C) ^ 2 := by
  constructor
  · exact indexFamily_le_uniform_sq_of_scaledConstant_le hC hm
  · intro hindex i
    exact (scaledConstant_le_iff_index_le_sq (C := C) (m := m i) (D := D)
      hC (hm i) hD).2 (hindex i)

/-- Pointwise version of the same obstruction: if the index is already above `(D/C)^2`, then the
normalized naive constant cannot be capped by `D`. -/
theorem not_scaledConstant_le_of_index_gt_sq {C m D : ℝ}
    (hC : 0 < C) (hm : 0 ≤ m) (hlarge : (D / C) ^ 2 < m) :
    ¬ C * Real.sqrt m ≤ D := by
  intro hbound
  have hindex := index_le_sq_of_scaledConstant_le hC hm hbound
  exact (not_lt_of_ge hindex) hlarge

/-- Degenerate index-one endpoint: if the index factor is absent, the naive incidence scale is
exactly the prize scale.  This identifies the only endpoint where the bridge has no scale loss;
the thin prize regime has `m` growing, not `m = 1`. -/
theorem naiveIncidenceScale_eq_prizeScale_of_m_eq_one {n L : ℝ} :
    naiveIncidenceScale n 1 L = prizeScale n L := by
  rw [naiveIncidenceScale_eq_sqrt_mul_prizeScale (n := n) (m := 1) (L := L) zero_le_one]
  simp

/-- Constant endpoint for the same degenerate case: the normalized naive constant `C√m` equals `C`
only at the index-one scale-loss-free endpoint. -/
theorem scaled_constant_eq_constant_of_m_eq_one {C : ℝ} :
    C * Real.sqrt (1 : ℝ) = C := by
  simp

/-- **Exact equality criterion for the index factor.**  With positive raw constant and nonnegative
index, the normalized naive constant `C√m` equals the desired constant `C` if and only if the index is
exactly `m = 1`.  Thus equality is not hidden bookkeeping slack: it is precisely the degenerate
index-one endpoint, while every genuine indexed regime must either inflate or deflate away from that
endpoint. -/
theorem scaled_constant_eq_constant_iff {C m : ℝ} (hC : 0 < C) (hm : 0 ≤ m) :
    C * Real.sqrt m = C ↔ m = 1 := by
  constructor
  · intro h
    have hs : Real.sqrt m = 1 := by
      have h' : Real.sqrt m * C = (1 : ℝ) * C := by simpa [mul_comm] using h
      exact (mul_left_inj' (ne_of_gt hC)).mp h'
    have hsq := congrArg (fun x : ℝ => x ^ 2) hs
    simpa [Real.sq_sqrt hm] using hsq
  · intro hm1
    rw [hm1]
    simp

/-- Family endpoint criterion for exact no-loss normalization: with a fixed positive raw constant,
a whole indexed family has normalized naive constants exactly equal to the desired constant iff every
index is the degenerate no-overshoot endpoint `m_i = 1`.  This is the family audit hook for claims that
the `sqrt(m)` factor disappears uniformly. -/
theorem scaled_constant_family_eq_constant_iff {ι : Type*} {C : ℝ} {m : ι → ℝ}
    (hC : 0 < C) (hm : ∀ i, 0 ≤ m i) :
    (∀ i, C * Real.sqrt (m i) = C) ↔ ∀ i, m i = 1 := by
  constructor
  · intro h i
    exact (scaled_constant_eq_constant_iff (C := C) (m := m i) hC (hm i)).1 (h i)
  · intro h i
    exact (scaled_constant_eq_constant_iff (C := C) (m := m i) hC (hm i)).2 (h i)

/-- In the actual indexed regime `1 ≤ m`, the naive incidence scale is never smaller than the
prize scale.  Thus the bridge cannot secretly improve the Shaw normalization by the index step; it
only preserves scale at `m = 1` and overshoots afterwards. -/
theorem prizeScale_le_naiveIncidenceScale_of_one_le_m {n m L : ℝ}
    (hn : 0 < n) (hm : 1 ≤ m) (hL : 0 < L) :
    prizeScale n L ≤ naiveIncidenceScale n m L := by
  rw [naiveIncidenceScale_eq_sqrt_mul_prizeScale (n := n) (m := m) (L := L)
      (le_trans zero_le_one hm)]
  have hps_nonneg : 0 ≤ prizeScale n L := le_of_lt (prizeScale_pos hn hL)
  have hsqrt_one : (1 : ℝ) ≤ Real.sqrt m := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hm
  nlinarith

/-- The normalized constant loss is also monotone: if the raw constant is nonnegative and `m ≥ 1`,
then the naive bridge's Shaw constant `C√m` is at least `C`.  Any constant-Shaw conclusion would
therefore need an independent argument removing this factor. -/
theorem constant_le_scaled_constant_of_one_le_m {C m : ℝ} (hC : 0 ≤ C) (hm : 1 ≤ m) :
    C ≤ C * Real.sqrt m := by
  have hsqrt_one : (1 : ℝ) ≤ Real.sqrt m := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hm
  nlinarith

/-- Exact non-overshoot criterion for the normalized constant.  For a positive raw constant and
nonnegative index, the naive bridge's inflated Shaw constant dominates the desired constant iff
`m ≥ 1`.  Thus any indexed regime beyond the degenerate endpoint necessarily pays the named
`sqrt(m)` factor; there is no extra normalization slack to hide it. -/
theorem constant_le_scaled_constant_iff_one_le_m {C m : ℝ} (hC : 0 < C) (hm0 : 0 ≤ m) :
    C ≤ C * Real.sqrt m ↔ 1 ≤ m := by
  constructor
  · intro h
    have hsqrt_one : (1 : ℝ) ≤ Real.sqrt m := by
      have hdiv : C / C ≤ (C * Real.sqrt m) / C :=
        div_le_div_of_nonneg_right h (le_of_lt hC)
      have hleft : C / C = (1 : ℝ) := div_self (ne_of_gt hC)
      have hright : (C * Real.sqrt m) / C = Real.sqrt m := by
        field_simp [ne_of_gt hC]
      rwa [hleft, hright] at hdiv
    have hsq : (1 : ℝ) ^ 2 ≤ (Real.sqrt m) ^ 2 :=
      pow_le_pow_left₀ zero_le_one hsqrt_one 2
    simpa [Real.sq_sqrt hm0] using hsq
  · exact constant_le_scaled_constant_of_one_le_m (le_of_lt hC)

/-- Strict scale form: once the index is genuinely nontrivial (`m > 1`), the naive incidence scale is
strictly larger than the prize scale.  Equality of the two scales is therefore exactly the degenerate
index-one case, not the thin prize regime. -/
theorem prizeScale_lt_naiveIncidenceScale_of_one_lt_m {n m L : ℝ}
    (hn : 0 < n) (hm : 1 < m) (hL : 0 < L) :
    prizeScale n L < naiveIncidenceScale n m L := by
  rw [naiveIncidenceScale_eq_sqrt_mul_prizeScale (n := n) (m := m) (L := L)
      (le_trans zero_le_one (le_of_lt hm))]
  have hps : 0 < prizeScale n L := prizeScale_pos hn hL
  have hsqrt_one : (1 : ℝ) < Real.sqrt m := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt zero_le_one hm
  nlinarith

/-- Strict normalized-constant form: with a positive raw constant and a genuinely nontrivial index,
the normalized naive Shaw constant is strictly larger than the desired constant.  Thus the index
factor is a real loss, not just a weak inequality, throughout the thin indexed regime. -/
theorem constant_lt_scaled_constant_of_one_lt_m {C m : ℝ} (hC : 0 < C) (hm : 1 < m) :
    C < C * Real.sqrt m := by
  have hsqrt_one : (1 : ℝ) < Real.sqrt m := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt zero_le_one hm
  nlinarith

/-- Contrapositive-facing form: at a genuinely nontrivial index and positive raw constant, the naive
normalized constant cannot stay below the desired constant.  Any proof of a constant Shaw bound that
passes through the naive scale must therefore remove the index factor before this step. -/
theorem not_scaled_constant_le_constant_of_one_lt_m {C m : ℝ} (hC : 0 < C) (hm : 1 < m) :
    ¬ C * Real.sqrt m ≤ C := by
  exact not_le_of_gt (constant_lt_scaled_constant_of_one_lt_m hC hm)

/-- Exact strict-overshoot criterion for the normalized constant.  For a positive raw constant and
nonnegative index, the naive bridge's Shaw constant is strictly larger than the desired constant if
and only if the hidden index is genuinely nontrivial (`1 < m`).  This is the strict analogue of
`constant_le_scaled_constant_iff_one_le_m`: no strict gain or loss can be hidden at the endpoint. -/
theorem constant_lt_scaled_constant_iff_one_lt_m {C m : ℝ} (hC : 0 < C) (hm0 : 0 ≤ m) :
    C < C * Real.sqrt m ↔ 1 < m := by
  constructor
  · intro h
    have hsqrt_one : (1 : ℝ) < Real.sqrt m := by
      have hdiv : C / C < (C * Real.sqrt m) / C :=
        div_lt_div_of_pos_right h hC
      have hleft : C / C = (1 : ℝ) := div_self (ne_of_gt hC)
      have hright : (C * Real.sqrt m) / C = Real.sqrt m := by
        field_simp [ne_of_gt hC]
      rwa [hleft, hright] at hdiv
    have hsq : (1 : ℝ) ^ 2 < (Real.sqrt m) ^ 2 := by
      apply sq_lt_sq' <;> linarith [Real.sqrt_nonneg m]
    simpa [Real.sq_sqrt hm0] using hsq
  · exact constant_lt_scaled_constant_of_one_lt_m hC

/-- Exact strict-overshoot criterion for the scales themselves.  In the positive thin regime, the
naive incidence scale is strictly larger than the prize scale exactly when the hidden index is
strictly larger than one. -/
theorem prizeScale_lt_naiveIncidenceScale_iff_one_lt_m {n m L : ℝ}
    (hn : 0 < n) (hm0 : 0 ≤ m) (hL : 0 < L) :
    prizeScale n L < naiveIncidenceScale n m L ↔ 1 < m := by
  rw [naiveIncidenceScale_eq_sqrt_mul_prizeScale (n := n) (m := m) (L := L) hm0]
  simpa [mul_comm] using
    (constant_lt_scaled_constant_iff_one_lt_m (C := prizeScale n L) (m := m)
      (prizeScale_pos hn hL) hm0)

/-- Uniform-family form of the same obstruction: pointwise naive incidence bounds normalize to a
Shaw-value family bound whose pointwise constant is multiplied by `sqrt(m i)`.  This is only scale
bookkeeping; the analytic loss remains in the hypotheses. -/
theorem shawValueFamilyBound_of_naiveIncidenceBound {ι : Type*}
    {M n m L C : ι → ℝ}
    (hn : ∀ i, 0 < n i) (hm : ∀ i, 0 ≤ m i) (hL : ∀ i, 0 < L i)
    (hraw : ∀ i, M i ≤ C i * naiveIncidenceScale (n i) (m i) (L i)) :
    ∀ i, shawValue (M i) (n i) (L i) ≤ C i * Real.sqrt (m i) := by
  intro i
  exact (naiveIncidenceBound_iff_shawValue_le_scaled
    (M := M i) (C := C i) (n := n i) (m := m i) (L := L i)
    (hn i) (hm i) (hL i)).1 (hraw i)

/-- Reversible family form of the index-factor bookkeeping.  Pointwise naive-incidence bounds at
scale `sqrt(n*m*L)` are exactly pointwise Shaw-value bounds with the inflated constant `C_i sqrt(m_i)`.
This is the family-level converse to `shawValueFamilyBound_of_naiveIncidenceBound`; it records that
normalization introduces no hidden slack beyond the named index factor. -/
theorem naiveIncidenceFamilyBound_iff_shawValueFamilyBound_scaled {ι : Type*}
    {M n m L C : ι → ℝ}
    (hn : ∀ i, 0 < n i) (hm : ∀ i, 0 ≤ m i) (hL : ∀ i, 0 < L i) :
    (∀ i, M i ≤ C i * naiveIncidenceScale (n i) (m i) (L i)) ↔
      (∀ i, shawValue (M i) (n i) (L i) ≤ C i * Real.sqrt (m i)) := by
  constructor
  · exact shawValueFamilyBound_of_naiveIncidenceBound hn hm hL
  · intro h i
    exact (naiveIncidenceBound_iff_shawValue_le_scaled
      (M := M i) (C := C i) (n := n i) (m := m i) (L := L i)
      (hn i) (hm i) (hL i)).2 (h i)

/-- Wall-facing family form of the same exact bookkeeping.  Failure of the pointwise inflated
Shaw-value bound is exactly failure of the corresponding naive-incidence family bound.  This is the
contrapositive audit hook: a claimed passage through `sqrt(n*m*L)` cannot evade the `sqrt(m)` loss by
switching normalizations. -/
theorem not_naiveIncidenceFamilyBound_iff_not_shawValueFamilyBound_scaled {ι : Type*}
    {M n m L C : ι → ℝ}
    (hn : ∀ i, 0 < n i) (hm : ∀ i, 0 ≤ m i) (hL : ∀ i, 0 < L i) :
    ¬ (∀ i, M i ≤ C i * naiveIncidenceScale (n i) (m i) (L i)) ↔
      ¬ (∀ i, shawValue (M i) (n i) (L i) ≤ C i * Real.sqrt (m i)) :=
  not_congr (naiveIncidenceFamilyBound_iff_shawValueFamilyBound_scaled hn hm hL)

/-- Single-witness failure form: one index whose inflated Shaw-value inequality fails refutes the
whole naive-incidence family certificate.  This is the probe-facing way to log an index-factor wall
without scanning redundant instances after a bad member is found. -/
theorem not_naiveIncidenceFamilyBound_of_exists_scaledShawValue_gt {ι : Type*}
    {M n m L C : ι → ℝ}
    (hn : ∀ i, 0 < n i) (hm : ∀ i, 0 ≤ m i) (hL : ∀ i, 0 < L i)
    (hbad : ∃ i, C i * Real.sqrt (m i) < shawValue (M i) (n i) (L i)) :
    ¬ ∀ i, M i ≤ C i * naiveIncidenceScale (n i) (m i) (L i) := by
  rw [not_naiveIncidenceFamilyBound_iff_not_shawValueFamilyBound_scaled hn hm hL]
  intro hscaled
  rcases hbad with ⟨i, hi⟩
  exact (not_lt_of_ge (hscaled i)) hi

end ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot

#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceScale_eq_sqrt_mul_prizeScale
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceScale_div_prizeScale_eq_sqrt
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceBound_iff_shawValue_le_scaled
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.scaledConstant_ge_linear_floor
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.scaledConstantFamily_ge_linear_floor
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.index_le_sq_of_scaledConstant_le
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.indexFamily_le_sq_of_scaledConstant_le
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.indexFamily_le_uniform_sq_of_scaledConstant_le
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.not_scaledConstantFamily_le_uniform_of_exists_index_gt_sq
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.scaledConstant_le_iff_index_le_sq
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.scaledConstantFamily_le_uniform_iff_indexFamily_le_sq
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.not_scaledConstant_le_of_index_gt_sq
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceScale_eq_prizeScale_of_m_eq_one
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.scaled_constant_eq_constant_of_m_eq_one
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.scaled_constant_eq_constant_iff
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.scaled_constant_family_eq_constant_iff
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.prizeScale_le_naiveIncidenceScale_of_one_le_m
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.constant_le_scaled_constant_of_one_le_m
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.constant_le_scaled_constant_iff_one_le_m
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.prizeScale_lt_naiveIncidenceScale_of_one_lt_m
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.constant_lt_scaled_constant_of_one_lt_m
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.not_scaled_constant_le_constant_of_one_lt_m
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.constant_lt_scaled_constant_iff_one_lt_m
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.prizeScale_lt_naiveIncidenceScale_iff_one_lt_m
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.shawValueFamilyBound_of_naiveIncidenceBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceFamilyBound_iff_shawValueFamilyBound_scaled
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.not_naiveIncidenceFamilyBound_iff_not_shawValueFamilyBound_scaled
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.not_naiveIncidenceFamilyBound_of_exists_scaledShawValue_gt

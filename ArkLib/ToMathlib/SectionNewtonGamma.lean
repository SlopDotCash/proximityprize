/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.PowerSeriesNewton
import ArkLib.ToMathlib.HenselUniqueness
import ArkLib.ToMathlib.NewtonTailEntry
import ArkLib.ToMathlib.PolyRootGradedBound

/-!
# The γ-assembly: Newton data → polynomial root → graded integral preimage (#304)

This file composes the four proven bricks of the elementary [BCIKS20] App-A.2 route into a
single engine-ready pipeline over a general commutative ring / field `k` (the target
instantiation is `k := RatFunc F`):

1. **γ exists + root** (`exists_gamma_root`, `isRoot_gamma`, `gamma_sub_C_mem_span`):
   the explicit Newton root `γ Q c` of `ProximityPrize.HenselSeriesCoeff` is an exact root of
   `Q : Polynomial k⟦X⟧` congruent to `C c` modulo `X`.  The hypothesis bridges
   `eval_C_mem_span_iff` / `isUnit_derivative_eval_C_iff` translate between the
   `a₀ := C c`-seed language of `ArkLib.powerSeries_newton_root` and the order-0-reduction
   language (`Q₀ := Q.map constantCoeff`) of the coefficient-recursive construction.
   `newton_root_choose_eq_gamma` identifies the abstract Newton-limit root of
   `powerSeries_newton_root` with the explicit `γ Q c` (via `hensel_root_unique`), so all
   downstream facts about either apply to both.

2. **tail-to-polynomial** (`gamma_eq_coe_trunc_of_window`, `exists_polynomial_gamma_of_window`):
   if the coefficients of `γ Q c` vanish on the counting window `[k, DX + deg_Y Q · (k−1)]`
   (the `NewtonTailEntry` hypothesis), the whole tail vanishes
   (`tail_of_range_vanish_of_polyQ`) and `γ Q c` **is** the coercion of the polynomial
   `trunc k (γ Q c)` of `natDegree < k`.

3. **polynomial root descent** (`polynomial_eval_eq_zero_of_coe_eval`): if `Q` has polynomial
   coefficients — `Q = QP.map coeToPowerSeries.ringHom` — the root identity over `k⟦X⟧`
   descends along the injective coercion `k[X] →+* k⟦X⟧` to the *polynomial* identity
   `Polynomial.eval γpoly QP = 0`, exactly the `hroot` field of
   `ArkLib.PolyRootGradedBound.exists_graded_preimage_of_eval_monic_eq_zero`.

4. **The fused statement** (`newton_window_graded_preimage`, and its `RatFunc`
   instantiation `newton_window_graded_preimage_ratFunc`): Newton seed data + window-vanish +
   polynomial coefficients + monic + balanced slope-`s` grading produce `g : B[X][Y]` with
   `g.map (algebraMap B[X] K) = trunc k (γ Q c)`, `↑(trunc k (γ Q c)) = γ Q c`, and **every**
   coefficient of `g` of inner degree ≤ `s` — the Claim-5.8 conclusion with the
   `ξ`-order/Λ-weight machinery fully eliminated.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Claim 5.8), Appendix A.2/A.4.
-/

set_option linter.style.longLine false

open PowerSeries ProximityPrize.HenselSeriesCoeff

namespace ArkLib

namespace SectionNewtonGamma

variable {R : Type*} [CommRing R]

/-! ## Hypothesis bridges: `C c`-seed language ↔ order-0-reduction language -/

/-- The order-0 reduction commutes with `derivative`. -/
theorem derivative_Q₀ (Q : Polynomial (PowerSeries R)) :
    Polynomial.derivative (Q₀ Q) = Q₀ (Polynomial.derivative Q) := by
  unfold Q₀
  exact Polynomial.derivative_map Q (constantCoeff (R := R))

/-- The seed-congruence hypothesis of `powerSeries_newton_root` at `a₀ := C c` **is** the
order-0 root hypothesis of the coefficient-recursive construction. -/
theorem eval_C_mem_span_iff (Q : Polynomial (PowerSeries R)) (c : R) :
    Polynomial.eval (PowerSeries.C c) Q ∈ Ideal.span {(X : PowerSeries R)}
      ↔ Polynomial.eval c (Q₀ Q) = 0 := by
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, constantCoeff_eval, constantCoeff_C]

/-- The unit-derivative hypothesis of `powerSeries_newton_root` at `a₀ := C c` **is** the
order-0 simpleness hypothesis of the coefficient-recursive construction.  Power series over any
commutative ring are units iff their constant coefficient is. -/
theorem isUnit_derivative_eval_C_iff (Q : Polynomial (PowerSeries R)) (c : R) :
    IsUnit (Polynomial.eval (PowerSeries.C c) (Polynomial.derivative Q))
      ↔ IsUnit (Polynomial.eval c (Polynomial.derivative (Q₀ Q))) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_eval, constantCoeff_C,
    ← derivative_Q₀]

/-! ## Deliverable 1: γ exists, is a root, and is congruent to `C c` modulo `X` -/

section GammaFacts

variable (Q : Polynomial (PowerSeries R)) (c : R)
variable (hc0 : Polynomial.eval c (Q₀ Q) = 0)
variable (hu : IsUnit (Polynomial.eval c (Polynomial.derivative (Q₀ Q))))

include hc0 hu in
/-- The explicit Newton root `γ Q c` is an exact root of `Q`. -/
theorem isRoot_gamma : Q.IsRoot (γ Q c) :=
  eval_γ_eq_zero Q c hc0 hu

/-- The explicit Newton root is congruent to its seed `C c` modulo `X`. -/
theorem gamma_sub_C_mem_span :
    γ Q c - PowerSeries.C c ∈ Ideal.span {(X : PowerSeries R)} := by
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub, constantCoeff_γ,
    constantCoeff_C, sub_self]

include hc0 hu in
/-- **γ exists + root** (deliverable 1, seriesCoeff shape, any commutative ring): there is a
power series root of `Q` congruent to `C c` modulo `X` — witnessed by the *explicit*
coefficient-recursive `γ Q c`, whose coefficients `NewtonTailEntry` can reason about. -/
theorem exists_gamma_root :
    ∃ a : PowerSeries R, Polynomial.eval a Q = 0 ∧
      a - PowerSeries.C c ∈ Ideal.span {(X : PowerSeries R)} :=
  ⟨γ Q c, eval_γ_eq_zero Q c hc0 hu, gamma_sub_C_mem_span Q c⟩

include hc0 hu in
/-- **Identification lemma**: *any* root of `Q` congruent to `C c` modulo `X` is the explicit
Newton root `γ Q c` (uniqueness of the simple Hensel lift, over any commutative ring). -/
theorem eq_gamma_of_isRoot {b : PowerSeries R} (hb_root : Q.IsRoot b)
    (hb_sub : b - PowerSeries.C c ∈ Ideal.span {(X : PowerSeries R)}) :
    b = γ Q c := by
  have hcc : constantCoeff (R := R) b = c := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub, constantCoeff_C,
      sub_eq_zero] at hb_sub
    exact hb_sub
  refine root_unique_seriesCoeff (Q := Q) ?_ ?_ hb_root (eval_γ_eq_zero Q c hc0 hu)
  · rw [hcc, constantCoeff_γ]
  · rw [hcc]; exact hu

end GammaFacts

/-- Thin wrapper for `powerSeries_newton_root` in the plain-`eval` shape (deliverable 1,
general seed `a₀`, field case). -/
theorem exists_newton_root_eval {k : Type*} [Field k] (f : Polynomial (PowerSeries k))
    (a₀ : PowerSeries k)
    (h₁ : Polynomial.eval a₀ f ∈ Ideal.span {(X : PowerSeries k)})
    (h₂ : IsUnit (Polynomial.eval a₀ (Polynomial.derivative f))) :
    ∃ a : PowerSeries k, Polynomial.eval a f = 0 ∧
      a - a₀ ∈ Ideal.span {(X : PowerSeries k)} :=
  powerSeries_newton_root f a₀ h₁ h₂

/-- **The two Newton iterations agree**: the abstract `X`-adic-limit root chosen by
`powerSeries_newton_root` (seed `C c`) is exactly the coefficient-recursive `γ Q c` of
`HenselSeriesCoeff`/`NewtonTailEntry`.  Consequence of `hensel_root_unique` via
`newton_root_eq_of_isRoot`. -/
theorem newton_root_choose_eq_gamma {k : Type*} [Field k]
    (Q : Polynomial (PowerSeries k)) (c : k)
    (hc0 : Polynomial.eval c (Q₀ Q) = 0)
    (hu : IsUnit (Polynomial.eval c (Polynomial.derivative (Q₀ Q)))) :
    (powerSeries_newton_root Q (PowerSeries.C c)
        ((eval_C_mem_span_iff Q c).mpr hc0)
        ((isUnit_derivative_eval_C_iff Q c).mpr hu)).choose = γ Q c :=
  newton_root_eq_of_isRoot Q (PowerSeries.C c)
    ((eval_C_mem_span_iff Q c).mpr hc0)
    ((isUnit_derivative_eval_C_iff Q c).mpr hu)
    (isRoot_gamma Q c hc0 hu) (gamma_sub_C_mem_span Q c)

/-! ## Deliverable 2: tail-vanishing makes γ a polynomial -/

/-- A power series with vanishing tail above `n` is the coercion of its `n`-truncation. -/
theorem coe_trunc_eq_of_tail {φ : PowerSeries R} {n : ℕ}
    (h : ∀ t, n ≤ t → PowerSeries.coeff t φ = 0) :
    ((trunc n φ : Polynomial R) : PowerSeries R) = φ := by
  ext t
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with ht
  · rfl
  · exact (h t (Nat.le_of_not_lt ht)).symm

/-- Truncation below a positive bound has `natDegree` strictly below it. -/
theorem natDegree_trunc_lt' (φ : PowerSeries R) {n : ℕ} (hn : 0 < n) :
    (trunc n φ).natDegree < n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact natDegree_trunc_lt φ m

section Window

variable (Q : Polynomial (PowerSeries R)) (c : R)
variable (hc0 : Polynomial.eval c (Q₀ Q) = 0)
variable (hu : IsUnit (Polynomial.eval c (Polynomial.derivative (Q₀ Q))))

include hc0 hu in
/-- **Tail-to-polynomial** (deliverable 2): window-vanish on `[k, DX + deg_Y Q · (k−1)]` plus
the coefficient-support bound `DX` for `Q` force `γ Q c` to *be* (the coercion of) the
polynomial `trunc k (γ Q c)`. -/
theorem gamma_eq_coe_trunc_of_window {DX k : ℕ} (hk : 0 < k)
    (hQX : ∀ i, ∀ a, DX < a → PowerSeries.coeff a (Q.coeff i) = 0)
    (hwindow : ∀ t, k ≤ t → t ≤ DX + Q.natDegree * (k - 1) →
      PowerSeries.coeff t (γ Q c) = 0) :
    ((trunc k (γ Q c) : Polynomial R) : PowerSeries R) = γ Q c :=
  coe_trunc_eq_of_tail (tail_of_range_vanish_of_polyQ Q c hc0 hu hk hQX hwindow)

include hc0 hu in
/-- Deliverable 2, existential packaging: under window-vanish, `γ Q c` is a polynomial of
`natDegree < k`. -/
theorem exists_polynomial_gamma_of_window {DX k : ℕ} (hk : 0 < k)
    (hQX : ∀ i, ∀ a, DX < a → PowerSeries.coeff a (Q.coeff i) = 0)
    (hwindow : ∀ t, k ≤ t → t ≤ DX + Q.natDegree * (k - 1) →
      PowerSeries.coeff t (γ Q c) = 0) :
    ∃ γp : Polynomial R, (γp : PowerSeries R) = γ Q c ∧ γp.natDegree < k :=
  ⟨trunc k (γ Q c), gamma_eq_coe_trunc_of_window Q c hc0 hu hk hQX hwindow,
    natDegree_trunc_lt' _ hk⟩

end Window

/-! ## Deliverable 3: polynomial root descent along `k[X] →+* k⟦X⟧` -/

/-- **Polynomial root descent**: if `Q = QP.map coeToPowerSeries.ringHom` has polynomial
coefficients and the polynomial-valued series `↑γp` is a root of `Q`, then `γp` is a root of
`QP` *as a polynomial identity* — the `hroot` shape consumed by
`PolyRootGradedBound.exists_graded_preimage_of_eval_monic_eq_zero`. -/
theorem polynomial_eval_eq_zero_of_coe_eval {QP : Polynomial (Polynomial R)}
    {γp : Polynomial R}
    (h : Polynomial.eval (γp : PowerSeries R)
      (QP.map (Polynomial.coeToPowerSeries.ringHom)) = 0) :
    Polynomial.eval γp QP = 0 := by
  apply Polynomial.coe_injective R
  rw [Polynomial.coe_zero]
  calc ((Polynomial.eval γp QP : Polynomial R) : PowerSeries R)
      = Polynomial.coeToPowerSeries.ringHom (Polynomial.eval γp QP) := rfl
    _ = Polynomial.eval₂ Polynomial.coeToPowerSeries.ringHom
          (Polynomial.coeToPowerSeries.ringHom γp) QP :=
        (Polynomial.eval₂_at_apply _ γp).symm
    _ = Polynomial.eval (γp : PowerSeries R)
          (QP.map Polynomial.coeToPowerSeries.ringHom) := by
        rw [Polynomial.eval_map, Polynomial.coeToPowerSeries.ringHom_apply]
    _ = 0 := h

/-! ## Deliverable 4: the fused statement — Newton data + window-vanish + grading ⟹
integral polynomial root of inner degree ≤ s -/

/-- **The fused γ-assembly** ([BCIKS20] Claim 5.8, elementary route, engine-ready): let `B` be
an integrally closed domain with fraction field `K` of `B[X]` (e.g. `B := F` a field,
`K := RatFunc F`).  Given
* `P : (B[X][Y])[T]` monic of positive degree with the balanced slope-`s` grading,
* its fraction-field image `QP` and series-coefficient image `Q`,
* Newton seed data `c` (order-0 root, unit derivative), and
* window-vanish for `γ Q c` on `[k, DX + deg_T Q · (k−1)]`,

the explicit Newton root `γ Q c` is the coercion of the polynomial `trunc k (γ Q c)`, which
descends to `g : B[X][Y]` with **every** coefficient of inner degree at most `s`. -/
theorem newton_window_graded_preimage
    {B K : Type*} [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [CommRing K] [Algebra (Polynomial B) K] [IsFractionRing (Polynomial B) K]
    {P : Polynomial (Polynomial (Polynomial B))} {s : ℕ}
    {QP : Polynomial (Polynomial K)} {Q : Polynomial (PowerSeries K)}
    (hQP : QP = P.map (Polynomial.mapRingHom (algebraMap (Polynomial B) K)))
    (hQ : Q = QP.map Polynomial.coeToPowerSeries.ringHom)
    (hmonic : P.Monic) (hd : P.natDegree ≠ 0)
    (hgrade : ∀ c < P.natDegree, ∀ j, ((P.coeff c).coeff j).natDegree ≤ s * (P.natDegree - c))
    {c : K}
    (hc0 : Polynomial.eval c (Q₀ Q) = 0)
    (hu : IsUnit (Polynomial.eval c (Polynomial.derivative (Q₀ Q))))
    {DX k : ℕ} (hk : 0 < k)
    (hDX : ∀ i, (QP.coeff i).natDegree ≤ DX)
    (hwindow : ∀ t, k ≤ t → t ≤ DX + Q.natDegree * (k - 1) →
      PowerSeries.coeff t (γ Q c) = 0) :
    ∃ g : Polynomial (Polynomial B),
      g.map (algebraMap (Polynomial B) K) = trunc k (γ Q c) ∧
      ((trunc k (γ Q c) : Polynomial K) : PowerSeries K) = γ Q c ∧
      ∀ j, (g.coeff j).natDegree ≤ s := by
  -- the coefficient-support bound for `Q` from the polynomial data
  have hQX : ∀ i, ∀ a, DX < a → PowerSeries.coeff a (Q.coeff i) = 0 := by
    intro i a ha
    rw [hQ, Polynomial.coeff_map, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hDX i) ha)
  -- the tail vanishes: γ is the coercion of its truncation
  have hcoe : ((trunc k (γ Q c) : Polynomial K) : PowerSeries K) = γ Q c :=
    coe_trunc_eq_of_tail (tail_of_range_vanish_of_polyQ Q c hc0 hu hk hQX hwindow)
  -- descend the root identity to `K[X]`
  have hrootser : Polynomial.eval ((trunc k (γ Q c) : Polynomial K) : PowerSeries K)
      (QP.map Polynomial.coeToPowerSeries.ringHom) = 0 := by
    rw [hcoe, ← hQ]
    exact eval_γ_eq_zero Q c hc0 hu
  have hrootp : Polynomial.eval (trunc k (γ Q c)) QP = 0 :=
    polynomial_eval_eq_zero_of_coe_eval hrootser
  rw [hQP] at hrootp
  -- the engine: integrality + the sharp inner-degree bound
  obtain ⟨g, hg_map, hg_deg⟩ :=
    PolyRootGradedBound.exists_graded_preimage_of_eval_monic_eq_zero
      hmonic hd hgrade hrootp
  exact ⟨g, hg_map, hcoe, hg_deg⟩

/-- The fused γ-assembly at the target instantiation `K := RatFunc F` (`B := F` a field):
all instances are Mathlib-native. -/
theorem newton_window_graded_preimage_ratFunc
    {F : Type*} [Field F]
    {P : Polynomial (Polynomial (Polynomial F))} {s : ℕ}
    {QP : Polynomial (Polynomial (RatFunc F))} {Q : Polynomial (PowerSeries (RatFunc F))}
    (hQP : QP = P.map (Polynomial.mapRingHom (algebraMap (Polynomial F) (RatFunc F))))
    (hQ : Q = QP.map Polynomial.coeToPowerSeries.ringHom)
    (hmonic : P.Monic) (hd : P.natDegree ≠ 0)
    (hgrade : ∀ c < P.natDegree, ∀ j, ((P.coeff c).coeff j).natDegree ≤ s * (P.natDegree - c))
    {c : RatFunc F}
    (hc0 : Polynomial.eval c (Q₀ Q) = 0)
    (hu : IsUnit (Polynomial.eval c (Polynomial.derivative (Q₀ Q))))
    {DX k : ℕ} (hk : 0 < k)
    (hDX : ∀ i, (QP.coeff i).natDegree ≤ DX)
    (hwindow : ∀ t, k ≤ t → t ≤ DX + Q.natDegree * (k - 1) →
      PowerSeries.coeff t (γ Q c) = 0) :
    ∃ g : Polynomial (Polynomial F),
      g.map (algebraMap (Polynomial F) (RatFunc F)) = trunc k (γ Q c) ∧
      ((trunc k (γ Q c) : Polynomial (RatFunc F)) : PowerSeries (RatFunc F)) = γ Q c ∧
      ∀ j, (g.coeff j).natDegree ≤ s :=
  newton_window_graded_preimage hQP hQ hmonic hd hgrade hc0 hu hk hDX hwindow

end SectionNewtonGamma

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.SectionNewtonGamma.derivative_Q₀
#print axioms ArkLib.SectionNewtonGamma.eval_C_mem_span_iff
#print axioms ArkLib.SectionNewtonGamma.isUnit_derivative_eval_C_iff
#print axioms ArkLib.SectionNewtonGamma.isRoot_gamma
#print axioms ArkLib.SectionNewtonGamma.gamma_sub_C_mem_span
#print axioms ArkLib.SectionNewtonGamma.exists_gamma_root
#print axioms ArkLib.SectionNewtonGamma.eq_gamma_of_isRoot
#print axioms ArkLib.SectionNewtonGamma.exists_newton_root_eval
#print axioms ArkLib.SectionNewtonGamma.newton_root_choose_eq_gamma
#print axioms ArkLib.SectionNewtonGamma.coe_trunc_eq_of_tail
#print axioms ArkLib.SectionNewtonGamma.natDegree_trunc_lt'
#print axioms ArkLib.SectionNewtonGamma.gamma_eq_coe_trunc_of_window
#print axioms ArkLib.SectionNewtonGamma.exists_polynomial_gamma_of_window
#print axioms ArkLib.SectionNewtonGamma.polynomial_eval_eq_zero_of_coe_eval
#print axioms ArkLib.SectionNewtonGamma.newton_window_graded_preimage
#print axioms ArkLib.SectionNewtonGamma.newton_window_graded_preimage_ratFunc

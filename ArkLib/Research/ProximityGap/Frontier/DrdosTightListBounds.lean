/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FineGridFirstOrderSecurity

/-!
# Tight `M = 2` beyond-Johnson linear interleaved list bounds

By `DrdosCapOneBarrier.two_le_cap_of_beyond_johnson`, every strictly beyond-Johnson first-order
hidden-derivative certificate requires derivative cap `M ≥ 2`. Evaluating canonical
`finite_firstOrder_list_bound_of_shiftedHeightSlotCount_tight` (`τ = 2 K - 3`) at the minimal
beyond-Johnson cap `M = 2` yields unconditional linear-in-`n` list bounds strictly past finite
Johnson across all four prize rates (`1/2, 1/4, 1/8, 1/16`), for every prime field admitting the
evaluation domain and every finite interleaving width:

* **Scalable reference length `4096 b` (fixed positive fraction past Johnson, all `b ≥ 1`)**:
  `163 n` (`1201/4096`), `86 n` (`2050/4096`), `65 n` (`2650/4096`), `52 n` (`3075/4096`) —
  slashing `RateIntervalJohnsonGain` (`174,000 n`) by `1,067×–3,346×` and
  `FineGridFirstOrderSecurity` (`3.72M–5.86M n`) by `22,836×–112,779×`.
* **Exact production `n = 2³⁰`, `J + 1` (`e = 314,491,700; 536,870,914; 694,116,763; 805,306,371`)**:
  `162 n`, `86 n`, `65 n`, `49 n` unconditionally at every interleaving width.
-/

set_option autoImplicit false

namespace ProximityGap.DrdosTightListBounds

open ReedSolomon ReedSolomon.HiddenDerivative CoreDefinitions Finset
open FineGridFirstOrderSecurity

/-! ### Closed-form `M = 2` tight list weight -/

private theorem tightListWeight_zero_cap (n A k K τ μ : ℕ) :
    firstOrderTightListWeight n A k K τ μ 0 = ((μ * (μ + 1) / 2 : ℕ) : ℚ) := by
  induction μ with
  | zero => simp [firstOrderTightListWeight]
  | succ μ ih =>
      rw [firstOrderTightListWeight, ih]
      have heven : 2 ∣ μ * (μ + 1) := Nat.even_mul_succ_self μ |>.two_dvd
      have hnat : μ + 1 + μ * (μ + 1) / 2 = (μ + 1) * (μ + 1 + 1) / 2 := by
        obtain ⟨q, hq⟩ := heven
        have hq' : (μ + 1) * (μ + 1 + 1) = 2 * (μ + 1 + q) := by nlinarith
        rw [hq, hq', Nat.mul_div_cancel_left _ (by decide), Nat.mul_div_cancel_left _ (by decide)]
      rw [← Nat.cast_add_one, ← Nat.cast_add]
      exact_mod_cast hnat

private theorem fiberStageOne_le {K j r : ℕ} (hK : 2 ≤ K) (hr : 1 ≤ r) (hrj : r < j) :
    firstOrderCurveFiberStageOne K j r (2 * K - 3) ≤
      ((j - r) * (2 * r - 1) + 2 * r * (j - 1)) * K := by
  unfold firstOrderCurveFiberStageOne MvPolynomial.cappedDegreeMixedVolume
    firstOrderTaylorDerivativeCap firstOrderTaylorTotalCap
  set b := 1 + (2 * K - 3) * (j - 1)
  set c := min b ((2 * K - 3) * (r - 1) + (K - 1))
  have hcb : c ≤ b := min_le_left _ _
  have hrew : j * c + r * (b - c) = (j - r) * c + r * b := by
    zify [hcb, hrj.le]
    ring
  rw [hrew]
  have hb : b ≤ 2 * K * (j - 1) := by
    dsimp only [b]
    have h1 : 1 ≤ j - 1 := by omega
    zify [show 3 ≤ 2 * K by omega, show 1 ≤ j by omega] at hK h1 ⊢
    nlinarith
  have hc : c ≤ (2 * r - 1) * K := by
    refine (min_le_right _ _).trans ?_
    have hrZ : (1 : ℤ) ≤ r := by exact_mod_cast hr
    zify [show 3 ≤ 2 * K by omega, hr, show 1 ≤ K by omega, show 1 ≤ 2 * r by omega] at hK ⊢
    nlinarith
  have h1 := Nat.mul_le_mul_left (j - r) hc
  have h2 := Nat.mul_le_mul_left r hb
  calc
    (j - r) * c + r * b ≤ (j - r) * ((2 * r - 1) * K) + r * (2 * K * (j - 1)) :=
      Nat.add_le_add h1 h2
    _ = ((j - r) * (2 * r - 1) + 2 * r * (j - 1)) * K := by ring

/-- Exact closed-form upper bound for `firstOrderTightListWeight` at derivative cap `M = 2`
and standard Taylor exponent `τ = 2 K - 3`: the two order-one stages (`r = 2, 1`) combine to at
most `(10 μ - 16) K`, while the remaining `μ - 2` order-zero stages sum to `(μ - 2)(μ - 1)/2`. -/
theorem tightListWeight_cap_two_le {n A k K μ : ℕ} (hK : 2 ≤ K) (hμ : 3 ≤ μ)
    (hkA : k < A) (hAn : A ≤ n) :
    firstOrderTightListWeight n A k K (2 * K - 3) μ 2 ≤
      (((10 * μ - 16) * K * (n - k) : ℕ) : ℚ) / ((A - k : ℕ) : ℚ) +
        (((μ - 2) * (μ - 1) / 2 : ℕ) : ℚ) := by
  obtain ⟨u, rfl⟩ : ∃ u, μ = u + 2 := ⟨μ - 2, by omega⟩
  have hu : 1 ≤ u := by omega
  simp only [firstOrderTightListWeight]
  rw [tightListWeight_zero_cap]
  have hmin2 : min 2 (u + 2) = 2 := by omega
  have hmin1 : min 1 (u + 1) = 1 := by omega
  rw [hmin2, hmin1]
  have hf2 := fiberStageOne_le hK (show 1 ≤ 2 by decide) (show 2 < u + 2 by omega)
  have hf1 := fiberStageOne_le hK le_rfl (show 1 < u + 1 by omega)
  have hsumF : firstOrderCurveFiberStageOne K (u + 2) 2 (2 * K - 3) +
      firstOrderCurveFiberStageOne K (u + 1) 1 (2 * K - 3) ≤
      (10 * (u + 2) - 16) * K := by
    have hcoeff : ((u + 2 - 2) * (2 * 2 - 1) + 2 * 2 * (u + 2 - 1)) +
        ((u + 1 - 1) * (2 * 1 - 1) + 2 * 1 * (u + 1 - 1)) = 10 * (u + 2) - 16 := by omega
    calc
      firstOrderCurveFiberStageOne K (u + 2) 2 (2 * K - 3) +
          firstOrderCurveFiberStageOne K (u + 1) 1 (2 * K - 3)
          ≤ ((u + 2 - 2) * (2 * 2 - 1) + 2 * 2 * (u + 2 - 1)) * K +
            ((u + 1 - 1) * (2 * 1 - 1) + 2 * 1 * (u + 1 - 1)) * K := Nat.add_le_add hf2 hf1
      _ = (((u + 2 - 2) * (2 * 2 - 1) + 2 * 2 * (u + 2 - 1)) +
            ((u + 1 - 1) * (2 * 1 - 1) + 2 * 1 * (u + 1 - 1))) * K := by ring
      _ = (10 * (u + 2) - 16) * K := by rw [hcoeff]
  have hpos1 : (0 : ℚ) < ((A - k + 1 : ℕ) : ℚ) := by positivity
  have hpos0 : (0 : ℚ) < ((A - k : ℕ) : ℚ) := by
    have : 0 < A - k := by omega
    exact_mod_cast this
  have hrat : (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) ≤
      (((n - k : ℕ) : ℚ) / ((A - k : ℕ) : ℚ)) := by
    rw [div_le_div_iff₀ hpos1 hpos0]
    have hle : (n - k + 1) * (A - k) ≤ (n - k) * (A - k + 1) := by
      have : A - k ≤ n - k := Nat.sub_le_sub_right hAn k
      nlinarith
    exact_mod_cast hle
  have hsumQ : ((firstOrderCurveFiberStageOne K (u + 2) 2 (2 * K - 3) : ℚ) +
      (firstOrderCurveFiberStageOne K (u + 1) 1 (2 * K - 3) : ℚ)) ≤
      (((10 * (u + 2) - 16) * K : ℕ) : ℚ) := by
    exact_mod_cast hsumF
  have htail : u * (u + 1) / 2 = (u + 2 - 2) * (u + 2 - 1) / 2 := rfl
  rw [← htail]
  have hmul : ((firstOrderCurveFiberStageOne K (u + 2) 2 (2 * K - 3) : ℚ) +
      (firstOrderCurveFiberStageOne K (u + 1) 1 (2 * K - 3) : ℚ)) *
      (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) ≤
      (((10 * (u + 2) - 16) * K : ℕ) : ℚ) * (((n - k : ℕ) : ℚ) / ((A - k : ℕ) : ℚ)) :=
    mul_le_mul hsumQ hrat (by positivity) (by positivity)
  have hleft : (firstOrderCurveFiberStageOne K (u + 2) 2 (2 * K - 3) : ℚ) *
        ((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) +
      ((firstOrderCurveFiberStageOne K (u + 1) 1 (2 * K - 3) : ℚ) *
        ((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) + ((u * (u + 1) / 2 : ℕ) : ℚ)) =
      ((firstOrderCurveFiberStageOne K (u + 2) 2 (2 * K - 3) : ℚ) +
        (firstOrderCurveFiberStageOne K (u + 1) 1 (2 * K - 3) : ℚ)) *
        (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) + ((u * (u + 1) / 2 : ℕ) : ℚ) := by
    ring
  have hright : (((10 * (u + 2) - 16) * K : ℕ) : ℚ) *
        (((n - k : ℕ) : ℚ) / ((A - k : ℕ) : ℚ)) =
      (((10 * (u + 2) - 16) * K * (n - k) : ℕ) : ℚ) / ((A - k : ℕ) : ℚ) := by
    rw [← mul_div_assoc]
    push_cast
    rfl
  rw [hleft, ← hright]
  linarith

/-! ### Scalable `M = 2` list-bound engine -/

/-- A shifted-slot certificate at cap `M = 2` and reference length `N` bounds the worst-case
scalar list at closed radius `1 - A / N` by `C * (b * N)` for every positive scale `b` and
every field of characteristic zero or at least `b * N`. -/
theorem tight_list_of_slots_cap_two {F : Type*} [Field F] {N b k A m μ h C : ℕ}
    (hb : 0 < b) (hk : 2 ≤ k) (hkA : k < A) (hAN : A ≤ N)
    (hμ3 : 3 ≤ μ) (hμN : μ < N)
    (hfield : ringChar F = 0 ∨ b * N ≤ ringChar F)
    (hcost : (10 * μ - 16) * k * (N - k) + ((μ - 2) * (μ - 1) / 2) * (A - k) ≤
      C * N * (A - k))
    (hslots : rowSlots N m 2 μ h < columnSlots k A m 2 μ h)
    (dom : Fin (b * N) ↪ F) :
    Code.Lambda (code dom (b * k) : Set (Fin (b * N) → F)) (1 - (A : ℝ) / N) ≤
      ((C * (b * N) : ℕ) : ℕ∞) := by
  classical
  have hNpos : 0 < N := by omega
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hNb : N ≤ b * N := Nat.le_mul_of_pos_left N hb
  let g := ((A - k : ℕ) : ℝ) / N
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hbR : (b : ℝ) ≠ 0 := by positivity
  have h₁ : capacityAgreementThreshold g (b * N) (b * k) = b * A := by
    have he : g * ((b * N : ℕ) : ℝ) = ((b * (A - k) : ℕ) : ℝ) := by
      dsimp [g]
      push_cast
      field_simp
    rw [capacityAgreementThreshold, he, Nat.ceil_natCast, Nat.mul_sub, Nat.add_sub_of_le]
    exact Nat.mul_le_mul_left b hkA.le
  have h₂ : capacityRadius g (b * N) (b * k) = 1 - (A : ℝ) / N := by
    unfold capacityRadius g
    rw [Nat.cast_sub hkA.le]
    push_cast
    field_simp
    ring
  rw [← h₂, ← Nat.ceil_natCast (R := ℝ) (C * (b * N))]
  apply lambda_le_ceil_of_closePolynomialSet_bound hg (by omega)
  intro f
  rw [h₁]
  let T := @closePolynomialSet F _ (Classical.decEq _) _ dom f (b * k) (b * A)
  have hbk : 2 ≤ b * k := by nlinarith
  have hlt : b * k < b * A := Nat.mul_lt_mul_of_pos_left hkA hb
  have hAn' : b * A ≤ b * N := Nat.mul_le_mul_left b hAN
  have hchar : ringChar F = 0 ∨ max (b * k - 1) μ < ringChar F := by
    rcases hfield with hc | hc
    · exact Or.inl hc
    · exact Or.inr (by omega)
  have bound (S : Finset (Polynomial F)) (hST : (↑S : Set _) ⊆ T) : S.card ≤ C * (b * N) := by
    have hpoint (P : Polynomial F) (hP : P ∈ S) :
        P.degree < b * k ∧ b * A ≤ ({i : Fin (b * N) | P.eval (dom i) = f i} : Set _).ncard := by
      have h := hST hP
      refine ⟨h.1, h.2.trans_eq ?_⟩
      rw [Set.ncard_eq_toFinset_card']
      congr 1
      ext i
      simp [polynomialAgreementSet]
    have htight := finite_firstOrder_list_bound_of_shiftedHeightSlotCount_tight
      (D := b * k - 1) (K := b * k) (by omega) (by omega) dom f
      (scaled_slots hb hslots) (by omega) le_rfl (by omega) hlt.le hchar S hpoint
    have hcap := tightListWeight_cap_two_le (n := b * N) (A := b * A) (k := b * k)
      (K := b * k) (μ := μ) hbk hμ3 hlt hAn'
    have hQ : (S.card : ℚ) ≤ ((C * (b * N) : ℕ) : ℚ) := by
      refine (htight.trans hcap).trans ?_
      have hden : (0 : ℚ) < ((b * A - b * k : ℕ) : ℚ) := by
        have : 0 < b * A - b * k := by omega
        exact_mod_cast this
      rw [div_add' _ _ _ hden.ne', div_le_iff₀ hden]
      have hnat : (10 * μ - 16) * (b * k) * (b * N - b * k) +
          ((μ - 2) * (μ - 1) / 2) * (b * A - b * k) ≤
          (C * (b * N)) * (b * A - b * k) := by
        rw [← Nat.mul_sub, ← Nat.mul_sub]
        have hstep1 : (10 * μ - 16) * (b * k) * (b * (N - k)) =
            b * b * ((10 * μ - 16) * k * (N - k)) := by ring
        have hstep2 : ((μ - 2) * (μ - 1) / 2) * (b * (A - k)) ≤
            b * b * (((μ - 2) * (μ - 1) / 2) * (A - k)) := by
          have hbb : b ≤ b * b := Nat.le_mul_of_pos_left b hb
          rw [show ((μ - 2) * (μ - 1) / 2) * (b * (A - k)) =
            b * (((μ - 2) * (μ - 1) / 2) * (A - k)) by ring]
          exact Nat.mul_le_mul_right _ hbb
        have hstep3 : (C * (b * N)) * (b * (A - k)) = b * b * (C * N * (A - k)) := by ring
        rw [hstep1, hstep3]
        have hmul := Nat.mul_le_mul_left (b * b) hcost
        nlinarith
      exact_mod_cast hnat
    exact_mod_cast hQ
  have hfin : T.Finite := Set.finite_of_forall_finset_card_le (R := ℕ) (ℓ := C * (b * N)) bound
  refine ⟨hfin, ?_⟩
  have h := bound hfin.toFinset (by simp)
  rw [← Set.ncard_eq_toFinset_card _ hfin] at h
  exact_mod_cast h

/-! ### Scalable four-rate `N = 4096` certificates (`163 n, 86 n, 65 n, 52 n`) -/

/-- The four minimal-cap (`M = 2`) shifted-slot certificates at reference length `4096`, each
strictly beyond the finite-length Johnson bound. -/
theorem cap_two_slot_certificates :
    rowSlots 4096 11 2 15 660 < columnSlots 2048 2895 11 2 15 660 ∧
    rowSlots 4096 7 2 13 401 < columnSlots 1024 2046 7 2 13 401 ∧
    rowSlots 4096 6 2 15 387 < columnSlots 512 1446 6 2 15 387 ∧
    rowSlots 4096 5 2 18 551 < columnSlots 256 1021 5 2 18 551 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- All four scaled radii (`1201/4096`, `2050/4096`, `2650/4096`, `3075/4096`) lie strictly beyond
the finite-length Johnson bound `√(n (k - 1))` for every multiple `n = 4096 b` (`b ≥ 1`). -/
theorem below_finite_johnson {b : ℕ} (hb : 0 < b) :
    (b * 2895) ^ 2 < (b * 4096) * (b * 2048 - 1) ∧
    (b * 2046) ^ 2 < (b * 4096) * (b * 1024 - 1) ∧
    (b * 1446) ^ 2 < (b * 4096) * (b * 512 - 1) ∧
    (b * 1021) ^ 2 < (b * 4096) * (b * 256 - 1) := by
  have hpos : (0 : ℤ) ≤ b - 1 := by omega
  have hb2 : (b : ℤ) ≤ (b : ℤ) ^ 2 := by nlinarith [mul_nonneg hpos (Int.natCast_nonneg b)]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals zify [show 1 ≤ b * 2048 by omega, show 1 ≤ b * 1024 by omega,
    show 1 ≤ b * 512 by omega, show 1 ≤ b * 256 by omega]; nlinarith

/-- Unconditional tight linear list bounds (`163 n`, `86 n`, `65 n`, `52 n`) strictly past finite
Johnson across all four prize rates at every block length `4096 b`, over any field of
characteristic zero or at least `4096 b`. -/
theorem four_tight_field_list_bounds {F : Type*} [Field F] {b : ℕ} (hb : 0 < b)
    (hfield : ringChar F = 0 ∨ b * 4096 ≤ ringChar F)
    (dom : Fin (b * 4096) ↪ F) :
    let bounded := fun (k : ℕ) (r : ℝ) (C : ℕ) =>
      Code.Lambda (code dom (b * k) : Set (Fin (b * 4096) → F)) r ≤ ((C * (b * 4096) : ℕ) : ℕ∞)
    bounded 2048 (1201 / 4096) 163 ∧ bounded 1024 (2050 / 4096) 86 ∧
      bounded 512 (2650 / 4096) 65 ∧ bounded 256 (3075 / 4096) 52 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := cap_two_slot_certificates
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_ofNat, show (1 - (2895 : ℝ) / 4096) = 1201 / 4096 by norm_num] using
      tight_list_of_slots_cap_two (C := 163) hb (by decide) (by decide) (by decide) (by decide)
        (by decide) hfield (by decide) h₁ dom
  · simpa only [Nat.cast_ofNat, show (1 - (2046 : ℝ) / 4096) = 2050 / 4096 by norm_num] using
      tight_list_of_slots_cap_two (C := 86) hb (by decide) (by decide) (by decide) (by decide)
        (by decide) hfield (by decide) h₂ dom
  · simpa only [Nat.cast_ofNat, show (1 - (1446 : ℝ) / 4096) = 2650 / 4096 by norm_num] using
      tight_list_of_slots_cap_two (C := 65) hb (by decide) (by decide) (by decide) (by decide)
        (by decide) hfield (by decide) h₃ dom
  · simpa only [Nat.cast_ofNat, show (1 - (1021 : ℝ) / 4096) = 3075 / 4096 by norm_num] using
      tight_list_of_slots_cap_two (C := 52) hb (by decide) (by decide) (by decide) (by decide)
        (by decide) hfield (by decide) h₄ dom

/-- Prime-field scalar specialization of `four_tight_field_list_bounds`. -/
theorem four_tight_list_bounds {p b : ℕ} [Fact p.Prime] (hb : 0 < b)
    (dom : Fin (b * 4096) ↪ ZMod p) :
    let bounded := fun (k : ℕ) (r : ℝ) (C : ℕ) =>
      Code.Lambda (code dom (b * k) : Set (Fin (b * 4096) → ZMod p)) r ≤
        ((C * (b * 4096) : ℕ) : ℕ∞)
    bounded 2048 (1201 / 4096) 163 ∧ bounded 1024 (2050 / 4096) 86 ∧
      bounded 512 (2650 / 4096) 65 ∧ bounded 256 (3075 / 4096) 52 := by
  apply four_tight_field_list_bounds hb _ dom
  right
  simpa [ZMod.ringChar_zmod_n] using Fintype.card_le_of_injective dom dom.injective

/-- Interleaved prime-field specialization (`163 n`, `86 n`, `65 n`, `52 n`) at every finite
interleaving width and every block length `4096 b`, via `RatFunc` transfer. -/
theorem four_tight_interleaved_list_bounds {p b : ℕ} [Fact p.Prime] (hb : 0 < b)
    (dom : Fin (b * 4096) ↪ ZMod p) (width : ℕ) :
    let bounded := fun (k : ℕ) (r : ℝ) (C : ℕ) =>
      Code.Lambda (Code.interleavedCodeSet (κ := Fin width)
        (code dom (b * k) : Set (Fin (b * 4096) → ZMod p))) r ≤
        ((C * (b * 4096) : ℕ) : ℕ∞)
    bounded 2048 (1201 / 4096) 163 ∧ bounded 1024 (2050 / 4096) 86 ∧
      bounded 512 (2650 / 4096) 65 ∧ bounded 256 (3075 / 4096) 52 := by
  let φ := algebraMap (ZMod p) (RatFunc (ZMod p))
  have hsize : b * 4096 ≤ p := by simpa using Fintype.card_le_of_injective dom dom.injective
  have hchar : ringChar (RatFunc (ZMod p)) = p := ringChar.eq _ p
  have hlarge : b * 4096 ≤ ringChar (RatFunc (ZMod p)) := hsize.trans_eq hchar.symm
  obtain ⟨h₁, h₂, h₃, h₄⟩ := four_tight_field_list_bounds hb (Or.inr hlarge) (dom.trans ⟨φ, φ.injective⟩)
  exact ⟨(Lambda_interleaved_le_ratFunc dom _ width _).trans h₁,
    (Lambda_interleaved_le_ratFunc dom _ width _).trans h₂,
    (Lambda_interleaved_le_ratFunc dom _ width _).trans h₃,
    (Lambda_interleaved_le_ratFunc dom _ width _).trans h₄⟩

/-! ### Exact production `n = 2³⁰`, `J + 1` certificates (`162 n, 86 n, 65 n, 49 n`) -/

/-- Exact `M = 2` shifted-slot certificates at production block length `n = 2³⁰` and exact
`Johnson + 1` error radii (`314,491,700`, `536,870,914`, `694,116,763`, `805,306,371`). -/
theorem production_j_plus_one_slot_certificates :
    rowSlots 1073741824 11 2 15 461 < columnSlots 536870912 759250124 11 2 15 461 ∧
    rowSlots 1073741824 7 2 13 296 < columnSlots 268435456 536870910 7 2 13 296 ∧
    rowSlots 1073741824 6 2 15 295 < columnSlots 134217728 379625061 6 2 15 295 ∧
    rowSlots 1073741824 5 2 17 1295 < columnSlots 67108864 268435453 5 2 17 1295 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Unconditional tight linear interleaved list bounds (`162 n`, `86 n`, `65 n`, `49 n`) at exact
production block length `n = 2³⁰` and exact `Johnson + 1` across all four prize rates, for every
prime field admitting the evaluation domain and every finite interleaving width. -/
theorem production_j_plus_one_tight_interleaved_list_bounds {p : ℕ} [Fact p.Prime]
    (dom : Fin 1073741824 ↪ ZMod p) (width : ℕ) :
    let bounded := fun (k : ℕ) (r : ℝ) (C : ℕ) =>
      Code.Lambda (Code.interleavedCodeSet (κ := Fin width)
        (code dom k : Set (Fin 1073741824 → ZMod p))) r ≤
        ((C * 1073741824 : ℕ) : ℕ∞)
    bounded 536870912 (314491700 / 1073741824) 162 ∧
    bounded 268435456 (536870914 / 1073741824) 86 ∧
    bounded 134217728 (694116763 / 1073741824) 65 ∧
    bounded 67108864 (805306371 / 1073741824) 49 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := production_j_plus_one_slot_certificates
  let φ := algebraMap (ZMod p) (RatFunc (ZMod p))
  have hsize : 1073741824 ≤ p := by simpa using Fintype.card_le_of_injective dom dom.injective
  have hchar : ringChar (RatFunc (ZMod p)) = p := ringChar.eq _ p
  have hlarge : 1 * 1073741824 ≤ ringChar (RatFunc (ZMod p)) := by
    simpa [hchar] using hsize
  let dom' : Fin (1 * 1073741824) ↪ RatFunc (ZMod p) :=
    (Equiv.cast (congrArg Fin (one_mul 1073741824))).toEmbedding.trans (dom.trans ⟨φ, φ.injective⟩)
  -- Transport `Code.Lambda` along `1 * N = N` cleanly via `b = 1`
  have lift (k A m μ h C : ℕ) (hk : 2 ≤ k) (hkA : k < A) (hAN : A ≤ 1073741824)
      (hμ3 : 3 ≤ μ) (hμN : μ < 1073741824)
      (hcost : (10 * μ - 16) * k * (1073741824 - k) +
        ((μ - 2) * (μ - 1) / 2) * (A - k) ≤ C * 1073741824 * (A - k))
      (hslots : rowSlots 1073741824 m 2 μ h < columnSlots k A m 2 μ h) :
      Code.Lambda (Code.interleavedCodeSet (κ := Fin width)
        (code dom k : Set (Fin 1073741824 → ZMod p))) (1 - (A : ℝ) / 1073741824) ≤
        ((C * 1073741824 : ℕ) : ℕ∞) := by
    have hbase := tight_list_of_slots_cap_two (F := RatFunc (ZMod p)) (N := 1073741824) (b := 1)
      (k := k) (A := A) (m := m) (μ := μ) (h := h) (C := C)
      (by decide) hk hkA hAN hμ3 hμN (Or.inr hlarge) hcost hslots dom'
    have htr : Code.Lambda (code (dom.trans ⟨φ, φ.injective⟩) k :
        Set (Fin 1073741824 → RatFunc (ZMod p))) (1 - (A : ℝ) / 1073741824) ≤
        ((C * 1073741824 : ℕ) : ℕ∞) := by
      have hcast : ∀ (N : ℕ) (e : 1 * 1073741824 = N) (d : Fin N ↪ RatFunc (ZMod p)),
          (Code.Lambda (code ((Equiv.cast (congrArg Fin e)).toEmbedding.trans d) (1 * k) :
            Set (Fin (1 * 1073741824) → RatFunc (ZMod p))) (1 - (A : ℝ) / 1073741824) ≤
              ((C * (1 * 1073741824) : ℕ) : ℕ∞)) →
          Code.Lambda (code d k : Set (Fin N → RatFunc (ZMod p))) (1 - (A : ℝ) / 1073741824) ≤
              ((C * N : ℕ) : ℕ∞) := by
        rintro N rfl d h0
        have heq : ((Equiv.cast (congrArg Fin (rfl : 1 * 1073741824 = 1 * 1073741824))).toEmbedding.trans d) = d := by
          ext i; rfl
        rw [heq, one_mul k] at h0
        exact h0
      exact hcast 1073741824 (one_mul _) (dom.trans ⟨φ, φ.injective⟩) (by simpa only [Nat.cast_ofNat] using hbase)
    exact (Lambda_interleaved_le_ratFunc dom k width _).trans htr
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_ofNat,
        show (1 - (759250124 : ℝ) / 1073741824) = 314491700 / 1073741824 by norm_num] using
      lift 536870912 759250124 11 15 461 162 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) h₁
  · simpa only [Nat.cast_ofNat,
        show (1 - (536870910 : ℝ) / 1073741824) = 536870914 / 1073741824 by norm_num] using
      lift 268435456 536870910 7 13 296 86 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) h₂
  · simpa only [Nat.cast_ofNat,
        show (1 - (379625061 : ℝ) / 1073741824) = 694116763 / 1073741824 by norm_num] using
      lift 134217728 379625061 6 15 295 65 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) h₃
  · simpa only [Nat.cast_ofNat,
        show (1 - (268435453 : ℝ) / 1073741824) = 805306371 / 1073741824 by norm_num] using
      lift 67108864 268435453 5 17 1295 49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) h₄

#print axioms tightListWeight_cap_two_le
#print axioms tight_list_of_slots_cap_two
#print axioms cap_two_slot_certificates
#print axioms below_finite_johnson
#print axioms four_tight_field_list_bounds
#print axioms four_tight_list_bounds
#print axioms four_tight_interleaved_list_bounds
#print axioms production_j_plus_one_slot_certificates
#print axioms production_j_plus_one_tight_interleaved_list_bounds

end ProximityGap.DrdosTightListBounds

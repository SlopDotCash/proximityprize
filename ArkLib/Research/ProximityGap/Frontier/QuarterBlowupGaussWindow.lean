/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorJetInterpolation
import ArkLib.Research.ProximityGap.Frontier.DoubleInterpolationCommonFactor

/-! # Blown-up Gauss-graph excess intersection and quarter-rate safety through 534,295,000 errors

This module proves the algebraic core of the nef-safe blown-up Gauss-graph height bound,
constructs the two mixed Hasse interpolation surfaces at `e = 534,295,000` quarter-rate errors
on any injective domain of length `2^30`, and certifies the dual-constraint `(α, β)` Veronese
and transverse allocation below the second designated prime's 128-bit budget `2^31`.

The surface intersection argument on `Bl_{∪ C_x} Bl_Σ P(O ⊕ O ⊕ O(d))` and projective
plane-curve duality are written in `docs/research/proximity-gap/quarter-blowup-gauss-window.md`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.QuarterBlowupGaussWindow

open Finset Polynomial HalfSuccessorJetInterpolation SecondPrimeQuarticInterpolation

abbrev n : ℕ := 1073741824
abbrev d : ℕ := 268435455
abbrev e : ℕ := 534295000
abbrev t : ℕ := n - e
abbrev miss : ℕ := 8192
abbrev core : ℕ := t - miss
abbrev bound : ℕ := 2146832205

/-! ## Algebraic core of the nef-safe blown-up Gauss-graph bound -/

/-- If a primary interpolant of order `r` on `T` (`|T| = t₀`) and strict weight `< r * t₀`
factors as `F^k * G` with `k * W + Wg < r * t₀` and `G` nonzero on a section agreeing on `T`,
then the site vanishing orders `i` of `F` on `T` satisfy `W + 1 ≤ ∑ x ∈ T, i x`. -/
theorem factor_order_sum_ge {α : Type*} (T : Finset α) (i j : α → ℕ)
    {k W Wg r t₀ : ℕ} (hT : T.card = t₀)
    (hwt : k * W + Wg < r * t₀)
    (hord : ∀ x ∈ T, r ≤ k * i x + j x)
    (hgj : ∑ x ∈ T, j x ≤ Wg) :
    W + 1 ≤ ∑ x ∈ T, i x := by
  have hsum : r * t₀ ≤ k * (∑ x ∈ T, i x) + ∑ x ∈ T, j x := by
    calc r * t₀ = ∑ _x ∈ T, r := by rw [Finset.sum_const, hT, smul_eq_mul, mul_comm]
      _ ≤ ∑ x ∈ T, (k * i x + j x) := Finset.sum_le_sum hord
      _ = k * (∑ x ∈ T, i x) + ∑ x ∈ T, j x := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hlt : k * W < k * ∑ x ∈ T, i x := by omega
  exact Nat.lt_of_mul_lt_mul_left hlt

/-- Integer pole-degree budget per unit of actual companion degree after subtracting the
nef-safe blown-up excess intersection along a `t₀`-site agreement set. -/
def blowupH (b W t₀ d₀ : ℕ) : ℕ :=
  (6 * b + 2) * W - 3 * b ^ 2 * d₀ - 3 * (W - t₀) ^ 2 / t₀ - 2 * (W - t₀)

/-- `blowupH b W t₀ d₀` is monotone nondecreasing in `W` throughout `[b * d₀, b * t₀ - 1]`. -/
theorem blowupH_mono {b W wMax t₀ d₀ : ℕ} (ht : 0 < t₀) (hbd : b * d₀ ≤ W)
    (hhi : W ≤ min wMax (b * t₀ - 1)) :
    blowupH b W t₀ d₀ ≤ blowupH b (min wMax (b * t₀ - 1)) t₀ d₀ := by
  have step : ∀ w, b * d₀ ≤ w → w + 1 ≤ b * t₀ - 1 →
      blowupH b w t₀ d₀ ≤ blowupH b (w + 1) t₀ d₀ := by
    intro w hwd hw1
    unfold blowupH
    have h1 : 3 * b ^ 2 * d₀ ≤ 3 * b * w := by nlinarith
    by_cases hwt : w < t₀
    · have hs0 : w - t₀ = 0 := by omega
      have hs1 : w + 1 - t₀ = 0 := by omega
      rw [hs0, hs1]
      simp only [Nat.zero_pow (by decide : 0 < 2), mul_zero, Nat.zero_div, Nat.sub_zero]
      exact Nat.sub_le_sub_right (Nat.mul_le_mul_left _ (Nat.le_succ w)) _
    · push Not at hwt
      have hs1 : w + 1 - t₀ = (w - t₀) + 1 := by omega
      have hdiff : 3 * ((w - t₀) + 1) ^ 2 ≤ 3 * (w - t₀) ^ 2 + (6 * b - 1) * t₀ := by
        have hbt : 1 ≤ b := by
          rcases Nat.eq_zero_or_pos b with rfl | hbpos
          · omega
          · exact hbpos
        have hle : w - t₀ + 1 ≤ b * t₀ - t₀ := by omega
        have h6 : 6 * (w - t₀) + 3 ≤ (6 * b - 1) * t₀ := by
          have hmul : 6 * (w - t₀ + 1) ≤ 6 * (b * t₀ - t₀) := Nat.mul_le_mul_left 6 hle
          have : (6 * b - 1) * t₀ = 6 * (b * t₀) - t₀ := by
            rw [Nat.sub_mul, one_mul, Nat.mul_assoc]
          omega
        nlinarith
      have hdiv_step : 3 * ((w - t₀) + 1) ^ 2 / t₀ ≤ 3 * (w - t₀) ^ 2 / t₀ + 6 * b := by
        have hA : 3 * (w - t₀) ^ 2 < (3 * (w - t₀) ^ 2 / t₀ + 1) * t₀ := by
          have := Nat.div_add_mod (3 * (w - t₀) ^ 2) t₀
          have := Nat.mod_lt (3 * (w - t₀) ^ 2) ht
          nlinarith
        have hB : 3 * ((w - t₀) + 1) ^ 2 < (3 * (w - t₀) ^ 2 / t₀ + 6 * b + 1) * t₀ := by
          have : (6 * b - 1) * t₀ ≤ 6 * b * t₀ := Nat.mul_le_mul_right t₀ (Nat.sub_le _ _)
          nlinarith
        exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul ht).mpr hB)
      have hsub_w : 3 * b ^ 2 * d₀ + 3 * (w - t₀) ^ 2 / t₀ + 2 * (w - t₀) ≤ (6 * b + 2) * w := by
        have h2 : 3 * (w - t₀) ^ 2 / t₀ ≤ 3 * b * w := by
          have : 3 * (w - t₀) ^ 2 ≤ 3 * b * w * t₀ := by
            have : w - t₀ ≤ w := Nat.sub_le w t₀
            have : w ≤ b * t₀ := by omega
            nlinarith
          exact Nat.div_le_of_le_mul (by linarith)
        have hlin : (6 * b + 2) * w = 3 * b * w + 3 * b * w + 2 * w := by ring
        omega
      have hmul_step : (6 * b + 2) * (w + 1) = (6 * b + 2) * w + 6 * b + 2 := by ring
      rw [hs1]
      omega
  have go : ∀ m, W ≤ m → m ≤ b * t₀ - 1 → blowupH b W t₀ d₀ ≤ blowupH b m t₀ d₀ := by
    intro m hWm
    refine Nat.le_induction (fun _ => le_rfl) (fun k hk ih hk1 => ?_) m hWm
    exact (ih (by omega)).trans (step k (hbd.trans hk) hk1)
  exact go (min wMax (b * t₀ - 1)) hhi (Nat.min_le_right _ _)

/-! ## Mixed Hasse interpolants at 534,295,000 quarter-rate errors -/

/-- Exact scalar-coefficient constraint count at a site of order `r`. -/
def rowCount (s r : ℕ) : ℕ := ∑ j ∈ range r, (r - j) * (s + 1 - j)

theorem card_rows (s r : ℕ) : Fintype.card (JetRows s r) = rowCount s r := by
  simp only [JetRows, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, rowCount]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => (r - j) * (s + 1 - j)) r

/-- Exact monomial count below the strict weighted-degree cap `W`. -/
def columnCount (s b D W : ℕ) : ℕ := ∑ j ∈ range (b + 1), (s + 1 - j) * (W - j * D)

theorem card_columns (s b D W : ℕ) : Fintype.card (Monomials s b D W) = columnCount s b D W := by
  simp only [Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, columnCount]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => (s + 1 - j) * (W - j * D)) (b + 1)

/-- Exact mixed-Hasse rank surpluses for the primary `(53, 106, 71987)` and
companion `(103, 206, 7378)` surfaces at `e = 534,295,000`. -/
theorem ranks :
    columnCount 71987 106 d (53 * t) = n * rowCount 71987 53 + 374155779 ∧
    columnCount 7378 206 d (103 * t) = n * rowCount 7378 103 + 24285466484 := by
  decide +kernel

/-- The support and specialization guarantees for a nonzero received-row interpolant. -/
def SectionSurface {I F : Type} [Field F] (dom : I ↪ F) (u v : I → F)
    (s b D W : ℕ) (T : ℕ) : Prop :=
  ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
    (∀ j h x, ((Q.coeff j).coeff h).coeff x ≠ 0 → j ≤ b ∧ h + j ≤ s ∧ x + j * D < W) ∧
    (∀ x, Q.eval₂ (mapRingHom (evalRingHom (dom x)))
      (Polynomial.C (u x) + X * Polynomial.C (v x)) = 0) ∧
    ∀ g : F, ∀ q : F[X], q.natDegree ≤ D → ∀ S : Finset I, T ≤ S.card →
      (∀ x ∈ S, q.eval (dom x) = u x + g * v x) → Q.eval₂ (evalRingHom (Polynomial.C g)) q = 0

private theorem received_line_of_jet {F : Type} [Field F] {s b D W : ℕ}
    (a : Monomials s b D W → F) (x u v : F)
    (h : ∑ m, Polynomial.C (a m) * jetTerm m 0 0 x u v = 0) :
    (surface a).eval₂ (mapRingHom (evalRingHom x)) (Polynomial.C u + X * Polynomial.C v) = 0 := by
  rw [surface_received_line]
  convert h using 1
  unfold receivedLine
  apply sum_congr rfl
  intro m _
  simp only [jetTerm, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  rfl

set_option maxRecDepth 8192 in
/-- Both production surfaces exist on every length-`2^30` injective domain over any field
and vanish on every witnessing section with at least `t = 539,446,824` agreements. -/
theorem surfaces {I F : Type} [Fintype I] [Field F] (dom : I ↪ F) (u v : I → F)
    (hn : Fintype.card I = n) (companion : Bool) :
    let r := if companion then 103 else 53
    let b := if companion then 206 else 106
    let s := if companion then 7378 else 71987
    SectionSurface dom u v s b d (r * t) t := by
  cases companion
  · obtain ⟨a, ha, jets, hf⟩ := exists_surface dom u v (by decide : 0 < 53) (by decide : 0 < t)
      (by decide : 53 ≤ 71987 + 1) (by
        rw [hn, card_rows, card_columns]
        exact ranks.1 ▸ Nat.lt_add_of_pos_right (by decide))
    exact ⟨surface a, surface_ne_zero ha, fun _ _ _ h => surface_support a h,
      fun x => received_line_of_jet a _ _ _ (jets x 0 0 (by decide)),
      fun g q hq S hS hag => by rw [surface_eval]; exact hf g q hq S hS hag⟩
  · obtain ⟨a, ha, jets, hf⟩ := exists_surface dom u v (by decide : 0 < 103) (by decide : 0 < t)
      (by decide : 103 ≤ 7378 + 1) (by
        rw [hn, card_rows, card_columns]
        exact ranks.2 ▸ Nat.lt_add_of_pos_right (by decide))
    exact ⟨surface a, surface_ne_zero ha, fun _ _ _ h => surface_support a h,
      fun x => received_line_of_jet a _ _ _ (jets x 0 0 (by decide)),
      fun g q hq S hS hag => by rw [surface_eval]; exact hf g q hq S hS hag⟩

/-! ## Dual-constraint `(α, β)` Veronese and transverse allocation -/

private def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

private def unionAt (j a : ℕ) : ℕ :=
  ceilDiv (2 * a * j * core - j * (j - 1) * d) (a * (a + 1))

private def discreteUnion (j : ℕ) : ℕ :=
  let a₁ := j / 2
  let a₂ := (j + 1) / 2
  let u₁ := if 1 ≤ a₁ ∧ a₁ < j then unionAt j a₁ else 0
  let u₂ := if 1 ≤ a₂ ∧ a₂ < j then unionAt j a₂ else 0
  max u₁ u₂

/-- Upper bound on the scalar population assigned to `j` rich polynomial affine heads. -/
def headMass (j : ℕ) : ℕ :=
  if j < 3 then j * (e + 1) else
    let cover := max (discreteUnion j) (ceilDiv (j * core ^ 2) (core + (j - 1) * d))
    min (j * (e + 1)) (j * n - (j - 1) * cover)

/-- Blown-up height bound maximized over `W ∈ [b * d, min (53 * t - 1 - j * d) (b * t - 1)]`. -/
def maxBlowupH (j b : ℕ) : ℕ :=
  blowupH b (min (53 * t - 1 - j * d) (b * t - 1)) t d

/-- Base price per unit of actual companion degree (triangle determinant, plus transverse
tangent bound when `j ≥ 4`), valid for every actual plane degree `m ≥ b`. -/
def basePrice (j b : ℕ) : ℕ :=
  let H := maxBlowupH j b
  let R := (2 * b - 1) * n
  let p := min j 2
  let tri := 2 * b + ceilDiv ((3 - p) * (R + H)) (3 * t - (n + 2 * d + p * miss))
  let trv := if 4 ≤ j then 2 * b + ceilDiv (H + R) (t + discreteUnion j - (n + d)) else tri
  4 * b - 2 + min tri trv

/-- Veronese price per unit of actual companion degree using `p = min j 3` fixed rich heads
(independent in degree `s ≥ 4`), valid whenever `m > s * (s - 1)`. -/
def veronesePrice (j b s a h C_a E_s : ℕ) : ℕ :=
  let H := maxBlowupH j b
  let R := (2 * b - 1) * n
  let p := min j 3
  let gap := a * h * t - (C_a * n + E_s * d + a * p * miss)
  4 * b - 2 + 2 * s * b + ceilDiv ((h - p) * (a * R + s * H)) gap

/-- Cumulative Veronese unit prices for `j ≤ 3` at cutoffs `12, 56, 240, 552`. -/
def price4 (j b : ℕ) : ℕ := min (basePrice j b) (veronesePrice j b 4 3 15 10 40)
def price8 (j b : ℕ) : ℕ := min (price4 j b) (veronesePrice j b 8 6 45 56 240)
def price16 (j b : ℕ) : ℕ := min (price8 j b) (veronesePrice j b 16 11 153 286 1632)
def price24 (j b : ℕ) : ℕ := min (price16 j b) (veronesePrice j b 24 17 325 969 5200)

/-- The five non-nonlinear label classes: rich heads, scalar-only primary factors,
single noncommon resultant, small polynomial heads, and nonaffine common linear factors. -/
def otherLabels (j : ℕ) : ℕ :=
  headMass j + 71987 + (71987 * 206 + 106 * 7378) + (106 - j) * 71987 + (7378 - j) * 17

/-- Linear-duality slope per unit of actual companion degree `m`. -/
def alpha (j : ℕ) : ℕ :=
  if j = 0 then 76050
  else if j = 1 then 74511
  else if j = 2 then 72990
  else if j = 3 then 71489
  else (bound - otherLabels j) / (7378 - j)

/-- Linear-duality surcharge per unit of actual ordinate degree `b` (nonzero only for `j ≤ 3`). -/
def beta (j : ℕ) : ℕ :=
  if j = 0 then 23143
  else if j = 1 then 19134
  else if j = 2 then 15213
  else if j = 3 then 11369
  else 0

/-- All denominator positivity, core-collinearity, identity-site, Veronese-gap, tame
characteristic, and global budget requirements hold strictly. -/
theorem parameters :
    n + 2 * d < 3 * core ∧ e < miss * 71987 ∧ 7378 < 71987 ∧
    4 * n ≤ 16 * (t - d) ∧
    n + 2 * d + 2 * miss < 3 * t ∧
    10 * n + 40 * d + 3 * 3 * miss < 3 * 15 * t ∧
    56 * n + 240 * d + 6 * 3 * miss < 6 * 45 * t ∧
    286 * n + 1632 * d + 11 * 3 * miss < 11 * 153 * t ∧
    969 * n + 5200 * d + 17 * 3 * miss < 17 * 325 * t ∧
    2 * (53 * t) * 106 < 2 ^ 100 ∧ 7378 * 7377 < 2 ^ 100 ∧
    bound < 2 * n ∧
    (∀ j : Fin 107, 4 ≤ j.val →
      ((1 ≤ j.val / 2 ∧ j.val / 2 < j.val) ∨
       (1 ≤ (j.val + 1) / 2 ∧ (j.val + 1) / 2 < j.val)) ∧
      n + d < t + discreteUnion j.val) := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Every `(j, b)` pair satisfies weight admissibility, Case-1 companion fallback,
and dual-constraint `(α, β)` pricing across all Veronese degree regimes. -/
theorem dual_prices :
    ∀ j : Fin 107,
      otherLabels j.val + (7378 - j.val) * alpha j.val + (106 - j.val) * beta j.val ≤ bound ∧
      (2 ≤ 106 - j.val → (7378 - j.val) + (206 - j.val) ≤ alpha j.val) ∧
      ∀ b : Fin (106 - j.val + 1), 2 ≤ b.val →
        b.val * d ≤ 53 * t - 1 - j.val * d ∧
        if j.val ≤ 3 then
          price24 j.val b.val ≤ alpha j.val ∧
          (b.val ≤ 12 → (basePrice j.val b.val - alpha j.val) * 12 ≤ beta j.val * b.val) ∧
          (b.val ≤ 56 → (price4 j.val b.val - alpha j.val) * 56 ≤ beta j.val * b.val) ∧
          (b.val ≤ 240 → (price8 j.val b.val - alpha j.val) * 240 ≤ beta j.val * b.val) ∧
          (b.val ≤ 552 → (price16 j.val b.val - alpha j.val) * 552 ≤ beta j.val * b.val)
        else
          basePrice j.val b.val ≤ alpha j.val := by
  decide +kernel

/-- Applicable per-unit-`m` nonlinear price for an actual factor of degrees `(b, m)`. -/
def factorUnitPrice (j b m : ℕ) : ℕ :=
  if j ≤ 3 then
    if 552 < m then price24 j b
    else if 240 < m then price16 j b
    else if 56 < m then price8 j b
    else if 12 < m then price4 j b
    else basePrice j b
  else basePrice j b

private theorem range_dual_step {u a β b m M : ℕ} (hm : m ≤ M)
    (h : (u - a) * M ≤ β * b) :
    m * u ≤ m * a + b * β := by
  by_cases hu : u ≤ a
  · exact (Nat.mul_le_mul_left m hu).trans (Nat.le_add_right _ _)
  · have hdiff : m * (u - a) ≤ (u - a) * M := by
      rw [mul_comm]; exact Nat.mul_le_mul_left _ hm
    have hstep : m * u = m * a + m * (u - a) := by
      rw [← Nat.mul_add, Nat.add_sub_of_le (by omega)]
    rw [hstep]
    have hbb : β * b = b * β := mul_comm _ _
    omega

private theorem factor_dual_bound (j : Fin 107) {b m : ℕ}
    (hb : 2 ≤ b) (hbhi : b ≤ 106 - j.val) (hbm : b ≤ m) :
    m * factorUnitPrice j.val b m ≤ m * alpha j.val + b * beta j.val := by
  have h := ((dual_prices j).2.2 ⟨b, by omega⟩ hb).2
  by_cases hj : j.val ≤ 3
  · simp only [hj, ↓reduceIte] at h
    unfold factorUnitPrice
    simp only [hj, ↓reduceIte]
    split_ifs with h552 h240 h56 h12
    · exact (Nat.mul_le_mul_left m h.1).trans (Nat.le_add_right _ _)
    · exact range_dual_step (by omega) (h.2.2.2.2 (by omega))
    · exact range_dual_step (by omega) (h.2.2.2.1 (by omega))
    · exact range_dual_step (by omega) (h.2.2.1 (by omega))
    · exact range_dual_step (by omega) (h.2.1 (by omega))
  · simp only [hj, ↓reduceIte] at h
    unfold factorUnitPrice
    simp only [hj, ↓reduceIte]
    exact (Nat.mul_le_mul_left m h).trans (Nat.le_add_right _ _)

/-- Total bad-scalar allocation across all six label classes at `534,295,000` quarter-rate errors.
Accepts both blown-up Gauss-graph factors (`pop ≤ deg * factorUnitPrice`) and Case-1
companion-cofactor fallback factors (`pop ≤ deg * ((7378 - j) + (206 - j))`). -/
theorem allocation {J : Type*} (S : Finset J) (degree value pop : J → ℕ) (j : Fin 107)
    (heads scalar outside small linear : ℕ)
    (hheads : heads ≤ headMass j.val)
    (hscalar : scalar ≤ 71987)
    (houtside : outside ≤ 71987 * 206 + 106 * 7378)
    (hsmall : small ≤ (106 - j.val) * 71987)
    (hlinear : linear ≤ (7378 - j.val) * 17)
    (htotalDeg : ∑ i ∈ S, degree i ≤ 7378 - j.val)
    (htotalVal : ∑ i ∈ S, value i ≤ 106 - j.val)
    (hvalue : ∀ i ∈ S, 2 ≤ value i ∧ value i ≤ degree i)
    (hpop : ∀ i ∈ S,
      pop i ≤ degree i * factorUnitPrice j.val (value i) (degree i) ∨
      pop i ≤ degree i * ((7378 - j.val) + (206 - j.val))) :
    heads + scalar + outside + small + linear + ∑ i ∈ S, pop i ≤ bound := by
  have each (i : J) (hi : i ∈ S) : pop i ≤ degree i * alpha j.val + value i * beta j.val := by
    obtain ⟨hlo, hvm⟩ := hvalue i hi
    have hhi : value i ≤ 106 - j.val :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi).trans htotalVal
    rcases hpop i hi with hgeom | hcase1
    · exact hgeom.trans (factor_dual_bound j hlo hhi hvm)
    · have h2 : 2 ≤ 106 - j.val := hlo.trans hhi
      exact (hcase1.trans (Nat.mul_le_mul_left _ ((dual_prices j).2.1 h2))).trans
        (Nat.le_add_right _ _)
  have hsum : ∑ i ∈ S, pop i ≤
      (∑ i ∈ S, degree i) * alpha j.val + (∑ i ∈ S, value i) * beta j.val := by
    calc ∑ i ∈ S, pop i ≤ ∑ i ∈ S, (degree i * alpha j.val + value i * beta j.val) :=
          Finset.sum_le_sum each
      _ = (∑ i ∈ S, degree i) * alpha j.val + (∑ i ∈ S, value i) * beta j.val := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  have h1 := Nat.mul_le_mul_right (alpha j.val) htotalDeg
  have h2 := Nat.mul_le_mul_right (beta j.val) htotalVal
  have htot := (dual_prices j).1
  unfold otherLabels at htot
  omega

#print axioms factor_order_sum_ge
#print axioms blowupH_mono
#print axioms ranks
#print axioms surfaces
#print axioms parameters
#print axioms dual_prices
#print axioms allocation

end ArkLib.ProximityGap.Frontier.QuarterBlowupGaussWindow

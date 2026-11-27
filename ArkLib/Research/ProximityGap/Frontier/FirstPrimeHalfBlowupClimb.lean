/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HalfBlowupGaussWindow

/-! # First-prime half-rate blown-up Gauss-graph climb through 312,400,000 errors

On the first designated prime (`B_1 = ⌊P_1 / 2^128⌋ = 2^30 = 1,073,741,824`, `d = 2^29 - 1`),
the open MCA first-failure bracket is `[268,435,457, 313,174,699]`.

This module reuses the nef-safe blown-up Gauss-graph algebraic core from `HalfBlowupGaussWindow`
at `e = 312,400,000` errors (`+43,964,543` errors above `268,435,457`, covering `98.27%` of the
open bracket) with primary surface `(54, 76, 44746)` and companion surface `(102, 144, 5412)`
(`miss = 7000`, `core = 761,334,824`) to prove:

1. **Non-exceptional (`j ≤ 3`) safety (`non_exceptional_safe`):** Every received pair with
   at most `3` rich polynomial affine heads (together with all nonlinear irreducible factors,
   nonaffine linear factors, small heads, scalar-only factors, and the primary/companion
   resultant) has at most `1,067,196,929 < 2^30` bad scalars (`6,544,895` slack below `B_1`).
2. **Forced collinear `4 ≤ j ≤ 76` reduction (`collinear_four_head_reduction`):** Across all
   remaining `4 ≤ j ≤ 76` rich-head counts allowed by the primary surface (`76 < 118`), the
   entire non-head bad-scalar contribution is at most `126,933,994`. Hence any over-budget pair
   in `[268,435,457, 312,400,000]` must possess `4 ≤ j ≤ 76` mutually collinear rich heads
   (`n + 2 * d < 3 * core`) carrying at least `946,807,831` bad scalars by themselves.
3. **Four-core overlap and common-direction cap (`four_core_overlap_and_direction_cap`):**
   Any four cores of size `≥ 761,334,824` on a length-`2^30` domain contain a distinct pair
   intersecting on at least `478,242,187` sites, capping the coprime common direction degree
   at `m ≤ 58,628,724`.

Honesty scope: The mixed-Hasse surface existence, dual-constraint allocation, non-head ceiling,
and four-core overlap/direction bounds are 100% kernel-checked in Lean. The blown-up surface
intersection and plane-curve duality bridge from bad scalars to the allocation hypotheses is
written in `docs/research/proximity-gap/half-blowup-gauss-window.md` and summarized in
`docs/research/proximity-gap/first-prime-half-blowup-climb.md`. The `4 ≤ j ≤ 76` collinear
rich-head family remains open in `[268,435,457, 312,400,000]`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.FirstPrimeHalfBlowupClimb

open Finset Polynomial HalfSuccessorJetInterpolation SecondPrimeQuarticInterpolation
open HalfBlowupGaussWindow (blowupH rowCount card_rows columnCount card_columns SectionSurface)

abbrev n : ℕ := 1073741824
abbrev d : ℕ := 536870911
abbrev e : ℕ := 312400000
abbrev t : ℕ := n - e
abbrev miss : ℕ := 7000
abbrev core : ℕ := t - miss
abbrev bound3 : ℕ := 1067196929
abbrev nonHeadBound4 : ℕ := 126933994

/-- Exact mixed-Hasse rank surpluses for the primary `(54, 76, 44746)` and
companion `(102, 144, 5412)` surfaces at `e = 312,400,000` half-rate errors. -/
theorem ranks :
    columnCount 44746 76 d (54 * t) = n * rowCount 44746 54 + 202506832 ∧
    columnCount 5412 144 d (102 * t) = n * rowCount 5412 102 + 7072525648 := by
  decide +kernel

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
/-- Both mixed-Hasse surfaces exist on every length-`2^30` injective domain over any field
and vanish on every witnessing section with at least `t = 761,341,824` agreements. -/
theorem surfaces {I F : Type} [Fintype I] [Field F] (dom : I ↪ F) (u v : I → F)
    (hn : Fintype.card I = n) (companion : Bool) :
    let r := if companion then 102 else 54
    let b := if companion then 144 else 76
    let s := if companion then 5412 else 44746
    SectionSurface dom u v s b d (r * t) t := by
  cases companion
  · obtain ⟨a, ha, jets, hf⟩ := exists_surface dom u v (by decide : 0 < 54) (by decide : 0 < t)
      (by decide : 54 ≤ 44746 + 1) (by
        rw [hn, card_rows, card_columns]
        exact ranks.1 ▸ Nat.lt_add_of_pos_right (by decide))
    exact ⟨surface a, surface_ne_zero ha, fun _ _ _ h => surface_support a h,
      fun x => received_line_of_jet a _ _ _ (jets x 0 0 (by decide)),
      fun g q hq S hS hag => by rw [surface_eval]; exact hf g q hq S hS hag⟩
  · obtain ⟨a, ha, jets, hf⟩ := exists_surface dom u v (by decide : 0 < 102) (by decide : 0 < t)
      (by decide : 102 ≤ 5412 + 1) (by
        rw [hn, card_rows, card_columns]
        exact ranks.2 ▸ Nat.lt_add_of_pos_right (by decide))
    exact ⟨surface a, surface_ne_zero ha, fun _ _ _ h => surface_support a h,
      fun x => received_line_of_jet a _ _ _ (jets x 0 0 (by decide)),
      fun g q hq S hS hag => by rw [surface_eval]; exact hf g q hq S hS hag⟩

/-! ## Dual-constraint Veronese and transverse pricing at 312,400,000 errors -/

private def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

private def unionAt (j a : ℕ) : ℕ :=
  ceilDiv (2 * a * j * core - j * (j - 1) * d) (a * (a + 1))

private def discreteUnion (j : ℕ) : ℕ :=
  let a₁ := 7 * j / 10
  let a₂ := (7 * j + 9) / 10
  let u₁ := if 1 ≤ a₁ ∧ a₁ < j then unionAt j a₁ else 0
  let u₂ := if 1 ≤ a₂ ∧ a₂ < j then unionAt j a₂ else 0
  max u₁ u₂

/-- Upper bound on the scalar population assigned to `j` rich polynomial affine heads. -/
def headMass (j : ℕ) : ℕ :=
  if j < 3 then j * (e + 1) else
    let cover := max (discreteUnion j) (ceilDiv (j * core ^ 2) (core + (j - 1) * d))
    min (j * (e + 1)) (j * n - (j - 1) * cover)

/-- Blown-up height bound maximized over `W ∈ [b * d, min (54 * t - 1 - j * d) (b * t - 1)]`. -/
def maxBlowupH (j b : ℕ) : ℕ :=
  blowupH b (min (54 * t - 1 - j * d) (b * t - 1)) t d

/-- Base price per unit of actual companion degree (triangle determinant, plus transverse
tangent bound when `j ≥ 3`), valid for every actual plane degree `m ≥ b`. -/
def basePrice (j b : ℕ) : ℕ :=
  let H := maxBlowupH j b
  let R := (2 * b - 1) * n
  let p := min j 2
  let tri := 2 * b + ceilDiv ((3 - p) * (R + H)) (3 * t - (n + 2 * d + p * miss))
  let trv := if 3 ≤ j then 2 * b + ceilDiv (H + R) (t + discreteUnion j - (n + d)) else tri
  4 * b - 2 + min tri trv

/-- Veronese price per unit of actual companion degree at `j = 0` for `(s, a)`
valid whenever `m > s * (s - 1)`. -/
def veronesePrice (b s a h C_a E_s : ℕ) : ℕ :=
  let H := maxBlowupH 0 b
  let R := (2 * b - 1) * n
  let gap := a * h * t - (C_a * n + E_s * d)
  4 * b - 2 + 2 * s * b + ceilDiv (h * (a * R + s * H)) gap

/-- Price per unit of actual companion degree at `j = 0` valid for `m > 30`. -/
def price6 (b : ℕ) : ℕ := min (basePrice 0 b) (veronesePrice b 6 5 28 35 112)

/-- Price per unit of actual companion degree at `j = 0` valid for `m > 132`. -/
def price12 (b : ℕ) : ℕ := min (price6 b) (veronesePrice b 12 10 91 220 728)

/-- Price per unit of actual companion degree at `j = 0` valid for `m > 552`. -/
def price24 (b : ℕ) : ℕ := min (price12 b) (veronesePrice b 24 20 325 1540 5200)

/-- The four non-head, non-nonlinear label classes: scalar-only primary factors, single
noncommon resultant, small polynomial heads, and nonaffine common linear factors. -/
def nonHeadBase (j : ℕ) : ℕ :=
  44746 + (44746 * 144 + 76 * 5412) + (76 - j) * 44746 + (5412 - j) * 21

/-- Linear-duality slope per unit of actual companion degree `m` for `j ≤ 3`. -/
def alphaLe3 (j : ℕ) : ℕ :=
  if j = 0 then 52991 else (bound3 - (headMass j + nonHeadBase j)) / (5412 - j)

/-- Linear-duality surcharge per unit of actual ordinate degree `b` for `j ≤ 3`. -/
def betaLe3 (j : ℕ) : ℕ :=
  if j = 0 then 14109 else 0

/-- Linear-duality slope per unit of actual companion degree `m` for `4 ≤ j ≤ 76`. -/
def alpha4Plus (j : ℕ) : ℕ :=
  (nonHeadBound4 - nonHeadBase j) / (5412 - j)

/-- Applicable per-unit-`m` nonlinear price for an actual factor of degrees `(b, m)`. -/
def factorUnitPrice (j b m : ℕ) : ℕ :=
  if j = 0 then
    if 552 < m then price24 b
    else if 132 < m then price12 b
    else if 30 < m then price6 b
    else basePrice 0 b
  else basePrice j b

/-- All denominator positivity, forced collinearity, identity-site, Veronese-gap,
tame characteristic (`< 2^100 < P_1`), and budget inequalities hold strictly. -/
theorem parameters :
    n + 2 * d < 3 * core ∧ e < miss * 44746 ∧ 5412 < 44746 ∧
    4 * n ≤ 20 * (t - d) ∧
    n + 2 * d + 2 * miss < 3 * t ∧
    35 * n + 112 * d < 5 * 28 * t ∧
    220 * n + 728 * d < 10 * 91 * t ∧
    1540 * n + 5200 * d < 20 * 325 * t ∧
    2 * (54 * t) * 76 < 2 ^ 100 ∧ 5412 * 5411 < 2 ^ 100 ∧
    bound3 < n ∧
    nonHeadBase 0 + 5412 * alphaLe3 0 + 76 * betaLe3 0 ≤ 298273406 ∧
    (∀ j : Fin 77, 3 ≤ j.val →
      ((1 ≤ 7 * j.val / 10 ∧ 7 * j.val / 10 < j.val) ∨
       (1 ≤ (7 * j.val + 9) / 10 ∧ (7 * j.val + 9) / 10 < j.val)) ∧
      n + d < t + discreteUnion j.val) := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Dual-constraint `(α, β)` pricing for all `j ≤ 3` rich-head counts below `bound3 < B_1`. -/
theorem dual_prices_le_three :
    ∀ j : Fin 4,
      headMass j.val + nonHeadBase j.val +
        (5412 - j.val) * alphaLe3 j.val + (76 - j.val) * betaLe3 j.val ≤ bound3 ∧
      (5412 - j.val) + (144 - j.val) ≤ alphaLe3 j.val ∧
      ∀ b : Fin (76 - j.val + 1), 2 ≤ b.val →
        b.val * d ≤ 54 * t - 1 - j.val * d ∧
        if j.val = 0 then
          price24 b.val ≤ alphaLe3 0 ∧
          (b.val ≤ 30 → (basePrice 0 b.val - alphaLe3 0) * 30 ≤ betaLe3 0 * b.val) ∧
          (b.val ≤ 132 → (price6 b.val - alphaLe3 0) * 132 ≤ betaLe3 0 * b.val) ∧
          (b.val ≤ 552 → (price12 b.val - alphaLe3 0) * 552 ≤ betaLe3 0 * b.val)
        else
          basePrice j.val b.val ≤ alphaLe3 j.val := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Uniform non-head cap `≤ 126,933,994` across all `4 ≤ j ≤ 76` rich-head counts. -/
theorem dual_prices_four_plus :
    ∀ j : Fin 77, 4 ≤ j.val →
      nonHeadBase j.val + (5412 - j.val) * alpha4Plus j.val ≤ nonHeadBound4 ∧
      (2 ≤ 76 - j.val → (5412 - j.val) + (144 - j.val) ≤ alpha4Plus j.val) ∧
      ∀ b : Fin (76 - j.val + 1), 2 ≤ b.val →
        b.val * d ≤ 54 * t - 1 - j.val * d ∧
        basePrice j.val b.val ≤ alpha4Plus j.val := by
  decide +kernel

private theorem factor_dual_bound_le3 (j : Fin 4) {b m : ℕ}
    (hb : 2 ≤ b) (hbhi : b ≤ 76 - j.val) (hbm : b ≤ m) :
    m * factorUnitPrice j.val b m ≤ m * alphaLe3 j.val + b * betaLe3 j.val := by
  have h := ((dual_prices_le_three j).2.2 ⟨b, by omega⟩ hb).2
  by_cases hj : j.val = 0
  · simp only [hj, ↓reduceIte] at h
    unfold factorUnitPrice
    simp only [hj, ↓reduceIte]
    split_ifs with h552 h132 h30
    · exact (Nat.mul_le_mul_left m h.1).trans (Nat.le_add_right _ _)
    · have hle : b ≤ 552 := by omega
      have h5 := h.2.2.2 hle
      by_cases hu : price12 b ≤ alphaLe3 0
      · exact (Nat.mul_le_mul_left m hu).trans (Nat.le_add_right _ _)
      · have hdiff : m * (price12 b - alphaLe3 0) ≤ (price12 b - alphaLe3 0) * 552 := by
          rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
        have hstep : m * price12 b = m * alphaLe3 0 + m * (price12 b - alphaLe3 0) := by
          rw [← Nat.mul_add, Nat.add_sub_of_le (by omega)]
        rw [hstep]
        have hbb : betaLe3 0 * b = b * betaLe3 0 := mul_comm _ _
        omega
    · have hle : b ≤ 132 := by omega
      have h4 := h.2.2.1 hle
      by_cases hu : price6 b ≤ alphaLe3 0
      · exact (Nat.mul_le_mul_left m hu).trans (Nat.le_add_right _ _)
      · have hdiff : m * (price6 b - alphaLe3 0) ≤ (price6 b - alphaLe3 0) * 132 := by
          rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
        have hstep : m * price6 b = m * alphaLe3 0 + m * (price6 b - alphaLe3 0) := by
          rw [← Nat.mul_add, Nat.add_sub_of_le (by omega)]
        rw [hstep]
        have hbb : betaLe3 0 * b = b * betaLe3 0 := mul_comm _ _
        omega
    · have hle : b ≤ 30 := by omega
      have h3 := h.2.1 hle
      by_cases hu : basePrice 0 b ≤ alphaLe3 0
      · exact (Nat.mul_le_mul_left m hu).trans (Nat.le_add_right _ _)
      · have hdiff : m * (basePrice 0 b - alphaLe3 0) ≤ (basePrice 0 b - alphaLe3 0) * 30 := by
          rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
        have hstep : m * basePrice 0 b = m * alphaLe3 0 + m * (basePrice 0 b - alphaLe3 0) := by
          rw [← Nat.mul_add, Nat.add_sub_of_le (by omega)]
        rw [hstep]
        have hbb : betaLe3 0 * b = b * betaLe3 0 := mul_comm _ _
        omega
  · simp only [hj, ↓reduceIte] at h
    unfold factorUnitPrice
    simp only [hj, ↓reduceIte]
    exact (Nat.mul_le_mul_left m h).trans (Nat.le_add_right _ _)

/-- **Non-exceptional (`j ≤ 3`) safety through `312,400,000` errors on the first prime:**
Any configuration with at most three rich polynomial affine heads (plus all nonlinear,
nonaffine linear, small-head, scalar-only, and resultant labels) has strictly fewer than
`B_1 = 2^30 = 1,073,741,824` bad scalars (`≤ 1,067,196,929`, slack `6,544,895`). -/
theorem non_exceptional_safe {J : Type*} (S : Finset J) (degree value pop : J → ℕ) (j : Fin 4)
    (heads scalar outside small linear : ℕ)
    (hheads : heads ≤ headMass j.val)
    (hscalar : scalar ≤ 44746)
    (houtside : outside ≤ 44746 * 144 + 76 * 5412)
    (hsmall : small ≤ (76 - j.val) * 44746)
    (hlinear : linear ≤ (5412 - j.val) * 21)
    (htotalDeg : ∑ i ∈ S, degree i ≤ 5412 - j.val)
    (htotalVal : ∑ i ∈ S, value i ≤ 76 - j.val)
    (hvalue : ∀ i ∈ S, 2 ≤ value i ∧ value i ≤ degree i)
    (hpop : ∀ i ∈ S,
      pop i ≤ degree i * factorUnitPrice j.val (value i) (degree i) ∨
      pop i ≤ degree i * ((5412 - j.val) + (144 - j.val))) :
    heads + scalar + outside + small + linear + ∑ i ∈ S, pop i ≤ bound3 ∧ bound3 < n := by
  have each (i : J) (hi : i ∈ S) :
      pop i ≤ degree i * alphaLe3 j.val + value i * betaLe3 j.val := by
    obtain ⟨hlo, hvm⟩ := hvalue i hi
    have hhi : value i ≤ 76 - j.val :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi).trans htotalVal
    rcases hpop i hi with hgeom | hcase1
    · exact hgeom.trans (factor_dual_bound_le3 j hlo hhi hvm)
    · exact (hcase1.trans (Nat.mul_le_mul_left _ (dual_prices_le_three j).2.1)).trans
        (Nat.le_add_right _ _)
  have hsum : ∑ i ∈ S, pop i ≤
      (∑ i ∈ S, degree i) * alphaLe3 j.val + (∑ i ∈ S, value i) * betaLe3 j.val := by
    calc ∑ i ∈ S, pop i ≤ ∑ i ∈ S, (degree i * alphaLe3 j.val + value i * betaLe3 j.val) :=
          Finset.sum_le_sum each
      _ = (∑ i ∈ S, degree i) * alphaLe3 j.val + (∑ i ∈ S, value i) * betaLe3 j.val := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  have h1 := Nat.mul_le_mul_right (alphaLe3 j.val) htotalDeg
  have h2 := Nat.mul_le_mul_right (betaLe3 j.val) htotalVal
  have htot := (dual_prices_le_three j).1
  unfold nonHeadBase at htot
  exact ⟨by omega, parameters.2.2.2.2.2.2.2.2.2.2.1⟩

/-- **Collinear `4 ≤ j ≤ 76` reduction through `312,400,000` errors on the first prime:**
For every `4 ≤ j ≤ 76`, the entire non-head mass is at most `126,933,994`. Consequently,
any configuration exceeding the first prime's 128-bit budget `2^30` must have its collinear
rich heads alone carry at least `946,807,831` bad scalars. -/
theorem collinear_four_head_reduction {J : Type*} (S : Finset J) (degree value pop : J → ℕ)
    (j : Fin 77) (hj : 4 ≤ j.val)
    (heads scalar outside small linear : ℕ)
    (hscalar : scalar ≤ 44746)
    (houtside : outside ≤ 44746 * 144 + 76 * 5412)
    (hsmall : small ≤ (76 - j.val) * 44746)
    (hlinear : linear ≤ (5412 - j.val) * 21)
    (htotalDeg : ∑ i ∈ S, degree i ≤ 5412 - j.val)
    (htotalVal : ∑ i ∈ S, value i ≤ 76 - j.val)
    (hvalue : ∀ i ∈ S, 2 ≤ value i ∧ value i ≤ degree i)
    (hpop : ∀ i ∈ S,
      pop i ≤ degree i * factorUnitPrice j.val (value i) (degree i) ∨
      pop i ≤ degree i * ((5412 - j.val) + (144 - j.val))) :
    scalar + outside + small + linear + ∑ i ∈ S, pop i ≤ nonHeadBound4 ∧
    (n < heads + scalar + outside + small + linear + ∑ i ∈ S, pop i → 946807831 ≤ heads) := by
  have hd := dual_prices_four_plus j hj
  have each (i : J) (hi : i ∈ S) : pop i ≤ degree i * alpha4Plus j.val := by
    obtain ⟨hlo, _⟩ := hvalue i hi
    have hhi : value i ≤ 76 - j.val :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi).trans htotalVal
    rcases hpop i hi with hgeom | hcase1
    · have hjne : j.val ≠ 0 := by omega
      unfold factorUnitPrice at hgeom
      simp only [hjne, ↓reduceIte] at hgeom
      exact hgeom.trans (Nat.mul_le_mul_left _ (hd.2.2 ⟨value i, by omega⟩ hlo).2)
    · exact hcase1.trans (Nat.mul_le_mul_left _ (hd.2.1 (hlo.trans hhi)))
  have hsum : ∑ i ∈ S, pop i ≤ (∑ i ∈ S, degree i) * alpha4Plus j.val := by
    calc ∑ i ∈ S, pop i ≤ ∑ i ∈ S, degree i * alpha4Plus j.val := Finset.sum_le_sum each
      _ = (∑ i ∈ S, degree i) * alpha4Plus j.val := (Finset.sum_mul ..).symm
  have h1 := Nat.mul_le_mul_right (alpha4Plus j.val) htotalDeg
  have htot := hd.1
  unfold nonHeadBase at htot
  have hnh : scalar + outside + small + linear + ∑ i ∈ S, pop i ≤ nonHeadBound4 := by omega
  exact ⟨hnh, fun hover => by dsimp only [n, nonHeadBound4] at hover hnh; omega⟩

/-- **Four-core pairwise overlap and common-direction degree cap at `312,400,000` errors:**
Among any four cores of size at least `core = 761,334,824` inside a length-`2^30` domain,
some distinct pair intersects in at least `478,242,187` sites (via the discrete `a = 2`
double-counting inequality `5 * d_x ≤ d_x^2 + 6`). Whenever a common coprime direction pair
has maximum degree `m` with `m + (C i ∩ C j).card ≤ d`, this forces `m ≤ 58,628,724`. -/
theorem four_core_overlap_and_direction_cap {I : Type*} [Fintype I] [DecidableEq I]
    (C : Fin 4 → Finset I) (hI : Fintype.card I = n)
    (hC : ∀ i : Fin 4, core ≤ (C i).card) :
    ∃ i j : Fin 4, i ≠ j ∧ 478242187 ≤ (C i ∩ C j).card ∧
      ∀ m : ℕ, m + (C i ∩ C j).card ≤ d → m ≤ 58628724 := by
  let deg (x : I) : ℕ := (univ.filter fun i : Fin 4 => x ∈ C i).card
  have hpoint : ∀ x : I, 4 * deg x ≤ deg x * (deg x - 1) + 6 := by
    intro x
    have hle : deg x ≤ 4 := (card_le_univ _).trans_eq (Fintype.card_fin 4)
    interval_cases h : deg x <;> decide
  have hsum_deg : ∑ x : I, deg x = ∑ i : Fin 4, (C i).card := by
    simp only [deg, card_eq_sum_ones, sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sum_filter, filter_mem_eq_inter, univ_inter]
  have hsum_pairs : ∑ x : I, deg x * (deg x - 1) =
      ∑ i : Fin 4, ∑ j ∈ univ.erase i, (C i ∩ C j).card := by
    have hpair_x : ∀ x : I, deg x * (deg x - 1) =
        ∑ i : Fin 4, ∑ j ∈ univ.erase i, if x ∈ C i ∩ C j then 1 else 0 := by
      intro x
      let Sx : Finset (Fin 4) := univ.filter fun i => x ∈ C i
      have hsum_off : deg x * (deg x - 1) = ∑ i ∈ Sx, ∑ _j ∈ Sx.erase i, (1 : ℕ) := by
        have hinner_card : ∀ i ∈ Sx, ∑ _j ∈ Sx.erase i, (1 : ℕ) = Sx.card - 1 := fun i hi => by
          rw [Finset.sum_const, Finset.card_erase_of_mem hi, smul_eq_mul, mul_one]
        rw [Finset.sum_congr rfl hinner_card, Finset.sum_const, smul_eq_mul]
      rw [hsum_off]
      have hinner : ∀ i : Fin 4,
          (if x ∈ C i then ∑ j ∈ Sx.erase i, (1 : ℕ) else 0) =
          ∑ j ∈ univ.erase i, if x ∈ C i ∩ C j then 1 else 0 := by
        intro i
        by_cases hi : x ∈ C i
        · simp only [hi, ↓reduceIte, mem_inter, true_and]
          rw [← sum_filter]
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext j
          simp [Sx]
        · simp only [hi, ↓reduceIte, mem_inter, false_and, sum_const_zero]
      calc ∑ i ∈ Sx, ∑ j ∈ Sx.erase i, (1 : ℕ)
          = ∑ i : Fin 4, if x ∈ C i then ∑ j ∈ Sx.erase i, (1 : ℕ) else 0 := by
              rw [← sum_filter]
        _ = ∑ i : Fin 4, ∑ j ∈ univ.erase i, if x ∈ C i ∩ C j then 1 else 0 :=
              Finset.sum_congr rfl fun i _ => hinner i
    calc ∑ x : I, deg x * (deg x - 1)
        = ∑ x : I, ∑ i : Fin 4, ∑ j ∈ univ.erase i, if x ∈ C i ∩ C j then 1 else 0 :=
            Finset.sum_congr rfl fun x _ => hpair_x x
      _ = ∑ i : Fin 4, ∑ x : I, ∑ j ∈ univ.erase i, if x ∈ C i ∩ C j then 1 else 0 :=
            Finset.sum_comm
      _ = ∑ i : Fin 4, ∑ j ∈ univ.erase i, ∑ x : I, if x ∈ C i ∩ C j then 1 else 0 :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ i : Fin 4, ∑ j ∈ univ.erase i, (C i ∩ C j).card := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [← sum_filter, filter_mem_eq_inter, univ_inter, card_eq_sum_ones]
  have htot_ineq : 4 * (∑ i : Fin 4, (C i).card) ≤
      (∑ i : Fin 4, ∑ j ∈ univ.erase i, (C i ∩ C j).card) + 6 * n := by
    have hs := Finset.sum_le_sum (s := (univ : Finset I)) fun x _ => hpoint x
    rw [← Finset.mul_sum, hsum_deg, Finset.sum_add_distrib, hsum_pairs,
      Finset.sum_const, Finset.card_univ, hI, smul_eq_mul, mul_comm n 6] at hs
    exact hs
  have hsumC : 4 * core ≤ ∑ i : Fin 4, (C i).card := by
    calc 4 * core = ∑ _i : Fin 4, core := by simp
      _ ≤ ∑ i : Fin 4, (C i).card := Finset.sum_le_sum fun i _ => hC i
  by_contra hno
  push Not at hno
  have hall : ∀ i : Fin 4, ∀ j ∈ univ.erase i, (C i ∩ C j).card ≤ 478242186 := by
    intro i j hj
    have hne : i ≠ j := (mem_erase.mp hj).1.symm
    have hlt := hno i j hne
    by_contra hge
    push Not at hge
    obtain ⟨m, hm1, hm2⟩ := hlt hge
    dsimp only [d] at hm1
    omega
  have hub : ∑ i : Fin 4, ∑ j ∈ univ.erase i, (C i ∩ C j).card ≤ 12 * 478242186 := by
    calc ∑ i : Fin 4, ∑ j ∈ univ.erase i, (C i ∩ C j).card
        ≤ ∑ i : Fin 4, ∑ _j ∈ univ.erase i, 478242186 :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => hall i j hj
      _ = 12 * 478242186 := by
            simp [Finset.sum_const, Finset.card_erase_of_mem]
  have : 16 * core ≤ 12 * 478242186 + 6 * n := by omega
  revert this
  decide

#print axioms ranks
#print axioms surfaces
#print axioms parameters
#print axioms dual_prices_le_three
#print axioms dual_prices_four_plus
#print axioms non_exceptional_safe
#print axioms collinear_four_head_reduction
#print axioms four_core_overlap_and_direction_cap

end ArkLib.ProximityGap.Frontier.FirstPrimeHalfBlowupClimb

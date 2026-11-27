/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HalfBlowupGaussWindow

/-!
# Interpolation and allocation with shared factor degrees

The four mixed-Hasse surfaces serve the half-rate window at 313,234,000 errors and the
quarter-rate window at 534,325,000 errors. Removing the selected common factors decreases
both degrees in the resultant. The remaining charge has its maximum at zero unused
companion degree or at its residual ordinate degree.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.SharedFactorDegrees

open Finset Polynomial SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation
open HalfBlowupGaussWindow (rowCount columnCount card_rows card_columns)

private abbrev length : ℕ := 2 ^ 30

/-- Order, ordinate, plane-degree and rank data of one received-row surface. -/
structure Shape where
  d : ℕ
  t : ℕ
  r : ℕ
  v : ℕ
  s : ℕ
  surplus : ℕ

/-- Primary and companion shapes for half rate, followed by their quarter-rate counterparts. -/
def shape : Fin 4 → Shape
  | 0 => ⟨536870911, 760507824, 89, 126, 295664, 4238610⟩
  | 1 => ⟨536870911, 760507824, 174, 246, 14868, 1662163854⟩
  | 2 => ⟨268435455, 539416824, 53, 106, 130044, 108222714⟩
  | 3 => ⟨268435455, 539416824, 104, 208, 7551, 14248080392⟩

set_option maxRecDepth 8192 in
/-- The surplus after imposing every received-line mixed jet, for all four shapes. -/
theorem ranks : ∀ i : Fin 4,
    let k := shape i
    columnCount k.s k.v k.d (k.r * k.t) = length * rowCount k.s k.r + k.surplus ∧
    0 < k.surplus ∧ 0 < k.t ∧ 0 < k.r ∧ k.r ≤ k.s + 1 := by
  decide +kernel

/-- The four nonzero interpolants exist for every injective domain and received row pair.
The conclusion includes the mixed jets and vanishing on every witnessing polynomial. -/
theorem surfaces {I F : Type} [Fintype I] [Field F] (dom : I ↪ F) (u v : I → F)
    (hn : Fintype.card I = 2 ^ 30) (i : Fin 4) :
    let k := shape i
    ∃ c : Monomials k.s k.v k.d (k.r * k.t) → F, c ≠ 0 ∧
      (∀ x a b, a + b < k.r →
        ∑ m, C (c m) * jetTerm m a b (dom x) (u x) (v x) = 0) ∧
      ∀ g : F, ∀ q : F[X], q.natDegree ≤ k.d → ∀ S : Finset I, k.t ≤ S.card →
        (∀ x ∈ S, q.eval (dom x) = u x + g * v x) → specialize c g q = 0 := by
  obtain ⟨hcount, hpos, ht, hr, hs⟩ := ranks i
  apply exists_surface dom u v hr ht hs
  rw [hn, card_rows, card_columns, hcount]
  exact Nat.lt_add_of_pos_right hpos

/-- With noncommon degree at most `offset + z` and companion ordinate degree at most
`min D z`, the surplus cost over the common-factor allocation peaks at `z = 0` or `z = D`.
The slope condition controls the tail above `D`. -/
theorem residual_charge_le (offset D g α z : ℤ) (hz : 0 ≤ z) (hprice : D + g ≤ α) :
    (offset + z) * min D z + (g - α) * z ≤ max 0 ((offset + D + g - α) * D) := by
  by_cases hzD : z ≤ D
  · rw [min_eq_right hzD]
    have hsq := mul_nonneg hz (sub_nonneg.mpr hzD)
    by_cases hlin : 0 ≤ offset + D + g - α
    · have htop := mul_nonneg (sub_nonneg.mpr hzD) hlin
      apply le_trans _ (le_max_right _ _)
      nlinarith only [hsq, htop]
    · have hlow := mul_nonpos_of_nonneg_of_nonpos hz (le_of_lt (lt_of_not_ge hlin))
      apply le_trans _ (le_max_left _ _)
      nlinarith only [hsq, hlow]
  · have hDz : D ≤ z := le_of_lt (lt_of_not_ge hzD)
    rw [min_eq_left hDz]
    have htail := mul_nonneg (sub_nonneg.mpr hDz) (sub_nonneg.mpr hprice)
    apply le_trans _ (le_max_right _ _)
    nlinarith only [htail]

/-- With a single residual ordinate slot, a small affine head or a nonaffine linear factor
fits into the same allowance for every unused companion plane degree `z`. -/
theorem linear_residual_le (s offset ℓ α z : ℤ) (hz : 0 ≤ z) (hℓ : 0 ≤ ℓ) (ha : ℓ ≤ α) :
    max s (ℓ * (offset + z)) - α * z ≤ max s (ℓ * offset) := by
  have hax := mul_nonneg (le_trans hℓ ha) hz
  have hdiff := mul_nonneg (sub_nonneg.mpr ha) hz
  apply sub_le_iff_le_add.mpr
  apply max_le
  · exact (le_max_left _ _).trans (le_add_of_nonneg_right hax)
  · have := le_max_right s (ℓ * offset)
    nlinarith only [this, hdiff]

#print axioms ranks
#print axioms surfaces
#print axioms residual_charge_le
#print axioms linear_residual_le


/-- Primary and companion shapes, with the choice of applicable tangent bounds. -/
structure Window where
  primary : Shape
  companion : Shape
  half : Bool

private def window (half : Bool) : Window :=
  if half then ⟨shape 0, shape 1, true⟩
  else ⟨shape 2, shape 3, false⟩

private def ceilDiv (x y : ℕ) : ℕ := (x + y - 1) / y

private def unionAt (j core d a : ℕ) : ℕ :=
  if 1 ≤ a ∧ a < j then
    ceilDiv (2 * a * j * core - j * (j - 1) * d) (a * (a + 1))
  else 0

private def headBounds (w : Window) (j miss : ℕ) : ℕ × ℕ :=
  let k := w.primary
  let separate := j * (length - k.t + 1)
  let core := k.t - miss
  if j < 3 then (separate, 0) else
    let test := unionAt j core k.d
    let discrete := max (max (test (j / 2)) (test ((j + 1) / 2)))
      (max (test (7 * j / 10)) (test ((7 * j + 9) / 10)))
    let cover := max discrete (ceilDiv (j * core ^ 2) (core + (j - 1) * k.d))
    (min separate (j * length - (j - 1) * cover), discrete)

private def levels (w : Window) (j : ℕ) : List (ℕ × ℕ) :=
  if w.half then
    if j = 0 then [(6,5), (12,10), (24,20)] else []
  else if j ≤ 3 then [(4,3), (8,6), (16,11), (24,17)] else []

/-- Tangent unit price and its slope relaxation in the actual ordinate degree. -/
private def factorPrice (w : Window) (j b miss union : ℕ) : ℕ × ℕ :=
  let k := w.primary
  let wt := min (k.r * k.t - 1 - j * k.d) (b * k.t - 1)
  let height := HalfBlowupGaussWindow.blowupH b wt k.t k.d
  let loss := (2 * b - 1) * length
  let p := min j 2
  let tri := 6 * b - 2 + ceilDiv ((3 - p) * (height + loss))
    (3 * k.t - (length + 2 * k.d + p * miss))
  let base := if (if w.half then 3 else 4) ≤ j then
      min tri (6 * b - 2 + ceilDiv (height + loss) (k.t + union - (length + k.d)))
    else tri
  let fallback := w.companion.s + w.companion.v - 2 * j
  let p' := min j 3
  let ladder := (levels w j).foldl (fun (acc : ℕ × List (ℕ × ℕ)) level =>
    let (s,a) := level
    let h := (s + 2) * (s + 1) / 2
    let gap := a * h * k.t - ((a + 2) * (a + 1) * a / 6 * length +
      s * (s + 1) * (s + 2) / 3 * k.d + a * p' * miss)
    let price := 4 * b - 2 + 2 * s * b +
      ceilDiv ((h - p') * (a * loss + s * height)) gap
    (min acc.1 price, (s * (s - 1), max acc.1 fallback) :: acc.2)) (base, [])
  let α := max fallback ladder.1
  (α, ladder.2.foldl (fun β pair => max β (ceilDiv (pair.1 * (pair.2 - α)) b)) 0)

private structure Charges where
  alpha : ℕ
  beta : ℕ
  peak : ℕ
  slopes : Bool

private def rowCharges (w : Window) (j : ℕ) : Charges :=
  let k := w.primary
  let l := w.companion
  let miss := (length - k.t) / k.s + 1
  let linear := 1 + ceilDiv (4 * length) (k.t - k.d)
  let (heads, union) := headBounds w j miss
  let empty := heads + k.s + (k.s - j) * (l.v - j) +
    (k.v - j) * (l.s - j + k.s) + linear * (l.s - j)
  (List.range (k.v - j - 1)).foldl (fun acc idx =>
    let c := idx + 2
    let (a,b) := factorPrice w j c miss union
    let α := max a acc.alpha
    let β := max b acc.beta
    let u := k.v - j - c
    let D := l.v - j - c
    let base := heads + k.s + (l.s - j) * α + (k.v - j) * β
    let extra := if u = 0 then 0 else if u = 1 then
        max k.s (linear * (k.s - l.s))
      else u * k.s + ((k.s - l.s) + D + u + linear - α) * D
    let slope := if u = 1 then linear ≤ α else if 2 ≤ u then D + u + linear ≤ α else True
    ⟨α, β, max acc.peak (base + extra), acc.slopes && decide slope⟩)
    ⟨0, 0, empty, true⟩

/-- Largest certified charge over all head counts, together with the residual slope tests. -/
def allocationSummary (half : Bool) : ℕ × Bool :=
  let w := window half
  (List.range (w.primary.v + 1)).foldl (fun summary j =>
    let charges := rowCharges w j
    (max summary.1 charges.peak, summary.2 && charges.slopes)) (0, true)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
/-- Every empty case and every possible maximum ordinate degree of an active common nonlinear
factor satisfies the residual slope condition and the two stated production bounds. -/
theorem allocation : allocationSummary true = (2145566228, true) ∧
    allocationSummary false = (2146821341, true) := by
  decide +kernel

#print axioms allocation

end ArkLib.ProximityGap.Frontier.SharedFactorDegrees

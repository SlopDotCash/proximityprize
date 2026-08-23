/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.QRShiftPairCount

/-!
# The G³-scaling assembly: zero-sum QR triples `= #QR* · M` (#389)

`QRShiftPairCount.qr_shift_count` proved the order-2 cyclotomic number
`M = #{u : u, u+1 ∈ QR*} = (q−5)/4` (the consecutive-quadratic-residue count, character-
sum-free via the conic `y² = 1 + x²`).  The docstring there flagged the **G³-scaling
assembly** — connecting `M` to the cubic word's sub-Johnson list size on the QR domain —
as the next step.  This file delivers its core:

> **`qr_zeroSum_ordered_eq`** — when `−1` is a square (`q ≡ 1 mod 4`) and `2 ≠ 0`, the
> number of ORDERED triples `(a,b,c) ∈ (QR*)³` with `a + b + c = 0` is exactly
> `#QR* · M`.

The mechanism is the multiplicative scaling that gives the assembly its name: the map
`(a,b,c) ↦ (a, b/a)` is a bijection onto `QR* × {u : u, u+1 ∈ QR*}`.  Indeed `b/a ∈ QR*`
(ratio of squares), and `(b/a) + 1 = (b+a)/a = −c/a ∈ QR*` (since `−1, c, a⁻¹` are all
squares); the inverse is `(a,u) ↦ (a, a·u, −a − a·u)`.  Combined with
`card_units_squares` (`#QR* = (q−1)/2`) and `qr_shift_count` (`M = (q−5)/4`) this gives
the exact ordered count `(q−1)(q−5)/8`, and via `cubic_list_eq_zeroSum` plus the standard
degenerate-triple correction `6·#unordered = #ordered − 3·#QR*·[−2 ∈ QR*]` it is the
heart of the exact smooth-domain (QR) cubic list size `n(q−5)/24` (`q ≡ 5 mod 8`) /
`n(q−17)/24` (`q ≡ 1 mod 8`).  Issue #389.
-/

open Finset

namespace ProximityGap.PairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The nonzero squares `QR* ⊆ F`. -/
def qrStar : Finset F := (Finset.univ : Finset F).filter (fun x => x ≠ 0 ∧ IsSquare x)

/-- The consecutive-QR pairs `{u : u, u+1 ∈ QR*}` — the `M`-set of `qr_shift_count`. -/
def qrConsec : Finset F :=
  (Finset.univ : Finset F).filter
    (fun u => u ≠ 0 ∧ IsSquare u ∧ u + 1 ≠ 0 ∧ IsSquare (u + 1))

/-- Ordered zero-sum triples of nonzero squares. -/
def qrZeroSumTriples : Finset (F × F × F) :=
  (Finset.univ : Finset (F × F × F)).filter
    (fun t => t.1 ∈ qrStar ∧ t.2.1 ∈ qrStar ∧ t.2.2 ∈ qrStar ∧ t.1 + t.2.1 + t.2.2 = 0)

omit [Fintype F] [DecidableEq F] in
/-- A ratio of squares is a square. -/
theorem isSquare_div {a b : F} (ha : IsSquare a) (hb : IsSquare b) : IsSquare (a / b) := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · exact ⟨s / t, by rw [div_mul_div_comm]⟩

omit [Fintype F] [DecidableEq F] in
/-- If `−1` and `a` are squares then so is `−a`. -/
theorem isSquare_neg_of_neg_one {a : F} (hneg1 : IsSquare (-1 : F)) (ha : IsSquare a) :
    IsSquare (-a) := by
  have : (-a) = (-1) * a := by ring
  rw [this]; exact hneg1.mul ha

/-- Membership in `qrStar`, unpacked. -/
theorem mem_qrStar {x : F} : x ∈ qrStar ↔ x ≠ 0 ∧ IsSquare x := by
  simp only [qrStar, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Membership in `qrConsec`, unpacked. -/
theorem mem_qrConsec {u : F} :
    u ∈ qrConsec ↔ u ≠ 0 ∧ IsSquare u ∧ u + 1 ≠ 0 ∧ IsSquare (u + 1) := by
  simp only [qrConsec, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Membership in `qrZeroSumTriples`, unpacked. -/
theorem mem_qrZeroSumTriples {t : F × F × F} :
    t ∈ qrZeroSumTriples ↔
      t.1 ∈ qrStar ∧ t.2.1 ∈ qrStar ∧ t.2.2 ∈ qrStar ∧ t.1 + t.2.1 + t.2.2 = 0 := by
  simp only [qrZeroSumTriples, Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in
/-- **THE G³-SCALING ASSEMBLY.**  When `−1` is a square and `2 ≠ 0`, the ordered zero-sum
triples of nonzero squares number exactly `#QR* · M` (`M` = the consecutive-QR pairs). -/
theorem qr_zeroSum_ordered_eq (hneg1 : IsSquare (-1 : F)) :
    (qrZeroSumTriples (F := F)).card = (qrStar (F := F)).card * (qrConsec (F := F)).card := by
  classical
  rw [← Finset.card_product]
  refine Finset.card_nbij'
    (fun t => (t.1, t.2.1 / t.1))
    (fun p => (p.1, p.1 * p.2, - p.1 - p.1 * p.2)) ?_ ?_ ?_ ?_
  · -- forward maps into qrStar ×ˢ qrConsec
    intro t ht
    rw [Finset.mem_coe, mem_qrZeroSumTriples] at ht
    obtain ⟨ha, hb, hc, hsum⟩ := ht
    obtain ⟨ha0, ha_sq⟩ := mem_qrStar.mp ha
    obtain ⟨hb0, hb_sq⟩ := mem_qrStar.mp hb
    obtain ⟨hc0, hc_sq⟩ := mem_qrStar.mp hc
    rw [Finset.mem_coe]
    refine Finset.mem_product.mpr ⟨mem_qrStar.mpr ⟨ha0, ha_sq⟩, ?_⟩
    have hba_sq : IsSquare (t.2.1 / t.1) := isSquare_div hb_sq ha_sq
    have hba0 : t.2.1 / t.1 ≠ 0 := div_ne_zero hb0 ha0
    have hkey : t.2.1 / t.1 + 1 = (-t.2.2) / t.1 := by
      rw [eq_div_iff ha0, add_mul, div_mul_cancel₀ _ ha0, one_mul]
      linear_combination hsum
    refine mem_qrConsec.mpr ⟨hba0, hba_sq, ?_, ?_⟩
    · rw [hkey]; exact div_ne_zero (neg_ne_zero.mpr hc0) ha0
    · rw [hkey]; exact isSquare_div (isSquare_neg_of_neg_one hneg1 hc_sq) ha_sq
  · -- inverse maps into qrZeroSumTriples
    intro p hp
    obtain ⟨ha, hu⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hp)
    obtain ⟨ha0, ha_sq⟩ := mem_qrStar.mp ha
    obtain ⟨hu0, hu_sq, hu10, hu1_sq⟩ := mem_qrConsec.mp hu
    rw [Finset.mem_coe, mem_qrZeroSumTriples]
    dsimp only
    refine ⟨mem_qrStar.mpr ⟨ha0, ha_sq⟩, ?_, ?_, by ring⟩
    · exact mem_qrStar.mpr ⟨mul_ne_zero ha0 hu0, ha_sq.mul hu_sq⟩
    · have heq : - p.1 - p.1 * p.2 = -(p.1 * (p.2 + 1)) := by ring
      refine mem_qrStar.mpr ⟨?_, ?_⟩
      · rw [heq]; exact neg_ne_zero.mpr (mul_ne_zero ha0 hu10)
      · rw [heq]; exact isSquare_neg_of_neg_one hneg1 (ha_sq.mul hu1_sq)
  · -- left inverse
    intro t ht
    rw [Finset.mem_coe, mem_qrZeroSumTriples] at ht
    obtain ⟨ha, _, _, hsum⟩ := ht
    have ha0 : t.1 ≠ 0 := (mem_qrStar.mp ha).1
    have hb_eq : t.1 * (t.2.1 / t.1) = t.2.1 := by field_simp
    have hc_eq : - t.1 - t.2.1 = t.2.2 := by linear_combination -hsum
    show (t.1, t.1 * (t.2.1 / t.1), - t.1 - t.1 * (t.2.1 / t.1)) = t
    rw [hb_eq, hc_eq]
  · -- right inverse
    intro p hp
    obtain ⟨ha, _⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hp)
    have ha0 : p.1 ≠ 0 := (mem_qrStar.mp ha).1
    show (p.1, (p.1 * p.2) / p.1) = p
    rw [mul_div_cancel_left₀ _ ha0]

/-- The cardinality identities feeding the closed form: `2·#QR* + 1 = q` and
`4·M + 5 = q`, hence the ordered zero-sum triple count is `((q−1)/2)·((q−5)/4)`. -/
theorem qrStar_card_eq (h2 : (2 : F) ≠ 0) :
    2 * (qrStar (F := F)).card + 1 = Fintype.card F :=
  card_units_squares h2

theorem qrConsec_card_eq (h2 : (2 : F) ≠ 0) (hneg1 : IsSquare (-1 : F)) :
    4 * (qrConsec (F := F)).card + 5 = Fintype.card F :=
  qr_shift_count h2 hneg1

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.qr_zeroSum_ordered_eq

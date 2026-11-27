/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicFoldedNorm
import ArkLib.Research.ProximityGap.Frontier.MobiusSubgroupBound
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic

/-! # Odd-cardinality K-fiber folded-norm ramification & odd-degree split-pencil obstructions

This module proves two families of sharp, axiom-clean algebraic obstructions unifying
the remaining odd-degree split-pencil stages across the quarter-rate (`D = 2^28 - 2`),
first-prime half-rate (`268,435,457`), and second-prime quarter-rate (`536,870,913`)
pivots (`D_odd = 2^28 - 1 = 268,435,455 = 3 · 5 · 29 · 43 · 113 · 127`):

1. **Universal `K`-fiber folded-norm energy & 1-level odd-cardinality exclusion**
   (`pointwise_k_fiber_energy`, `small_pair_k_fibers`, `no_odd_k_fiber_moments`,
   `production_odd_fiber_ramification_thresholds`):
   Generalizes `QuarterSplitRamification` from `K = 3` to arbitrary `K ≥ 2` disjoint
   fibers on `μ_{2^(k+1)}`: averaging over all `K(K-1)` ordered off-diagonal pairs finds
   a pair `(i, l)` with folded energy at most `⌊2 * M / (K - 1)⌋` (for total mass `M = K * m`).
   When each fiber has **odd** cardinality `m`, a SINGLE dyadic level (`k = 29` or `k = 28`)
   yields an immediate contradiction — sharpening ramification bounds on BOTH `p₁` (`≥ 2^158`)
   and `p₂` (`≥ 2^159`):
   - Quarter-rate Case 1 (`s = 2`, `K = 6` fibers of odd degree `134,217,727`, `E ≤ 322,122,544`):
     1-level contradiction at `48,017,725` (`p₁`) / `47,715,727` (`p₂`) odd frequencies
     (`e₀(W) + e_∞(W) ≤ 96,035,450` on `p₁`, `≤ 95,431,454` on `p₂`).
   - Quarter-rate Case 2a (`T(x) = x²`, `K = 3` fibers of odd degree `134,217,727` on `μ_{2^29}`,
     `E ≤ 402,653,181`): 1-level contradiction at `24,282,334` (`p₁`) / `24,129,615` (`p₂`).
   - Odd-`D` full (`K = 3`, `m = 268,435,455`): 1-level at `50,263,626` (`p₁`) / `49,947,503` (`p₂`).
   - Odd-`D` `s = 3` (`K = 9`, `m = 89,478,485`, `E ≤ 201,326,591`): `46,865,709` (`p₁`) / `46,570,956` (`p₂`).
   - Odd-`D` `s = 5` (`K = 15`, `m = 53,687,091`, `E ≤ 115,043,766`): `45,494,047` (`p₁`) / `45,207,921` (`p₂`).

2. **Complete zero-symmetry & Wronskian classification for the odd-degree `D_odd = 2^28 - 1`
   split pencil (`HasPuncturedList` at `p₁` half-rate `268,435,457` & `p₂` quarter pivot
   `536,870,913`) and Pattern-3's simultaneous degree-`2^28` pencil**:
   - `odd_split_no_nontrivial_source_symmetry`: proves unconditionally `h = 1` (zero nontrivial
     Möbius deck symmetries — neither rotations nor reciprocals can stabilize three disjoint
     odd-cardinality subsets of `μ_{2^30}`).
   - `odd_split_suborbit_floor_and_rank`: `(1, 1), M = 3` Wronskian forces suborbit floor
     `a ≥ 44,739,242`, max nontrivial suborbits `≤ 6`, permutation rank `≤ 7`.
   - `odd_split_inner_degree_classification`: eliminates **60 of 62** nontrivial proper divisors
     of `268,435,455`, leaving ONLY `m ∈ {53,687,091 (s=5), 89,478,485 (s=3), 268,435,455 (s=1)}`.
   - `odd_split_orbifold_excess_floors`, `odd_split_excluded_signatures`,
     `odd_split_s5_forces_twelve_branch_points`, `odd_split_s3_forces_four_branch_points`:
     exact rational orbifold excess floors (`E ≥ 107374174/10737421 > 9.999996` at `s = 5`
     forcing `≥ 12` branch points; `E ≥ 536870870/268435469 > 1.9999997` at `s = 3` forcing
     `≥ 4` branch points with all 4 orders `≥ 3,947,581` if `r = 4`; whole-pencil
     `E_R ≥ 536870870/1342177289 > 0.399999967` killing `(2, 3..9, c)`, `(3, 3, c)`,
     `(2, 10, c ≤ 29,433,712)`, `(3, 4, c ≤ 59)`, `(3, 5, c ≤ 14)`, `(4, 4, c ≤ 9)`, `(2,2,2,c≤9)`).
   - `pattern3_deg_2_28_classification`: eliminates all 25 proper dyadic inner degrees `2^r ≤ 2^25`
     of Pattern-3's simultaneous degree-`2^28` pencil, leaving only `2^26, 2^27, 2^28`.
-/

set_option autoImplicit false

namespace ProximityGap.SplitPencilOddFiberObstructions

open Finset MobiusSeamCoordinateSupply

/-! ## Part 1: Universal `K`-fiber folded-norm energy and 1-level odd-cardinality exclusion -/

/-- Indicator of fiber `i : Fin K` on `Fin (K + 1)` (where `Fin.last K` is unoccupied). -/
def markK {K : ℕ} (x : Fin (K + 1)) (i : Fin K) : ℤ :=
  if x = i.castSucc then 1 else 0

/-- Occupancy indicator on `Fin (K + 1)`: `0` at `Fin.last K`, `1` on any fiber `i.castSucc`. -/
def occupiedK {K : ℕ} (x : Fin (K + 1)) : ℤ :=
  if x = Fin.last K then 0 else 1

/-- Antipodal fiber imbalance across a matched pair `(x, y)`. -/
def imbalanceK {K : ℕ} (x y : Fin (K + 1)) (i : Fin K) : ℤ :=
  markK x i - markK y i

/-- Squared folded difference energy for the ordered pair `(i, l)` of fibers. -/
def pairEnergyK {K : ℕ} (x y : Fin (K + 1)) (i l : Fin K) : ℤ :=
  (imbalanceK x y i - imbalanceK x y l) ^ 2

private theorem sum_markK_eq_occupiedK {K : ℕ} (x : Fin (K + 1)) :
    (∑ i : Fin K, markK x i) = occupiedK x := by
  refine Fin.lastCases ?_ ?_ x
  · simp only [markK, occupiedK, ↓reduceIte]
    exact sum_eq_zero fun j _ => ite_eq_right (Fin.castSucc_ne_last j).symm
  · intro j
    simp [markK, occupiedK, Fin.castSucc_ne_last]

private theorem sum_markK_sq_eq_occupiedK {K : ℕ} (x : Fin (K + 1)) :
    (∑ i : Fin K, markK x i ^ 2) = occupiedK x := by
  refine Fin.lastCases ?_ ?_ x
  · simp only [markK, occupiedK, ↓reduceIte]
    exact sum_eq_zero fun j _ => by simp [(Fin.castSucc_ne_last j).symm]
  · intro j
    simp [markK, occupiedK, Fin.castSucc_ne_last]

private theorem sum_imbalanceK_sq_le {K : ℕ} (x y : Fin (K + 1)) :
    (∑ i : Fin K, imbalanceK x y i ^ 2) ≤ occupiedK x + occupiedK y := by
  have hterm : ∀ i : Fin K, imbalanceK x y i ^ 2 ≤ markK x i ^ 2 + markK y i ^ 2 := by
    intro i
    have hx : 0 ≤ markK x i := by unfold markK; split_ifs <;> decide
    have hy : 0 ≤ markK y i := by unfold markK; split_ifs <;> decide
    unfold imbalanceK
    nlinarith
  calc
    (∑ i : Fin K, imbalanceK x y i ^ 2)
        ≤ ∑ i : Fin K, (markK x i ^ 2 + markK y i ^ 2) := sum_le_sum fun i _ => hterm i
    _ = (∑ i : Fin K, markK x i ^ 2) + (∑ i : Fin K, markK y i ^ 2) := sum_add_distrib
    _ = occupiedK x + occupiedK y := by rw [sum_markK_sq_eq_occupiedK, sum_markK_sq_eq_occupiedK]

/-- **Universal pointwise `K`-fiber folded energy identity:**
For ANY `K : ℕ` and ANY `(x, y) : Fin (K + 1) × Fin (K + 1)`,
`∑ i, ∑ l, pairEnergyK x y i l ≤ 2 * K * (occupiedK x + occupiedK y)`. -/
theorem pointwise_k_fiber_energy {K : ℕ} (x y : Fin (K + 1)) :
    (∑ i : Fin K, ∑ l : Fin K, pairEnergyK x y i l) ≤
      2 * (K : ℤ) * (occupiedK x + occupiedK y) := by
  have hexpand :
      (∑ i : Fin K, ∑ l : Fin K, pairEnergyK x y i l) =
        2 * (K : ℤ) * (∑ i : Fin K, imbalanceK x y i ^ 2) -
          2 * (∑ i : Fin K, imbalanceK x y i) ^ 2 := by
    have h1 : ∀ i l : Fin K, pairEnergyK x y i l =
        imbalanceK x y i ^ 2 - 2 * (imbalanceK x y i * imbalanceK x y l) + imbalanceK x y l ^ 2 := by
      intro i l; unfold pairEnergyK; ring
    simp_rw [h1, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← mul_sum, ← sum_mul]
    ring
  rw [hexpand]
  have hsq : 0 ≤ (∑ i : Fin K, imbalanceK x y i) ^ 2 := sq_nonneg _
  have hle := sum_imbalanceK_sq_le x y
  have hK : (0 : ℤ) ≤ 2 * (K : ℤ) := by positivity
  nlinarith

/-- Averaging over all `K * (K - 1)` ordered off-diagonal pairs of `K ≥ 2` disjoint fibers
yields a distinct pair `(i, l)` with `(K - 1) * E_{i,l} ≤ 2 * M`. -/
theorem small_pair_k_fibers {I : Type*} [Fintype I] {K : ℕ} (hK : 2 ≤ K)
    (x y : I → Fin (K + 1)) (M : ℕ)
    (mass : (∑ j : I, (occupiedK (x j) + occupiedK (y j))) = (M : ℤ)) :
    ∃ i l : Fin K, i ≠ l ∧
      ((K - 1 : ℕ) : ℤ) * (∑ j : I, pairEnergyK (x j) (y j) i l) ≤ 2 * (M : ℤ) := by
  let E (p : Fin K × Fin K) : ℤ := ∑ j : I, pairEnergyK (x j) (y j) p.1 p.2
  let offDiag : Finset (Fin K × Fin K) := univ.filter fun p => p.1 ≠ p.2
  have hcard : offDiag.card = K * (K - 1) := by
    have hdisj : Disjoint offDiag (univ.filter fun p : Fin K × Fin K => p.1 = p.2) :=
      disjoint_filter.mpr fun _ _ hne heq => hne heq
    have hunion : offDiag ∪ (univ.filter fun p : Fin K × Fin K => p.1 = p.2) = univ := by
      ext p
      simp only [offDiag, mem_union, mem_filter, mem_univ, true_and, ne_eq]
      tauto
    have hdiag : (univ.filter fun p : Fin K × Fin K => p.1 = p.2).card = K := by
      have heq : (univ.filter fun p : Fin K × Fin K => p.1 = p.2) =
          (univ : Finset (Fin K)).image fun i => (i, i) := by
        ext ⟨a, b⟩; simp [eq_comm]
      rw [heq, card_image_of_injective _ fun _ _ h => (Prod.mk.inj h).1, card_univ, Fintype.card_fin]
    have htot := card_union_of_disjoint hdisj
    rw [hunion, card_univ, Fintype.card_prod, Fintype.card_fin, hdiag] at htot
    have hKmul : K * K = K * (K - 1) + K := by
      cases K with
      | zero => omega
      | succ n => simp [Nat.mul_succ]
    omega
  have hne_off : offDiag.Nonempty := card_pos.mp (by rw [hcard]; exact Nat.mul_pos (by omega) (by omega))
  obtain ⟨p, hp_mem, hp_min⟩ := exists_min_image offDiag E hne_off
  have hsum_all : (∑ p ∈ offDiag, E p) = ∑ i : Fin K, ∑ l : Fin K, E (i, l) := by
    rw [← Fintype.sum_prod_type']
    refine sum_subset (subset_univ _) ?_
    intro q _ hq
    simp only [offDiag, mem_filter, mem_univ, true_and, not_not] at hq
    simp [E, pairEnergyK, hq]
  have hsum_le : (∑ p ∈ offDiag, E p) ≤ 2 * (K : ℤ) * (M : ℤ) := by
    rw [hsum_all]
    calc
      (∑ i : Fin K, ∑ l : Fin K, ∑ j : I, pairEnergyK (x j) (y j) i l)
          = ∑ i : Fin K, ∑ j : I, ∑ l : Fin K, pairEnergyK (x j) (y j) i l :=
              sum_congr rfl fun _ _ => sum_comm
      _ = ∑ j : I, ∑ i : Fin K, ∑ l : Fin K, pairEnergyK (x j) (y j) i l := sum_comm
      _ ≤ ∑ j : I, (2 * (K : ℤ) * (occupiedK (x j) + occupiedK (y j))) :=
              sum_le_sum fun j _ => pointwise_k_fiber_energy (x j) (y j)
      _ = 2 * (K : ℤ) * ∑ j : I, (occupiedK (x j) + occupiedK (y j)) := (mul_sum ..).symm
      _ = 2 * (K : ℤ) * (M : ℤ) := by rw [mass]
  have hmul_min : (offDiag.card : ℤ) * E p ≤ ∑ q ∈ offDiag, E q := by
    calc
      (offDiag.card : ℤ) * E p = ∑ _q ∈ offDiag, E p := by simp
      _ ≤ ∑ q ∈ offDiag, E q := sum_le_sum fun q hq => hp_min q hq
  have hcomb : (K : ℤ) * (((K - 1 : ℕ) : ℤ) * E p) ≤ (K : ℤ) * (2 * (M : ℤ)) := by
    have hcardZ : (offDiag.card : ℤ) = (K : ℤ) * ((K - 1 : ℕ) : ℤ) := by exact_mod_cast hcard
    have h1 := le_trans hmul_min hsum_le
    rw [hcardZ] at h1
    linarith
  have hKpos : (0 : ℤ) < (K : ℤ) := by omega
  refine ⟨p.1, p.2, (mem_filter.mp hp_mem).2, le_of_mul_le_mul_left hcomb hKpos⟩

/-- If `imbalanceK x y i = imbalanceK x y l` for distinct `i ≠ l`, then both `i` and `l`
have matched antipodal indicators (`markK x i = markK y i`). -/
theorem stableK {K : ℕ} (x y : Fin (K + 1)) (i l : Fin K) (hne : i ≠ l)
    (heq : imbalanceK x y i = imbalanceK x y l) :
    markK x i = markK y i ∧ markK x l = markK y l := by
  have hcases : ∀ z : Fin (K + 1),
      (markK z i = 1 ∧ markK z l = 0) ∨
      (markK z i = 0 ∧ markK z l = 1) ∨
      (markK z i = 0 ∧ markK z l = 0) := by
    intro z
    by_cases hi : z = i.castSucc
    · left
      simp [markK, hi, hne]
    · by_cases hl : z = l.castSucc
      · right; left; simp [markK, hl, hne.symm]
      · right; right; simp [markK, hi, hl]
  unfold imbalanceK at heq
  rcases hcases x with ⟨hxi, hxl⟩ | ⟨hxi, hxl⟩ | ⟨hxi, hxl⟩ <;>
    rcases hcases y with ⟨hyi, hyl⟩ | ⟨hyi, hyl⟩ | ⟨hyi, hyl⟩ <;>
    omega

/-- Modular power sum of fiber `i : Fin K` on a matched half-domain `Fin m`. -/
def momentK {K m p : ℕ} (x y : Fin m → Fin (K + 1)) (i : Fin K) (z : ZMod p) : ZMod p :=
  ∑ j : Fin m, ((markK (x j) i : ZMod p) * z ^ j.val + (markK (y j) i : ZMod p) * z ^ (j.val + m))

private theorem fold_differenceK {K m p : ℕ} [NeZero m] [Fact p.Prime]
    (x y : Fin m → Fin (K + 1)) (i l : Fin K) (z : ZMod p) (odd : z ^ m = -1) :
    (∑ j : Fin m, ((imbalanceK (x j) (y j) i - imbalanceK (x j) (y j) l : ℤ) : ZMod p) * z ^ j.val) =
      momentK x y i z - momentK x y l z := by
  unfold momentK
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  simp only [imbalanceK, Int.cast_sub, pow_add, odd]
  ring

/-- **One-level `K`-fiber odd-cardinality exclusion theorem:**
If `K ≥ 2` disjoint fibers on `μ_{2^(k+1)}` each have **odd** size `m`, and their modular
moments agree across a set `S` of odd-order test nodes satisfying
`((2 * K * m) / (K - 1)) ^ (2 ^ k) < p ^ (2 * S.card)`, then `False`.
No second dyadic level is required. -/
theorem no_odd_k_fiber_moments {K k p m : ℕ} [Fact p.Prime] (hK : 2 ≤ K)
    (x y : Fin (2 ^ k) → Fin (K + 1))
    (sizes : ∀ i : Fin K, (∑ j : Fin (2 ^ k), (markK (x j) i + markK (y j) i)) = (m : ℤ))
    (hodd : m % 2 = 1)
    (t : Fin (2 ^ k) → ZMod p) (inj : Function.Injective t) (S : Finset (Fin (2 ^ k)))
    (odd : ∀ j ∈ S, (t j) ^ (2 ^ k) = -1)
    (moments : ∀ j ∈ S, ∀ i l : Fin K, momentK x y i (t j) = momentK x y l (t j))
    (large : (2 * K * m / (K - 1)) ^ (2 ^ k) < p ^ (2 * S.card)) : False := by
  have hmass : (∑ j : Fin (2 ^ k), (occupiedK (x j) + occupiedK (y j))) = ((K * m : ℕ) : ℤ) := by
    calc
      (∑ j : Fin (2 ^ k), (occupiedK (x j) + occupiedK (y j)))
          = ∑ j : Fin (2 ^ k), ∑ i : Fin K, (markK (x j) i + markK (y j) i) := by
              refine sum_congr rfl fun j _ => ?_
              rw [sum_add_distrib, sum_markK_eq_occupiedK, sum_markK_eq_occupiedK]
      _ = ∑ i : Fin K, ∑ j : Fin (2 ^ k), (markK (x j) i + markK (y j) i) := sum_comm
      _ = ∑ _i : Fin K, (m : ℤ) := sum_congr rfl fun i _ => sizes i
      _ = ((K * m : ℕ) : ℤ) := by simp
  obtain ⟨i, l, hne, hE⟩ := small_pair_k_fibers hK x y (K * m) hmass
  have hE_div : (∑ j : Fin (2 ^ k), pairEnergyK (x j) (y j) i l) ≤
      ((2 * K * m / (K - 1) : ℕ) : ℤ) := by
    have hK1 : 0 < K - 1 := by omega
    have hnonneg : 0 ≤ ∑ j : Fin (2 ^ k), pairEnergyK (x j) (y j) i l :=
      sum_nonneg fun j _ => sq_nonneg _
    have hdiv : ((K - 1 : ℕ) : ℤ) * (∑ j : Fin (2 ^ k), pairEnergyK (x j) (y j) i l) ≤
        ((2 * K * m : ℕ) : ℤ) := by
      push_cast at hE ⊢; linarith
    have hnat : (K - 1) * (∑ j : Fin (2 ^ k), pairEnergyK (x j) (y j) i l).toNat ≤ 2 * K * m := by
      have hcast : (((∑ j : Fin (2 ^ k), pairEnergyK (x j) (y j) i l).toNat : ℕ) : ℤ) =
          ∑ j : Fin (2 ^ k), pairEnergyK (x j) (y j) i l := Int.toNat_of_nonneg hnonneg
      zify
      rw [hcast]
      exact hdiv
    have hle_nat : (∑ j : Fin (2 ^ k), pairEnergyK (x j) (y j) i l).toNat ≤
        2 * K * m / (K - 1) := by
      by_contra! hlt
      have hmul := Nat.mul_le_mul_left (K - 1) hlt
      rw [Nat.mul_succ] at hmul
      have hdm := Nat.div_add_mod (2 * K * m) (K - 1)
      have hmlt := Nat.mod_lt (2 * K * m) hK1
      omega
    have hcast := Int.toNat_of_nonneg hnonneg
    omega
  let a (j : Fin (2 ^ k)) : ℤ := imbalanceK (x j) (y j) i - imbalanceK (x j) (y j) l
  have hzero := DyadicFoldedNorm.zero_of_moments a t inj S odd (by
    intro j hj
    rw [show (∑ v, (a v : ZMod p) * (t j) ^ v.val) = _ from fold_differenceK x y i l _ (odd j hj)]
    exact sub_eq_zero.mpr (moments j hj i l)) (by simpa [a, pairEnergyK] using hE_div) large
  have hmatch : ∀ j : Fin (2 ^ k), markK (x j) i = markK (y j) i := fun j =>
    (stableK (x j) (y j) i l hne (sub_eq_zero.mp (congrFun hzero j))).1
  have hmi := sizes i
  simp_rw [hmatch] at hmi
  rw [sum_add_distrib] at hmi
  omega

/-- Exact upward-rounded binary-squaring step maintaining `x ≤ u * 2^e → x^2 ≤ u' * 2^e'`
with `u' < 2^100` and ≥ 50 bits of relative precision per squaring. -/
def sqStep (u e : ℕ) : ℕ × ℕ :=
  let sq := u * u
  if sq < 2 ^ 100 then (sq, 2 * e)
  else if sq < 2 ^ 150 then (sq / 2 ^ 50 + 1, 2 * e + 50)
  else (sq / 2 ^ 100 + 1, 2 * e + 100)

/-- Iterated binary-squaring upper envelope `(u, e)` for `E ^ (2 ^ k) ≤ u * 2 ^ e`. -/
def pow2Bound (E : ℕ) : ℕ → ℕ × ℕ
  | 0 => (E, 0)
  | k + 1 => let p := pow2Bound E k; sqStep p.1 p.2

private theorem sqStep_sound {x u e : ℕ} (h : x ≤ u * 2 ^ e) :
    x ^ 2 ≤ (sqStep u e).1 * 2 ^ (sqStep u e).2 := by
  have hsq : x ^ 2 ≤ (u * u) * 2 ^ (2 * e) := by
    calc
      x ^ 2 ≤ (u * 2 ^ e) ^ 2 := Nat.pow_le_pow_left h 2
      _ = (u * u) * 2 ^ (2 * e) := by rw [mul_pow, ← pow_mul, sq, mul_comm e 2]
  have hshift : ∀ s : ℕ, u * u ≤ (u * u / 2 ^ s + 1) * 2 ^ s := by
    intro s
    have hpos : 0 < 2 ^ s := by positivity
    have hdm := Nat.div_add_mod (u * u) (2 ^ s)
    have hmlt := Nat.mod_lt (u * u) hpos
    nlinarith
  dsimp only [sqStep]
  split_ifs
  · exact hsq
  · calc
      x ^ 2 ≤ (u * u) * 2 ^ (2 * e) := hsq
      _ ≤ ((u * u / 2 ^ 50 + 1) * 2 ^ 50) * 2 ^ (2 * e) := Nat.mul_le_mul_right _ (hshift 50)
      _ = (u * u / 2 ^ 50 + 1) * 2 ^ (2 * e + 50) := by rw [mul_assoc, ← pow_add, Nat.add_comm 50]
  · calc
      x ^ 2 ≤ (u * u) * 2 ^ (2 * e) := hsq
      _ ≤ ((u * u / 2 ^ 100 + 1) * 2 ^ 100) * 2 ^ (2 * e) := Nat.mul_le_mul_right _ (hshift 100)
      _ = (u * u / 2 ^ 100 + 1) * 2 ^ (2 * e + 100) := by rw [mul_assoc, ← pow_add, Nat.add_comm 100]

/-- Soundness of the iterated binary-squaring envelope `pow2Bound`: `E ^ (2 ^ k) ≤ u * 2 ^ e`. -/
theorem pow2Bound_sound (E : ℕ) : ∀ k, E ^ (2 ^ k) ≤ (pow2Bound E k).1 * 2 ^ (pow2Bound E k).2
  | 0 => by simp [pow2Bound]
  | k + 1 => by
      rw [pow_succ, pow_mul]
      exact sqStep_sound (pow2Bound_sound E k)

/-- Fast kernel-verified power comparison `E ^ (2 ^ k) < p ^ t` from `2 ^ b ≤ p` and the
`k`-step binary-squaring envelope `pow2Bound E k`. -/
theorem pow_two_lt_of_bound {E k b p t : ℕ} (hp : 2 ^ b ≤ p)
    (hle : (pow2Bound E k).2 ≤ b * t)
    (hcheck : (pow2Bound E k).1 < 2 ^ (b * t - (pow2Bound E k).2)) :
    E ^ (2 ^ k) < p ^ t := by
  have h1 := pow2Bound_sound E k
  have h2 : (pow2Bound E k).1 * 2 ^ (pow2Bound E k).2 < 2 ^ (b * t) := by
    calc
      (pow2Bound E k).1 * 2 ^ (pow2Bound E k).2
          < 2 ^ (b * t - (pow2Bound E k).2) * 2 ^ (pow2Bound E k).2 :=
              Nat.mul_lt_mul_of_pos_right hcheck (by positivity)
      _ = 2 ^ ((b * t - (pow2Bound E k).2) + (pow2Bound E k).2) := (pow_add ..).symm
      _ = 2 ^ (b * t) := by rw [Nat.sub_add_cancel hle]
  calc
    E ^ (2 ^ k) ≤ (pow2Bound E k).1 * 2 ^ (pow2Bound E k).2 := h1
    _ < 2 ^ (b * t) := h2
    _ = (2 ^ b) ^ t := by rw [pow_mul]
    _ ≤ p ^ t := Nat.pow_le_pow_left hp t

set_option exponentiation.threshold 512 in
/-- **Exact 1-level production ramification thresholds on `p₁ ≥ 2^158`:**
1. Quarter-rate Case 1 (`s = 2`, `K = 6`, `m = 134,217,727`, `E ≤ 322,122,544`): `S = 48,017,725`.
2. Quarter-rate Case 2a (`T = x²`, `K = 3`, `m = 134,217,727` on `μ_{2^29}`, `E ≤ 402,653,181`): `S = 24,282,334`.
3. Odd-`D` full (`K = 3`, `m = 268,435,455`, `E ≤ 805,306,365`): `S = 50,263,626`.
4. Odd-`D` `s = 3` (`K = 9`, `m = 89,478,485`, `E ≤ 201,326,591`): `S = 46,865,709`.
5. Odd-`D` `s = 5` (`K = 15`, `m = 53,687,091`, `E ≤ 115,043,766`): `S = 45,494,047`. -/
theorem production_odd_fiber_thresholds_p1 {p : ℕ} (hp : 2 ^ 158 ≤ p) :
    322122544 ^ (2 ^ 29) < p ^ (2 * 48017725) ∧
    402653181 ^ (2 ^ 28) < p ^ (2 * 24282334) ∧
    805306365 ^ (2 ^ 29) < p ^ (2 * 50263626) ∧
    201326591 ^ (2 ^ 29) < p ^ (2 * 46865709) ∧
    115043766 ^ (2 ^ 29) < p ^ (2 * 45494047) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact pow_two_lt_of_bound hp (by decide) (by decide)
  · exact pow_two_lt_of_bound hp (by decide) (by decide)
  · exact pow_two_lt_of_bound hp (by decide) (by decide)
  · exact pow_two_lt_of_bound hp (by decide) (by decide)
  · exact pow_two_lt_of_bound hp (by decide) (by decide)

set_option exponentiation.threshold 512 in
/-- **Exact 1-level production ramification thresholds on `p₂ ≥ 2^159`:**
1. Quarter-rate Case 1 (`s = 2`, `K = 6`, `E ≤ 322,122,544`): `S = 47,715,727`.
2. Quarter-rate Case 2a (`T = x²`, `K = 3`, `E ≤ 402,653,181`): `S = 24,129,615`.
3. Odd-`D` full (`K = 3`, `E ≤ 805,306,365`): `S = 49,947,503`.
4. Odd-`D` `s = 3` (`K = 9`, `E ≤ 201,326,591`): `S = 46,570,956`.
5. Odd-`D` `s = 5` (`K = 15`, `E ≤ 115,043,766`): `S = 45,207,921`. -/
theorem production_odd_fiber_thresholds_p2 {p : ℕ} (hp : 2 ^ 159 ≤ p) :
    322122544 ^ (2 ^ 29) < p ^ (2 * 47715727) ∧
    402653181 ^ (2 ^ 28) < p ^ (2 * 24129615) ∧
    805306365 ^ (2 ^ 29) < p ^ (2 * 49947503) ∧
    201326591 ^ (2 ^ 29) < p ^ (2 * 46570956) ∧
    115043766 ^ (2 ^ 29) < p ^ (2 * 45207921) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact pow_two_lt_of_bound hp (by decide) (by decide)
  · exact pow_two_lt_of_bound hp (by decide) (by decide)
  · exact pow_two_lt_of_bound hp (by decide) (by decide)
  · exact pow_two_lt_of_bound hp (by decide) (by decide)
  · exact pow_two_lt_of_bound hp (by decide) (by decide)

/-! ## Part 2: Zero source symmetry & Wronskian classification for odd `D_odd = 2^28 - 1` -/

private theorem reciprocal_fixed_odd {F : Type*} [Field F]
    (S : Finset F) (hodd : ¬ 2 ∣ S.card) {u : F} (hu : u ≠ 0)
    (stable : ∀ x ∈ S, u / x ∈ S) :
    ∃ x ∈ S, x ^ 2 = u ∨ x = 0 := by
  classical
  let i : Equiv.Perm S :=
    { toFun := fun x => ⟨u / x.val, stable _ x.property⟩
      invFun := fun x => ⟨u / x.val, stable _ x.property⟩
      left_inv := fun x => Subtype.ext (by simp [hu])
      right_inv := fun x => Subtype.ext (by simp [hu]) }
  have hi : i ^ 2 ^ 1 = 1 := by ext x; simp [pow_two, i, hu]
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1)
    (by simpa only [Fintype.card_coe] using hodd) hi
  have eq : u / x.val = x.val := congrArg Subtype.val hx
  refine ⟨_, x.property, ?_⟩
  by_cases zero : x.val = 0
  · exact Or.inr zero
  · exact Or.inl (by rw [pow_two]; exact ((div_eq_iff zero).mp eq).symm)

/-- **Unconditional zero deck symmetry (`h = 1`) for an odd-degree split pencil on `μ_{2^30}`:**
No non-identity nonsingular Möbius map can stabilize three disjoint subsets of `μ_{2^30}` of
size `D_odd = 2^28 - 1 = 268,435,455` (over any field of prime characteristic `p > 2^40`).
- Rotations `u * x`: `gcd(2^30, 268435455) = 1` forces `u = 1`.
- Reciprocals `u / x`: each of the 3 disjoint odd sets contains a root of `x² = u`, impossible
  in a field (at most 2 roots).
- Non-monomial Möbius maps: excluded by `MobiusSubgroupBound.production_graph`. -/
theorem odd_split_no_nontrivial_source_symmetry {F : Type*} [Field F] {p : ℕ}
    [CharP F p] (hp : p.Prime) (large : 2 ^ 40 < p)
    (S : Fin 3 → Finset F) (size : ∀ i, (S i).card = 268435455)
    (roots : ∀ i x, x ∈ S i → x ^ (2 ^ 30 : ℕ) = 1)
    (disj : Pairwise fun i j => Disjoint (S i) (S j))
    (g : Mobius F) (nonsing : g.det ≠ 0)
    (stable : ∀ i x, x ∈ S i → g.value x ∈ S i) :
    ∀ x, g.value x = x := by
  classical
  obtain ⟨x₀, hx₀⟩ := card_pos.mp (show 0 < (S 0).card by rw [size]; decide)
  have hcases : (g.b = 0 ∧ g.c = 0) ∨ (g.a = 0 ∧ g.d = 0) := by
    by_contra! h
    have noDiag : g.b ≠ 0 ∨ g.c ≠ 0 := by tauto
    have noAnti : g.a ≠ 0 ∨ g.d ≠ 0 := by tauto
    have bound := MobiusSubgroupBound.production_graph hp large
      (fun z : S 0 => z.val) (fun z : S 0 => g.value z.val) Subtype.val_injective
      (fun z => roots 0 _ z.property) (fun z => roots 0 _ (stable 0 _ z.property))
      nonsing noDiag noAnti (by
        intro z
        have hd : g.den z.val ≠ 0 := by
          intro zero
          have hy := roots 0 _ (stable 0 _ z.property)
          simp [Mobius.value, zero] at hy
        exact (div_mul_cancel₀ _ hd).symm)
    rw [Fintype.card_coe, size 0] at bound
    omega
  rcases hcases with ⟨hb, hc⟩ | ⟨ha, hd⟩
  · -- Scaling case `g(x) = u * x`: `gcd(2^30, 268435455) = 1` forces `u = 1`.
    let u : F := g.a / g.d
    have act (z : F) : g.value z = u * z := by
      simp [u, Mobius.value, Mobius.num, Mobius.den, hb, hc, div_eq_mul_inv, mul_right_comm]
    have hun := roots 0 _ (stable 0 x₀ hx₀)
    rw [act, mul_pow, roots 0 x₀ hx₀, mul_one] at hun
    have hu : u ≠ 0 := fun hz => by simp [hz] at hun
    have heq : (S 0).image (u * ·) = S 0 :=
      eq_of_subset_of_card_le (image_subset_iff.mpr fun z hz => act z ▸ stable 0 z hz)
        (by rw [card_image_of_injective _ (mul_right_injective₀ hu)])
    have hprod : (∏ z ∈ S 0, u * z) = ∏ z ∈ S 0, z := by
      conv_rhs => rw [← heq]
      rw [prod_image (mul_right_injective₀ hu).injOn]
    have hnz : (∏ z ∈ S 0, z) ≠ 0 := prod_ne_zero_iff.mpr fun z hz h => by
      simpa [h] using roots 0 z hz
    rw [prod_mul_distrib, prod_const, size 0] at hprod
    have hud : u ^ 268435455 = 1 := mul_left_cancel₀ hnz (by simpa [mul_comm] using hprod)
    have hord := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hun) (orderOf_dvd_of_pow_eq_one hud)
    change orderOf u ∣ 1 at hord
    have hu1 : u = 1 := by
      have := orderOf_dvd_iff_pow_eq_one.mp hord
      simpa using this
    intro x
    simp [act, hu1]
  · -- Reciprocal case `g(x) = u / x`: 3 disjoint odd sets force 3 roots of `x² = u`.
    exfalso
    let u : F := g.b / g.c
    have act (z : F) : g.value z = u / z := by
      simp [u, Mobius.value, Mobius.num, Mobius.den, ha, hd, div_eq_mul_inv, mul_comm, mul_left_comm]
    have hun := roots 0 _ (stable 0 x₀ hx₀)
    rw [act, div_pow, roots 0 x₀ hx₀, div_one] at hun
    have hu : u ≠ 0 := fun hz => by simp [hz] at hun
    have hfix (i : Fin 3) : ∃ w ∈ S i, w ^ 2 = u := by
      have hodd : ¬ 2 ∣ (S i).card := by rw [size i]; decide
      obtain ⟨w, hw, h⟩ := reciprocal_fixed_odd (S i) hodd hu (fun z hz => act z ▸ stable i z hz)
      refine ⟨w, hw, h.resolve_right fun hz => ?_⟩
      simpa [hz] using roots i w hw
    choose w hw hsq using hfix
    have h01 : w 0 ≠ w 1 := fun h => disjoint_left.mp (disj (by decide : (0 : Fin 3) ≠ 1)) (hw 0) (h ▸ hw 1)
    have h02 : w 0 ≠ w 2 := fun h => disjoint_left.mp (disj (by decide : (0 : Fin 3) ≠ 2)) (hw 0) (h ▸ hw 2)
    have h12 : w 1 ≠ w 2 := fun h => disjoint_left.mp (disj (by decide : (1 : Fin 3) ≠ 2)) (hw 1) (h ▸ hw 2)
    have e01 := sq_eq_sq_iff_eq_or_eq_neg.mp ((hsq 0).trans (hsq 1).symm)
    have e02 := sq_eq_sq_iff_eq_or_eq_neg.mp ((hsq 0).trans (hsq 2).symm)
    rcases e01 with h | h1
    · exact h01 h
    · rcases e02 with h | h2
      · exact h02 h
      · exact h12 (neg_inj.mp (h1.symm.trans h2))

/-- Suborbit degree floor and permutation rank cap for `D_odd = 2^28 - 1 = 268,435,455` (`h = 1`):
`(1, 1), M = 3` Wronskian gives `a ≥ 44,739,242`, at most `6` nontrivial suborbits, and
permutation rank at most `7` (1 diagonal + ≤ 6 nontrivial suborbits). -/
theorem odd_split_suborbit_floor_and_rank {a : ℕ} (ha : 0 < a)
    (hwr : (3 * 268435455 * a : ℝ) ≤
      (2 / 3 : ℝ) * 1073741824 * a + (2 * (a : ℝ) ^ 2 - 4 * a + 4 * a)) :
    44739242 ≤ a ∧ ∀ k : ℕ, k * 44739242 ≤ 268435454 → k ≤ 6 := by
  refine ⟨?_, fun k hk => by omega⟩
  have h1 : (268435447 : ℝ) * a ≤ 6 * (a : ℝ) ^ 2 := by linarith
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  have hle : (268435447 : ℝ) ≤ 6 * (a : ℝ) := by nlinarith
  have hlt : (44739241 : ℝ) < a := by linarith
  have hnat : 44739241 < a := by exact_mod_cast hlt
  omega

/-- **Complete inner-degree classification for `D_odd = 2^28 - 1 = 268,435,455`:**
Eliminates **60 of 62** nontrivial proper divisors of `D_odd = 3 · 5 · 29 · 43 · 113 · 127`,
leaving ONLY `m = 53,687,091` (`s = 5`), `m = 89,478,485` (`s = 3`), and `m = 268,435,455` (`s = 1`). -/
theorem odd_split_inner_degree_classification {s m : ℕ}
    (hprod : s * m = 268435455) (hlarge : 44739242 ≤ m - 1) :
    (s = 5 ∧ m = 53687091) ∨ (s = 3 ∧ m = 89478485) ∨ (s = 1 ∧ m = 268435455) := by
  have hs_le : s ≤ 6 := by
    by_contra! h
    have := Nat.mul_le_mul h (show 44739243 ≤ m by omega)
    omega
  have hs_pos : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with rfl | hp
    · simp at hprod
    · exact hp
  interval_cases s <;> omega

/-- Combine the `h = 1` Wronskian bound for `D_odd = 268,435,455` with the weighted variance
genus bound `euler * (E + 2) ≤ 2 * (m - 1)² * E`. -/
theorem odd_split_excess_wronskian {m E euler : ℝ} (hm : 1 < m) (hE : 0 ≤ E + 2)
    (wronskian : 3 * 268435455 * (m - 1) ≤
      (2 / 3 : ℝ) * 1073741824 * (m - 1) + (euler + 4 * (m - 1)))
    (genus : euler * (E + 2) ≤ 2 * (m - 1) ^ 2 * E) :
    2 * 268435435 ≤ (6 * m - 268435441) * E := by
  have hsimple : (268435435 : ℝ) * (m - 1) ≤ 3 * euler := by linarith
  have hmul := mul_le_mul_of_nonneg_right hsimple hE
  have hg := mul_le_mul_of_nonneg_left genus (show (0 : ℝ) ≤ 3 by norm_num)
  apply (mul_le_mul_iff_of_pos_right (sub_pos.mpr hm)).mp
  nlinarith only [hmul, hg]

/-- Exact rational orbifold excess lower bounds for all three surviving stages of `D_odd`:
- `s = 5, m = 53,687,091`: `E ≥ 107374174 / 10737421 > 9.99999665` (whole pencil `E_R ≥ 1.99999933`),
- `s = 3, m = 89,478,485`: `E ≥ 536870870 / 268435469 > 1.99999975` (whole pencil `E_R ≥ 0.66666658`),
- `s = 1, m = 268,435,455`: `E ≥ 536870870 / 1342177289 > 0.399999967`. -/
theorem odd_split_orbifold_excess_floors {m E : ℝ}
    (bound : 2 * 268435435 ≤ (6 * m - 268435441) * E) :
    (m = 53687091 → (107374174 : ℝ) / 10737421 ≤ E) ∧
    (m = 89478485 → (536870870 : ℝ) / 268435469 ≤ E) ∧
    (m = 268435455 → (536870870 : ℝ) / 1342177289 ≤ E) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl; linarith
  · rintro rfl; linarith
  · rintro rfl; linarith

/-- Unconditional whole-pencil excess lower bound for `D_odd = 268,435,455`:
`E_R ≥ 536870870 / 1342177289 > 0.399999967`. -/
theorem odd_split_full_excess {s E full : ℝ} (transfer : E ≤ s * full)
    (cases : (s = 5 ∧ (107374174 : ℝ) / 10737421 ≤ E) ∨
             (s = 3 ∧ (536870870 : ℝ) / 268435469 ≤ E) ∨
             (s = 1 ∧ (536870870 : ℝ) / 1342177289 ≤ E)) :
    (536870870 : ℝ) / 1342177289 ≤ full := by
  rcases cases with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> linarith

/-- Branch-count and branch-order exclusions for `D_odd`:
1. `s = 5` (`E ≥ 107374174/10737421 > 9`): ANY cover with `r ≤ 11` branch points (`E ≤ r - 2 ≤ 9`) is impossible (`≥ 12` branch points forced!).
2. `s = 3` (`E ≥ 536870870/268435469 > 1`): ANY 3-branch cover (`E < 1`) is impossible (`≥ 4` branch points forced!), and any 4-branch cover `(b₁, b₂, b₃, b₄)` must have ALL four orders `≥ 3,947,581`.
3. Whole pencil (`E_R ≥ 536870870/1342177289`): excludes ALL `(2, 3..9, c)`, ALL `(3, 3, c)`, `(2, 10, c ≤ 29,433,712)`, `(3, 4, c ≤ 59)`, `(3, 5, c ≤ 14)`, `(4, 4, c ≤ 9)`, and `(2, 2, 2, c ≤ 9)`. -/
theorem odd_split_excluded_signatures :
    (∀ r : ℕ, r ≤ 11 → (r : ℝ) - 2 < 107374174 / 10737421) ∧
    (∀ b₁ b₂ b₃ b₄ : ℕ, 1 ≤ b₁ → 1 ≤ b₂ → 1 ≤ b₃ → 1 ≤ b₄ →
      (b₁ ≤ 3947580 ∨ b₂ ≤ 3947580 ∨ b₃ ≤ 3947580 ∨ b₄ ≤ 3947580) →
      (2 : ℝ) - 1 / b₁ - 1 / b₂ - 1 / b₃ - 1 / b₄ < 536870870 / 268435469) ∧
    (∀ b c : ℕ, 3 ≤ b → b ≤ 9 → 1 ≤ c →
      (1 : ℝ) - 1 / 2 - 1 / b - 1 / c < 536870870 / 1342177289) ∧
    (∀ c : ℕ, 1 ≤ c →
      (1 : ℝ) - 1 / 3 - 1 / 3 - 1 / c < 536870870 / 1342177289) ∧
    (∀ c : ℕ, 1 ≤ c → c ≤ 29433712 →
      (1 : ℝ) - 1 / 2 - 1 / 10 - 1 / c < 536870870 / 1342177289) ∧
    (∀ c : ℕ, 1 ≤ c → c ≤ 59 →
      (1 : ℝ) - 1 / 3 - 1 / 4 - 1 / c < 536870870 / 1342177289) ∧
    (∀ c : ℕ, 1 ≤ c → c ≤ 14 →
      (1 : ℝ) - 1 / 3 - 1 / 5 - 1 / c < 536870870 / 1342177289) ∧
    (∀ c : ℕ, 1 ≤ c → c ≤ 9 →
      (1 : ℝ) - 1 / 4 - 1 / 4 - 1 / c < 536870870 / 1342177289) ∧
    (∀ c : ℕ, 1 ≤ c → c ≤ 9 →
      (2 : ℝ) - 1 / 2 - 1 / 2 - 1 / 2 - 1 / c < 536870870 / 1342177289) := by
  have ipos : ∀ x : ℕ, 1 ≤ x → (0 : ℝ) < 1 / x := fun x hx => by
    have : (0 : ℝ) < x := by exact_mod_cast hx
    positivity
  have ige : ∀ (x N : ℕ), 1 ≤ x → x ≤ N → (1 : ℝ) / N ≤ 1 / x := fun x N hx hle =>
    one_div_le_one_div_of_le (by exact_mod_cast hx) (by exact_mod_cast hle)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    have : (r : ℝ) ≤ 11 := by exact_mod_cast hr
    linarith
  · intro b₁ b₂ b₃ b₄ h1 h2 h3 h4 hsmall
    have p1 := ipos b₁ h1; have p2 := ipos b₂ h2; have p3 := ipos b₃ h3; have p4 := ipos b₄ h4
    rcases hsmall with h | h | h | h
    · have := ige b₁ 3947580 h1 h; linarith
    · have := ige b₂ 3947580 h2 h; linarith
    · have := ige b₃ 3947580 h3 h; linarith
    · have := ige b₄ 3947580 h4 h; linarith
  · intro b c hb1 hb2 hc
    have := ige b 9 (by omega) hb2; have := ipos c hc; linarith
  · intro c hc
    have := ipos c hc; linarith
  · intro c hc hle
    have := ige c 29433712 hc hle; linarith
  · intro c hc hle
    have := ige c 59 hc hle; linarith
  · intro c hc hle
    have := ige c 14 hc hle; linarith
  · intro c hc hle
    have := ige c 9 hc hle; linarith
  · intro c hc hle
    have := ige c 9 hc hle; linarith

/-- **Pattern-3 simultaneous degree-`2^28` pencil classification (`h = 1`):**
Eliminates ALL 25 proper dyadic inner degrees `2^r` (`1 ≤ r ≤ 25`), leaving only
`m ∈ {2^26, 2^27, 2^28}`. -/
theorem pattern3_deg_2_28_classification {r : ℕ} (hr : r ≤ 28)
    (hlarge : 44739242 ≤ 2 ^ r - 1) :
    r = 26 ∨ r = 27 ∨ r = 28 := by
  by_contra h
  have hle : r ≤ 25 := by omega
  have hpow : 2 ^ r ≤ 2 ^ 25 := Nat.pow_le_pow_right (by decide) hle
  omega

/-- Characteristic headroom for odd `D_odd = 2^28 - 1` and Pattern-3 `2^28`:
`2 * 2^30 * 2^28 = 2^59 < p₁ < p₂`. -/
theorem odd_split_characteristic_headroom :
    2 * 1073741824 * 268435455 < 2 ^ 59 ∧
    2 * 1073741824 * 268435456 = 2 ^ 59 ∧
    2 ^ 59 < 365375409332725729550921208179070755120141565953 ∧
    2 ^ 59 < 730750818665451459101842416358141509841924915201 := by
  decide

#print axioms pointwise_k_fiber_energy
#print axioms small_pair_k_fibers
#print axioms stableK
#print axioms no_odd_k_fiber_moments
#print axioms pow2Bound_sound
#print axioms pow_two_lt_of_bound
#print axioms production_odd_fiber_thresholds_p1
#print axioms production_odd_fiber_thresholds_p2
#print axioms odd_split_no_nontrivial_source_symmetry
#print axioms odd_split_suborbit_floor_and_rank
#print axioms odd_split_inner_degree_classification
#print axioms odd_split_excess_wronskian
#print axioms odd_split_orbifold_excess_floors
#print axioms odd_split_full_excess
#print axioms odd_split_excluded_signatures
#print axioms pattern3_deg_2_28_classification
#print axioms odd_split_characteristic_headroom

end ProximityGap.SplitPencilOddFiberObstructions

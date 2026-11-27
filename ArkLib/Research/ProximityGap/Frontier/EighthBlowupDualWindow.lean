/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorJetInterpolation
import ArkLib.Research.ProximityGap.Frontier.DoubleInterpolationCommonFactor

/-! # Blown-Up Gauss-Graph Excess Intersection and Dual `(α, β)` Veronese Windows at Eighth Rate

This module applies the nef-safe blown-up Gauss-graph height bound (`blowupH`) together with
dual-constraint `(α, β)` Veronese pricing and unconditionally independent fixed rich-head rows
(`p = min(j, s + 1)`) to four eighth-rate (`n = 2^30`, `k = 2^27`, `d = 2^27 - 1`, `B₂ = 2^31`)
second-prime production windows:

| Window | Errors `e` | Primary `(r₁, b₁, s₁)` | Companion `(r₂, b₂, s₂)` | `j = 4` Residual | Max Non-Exceptional Total |
|---|---:|---|---|---:|---:|
| **W0** (Safe predecessor) | `671,088,639` | `(6, 16, 335)` | `(10, 29, 126)` | **`189,082`** | **`2,125,303,109`** (`+22,180,539` slack) |
| **W1** (`5k` successor) | `671,088,640` | `(6, 16, 335)` | `(10, 29, 126)` | **`189,082`** | **`2,125,303,112`** (`+22,180,536` slack) |
| **W2** (`(1,1,1,6)` climb) | `677,920,000` | `(8, 23, 680)` | `(14, 41, 244)` | **`711,893`** | **`2,147,458,563`** (`+25,085` slack) |
| **W3** (Ceiling-1) | `679,477,247` | `(9, 25, 887)` | `(16, 46, 296)` | **`1,090,505`** | **`2,136,590,428`** (`+10,893,220` slack) |

## What is Lean-checked in this file

1. **Nef-safe blown-up Gauss-graph algebraic core** (`factor_order_sum_ge`, `blowupH`,
   `blowupH_mono`).
2. **Unconditional Lagrange Veronese point-separation and row-independence theorem**
   (`veronese_lagrange_separation`, `veronese_eval_linearIndependent`): over *any* field `F`
   (arbitrary characteristic, no general-position assumption), any `p ≤ s + 1` pairwise distinct
   points in `F²` have linearly independent evaluation functionals on bivariate polynomials of
   total degree `≤ s`, formally justifying `p = min(j, s + 1)` fixed rich-head rows in the
   degree-`s` Veronese tangent-polar determinant.
3. **Exact mixed-Hasse surface construction** (`ranks`, `surfaces`) for all eight production
   surfaces across W0–W3 on any injective domain of size `2^30` over any field.
4. **Dual-constraint `(α, β)` Veronese allocation** (`parameters`, `dual_prices`, `allocation`):
   exact verification of all Veronese gaps, 5-column conic determinant gaps (`5t - n - 6d > 0`),
   tame-characteristic guards, Case-1 companion-cofactor fallback floors, and shared-degree
   allocations across all `0 ≤ j ≤ b₁` and `2 ≤ b ≤ b₁ - j`.
5. **Sharpened `671,088,640` Blowup-Dual corollaries** (`blowup_sharpened_floors`):
   cutting the `j = 4` residual **109.0×** from `20,607,410` to **`189,082`** tightens
   the saturated `(1,1,1,1)` orbit floor to **`B ≥ 268,340,910`** (within `94,544` of `2d`),
   the `(1,1,1,5)` fresh-label collision cap to **`≤ 189,085`**, and the universal non-Galois
   homothetic-cover image floor across all `0 ≤ s ≤ 4` to **`|h(H_reg)| ≥ 670,994,076`**
   (isolated singletons `≥ 268,246,328`, partial-involution pair cap `P ≤ 402,747,748`).

The surface intersection argument on `Bl_{∪ C_x} Bl_Σ P(O ⊕ O ⊕ O(-d))`, plane-curve
reflexivity, and 5-column conic / Veronese determinant extractions are written in
`docs/research/proximity-gap/half-blowup-gauss-window.md`,
`docs/research/proximity-gap/tangent-polar-windows.md`, and
`docs/research/proximity-gap/eighth-blowup-dual-window.md`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.EighthBlowupDualWindow

open Finset Polynomial HalfSuccessorJetInterpolation SecondPrimeQuarticInterpolation

abbrev n : ℕ := 1073741824
abbrev k : ℕ := 134217728
abbrev d : ℕ := 134217727
abbrev budget : ℕ := 2147483648

/-! ## Section 1: Nef-safe blown-up Gauss-graph algebraic core -/

/-- If an interpolant of order `r` on `T` (`|T| = t₀`) and strict weight `< r * t₀` factors as
`F^k * G` with `k * W + Wg < r * t₀` and `G` nonzero on a section agreeing on `T`, then the site
vanishing orders `i` of `F` on `T` satisfy `W + 1 ≤ ∑ x ∈ T, i x`. -/
theorem factor_order_sum_ge {α : Type*} (T : Finset α) (i j : α → ℕ)
    {k_ W Wg r t₀ : ℕ} (hT : T.card = t₀)
    (hwt : k_ * W + Wg < r * t₀)
    (hord : ∀ x ∈ T, r ≤ k_ * i x + j x)
    (hgj : ∑ x ∈ T, j x ≤ Wg) :
    W + 1 ≤ ∑ x ∈ T, i x := by
  have hsum : r * t₀ ≤ k_ * (∑ x ∈ T, i x) + ∑ x ∈ T, j x := by
    calc r * t₀ = ∑ _x ∈ T, r := by rw [Finset.sum_const, hT, smul_eq_mul, mul_comm]
      _ ≤ ∑ x ∈ T, (k_ * i x + j x) := Finset.sum_le_sum hord
      _ = k_ * (∑ x ∈ T, i x) + ∑ x ∈ T, j x := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hlt : k_ * W < k_ * ∑ x ∈ T, i x := by omega
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
    refine Nat.le_induction (fun _ => le_rfl) (fun m' hm ih hm1 => ?_) m hWm
    exact (ih (by omega)).trans (step m' (hbd.trans hm) hm1)
  exact go (min wMax (b * t₀ - 1)) hhi (Nat.min_le_right _ _)

/-! ## Section 2: Unconditional Lagrange Veronese point-separation theorem -/

/-- Evaluation coordinate map `Fin 2 → F` for an affine plane point `pt : F × F`. -/
def planeCoord {F : Type*} (pt : F × F) : Fin 2 → F
  | ⟨0, _⟩ => pt.1
  | ⟨1, _⟩ => pt.2

/-- **Unconditional Lagrange point-separation in `F²`**: over *any* field `F` (arbitrary
characteristic, with *no* collinearity or general-position hypothesis), for any `p ≤ s + 1`
pairwise distinct points `pt : Fin p → F × F` and every `i : Fin p`, there exists a bivariate
polynomial `P` of total degree `≤ s` vanishing at every `pt j` (`j ≠ i`) and nonzero at `pt i`. -/
theorem veronese_lagrange_separation {F : Type*} [Field F] {p s : ℕ} (hps : p ≤ s + 1)
    (pt : Fin p → F × F) (hinj : Function.Injective pt) (i : Fin p) :
    ∃ P : MvPolynomial (Fin 2) F,
      P.totalDegree ≤ s ∧
      MvPolynomial.eval (planeCoord (pt i)) P ≠ 0 ∧
      ∀ j : Fin p, j ≠ i → MvPolynomial.eval (planeCoord (pt j)) P = 0 := by
  classical
  let fac : Fin p → MvPolynomial (Fin 2) F := fun j =>
    if (pt i).1 ≠ (pt j).1 then
      MvPolynomial.X 0 - MvPolynomial.C (pt j).1
    else
      MvPolynomial.X 1 - MvPolynomial.C (pt j).2
  refine ⟨∏ j ∈ univ.erase i, fac j, ?_, ?_, ?_⟩
  · have hdeg1 : ∀ j ∈ univ.erase i, (fac j).totalDegree ≤ 1 := by
      intro j _
      dsimp only [fac]
      split_ifs
      · exact (MvPolynomial.totalDegree_sub _ _).trans
          (max_le (by simp [MvPolynomial.totalDegree_X]) (by simp))
      · exact (MvPolynomial.totalDegree_sub _ _).trans
          (max_le (by simp [MvPolynomial.totalDegree_X]) (by simp))
    have hprod := MvPolynomial.totalDegree_finsetProd (univ.erase i) fac
    have hsum : ∑ j ∈ univ.erase i, (fac j).totalDegree ≤ (univ.erase i).card := by
      simpa using Finset.sum_le_sum hdeg1
    have hcard : (univ.erase i).card = p - 1 := by
      rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
    exact hprod.trans (hsum.trans (by omega))
  · rw [map_prod, Finset.prod_ne_zero_iff]
    intro j hj
    have hji : j ≠ i := (mem_erase.mp hj).1
    dsimp only [fac]
    split_ifs with h1
    · simp only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, planeCoord]
      exact sub_ne_zero.mpr h1
    · push Not at h1
      have h2 : (pt i).2 ≠ (pt j).2 := by
        intro heq
        exact hji.symm (hinj (Prod.ext h1 heq))
      simp only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, planeCoord]
      exact sub_ne_zero.mpr h2
  · intro j hji
    rw [map_prod]
    apply Finset.prod_eq_zero (mem_erase.mpr ⟨hji, mem_univ j⟩)
    dsimp only [fac]
    split_ifs <;> simp [planeCoord]

/-- **Unconditional Veronese row independence**: for any `p ≤ s + 1` pairwise distinct points in
`F²`, their evaluation functionals on bivariate polynomials of total degree `≤ s` are linearly
independent over `F` (justifying `p = min(j, s + 1)` fixed rich-head rows in degree-`s` Veronese
determinants, whether or not the rich heads are collinear). -/
theorem veronese_eval_linearIndependent {F : Type*} [Field F] {p s : ℕ} (hps : p ≤ s + 1)
    (pt : Fin p → F × F) (hinj : Function.Injective pt) (c : Fin p → F)
    (hvan : ∀ P : MvPolynomial (Fin 2) F, P.totalDegree ≤ s →
      ∑ j : Fin p, c j * MvPolynomial.eval (planeCoord (pt j)) P = 0) :
    ∀ i : Fin p, c i = 0 := by
  intro i
  obtain ⟨P, hdeg, hne, hzero⟩ := veronese_lagrange_separation hps pt hinj i
  have hsum := hvan P hdeg
  have hsingle : ∑ j : Fin p, c j * MvPolynomial.eval (planeCoord (pt j)) P =
      c i * MvPolynomial.eval (planeCoord (pt i)) P := by
    rw [Finset.sum_eq_single i]
    · intro j _ hji
      rw [hzero j hji, mul_zero]
    · intro hi; exact absurd (mem_univ i) hi
  rw [hsingle] at hsum
  exact (mul_eq_zero.mp hsum).resolve_right hne

/-! ## Section 3: Four eighth-rate Blowup-Dual windows and mixed-Hasse surfaces -/

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

/-- Parameter package for an eighth-rate Blowup-Dual production window. -/
structure Window where
  errors : ℕ
  r₁ : ℕ
  b₁ : ℕ
  s₁ : ℕ
  r₂ : ℕ
  b₂ : ℕ
  s₂ : ℕ
  cutoff : ℕ
  linMult : ℕ
  resJ4 : ℕ
  ordBound : ℕ
  hasPredecessorCap : Bool
  has1116 : Bool
  has41Cap : Bool
  alphas : List ℕ
  betas : List ℕ
deriving DecidableEq, Repr

/-- The four production Blowup-Dual windows at rate `1/8`:
- `0`: `671,088,639` (unconditional safety predecessor, max `2,125,303,109`, slack `+22,180,539`),
- `1`: `671,088,640` (`5k` successor, `res4 = 189,082`, `109.0×` drop from `main`),
- `2`: `677,920,000` (new `(1,1,1,6)` safety climb record, `+6,831,360` past `5k`),
- `3`: `679,477,247` (Ceiling-1 tightening, `res4 = 1,090,505`). -/
def win : Fin 4 → Window
  | 0 => {
      errors := 671088639, r₁ := 6, b₁ := 16, s₁ := 335, r₂ := 10, b₂ := 29, s₂ := 126,
      cutoff := 335, linMult := 17, resJ4 := 189082, ordBound := 2125303109,
      hasPredecessorCap := true, has1116 := true, has41Cap := true,
      alphas := [1188, 1003, 918, 717, 698, 479, 406, 463, 408, 418, 185, 133, 226, 129, 127, 17, 17],
      betas  := [9072, 9150, 8494, 8979, 7320, 7799, 6924, 5117, 4661, 3159, 6032, 6003, 2109, 3164, 411, 0, 0]
    }
  | 1 => {
      errors := 671088640, r₁ := 6, b₁ := 16, s₁ := 335, r₂ := 10, b₂ := 29, s₂ := 126,
      cutoff := 335, linMult := 17, resJ4 := 189082, ordBound := 2125303112,
      hasPredecessorCap := false, has1116 := true, has41Cap := true,
      alphas := [1188, 1003, 918, 717, 698, 479, 406, 463, 408, 418, 185, 133, 226, 129, 127, 17, 17],
      betas  := [9072, 9150, 8494, 8979, 7320, 7799, 6924, 5117, 4661, 3159, 6032, 6003, 2109, 3164, 411, 0, 0]
    }
  | 2 => {
      errors := 677920000, r₁ := 8, b₁ := 23, s₁ := 680, r₂ := 14, b₂ := 41, s₂ := 244,
      cutoff := 680, linMult := 18, resJ4 := 711893, ordBound := 2147458563,
      hasPredecessorCap := false, has1116 := true, has41Cap := false,
      alphas := [2952, 2607, 2704, 3003, 2265, 1671, 1315, 1837, 999, 1265, 766, 730, 700, 463, 426, 478, 374, 258, 322, 247, 245, 243, 18, 18],
      betas  := [10980, 11664, 7502, 723, 6379, 9746, 10626, 711, 11092, 4465, 10800, 9320, 7656, 10626, 9379, 5496, 5928, 7264, 1356, 900, 415, 252, 0, 0]
    }
  | 3 => {
      errors := 679477247, r₁ := 9, b₁ := 25, s₁ := 887, r₂ := 16, b₂ := 46, s₂ := 296,
      cutoff := 1300, linMult := 18, resJ4 := 1090505, ordBound := 2136590428,
      hasPredecessorCap := false, has1116 := false, has41Cap := false,
      alphas := [3368, 3654, 3960, 2381, 3347, 2958, 1653, 2356, 1809, 1779, 1575, 1186, 1033, 770, 615, 466, 543, 664, 306, 374, 320, 300, 298, 296, 18, 18],
      betas  := [17393, 10030, 2058, 18752, 1752, 1455, 15370, 1397, 7217, 4610, 5148, 9690, 9940, 13018, 14100, 15455, 10360, 2790, 12510, 6094, 4416, 650, 537, 394, 0, 0]
    }

/-- Exact positive mixed-Hasse rank surpluses for all eight production surfaces across W0–W3. -/
theorem ranks : ∀ (i : Fin 4) (companion : Bool),
    let w := win i
    let t := n - w.errors
    let r := if companion then w.r₂ else w.r₁
    let b := if companion then w.b₂ else w.b₁
    let s := if companion then w.s₂ else w.s₁
    0 < r ∧ 0 < t ∧ r ≤ s + 1 ∧
    n * rowCount s r < columnCount s b d (r * t) := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- All eight production mixed-Hasse surfaces exist on every injective length-`2^30` domain
over any field and vanish on every witnessing section with at least `t = n - w.errors` agreements. -/
theorem surfaces {I F : Type} [Fintype I] [Field F] (dom : I ↪ F) (u v : I → F)
    (hn : Fintype.card I = n) (i : Fin 4) (companion : Bool) :
    let w := win i
    let t := n - w.errors
    let r := if companion then w.r₂ else w.r₁
    let b := if companion then w.b₂ else w.b₁
    let s := if companion then w.s₂ else w.s₁
    SectionSurface dom u v s b d (r * t) t := by
  dsimp only
  let w := win i
  let t := n - w.errors
  let r := if companion then w.r₂ else w.r₁
  let b := if companion then w.b₂ else w.b₁
  let s := if companion then w.s₂ else w.s₁
  have hrk := ranks i companion
  dsimp only at hrk
  obtain ⟨hr, ht, hrs, hlt⟩ := hrk
  have hnum : Fintype.card I * Fintype.card (JetRows s r) < Fintype.card (Monomials s b d (r * t)) := by
    rw [hn, card_rows, card_columns]
    exact hlt
  obtain ⟨a, ha, jets, hf⟩ := exists_surface dom u v hr ht hrs hnum
  exact ⟨surface a, surface_ne_zero ha, fun _ _ _ h => surface_support a h,
    fun x => received_line_of_jet a _ _ _ (jets x 0 0 (by omega)),
    fun g q hq S hS hag => by rw [surface_eval]; exact hf g q hq S hS hag⟩

/-! ## Section 4: Dual-constraint `(α, β)` Veronese allocation -/

private def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- Collinear rich-head population cap via Cauchy–Schwarz core union. -/
def collinearMass (w : Window) (j : ℕ) : ℕ :=
  if j = 0 then 0
  else if j ≤ 2 then j * (w.errors + 1)
  else
    let c := (n - w.errors) - w.errors / w.cutoff
    let u := ceilDiv (j * c * c) (c + (j - 1) * d)
    min (j * (w.errors + 1)) (j * n - (j - 1) * u)

/-- Non-exceptional rich-head population allowance for `j` rich heads in window `w`:
- `j ≤ 3`: `j * (e + 1)` (unconditional).
- `j = 4`: `max` of collinear cap and (`2,125,114,027` at W0; `(1,1,1,6)` at W1–W2; `(1,1,1,7)` at W3).
- `j = 5`: `max` of collinear cap and `2,058,021,547` (`EighthFourPlusOne`) at W0–W1; collinear cap at W2–W3.
- `j ≥ 6`: all `j` heads are collinear (`15c > 3n + 20d` and `13c > 3n + 13d`). -/
def ordHeadMass (w : Window) (j : ℕ) : ℕ :=
  if j ≤ 3 then j * (w.errors + 1)
  else if j = 4 then
    let base := collinearMass w 4
    if w.hasPredecessorCap then max base 2125114027
    else if w.has1116 then max base (3 * (w.errors + 1) + (1 + w.errors / 6))
    else max base (3 * (w.errors + 1) + (1 + w.errors / 7))
  else if j = 5 then
    let base := collinearMass w 5
    if w.has41Cap then max base 2058021547
    else base
  else collinearMass w j

/-- Blown-up height bound maximized over `W ∈ [b * d, min (w.r₁ * t - 1 - j * d) (b * t - 1)]`. -/
def maxBlowupH (w : Window) (j b : ℕ) : ℕ :=
  let t := n - w.errors
  blowupH b (min (w.r₁ * t - 1 - j * d) (b * t - 1)) t d

/-- Fast shared-`H`/`R` conic price given precomputed `(t, H, R)`. -/
def conicPriceFast (t H R b : ℕ) : ℕ :=
  4 * b - 2 + 2 + ceilDiv (5 * (R + 2 * H)) (5 * t - n - 6 * d)

/-- Fast shared-`H`/`R` Veronese price given precomputed `(t, miss, H, R)`. -/
def veronesePriceFast (t miss H R j b s a h C_a E_s : ℕ) : ℕ :=
  let p := min j (s + 1)
  let gap := a * h * t - (C_a * n + E_s * d + a * p * miss)
  4 * b - 2 + 2 * s * b + ceilDiv ((h - p) * (a * R + s * H)) gap

/-- Five-column conic-modulo-equation determinant unit price at `m = b = 2`
(`gap = 5t - n - 6d > 0`, `h = 5`, `a = 1`, `C₁ = 1`, `E = 6`, Bezout `≤ 4 = 2 * m`). -/
def conicPrice (w : Window) (j b : ℕ) : ℕ :=
  conicPriceFast (n - w.errors) (maxBlowupH w j b) ((2 * b - 1) * n) b

/-- Degree-`s`, slope-`a` Veronese determinant unit price using `p = min(j, s + 1)`
unconditionally independent fixed rich heads (`veronese_eval_linearIndependent`),
valid for every actual companion degree `m > s * (s - 1)`. -/
def veronesePrice (w : Window) (j b s a h C_a E_s : ℕ) : ℕ :=
  veronesePriceFast (n - w.errors) (w.errors / w.cutoff) (maxBlowupH w j b) ((2 * b - 1) * n)
    j b s a h C_a E_s

/-- Fixed non-head residual overhead (scalar-only primary factors, single noncommon resultant,
and small polynomial affine heads). Common nonaffine linear factors share the `s₂ - j` degree
budget with nonlinear factors because `linMult ≤ alpha w j`. -/
def fixedOverhead (w : Window) (j : ℕ) : ℕ :=
  w.s₁ + (w.s₁ * w.b₂ + w.b₁ * w.s₂) + (w.b₁ - j) * w.cutoff

/-- Dual-constraint slope `α(w, j)` per unit of companion degree `m`. -/
def alpha (w : Window) (j : ℕ) : ℕ := w.alphas.getD j 0

/-- Dual-constraint surcharge `β(w, j)` per unit of ordinate degree `b`. -/
def beta (w : Window) (j : ℕ) : ℕ := w.betas.getD j 0

/-- Total residual budget for window `w` at `j` rich heads. -/
def residualCap (w : Window) (j : ℕ) : ℕ :=
  fixedOverhead w j + (w.s₂ - j) * alpha w j + (w.b₁ - j) * beta w j

/-- Single-pass check of all eight `(α, β)` dual-price regimes for `(w, j, b)`, computing
`H = maxBlowupH w j b`, `R`, and the cumulative `min` ladder `p2..p10` once (`28×` faster). -/
def checkDualRegimes (w : Window) (j b : ℕ) : Bool :=
  let t := n - w.errors
  let miss := w.errors / w.cutoff
  let H := maxBlowupH w j b
  let R := (2 * b - 1) * n
  let a := alpha w j
  let β := beta w j
  let pc := conicPriceFast t H R b
  let p2 := veronesePriceFast t miss H R j b 2 1 6 1 8
  let p3 := min p2 (veronesePriceFast t miss H R j b 3 2 10 4 20)
  let p4 := min p3 (veronesePriceFast t miss H R j b 4 2 15 4 40)
  let p5 := min p4 (veronesePriceFast t miss H R j b 5 3 21 10 70)
  let p6 := min p5 (veronesePriceFast t miss H R j b 6 4 28 20 112)
  let p8 := min p6 (veronesePriceFast t miss H R j b 8 5 45 35 240)
  let p10 := min p8 (veronesePriceFast t miss H R j b 10 6 66 56 440)
  decide (b * d ≤ w.r₁ * t - 1 - j * d) &&
  decide ((p10 - a) * (w.s₂ - j) ≤ β * b) &&
  (decide (b ≠ 2) || decide ((pc - a) * 2 ≤ β * b)) &&
  (decide (6 < b)  || decide ((p2 - a) * 6  ≤ β * b)) &&
  (decide (12 < b) || decide ((p3 - a) * 12 ≤ β * b)) &&
  (decide (20 < b) || decide ((p4 - a) * 20 ≤ β * b)) &&
  (decide (30 < b) || decide ((p5 - a) * 30 ≤ β * b)) &&
  (decide (56 < b) || decide ((p6 - a) * 56 ≤ β * b)) &&
  (decide (90 < b) || decide ((p8 - a) * 90 ≤ β * b))

/-- Cumulative 7-tier Veronese unit prices at cutoffs `2, 6, 12, 20, 30, 56, 90`. -/
def price2  (w : Window) (j b : ℕ) : ℕ := veronesePrice w j b 2 1 6 1 8
def price3  (w : Window) (j b : ℕ) : ℕ := min (price2 w j b) (veronesePrice w j b 3 2 10 4 20)
def price4  (w : Window) (j b : ℕ) : ℕ := min (price3 w j b) (veronesePrice w j b 4 2 15 4 40)
def price5  (w : Window) (j b : ℕ) : ℕ := min (price4 w j b) (veronesePrice w j b 5 3 21 10 70)
def price6  (w : Window) (j b : ℕ) : ℕ := min (price5 w j b) (veronesePrice w j b 6 4 28 20 112)
def price8  (w : Window) (j b : ℕ) : ℕ := min (price6 w j b) (veronesePrice w j b 8 5 45 35 240)
def price10 (w : Window) (j b : ℕ) : ℕ := min (price8 w j b) (veronesePrice w j b 10 6 66 56 440)

/-- Applicable per-unit-`m` nonlinear price for an irreducible common nonlinear factor `(b, m)`. -/
def factorUnitPrice (w : Window) (j b m : ℕ) : ℕ :=
  if 90 < m then price10 w j b
  else if 56 < m then price8 w j b
  else if 30 < m then price6 w j b
  else if 20 < m then price5 w j b
  else if 12 < m then price4 w j b
  else if 6 < m then price3 w j b
  else if 2 < m then price2 w j b
  else conicPrice w j b

private lemma checkDualRegimes_sound {w : Window} {j b : ℕ} (h : checkDualRegimes w j b = true) :
    b * d ≤ w.r₁ * (n - w.errors) - 1 - j * d ∧
    (price10 w j b - alpha w j) * (w.s₂ - j) ≤ beta w j * b ∧
    (b = 2 → (conicPrice w j b - alpha w j) * 2 ≤ beta w j * b) ∧
    (b ≤ 6  → (price2 w j b - alpha w j) * 6  ≤ beta w j * b) ∧
    (b ≤ 12 → (price3 w j b - alpha w j) * 12 ≤ beta w j * b) ∧
    (b ≤ 20 → (price4 w j b - alpha w j) * 20 ≤ beta w j * b) ∧
    (b ≤ 30 → (price5 w j b - alpha w j) * 30 ≤ beta w j * b) ∧
    (b ≤ 56 → (price6 w j b - alpha w j) * 56 ≤ beta w j * b) ∧
    (b ≤ 90 → (price8 w j b - alpha w j) * 90 ≤ beta w j * b) := by
  unfold checkDualRegimes at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hW, hp10⟩, hpc⟩, hp2⟩, hp3⟩, hp4⟩, hp5⟩, hp6⟩, hp8⟩ := h
  refine ⟨hW, hp10, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hb2; exact hpc.resolve_left (fun hne => hne hb2)
  · intro hb6; exact hp2.resolve_left (by omega)
  · intro hb12; exact hp3.resolve_left (by omega)
  · intro hb20; exact hp4.resolve_left (by omega)
  · intro hb30; exact hp5.resolve_left (by omega)
  · intro hb56; exact hp6.resolve_left (by omega)
  · intro hb90; exact hp8.resolve_left (by omega)

/-- All denominator positivity, core five/six-head collinearity, identity-site linear, Veronese
gap (at maximal `p = s + 1`), conic gap, tame-characteristic, and global budget guards hold
strictly across all four windows. -/
theorem parameters : ∀ i : Fin 4,
    let w := win i
    let t := n - w.errors
    let miss := w.errors / w.cutoff
    let core := t - miss
    max w.s₁ w.s₂ ≤ w.cutoff ∧
    w.b₁ ≤ w.s₂ ∧
    4 * n ≤ (w.linMult - 1) * (t - d) ∧
    3 * n + 20 * d < 15 * core ∧
    3 * n + 13 * d < 13 * core ∧
    n + 6 * d < 5 * t ∧
    1 * n + 8 * d + 1 * 3 * miss < 1 * 6 * t ∧
    4 * n + 20 * d + 2 * 4 * miss < 2 * 10 * t ∧
    4 * n + 40 * d + 2 * 5 * miss < 2 * 15 * t ∧
    10 * n + 70 * d + 3 * 6 * miss < 3 * 21 * t ∧
    20 * n + 112 * d + 4 * 7 * miss < 4 * 28 * t ∧
    35 * n + 240 * d + 5 * 9 * miss < 5 * 45 * t ∧
    56 * n + 440 * d + 6 * 11 * miss < 6 * 66 * t ∧
    2 * (w.r₁ * t) * w.b₁ < 2 ^ 100 ∧
    w.s₂ * (w.s₂ - 1) < 2 ^ 100 ∧
    residualCap w 4 = w.resJ4 ∧
    w.ordBound < budget := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
private theorem dual_prices_fast : ∀ i : Fin 4,
    let w := win i
    ∀ j : Fin (w.b₁ + 1),
      ordHeadMass w j.val + residualCap w j.val ≤ w.ordBound ∧
      w.linMult ≤ alpha w j.val ∧
      (2 ≤ w.b₁ - j.val → (w.s₂ - j.val) + (w.b₂ - j.val) ≤ alpha w j.val) ∧
      ∀ b : Fin (w.b₁ - j.val + 1), 2 ≤ b.val → checkDualRegimes w j.val b.val = true := by
  decide +kernel

/-- Every `(i, j, b)` triple across all four windows satisfies:
1. Total non-exceptional head + residual budget `≤ ordBound < 2^31`,
2. Nonaffine linear factor price `linMult ≤ alpha` and Case-1 companion-cofactor fallback
   `(s₂ - j) + (b₂ - j) ≤ alpha` whenever `2 ≤ b₁ - j`,
3. Weight admissibility `b * d ≤ r₁ * t - 1 - j * d` and exact dual-constraint `(α, β)` pricing
   across all eight degree regimes (`m = 2`, `3..6`, `7..12`, `13..20`, `21..30`, `31..56`, `57..90`, `> 90`). -/
theorem dual_prices : ∀ i : Fin 4,
    let w := win i
    let t := n - w.errors
    ∀ j : Fin (w.b₁ + 1),
      ordHeadMass w j.val + residualCap w j.val ≤ w.ordBound ∧
      w.linMult ≤ alpha w j.val ∧
      (2 ≤ w.b₁ - j.val → (w.s₂ - j.val) + (w.b₂ - j.val) ≤ alpha w j.val) ∧
      ∀ b : Fin (w.b₁ - j.val + 1), 2 ≤ b.val →
        b.val * d ≤ w.r₁ * t - 1 - j.val * d ∧
        (price10 w j.val b.val - alpha w j.val) * (w.s₂ - j.val) ≤ beta w j.val * b.val ∧
        (b.val = 2 → (conicPrice w j.val b.val - alpha w j.val) * 2 ≤ beta w j.val * b.val) ∧
        (b.val ≤ 6  → (price2 w j.val b.val - alpha w j.val) * 6  ≤ beta w j.val * b.val) ∧
        (b.val ≤ 12 → (price3 w j.val b.val - alpha w j.val) * 12 ≤ beta w j.val * b.val) ∧
        (b.val ≤ 20 → (price4 w j.val b.val - alpha w j.val) * 20 ≤ beta w j.val * b.val) ∧
        (b.val ≤ 30 → (price5 w j.val b.val - alpha w j.val) * 30 ≤ beta w j.val * b.val) ∧
        (b.val ≤ 56 → (price6 w j.val b.val - alpha w j.val) * 56 ≤ beta w j.val * b.val) ∧
        (b.val ≤ 90 → (price8 w j.val b.val - alpha w j.val) * 90 ≤ beta w j.val * b.val) := by
  intro i
  dsimp only
  intro j
  obtain ⟨h1, h2, h3, h4⟩ := dual_prices_fast i j
  exact ⟨h1, h2, h3, fun b hb => checkDualRegimes_sound (h4 b hb)⟩

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

private theorem factor_dual_bound (i : Fin 4) (j : Fin ((win i).b₁ + 1)) {b m : ℕ}
    (hb : 2 ≤ b) (hbhi : b ≤ (win i).b₁ - j.val) (hbm : b ≤ m) (hmhi : m ≤ (win i).s₂ - j.val) :
    m * factorUnitPrice (win i) j.val b m ≤ m * alpha (win i) j.val + b * beta (win i) j.val := by
  have h := ((dual_prices i j).2.2.2 ⟨b, by omega⟩ hb).2
  dsimp only at h
  unfold factorUnitPrice
  split_ifs with h90 h56 h30 h20 h12 h6 h2
  · exact range_dual_step hmhi h.1
  · exact range_dual_step (by omega) (h.2.2.2.2.2.2.2 (by omega))
  · exact range_dual_step (by omega) (h.2.2.2.2.2.2.1 (by omega))
  · exact range_dual_step (by omega) (h.2.2.2.2.2.1 (by omega))
  · exact range_dual_step (by omega) (h.2.2.2.2.1 (by omega))
  · exact range_dual_step (by omega) (h.2.2.2.1 (by omega))
  · exact range_dual_step (by omega) (h.2.2.1 (by omega))
  · exact range_dual_step (by omega) (h.2.1 (by omega))

/-- **Master Blowup-Dual shared-degree allocation theorem** across all four eighth-rate windows:
handles scalar-only factors, single noncommon resultant, small polynomial affine heads, common
nonaffine linear factors (`pop ≤ deg * linMult`), Case-1 companion-cofactor fallback nonlinear
factors, and Case-2 blown-up Gauss-graph Veronese nonlinear factors simultaneously. -/
theorem allocation {J L : Type*} (S : Finset J) (T : Finset L)
    (degN valN popN : J → ℕ) (degL popL : L → ℕ)
    (i : Fin 4) (j : Fin ((win i).b₁ + 1))
    (heads scalar outside small : ℕ)
    (hheads : heads ≤ ordHeadMass (win i) j.val)
    (hscalar : scalar ≤ (win i).s₁)
    (houtside : outside ≤ (win i).s₁ * (win i).b₂ + (win i).b₁ * (win i).s₂)
    (hsmall : small ≤ ((win i).b₁ - j.val) * (win i).cutoff)
    (htotalDeg : (∑ a ∈ S, degN a) + (∑ l ∈ T, degL l) ≤ (win i).s₂ - j.val)
    (htotalVal : ∑ a ∈ S, valN a ≤ (win i).b₁ - j.val)
    (hvalN : ∀ a ∈ S, 2 ≤ valN a ∧ valN a ≤ degN a)
    (hpopN : ∀ a ∈ S,
      popN a ≤ degN a * factorUnitPrice (win i) j.val (valN a) (degN a) ∨
      popN a ≤ degN a * (((win i).s₂ - j.val) + ((win i).b₂ - j.val)))
    (hpopL : ∀ l ∈ T, popL l ≤ degL l * (win i).linMult) :
    heads + scalar + outside + small + (∑ a ∈ S, popN a) + (∑ l ∈ T, popL l) ≤ (win i).ordBound ∧
    (win i).ordBound < budget := by
  have hdp := dual_prices i j
  have hpar := parameters i
  have eachN (a : J) (ha : a ∈ S) :
      popN a ≤ degN a * alpha (win i) j.val + valN a * beta (win i) j.val := by
    obtain ⟨hlo, hvm⟩ := hvalN a ha
    have hhi : valN a ≤ (win i).b₁ - j.val :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) ha).trans htotalVal
    have hdeg_hi : degN a ≤ (win i).s₂ - j.val :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) ha).trans ((Nat.le_add_right _ _).trans htotalDeg)
    rcases hpopN a ha with hgeom | hcase1
    · exact hgeom.trans (factor_dual_bound i j hlo hhi hvm hdeg_hi)
    · have h2 : 2 ≤ (win i).b₁ - j.val := hlo.trans hhi
      exact (hcase1.trans (Nat.mul_le_mul_left _ (hdp.2.2.1 h2))).trans (Nat.le_add_right _ _)
  have hsumN : ∑ a ∈ S, popN a ≤
      (∑ a ∈ S, degN a) * alpha (win i) j.val + (∑ a ∈ S, valN a) * beta (win i) j.val := by
    calc ∑ a ∈ S, popN a
        ≤ ∑ a ∈ S, (degN a * alpha (win i) j.val + valN a * beta (win i) j.val) :=
          Finset.sum_le_sum eachN
      _ = (∑ a ∈ S, degN a) * alpha (win i) j.val + (∑ a ∈ S, valN a) * beta (win i) j.val := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  have hsumL : ∑ l ∈ T, popL l ≤ (∑ l ∈ T, degL l) * alpha (win i) j.val := by
    calc ∑ l ∈ T, popL l
        ≤ ∑ l ∈ T, degL l * (win i).linMult := Finset.sum_le_sum hpopL
      _ = (∑ l ∈ T, degL l) * (win i).linMult := (Finset.sum_mul T degL _).symm
      _ ≤ (∑ l ∈ T, degL l) * alpha (win i) j.val := Nat.mul_le_mul_left _ hdp.2.1
  have hdeg_comb :
      (∑ a ∈ S, degN a) * alpha (win i) j.val + (∑ l ∈ T, degL l) * alpha (win i) j.val ≤
        ((win i).s₂ - j.val) * alpha (win i) j.val := by
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_right _ htotalDeg
  have hval_comb := Nat.mul_le_mul_right (beta (win i) j.val) htotalVal
  have htot := hdp.1
  unfold residualCap fixedOverhead at htot
  exact ⟨by omega, hpar.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-! ## Section 5: Sharpened `671,088,640` Blowup-Dual orbit, collision, and cover floors -/

/-- Under the Blowup-Dual `671,088,640` residual allowance (`other ≤ 189,082`, a `109.0×`
tightening from `20,607,410`):
1. **Saturated `(1,1,1,1)` orbit floor**: `B ≥ 268,340,910` (within `94,544` of the 2-to-1
   double-site threshold `2d = 268,435,454`, i.e., `> 49.982%` of all `4d = 536,870,908` double sites).
2. **Profile `(1,1,1,5)` collision cap**: at most **`189,085`** total fresh-label collisions
   across all four heads (out of `2,147,483,652` fresh slots, `> 99.991%` collision-free).
3. **Universal non-Galois homothetic-cover floors across all `0 ≤ s ≤ 4`**:
   image size **`|h(H_reg)| ≥ 670,994,076`** (`> 0.6249 n`), isolated singleton fibers
   **`≥ 268,246,328`**, and partial-involution pair cap **`P ≤ 402,747,748`**. -/
theorem blowup_sharpened_floors :
    (∀ (B heads other : ℕ), heads ≤ 2 * B + 3 * (n - 4 * d) → other ≤ 189082 →
      budget < heads + other → 268340910 ≤ B ∧ 2 * d - B ≤ 94544) ∧
    (∀ (heads collisions other : ℕ),
      heads + collisions ≤ 3 * (671088640 + 1) + (1 + 671088640 / 5) →
      other ≤ 189082 → budget < heads + other → collisions ≤ 189085) ∧
    (∀ (imgCard singletons pairs heads other : ℕ),
      2 * heads + 3 * (12 * k - 8) ≤ 6 * n + 4 * imgCard + 72 →
      other ≤ 189082 → budget < heads + other →
      2 * imgCard ≤ n + singletons → imgCard + pairs ≤ n →
      670994076 ≤ imgCard ∧ 268246328 ≤ singletons ∧ pairs ≤ 402747748) := by
  simp only [n, k, d, budget]
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> omega

#print axioms factor_order_sum_ge
#print axioms blowupH_mono
#print axioms veronese_lagrange_separation
#print axioms veronese_eval_linearIndependent
#print axioms ranks
#print axioms surfaces
#print axioms parameters
#print axioms dual_prices
#print axioms allocation
#print axioms blowup_sharpened_floors

end ArkLib.ProximityGap.Frontier.EighthBlowupDualWindow

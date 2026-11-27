/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorJetInterpolation

/-! # Tight eighth-rate successor windows and non-exceptional climb through 679,477,247 errors

At length `n = 2^30 = 1,073,741,824`, dimension `k = 2^27 = 134,217,728`, degree
`d = k - 1 = 134,217,727`, and second-prime budget `2n = 2,147,483,648`, this module
combines the single noncommon resultant and shared companion total degree
(`QuarterCommonFactorDegrees`) with multi-tier projective Veronese polars
(`TangentPolarWindows`) and sparse surface Gauss heights (`HalfSparseGaussWindow`) across
four eighth-rate production windows:

0. **`e = 671,088,640` (Pure L1+L2 algebraic model, zero Gauss graph):**
   shapes `(6, 16, 335)` and `(10, 29, 126)`, cutoff `H = 1,000`, ten polar tiers `(2,1)..(11,7)`.
   Cuts the four-head residual allowance from `20,607,410` to **`2,280,700`** (`9.0×`),
   lowering the maximum ordinary total (including `4 + 1` capped at `2,058,021,547` by
   `EighthFourPlusOne.lean` and all `j ≥ 6` collinear via `15c > 3n + 20d` & `13c > 3n + 13d`)
   to **`2,127,394,730`** (`20,088,918` slack) and raising the saturated double-site orbit floor
   to **`267,295,101`**.
1. **`e = 671,088,640` (Sparse-Gauss + 3-tier polar model):**
   shapes `(6, 16, 335)` and `(10, 29, 126)`, cutoff `H = 500`, three polar tiers
   `(2,1), (3,2), (4,2)`. Cuts the four-head residual allowance from `20,607,410` to
   **`397,364`** (`51.8×`), lowering the maximum ordinary total (including `4 + 1` via
   `EighthFourPlusOne.lean` and all `j ≥ 6` collinear) to **`2,125,511,394`** (`21,972,254`
   slack), raising the saturated double-site orbit floor from `258,131,746` to
   **`268,236,769`** (within `198,685` of the 2-to-1 double-site threshold `2d = 268,435,454`,
   i.e., `> 49.963%` of all `4d = 536,870,908` double sites), and capping total fresh-label
   collisions in `(1,1,1,5)` at `397,367`.
2. **`e = 677,600,000` (Climb `+6,511,360` errors past `5k`, covering `77.6%` of the open bracket):**
   shapes `(8, 22, 950)` and `(14, 41, 237)`, cutoff `H = 1,000`. All `j ≤ 3`, all `j ≥ 6`
   collinear (forced by `15c > 3n + 20d` & `13c > 3n + 13d`, which also force every `j = 5`
   rich family to contain 4 collinear heads, leaving `4 + 1` and `3 + 1` open above `5k`),
   collinear `j = 4, 5`, and all noncollinear `j = 4` profiles with `D₃ ≥ 2` or `D₄ ≥ 6` stay
   at or below **`2,147,225,906 ≤ 2n`** (`res4 = 1,492,569`).
3. **`e = 679,477,247` (One error below the `679,477,248` transverse attack):**
   shapes `(9, 25, 887)` and `(15, 44, 297)`, cutoff `H = 2,000`. All `j ≤ 3`, all `j ≥ 6`
   collinear (and every `j = 5` rich family contains 4 collinear heads; `4 + 1` and `3 + 1` open
   above `5k`), collinear `j = 4, 5`, and all noncollinear `j = 4` profiles with `D₃ ≥ 2` or
   `D₄ ≥ 7` stay at or below **`2,137,916,562 ≤ 2n`**.

The underlying logarithmic-derivation, plane-curve duality, and sparse Gauss-graph bounds are
written mathematics (`tangent-polar-windows.md`, `half-sparse-gauss-window.md`); this module
verifies the two trivariate interpolants, monotonicity of component caps in value degree `b`,
all positive denominators and five-head/identity-site hypotheses, every `(i, j, b, m)` nonlinear
component price, all non-exceptional allocations, and the sharpened orbit/collision floors.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.EighthSuccessorTightWindow

open Finset Polynomial
open SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation

abbrev n : ℕ := 1073741824
abbrev k : ℕ := 134217728
abbrev d : ℕ := 134217727
abbrev budget : ℕ := 2147483648

/-- Parameters of a second-prime eighth-rate interpolation window. -/
structure Window where
  errors : ℕ
  order₁ : ℕ
  degree₁ : ℕ
  first : ℕ
  order₂ : ℕ
  degree₂ : ℕ
  second : ℕ
  cutoff : ℕ
  linMult : ℕ
  sparseGauss : Bool
  resJ4 : ℕ
  ordBound : ℕ
  allowSix : Bool

/-- The four verified eighth-rate production windows. -/
def win (i : Fin 4) : Window :=
  ![⟨671088640, 6, 16, 335, 10, 29, 126, 1000, 17, false, 2280700, 2127394730, true⟩,
    ⟨671088640, 6, 16, 335, 10, 29, 126,  500, 17, true,   397364, 2125511394, true⟩,
    ⟨677600000, 8, 22, 950, 14, 41, 237, 1000, 18, true,  1492569, 2147225906, true⟩,
    ⟨679477247, 9, 25, 887, 15, 44, 297, 2000, 18, true,  2416639, 2137916562, false⟩] i

/-- Active Veronese polar `(s, a)` tiers for each model. -/
def polarTiers (sg : Bool) : List (ℕ × ℕ) :=
  if sg then [(2, 1), (3, 2), (4, 2)]
  else [(2, 1), (3, 2), (4, 2), (5, 3), (6, 4), (7, 4), (8, 5), (9, 5), (10, 6), (11, 7)]

/-- Veronese polar determinant denominator `a * C(s+2,2) * t - C(a+2,3) * n - s(s+1)(s+2)/3 * d`. -/
def polarGap (s a t : ℕ) : ℕ :=
  a * ((s + 2) * (s + 1) / 2) * t - ((a + 2) * (a + 1) * a / 6) * n -
    (s * (s + 1) * (s + 2) / 3) * d

/-- Ceiling division for positive `b`. -/
def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- Single-tier polar population bound for a nonlinear component `(b, m)`. -/
def polarPop (sg : Bool) (b m loss height t sp ap : ℕ) : ℕ :=
  let bez := if sg then sp * b * (2 * m - b - 1) else sp * m * (m - 1)
  let h := (sp + 2) * (sp + 1) / 2
  bez + h * (ap * loss + sp * height) / polarGap sp ap t

/-- Multi-tier nonlinear component population cap at value degree `b`, total scalar/value
degree `m`, coordinate/value weight `W`, and agreement threshold `t`. -/
def componentCap (sg : Bool) (b m W t : ℕ) : ℕ :=
  let gz := (2 * b - 2) * m - b * (b - 1)
  let height :=
    if sg then m * ((6 * b + 2) * W - 3 * b * b * d)
    else
      let ax := (2 * b - 2) * W - b * (b - 1) * d
      2 * ax * gz + 2 * W * m
  let loss := (gz + m) * n
  let ordPop := (2 * t * loss + n * (2 * height + m * n)) / (t * t - n * d)
  let bestPop := (polarTiers sg).foldl
    (fun acc p => if p.1 * (p.1 - 1) < m then min acc (polarPop sg b m loss height t p.1 p.2) else acc)
    ordPop
  gz + 2 * b * m + bestPop

/-- Collinear rich-head union bound combining Cauchy-Schwarz and the integer-cut lower bound. -/
def collinearUnion (j c : ℕ) : ℕ :=
  let cauchy := ceilDiv (j * c * c) (c + (j - 1) * d)
  let bestInt := (List.range j).foldl
    (fun acc idx =>
      let a := idx + 1
      let num := 2 * a * j * c - j * (j - 1) * d
      max acc (if num = 0 then 0 else ceilDiv num (a * (a + 1))))
    0
  max cauchy bestInt

/-- Collinear rich-head fresh-label cap for `j ≥ 4` heads on one polynomial line. -/
def collinearMass (w : Window) (j : ℕ) : ℕ :=
  let t := n - w.errors
  let c := t - w.errors / w.cutoff
  min (j * (w.errors + 1)) (j * n - (j - 1) * collinearUnion j c)

/-- Ordinary non-exceptional head-mass cap for `j` rich heads.
- For `j ≤ 3`: `j * (e + 1)`.
- For `j = 4`: covers all collinear quartets AND all noncollinear quartets with `D₃ ≥ 2` or
  `D₄ ≥ 6` (or `D₄ ≥ 7` when `allowSix = false`).
- For `j = 5`: at `e = 671,088,640`, covers both collinear quintuples and the `4 + 1`
  transverse-outlier family (capped at `2,058,021,547` by `EighthFourPlusOne.lean`); above
  `5k`, covers collinear quintuples (`4 + 1` remains open above `5k`).
- For `j ≥ 6`: all rich heads are forced collinear by `15c > 3n + 20d` and `13c > 3n + 13d`
  (`EighthCollinearOutlier.six`). -/
def ordinaryHeadMass (w : Window) (j : ℕ) : ℕ :=
  if j ≤ 3 then j * (w.errors + 1)
  else if j = 4 then
    let ord1122 := 2 * (w.errors + 1) + 2 * (1 + w.errors / 2)
    let ord111q := 3 * (w.errors + 1) + (1 + w.errors / (if w.allowSix then 6 else 7))
    max (collinearMass w 4) (max ord1122 ord111q)
  else if j = 5 ∧ w.errors ≤ 671088640 then
    max (collinearMass w 5) 2058021547
  else collinearMass w j

/-- Fixed non-shared residual overhead for `j` rich heads (scalar-only factors, single
noncommon value resultant, and small polynomial affine heads). -/
def fixedResidual (w : Window) (j : ℕ) : ℕ :=
  w.first + (w.first * w.degree₂ + w.degree₁ * w.second) + (w.degree₁ - j) * w.cutoff

/-- Upper-rounded single-tier polar population bound used for tier-endpoint scaling. -/
def polarPopCeil (sg : Bool) (b m loss height t sp ap : ℕ) : ℕ :=
  let bez := if sg then sp * b * (2 * m - b - 1) else sp * m * (m - 1)
  let h := (sp + 2) * (sp + 1) / 2
  bez + ceilDiv (h * (ap * loss + sp * height)) (polarGap sp ap t)

/-- Upper-rounded component cap used at polar-tier right endpoints (`17×` fewer kernel evaluations). -/
def componentCapCeil (sg : Bool) (b m W t : ℕ) : ℕ :=
  let gz := (2 * b - 2) * m - b * (b - 1)
  let height :=
    if sg then m * ((6 * b + 2) * W - 3 * b * b * d)
    else
      let ax := (2 * b - 2) * W - b * (b - 1) * d
      2 * ax * gz + 2 * W * m
  let loss := (gz + m) * n
  let ordPop := ceilDiv (2 * t * loss + n * (2 * height + m * n)) (t * t - n * d)
  let bestPop := (polarTiers sg).foldl
    (fun acc p => if p.1 * (p.1 - 1) < m then min acc (polarPopCeil sg b m loss height t p.1 p.2) else acc)
    ordPop
  gz + 2 * b * m + bestPop

/-- Per-unit price contribution of total degree `m` at maximal admissible value degree. -/
def unitTerm (w : Window) (j m : ℕ) : ℕ :=
  let t := n - w.errors
  let W := w.order₁ * t - 1 - j * d
  let b := min (w.degree₁ - j) m
  if m < 2 ∨ b < 2 ∨ W < b * d then 0
  else ceilDiv (componentCapCeil w.sparseGauss b m W t) m

/-- Polar tier cutoff right-endpoints `s * (s - 1)` for `polarTiers sg`. -/
def tierCutoffs (sg : Bool) : List ℕ :=
  if sg then [6, 12] else [6, 12, 20, 30, 42, 56, 72, 90, 110]

/-- Compact endpoint list covering every `2 ≤ m ≤ s₂ - j`: individual values `2 .. min (v₁ - j) (s₂ - j)`
plus the polar tier right-endpoints `c ∈ tierCutoffs` and `s₂ - j` where `b = v₁ - j` is constant. -/
def unitEndpoints (w : Window) (j : ℕ) : List ℕ :=
  let bcap := w.degree₁ - j
  let srem := w.second - j
  let small := List.range (min bcap srem + 1)
  let large := ((tierCutoffs w.sparseGauss).filter fun c => bcap < c ∧ c ≤ srem) ++
    (if bcap < srem then [srem] else [])
  small ++ large

/-- Maximum nonlinear/nonaffine-linear per-unit price across all `unitEndpoints w j`. -/
def maxUnitPrice (w : Window) (j : ℕ) : ℕ :=
  (unitEndpoints w j).foldl (fun acc m => max acc (unitTerm w j m)) w.linMult

/-- Total residual budget for `j` rich heads using the shared companion degree `s₂ - j`. -/
def residualBudget (w : Window) (j : ℕ) : ℕ :=
  fixedResidual w j + (w.second - j) * maxUnitPrice w j

/-! ## Section 1: Monotonicity of `componentCap` in value degree `b` -/

private lemma foldl_min_mono {α : Type*} (l : List α) (f g : α → ℕ → ℕ)
    (hf : ∀ x a b, a ≤ b → f x a ≤ g x b) :
    ∀ a b, a ≤ b → l.foldl (fun acc x => f x acc) a ≤ l.foldl (fun acc x => g x acc) b := by
  induction l with
  | nil => intro a b hab; exact hab
  | cons x xs ih =>
    intro a b hab
    exact ih _ _ (hf x a b hab)

private lemma step_gz_le {b m : ℕ} (hb : 1 ≤ b) (hbm : b + 1 ≤ m) :
    (2 * b - 2) * m - b * (b - 1) ≤ (2 * (b + 1) - 2) * m - (b + 1) * b := by
  have h1 : b * (b - 1) ≤ (2 * b - 2) * m := by
    have hbb : b * (b - 1) ≤ (b - 1) * (2 * m) := by
      rw [Nat.mul_comm b (b - 1)]
      exact Nat.mul_le_mul_left (b - 1) (by omega)
    have heq : (b - 1) * (2 * m) = (2 * b - 2) * m := by
      calc (b - 1) * (2 * m) = (2 * (b - 1)) * m := by ring
        _ = (2 * b - 2) * m := by congr 1; omega
    omega
  have h2 : (b + 1) * b ≤ (2 * (b + 1) - 2) * m := by
    have : (b + 1) * b ≤ 2 * b * m := by
      have hm2 : b + 1 ≤ 2 * m := by omega
      calc (b + 1) * b = b * (b + 1) := by ring
        _ ≤ b * (2 * m) := Nat.mul_le_mul_left b hm2
        _ = 2 * b * m := by ring
    have heq : 2 * (b + 1) - 2 = 2 * b := by omega
    rw [heq]; exact this
  have hdiff : (2 * b - 2) * m + (b + 1) * b ≤ (2 * (b + 1) - 2) * m + b * (b - 1) := by
    have hmul1 : (2 * b - 2) * m + 2 * m = (2 * (b + 1) - 2) * m := by
      have : (2 * b - 2) + 2 = 2 * (b + 1) - 2 := by omega
      rw [← Nat.add_mul, this]
    have hmul2 : b * (b - 1) + 2 * b = (b + 1) * b := by
      cases b with
      | zero => omega
      | succ k => simp [Nat.mul_succ]; ring
    have hbm2 : 2 * b ≤ 2 * m := by omega
    omega
  omega

private lemma step_ax_le {b W dd : ℕ} (hb : 1 ≤ b) (hW : (b + 1) * dd ≤ W) :
    (2 * b - 2) * W - b * (b - 1) * dd ≤ (2 * (b + 1) - 2) * W - (b + 1) * b * dd := by
  have hbd : b * dd ≤ W := (Nat.mul_le_mul_right dd (by omega : b ≤ b + 1)).trans hW
  have h1 : b * (b - 1) * dd ≤ (2 * b - 2) * W := by
    have hbb : (b - 1) * (b * dd) ≤ (b - 1) * (2 * W) :=
      Nat.mul_le_mul_left (b - 1) (by omega)
    have heq1 : b * (b - 1) * dd = (b - 1) * (b * dd) := by ring
    have heq2 : (b - 1) * (2 * W) = (2 * b - 2) * W := by
      calc (b - 1) * (2 * W) = (2 * (b - 1)) * W := by ring
        _ = (2 * b - 2) * W := by congr 1; omega
    omega
  have h2 : (b + 1) * b * dd ≤ (2 * (b + 1) - 2) * W := by
    have heq : 2 * (b + 1) - 2 = 2 * b := by omega
    rw [heq]
    have h3 : b * ((b + 1) * dd) ≤ b * (2 * W) := Nat.mul_le_mul_left b (by omega)
    have heq1 : (b + 1) * b * dd = b * ((b + 1) * dd) := by ring
    have heq2 : 2 * b * W = b * (2 * W) := by ring
    omega
  have hdiff : (2 * b - 2) * W + (b + 1) * b * dd ≤ (2 * (b + 1) - 2) * W + b * (b - 1) * dd := by
    have hmul1 : (2 * b - 2) * W + 2 * W = (2 * (b + 1) - 2) * W := by
      have : (2 * b - 2) + 2 = 2 * (b + 1) - 2 := by omega
      rw [← Nat.add_mul, this]
    have hmul2 : b * (b - 1) + 2 * b = (b + 1) * b := by
      cases b with
      | zero => omega
      | succ k => simp [Nat.mul_succ]; ring
    have hmul3 : b * (b - 1) * dd + 2 * (b * dd) = (b + 1) * b * dd := by
      calc b * (b - 1) * dd + 2 * (b * dd) = (b * (b - 1) + 2 * b) * dd := by ring
        _ = (b + 1) * b * dd := by rw [hmul2]
    omega
  omega

private lemma step_sg_height_le {b W dd : ℕ} (hW : (2 * b + 1) * dd ≤ 2 * W) :
    (6 * b + 2) * W - 3 * b * b * dd ≤ (6 * (b + 1) + 2) * W - 3 * (b + 1) * (b + 1) * dd := by
  have hbd : b * dd ≤ W := by
    have : 2 * (b * dd) ≤ (2 * b + 1) * dd := by
      have : 2 * b ≤ 2 * b + 1 := by omega
      calc 2 * (b * dd) = (2 * b) * dd := by ring
        _ ≤ (2 * b + 1) * dd := Nat.mul_le_mul_right dd this
    omega
  have h1 : 3 * b * b * dd ≤ (6 * b + 2) * W := by
    have h3 : 3 * b * (b * dd) ≤ 3 * b * W := Nat.mul_le_mul_left (3 * b) hbd
    have heq1 : 3 * b * b * dd = 3 * b * (b * dd) := by ring
    have h36 : 3 * b * W ≤ (6 * b + 2) * W := Nat.mul_le_mul_right W (by omega)
    omega
  have h6W : (6 * b + 2) * W + 6 * W = (6 * (b + 1) + 2) * W := by ring
  have h6d : 3 * (2 * b + 1) * dd ≤ 6 * W := by
    have : 3 * ((2 * b + 1) * dd) ≤ 3 * (2 * W) := Nat.mul_le_mul_left 3 hW
    have heq1 : 3 * (2 * b + 1) * dd = 3 * ((2 * b + 1) * dd) := by ring
    have heq2 : 3 * (2 * W) = 6 * W := by ring
    omega
  have h3b : 3 * (b + 1) * (b + 1) * dd = 3 * b * b * dd + 3 * (2 * b + 1) * dd := by ring
  omega

private lemma step_bez_sg_le {b m : ℕ} (hbm : b + 1 ≤ m) :
    b * (2 * m - b - 1) ≤ (b + 1) * (2 * m - (b + 1) - 1) := by
  have h1 : b + 1 ≤ 2 * m := by omega
  have h2 : b + 2 ≤ 2 * m := by omega
  have heq1 : b * (2 * m - b - 1) + b * (b + 1) = b * (2 * m) := by
    rw [← Nat.mul_add]; congr 1; omega
  have heq2 : (b + 1) * (2 * m - (b + 1) - 1) + (b + 1) * (b + 2) = (b + 1) * (2 * m) := by
    rw [← Nat.mul_add]; congr 1; omega
  have hdiff : (b + 1) * (b + 2) ≤ b * (b + 1) + 2 * m := by nlinarith
  nlinarith

/-- One-step monotonicity of `componentCap` from `b` to `b + 1`. -/
private lemma componentCap_step_b {sg : Bool} {b m W t : ℕ}
    (hb : 1 ≤ b) (hbm : b + 1 ≤ m) (hW : (2 * b + 1) * d ≤ 2 * W) (hW2 : (b + 1) * d ≤ W) :
    componentCap sg b m W t ≤ componentCap sg (b + 1) m W t := by
  unfold componentCap
  simp only [Nat.add_sub_cancel]
  set gz1 := (2 * b - 2) * m - b * (b - 1)
  set gz2 := (2 * (b + 1) - 2) * m - (b + 1) * b
  set ht1 := if sg then m * ((6 * b + 2) * W - 3 * b * b * d)
    else 2 * ((2 * b - 2) * W - b * (b - 1) * d) * gz1 + 2 * W * m
  set ht2 := if sg then m * ((6 * (b + 1) + 2) * W - 3 * (b + 1) * (b + 1) * d)
    else 2 * ((2 * (b + 1) - 2) * W - (b + 1) * b * d) * gz2 + 2 * W * m
  set ls1 := (gz1 + m) * n
  set ls2 := (gz2 + m) * n
  set ord1 := (2 * t * ls1 + n * (2 * ht1 + m * n)) / (t * t - n * d)
  set ord2 := (2 * t * ls2 + n * (2 * ht2 + m * n)) / (t * t - n * d)
  have hgz : gz1 ≤ gz2 := step_gz_le hb hbm
  have hloss : ls1 ≤ ls2 := Nat.mul_le_mul_right n (Nat.add_le_add_right hgz m)
  have hheight : ht1 ≤ ht2 := by
    cases sg
    · simp only [ht1, ht2, Bool.false_eq_true, ↓reduceIte]
      have hax := step_ax_le hb hW2
      have hmul := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hax) hgz
      omega
    · simp only [ht1, ht2, ↓reduceIte]
      exact Nat.mul_le_mul_left m (step_sg_height_le hW)
  have hord : ord1 ≤ ord2 := by
    apply Nat.div_le_div_right
    have h1 := Nat.mul_le_mul_left (2 * t) hloss
    have h2 := Nat.mul_le_mul_left n (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hheight) (m * n))
    omega
  have hfold :
      (polarTiers sg).foldl
        (fun acc p => if p.1 * (p.1 - 1) < m then min acc (polarPop sg b m ls1 ht1 t p.1 p.2) else acc) ord1 ≤
      (polarTiers sg).foldl
        (fun acc p => if p.1 * (p.1 - 1) < m then min acc (polarPop sg (b + 1) m ls2 ht2 t p.1 p.2) else acc) ord2 := by
    apply foldl_min_mono
    · intro p x y hxy
      split_ifs
      · apply min_le_min hxy
        unfold polarPop
        dsimp only
        have hbez : (if sg then p.1 * b * (2 * m - b - 1) else p.1 * m * (m - 1)) ≤
            (if sg then p.1 * (b + 1) * (2 * m - (b + 1) - 1) else p.1 * m * (m - 1)) := by
          cases sg
          · simp
          · simp only [↓reduceIte, mul_assoc]
            exact Nat.mul_le_mul_left p.1 (step_bez_sg_le hbm)
        have hdiv :
            ((p.1 + 2) * (p.1 + 1) / 2) * (p.2 * ls1 + p.1 * ht1) / polarGap p.1 p.2 t ≤
            ((p.1 + 2) * (p.1 + 1) / 2) * (p.2 * ls2 + p.1 * ht2) / polarGap p.1 p.2 t := by
          apply Nat.div_le_div_right
          apply Nat.mul_le_mul_left
          exact Nat.add_le_add (Nat.mul_le_mul_left p.2 hloss) (Nat.mul_le_mul_left p.1 hheight)
        omega
      · exact hxy
    · exact hord
  have h2bm : 2 * b * m ≤ 2 * (b + 1) * m :=
    Nat.mul_le_mul_right m (by omega)
  omega

/-- Full monotonicity of `componentCap` in value degree `b ≤ b' ≤ m` whenever
`(2 * b' - 1) * d ≤ 2 * W` and `b' * d ≤ W`. -/
theorem componentCap_mono_b {sg : Bool} {b b' m W t : ℕ}
    (hb : 1 ≤ b) (hbb' : b ≤ b') (hb'm : b' ≤ m)
    (hW : (2 * b' - 1) * d ≤ 2 * W) (hW2 : b' * d ≤ W) :
    componentCap sg b m W t ≤ componentCap sg b' m W t := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hbb'
  induction r with
  | zero => simp
  | succ r ih =>
    have h1 := ih (by omega) (by omega)
      ((Nat.mul_le_mul_right d (by omega)).trans hW)
      ((Nat.mul_le_mul_right d (by omega)).trans hW2)
    have h2 : componentCap sg (b + r) m W t ≤ componentCap sg (b + r + 1) m W t :=
      componentCap_step_b (by omega) (by omega)
        ((Nat.mul_le_mul_right d (by omega)).trans hW)
        ((Nat.mul_le_mul_right d (by omega)).trans hW2)
    simpa [Nat.add_assoc] using h1.trans h2

/-! ## Section 2: Production hypotheses, finite allocations, and trivariate interpolants -/

/-- All Johnson, rich-head divisor, identity-site linear, five-head noncollinear, weight,
and active Veronese polar denominator conditions hold across all four windows. -/
theorem hypotheses : ∀ i : Fin 4,
    let w := win i
    let t := n - w.errors
    let c := t - w.errors / w.cutoff
    n * d < t * t ∧
    max w.first w.second ≤ w.cutoff ∧
    (4 * w.linMult - 1) * n < w.linMult * (w.linMult - 1) * (t - d) ∧
    3 * n + 20 * d < 15 * c ∧
    3 * n + 13 * d < 13 * c ∧
    w.degree₁ * d ≤ w.order₁ * t - 1 ∧
    (2 * w.degree₁ + 1) * d ≤ 2 * (w.order₁ * t - 1) ∧
    (polarTiers w.sparseGauss).all (fun p =>
      (p.1 + 2).choose 2 == (p.1 + 2) * (p.1 + 1) / 2 &&
      (p.2 + 2).choose 3 == (p.2 + 2) * (p.2 + 1) * p.2 / 6 &&
      0 < polarGap p.1 p.2 t) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Kernel-checked verification of:
1. Exact `j = 4` residual budgets (`2,280,700` pure L1+L2; `397,364` Sparse-Gauss;
   `1,492,569` at `677.6M`; `2,416,639` at `679.477M`),
2. Every non-exceptional head-count allocation `0 ≤ j ≤ degree₁` fits within `ordBound ≤ 2n`,
3. Every nonlinear component at maximal admissible `b = min (degree₁ - j) m` obeys `maxUnitPrice`. -/
theorem window_budgets : ∀ i : Fin 4,
    let w := win i
    residualBudget w 4 = w.resJ4 ∧
    w.ordBound ≤ budget ∧
    (List.range (w.degree₁ + 1)).all (fun j =>
      ordinaryHeadMass w j + residualBudget w j ≤ w.ordBound) = true := by
  decide +kernel

private lemma foldl_max_ge_init {α : Type*} (l : List α) (f : α → ℕ) :
    ∀ a, a ≤ l.foldl (fun acc x => max acc (f x)) a := by
  induction l with
  | nil => intro a; exact le_rfl
  | cons x xs ih =>
    intro a
    exact (le_max_left a (f x)).trans (ih _)

private lemma foldl_max_ge_mem {α : Type*} (l : List α) (f : α → ℕ) {x : α} (hx : x ∈ l) :
    ∀ a, f x ≤ l.foldl (fun acc y => max acc (f y)) a := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    intro a
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact (le_max_right a (f x)).trans (foldl_max_ge_init ys f _)
    · exact ih hmem _

private lemma mul_div_le_mul_ceilDiv {A B D m m' : ℕ} (hD : 0 < D) (h : m' * A ≤ m * B) :
    m' * (A / D) ≤ m * ceilDiv B D := by
  have h1 : m' * (A / D) * D ≤ m' * A := by
    calc m' * (A / D) * D = m' * (D * (A / D)) := by ring
      _ ≤ m' * A := Nat.mul_le_mul_left m' (Nat.mul_div_le A D)
  have h2 : B ≤ D * ceilDiv B D := by
    unfold ceilDiv
    have hdm := Nat.div_add_mod (B + D - 1) D
    have hlt := Nat.mod_lt (B + D - 1) hD
    omega
  have h3 : m * B ≤ m * ceilDiv B D * D := by
    calc m * B ≤ m * (D * ceilDiv B D) := Nat.mul_le_mul_left m h2
      _ = m * ceilDiv B D * D := by ring
  exact Nat.le_of_mul_le_mul_right (h1.trans (h.trans h3)) hD

private lemma foldl_min_scale {α : Type*} (l : List α) (f g : α → ℕ → ℕ) (m m' : ℕ)
    (hf : ∀ x ∈ l, ∀ a b, m' * a ≤ m * b → m' * f x a ≤ m * g x b) :
    ∀ a b, m' * a ≤ m * b →
      m' * l.foldl (fun acc x => f x acc) a ≤ m * l.foldl (fun acc x => g x acc) b := by
  induction l with
  | nil => intro a b hab; exact hab
  | cons x xs ih =>
    intro a b hab
    exact ih (fun y hy => hf y (List.mem_cons_of_mem x hy)) _ _
      (hf x (List.mem_cons_self ..) a b hab)

/-- Exact tier-endpoint scaling: for fixed `b ≤ m ≤ m'` where every polar tier active at `m'`
is already active at `m`, `m' * componentCap sg b m W t ≤ m * componentCapCeil sg b m' W t`. -/
private lemma componentCap_mul_le_ceil {sg : Bool} {b m m' W t : ℕ}
    (hb : 1 ≤ b) (hbm : b ≤ m) (hmm' : m ≤ m')
    (hD0 : 0 < t * t - n * d)
    (hgap : ∀ p ∈ polarTiers sg, 0 < polarGap p.1 p.2 t)
    (htier : ∀ p ∈ polarTiers sg, p.1 * (p.1 - 1) < m' → p.1 * (p.1 - 1) < m) :
    m' * componentCap sg b m W t ≤ m * componentCapCeil sg b m' W t := by
  unfold componentCap componentCapCeil
  set gz1 := (2 * b - 2) * m - b * (b - 1)
  set gz2 := (2 * b - 2) * m' - b * (b - 1)
  have hbb1 : b * (b - 1) ≤ (2 * b - 2) * m := by
    have h1 : b * (b - 1) = (b - 1) * b := Nat.mul_comm _ _
    have h2 : (b - 1) * b ≤ (b - 1) * (2 * m) := Nat.mul_le_mul_left _ (by omega)
    have h3 : (b - 1) * (2 * m) = (2 * b - 2) * m := by
      calc (b - 1) * (2 * m) = (2 * (b - 1)) * m := by ring
        _ = (2 * b - 2) * m := by congr 1; omega
    omega
  have hbb2 : b * (b - 1) ≤ (2 * b - 2) * m' :=
    hbb1.trans (Nat.mul_le_mul_left _ hmm')
  have hgz : m' * gz1 ≤ m * gz2 := by
    have heq1 : m' * gz1 + m' * (b * (b - 1)) = m' * ((2 * b - 2) * m) := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hbb1]
    have heq2 : m * gz2 + m * (b * (b - 1)) = m * ((2 * b - 2) * m') := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hbb2]
    have heqm : m' * ((2 * b - 2) * m) = m * ((2 * b - 2) * m') := by ring
    have hle : m * (b * (b - 1)) ≤ m' * (b * (b - 1)) := Nat.mul_le_mul_right _ hmm'
    omega
  set ht1 := if sg then m * ((6 * b + 2) * W - 3 * b * b * d)
    else 2 * ((2 * b - 2) * W - b * (b - 1) * d) * gz1 + 2 * W * m
  set ht2 := if sg then m' * ((6 * b + 2) * W - 3 * b * b * d)
    else 2 * ((2 * b - 2) * W - b * (b - 1) * d) * gz2 + 2 * W * m'
  have hht : m' * ht1 ≤ m * ht2 := by
    cases sg
    · simp only [ht1, ht2, Bool.false_eq_true, ↓reduceIte]
      have h1 : m' * (2 * ((2 * b - 2) * W - b * (b - 1) * d) * gz1) ≤
          m * (2 * ((2 * b - 2) * W - b * (b - 1) * d) * gz2) := by
        have hmul := Nat.mul_le_mul_left (2 * ((2 * b - 2) * W - b * (b - 1) * d)) hgz
        linarith
      have h2 : m' * (2 * W * m) = m * (2 * W * m') := by ring
      linarith
    · simp only [ht1, ht2, ↓reduceIte]
      exact le_of_eq (by ring)
  set ls1 := (gz1 + m) * n
  set ls2 := (gz2 + m') * n
  have hls : m' * ls1 ≤ m * ls2 := by
    have h1 : m' * (gz1 + m) ≤ m * (gz2 + m') := by
      have : m' * m = m * m' := Nat.mul_comm _ _
      linarith
    dsimp only [ls1, ls2]
    rw [← Nat.mul_assoc, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_right n h1
  set ord1 := (2 * t * ls1 + n * (2 * ht1 + m * n)) / (t * t - n * d)
  set ord2 := ceilDiv (2 * t * ls2 + n * (2 * ht2 + m' * n)) (t * t - n * d)
  have hord : m' * ord1 ≤ m * ord2 := by
    apply mul_div_le_mul_ceilDiv hD0
    have h1 := Nat.mul_le_mul_left (2 * t) hls
    have h2 := Nat.mul_le_mul_left (2 * n) hht
    have h3 : m' * (n * (m * n)) = m * (n * (m' * n)) := by ring
    linarith
  have hmin_scale : ∀ x₁ y₁ x₂ y₂ : ℕ, m' * x₁ ≤ m * x₂ → m' * y₁ ≤ m * y₂ →
      m' * min x₁ y₁ ≤ m * min x₂ y₂ := by
    intro x₁ y₁ x₂ y₂ hx hy
    rcases le_total x₂ y₂ with hxy | hyx
    · rw [min_eq_left hxy]; exact (Nat.mul_le_mul_left m' (min_le_left x₁ y₁)).trans hx
    · rw [min_eq_right hyx]; exact (Nat.mul_le_mul_left m' (min_le_right x₁ y₁)).trans hy
  have hfold :
      m' * (polarTiers sg).foldl
        (fun acc p => if p.1 * (p.1 - 1) < m then min acc (polarPop sg b m ls1 ht1 t p.1 p.2) else acc) ord1 ≤
      m * (polarTiers sg).foldl
        (fun acc p => if p.1 * (p.1 - 1) < m' then min acc (polarPopCeil sg b m' ls2 ht2 t p.1 p.2) else acc) ord2 := by
    apply foldl_min_scale
    · intro p hp a c hac
      by_cases hp' : p.1 * (p.1 - 1) < m'
      · have hpm : p.1 * (p.1 - 1) < m := htier p hp hp'
        simp only [hp', hpm, ↓reduceIte]
        apply hmin_scale _ _ _ _ hac
        unfold polarPop polarPopCeil
        dsimp only
        have hbez : m' * (if sg then p.1 * b * (2 * m - b - 1) else p.1 * m * (m - 1)) ≤
            m * (if sg then p.1 * b * (2 * m' - b - 1) else p.1 * m' * (m' - 1)) := by
          cases sg
          · simp only [Bool.false_eq_true, ↓reduceIte]
            have h1 : m - 1 ≤ m' - 1 := by omega
            have h2 := Nat.mul_le_mul_left (p.1 * m * m') h1
            linarith
          · simp only [↓reduceIte]
            have h1 : b + 1 ≤ 2 * m := by omega
            have h2 : b + 1 ≤ 2 * m' := by omega
            have heq1 : m' * (2 * m - b - 1) + m' * (b + 1) = m' * (2 * m) := by
              rw [← Nat.mul_add]; congr 1; omega
            have heq2 : m * (2 * m' - b - 1) + m * (b + 1) = m * (2 * m') := by
              rw [← Nat.mul_add]; congr 1; omega
            have h3 : m * (b + 1) ≤ m' * (b + 1) := Nat.mul_le_mul_right _ hmm'
            have h4 : m' * (2 * m - b - 1) ≤ m * (2 * m' - b - 1) := by nlinarith
            have h5 := Nat.mul_le_mul_left (p.1 * b) h4
            linarith
        have hdiv : m' * (((p.1 + 2) * (p.1 + 1) / 2) * (p.2 * ls1 + p.1 * ht1) / polarGap p.1 p.2 t) ≤
            m * ceilDiv (((p.1 + 2) * (p.1 + 1) / 2) * (p.2 * ls2 + p.1 * ht2)) (polarGap p.1 p.2 t) := by
          apply mul_div_le_mul_ceilDiv (hgap p hp)
          have h1 := Nat.mul_le_mul_left p.2 hls
          have h2 := Nat.mul_le_mul_left p.1 hht
          have h3 : m' * (p.2 * ls1 + p.1 * ht1) ≤ m * (p.2 * ls2 + p.1 * ht2) := by linarith
          have h4 := Nat.mul_le_mul_left ((p.1 + 2) * (p.1 + 1) / 2) h3
          linarith
        linarith
      · by_cases hpm : p.1 * (p.1 - 1) < m
        · simp only [hp', hpm, ↓reduceIte]
          exact (Nat.mul_le_mul_left m' (min_le_left _ _)).trans hac
        · simp only [hp', hpm, ↓reduceIte]
          exact hac
    · exact hord
  have h2bm : m' * (2 * b * m) = m * (2 * b * m') := by ring
  linarith

private def tierEnd (sg : Bool) (m srem : ℕ) : ℕ :=
  if sg then
    if m ≤ 6 then min 6 srem
    else if m ≤ 12 then min 12 srem
    else srem
  else
    if m ≤ 6 then min 6 srem
    else if m ≤ 12 then min 12 srem
    else if m ≤ 20 then min 20 srem
    else if m ≤ 30 then min 30 srem
    else if m ≤ 42 then min 42 srem
    else if m ≤ 56 then min 56 srem
    else if m ≤ 72 then min 72 srem
    else if m ≤ 90 then min 90 srem
    else if m ≤ 110 then min 110 srem
    else srem

private lemma mem_unitEndpoints_srem (w : Window) {j : ℕ}
    (hlt : w.degree₁ - j < w.second - j) : w.second - j ∈ unitEndpoints w j := by
  unfold unitEndpoints
  exact List.mem_append_right _ (List.mem_append_right _ (by simp [hlt]))

private lemma mem_unitEndpoints_min_cutoff (w : Window) {j c : ℕ}
    (hc : c ∈ tierCutoffs w.sparseGauss) (hbc : w.degree₁ - j < c)
    (hlt : w.degree₁ - j < w.second - j) :
    min c (w.second - j) ∈ unitEndpoints w j := by
  by_cases hle : c ≤ w.second - j
  · rw [min_eq_left hle]
    unfold unitEndpoints
    exact List.mem_append_right _ (List.mem_append_left _
      (List.mem_filter.mpr ⟨hc, by simp [hbc, hle]⟩))
  · rw [min_eq_right (by omega)]
    exact mem_unitEndpoints_srem w hlt

private lemma tierEnd_props (w : Window) {j m : ℕ}
    (hb2 : 2 ≤ w.degree₁ - j) (hgt : w.degree₁ - j < m) (hmhi : m ≤ w.second - j) :
    let m' := tierEnd w.sparseGauss m (w.second - j)
    m ≤ m' ∧ m' ≤ w.second - j ∧ m' ∈ unitEndpoints w j ∧
    ∀ p ∈ polarTiers w.sparseGauss, p.1 * (p.1 - 1) < m' → p.1 * (p.1 - 1) < m := by
  dsimp only
  have hlt : w.degree₁ - j < w.second - j := by omega
  have hmem_c : ∀ c ∈ tierCutoffs w.sparseGauss, m ≤ c → min c (w.second - j) ∈ unitEndpoints w j :=
    fun c hc hmc => mem_unitEndpoints_min_cutoff w hc (by omega) hlt
  cases hsg : w.sparseGauss
  · dsimp only [tierEnd]
    have hc_list : tierCutoffs false = [6, 12, 20, 30, 42, 56, 72, 90, 110] := rfl
    have hpt_list : polarTiers false =
        [(2, 1), (3, 2), (4, 2), (5, 3), (6, 4), (7, 4), (8, 5), (9, 5), (10, 6), (11, 7)] := rfl
    simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs
    all_goals refine ⟨by omega, by omega, ?_, ?_⟩
    all_goals first
      | exact hmem_c _ (by rw [hsg, hc_list]; simp) (by omega)
      | exact mem_unitEndpoints_srem w hlt
      | (intro p hp hlt'
         rw [hpt_list] at hp
         simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
         rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
           (dsimp only at hlt' ⊢; omega))
  · dsimp only [tierEnd]
    have hc_list : tierCutoffs true = [6, 12] := rfl
    have hpt_list : polarTiers true = [(2, 1), (3, 2), (4, 2)] := rfl
    simp only [↓reduceIte]
    split_ifs
    all_goals refine ⟨by omega, by omega, ?_, ?_⟩
    all_goals first
      | exact hmem_c _ (by rw [hsg, hc_list]; simp) (by omega)
      | exact mem_unitEndpoints_srem w hlt
      | (intro p hp hlt'
         rw [hpt_list] at hp
         simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
         rcases hp with rfl | rfl | rfl <;> (dsimp only at hlt' ⊢; omega))

private lemma mem_maxUnitPrice {w : Window} {j m' : ℕ}
    (hmem : m' ∈ unitEndpoints w j)
    (hm2 : 2 ≤ m') (hb2 : 2 ≤ min (w.degree₁ - j) m')
    (hW : min (w.degree₁ - j) m' * d ≤ w.order₁ * (n - w.errors) - 1 - j * d) :
    ceilDiv (componentCapCeil w.sparseGauss (min (w.degree₁ - j) m') m'
      (w.order₁ * (n - w.errors) - 1 - j * d) (n - w.errors)) m' ≤ maxUnitPrice w j := by
  have hfn := foldl_max_ge_mem (unitEndpoints w j) (unitTerm w j) hmem w.linMult
  have hval : unitTerm w j m' =
      ceilDiv (componentCapCeil w.sparseGauss (min (w.degree₁ - j) m') m'
        (w.order₁ * (n - w.errors) - 1 - j * d) (n - w.errors)) m' := by
    unfold unitTerm
    dsimp only
    split_ifs with h
    · exfalso
      rcases h with h1 | h2 | h3
      · exact (Nat.not_lt.mpr hm2) h1
      · exact (Nat.not_lt.mpr hb2) h2
      · exact (Nat.not_lt.mpr hW) h3
    · rfl
  rw [hval] at hfn
  exact hfn

/-- Every nonlinear common factor `(b, m)` with `2 ≤ b ≤ min (degree₁ - j) m` and `m ≤ second - j`
is bounded by `m * maxUnitPrice (win i) j`. -/
theorem componentCap_le_mul_maxUnitPrice (i : Fin 4) {j b m : ℕ}
    (hj : j ≤ (win i).degree₁) (hb2 : 2 ≤ b) (hb_hi : b ≤ (win i).degree₁ - j)
    (hbm : b ≤ m) (hm_hi : m ≤ (win i).second - j) :
    componentCap (win i).sparseGauss b m
      ((win i).order₁ * (n - (win i).errors) - 1 - j * d) (n - (win i).errors) ≤
      m * maxUnitPrice (win i) j := by
  have hhyp := hypotheses i
  set w := win i
  set t := n - w.errors
  set W := w.order₁ * t - 1 - j * d
  set b' := min (w.degree₁ - j) m
  have hb'_ge : b ≤ b' := le_min hb_hi hbm
  have hb'_m : b' ≤ m := min_le_right _ _
  have hb'_v : b' ≤ w.degree₁ - j := min_le_left _ _
  have hW_full : w.degree₁ * d ≤ w.order₁ * t - 1 := hhyp.2.2.2.2.2.1
  have hW_dbl : (2 * w.degree₁ + 1) * d ≤ 2 * (w.order₁ * t - 1) := hhyp.2.2.2.2.2.2.1
  have hW2 : b' * d ≤ W := by
    have h1 : (b' + j) * d ≤ w.degree₁ * d := Nat.mul_le_mul_right d (by omega)
    have h2 : b' * d + j * d ≤ w.order₁ * t - 1 := by
      rw [← Nat.add_mul]; exact h1.trans hW_full
    exact Nat.le_sub_of_add_le h2
  have hW1 : (2 * b' - 1) * d ≤ 2 * W := by
    have h1 : ((2 * b' + 1) + 2 * j) * d ≤ (2 * w.degree₁ + 1) * d :=
      Nat.mul_le_mul_right d (by omega)
    have h2 : (2 * b' + 1) * d + 2 * (j * d) ≤ 2 * (w.order₁ * t - 1) := by
      rw [← Nat.mul_assoc, ← Nat.add_mul]; exact h1.trans hW_dbl
    have h3 : (2 * b' - 1) * d ≤ (2 * b' + 1) * d := Nat.mul_le_mul_right d (by omega)
    have h4 : (2 * b' - 1) * d + 2 * (j * d) ≤ 2 * (w.order₁ * t - 1) :=
      (Nat.add_le_add_right h3 _).trans h2
    have hsub : 2 * W = 2 * (w.order₁ * t - 1) - 2 * (j * d) := Nat.mul_sub_left_distrib 2 _ _
    rw [hsub]
    exact Nat.le_sub_of_add_le h4
  have hmono : componentCap w.sparseGauss b m W t ≤ componentCap w.sparseGauss b' m W t :=
    componentCap_mono_b (by omega) hb'_ge hb'_m hW1 hW2
  have hD0 : 0 < t * t - n * d := Nat.sub_pos_of_lt hhyp.1
  have hgap : ∀ p ∈ polarTiers w.sparseGauss, 0 < polarGap p.1 p.2 t := by
    intro p hp
    have hall := List.all_eq_true.mp hhyp.2.2.2.2.2.2.2 p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
    exact hall.2
  have hscale : ∀ m', m ≤ m' → m' ∈ unitEndpoints w j → min (w.degree₁ - j) m' = b' →
      (∀ p ∈ polarTiers w.sparseGauss, p.1 * (p.1 - 1) < m' → p.1 * (p.1 - 1) < m) →
      componentCap w.sparseGauss b' m W t ≤ m * maxUnitPrice w j := by
    intro m' hmm' hmem hbe htier
    have hmul := componentCap_mul_le_ceil (W := W) (by omega) hb'_m hmm' hD0 hgap htier
    have hunit := mem_maxUnitPrice hmem (by omega) (by rw [hbe]; omega) (by rw [hbe]; exact hW2)
    rw [hbe] at hunit
    have hceil : componentCapCeil w.sparseGauss b' m' W t ≤
        m' * ceilDiv (componentCapCeil w.sparseGauss b' m' W t) m' := by
      unfold ceilDiv
      have hmpos : 0 < m' := by omega
      have hdiv := Nat.div_add_mod (componentCapCeil w.sparseGauss b' m' W t + m' - 1) m'
      have hmod := Nat.mod_lt (componentCapCeil w.sparseGauss b' m' W t + m' - 1) hmpos
      omega
    have hstep : m' * componentCap w.sparseGauss b' m W t ≤ m' * (m * maxUnitPrice w j) := by
      calc m' * componentCap w.sparseGauss b' m W t
          ≤ m * componentCapCeil w.sparseGauss b' m' W t := hmul
        _ ≤ m * (m' * ceilDiv (componentCapCeil w.sparseGauss b' m' W t) m') :=
          Nat.mul_le_mul_left m hceil
        _ ≤ m * (m' * maxUnitPrice w j) := Nat.mul_le_mul_left m (Nat.mul_le_mul_left m' hunit)
        _ = m' * (m * maxUnitPrice w j) := by ring
    exact Nat.le_of_mul_le_mul_left hstep (by omega)
  by_cases hsmall : m ≤ w.degree₁ - j
  · have hmem : m ∈ unitEndpoints w j := by
      unfold unitEndpoints
      exact List.mem_append_left _ (List.mem_range.mpr (by omega))
    exact hmono.trans (hscale m le_rfl hmem rfl (fun _ _ h => h))
  · push Not at hsmall
    obtain ⟨hmm', hm'hi, hmem, htier⟩ := tierEnd_props w (by omega) hsmall hm_hi
    have hbe : min (w.degree₁ - j) (tierEnd w.sparseGauss m (w.second - j)) = b' := by
      dsimp only [b']; omega
    exact hmono.trans (hscale _ hmm' hmem hbe htier)

/-- Any nonaffine common linear factor of total degree `m` obeys `m * linMult ≤ m * maxUnitPrice`. -/
theorem linMult_le_maxUnitPrice (w : Window) (j : ℕ) : w.linMult ≤ maxUnitPrice w j := by
  unfold maxUnitPrice
  exact foldl_max_ge_init _ _ _

/-- **Shared-degree allocation theorem**: across all four windows and every head count
`j ≤ degree₁`, combining scalar-only factors, the single noncommon resultant, small polynomial
affine heads, and any collection of common nonaffine linear + nonlinear factors sharing the
companion degree sum `∑ deg ≤ second - j` fits inside `residualBudget (win i) j`, and any
non-exceptional head family fits inside `(win i).ordBound ≤ 2n`. -/
theorem all_non_exceptional_allocations {ι : Type*} (S : Finset ι) (deg pop : ι → ℕ)
    (i : Fin 4) {j heads scalar noncommon small : ℕ}
    (hj : j ≤ (win i).degree₁)
    (hheads : heads ≤ ordinaryHeadMass (win i) j)
    (hscalar : scalar ≤ (win i).first)
    (hnoncommon : noncommon ≤ (win i).first * (win i).degree₂ + (win i).degree₁ * (win i).second)
    (hsmall : small ≤ ((win i).degree₁ - j) * (win i).cutoff)
    (hdeg : ∑ a ∈ S, deg a ≤ (win i).second - j)
    (hpop : ∀ a ∈ S, pop a ≤ deg a * maxUnitPrice (win i) j) :
    heads + scalar + noncommon + small + ∑ a ∈ S, pop a ≤ (win i).ordBound ∧
    (win i).ordBound ≤ budget := by
  have hwb := window_budgets i
  have hsum : ∑ a ∈ S, pop a ≤ ((win i).second - j) * maxUnitPrice (win i) j := by
    calc
      ∑ a ∈ S, pop a ≤ ∑ a ∈ S, deg a * maxUnitPrice (win i) j := sum_le_sum hpop
      _ = (∑ a ∈ S, deg a) * maxUnitPrice (win i) j := (sum_mul S deg _).symm
      _ ≤ ((win i).second - j) * maxUnitPrice (win i) j := Nat.mul_le_mul_right _ hdeg
  have hmem : j ∈ List.range ((win i).degree₁ + 1) := List.mem_range.mpr (by omega)
  have hle : ordinaryHeadMass (win i) j + residualBudget (win i) j ≤ (win i).ordBound := by
    have hall := List.all_eq_true.mp hwb.2.2 j hmem
    exact of_decide_eq_true hall
  unfold residualBudget fixedResidual at hle
  exact ⟨by omega, hwb.2.1⟩

private lemma sum_fin_eq_list_range (m : ℕ) (f : ℕ → ℕ) :
    (∑ j : Fin m, f j.val) = ((List.range m).map f).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc, List.range_succ, List.map_append, List.sum_append]
    simp [ih]

/-- Closed-form list count for `JetRows s r`. -/
def jetRowCount (s r : ℕ) : ℕ :=
  ((List.range r).map fun j => (r - j) * (s + 1 - j)).sum

/-- Closed-form list count for `Monomials s b d W`. -/
def monomialCount (s b d_ W : ℕ) : ℕ :=
  ((List.range (b + 1)).map fun j => (s + 1 - j) * (W - j * d_)).sum

private lemma card_jetRows_eq (s r : ℕ) : Fintype.card (JetRows s r) = jetRowCount s r := by
  unfold JetRows jetRowCount
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  exact sum_fin_eq_list_range r (fun j => (r - j) * (s + 1 - j))

private lemma card_monomials_eq (s b d_ W : ℕ) :
    Fintype.card (Monomials s b d_ W) = monomialCount s b d_ W := by
  unfold Monomials monomialCount
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  exact sum_fin_eq_list_range (b + 1) (fun j => (s + 1 - j) * (W - j * d_))

/-- Strict positive mixed-Hasse coefficient surplus for all eight production surfaces. -/
theorem surface_ranks : ∀ (i : Fin 4) (second : Bool),
    let w := win i
    let t := n - w.errors
    let r := if second then w.order₂ else w.order₁
    let b := if second then w.degree₂ else w.degree₁
    let s := if second then w.second else w.first
    0 < r ∧ 0 < t ∧ r ≤ s + 1 ∧
    n * jetRowCount s r < monomialCount s b d (r * t) := by
  decide +kernel

/-- Both mixed-Hasse trivariate interpolants exist on any `Fintype` domain of size `n = 2^30`
for all four production windows (`i : Fin 4`, `second : Bool`). -/
theorem surfaces {F : Type} [Field F] {ι : Type*} [Fintype ι]
    (dom : ι ↪ F) (u v : ι → F) (hn : Fintype.card ι = n) (i : Fin 4) (second : Bool) :
    let w := win i
    let t := n - w.errors
    let r := if second then w.order₂ else w.order₁
    let b := if second then w.degree₂ else w.degree₁
    let s := if second then w.second else w.first
    ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
      (∀ j h x, ((Q.coeff j).coeff h).coeff x ≠ 0 → j ≤ b ∧ h + j ≤ s ∧ x + j * d < r * t) ∧
      ∀ z : F, ∀ q : F[X], q.natDegree ≤ d → ∀ B : Finset ι, t ≤ B.card →
        (∀ x ∈ B, q.eval (dom x) = u x + z * v x) → Q.eval₂ (evalRingHom (C z)) q = 0 := by
  dsimp only
  let w := win i
  let t := n - w.errors
  let r := if second then w.order₂ else w.order₁
  let b := if second then w.degree₂ else w.degree₁
  let s := if second then w.second else w.first
  have hrank := surface_ranks i second
  dsimp only at hrank
  obtain ⟨hr, ht, hrs, hlt⟩ := hrank
  have hnum : Fintype.card ι * Fintype.card (JetRows s r) < Fintype.card (Monomials s b d (r * t)) := by
    rw [hn, card_jetRows_eq, card_monomials_eq]
    exact hlt
  obtain ⟨c, hc, _, hf⟩ := exists_surface dom u v hr ht hrs hnum
  exact ⟨surface c, surface_ne_zero hc, fun _ _ _ h => surface_support c h,
    fun z q hq B hB hg => by rw [surface_eval]; exact hf z q hq B hB hg⟩

/-! ## Section 3: Sharpened `671,088,640` orbit and collision floors -/

/-- Under the tightened `671,088,640` residual allowances:
1. **Pure L1+L2** (`other ≤ 2,280,700`): a saturated four-head overrun needs at least
   **`267,295,101`** distinct double-site direction orbits (within `1,140,353` of the 2-to-1
   double-site threshold `2d = 268,435,454`, out of `4d = 536,870,908` total double sites).
2. **Sparse-Gauss** (`other ≤ 397,364`): a saturated four-head overrun needs at least
   **`268,236,769`** distinct double-site direction orbits (within `198,685` of the 2-to-1
   double-site threshold `2d = 268,435,454`, i.e., `> 49.963%` of all `4d = 536,870,908`
   double sites).
3. **Profile `(1, 1, 1, 5)` collision cap**: with `other ≤ 397,364`, any `(1, 1, 1, 5)`
   overrun can have at most **`397,367`** total fresh-label collisions across all four heads. -/
theorem sharpened_orbit_and_collision_floors :
    (∀ (B heads other : ℕ), heads ≤ 2 * B + 3 * (n - 4 * d) → other ≤ 2280700 →
      budget < heads + other → 267295101 ≤ B) ∧
    (∀ (B heads other : ℕ), heads ≤ 2 * B + 3 * (n - 4 * d) → other ≤ 397364 →
      budget < heads + other → 268236769 ≤ B ∧ 2 * d - B ≤ 198685) ∧
    (∀ (heads collisions other : ℕ),
      heads + collisions ≤ 3 * (671088640 + 1) + (1 + 671088640 / 5) →
      other ≤ 397364 → budget < heads + other → collisions ≤ 397367) := by
  simp only [n, d, budget]
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> omega

#print axioms componentCap_mono_b
#print axioms hypotheses
#print axioms window_budgets
#print axioms componentCap_le_mul_maxUnitPrice
#print axioms linMult_le_maxUnitPrice
#print axioms all_non_exceptional_allocations
#print axioms surface_ranks
#print axioms surfaces
#print axioms sharpened_orbit_and_collision_floors

end ArkLib.ProximityGap.Frontier.EighthSuccessorTightWindow

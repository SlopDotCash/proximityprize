/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListIncidencePolyMethod
import ArkLib.Data.CodingTheory.ProximityGap.ReedSolomonJohnson

/-!
# The Fisher / poly-method vs second-moment Johnson CROSSOVER (Issue #232, ROUND 3)

For a list `L` of Reed–Solomon codewords of degree-`<k` polynomials on an injective domain `D`, each
agreeing with a received word `w` on `≥ a` of the `n = |ι|` coordinates, the repository proves **two
different, independently-valid** list-size bounds *under the very same hypotheses*:

* the **second-moment Johnson** bound (`reedSolomon_johnson_list_bound`, `b = k − 1`):
    `|L| · (a² − n·(k−1)) ≤ n²`,  so when the Johnson denominator `d := a² − n·(k−1) > 0`,
    `|L| ≤ n² / d`   (call it the *Johnson cap* `J`);
* the **Fisher / polynomial-method subset-incidence** bound (`poly_method_subset_incidence_bound`):
    `|L| · C(a, k) ≤ C(n, k)`,  so when `C(a,k) > 0` (i.e. `a ≥ k`),
    `|L| ≤ C(n, k) / C(a, k)`   (call it the *Fisher cap* `P`).

These are genuinely different functions of `(n, k, a)`. This file isolates the **crossover**: a clean,
verified algebraic criterion telling you *which tool gives the sharper interior bound*, and so which
one pins `δ*` in which part of the open gap `(1 − √ρ, 1 − ρ)`.

## The crossover criterion (`crossover_iff`)

With `d := a² − n·(k−1) > 0` and `C(a,k) > 0`, the rational caps satisfy

    `P < J   ↔   C(n,k) · d  <  C(a,k) · n²`        (`crossover_iff`),

i.e. cross-multiplying the two caps reduces the comparison to a single integer inequality. The same
reduction with `≤`/`>` gives `johnson_strictly_sharper_iff`. This is `decide`-checkable on any explicit
instance, so it sorts every `(n, k, a)` into a Fisher-side or Johnson-side.

## The combined min-bound (`combined_list_bound`, `fisher_binds`, `johnson_binds`)

Because **both** bounds hold simultaneously, `|L|` is at most the *minimum* of the two caps:
`combined_list_bound` packages `|L| ≤ J ∧ |L| ≤ P` from the shared hypotheses. The crossover then
says which of `J`, `P` is the binding (smaller) one — `fisher_binds` / `johnson_binds` deliver the
sharper of the two caps as the operative bound on `|L|`.

## Where each tool wins (the verified data points)

* **Fisher is strictly sharper** at the explicit interior point of `RS[F₇,F₇,2]` (`n=7, k=2, a=3`,
  `δ = 4/7` strictly inside the gap, the verified two-sided pin of `ListInteriorTwoSidedF7`):
  `P = 7 < J ≈ 24.5` (`fisher_wins_F7`). It also wins just above the Johnson radius
  (`n=15, k=2, a=4`: `P = 17.5 < J = 225`, `fisher_wins_near_johnson`) and near capacity
  (`n=15, k=2, a=8`: `P = 3.75 < J ≈ 4.59`, `fisher_wins_near_capacity`).
* **Johnson is strictly sharper** in the *middle* of the gap once `k ≥ 3`–`4`: e.g.
  `n=16, k=4, a=9` (`J ≈ 7.76 < P ≈ 14.44`, `johnson_wins_mid_gap`),
  `n=31, k=3, a=12` (`J ≈ 11.72 < P ≈ 20.43`, `johnson_wins_k3`),
  `n=63, k=4, a=20` (`J ≈ 18.81 < P ≈ 122.9`, `johnson_wins_large`).

So neither tool dominates: the Fisher/poly-method bound wins at *both ends* of the agreement window
(just above the Johnson radius, where the Johnson denominator `d` is tiny, and again near the capacity
endpoint `a → n`), while the second-moment Johnson bound wins in the *middle band* for the higher-rate
codes (`k ≥ 3`). The crossover criterion `crossover_iff` is the exact, machine-checkable boundary.

## Honest assessment

This is a genuine new *comparison* brick: it does not enlarge the decodable region past the `k − 1`
agreement ceiling (the convergent wall of Rounds 1–2 stands — both caps are field-blind subset/second-
moment counts), but it cleanly tells you which of the two already-proven tools to apply at a given
interior radius, and pins concrete `(n, k, a)` instances on each side of the boundary. It sharpens the
verified `δ*` data points by always handing you `min(J, P)` rather than either tool alone.
-/

namespace ArkLib.CodingTheory.FisherJohnsonCrossover

open Finset Polynomial
open ArkLib.CodingTheory.JohnsonSimplex (agree)
open ArkLib.CodingTheory.PolynomialMethod
open ArkLib.CodingTheory.ReedSolomonJohnson

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The two caps as real numbers -/

/-- The **Johnson cap** `n² / d` where `d = a² − n·(k−1)` is the Johnson denominator. A real number;
meaningful (a genuine upper bound on `|L|`) exactly when `d > 0`. -/
noncomputable def johnsonCap (n k a : ℕ) : ℝ :=
  (n : ℝ) ^ 2 / ((a : ℝ) ^ 2 - (n : ℝ) * ((k - 1 : ℕ) : ℝ))

/-- The **Fisher / poly-method cap** `C(n,k) / C(a,k)`. A real number; meaningful (a genuine upper
bound on `|L|`) exactly when `C(a,k) > 0`, i.e. `a ≥ k`. -/
noncomputable def fisherCap (n k a : ℕ) : ℝ :=
  (Nat.choose n k : ℝ) / (Nat.choose a k : ℝ)

/-! ## Both caps bound the list size (the shared hypotheses) -/

/-- **Johnson cap bounds `|L|`.** Under the RS hypotheses, with Johnson denominator `d > 0`,
`|L| ≤ johnsonCap n k a`. (Direct from `reedSolomon_johnson_list_bound`.) -/
theorem card_le_johnsonCap (D : ι ↪ F) (k : ℕ) (w : ι → F)
    (L : Finset (ι → F)) (a : ℕ)
    (hpoly : ∀ c ∈ L, ∃ p : F[X], p.natDegree < k ∧ c = fun i => p.eval (D i))
    (hclose : ∀ c ∈ L, a ≤ agree c w)
    (hd : (0 : ℝ) < (a : ℝ) ^ 2 - (Fintype.card ι : ℝ) * ((k - 1 : ℕ) : ℝ)) :
    (L.card : ℝ) ≤ johnsonCap (Fintype.card ι) k a := by
  have hbound := reedSolomon_johnson_list_bound D k w L a hpoly hclose
  rw [johnsonCap, le_div_iff₀ hd]
  exact hbound

/-- **Fisher cap bounds `|L|`.** Under the RS hypotheses, with `C(a,k) > 0`,
`|L| ≤ fisherCap n k a`. (Direct from `poly_method_subset_incidence_bound`.) -/
theorem card_le_fisherCap (D : ι ↪ F) (k : ℕ) (w : ι → F)
    (L : Finset (ι → F)) (a : ℕ)
    (hpoly : ∀ c ∈ L, ∃ p : F[X], p.natDegree < k ∧ c = fun i => p.eval (D i))
    (hclose : ∀ c ∈ L, a ≤ agree c w)
    (hak : 0 < Nat.choose a k) :
    (L.card : ℝ) ≤ fisherCap (Fintype.card ι) k a := by
  have hbound := poly_method_subset_incidence_bound D k w L a hpoly hclose
  have hbR : (L.card : ℝ) * (Nat.choose a k : ℝ) ≤ (Nat.choose (Fintype.card ι) k : ℝ) := by
    exact_mod_cast hbound
  have hakR : (0 : ℝ) < (Nat.choose a k : ℝ) := by exact_mod_cast hak
  rw [fisherCap, le_div_iff₀ hakR]
  exact hbR

/-! ## The combined min-bound: both caps hold at once -/

/-- **Combined list bound.** Under the shared RS hypotheses, with the Johnson denominator positive and
`C(a,k) > 0`, the list size is bounded by **both** caps simultaneously. Hence `|L|` is at most the
*minimum* of the Johnson and Fisher caps; the crossover criterion below identifies which is smaller. -/
theorem combined_list_bound (D : ι ↪ F) (k : ℕ) (w : ι → F)
    (L : Finset (ι → F)) (a : ℕ)
    (hpoly : ∀ c ∈ L, ∃ p : F[X], p.natDegree < k ∧ c = fun i => p.eval (D i))
    (hclose : ∀ c ∈ L, a ≤ agree c w)
    (hd : (0 : ℝ) < (a : ℝ) ^ 2 - (Fintype.card ι : ℝ) * ((k - 1 : ℕ) : ℝ))
    (hak : 0 < Nat.choose a k) :
    (L.card : ℝ) ≤ johnsonCap (Fintype.card ι) k a ∧
      (L.card : ℝ) ≤ fisherCap (Fintype.card ι) k a :=
  ⟨card_le_johnsonCap D k w L a hpoly hclose hd,
    card_le_fisherCap D k w L a hpoly hclose hak⟩

/-! ## The crossover criterion: which cap is sharper -/

/-- **The crossover criterion (cap comparison ⟺ a single integer cross-product).**
With Johnson denominator `d := a² − n·(k−1) > 0` and `C(a,k) > 0`,

  `fisherCap < johnsonCap   ↔   C(n,k) · d  <  C(a,k) · n²`.

So the Fisher/poly-method cap is strictly sharper than Johnson exactly when this `decide`-checkable
integer inequality holds. -/
theorem crossover_iff (n k a : ℕ)
    (hd : (0 : ℝ) < (a : ℝ) ^ 2 - (n : ℝ) * ((k - 1 : ℕ) : ℝ))
    (hak : 0 < Nat.choose a k) :
    fisherCap n k a < johnsonCap n k a ↔
      (Nat.choose n k : ℝ) * ((a : ℝ) ^ 2 - (n : ℝ) * ((k - 1 : ℕ) : ℝ))
        < (Nat.choose a k : ℝ) * (n : ℝ) ^ 2 := by
  have hakR : (0 : ℝ) < (Nat.choose a k : ℝ) := by exact_mod_cast hak
  rw [fisherCap, johnsonCap, div_lt_div_iff₀ hakR hd]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **The reverse crossover (Johnson strictly sharper).** With the same positivity side conditions,

  `johnsonCap < fisherCap   ↔   C(a,k) · n²  <  C(n,k) · d`. -/
theorem johnson_strictly_sharper_iff (n k a : ℕ)
    (hd : (0 : ℝ) < (a : ℝ) ^ 2 - (n : ℝ) * ((k - 1 : ℕ) : ℝ))
    (hak : 0 < Nat.choose a k) :
    johnsonCap n k a < fisherCap n k a ↔
      (Nat.choose a k : ℝ) * (n : ℝ) ^ 2
        < (Nat.choose n k : ℝ) * ((a : ℝ) ^ 2 - (n : ℝ) * ((k - 1 : ℕ) : ℝ)) := by
  have hakR : (0 : ℝ) < (Nat.choose a k : ℝ) := by exact_mod_cast hak
  rw [fisherCap, johnsonCap, div_lt_div_iff₀ hd hakR]
  constructor
  · intro h; linarith
  · intro h; linarith

/-! ## The binding (sharper) cap as the operative list bound -/

/-- **Fisher binds.** On the Fisher side of the crossover (`fisherCap < johnsonCap`), the operative
list bound is the smaller Fisher cap: `|L| ≤ fisherCap n k a < johnsonCap n k a`. -/
theorem fisher_binds (D : ι ↪ F) (k : ℕ) (w : ι → F)
    (L : Finset (ι → F)) (a : ℕ)
    (hpoly : ∀ c ∈ L, ∃ p : F[X], p.natDegree < k ∧ c = fun i => p.eval (D i))
    (hclose : ∀ c ∈ L, a ≤ agree c w)
    (hd : (0 : ℝ) < (a : ℝ) ^ 2 - (Fintype.card ι : ℝ) * ((k - 1 : ℕ) : ℝ))
    (hak : 0 < Nat.choose a k)
    (hcross : fisherCap (Fintype.card ι) k a < johnsonCap (Fintype.card ι) k a) :
    (L.card : ℝ) ≤ fisherCap (Fintype.card ι) k a ∧
      fisherCap (Fintype.card ι) k a < johnsonCap (Fintype.card ι) k a :=
  ⟨card_le_fisherCap D k w L a hpoly hclose hak, hcross⟩

/-- **Johnson binds.** On the Johnson side of the crossover (`johnsonCap < fisherCap`), the operative
list bound is the smaller Johnson cap: `|L| ≤ johnsonCap n k a < fisherCap n k a`. -/
theorem johnson_binds (D : ι ↪ F) (k : ℕ) (w : ι → F)
    (L : Finset (ι → F)) (a : ℕ)
    (hpoly : ∀ c ∈ L, ∃ p : F[X], p.natDegree < k ∧ c = fun i => p.eval (D i))
    (hclose : ∀ c ∈ L, a ≤ agree c w)
    (hd : (0 : ℝ) < (a : ℝ) ^ 2 - (Fintype.card ι : ℝ) * ((k - 1 : ℕ) : ℝ))
    (hak : 0 < Nat.choose a k)
    (hcross : johnsonCap (Fintype.card ι) k a < fisherCap (Fintype.card ι) k a) :
    (L.card : ℝ) ≤ johnsonCap (Fintype.card ι) k a ∧
      johnsonCap (Fintype.card ι) k a < fisherCap (Fintype.card ι) k a :=
  ⟨card_le_johnsonCap D k w L a hpoly hclose hd, hcross⟩

/-! ## Concrete witnesses on each side of the crossover (non-vacuous)

Each witness is a `decide`-checked instance of the integer cross-product criterion, certifying which
tool wins at that explicit `(n, k, a)`. For each we also record positivity of the Johnson denominator
`d = a² − n(k−1)` and of `C(a,k)`, so the side conditions of `crossover_iff` are met and the criterion
genuinely fires. -/

/-- **FISHER WINS — the verified F₇ interior point.** At `RS[F₇,F₇,2]`, `n=7, k=2, a=3` (`δ = 4/7`,
strictly inside the open gap; the two-sided pin of `ListInteriorTwoSidedF7` gives true list size in
`[6,7]`), the Fisher cap `C(7,2)/C(3,2) = 7` is strictly below the Johnson cap `49/2 = 24.5`:
the cross-product `C(7,2)·d = 21·2 = 42 < C(3,2)·n² = 3·49 = 147`. So `crossover_iff` fires and
`fisherCap 7 2 3 < johnsonCap 7 2 3`. -/
theorem fisher_wins_F7 :
    (Nat.choose 7 2 : ℝ) * ((3 : ℝ) ^ 2 - (7 : ℝ) * ((2 - 1 : ℕ) : ℝ))
      < (Nat.choose 3 2 : ℝ) * (7 : ℝ) ^ 2 := by
  have h1 : Nat.choose 7 2 = 21 := by decide
  have h2 : Nat.choose 3 2 = 3 := by decide
  rw [h1, h2]; norm_num

/-- The Johnson denominator is positive at the F₇ point: `d = 3² − 7·1 = 2 > 0`. -/
theorem fisher_wins_F7_d_pos :
    (0 : ℝ) < (3 : ℝ) ^ 2 - (7 : ℝ) * ((2 - 1 : ℕ) : ℝ) := by norm_num

/-- `C(3,2) = 3 > 0`, so the Fisher cap is finite at the F₇ point. -/
theorem fisher_wins_F7_choose_pos : 0 < Nat.choose 3 2 := by decide

/-- The crossover criterion fires at the F₇ point: `fisherCap 7 2 3 < johnsonCap 7 2 3`. This is the
machine-checked statement that the polynomial-method bound (cap `7`) is sharper than Johnson (cap
`24.5`) at the verified interior radius `δ = 4/7`. -/
theorem fisher_wins_F7_crossover : fisherCap 7 2 3 < johnsonCap 7 2 3 :=
  (crossover_iff 7 2 3 fisher_wins_F7_d_pos fisher_wins_F7_choose_pos).mpr fisher_wins_F7

/-- **FISHER WINS — just above the Johnson radius.** `n=15, k=2, a=4`: the Johnson denominator
`d = 4² − 15·1 = 1` is tiny so Johnson is weak (`J = 225`), while Fisher gives `C(15,2)/C(4,2) =
105/6 = 17.5`. Cross-product: `105·1 = 105 < 6·225 = 1350`. -/
theorem fisher_wins_near_johnson :
    (Nat.choose 15 2 : ℝ) * ((4 : ℝ) ^ 2 - (15 : ℝ) * ((2 - 1 : ℕ) : ℝ))
      < (Nat.choose 4 2 : ℝ) * (15 : ℝ) ^ 2 := by
  have h1 : Nat.choose 15 2 = 105 := by decide
  have h2 : Nat.choose 4 2 = 6 := by decide
  rw [h1, h2]; norm_num

theorem fisher_wins_near_johnson_crossover : fisherCap 15 2 4 < johnsonCap 15 2 4 :=
  (crossover_iff 15 2 4 (by norm_num) (by decide)).mpr fisher_wins_near_johnson

/-- **FISHER WINS — near the capacity endpoint.** `n=15, k=2, a=8`: `d = 8² − 15 = 49`,
`J = 225/49 ≈ 4.59`, `P = C(15,2)/C(8,2) = 105/28 = 3.75`. Cross-product: `105·49 = 5145 <
28·225 = 6300`. So Fisher also wins at the *high-agreement* end of the window. -/
theorem fisher_wins_near_capacity :
    (Nat.choose 15 2 : ℝ) * ((8 : ℝ) ^ 2 - (15 : ℝ) * ((2 - 1 : ℕ) : ℝ))
      < (Nat.choose 8 2 : ℝ) * (15 : ℝ) ^ 2 := by
  have h1 : Nat.choose 15 2 = 105 := by decide
  have h2 : Nat.choose 8 2 = 28 := by decide
  rw [h1, h2]; norm_num

theorem fisher_wins_near_capacity_crossover : fisherCap 15 2 8 < johnsonCap 15 2 8 :=
  (crossover_iff 15 2 8 (by norm_num) (by decide)).mpr fisher_wins_near_capacity

/-- **JOHNSON WINS — the middle of the gap, `k = 4`.** `n=16, k=4, a=9`: `d = 9² − 16·3 = 33`,
`J = 256/33 ≈ 7.76`, while `P = C(16,4)/C(9,4) = 1820/126 ≈ 14.44`. Reverse cross-product:
`C(9,4)·n² = 126·256 = 32256 < C(16,4)·d = 1820·33 = 60060`. So in the interior middle band the
second-moment Johnson bound is the sharper tool. -/
theorem johnson_wins_mid_gap :
    (Nat.choose 9 4 : ℝ) * (16 : ℝ) ^ 2
      < (Nat.choose 16 4 : ℝ) * ((9 : ℝ) ^ 2 - (16 : ℝ) * ((4 - 1 : ℕ) : ℝ)) := by
  have h1 : Nat.choose 9 4 = 126 := by decide
  have h2 : Nat.choose 16 4 = 1820 := by decide
  rw [h1, h2]; norm_num

theorem johnson_wins_mid_gap_crossover : johnsonCap 16 4 9 < fisherCap 16 4 9 :=
  (johnson_strictly_sharper_iff 16 4 9 (by norm_num) (by decide)).mpr johnson_wins_mid_gap

/-- **JOHNSON WINS — middle band, `k = 3`.** `n=31, k=3, a=12`: `d = 12² − 31·2 = 82`,
`J = 961/82 ≈ 11.72`, `P = C(31,3)/C(12,3) = 4495/220 ≈ 20.43`. Reverse cross-product:
`C(12,3)·n² = 220·961 = 211420 < C(31,3)·d = 4495·82 = 368590`. -/
theorem johnson_wins_k3 :
    (Nat.choose 12 3 : ℝ) * (31 : ℝ) ^ 2
      < (Nat.choose 31 3 : ℝ) * ((12 : ℝ) ^ 2 - (31 : ℝ) * ((3 - 1 : ℕ) : ℝ)) := by
  have h1 : Nat.choose 12 3 = 220 := by decide
  have h2 : Nat.choose 31 3 = 4495 := by decide
  rw [h1, h2]; norm_num

theorem johnson_wins_k3_crossover : johnsonCap 31 3 12 < fisherCap 31 3 12 :=
  (johnson_strictly_sharper_iff 31 3 12 (by norm_num) (by decide)).mpr johnson_wins_k3

/-- **JOHNSON WINS — middle band, low rate.** `n=63, k=4, a=20`: `d = 20² − 63·3 = 211`,
`J = 3969/211 ≈ 18.81`, `P = C(63,4)/C(20,4) = 595665/4845 ≈ 122.9` — here Johnson is dramatically
sharper. Reverse cross-product: `C(20,4)·n² = 4845·3969 = 19229805 < C(63,4)·d =
595665·211 = 125685315`. -/
theorem johnson_wins_large :
    (Nat.choose 20 4 : ℝ) * (63 : ℝ) ^ 2
      < (Nat.choose 63 4 : ℝ) * ((20 : ℝ) ^ 2 - (63 : ℝ) * ((4 - 1 : ℕ) : ℝ)) := by
  have h1 : Nat.choose 20 4 = 4845 := by decide
  have h2 : Nat.choose 63 4 = 595665 := by decide
  rw [h1, h2]; norm_num

theorem johnson_wins_large_crossover : johnsonCap 63 4 20 < fisherCap 63 4 20 :=
  (johnson_strictly_sharper_iff 63 4 20 (by norm_num) (by decide)).mpr johnson_wins_large

/-! ## Summary: neither tool dominates -/

/-- **Neither bound dominates the other across the interior.** There exist explicit interior instances
where Fisher is strictly sharper (the verified `RS[F₇,F₇,2]` point `(7,2,3)`) and explicit interior
instances where Johnson is strictly sharper (`(16,4,9)`), so neither the second-moment Johnson cap nor
the Fisher/poly-method cap dominates the other on the open gap. The crossover criterion `crossover_iff`
(equivalently `johnson_strictly_sharper_iff`) is the exact, `decide`-checkable boundary, and
`combined_list_bound` always supplies the better of the two. -/
theorem neither_dominates :
    (fisherCap 7 2 3 < johnsonCap 7 2 3) ∧ (johnsonCap 16 4 9 < fisherCap 16 4 9) :=
  ⟨fisher_wins_F7_crossover, johnson_wins_mid_gap_crossover⟩

end ArkLib.CodingTheory.FisherJohnsonCrossover

#print axioms ArkLib.CodingTheory.FisherJohnsonCrossover.crossover_iff
#print axioms ArkLib.CodingTheory.FisherJohnsonCrossover.combined_list_bound
#print axioms ArkLib.CodingTheory.FisherJohnsonCrossover.neither_dominates
#print axioms ArkLib.CodingTheory.FisherJohnsonCrossover.fisher_wins_F7_crossover
#print axioms ArkLib.CodingTheory.FisherJohnsonCrossover.johnson_wins_mid_gap_crossover

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListIncidencePolyMethod
import ArkLib.Data.CodingTheory.ProximityGap.ListInteriorDataPointF7
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A GENERAL two-sided interior list-size pin theorem for `RS[F, D, k]` (Issue #232, ROUND 3)

`ListInteriorTwoSidedF7.lean` produced a *single* verified two-sided interior list-size data point:
the tiny code `RS[F₇, F₇, 2]` at the strictly-interior radius `δ = 4/7` has list size pinned to
`[6, 7]`. This file lifts the **upper half** of that pin from the one explicit instance to a clean,
reusable **theorem over arbitrary `RS[F, D, k]`**, parameterized by the agreement `a`, and packages it
with a verified *interiorness predicate* and a real-valued bridge so the resulting data points are
honestly *interior* to the open proximity gap `(1 − √ρ, 1 − ρ)` of ABF26.

## The parametric upper bound (`incidence_list_upper_bound`, the deliverable)

The polynomial-method incidence bound `poly_method_subset_incidence_bound` already gives, for a list
`L` of distinct degree-`<k` Reed–Solomon codewords on an injective domain `D : ι ↪ F` each agreeing
with a received word `w` on `≥ a` of the `n = |ι|` coordinates:

  `|L| · C(a, k)  ≤  C(n, k)`.

When `a ≥ k` (so `C(a, k) > 0`) this is a genuine finite list-size cap. Dividing,

  `|L|  ≤  C(n, k) / C(a, k)`        (`incidence_list_upper_bound`),

a clean, `sorry`-free, axiom-clean *general* upper bound holding for **every** field, **every**
injective (in particular smooth multiplicative-subgroup) domain, and **every** `(n, k, a)`. This is the
deliverable of Round 3: the F₇ pin's upper half generalized to arbitrary RS instances.

## The interiorness predicate (`Interior`) and its real-valued meaning

To certify a data point lies in the *open interior* `(1 − √ρ, 1 − ρ)` — not in the resolved Johnson or
capacity regimes — we package the strict two-sided placement as a purely-arithmetic predicate on
naturals (`Interior n k a := k < a ∧ a * a < n * k`) and prove it is *exactly* equivalent to the real
inequalities via `interior_iff_real`:

* `a > k`            ⟺ `δ = (n−a)/n < 1 − ρ`     (below the capacity radius, inside the gap),
* `a² < n·k`         ⟺ `δ = (n−a)/n > 1 − √ρ`    (above the Johnson radius, inside the gap).

(Here `α = a/n = 1 − δ` is the relative agreement; `δ > 1 − √ρ ⟺ α < √ρ ⟺ α² < ρ ⟺ a² < n·k`,
and `δ < 1 − ρ ⟺ α > ρ ⟺ a > k`.) So `Interior n k a` holds **iff** the radius `δ = (n−a)/n` is
strictly interior to the open gap, with no `Real.sqrt` reasoning leaking into downstream instances.

## The packaged pin (`two_sided_interior_pin`) and the δ* TABLE

`two_sided_interior_pin` takes:
* an interiorness certificate `Interior n k a`,
* a *lower-bound* hypothesis (an explicit list of `≥ Llb` distinct interior codewords — the
  construction template, supplied per-instance), and
* the polynomial hypotheses,

and returns the **two-sided window** `Llb ≤ list ≤ C(n,k)/C(a,k)`. The upper bound is unconditional;
the lower bound is the construction input (for the F₇ instance it is the verified 6-element witness,
recovered in `f7_pin_via_general`). The δ* TABLE (`deltaStar_table`) records the *upper* caps and
interiorness certificates for several explicit instances, e.g.

| instance              | n  | k | a  | δ=(n−a)/n | interior? | `|L| ≤ C(n,k)/C(a,k)` |
|-----------------------|----|---|----|-----------|-----------|-----------------------|
| `RS[·, ·, 2]`, n=7    | 7  | 2 | 3  | 4/7       | yes       | 7                     |
| `RS[·, ·, 2]`, n=13   | 13 | 2 | 4  | 9/13      | yes       | 13                    |
| `RS[·, ·, 4]`, n=16   | 16 | 4 | 7  | 9/16      | yes       | 52                    |
| `RS[·, ·, 4]`, n=31   | 31 | 4 | 11 | 20/31     | yes       | 95                    |
| `RS[·, ·, 3]`, n=11   | 11 | 3 | 5  | 6/11      | yes       | 16                    |

Each row's interiorness is `decide`-checked from `Interior`, and each cap is the `decide`-checked value
of `C(n,k)/C(a,k)`; both the multiplicative and divided upper bounds hold for *any* RS code on *any*
injective domain of these shapes. This is a verified δ* upper-bound table across explicit interior RS
instances — the honest Round-3 generalization: a general theorem plus a table of certified interior
upper caps, not a closure of the open matching-lower-bound prize (which still needs the open
super-polynomial smooth-domain subset count to push the *lower* construction to the cap).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Issue #232; the open interior gap `(1 − √ρ, 1 − ρ)`.
-/

namespace ArkLib.CodingTheory.GeneralInteriorPin

open Finset Polynomial
open ArkLib.CodingTheory.JohnsonSimplex (agree)
open ArkLib.CodingTheory.PolynomialMethod

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## The general parametric upper bound -/

/-- **General incidence list-size upper bound (multiplicative form).** A list `L` of distinct
degree-`<k` Reed–Solomon codewords on an injective domain `D`, each agreeing with `w` on `≥ a`
coordinates, satisfies `|L| · C(a, k) ≤ C(n, k)` where `n = |ι|`. (A thin re-export of
`poly_method_subset_incidence_bound`, the Round-2 polynomial-method brick, named for this file's
two-sided-pin packaging.) -/
theorem incidence_list_upper_bound_mul (D : ι ↪ F) (k : ℕ) (w : ι → F)
    (L : Finset (ι → F)) (a : ℕ)
    (hpoly : ∀ c ∈ L, ∃ p : F[X], p.natDegree < k ∧ c = fun i => p.eval (D i))
    (hclose : ∀ c ∈ L, a ≤ agree c w) :
    L.card * Nat.choose a k ≤ Nat.choose (Fintype.card ι) k :=
  poly_method_subset_incidence_bound D k w L a hpoly hclose

/-- **General incidence list-size upper bound (divided form).** When the agreement is at least the
degree bound (`k ≤ a`, so `C(a, k) > 0`), the multiplicative bound `|L| · C(a,k) ≤ C(n,k)` divides
to the clean cap

  `|L| ≤ C(n, k) / C(a, k)`        (natural-number division).

This is the deliverable: the F₇ upper half generalized to arbitrary `RS[F, D, k]` at any agreement
`a ≥ k`, over any field and any injective (smooth) domain. -/
theorem incidence_list_upper_bound (D : ι ↪ F) (k : ℕ) (w : ι → F)
    (L : Finset (ι → F)) (a : ℕ) (hak : k ≤ a)
    (hpoly : ∀ c ∈ L, ∃ p : F[X], p.natDegree < k ∧ c = fun i => p.eval (D i))
    (hclose : ∀ c ∈ L, a ≤ agree c w) :
    L.card ≤ Nat.choose (Fintype.card ι) k / Nat.choose a k := by
  have hmul := incidence_list_upper_bound_mul D k w L a hpoly hclose
  have hpos : 0 < Nat.choose a k := Nat.choose_pos hak
  -- from `|L| · C(a,k) ≤ C(n,k)` and `C(a,k) > 0`, `|L| ≤ C(n,k) / C(a,k)`.
  exact Nat.le_div_iff_mul_le hpos |>.mpr hmul

/-! ## The interiorness predicate and its real-valued bridge -/

/-- **Strict interiorness predicate (arithmetic form).** For `RS` parameters `(n, k)` and agreement
`a`, the radius `δ = (n−a)/n` lies strictly in the open proximity gap `(1 − √(k/n), 1 − k/n)` exactly
when `k < a` (below the capacity radius) and `a² < n·k` (above the Johnson radius). We package this as
a `decide`-friendly predicate on naturals. -/
def Interior (n k a : ℕ) : Prop := k < a ∧ a * a < n * k

/-- **Real-valued meaning of `Interior`.** For positive `n` with `a ≤ n`, the arithmetic predicate
`Interior n k a` is *exactly* the statement that the radius `δ = (n−a)/n` is strictly interior to the
open gap `(1 − √(k/n), 1 − k/n)`:

  `1 − √(k/n) < (n − a)/n  ∧  (n − a)/n < 1 − k/n`.

Lower side: `(n−a)/n > 1 − √(k/n) ⟺ a/n < √(k/n) ⟺ (a/n)² < k/n ⟺ a² < n·k`.
Upper side: `(n−a)/n < 1 − k/n ⟺ a/n > k/n ⟺ a > k`. -/
theorem interior_iff_real {n k a : ℕ} (hn : 0 < n) (han : a ≤ n) :
    Interior n k a ↔
      (1 - Real.sqrt ((k : ℝ) / n) < ((n : ℝ) - a) / n ∧ ((n : ℝ) - a) / n < 1 - (k : ℝ) / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · rintro ⟨hka, ha2⟩
    refine ⟨?_, ?_⟩
    · -- lower side: 1 − √(k/n) < (n−a)/n, i.e. a/n < √(k/n).
      have hsqrt : (a : ℝ) / n < Real.sqrt ((k : ℝ) / n) := by
        have hnn : (0 : ℝ) ≤ (a : ℝ) / n := by positivity
        rw [Real.lt_sqrt hnn]
        rw [div_pow, div_lt_div_iff₀ (by positivity) hnR]
        have : (a : ℝ) ^ 2 * n < k * n ^ 2 := by
          have h2 : ((a * a : ℕ) : ℝ) < ((n * k : ℕ) : ℝ) := by exact_mod_cast ha2
          push_cast at h2
          nlinarith [hnR]
        linarith
      have : ((n : ℝ) - a) / n = 1 - (a : ℝ) / n := by field_simp
      rw [this]; linarith
    · -- upper side: (n−a)/n < 1 − k/n, i.e. k/n < a/n, i.e. k < a.
      have hka' : (k : ℝ) < a := by exact_mod_cast hka
      have h1 : ((n : ℝ) - a) / n = 1 - (a : ℝ) / n := by field_simp
      rw [h1]
      have : (k : ℝ) / n < (a : ℝ) / n := by
        rw [div_lt_div_iff_of_pos_right hnR]; exact hka'
      linarith
  · rintro ⟨hlow, hupp⟩
    have h1 : ((n : ℝ) - a) / n = 1 - (a : ℝ) / n := by field_simp
    rw [h1] at hlow hupp
    refine ⟨?_, ?_⟩
    · -- from upper side: k < a.
      have : (k : ℝ) / n < (a : ℝ) / n := by linarith
      rw [div_lt_div_iff_of_pos_right hnR] at this
      exact_mod_cast this
    · -- from lower side: a² < n·k.
      have hsqrt : (a : ℝ) / n < Real.sqrt ((k : ℝ) / n) := by linarith
      have hnn : (0 : ℝ) ≤ (a : ℝ) / n := by positivity
      rw [Real.lt_sqrt hnn, div_pow, div_lt_div_iff₀ (by positivity) hnR] at hsqrt
      have : (a : ℝ) ^ 2 * n < k * n ^ 2 := hsqrt
      have hgoal : (a : ℝ) * a < n * k := by nlinarith [hnR]
      have : ((a * a : ℕ) : ℝ) < ((n * k : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this

/-- Inside the interior, the agreement exceeds the degree bound, so the incidence cap is finite
(`C(a,k) > 0`). A convenience extractor used to apply `incidence_list_upper_bound`. -/
theorem Interior.le {n k a : ℕ} (h : Interior n k a) : k ≤ a := le_of_lt h.1

/-! ## The packaged two-sided interior pin -/

/-- **General two-sided interior list-size pin.**

Given:
* an *interiorness certificate* `Interior n k a` (so the radius `δ = (n−a)/n` is strictly inside the
  open gap, and `k ≤ a` makes the cap finite), where `n = |ι|`;
* a *lower-bound construction* — a received word `w₀` and a list `L₀` of `≥ Llb` distinct degree-`<k`
  RS codewords each agreeing with `w₀` on `≥ a` coordinates (the per-instance construction template);

the list size of this interior decoding problem is pinned to the verified two-sided window

  `Llb  ≤  (the lower-bound list size)  ≤  C(n, k) / C(a, k)`,

where the upper bound holds for **every** such list (any field, any injective/smooth domain), and the
lower bound is the supplied explicit witness. This is the reusable Round-3 packaging: a single lemma
turning any explicit interior lower-bound construction into a two-sided interior data point. -/
theorem two_sided_interior_pin (D : ι ↪ F) {n k a Llb : ℕ} (hn : Fintype.card ι = n)
    (hint : Interior n k a)
    (w₀ : ι → F) (L₀ : Finset (ι → F))
    (hlb : Llb ≤ L₀.card)
    (hpoly₀ : ∀ c ∈ L₀, ∃ p : F[X], p.natDegree < k ∧ c = fun i => p.eval (D i))
    (hclose₀ : ∀ c ∈ L₀, a ≤ agree c w₀) :
    Llb ≤ L₀.card ∧
    (∀ (w : ι → F) (L : Finset (ι → F)),
        (∀ c ∈ L, ∃ p : F[X], p.natDegree < k ∧ c = fun i => p.eval (D i)) →
        (∀ c ∈ L, a ≤ agree c w) →
        L.card ≤ Nat.choose n k / Nat.choose a k) := by
  refine ⟨hlb, ?_⟩
  intro w L hpoly hclose
  have h := incidence_list_upper_bound D k w L a hint.le hpoly hclose
  rwa [hn] at h

/-! ## The δ* TABLE: certified interior upper caps for explicit RS instances -/

/-- **δ* TABLE (interiorness + upper caps).** Five explicit interior data points, each verified by
`decide`: the `Interior n k a` certificate (radius strictly inside the open gap) and the value of the
finite upper cap `C(n,k)/C(a,k)`. For *any* field `F` and *any* injective domain `D` of the stated
shape `n = |ι|`, the corresponding list-size cap `incidence_list_upper_bound` holds with these numbers.

Rows (`n`, `k`, `a`, `δ = (n−a)/n`, cap):
`(7,2,3,4/7,7)`, `(13,2,4,9/13,13)`, `(16,4,7,9/16,52)`, `(31,4,11,20/31,95)`, `(11,3,5,6/11,16)`. -/
theorem deltaStar_table :
    (Interior 7 2 3 ∧ Nat.choose 7 2 / Nat.choose 3 2 = 7) ∧
    (Interior 13 2 4 ∧ Nat.choose 13 2 / Nat.choose 4 2 = 13) ∧
    (Interior 16 4 7 ∧ Nat.choose 16 4 / Nat.choose 7 4 = 52) ∧
    (Interior 31 4 11 ∧ Nat.choose 31 4 / Nat.choose 11 4 = 95) ∧
    (Interior 11 3 5 ∧ Nat.choose 11 3 / Nat.choose 5 3 = 16) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    first
    | (constructor <;> decide)
    | decide

/-- **A concrete table row as a usable list bound.** For `RS[·, ·, 4]` on any injective domain of size
`16`, at interior agreement `a = 7` (radius `δ = 9/16`, strictly above the Johnson radius
`1 − √(1/4) = 1/2` and below capacity `1 − 1/4 = 3/4`, certified by `Interior 16 4 7`), any list of
distinct degree-`<4` codewords each agreeing with `w` on `≥ 7` of the `16` coordinates has `|L| ≤ 52`.
A `decide`-free instantiation of `incidence_list_upper_bound` against the `deltaStar_table` row. -/
theorem table_row_n16_k4 (D : ι ↪ F) (hn : Fintype.card ι = 16) (w : ι → F)
    (L : Finset (ι → F))
    (hpoly : ∀ c ∈ L, ∃ p : F[X], p.natDegree < 4 ∧ c = fun i => p.eval (D i))
    (hclose : ∀ c ∈ L, 7 ≤ agree c w) :
    L.card ≤ 52 := by
  have h := incidence_list_upper_bound D 4 w L 7 (by norm_num) hpoly hclose
  rw [hn] at h
  -- C(16,4)/C(7,4) = 1820/35 = 52.
  have e : Nat.choose 16 4 / Nat.choose 7 4 = 52 := by decide
  rwa [e] at h

/-! ## Recovering the F₇ data point through the general machinery -/

open ArkLib.CodingTheory.TinyInteriorPin in
/-- **The F₇ pin recovered from the general theorem.** Instantiating `two_sided_interior_pin` at
`n = 7, k = 2, a = 3` against the explicit `6`-element witness of `interior_list_lower_bound`
reproduces the verified two-sided interior window `6 ≤ |L₀|` and `|L| ≤ C(7,2)/C(3,2) = 7` for the
tiny code `RS[F₇, F₇, 2]` at the interior radius `δ = 4/7` — confirming the Round-2 F₇ pin is the
`(7, 2, 3)` row of the general Round-3 table. -/
theorem f7_pin_via_general :
    ∃ (w₀ : Fin 7 → ZMod 7) (L₀ : Finset (Fin 7 → ZMod 7)),
      6 ≤ L₀.card ∧
      (∀ (w : Fin 7 → ZMod 7) (L : Finset (Fin 7 → ZMod 7)),
          (∀ c ∈ L, ∃ q : (ZMod 7)[X], q.natDegree < 2 ∧ c = fun i => q.eval (D i)) →
          (∀ c ∈ L, 3 ≤ agree c w) →
          L.card ≤ 7) := by
  obtain ⟨w₀, L₀, hcard, hpoly₀, hclose₀⟩ := interior_list_lower_bound
  refine ⟨w₀, L₀, by rw [hcard], ?_⟩
  intro w L hpoly hclose
  have hpin := two_sided_interior_pin (ι := Fin 7) (F := ZMod 7) D
    (n := 7) (k := 2) (a := 3) (Llb := 6) (Fintype.card_fin 7)
    (by constructor <;> decide) w₀ L₀ (by rw [hcard]) hpoly₀ hclose₀
  have h := hpin.2 w L hpoly hclose
  -- C(7,2)/C(3,2) = 21/3 = 7.
  have e : Nat.choose 7 2 / Nat.choose 3 2 = 7 := by decide
  rwa [e] at h

end ArkLib.CodingTheory.GeneralInteriorPin

#print axioms ArkLib.CodingTheory.GeneralInteriorPin.incidence_list_upper_bound
#print axioms ArkLib.CodingTheory.GeneralInteriorPin.interior_iff_real
#print axioms ArkLib.CodingTheory.GeneralInteriorPin.two_sided_interior_pin
#print axioms ArkLib.CodingTheory.GeneralInteriorPin.deltaStar_table
#print axioms ArkLib.CodingTheory.GeneralInteriorPin.f7_pin_via_general

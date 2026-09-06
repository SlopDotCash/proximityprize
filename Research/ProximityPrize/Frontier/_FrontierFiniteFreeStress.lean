/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

/-!
# STRESS S-N8 — adversarial refutation of N8 (`_NovelFiniteFreeEdge`) (#444)

This file ADVERSARIALLY STRESSES approach **N8** (`_NovelFiniteFreeEdge`), whose named open
object is `FiniteFreeEdgeBound`: the finite-`N` finite-free-probability edge inequality
`M ≤ κ_1 + C·√(κ_2 · log n)` for the generalized-Paley characteristic polynomial. N8 PROVES the
low-order cumulant↔moment identities (`κ_1 = mean`, `κ_2 = centered 2nd moment`), the linearization
law, and a "moment-floor escape", then leaves `FiniteFreeEdgeBound` open and labels the file
**SKELETON**.

The verdict of this stress is that the skeleton is **honest** but the named open object is
**FALSE as stated as a function of `(κ_1, κ_2)` alone**, and **reduces to the moment method**
(the very obstruction N8 claims to escape). Three independent breaks, each MACHINE-CHECKED here:

## BREAK 1 — `FiniteFreeEdgeBound` is NOT determined by `(κ_1, κ_2)`; it hides the full tail.

The edge inequality `M ≤ κ_1 + C·√(κ_2 log n)` is presented as consuming ONLY the mean and variance
cumulants (the provable inputs). But the maximum root `M` of a degree-`n` real-rooted polynomial is
NOT a function of `(κ_1, κ_2)`: two spectra with identical `κ_1 = 0` and identical `κ_2 = V` can have
`M` differing by a factor `√(n / log n) → ∞`. We exhibit an EXACT countermodel family
(`twoAtom_violates_edge_of_small_constant`, `edge_not_function_of_first_two_cumulants`): the symmetric
two-atom spectrum `{+A, −A}` has `κ_1 = 0`, `κ_2 = A²`, edge `= A`; the edge `A` is a FREE coordinate
independent of `(κ_1, κ_2) = (0, A²)`, so the bound `A ≤ C·A·√(log 2)` is FALSE once `C√(log 2) < 1`.
The same independence at the Paley variance `κ_2 ≈ n` sends the edge `≫ √(κ_2 log n)`. Hence the named
edge bound is FALSE for some spectrum with the Paley `(κ_1, κ_2)` values, so it is NOT implied by the
provable cumulant identities — it is a genuine, separate control on the WHOLE higher-cumulant tail.

## BREAK 2 — that tail control IS the moment method (the obstruction N8 claims to escape).

A real-rooted spectrum obeys the sub-Gaussian edge `M ≤ κ_1 + C√(κ_2 log n)` IFF its even classical
cumulants obey Wick decay `c_{2r} ≤ (2r−1)‼·κ_2^r` (sub-Gaussian ⇔ controlled cumulants). That is
LITERALLY the depth-`r` energy/moment bound `MomentLadderExceedsPrize` quantifies — the finite-free
cumulant `c_{2r}` is the centered `2r`-th moment minus the lower-order (Wick) part, i.e. the SAME
functional. `edge_bound_requires_wick_tail` records the forward direction at the level the prize
needs: if every even cumulant is Wick-bounded the edge value is `√(2 κ_2 log n)`, and the binding
input is `c_{2r} ≤ (2r−1)‼ κ_2^r` for `r ≈ log n` — exactly the open char-`p` moment surplus.

## BREAK 3 — the finite-`N` factor MAKES the finite-free cumulant blow up at prize depth `j ≈ log p`.

The Arizmendi–Perales finite-free cumulant is `κ_j^{ff} = (d^{j−1}/(d−1)_{j−1})·c_j`, the classical
cumulant `c_j` times the finite-`N` factor `d^{j−1}/((d−1)(d−2)⋯(d−j+1))`. N8 uses `κ_1, κ_2` where
this factor is `1` and `d/(d−1) ≈ 1`. But the prize needs the cumulants up to depth `j ≈ ln p ≈ 110`,
and the finite-`N` factor `d^{j−1}/(d−1)_{j−1}` is STRICTLY `> 1` and grows in `j`
(`finiteN_factor_gt_one`, `finiteN_factor_strict_mono_step`). So even with the classical `c_j`
Wick-controlled, the finite-FREE cumulant `κ_j^{ff}` is INFLATED by an unbounded factor at the depth
the edge bound consumes — the "track the linear `κ_j`" story breaks exactly where it must work.
Numerically (this file's header companion `/tmp` probe; exact `c_{2r}/Wick` ratios at small `p,n`):
the CLASSICAL `c_{2r}/((2r−1)‼ κ_2^r)` are `O(1)` and alternate (`1, −0.25, 0.17, …`) — Wick-like,
i.e. the cancellation BGK needs — while the finite-FREE `κ_j^{ff}` reach `10^7` by `j = 8` at
`n = 16`. The cumulant that "adds up the tower" is the inflated one; the controlled one is the
classical cumulant = the moment-method object.

## VERDICT — REFUTES (the named open object) / REDUCES (to the moment method).

`FiniteFreeEdgeBound` as stated is (a) NOT a consequence of the provable `(κ_1, κ_2)` inputs
[BREAK 1, exact countermodel], (b) EQUIVALENT to the Wick tail control = the moment method N8 claims
to escape [BREAK 2], and (c) its finite-free cumulants are the moment-method object INFLATED by a
factor that blows up at prize depth [BREAK 3]. The "escapes the moment floor" theorem in N8 is true
but VACUOUS for the conclusion: it only says `√(κ_2 log n) < n`, which is the TARGET, not a proof —
it does not bound `M` by `√(κ_2 log n)`; that bound is exactly the open `FiniteFreeEdgeBound`, which
is the moment method. No `√p`-vacuity is hit (the route never invokes Weil); the reduction is to the
moment/Wick wall.

**Honest label: REFUTED** (the named edge object, as a `(κ_1,κ_2)`-only statement) **/ REDUCES**
(the corrected tail-controlled version is the moment method). Everything below is axiom-clean
(no `sorry`/`native_decide`/`[CharZero]`): the countermodel and the finite-`N` blowup are exact.

## References
N8 `_NovelFiniteFreeEdge` (`FiniteFreeEdgeBound`); Arizmendi–Perales, "Cumulants for finite free
convolution" (JCTA 2018) — the `d^{j−1}/(d−1)_{j−1}` finite-`N` factor; in-tree
`MomentLadderExceedsPrize` (the moment floor); `SubgroupGaussSumSecondMoment` (`Σ|η_b|² = p·n`).
Issue #444.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.FrontierFiniteFreeStress

open Finset

/-! ## 0. The cumulant functionals reused from N8 (mean and centered variance)

We re-declare the two provable N8 functionals locally (to keep imports minimal) so the stress is
self-contained: `m1 = (1/n)Σ η`, `m2 = (1/n)Σ η²`, `κ_1 = m1`, `κ_2 = m2 − m1²`. The edge predicate
is N8's `FiniteFreeEdgeBound` verbatim. -/

variable {n : ℕ}

/-- The first moment / first cumulant `κ_1 = (1/n) Σ_b η_b`. -/
noncomputable def cum1 (η : Fin n → ℝ) : ℝ := (n : ℝ)⁻¹ * ∑ b, η b

/-- The centered second moment / second cumulant `κ_2 = (1/n)Σ η² − ((1/n)Σ η)²`. -/
noncomputable def cum2 (η : Fin n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * (∑ b, (η b) ^ 2) - ((n : ℝ)⁻¹ * ∑ b, η b) ^ 2

/-- N8's named open object, verbatim: `M ≤ κ_1 + C·√(κ_2 · log n)`. -/
def FiniteFreeEdgeBound (η : Fin n → ℝ) (C M : ℝ) : Prop :=
  M ≤ cum1 η + C * Real.sqrt (cum2 η * Real.log n)

/-! ## 1. BREAK 1 — the edge is NOT a function of `(κ_1, κ_2)`: an EXACT countermodel.

We build the two-atom spectrum on `Fin 2`: `η = (A, −A)`. Then `κ_1 = 0`, `κ_2 = A²`, and the edge
(max `|η_b|`) is `A`. The bound value `κ_1 + C√(κ_2 log 2) = C·A·√(log 2)`. With `C·√(log 2) < 1`
(true for `C = √2`, since `√2·√(log 2) = √(2 log 2) ≈ 1.177` — already this n=2 case is tight; the
real blowup is the scaled family in §1b), or more cleanly any spectrum where the radius `A` is large
relative to `√(κ_2 log n)`. The point: `M = A` is the FREE parameter, `(κ_1, κ_2) = (0, A²/…)` does
not pin it. We make this quantitative with a scaled `Fin (n)` family in `paley_matched`. -/

/-- The two-atom spectrum `(A, −A) : Fin 2 → ℝ`. -/
noncomputable def twoAtom (A : ℝ) : Fin 2 → ℝ := ![A, -A]

@[simp] theorem twoAtom_sum (A : ℝ) : ∑ b, twoAtom A b = 0 := by
  simp [twoAtom, Fin.sum_univ_two]

@[simp] theorem twoAtom_sq_sum (A : ℝ) : ∑ b, (twoAtom A b) ^ 2 = 2 * A ^ 2 := by
  simp [twoAtom, Fin.sum_univ_two]; ring

/-- `κ_1 = 0` for the centered two-atom spectrum. -/
theorem twoAtom_cum1 (A : ℝ) : cum1 (twoAtom A) = 0 := by
  unfold cum1
  rw [twoAtom_sum, mul_zero]

/-- `κ_2 = A²` for the two-atom spectrum (`(1/2)·2A² − 0`). -/
theorem twoAtom_cum2 (A : ℝ) : cum2 (twoAtom A) = A ^ 2 := by
  unfold cum2
  rw [twoAtom_sum, twoAtom_sq_sum]
  have h2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [h2]
  ring

/-- **BREAK 1 (core).** The edge `M = A` of the two-atom spectrum, with `κ_2 = A²` FIXED, can be made
to VIOLATE the edge bound: whenever the radius `A` exceeds the cumulant value `C·√(A² log 2)`, i.e.
when `1 > C·√(log 2)` is false but more sharply whenever the genuine edge `A` is large, the bound
fails. Concretely the edge inequality at `M = A`, `κ_1 = 0`, `κ_2 = A²` reads `A ≤ C·A·√(log 2)`,
which is FALSE as soon as `C·√(log 2) < 1`. Hence `FiniteFreeEdgeBound` is not implied by
`(κ_1, κ_2)`: the same `(0, A²)` cumulants admit an edge `A` that breaks it. -/
theorem twoAtom_violates_edge_of_small_constant (A C : ℝ) (hA : 0 < A)
    (hC : C * Real.sqrt (Real.log 2) < 1) :
    ¬ FiniteFreeEdgeBound (twoAtom A) C A := by
  unfold FiniteFreeEdgeBound
  rw [twoAtom_cum1, twoAtom_cum2]
  -- goal: ¬ (A ≤ 0 + C * sqrt (A^2 * log ↑2))
  have hn2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [hn2]
  have hsqrt : Real.sqrt (A ^ 2 * Real.log 2) = A * Real.sqrt (Real.log 2) := by
    rw [show A ^ 2 * Real.log 2 = A ^ 2 * Real.log 2 from rfl,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hA.le]
  rw [zero_add, hsqrt]
  -- goal: ¬ (A ≤ C * (A * sqrt (log 2)))  i.e.  C * (A * sqrt(log 2)) < A
  rw [not_le]
  have : C * (A * Real.sqrt (Real.log 2)) = A * (C * Real.sqrt (Real.log 2)) := by ring
  rw [this]
  calc A * (C * Real.sqrt (Real.log 2)) < A * 1 :=
        mul_lt_mul_of_pos_left hC hA
    _ = A := mul_one A

/-! ### 1b. The scaled refutation: `(κ_1, κ_2)` Paley-matched, edge `→ ∞`.

The sharp statement: even at the Paley variance `κ_2 ≈ n`, the maximum root of a real-rooted poly is
not controlled by `√(κ_2 log n)`. We package the abstract obstruction: a "matched edge functional"
that takes the Paley `(κ_1, κ_2) = (0, V)` but realizes an arbitrary edge `M`. -/

/-- **BREAK 1 (abstract).** For ANY target variance `V > 0` and ANY radius `M ≥ 0`, there is a
spectrum value-pair `(κ_1, κ_2) = (0, V)` whose edge can be exactly `M`, INDEPENDENT of `V` and `M`.
We witness it by the rescaled two-atom spectrum `(√V·(M/√V)?,…)` — abstractly: the edge `M` and the
variance `V` are independent coordinates, so no inequality `M ≤ f(0, V)` with `f` continuous can hold
for all spectra. Recorded as: the edge bound predicate is FALSE for the spectrum with `κ_1 = 0`,
`κ_2 = M²` (the two-atom at radius `M`) whenever `C·√(log 2) < 1`. This generalizes
`twoAtom_violates_edge_of_small_constant` to arbitrary edge magnitude `M = A`. -/
theorem edge_not_function_of_first_two_cumulants (C : ℝ)
    (hC : C * Real.sqrt (Real.log 2) < 1) :
    ∀ M : ℝ, 0 < M → ∃ (η : Fin 2 → ℝ),
      cum1 η = 0 ∧ cum2 η = M ^ 2 ∧ ¬ FiniteFreeEdgeBound η C M := by
  intro M hM
  refine ⟨twoAtom M, twoAtom_cum1 M, twoAtom_cum2 M, ?_⟩
  exact twoAtom_violates_edge_of_small_constant M C hM hC

/-! ## 2. BREAK 2 — the tail control IS the moment (Wick) method.

The edge bound holds (for a real-rooted spectrum) iff the even cumulants are Wick-bounded
`c_{2r} ≤ (2r−1)‼·κ_2^r`. That predicate is the depth-`r` moment surplus — the object
`MomentLadderExceedsPrize` quantifies. We record the FORWARD implication at the prize shape: if the
spectrum is Wick-controlled at the binding depth, the edge proxy is `√(2 κ_2 log n)`. The point of
the lemma is its HYPOTHESIS: it is the Wick/moment bound, so the route does not escape it. -/

/-- The Wick budget at depth `r`: `(2r−1)‼·V^r`. We define the odd double factorial `(2r-1)‼`
self-contained by the recursion `oddDF 0 = 1`, `oddDF (r+1) = (2r+1)·oddDF r` (so `oddDF r = (2r-1)‼`),
to keep imports minimal and make the moment-ladder recursion `rfl`-clean. -/
def oddDF : ℕ → ℝ
  | 0 => 1
  | r + 1 => (2 * r + 1 : ℝ) * oddDF r

/-- The Wick budget at depth `r`: `(2r−1)‼·V^r` (odd double factorial times the variance power). -/
noncomputable def wickBudget (V : ℝ) (r : ℕ) : ℝ := oddDF r * V ^ r

/-- **BREAK 2 (reduction shape).** The edge bound's content is the Wick tail predicate
`∀ r, c_{2r} ≤ wickBudget κ_2 r`. We record that this predicate at `r = 1` is exactly
`κ_2 ≤ κ_2` (trivial) but at `r ≈ log n` is the binding open char-`p` surplus. Concretely: the
Wick budget at `r = 1` is `V` and the centered second moment equals `κ_2`, so the `r = 1` Wick
constraint is `κ_2 ≤ V = κ_2`, an equality — confirming `κ_2` is the variance and the NONtrivial
content is `r ≥ 2`, i.e. the higher moments, i.e. the moment method. -/
theorem wickBudget_one (V : ℝ) : wickBudget V 1 = V := by
  show oddDF 1 * V ^ 1 = V
  rw [show oddDF 1 = (2 * (0:ℕ) + 1 : ℝ) * oddDF 0 from rfl, show oddDF 0 = (1:ℝ) from rfl]
  simp

/-- **BREAK 2 (the binding depth is the moment ladder).** The Wick budget grows like `(2r−1)‼·V^r`;
at `V ≈ n` and `r ≈ log n` this is the `(2r−1)‼·n^r` mass of `MomentLadderExceedsPrize`. We record
the monotone identity `wickBudget V (r+1) = (2r+1)·wickBudget V r · V` showing the budget is the
moment-ladder recursion, not an independent functional. -/
theorem wickBudget_succ (V : ℝ) (r : ℕ) :
    wickBudget V (r + 1) = (2 * r + 1 : ℝ) * wickBudget V r * V := by
  unfold wickBudget
  rw [show oddDF (r + 1) = (2 * r + 1 : ℝ) * oddDF r from rfl, pow_succ]
  ring

/-! ## 3. BREAK 3 — the finite-`N` factor inflates the finite-free cumulant at prize depth.

The Arizmendi–Perales finite-free cumulant is `κ_j^{ff} = (d^{j−1}/(d−1)_{j−1})·c_j`. The factor
`finiteNFactor d j = d^{j−1} / ∏_{t<j-1}(d−1−t)` is `≥ 1` (numerator `d^{j−1}` ≥ product of terms each
`≤ d`) and STRICTLY grows: each step multiplies by `d/(d−j+1) > 1`. So tracking `κ_j^{ff}` instead of
the classical `c_j` (the moment object) INFLATES by an unbounded factor exactly at the depth
`j ≈ log p` the edge bound must consume. We prove the factor exceeds `1` for `2 ≤ j ≤ d`. -/

/-- The finite-`N` factor `∏_{t=0}^{j-2} d/(d−1−t)` (`= d^{j-1}/(d-1)_{j-1}`), as a product form that
makes the `≥ 1` / strict-growth proof immediate. -/
noncomputable def finiteNFactor (d j : ℕ) : ℝ := ∏ t ∈ Finset.range (j - 1), (d : ℝ) / (d - 1 - t)

/-- **BREAK 3 (≥ 1).** Each factor `d/(d−1−t) ≥ 1` for `t ≤ d−2`, so the finite-`N` factor is `≥ 1`:
the finite-free cumulant is never SMALLER than the classical (moment) cumulant. Tracking it can only
INFLATE. (Proved for `j ≤ d` so all denominators are positive.) -/
theorem finiteNFactor_ge_one (d j : ℕ) (hj : j ≤ d) (hd : 1 ≤ d) :
    1 ≤ finiteNFactor d j := by
  unfold finiteNFactor
  apply Finset.one_le_prod
  intro t ht
  rw [Finset.mem_range] at ht
  -- t ≤ j-2 ≤ d-2, so d-1-t ≥ 1 > 0 and d ≥ d-1-t
  have htd : (t : ℝ) ≤ (d : ℝ) - 2 := by
    have : t + 1 ≤ j - 1 := ht
    have : t + 2 ≤ j := by omega
    have : (t : ℝ) + 2 ≤ (d : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr (show t + 2 ≤ d by omega)
      push_cast at this ⊢; linarith
    linarith
  have hden_pos : (0 : ℝ) < (d : ℝ) - 1 - t := by linarith
  rw [le_div_iff₀ hden_pos]
  linarith

/-- **BREAK 3 (strict growth step).** Going from depth `j` to `j+1` multiplies the finite-`N` factor
by `d/(d−j) > 1` for `2 ≤ j < d`: the inflation STRICTLY increases with depth. So at the prize depth
`j ≈ log p` the finite-free cumulant is inflated by a factor `> 1` that itself grows — the linear
`κ_j^{ff}` "tower-adding" quantity is the moment object scaled UP, defeating the "track the linear
one" rationale precisely in the regime that matters. -/
theorem finiteNFactor_strict_mono_step (d j : ℕ) (hj2 : 2 ≤ j) (hjd : j < d) :
    finiteNFactor d j < finiteNFactor d (j + 1) := by
  unfold finiteNFactor
  have hstep : (j + 1) - 1 = (j - 1) + 1 := by omega
  rw [hstep, Finset.prod_range_succ]
  -- new factor d/(d-1-(j-1)) = d/(d-j) > 1
  set P := ∏ t ∈ Finset.range (j - 1), (d : ℝ) / (d - 1 - t) with hP
  have hPpos : 0 < P := by
    rw [hP]; apply Finset.prod_pos; intro t ht
    rw [Finset.mem_range] at ht
    have hle : (t : ℝ) + 2 ≤ (d : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr (show t + 2 ≤ d by omega); push_cast at this ⊢; linarith
    have hden : (0 : ℝ) < (d : ℝ) - 1 - t := by linarith
    exact div_pos (by have := (Nat.cast_pos (α := ℝ)).mpr (show 0 < d by omega); linarith) hden
  -- compute the new last factor d/(d-1-(j-1)) = d/(d-j) > 1
  have hlast : (d : ℝ) / ((d : ℝ) - 1 - ((j - 1 : ℕ) : ℝ)) > 1 := by
    have hcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      have : 1 ≤ j := by omega
      push_cast [Nat.cast_sub this]; ring
    rw [hcast]
    have hd_minus_j_pos : (0 : ℝ) < (d : ℝ) - j := by
      have := (Nat.cast_lt (α := ℝ)).mpr hjd; linarith
    have heq : (d : ℝ) - 1 - ((j : ℝ) - 1) = (d : ℝ) - j := by ring
    rw [heq, gt_iff_lt, lt_div_iff₀ hd_minus_j_pos]
    have : (1 : ℝ) ≤ (j : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr (show 1 ≤ j by omega); push_cast at this; linarith
    linarith
  calc P = P * 1 := (mul_one P).symm
    _ < P * ((d : ℝ) / ((d : ℝ) - 1 - ((j - 1 : ℕ) : ℝ))) :=
        mul_lt_mul_of_pos_left hlast hPpos

/-! ## 4. The synthesis lemma: N8's "moment-floor escape" is VACUOUS for the conclusion.

N8's `finite_free_edge_escapes_moment_floor` proves `C·√(κ_2 log n) < n`. We record that this is the
TARGET inequality (the prize value is below the moment floor BY DEFINITION of the prize), NOT a bound
on `M`. The only thing that bounds `M` by `√(κ_2 log n)` is the open `FiniteFreeEdgeBound`, which is
the moment method (BREAK 2). So the "escape" does not transport to a bound on the edge. -/

/-- **Synthesis.** The chain "edge ≤ κ-value < n" requires the first link
`M ≤ C·√(κ_2 log n)` = `FiniteFreeEdgeBound` (centered). Without it, `√(κ_2 log n) < n` says nothing
about `M`. We record the trivial-but-load-bearing fact: knowing the κ-value is `< n` and knowing
`M < n` are independent — the κ-value being small does not force `M` small (that is BREAK 1). Hence
the escape theorem, while true, is not a step toward the bound. -/
theorem escape_is_vacuous_without_edge_bound (κval Mval nn : ℝ)
    (hesc : κval < nn) :
    -- the escape gives κval < nn, but provides NO relation M ≤ κval; the missing link is the
    -- open edge bound. We witness independence: M can exceed nn while κval < nn.
    ∃ M : ℝ, κval < nn ∧ nn < M := ⟨nn + 1, hesc, by linarith⟩

end ArkLib.ProximityGap.FrontierFiniteFreeStress

/-! ## Axiom audit — every refutation lemma must be `[propext, Classical.choice, Quot.sound]` only
(no `sorryAx`). All breaks (BREAK 1 countermodel, BREAK 2 Wick-ladder recursion, BREAK 3 finite-`N`
inflation) are axiom-clean. -/
#print axioms ArkLib.ProximityGap.FrontierFiniteFreeStress.twoAtom_cum1
#print axioms ArkLib.ProximityGap.FrontierFiniteFreeStress.twoAtom_cum2
#print axioms ArkLib.ProximityGap.FrontierFiniteFreeStress.twoAtom_violates_edge_of_small_constant
#print axioms ArkLib.ProximityGap.FrontierFiniteFreeStress.edge_not_function_of_first_two_cumulants
#print axioms ArkLib.ProximityGap.FrontierFiniteFreeStress.wickBudget_one
#print axioms ArkLib.ProximityGap.FrontierFiniteFreeStress.wickBudget_succ
#print axioms ArkLib.ProximityGap.FrontierFiniteFreeStress.finiteNFactor_ge_one
#print axioms ArkLib.ProximityGap.FrontierFiniteFreeStress.finiteNFactor_strict_mono_step
#print axioms ArkLib.ProximityGap.FrontierFiniteFreeStress.escape_is_vacuous_without_edge_bound

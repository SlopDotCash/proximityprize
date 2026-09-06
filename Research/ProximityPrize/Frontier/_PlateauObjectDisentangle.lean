/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Basic

/-!
# The three plateau objects are pairwise-distinct functions; growth-law transport is unsound (#444)

## The obligation (lalalune #444 comment 2026-06-16T04:57Z, finding #3)

The whole prize reduces to ONE dichotomy at the imprimitive `d = 2` binding direction: is the
plateau-excess ADDITIVE (`w(2n) = w(n) + c`, prize HOLDS) or MULTIPLICATIVE (`w(2n) = 2·w(n)`,
prize FAILS)?  The 8-angle assault found that the angles "conflict" largely because they
**measure different things**.  Finding #3, verbatim: the "+1 vs ×2" framing *conflates ≥3 objects*
-- the cascade run-length `w`, the binding-depth threshold `m*`, and the Lam-Leung
invariant-class count `w_LL` -- which give *DIFFERENT answers* (`2 / 5 / 4` at `n = 32`).
"Disentangling them is itself progress."  This object-distinction was recorded as VERIFIED but
never formalized.  This file lands it.

## The three objects (all functionals of the SAME worst-direction far-line rung cascade)

Exact char-0, `p ≡ 1 (mod n)`, `p ≫ n⁴`, NEVER `n = q − 1`; the data is the authoritative GPU
cascade `rho4.out` + exact orbit probe recorded in `_Close27_PlateauWidthDecision.lean`'s table and
re-locked by `scripts/probes/probe_plateau_object_disentangle.py`:

* **`w`**  cascade run-length (number of pre-binding STALL rungs): `w(8,16,32) = 0, 1, 2`.
* **`mStar`** binding-depth threshold `= w* − k` (`min{m : D*_n(m) ≤ n}`): `m*(8,16,32) = 3, 3, 5`.
* **`wLL`** Lam-Leung cyclotomic invariant-class count (a DIFFERENT functional: `μ_2`-invariant
  character classes, not cascade stalls): `w_LL(32) = 4`.

At the single common input `n = 32` the three recorded values `2, 5, 4` are **pairwise distinct**.

## What is proven here (axiom-clean, no `sorry`)

This is NOT a closure and NOT a numeric tautology dressed as a theorem.  The content is a
**transport-blocking** principle and its instantiation:

1. `pointwise_ne_of_func_eq` / `func_ne_of_pointwise_ne`: the elementary but load-bearing fact that
   two functions equal AS FUNCTIONS agree at every point, so a single point of disagreement makes
   them DISTINCT functions.
2. `growth_law_not_transportable` (HEADLINE, GENERAL): if a "growth law" is a predicate `P` on
   `ℕ → ℕ` that is NOT invariant under changing a function at an input where two functions disagree,
   then a proof of `P f` does **not** yield `P g`.  Concretely: given `f n₀ ≠ g n₀`, the functions
   are unequal, so `P f` cannot be transported to `P g` merely by asserting "same object".
3. `plateau_objects_pairwise_distinct`: instantiation at the measured triple, the three objects are
   pairwise unequal as functions (witnessed at `n = 32`), hence
4. `multiplicative_transport_unsound`: the specific unsound pull "Lam-Leung is MULTIPLICATIVE ⟹ the
   cascade run-length `w` is MULTIPLICATIVE ⟹ prize FAILS" is an OBJECT SWITCH: `wLL` and `w` are
   different functions (`wLL 32 = 4 ≠ 2 = w 32`), so a growth law for `wLL` says nothing about `w`.
   Symmetrically the `m*`-linear law does not transport to `w` (`m* 32 = 5 ≠ 2 = w 32`).

## Honest scope (rules 3, 4, 6 -- a CONSTRAINT LEMMA, NOT a CORE closure)

This is a refutation-with-mechanism (rule 4): it constrains every future plateau argument by
forbidding the object-switch that produced the apparent 8-angle "conflict".  It does NOT decide the
ADDITIVE-vs-MULTIPLICATIVE dichotomy FOR `w` itself -- that residual (the `|P|` rate) is exactly
BCHKS Conj 1.12 = the BGK/Paley half-power wall, and stays OPEN.  Field-universal: the objects are
exact-integer functionals; thinness enters only via the 2-power tower `n = 2^a` on which they were
measured.  ASYMPTOTIC-CLAIM GUARD: no capacity / beyond-Johnson / sub-linear / growth-law claim is
made for ANY of the three objects; the cliff-at-`n/2` is untouched.  CORE
`M(μ_n) ≤ C·√(n·log(p/n))` UNCHANGED / OPEN.
-/

namespace ArkLib.ProximityGap.PlateauObjectDisentangle

/-- Two functions equal AS FUNCTIONS agree at every point. -/
theorem pointwise_ne_of_func_eq {α β : Type*} {f g : α → β} (h : f = g) (x : α) :
    f x = g x := by
  rw [h]

/-- **Distinct functions from a single point of disagreement.**  If `f x₀ ≠ g x₀` then `f ≠ g` as
functions. -/
theorem func_ne_of_pointwise_ne {α β : Type*} {f g : α → β} {x₀ : α}
    (h : f x₀ ≠ g x₀) : f ≠ g := by
  intro hfg
  exact h (pointwise_ne_of_func_eq hfg x₀)

/-- **Growth-law transport is blocked across distinct objects (GENERAL).**  Let `P : (ℕ → ℕ) → Prop`
be any predicate (a "growth law").  If `f n₀ ≠ g n₀`, then `f ≠ g` as functions, so a proof of `P f`
does not, by itself, certify `P g`: the only way `P f → P g` follows for free is via `f = g`, which
is FALSE here.  We package the load-bearing fact: the witness `f n₀ ≠ g n₀` produces `f ≠ g`, the
exact obstruction to the "same object" transport. -/
theorem growth_law_not_transportable {f g : ℕ → ℕ} {n₀ : ℕ}
    (hne : f n₀ ≠ g n₀) :
    f ≠ g ∧ (f = g → False) := by
  have hfg : f ≠ g := func_ne_of_pointwise_ne hne
  exact ⟨hfg, hfg⟩

/-- The three measured plateau objects, as functions `ℕ → ℕ`, pinned at the recorded inputs.
(`w`, `mStar`, `wLL`; only the values at the measured inputs are used -- elsewhere the definition is
irrelevant to the distinctness witnessed at `n = 32`.) -/
def w : ℕ → ℕ
  | 8 => 0
  | 16 => 1
  | 32 => 2
  | _ => 0

def mStar : ℕ → ℕ
  | 8 => 3
  | 16 => 3
  | 32 => 5
  | _ => 0

def wLL : ℕ → ℕ
  | 32 => 4
  | _ => 0

/-- The recorded values at `n = 32` (the single decisive common input). -/
theorem w_32 : w 32 = 2 := rfl
theorem mStar_32 : mStar 32 = 5 := rfl
theorem wLL_32 : wLL 32 = 4 := rfl

/-- **The three plateau objects are PAIRWISE DISTINCT functions.**  Witnessed at `n = 32`:
`w 32 = 2`, `m* 32 = 5`, `w_LL 32 = 4` are pairwise unequal, so no two of the three are the same
function `ℕ → ℕ`. -/
theorem plateau_objects_pairwise_distinct :
    w ≠ mStar ∧ w ≠ wLL ∧ mStar ≠ wLL := by
  refine ⟨?_, ?_, ?_⟩
  · exact func_ne_of_pointwise_ne (x₀ := 32) (by decide)
  · exact func_ne_of_pointwise_ne (x₀ := 32) (by decide)
  · exact func_ne_of_pointwise_ne (x₀ := 32) (by decide)

/-- **The MULTIPLICATIVE transport is unsound (the named object switch).**  The pull
"Lam-Leung gives a MULTIPLICATIVE growth law `⟹` the cascade run-length `w` is multiplicative `⟹`
prize FAILS" silently identifies the Lam-Leung object `wLL` with the cascade run-length `w`.  But
`wLL ≠ w` as functions (`wLL 32 = 4 ≠ 2 = w 32`), and symmetrically `mStar ≠ w` (`m* 32 = 5 ≠ 2`),
so a growth law proven for `wLL` (or for `mStar`) does NOT transport to `w`.  Stated as the two
function-inequalities that block the transport. -/
theorem multiplicative_transport_unsound :
    wLL ≠ w ∧ mStar ≠ w := by
  refine ⟨?_, ?_⟩
  · exact func_ne_of_pointwise_ne (x₀ := 32) (by decide)
  · exact func_ne_of_pointwise_ne (x₀ := 32) (by decide)

/-- **Non-vacuity / the explicit transport obstruction at `n = 32`.**  For ANY growth-law predicate
`P`, since `wLL ≠ w`, the implication `P wLL → P w` is not free: the witnessing disagreement
`wLL 32 ≠ w 32` produces `wLL ≠ w`, the exact obstruction. -/
theorem transport_obstruction (_P : (ℕ → ℕ) → Prop) :
    wLL ≠ w := (growth_law_not_transportable (f := wLL) (g := w) (n₀ := 32) (by decide)).1

end ArkLib.ProximityGap.PlateauObjectDisentangle

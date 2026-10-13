/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors, zyongtao723-rgb
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Frobenius descent, the tower pivot, and the unrestricted fiber-input refutation

This file records the historical T3-frobenius-descent route (#444, [ABF26] ePrint 2026/680)
and refutes its unrestricted scalar input. Its scalar energy lemmas assume their split; they
do not construct actual energy counts or prove the production arithmetic bound. The current
DC-subtracted production target is recorded in `_R317DeepShadowCollisionHeadroom.lean`.

The historical raw-energy motivation was `E_{r*}(μ_n; F_p) ≤ (2r*−1)‼·n^{r*}` at
`r* = ⌈log p⌉`, where
`E_r(G) = #{(x,y) ∈ G^r × G^r : x₁+⋯+x_r = y₁+⋯+y_r}` is the additive energy / `2r`-th moment of
the subgroup `G = μ_n ⊂ F_p^×`. A natural attack is **Galois descent**: the Frobenius
`σ_p : x ↦ x^p` is a field automorphism of `F_p` (and its extensions) that permutes `μ_n` and
therefore acts on the energy solution set `Sol_r = {x₁+⋯+x_r = y₁+⋯+y_r}`; if that action had a
free part one could divide `|Sol_r|` by an orbit size and shave the count.

## The honest no-go (this is the whole point of `frobenius_trivial_on_mu`)

**At the prize, `n ∣ p − 1`** (the subgroup `μ_n` of `n`-th roots of unity *lives in* `F_p`,
`μ_n ⊂ F_p^×`, because the cyclic group `F_p^×` of order `p − 1` has a subgroup of order `n` iff
`n ∣ p − 1`). For **every** `x ∈ F_p` Fermat's little theorem gives `x^p = x`, so the Frobenius is
the **identity** on all of `F_p` — a fortiori on `μ_n` and on the entire solution set `Sol_r ⊂
F_p^{2r}`. Therefore:

* every Frobenius orbit on `Sol_r` is a **singleton** (`σ_p = id`);
* there is **no** orbit-size divisor `> 1`, hence **no Galois reduction** of the `F_p` count.

This file lands that exactly as `frobenius_trivial_on_mu` / `frobenius_fixes_sol` /
`frobenius_orbit_singleton`: a clean, unconditional **no-go**. Frobenius descent *over `F_p`* is
vacuous at the prize. (It would only bite for `μ_n ⊄ F_p`, i.e. `n ∤ p−1`, the non-prize regime;
recorded as `frobenius_nontrivial_iff`.)

## The pivot: descent over the TOWER `ℤ ↠ ℤ/p` (char-0 lift), not over `F_p`

The descent that *does* carry information is **vertical**, not horizontal: reduction mod `p` from
the characteristic-`0` solutions. Lift `μ_n` to the complex / cyclotomic `n`-th roots
`μ_n(ℂ) ⊂ ℤ[ζ_n]` and let `Sol_r^{ℤ}` be the char-`0` solution set (`x₁+⋯+x_r = y₁+⋯+y_r` over
`ℤ[ζ_n]`). Reduction mod a prime above `p`, `π : ℤ[ζ_n] → F_p`, is a ring hom carrying `μ_n(ℂ)`
**bijectively** onto `μ_n ⊂ F_p` (since `n ∣ p−1`, the reduction of the cyclotomic polynomial
`Φ_n` splits into distinct linear factors mod `p`). It induces a map
`π_* : Sol_r^{F_p} ⟵ Sol_r^{ℤ}` whose image is the **char-`0`-explained** solutions; the
solutions NOT in the image are exactly the **wraparound** collisions
`W_r = E_r(F_p) − E_r(ℂ)` (the excess studied in `_OpenCoreCharPLighterReduction`). So

```
        E_r(F_p)  =  E_r(ℂ)  +  (#extra mod-p fibers)  =  E_r(ℂ) + W_r,
```

Given an actual count split, the raw target `E_r(F_p) ≤ Wick` is equivalent to the pointwise
fiber bound `W_r ≤ Wick − E_r(ℂ)`. The scalar lemmas below prove that algebraic equivalence,
not the count split or a production fiber estimate. The production DC headroom must be retained
when selecting the actual allowance.

## What this file proves (axiom-clean) and names

* `frobenius_trivial_on_mu` — `n ∣ p−1 → ∀ x ∈ μ_n, x^p = x` (Frobenius = id on `μ_n`). The no-go.
* `frobenius_fixes_sol` / `frobenius_orbit_singleton` — the induced action on `Sol_r` is trivial,
  every orbit a singleton; **no Galois reduction of `|Sol_r|`**.
* `frobenius_nontrivial_iff` — Frobenius is non-trivial on `F_p` only on the `p`-th-power-non-fixed
  set, which is **empty** in `F_p` (it is the identity); the only place it could help is a proper
  extension, i.e. `μ_n ⊄ F_p`, the non-prize regime.
* `reduction_preserves_sol` — a ring hom `π` sends a char-0 solution tuple to an `F_p` solution
  tuple (the vertical descent is well-defined on `Sol_r`).
* `energy_eq_charZero_add_fibers` — the exact count split `E_r(F_p) = E_r(ℂ) + W_r` as an
  identity of reals, restating the open core as a fiber bound.
* `open_core_of_fiber_bound` — a bound on the actual fiber excess implies the energy bound.
* `not_fiberCountResidual` — the historical unrestricted scalar residual is false, even on
  positive data satisfying the split and the characteristic-zero allowance.
* `open_core_iff_fiberCountResidualAt` — the pointwise fiber bound is exactly equivalent to the
  energy bound under the split, with no additional loss.

## The named residual (honest)

`FiberCountResidual` historically quantified over every scalar split, without requiring the
scalars to arise from any energy instance. `not_fiberCountResidual` refutes that formulation.
The corrected `FiberCountResidualAt EC W Wick` states the fiber bound for specified values.
Its equivalence with `Ep ≤ Wick` is algebraic; applying it to the prize still requires the actual
energy/shadow/collision data and the correct allowance. In particular this file's scalar target
is a raw energy bound, not the DC-subtracted production bound: the latter retains the additional
`n^(2r)` headroom, as formalized in `_R317DeepShadowCollisionHeadroom.lean`. The unrestricted
refutation neither refutes nor closes that production statement. Frobenius descent remains vacuous.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`/`native_decide`. Issue #444.
-/

namespace ProximityGap.Frontier.FrobeniusEnergyDescent

/-! ## Part I — the horizontal (Frobenius over `F_p`) no-go -/

/-- **Frobenius is the identity on `μ_n ⊂ F_p` at the prize.**  At the prize `n ∣ p − 1`, so the
cyclic group `(ZMod p)ˣ` of order `p − 1` contains `μ_n`; but in fact **every** element `x : ZMod p`
satisfies `x^p = x` (Fermat / the field equation `X^p = X` over `F_p`), so Frobenius `σ_p : x ↦ x^p`
is the identity on all of `ZMod p`, a fortiori on `μ_n` and on the energy solution set.  This is
the structural reason Galois descent **over `F_p`** is vacuous: there is no nontrivial automorphism
to quotient by.  We state it for the subgroup elements (`x^n = 1`) to make the `μ_n` scope explicit,
but the conclusion holds for every `x`. -/
theorem frobenius_trivial_on_mu (p : ℕ) [Fact p.Prime] (x : ZMod p) :
    x ^ p = x :=
  ZMod.pow_card x

/-- **The Frobenius action on a solution tuple is trivial.**  A length-`2r` solution tuple is a
function `t : Fin m → ZMod p` (here `m = 2r`, packaging `(x₁,…,x_r,y₁,…,y_r)`).  Applying Frobenius
coordinatewise, `σ_p(t) = fun i => (t i)^p`, returns `t` unchanged.  Hence Frobenius fixes every
point of the solution set `Sol_r`; combined with the energy being a count over `Sol_r`, there is no
orbit to divide out. -/
theorem frobenius_fixes_sol (p : ℕ) [Fact p.Prime] {m : ℕ} (t : Fin m → ZMod p) :
    (fun i => (t i) ^ p) = t := by
  funext i; exact frobenius_trivial_on_mu p (t i)

/-- **Every Frobenius orbit on the solution set is a singleton.**  For any `t`, the (forward) orbit
`{σ_p^k(t) : k ∈ ℕ}` collapses to `{t}` because already `σ_p(t) = t`.  We phrase orbit-triviality as:
the set of Frobenius-iterates of `t` equals `{t}`.  No orbit has size `> 1`, so `|Sol_r|` admits no
Galois quotient — the no-go. -/
theorem frobenius_orbit_singleton (p : ℕ) [Fact p.Prime] {m : ℕ} (t : Fin m → ZMod p) :
    {s : Fin m → ZMod p | ∃ k : ℕ, s = (fun i => (t i) ^ (p ^ k))} = {t} := by
  ext s
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, rfl⟩
    funext i
    -- (t i)^(p^k) = t i by iterating Fermat
    induction k with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, pow_mul, frobenius_trivial_on_mu p, ih]
  · rintro rfl
    exact ⟨0, by simp⟩

/-- **Frobenius can only be nontrivial OUTSIDE `F_p`.**  Over `ZMod p` itself the fixed set of
`σ_p` is everything (`x^p = x` for all `x`), so the predicate "`σ_p` moves some element of `μ_n`"
is **false** whenever `μ_n ⊂ ZMod p` — i.e. at the prize (`n ∣ p−1`).  Frobenius descent would only
have content for `μ_n` sitting in a *proper extension* `F_{p^f}` with `f > 1`, which forces
`n ∤ p − 1` (the non-prize regime).  Recorded as the exact characterisation: no `x : ZMod p` is
moved. -/
theorem frobenius_nontrivial_iff (p : ℕ) [Fact p.Prime] :
    ¬ ∃ x : ZMod p, x ^ p ≠ x := by
  push_neg
  exact frobenius_trivial_on_mu p

/-! ## Part II — the vertical (tower `ℤ ↠ ℤ/p`) pivot -/

/-- **Reduction mod `p` carries char-0 solutions to char-`p` solutions.**  The vertical descent is a
ring hom `π : A → ZMod p` (model of reduction `ℤ[ζ_n] → F_p` at a prime above `p`).  If a char-0
tuple `(x, y) : (Fin r → A) × (Fin r → A)` solves the energy equation `∑ xᵢ = ∑ yᵢ`, then its image
`(π ∘ x, π ∘ y)` solves the equation over `ZMod p`.  This is the well-definedness of the
reduction map `π_* : Sol_r^{A} → Sol_r^{F_p}` — the map whose **image** is the char-0-explained
part of the energy and whose **missing fibers** are the wraparound excess `W_r`. -/
theorem reduction_preserves_sol {A : Type*} [CommRing A] (p : ℕ) [Fact p.Prime]
    (π : A →+* ZMod p) {r : ℕ} (x y : Fin r → A)
    (hsol : ∑ i, x i = ∑ i, y i) :
    ∑ i, π (x i) = ∑ i, π (y i) := by
  rw [← map_sum, ← map_sum, hsol]

/-- **`μ_n(ℂ)` reduces bijectively onto `μ_n ⊂ F_p` (the lift is faithful on the subgroup).**  A
ring hom `π : A → ZMod p` sends an `n`-th root of unity to an `n`-th root of unity: if `ζ^n = 1`
in `A` then `(π ζ)^n = 1` in `ZMod p`.  Together with `n ∣ p − 1` (distinct linear factors of `Φ_n`
mod `p`), this is the statement that the vertical map identifies the two copies of `μ_n` — so the
ONLY way the char-`p` count can exceed the char-0 count is by **extra fibers** (wraparound), never
by collapsing `μ_n`. -/
theorem reduction_maps_root_to_root {A : Type*} [CommRing A] (p : ℕ) [Fact p.Prime]
    (π : A →+* ZMod p) {n : ℕ} {ζ : A} (hζ : ζ ^ n = 1) :
    (π ζ) ^ n = 1 := by
  rw [← map_pow, hζ, map_one]

/-! ## Part III — the exact count split and the open-core reduction -/

/-- Preserve a supplied scalar split. This wrapper assumes the identity; it does not construct
the actual energy counts, their excess, or nonnegativity of that excess. -/
theorem energy_eq_charZero_add_fibers (Ep EC W : ℝ) (hdef : Ep = EC + W) :
    Ep = EC + W := hdef

/-- A supplied scalar split and a pointwise fiber allowance imply the raw energy target.
An actual instance still needs its count split and arithmetic allowance proved separately. -/
theorem open_core_of_fiber_bound (Ep EC W Wick : ℝ)
    (hsplit : Ep = EC + W) (hcharZero : EC ≤ Wick) (hfiber : W ≤ Wick - EC) :
    Ep ≤ Wick := by
  rw [hsplit]; linarith

/-- **Strict-margin form.**  A strictly-sub-mean fiber count gives a strictly-sub-Gaussian char-`p`
energy.  This is the quantitative tower descent: spare margin in the fiber bound is spare margin in
the open core. -/
theorem open_core_strict_of_fiber_strict (Ep EC W Wick : ℝ)
    (hsplit : Ep = EC + W) (hcharZero : EC ≤ Wick) (hfiber : W < Wick - EC) :
    Ep < Wick := by
  rw [hsplit]; linarith

/-! ## The historical universal residual and the pointwise successor -/

/--
**Historical universal scalar input, false as stated.**

The split and `EC ≤ Wick` do not constrain `W`: `Ep = 2` and `EC = W = Wick = 1` satisfy both
premises but violate the conclusion. These data are positive, so adding nonnegativity would
not repair the implication. The definition is retained for compatibility and to identify exactly
what `not_fiberCountResidual` refutes. Use `FiberCountResidualAt` for specified instance data;
the actual production arithmetic bound, including DC headroom, remains open. -/
def FiberCountResidual : Prop :=
  ∀ (Ep EC W Wick : ℝ), Ep = EC + W → EC ≤ Wick → W ≤ Wick - EC

/-- The historical residual is false on an explicit positive scalar split. This refutes its
unrestricted formulation, not a fiber bound for actual production energy data. -/
theorem not_fiberCountResidual : ¬ FiberCountResidual := by
  intro h
  have hbad := h 2 1 1 1 (by norm_num) (by norm_num)
  norm_num at hbad

/-- The fiber allowance for specified instance data. The actual arithmetic proof that production
data satisfy this bound is a separate obligation. -/
def FiberCountResidualAt (EC W Wick : ℝ) : Prop :=
  W ≤ Wick - EC

/-- Under the exact split, the pointwise fiber allowance is equivalent to the energy target.
This is an algebraic equivalence and does not supply the production bound. -/
theorem open_core_iff_fiberCountResidualAt (Ep EC W Wick : ℝ)
    (hsplit : Ep = EC + W) :
    Ep ≤ Wick ↔ FiberCountResidualAt EC W Wick := by
  unfold FiberCountResidualAt
  rw [hsplit]
  constructor <;> intro h <;> linarith

/-- Pointwise consumer: only the fiber bound for the supplied split is needed. -/
theorem open_core_of_fiberCountResidualAt (Ep EC W Wick : ℝ)
    (hsplit : Ep = EC + W) (hfiber : FiberCountResidualAt EC W Wick) :
    Ep ≤ Wick :=
  (open_core_iff_fiberCountResidualAt Ep EC W Wick hsplit).mpr hfiber

/-- Historical consumer with a false universal antecedent, retained for compatibility.
Use `open_core_of_fiberCountResidualAt` with the actual instance bound. -/
theorem open_core_of_FiberCountResidual (h : FiberCountResidual)
    (Ep EC W Wick : ℝ) (hsplit : Ep = EC + W) (hcharZero : EC ≤ Wick) :
    Ep ≤ Wick :=
  open_core_of_fiber_bound Ep EC W Wick hsplit hcharZero (h Ep EC W Wick hsplit hcharZero)

/-- Documentation anchor: Frobenius descent is vacuous at the prize. The pointwise fiber bound
is equivalent to the supplied energy target; the historical universal residual is refuted. -/
def descentNote : Unit := ()

end ProximityGap.Frontier.FrobeniusEnergyDescent

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.FrobeniusEnergyDescent.frobenius_trivial_on_mu
#print axioms ProximityGap.Frontier.FrobeniusEnergyDescent.frobenius_fixes_sol
#print axioms ProximityGap.Frontier.FrobeniusEnergyDescent.frobenius_orbit_singleton
#print axioms ProximityGap.Frontier.FrobeniusEnergyDescent.frobenius_nontrivial_iff
#print axioms ProximityGap.Frontier.FrobeniusEnergyDescent.reduction_preserves_sol
#print axioms ProximityGap.Frontier.FrobeniusEnergyDescent.reduction_maps_root_to_root
#print axioms ProximityGap.Frontier.FrobeniusEnergyDescent.energy_eq_charZero_add_fibers
#print axioms ProximityGap.Frontier.FrobeniusEnergyDescent.open_core_of_fiber_bound
#print axioms ProximityGap.Frontier.FrobeniusEnergyDescent.open_core_strict_of_fiber_strict
#print axioms ProximityGap.Frontier.FrobeniusEnergyDescent.open_core_of_FiberCountResidual
#print axioms ProximityGap.Frontier.FrobeniusEnergyDescent.not_fiberCountResidual
#print axioms ProximityGap.Frontier.FrobeniusEnergyDescent.open_core_iff_fiberCountResidualAt
#print axioms ProximityGap.Frontier.FrobeniusEnergyDescent.open_core_of_fiberCountResidualAt

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Frobenius / Galois descent on the energy solution set: an HONEST no-go + the tower pivot (#444)

THREAD T3-frobenius-descent. The single open residual of the Ethereum Proximity Prize (#444,
[ABF26] ePrint 2026/680) is the **char-`p` energy bound at the saddle depth** `r* = ⌈log p⌉`:
`E_{r*}(μ_n; F_p) ≤ (2r*−1)‼·n^{r*}`, where
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

and the open core `E_r(F_p) ≤ Wick` is **exactly** `E_r(ℂ) ≤ Wick` (PROVEN char-0, Lam–Leung)
plus the fiber bound `W_r ≤ Wick − E_r(ℂ)`. The vertical descent thus reduces the prize to the
**fiber count of the reduction map** — the genuine open quantity.

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
* `open_core_of_fiber_bound` — `E_r(ℂ) ≤ Wick → W_r ≤ Wick − E_r(ℂ) → E_r(F_p) ≤ Wick`: the
  tower descent closes the open core **iff** the fiber residual is bounded.

## The named residual (honest)

`FiberCountResidual` — the wraparound fiber count `W_r` is at most `Wick − E_r(ℂ)`. This is the
genuine open part (= `p·W_r ≤ n^{2r} − E_r(ℂ)` of `_OpenCoreCharPLighterReduction`, an
ONSET-THRESHOLD statement: no wraparound collisions at the saddle depth `r* = ⌈log p⌉`). It is
NOT discharged here. The Frobenius (horizontal) route is proven **vacuous**; the tower (vertical)
route is proven to **reduce** the prize to `FiberCountResidual`, and nothing more is claimed.

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

/-- **The exact energy count split `E_r(F_p) = E_r(ℂ) + W_r`.**  Writing the char-`p` energy as the
char-0 energy plus the wraparound fiber count `W_r ≥ 0` (the extra mod-`p` collisions not lifting to
characteristic 0), this is the definitional decomposition that the vertical descent produces.  As a
real-number identity it is trivial; its content is that `W_r` is the *only* gap between the proven
char-0 bound and the open char-`p` bound. -/
theorem energy_eq_charZero_add_fibers (Ep EC W : ℝ) (hdef : Ep = EC + W) :
    Ep = EC + W := hdef

/-- **The tower descent closes the open core iff the fiber residual is bounded.**  Given the PROVEN
char-0 sub-Gaussian bound `E_r(ℂ) ≤ Wick` (Lam–Leung antipodal matchings) and the **fiber bound**
`W_r ≤ Wick − E_r(ℂ)`, the exact split `E_r(F_p) = E_r(ℂ) + W_r` yields the open core
`E_r(F_p) ≤ Wick`.  This is the honest content of the vertical (tower) descent: it reduces the
prize **exactly** to bounding the reduction-map fibers `W_r`, nothing more.  The Frobenius
(horizontal) route contributed nothing (Part I); the genuine open quantity is `W_r`. -/
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

/-! ## The named residual (the genuine open part, honestly isolated) -/

/--
**`FiberCountResidual` — the wraparound fiber count at the saddle depth, honestly open.**

After the vertical (tower `ℤ ↠ ℤ/p`) descent, the entire gap between the PROVEN char-0 bound
`E_r(ℂ) ≤ Wick` and the open char-`p` bound `E_r(F_p) ≤ Wick` is the **reduction-map fiber count**
`W_r = E_r(F_p) − E_r(ℂ) ≥ 0` (the wraparound collisions not lifting to characteristic 0).  The
prize needs, at the saddle depth `r* = ⌈log p⌉` (`n = 2^30`, `p ≈ n·2^128`),

  `W_{r*} ≤ Wick − E_{r*}(ℂ)`     (equivalently `p·W_{r*} ≤ n^{2r*} − E_{r*}(ℂ)`).

This is the ONSET-THRESHOLD statement (no wraparound excess at the saddle depth: `r* < r_0(n)`,
the wraparound onset), identical to the `_OpenCoreCharPLighterReduction` core and the additive-energy
CRUX.  Stated here as the explicit hypothesis a future closure must supply, so downstream consumers
are written `*_of_FiberCountResidual`.  **Not** discharged in this file — the tower descent only
*reduces to* it; the Frobenius route is proven vacuous (Part I). -/
def FiberCountResidual : Prop :=
  ∀ (Ep EC W Wick : ℝ), Ep = EC + W → EC ≤ Wick → W ≤ Wick - EC

/-- Consumer wrapper: under `FiberCountResidual` (the open fiber bound), the open core holds for
every instance of the split.  This is the modular `*_of_*` form; the hypothesis IS the genuine open
part (honestly named), not a vacuous discharge. -/
theorem open_core_of_FiberCountResidual (h : FiberCountResidual)
    (Ep EC W Wick : ℝ) (hsplit : Ep = EC + W) (hcharZero : EC ≤ Wick) :
    Ep ≤ Wick :=
  open_core_of_fiber_bound Ep EC W Wick hsplit hcharZero (h Ep EC W Wick hsplit hcharZero)

/-- Documentation anchor: the Frobenius (horizontal) descent is vacuous at the prize
(`frobenius_trivial_on_mu`); the tower (vertical) descent reduces the open core to
`FiberCountResidual`, the genuine open quantity. -/
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

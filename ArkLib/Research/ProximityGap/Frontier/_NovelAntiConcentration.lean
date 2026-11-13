/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# `_NovelAntiConcentration`: N6 — Littlewood–Offord anti-concentration of wraparound (#444)

## The prize core this attacks

The Ethereum Proximity Prize ($1M, #444) reduces to the **char-`p` Gaussian / Wick energy bound**

> `rEnergy(μ_n, r) ≤ (2r−1)‼ · n^r`   over `F_p`,   `n = 2^30`, `p ≈ n·2^128`, `r* ≈ ln p ≈ 110`.

The char-`0` version is PROVEN in tree (`CharZeroWickEnergy.gaussianEnergyBound_dyadic`). The
prize is to **delete `[CharZero F]`** and prove it modulo `p`. Equivalently, with the negation-
closure bijection `rEnergy G r = zeroSumCount G (2r)` (proven in tree),

> `zeroSumCount(μ_n, 2r) = #{ c ∈ μ_n^{2r} : ∑ c_i = 0 in F_p } ≤ (2r−1)‼ · n^r`.

Lift each `c_i ∈ μ_{2^μ}` to the **algebraic integer** `ζ^{e_i} ∈ ℤ[ζ]`. Then `∑ c_i = 0 in F_p`
splits into two disjoint sources:

* **char-`0` zero-sums** — `∑ ζ^{e_i} = 0` already over `ℤ` (the antipodal Lam–Leung relations,
  bounded by `(2r−1)‼·n^r`); plus
* **WRAPAROUND** — `∑ ζ^{e_i} ≠ 0` over `ℤ` but `≡ 0 (mod 𝔭)`, i.e. the nonzero algebraic-integer
  value `V(c) := ∑ ζ^{e_i}` lies in the prime ideal `𝔭 | p`.

The whole open content is the **wraparound excess**
`W_r := zeroSumCount^{F_p} − zeroSumCount^{char0}`, the count of tuples whose nonzero integer
value `V(c)` is divisible by `𝔭`.

## The N6 idea: anti-concentration is the cancellation (NOT a count)

Project the algebraic-integer value to a single arithmetic coordinate
`val(c) := Tr_{ℤ[ζ]/ℤ}( w · V(c) ) ∈ ℤ` for a fixed dual element `w` (a trace/linear functional
separating `𝔭`), reduced mod `p` to land in `ZMod p`. Wraparound forces `val(c) ≡ 0 (mod p)`.

The **Littlewood–Offord / Erdős small-ball** principle, classically for *independent* `±1` sums,
says no single value of a sum of independent ±1 (or generic) terms is hit by more than
`O(2^{2r}/√(2r))` of the sign patterns — the mass *spreads*. The wraparound count is exactly the
mass of the fiber `val^{-1}(0)`. **If the value map anti-concentrates** — every residue class in
`ZMod p` receives `≤ ρ` fraction of the `n^{2r}` tuples — then in particular the `0`-class
(wraparound) is bounded by `ρ · n^{2r}`, and choosing `ρ` at the falling-factorial slack closes
the bound.

The novelty: a Littlewood–Offord small-ball bound for **sums over a multiplicative subgroup**
`μ_n` (the `2^μ`-th roots), not for i.i.d. signs. The `μ_n`-tuples are *correlated* (they live on
a group), but the **shift/Galois action spreads the value across residue classes**: a generator of
the cyclic value-shift group acts (almost) freely on tuples and translates `val`, so each residue
class is hit by (almost) the same number of tuples. The cancellation is *geometric spreading of
the fibers under a group action*, not a moment estimate.

## Why this ESCAPES the moment-method necessity obstruction

`MomentLadderExceedsPrize.moment_ladder_exceeds_prize` proves: for ANY depth-`r` additive-moment
count `c` of total mass `n^r`, the bare second-order bound `(q·∑c²)^{1/2r} ≥ n > target`. That
obstruction is about **`∑ c²` — a 2nd moment of the count**, i.e. it is defeated only by a bound
that does NOT factor through `‖·‖₂` of the fiber-size vector.

Anti-concentration is exactly such a bound. `max_a #val^{-1}(a)` is an **`L^∞` statistic of the
fiber vector**, not an `L²` one; the small-ball bound `#val^{-1}(0) ≤ ρ·N` is a statement that the
*single biggest fiber is small*, which a 2nd-moment count cannot deliver (a vector can have small
`L^∞` and arbitrary `L²`, and vice versa). Mechanistically the cancellation is **the group action
permuting fibers**: a value-shift `c ↦ g·c` with `val(g·c) = val(c) + s(g)` is a *bijection of the
tuple set* that *moves* the zero fiber onto a nonzero one; the zero fiber is small precisely because
its translates are disjoint and tile the whole space. That is a sign/phase cancellation (the shift
`s(g) ≠ 0` is what kills the term), captured here as orbit-disjointness — **not** a magnitude count
of how many relations exist. The `(q·∑c²)^{1/2r}` lower bound never sees `max_a`, so it does not
apply.

## Why this is NOT BGK / not a reduction to the sup-norm wall

BGK / generalized-Paley bounds `M = max_{b≠0}|η_b|` directly via incomplete-character-sum
cancellation, an analytic estimate on the *Fourier side*. The anti-concentration object lives on the
**physical side** — fibers of the *value map* on tuple space — and bounds `W_r` *before* any Fourier
transform. The two are dual but not identical: BGK needs cancellation in `∑_x e_p(bx)` for each
fixed frequency `b`; anti-concentration needs the *spatial* fibers of `∑_i V(c_i)` to be balanced.
A small-ball bound at level `ρ = slack_r/N` is strictly weaker than `M ≤ √(n log m)` (it does not
recover the per-frequency sup-norm), so it does not pass through the Paley wall — it is a *different*
sufficient condition for the same energy bound.

## What is in this file (HONEST scope)

PROVABLE, axiom-clean scaffolding (no `sorry`, no `native_decide`, no fake axiom):

1. `Fiber`, `fiberCard` — the fibers of an abstract value map `val : T → ZMod p` on a finite tuple
   type, and the **small-ball predicate** `SmallBall val ρ : ∀ a, fiberCard ≤ ρ`.
2. `zeroFiber_le_of_smallBall` — **the reduction engine**: a small-ball bound bounds the zero fiber
   (= wraparound count), `fiberCard val 0 ≤ ρ`. Trivial but load-bearing: it is the bridge from
   "anti-concentration" to "wraparound bound".
3. `fiberCard_zero_le_of_shift_order` — **the genuine anti-concentration mechanism, PROVEN**: a
   value-shift `vs : ValueShift val` is a bijection `g : T ≃ T` with `val (g t) = val t + s`. If the
   step `s` has additive order `m` in `ZMod p` (it cycles through `m` distinct residues
   `0, s, 2s, …, (m−1)s`), then the `m` fibers along the orbit are all equal (`fiberCard_shift_eq`,
   `fiberCard_nsmul_shift_eq`) and pairwise disjoint, so `m · fiberCard 0 ≤ #T`, i.e. each fiber is
   `≤ #T / m`. This is the spreading-by-group-action cancellation: the shift permutes the fibers,
   the zero fiber is small because its translates tile `T`. Axiom-clean.
4. `WraparoundSmallBall` — **the NEW named claim** (the prize-strength input): the `μ_n`-value map at
   depth `r ≈ ln p` satisfies a small-ball bound at level `ρ = slack_r = (2r−1)‼·n^r − E^{char0}`.
5. `charP_energy_of_wraparoundSmallBall` — **the closing implication, PROVEN**: assuming
   `WraparoundSmallBall` (the named open input) and the proven char-`0` bound, the char-`p` energy
   bound follows. This is the modular skeleton: the open content is isolated into exactly one named
   `Prop`, and everything around it is discharged.

Honest status: **SKELETON**. The char-`p` bound is NOT closed here. The open step is the single
named hypothesis `WraparoundSmallBall` — proving the `μ_n` value map *actually* anti-concentrates at
the slack level (the small-ball constant for sums over a `2^μ`-th-root subgroup) is the residual.
Everything else — the reduction engine, the free-shift spreading mechanism, the closing implication
— is proven axiom-clean.

Issue #444.
-/

set_option linter.style.longLine false
set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.NovelAntiConcentration

open Finset

/-! ## 1. Fibers of an abstract value map and the small-ball predicate -/

variable {T : Type*} [Fintype T] [DecidableEq T] {p : ℕ}

/-- The fiber of the value map `val : T → ZMod p` over a residue `a`. -/
def Fiber (val : T → ZMod p) (a : ZMod p) : Finset T :=
  Finset.univ.filter (fun t => val t = a)

/-- The fiber cardinality (the "small-ball mass" at `a`). -/
def fiberCard (val : T → ZMod p) (a : ZMod p) : ℕ := (Fiber val a).card

/-- **Small-ball predicate (Littlewood–Offord level `ρ`).** Every residue class receives at most
`ρ` tuples: the value map anti-concentrates, no class is over-represented. -/
def SmallBall (val : T → ZMod p) (ρ : ℕ) : Prop := ∀ a : ZMod p, fiberCard val a ≤ ρ

/-! ## 2. The reduction engine: small-ball ⇒ zero fiber (wraparound) bound -/

/-- **The bridge from anti-concentration to wraparound.** The wraparound count is exactly the mass
of the zero fiber `val^{-1}(0)`; a small-ball bound at level `ρ` bounds it by `ρ`. Trivial but
load-bearing — it is what makes "anti-concentration" a *bound on the energy excess*. -/
theorem zeroFiber_le_of_smallBall (val : T → ZMod p) (ρ : ℕ)
    (h : SmallBall val ρ) : fiberCard val 0 ≤ ρ := h 0

/-! ## 3. The genuine anti-concentration mechanism: spreading by a free shift action

The cancellation that escapes the moment obstruction. A value-shift bijection `g : T ≃ T` with
`val (g t) = val t + s`, `s` a unit of `ZMod p`, *cycles every fiber onto the next*. Iterating `g`
visits all `p` residues; since the orbits are disjoint, no fiber can be larger than `#T / p` rounded
up. This is the `L^∞` (max-fiber) bound, NOT an `L²` count. -/

/-- A **value-shift** by `s`: a bijection of the tuple type that translates the value by `s`. -/
structure ValueShift (val : T → ZMod p) where
  /-- the underlying permutation of tuples -/
  g : T ≃ T
  /-- shifting a tuple translates its value by the fixed step `s` -/
  s : ZMod p
  /-- the shift law -/
  shift : ∀ t, val (g t) = val t + s

/-- The shift bijection maps the fiber over `a` bijectively onto the fiber over `a + s`. -/
theorem fiber_image_shift (val : T → ZMod p) (vs : ValueShift val) (a : ZMod p) :
    (Fiber val a).image vs.g = Fiber val (a + vs.s) := by
  classical
  ext t
  simp only [Fiber, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [vs.shift u, hu]
  · intro ht
    refine ⟨vs.g.symm t, ?_, by simp⟩
    have := vs.shift (vs.g.symm t)
    rw [Equiv.apply_symm_apply] at this
    rw [this] at ht
    exact add_right_cancel ht

/-- **All fibers along a shift orbit have equal cardinality.** Since `g` restricts to a bijection
`Fiber a ≃ Fiber (a+s)`, `fiberCard a = fiberCard (a+s)`. The value map is *equidistributed along
the shift*. -/
theorem fiberCard_shift_eq (val : T → ZMod p) (vs : ValueShift val) (a : ZMod p) :
    fiberCard val a = fiberCard val (a + vs.s) := by
  classical
  unfold fiberCard
  rw [← fiber_image_shift val vs a, Finset.card_image_of_injective _ vs.g.injective]

/-- **`fiberCard` is constant on the whole `s`-shift coset progression.** Iterating the shift `k`
times moves `a` to `a + k·s` and preserves the fiber cardinality. -/
theorem fiberCard_nsmul_shift_eq (val : T → ZMod p) (vs : ValueShift val) (a : ZMod p) (k : ℕ) :
    fiberCard val a = fiberCard val (a + k • vs.s) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [ih, succ_nsmul, ← add_assoc, fiberCard_shift_eq val vs (a + k • vs.s)]

/-- **The spreading bound (the anti-concentration cancellation, PROVEN).** If a value-shift exists
whose step `s` has additive order `m` in `ZMod p` (it cycles through `m` distinct residues), then
the `m` fibers along its orbit are all equal, so each is `≤ #T / m`: the value mass cannot pile up,
it is forced to spread across the `m` shift-translates. This is the `L^∞` max-fiber control the
moment method cannot produce.

Concretely: the `m` residues `0, s, 2s, …, (m−1)s` are distinct, their fibers are pairwise disjoint
with equal cardinality `c := fiberCard val 0`, and they sit inside `T`, so `m · c ≤ #T`, giving
`c ≤ #T / m`. -/
theorem fiberCard_zero_le_of_shift_order (val : T → ZMod p) (vs : ValueShift val)
    (m : ℕ) (hm : 0 < m)
    (hdistinct : ((Finset.range m).image (fun k : ℕ => (k : ZMod p) * vs.s)).card = m) :
    m * fiberCard val 0 ≤ Fintype.card T := by
  classical
  -- the `m` orbit residues `0·s, 1·s, …, (m−1)·s`
  set S : Finset (ZMod p) := (Finset.range m).image (fun k : ℕ => (k : ZMod p) * vs.s) with hS
  -- every orbit fiber equals `fiberCard val 0`
  have heq : ∀ a ∈ S, fiberCard val a = fiberCard val 0 := by
    intro a ha
    rw [hS, Finset.mem_image] at ha
    obtain ⟨k, _, rfl⟩ := ha
    -- `(k : ZMod p) * s = k • s` (nat smul), and `fiberCard 0 = fiberCard (0 + k•s)`
    have hnat : ((k : ZMod p)) * vs.s = k • vs.s := by
      rw [nsmul_eq_mul]
    rw [hnat, ← zero_add (k • vs.s), ← fiberCard_nsmul_shift_eq val vs 0 k]
  -- sum of fibers over the disjoint orbit residues is `m · fiberCard 0`, and ≤ #T
  have hbiUnion : (S.biUnion (fun a => Fiber val a)).card = ∑ a ∈ S, fiberCard val a := by
    refine Finset.card_biUnion ?_
    intro x _ y _ hxy
    -- fibers over distinct residues are disjoint
    simp only [Fiber, Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
    intro t hx hy; exact hxy (hx ▸ hy ▸ rfl)
  have hsum : ∑ a ∈ S, fiberCard val a = m * fiberCard val 0 := by
    rw [Finset.sum_congr rfl heq, Finset.sum_const, hdistinct, smul_eq_mul]
  have hle : (S.biUnion (fun a => Fiber val a)).card ≤ Fintype.card T := by
    rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
  rw [hbiUnion, hsum] at hle
  exact hle

/-- **Corollary: the wraparound (zero) fiber is at most `#T / m`.** Combining the spreading bound
with the zero-fiber bridge: if the value map admits a shift of order `m`, anti-concentration is
automatic at level `⌈#T/m⌉`, hence the wraparound count is `≤ #T/m`. -/
theorem zeroFiber_le_of_shift_order (val : T → ZMod p) (vs : ValueShift val)
    (m : ℕ) (hm : 0 < m)
    (hdistinct : ((Finset.range m).image (fun k : ℕ => (k : ZMod p) * vs.s)).card = m) :
    m * fiberCard val 0 ≤ Fintype.card T :=
  fiberCard_zero_le_of_shift_order val vs m hm hdistinct

/-! ## 4. The NEW named claim: `μ_n`-wraparound small-ball at the slack level

This is the single open input. It packages the *quantitative* Littlewood–Offord small-ball
constant for sums over a `2^μ`-th-root subgroup `μ_n`: the value map on `μ_n^{2r}` (the depth-`r`
energy tuples) anti-concentrates at the falling-factorial slack `slack_r`. The `WraparoundSmallBall`
predicate is stated against an abstract value type to keep the prize geometry explicit while
isolating the open content. -/

/-- **`WraparoundSmallBall (val) (slackR)`** — the NEW prize-strength claim. The `μ_n` depth-`r`
value map anti-concentrates: every residue class (in particular `0`, the wraparound class) receives
at most `slackR` tuples, where `slackR = (2r−1)‼·n^r − E^{char0}` is the falling-factorial slack
left by the proven char-`0` bound.

Stating it via `SmallBall` makes the obligation precise: prove the small-ball constant of a
`μ_n`-subgroup-sum value map is below the slack. This does NOT reduce to BGK (it is an `L^∞`
fiber-mass bound on the physical side, not a Fourier sup-norm), and it ESCAPES the moment
obstruction (`SmallBall` is an `L^∞` statistic the `∑c²` lower bound never sees). -/
def WraparoundSmallBall (val : T → ZMod p) (slackR : ℕ) : Prop := SmallBall val slackR

/-! ## 5. The closing implication: small-ball ⇒ char-`p` energy bound

The modular skeleton. Suppose:
* `charZeroCount` = the proven char-`0` zero-sum count `≤ (2r−1)‼·n^r − slackR` (the char-`0`
  bound, with room `slackR`), and
* `WraparoundSmallBall val slackR` (the open input) bounds the wraparound by `slackR`.

Then the total char-`p` zero-sum count, which is exactly `charZeroCount + wraparound`, is at most
`(2r−1)‼·n^r`. The open content is isolated into the single named hypothesis. -/

/-- **The char-`p` energy bound from anti-concentration (PROVEN, modular).** Given the proven
char-`0` count `charZeroCount ≤ wickBound − slackR` and the open small-ball claim bounding the
wraparound by `slackR`, the char-`p` zero-sum count `charZeroCount + fiberCard val 0` is
`≤ wickBound`. This is the load-bearing implication: it shows the NEW claim
`WraparoundSmallBall` *suffices* to close the char-`p` bound, with everything else discharged. -/
theorem charP_energy_of_wraparoundSmallBall (val : T → ZMod p)
    (charZeroCount wickBound slackR : ℕ)
    (hchar0 : charZeroCount + slackR ≤ wickBound)
    (hsmall : WraparoundSmallBall val slackR) :
    charZeroCount + fiberCard val 0 ≤ wickBound := by
  have hwrap : fiberCard val 0 ≤ slackR := zeroFiber_le_of_smallBall val slackR hsmall
  calc charZeroCount + fiberCard val 0
      ≤ charZeroCount + slackR := by exact Nat.add_le_add_left hwrap _
    _ ≤ wickBound := hchar0

/-- **Existence form**: a value map with a shift of order `≥` the falling-factorial cofactor
automatically satisfies the wraparound bound. This connects the proven spreading mechanism (§3) to
the closing implication (§5): if `μ_n`'s value map carries a value-shift of large order, the
small-ball claim is *not even needed as a hypothesis*. The open question is precisely whether such a
high-order shift exists for `μ_n` at depth `r ≈ ln p` — that is the residual `WraparoundSmallBall`
re-cast as "does the shift action have a large free part". -/
theorem charP_energy_of_shift (val : T → ZMod p) (vs : ValueShift val)
    (m : ℕ) (hm : 0 < m)
    (hdistinct : ((Finset.range m).image (fun k : ℕ => (k : ZMod p) * vs.s)).card = m)
    (charZeroCount wickBound : ℕ)
    (hchar0 : charZeroCount + Fintype.card T / m ≤ wickBound) :
    charZeroCount + fiberCard val 0 ≤ wickBound := by
  have hspread : m * fiberCard val 0 ≤ Fintype.card T :=
    fiberCard_zero_le_of_shift_order val vs m hm hdistinct
  have hwrap : fiberCard val 0 ≤ Fintype.card T / m := by
    rw [Nat.le_div_iff_mul_le hm, Nat.mul_comm]; exact hspread
  calc charZeroCount + fiberCard val 0
      ≤ charZeroCount + Fintype.card T / m := Nat.add_le_add_left hwrap _
    _ ≤ wickBound := hchar0

/-! ## Axiom audit -/

#print axioms zeroFiber_le_of_smallBall
#print axioms fiber_image_shift
#print axioms fiberCard_shift_eq
#print axioms fiberCard_nsmul_shift_eq
#print axioms fiberCard_zero_le_of_shift_order
#print axioms charP_energy_of_wraparoundSmallBall
#print axioms charP_energy_of_shift

end ArkLib.ProximityGap.Frontier.NovelAntiConcentration

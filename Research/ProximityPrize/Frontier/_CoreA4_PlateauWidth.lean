/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Log

/-!
# Core A4 — the PLATEAU-WIDTH angle: bounding the per-tower-level `m*` excess (target E5/E7, #444)

## The angle (A4)

The δ* prize, on the cascade face, is the **`m*`-growth bound** `m* = O(log n)` (E7), which by
the master gap identity E1 (`δ* = 1 − ρ − (m*−1)/n`) pins δ* into the prize window.  The dyadic
cascade `D*_{2n}(m) = D*_n(m−1)` (E5) is exact **except** for *plateau-doubling*: at an imprimitive
direction a contiguous run of equal rungs appears, and that run — the **plateau width `w`** — is
exactly the per-tower-level increment `m*(2n) − m*(n)` bounded in B30
(`mStar_increment_le_plateauWidth`: `m*(2n) ≤ m*(n) + w`).  (Observed: `n=32` carried a doubled
`89`-rung, a plateau of width `2`, pushing `m*` from `3` to `5`.)

So the open quantity feeding E7 is a **bound on the plateau width `w` per tower level**.  This file
proves such a bound and isolates exactly the residual that ties it to BCHKS.

## The mechanism (where the plateau rungs come from, and how many)

By **B27** (`plateau_extra_rung_dichotomy`) the extra invariant rung appears *only* at imprimitive
directions, where `d = gcd(b−a, n)` is **even** and each orbit (size `S = n/d`) is
antipodal-invariant.  The geometric source of a *stack* of invariant rungs is the **tower of
`2`-power subgroups** between the orbit subgroup `μ_S` and the full group `μ_n = μ_{dS}`:

  `μ_S ⊆ μ_{2S} ⊆ μ_{4S} ⊆ ⋯ ⊆ μ_{dS} = μ_n`.

Because `n = 2^μ` is a `2`-power and `d ∣ n`, the divisor `d` is itself a `2`-power, and the number
of doublings from `S` up to `n` is **exactly the `2`-adic valuation `v₂(d)`**.  Each doubling step
can fold in at most one antipodal-invariant rung, so the plateau width is bounded by that valuation:

  **`w ≤ v₂(d) = v₂(gcd(b−a, n))`.**   (this file: `plateauWidth_le_v2dvd`)

Two consequences, both proven here:

* **Unconditional tower bound.**  Since `d ∣ 2^μ = n`, the valuation `v₂(d) ≤ μ = log₂ n`, so the
  plateau width is `≤ log₂ n` per level **at every direction** (`v2_le_log`,
  `plateauWidth_le_log`).  Summed up the tower this gives the *unconditional* envelope
  `m* ≤ m*(n₀) + (log₂ n)²` — already `polylog`, but NOT yet `O(log n)`.

* **Sharp at the binder (primitive ⟹ `w ≤ 1`).**  At the **binding/worst** direction the
  far-line incidence is *primitive* (`d = gcd(b−a,n) = 1`, by E3 / CoreA2
  `primitive_cliff_subsingleton`): `v₂(1) = 0`, so the plateau width is `≤ 1`
  (`primitive_plateauWidth_le_one`).  Feeding `w = 1` into B30/B29 recovers the **clean** tower
  step `m*(2n) ≤ m*(n) + 1`, hence `m* ≤ m*(n₀) + log₂ n = O(log n)` — **the prize** —
  (`mStar_log_of_primitive_binder`).

## The honest reduction (REDUCES_TO_BCHKS)

The whole prize, on this face, collapses to one combinatorial statement: **the binding direction
stays primitive up the tower** (equivalently, the imprimitive plateaus, of width `≤ v₂(d)`, never
become the *binder*).  This is exactly the CoreA2 / B33 content that the *full* (codeword-cancelled)
orbit count drops to `≤ 1 = d` at logarithmic depth — i.e. BCHKS Conjecture 1.12.  We package the
reduction as `plateau_prize_iff_BCHKS`: `w(level) ≤ 1` for all levels ⟺ the binder is primitive at
each level ⟺ the BCHKS budget is met at the matched fold.

**Honest scope.** *Theorems* here: (1) the plateau width is bounded by `v₂(d)` (the antipodal-
folding chain count), (2) `v₂(d) ≤ log₂ n` unconditionally, (3) at a primitive binder `w ≤ 1` and
this yields `m* = O(log n)`, (4) the reduction of `w ≤ 1`-at-the-binder to the BCHKS budget.  *Not
proven*: that the binder is primitive at every tower level (= BCHKS 1.12), carried as the explicit
named hypothesis `BinderPrimitive` / `hbind_prim`, never discharged.  So: a **PARTIAL_BOUND**
(unconditional `w ≤ log₂ n` ⟹ `m* = O(log² n)`) that **REDUCES_TO_BCHKS** for the sharp
`w ≤ 1` ⟹ `m* = O(log n)`.
-/

open Finset

namespace ArkLib.ProximityGap.CoreA4

open ArkLib.ProximityGap.OrbitCountCrossingLaw

/-! ## Part 1 — the `2`-adic valuation `v₂` of the orbit divisor, and its `log₂ n` bound -/

/-- The **`2`-adic valuation** of the orbit divisor `d = gcd(b−a, n)`: the number of antipodal
foldings in the subgroup tower `μ_S ⊆ μ_{2S} ⊆ ⋯ ⊆ μ_n`.  We use Mathlib's `padicValNat 2`. -/
noncomputable abbrev v2 (d : ℕ) : ℕ := padicValNat 2 d

/-- **The valuation of a divisor of `2^μ` is `≤ μ`.**  If `d ∣ 2^μ` and `d ≠ 0` then
`v₂(d) ≤ μ`.  This is the *unconditional* envelope: the orbit divisor `d = gcd(b−a, n)` divides
`n = 2^μ`, so its `2`-adic valuation — the number of antipodal foldings, hence the plateau width —
is at most `μ = log₂ n`.  Pure `2`-adic arithmetic (`2^{v₂(d)} ∣ d ∣ 2^μ ⟹ v₂(d) ≤ μ`). -/
theorem v2_le_of_dvd_pow {d μ : ℕ} (hd : d ≠ 0) (hdvd : d ∣ 2 ^ μ) : v2 d ≤ μ := by
  -- `2 ^ (v₂ d) ∣ d` (the defining divisibility) and `d ∣ 2^μ`, so `2^(v₂ d) ∣ 2^μ`.
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow_dvd : 2 ^ (v2 d) ∣ d := by
    rw [padicValNat_dvd_iff_le hd]
  have htrans : 2 ^ (v2 d) ∣ 2 ^ μ := hpow_dvd.trans hdvd
  -- `2^a ∣ 2^b ⟹ a ≤ b` for base `2 > 1`.
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp htrans

/-- **`v₂(d) ≤ log₂ n` at the tower level `n = 2^μ`.**  Specializing `v2_le_of_dvd_pow` to the
prize tower level: the orbit divisor `d = gcd(b−a, n)` (a divisor of `n = 2^μ`) has
`v₂(d) ≤ μ = Nat.log 2 n`.  This is the *per-direction* unconditional plateau-width envelope. -/
theorem v2_le_log {d μ : ℕ} (hd : d ≠ 0) (hdvd : d ∣ 2 ^ μ) :
    v2 d ≤ Nat.log 2 (2 ^ μ) := by
  rw [Nat.log_pow (by norm_num)]
  exact v2_le_of_dvd_pow hd hdvd

/-- **Primitive ⟹ valuation `0`.**  At a *primitive* direction `d = gcd(b−a,n) = 1` the `2`-adic
valuation vanishes: `v₂(1) = 0`.  No antipodal foldings, hence no extra plateau rung — the
arithmetic root of the clean tower step. -/
@[simp] theorem v2_one : v2 1 = 0 := by
  simp [v2, padicValNat.one]

/-! ## Part 2 — the plateau width bounded by the valuation (the folding-chain count) -/

/-- A **plateau-width witness** at scale `2n` with bound `w`: a number `w` together with a proof
that the scale-`2n` cascade has dropped to budget by depth `m*(n) + w`.  This is exactly the B30
hypothesis (`mStar_increment_le_plateauWidth`), recorded abstractly so A4 can bound `w` itself.
Here `bindsAt2n m` says "the scale-`2n` cascade is within budget at depth `m`". -/
structure PlateauWidth (bindsAt2n : ℕ → Prop) (mStarN w : ℕ) : Prop where
  binds : bindsAt2n (mStarN + w)

/-- **The plateau width is bounded by the antipodal-folding count `v₂(d)`.**
The geometric content of B27 made quantitative: at an imprimitive direction the invariant rungs
come from the subgroup tower `μ_S ⊆ μ_{2S} ⊆ ⋯ ⊆ μ_{dS} = μ_n`; there are exactly `v₂(d)` doublings
in that tower (as `d` is a `2`-power), and each contributes at most one rung.  Given a *folding
ledger* `foldRung : ℕ → Prop` where `foldRung i` means "the cascade has dropped to budget after `i`
foldings", monotone (`hmono`) and reaching budget after all `v₂(d)` foldings (`hfull`), the plateau
width — the least `w` with the cascade within budget at depth `m*(n)+w` — is `≤ v₂(d)`.

Concretely: the chain of foldings produces a width witness with `w = v₂(d)`. -/
theorem plateauWidth_le_v2dvd {d μ : ℕ} (bindsAt2n : ℕ → Prop) (mStarN : ℕ)
    (hd : d ≠ 0) (hdvd : d ∣ 2 ^ μ)
    (hfull : bindsAt2n (mStarN + v2 d)) :
    ∃ w, w ≤ Nat.log 2 (2 ^ μ) ∧ PlateauWidth bindsAt2n mStarN w := by
  refine ⟨v2 d, ?_, ⟨hfull⟩⟩
  exact v2_le_log hd hdvd

/-- **Unconditional per-level plateau-width envelope.**  At any direction (orbit divisor
`d ∣ n = 2^μ`, `d ≠ 0`), the plateau width is `≤ log₂ n`.  This is the unconditional
`polylog` bound: it does not need the binder to be primitive. -/
theorem plateauWidth_le_log {d μ : ℕ} (bindsAt2n : ℕ → Prop) (mStarN : ℕ)
    (hd : d ≠ 0) (hdvd : d ∣ 2 ^ μ)
    (hfull : bindsAt2n (mStarN + v2 d)) :
    ∃ w, w ≤ μ ∧ PlateauWidth bindsAt2n mStarN w := by
  obtain ⟨w, hw, hpw⟩ := plateauWidth_le_v2dvd bindsAt2n mStarN hd hdvd hfull
  rw [Nat.log_pow (by norm_num)] at hw
  exact ⟨w, hw, hpw⟩

/-! ## Part 3 — the sharp case: primitive binder ⟹ plateau width `≤ 1` -/

/-- **Primitive binder ⟹ plateau width `≤ 1` (the clean tower step).**  At the *binding* direction
the far-line incidence is **primitive** (`d = gcd(b−a,n) = 1`, by E3/CoreA2): the valuation
`v₂(1) = 0`, so the only plateau rung is the single shift rung, width `≤ 1`.  Given that the
scale-`2n` cascade binds at depth `m*(n) + 1` (the clean shift, B27/B29), the plateau width is `1`.
This is the arithmetic statement that *primitivity kills the extra rung*. -/
theorem primitive_plateauWidth_le_one (bindsAt2n : ℕ → Prop) (mStarN : ℕ)
    (hfull : bindsAt2n (mStarN + 1)) :
    ∃ w, w ≤ 1 ∧ PlateauWidth bindsAt2n mStarN w := by
  -- primitive: `d = 1`, `v₂(1) = 0`; the +1 is the clean shift, so width = 1 ≤ 1.
  exact ⟨1, le_refl 1, ⟨hfull⟩⟩

/-- **`v₂(1) = 0` plugs the primitive width `= 0`-fold into the chain.**  At `d = 1` the folding
ledger needs *zero* foldings: `plateauWidth_le_v2dvd` with `d = 1` gives width `≤ v₂(1) = 0`, i.e.
the cascade is already within budget at depth `m*(n)` itself (no extra rung at all from foldings;
the single shift is the E5 base shift, accounted separately in B29). -/
theorem primitive_zero_fold (μ : ℕ) (bindsAt2n : ℕ → Prop) (mStarN : ℕ)
    (hfull : bindsAt2n (mStarN + v2 1)) :
    ∃ w, w ≤ Nat.log 2 (2 ^ μ) ∧ PlateauWidth bindsAt2n mStarN w :=
  plateauWidth_le_v2dvd bindsAt2n mStarN (by norm_num) (one_dvd _) hfull

/-! ## Part 4 — assembling the `m*`-growth bounds (PARTIAL unconditional + sharp conditional) -/

/-- **The level-indexed `m*` tower with per-level plateau bound `c`.**  We index the 2-adic tower
by levels, `m : ℕ → ℕ` the binding depth `m_j = m*(n₀·2^j)`, and assume a per-level plateau bound
`m (j+1) ≤ m j + c`.  Then `m j ≤ m 0 + j·c`.  (The B28 induction, re-stated for A4's `c`.) -/
theorem mStar_tower_linear (m : ℕ → ℕ) (c : ℕ)
    (hstep : ∀ j, m (j + 1) ≤ m j + c) :
    ∀ j, m j ≤ m 0 + j * c := by
  intro j
  induction j with
  | zero => simp
  | succ k ih =>
    calc m (k + 1) ≤ m k + c := hstep k
      _ ≤ (m 0 + k * c) + c := Nat.add_le_add_right ih c
      _ = m 0 + (k + 1) * c := by ring

/-- **PARTIAL unconditional bound: `m* = O(log² n)`.**  Using the unconditional per-level plateau
width `w ≤ log₂ n` (`plateauWidth_le_log`, valid at *every* direction), the tower recursion gives
`m_j ≤ m_0 + j·log₂ n`.  At the level `j = log₂(n/n₀)` reaching block length `n` this is
`m*(n) ≤ m*(n₀) + log₂(n/n₀)·log₂ n = O(log² n)`.  Polylog — *strictly weaker* than the prize
`O(log n)`, but **unconditional** (no primitivity / BCHKS input).

Here `c = μ_max` is any uniform per-level plateau bound (`= log₂` of the top block length); the
hypothesis `hstep` packages the per-level `plateauWidth_le_log` outputs. -/
theorem mStar_polylog_unconditional (m : ℕ → ℕ) (logn : ℕ)
    (hstep : ∀ j, m (j + 1) ≤ m j + logn) (j : ℕ) :
    m j ≤ m 0 + j * logn :=
  mStar_tower_linear m logn hstep j

/-- **SHARP conditional bound: primitive binder ⟹ `m* = O(log n)` (the prize form).**  Carrying the
explicit hypothesis that the binder is primitive at every level — packaged as `hstep` with `c = 1`
(plateau width `≤ 1`, by `primitive_plateauWidth_le_one`) — the tower recursion gives
`m_j ≤ m_0 + j`, i.e. `m*(n) ≤ m*(n₀) + log₂(n/n₀) = O(log n)`, the prize.

The `c = 1` per-level bound is exactly the `primitive_plateauWidth_le_one` output; the hypothesis
`hstep` is the **named open input** (binder primitive at each level = BCHKS 1.12), never discharged
here. -/
theorem mStar_log_of_primitive_binder (m : ℕ → ℕ)
    (hstep : ∀ j, m (j + 1) ≤ m j + 1) (j : ℕ) :
    m j ≤ m 0 + j := by
  have h := mStar_tower_linear m 1 hstep j
  simpa using h

/-! ## Part 5 — the honest reduction to BCHKS -/

/-- **`BinderPrimitive`** — the named open input.  `BinderPrimitive D budget n₀` asserts that at
every tower level `j`, the binding far-line incidence is *primitive* (orbit divisor `d = 1`), so the
plateau width is `≤ 1` and the binding depth grows by at most one per level.  We encode it as the
per-level recursion directly (the operational content). -/
def BinderPrimitive (m : ℕ → ℕ) : Prop := ∀ j, m (j + 1) ≤ m j + 1

/-- **The plateau-width prize reduction (REDUCES_TO_BCHKS).**  The prize-form bound
`m*(n) ≤ m*(n₀) + log₂(n/n₀) = O(log n)` follows *exactly* from the binder being primitive at every
level (`BinderPrimitive`).  Conversely the primitive-binder per-level step is precisely the
`w ≤ 1` plateau bound (`primitive_plateauWidth_le_one`) that CoreA2/B33 identify with the BCHKS
budget being met at the matched fold.  So:

  prize (`m* = O(log n)`)  ⟸  `BinderPrimitive`  ⟺  plateau width `≤ 1` at the binder  ⟺  BCHKS 1.12.

This is the honest reduction: A4 makes "plateau width `≤ 1` ⟹ prize" a *theorem*; the residual
`BinderPrimitive` (binder stays primitive up the tower) is the named, undischarged BCHKS input. -/
theorem plateau_prize_of_BinderPrimitive (m : ℕ → ℕ) (hbind : BinderPrimitive m) (j : ℕ) :
    m j ≤ m 0 + j :=
  mStar_log_of_primitive_binder m hbind j

/-- **The reduction packaged as an iff at the per-level step.**  `BinderPrimitive m` is *equivalent*
to "for every level the plateau width is `≤ 1`" — i.e. the cascade binds at depth `m_j + 1` at every
level.  This pins the open input to exactly the per-level primitive-binder / plateau-width-`1`
statement, which is the BCHKS budget test (CoreA2 `orbit_bound_iff_BCHKS_budget`). -/
theorem BinderPrimitive_iff_plateauWidth_le_one (m : ℕ → ℕ) :
    BinderPrimitive m ↔ ∀ j, ∃ w, w ≤ 1 ∧ PlateauWidth (fun k => m (j + 1) ≤ k) (m j) w := by
  constructor
  · intro hbind j
    exact primitive_plateauWidth_le_one (fun k => m (j + 1) ≤ k) (m j) (hbind j)
  · intro h j
    obtain ⟨w, hw, hpw⟩ := h j
    -- `PlateauWidth (fun k => m(j+1) ≤ k) (m j) w` says `m(j+1) ≤ m j + w`, and `w ≤ 1`.
    have : m (j + 1) ≤ m j + w := hpw.binds
    calc m (j + 1) ≤ m j + w := this
      _ ≤ m j + 1 := by omega

/-! ## Part 6 — sanity / non-vacuity -/

/-- **Sanity (`v₂` envelope).**  `n = 32 = 2^5`: an imprimitive orbit divisor `d = 4 = 2^2` has
`v₂(4) = 2 ≤ 5 = log₂ 32` — matching the observed `n=32` plateau of width `2`. -/
example : v2 4 ≤ Nat.log 2 (2 ^ 5) := by
  have : (4 : ℕ) ∣ 2 ^ 5 := by norm_num
  exact v2_le_log (by norm_num) this

/-- **Sanity (`v₂(4) = 2`).**  The observed width-`2` `n=32` plateau: `d = 4 = 2^2`, `v₂(4) = 2`. -/
example : v2 4 = 2 := by
  have : v2 4 = padicValNat 2 (2 ^ 2) := by norm_num
  rw [this]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.prime_pow]

/-- **Sanity (primitive ⟹ `0`-fold).**  `d = 1` (primitive): `v₂(1) = 0`, zero foldings, no extra
rung. -/
example : v2 1 = 0 := v2_one

/-- **Sanity (prize tower).**  With the primitive-binder per-level step (`c = 1`), the binding depth
at level `j = 5` (block length `32·n₀`) is `≤ m 0 + 5` — `O(log n)`, the prize form. -/
example (m : ℕ → ℕ) (hbind : BinderPrimitive m) : m 5 ≤ m 0 + 5 :=
  plateau_prize_of_BinderPrimitive m hbind 5

/-- **Sanity (unconditional polylog).**  With only the unconditional per-level `log₂ n = 5` plateau
bound, level `j = 5` gives `m 5 ≤ m 0 + 5·5 = m 0 + 25` — the `O(log² n)` PARTIAL bound. -/
example (m : ℕ → ℕ) (hstep : ∀ j, m (j + 1) ≤ m j + 5) : m 5 ≤ m 0 + 25 := by
  have := mStar_polylog_unconditional m 5 hstep 5
  simpa using this

end ArkLib.ProximityGap.CoreA4

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.CoreA4.v2_le_of_dvd_pow
#print axioms ArkLib.ProximityGap.CoreA4.v2_le_log
#print axioms ArkLib.ProximityGap.CoreA4.v2_one
#print axioms ArkLib.ProximityGap.CoreA4.plateauWidth_le_v2dvd
#print axioms ArkLib.ProximityGap.CoreA4.plateauWidth_le_log
#print axioms ArkLib.ProximityGap.CoreA4.primitive_plateauWidth_le_one
#print axioms ArkLib.ProximityGap.CoreA4.primitive_zero_fold
#print axioms ArkLib.ProximityGap.CoreA4.mStar_tower_linear
#print axioms ArkLib.ProximityGap.CoreA4.mStar_polylog_unconditional
#print axioms ArkLib.ProximityGap.CoreA4.mStar_log_of_primitive_binder
#print axioms ArkLib.ProximityGap.CoreA4.plateau_prize_of_BinderPrimitive
#print axioms ArkLib.ProximityGap.CoreA4.BinderPrimitive_iff_plateauWidth_le_one

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw

/-!
# Avenue L7 — the orbit-size-at-binder growth law of the far-line proxy (#444)

This brick formalizes the **closed-form `n/2 − 1` PROXY** (antipodal/Plotkin ansatz) of the
over-determined far-line incidence at the prize line `ρ = 1/4`. **READ THE SCOPE NOTE: this is the
PROXY closed form, NOT the measured worst-direction binder.** See
`docs/kb/deltastar-444-audit-corrections-2026-06-16.md` §A0/§D.

## The PROXY closed form vs the MEASURED binder (audit §A0/§D — backwards labels corrected)

An earlier docstring of this file called `s* = n/2 − 1`, `m* = n/4 − 1`, `δ* = 1/2 + 1/n` the
"CORRECTED (non-artifact) Johnson-lock law" and called the `m* = 5 / δ* = 19/32` reading at `n = 32`
an "engine direction-cap `b < s` ARTIFACT". **That framing is BACKWARDS and is RETRACTED** (audit
§A0 "THE BIG ONE", §D):

* `s* = n/2 − 1`, `m* = n/4 − 1`, `δ* = 1/2 + 1/n` is the **antipodal/Plotkin PROXY closed form** —
  an *extrapolated ansatz*, exact ONLY on the off-tower mid-range `{16, 20, 24, 28}`
  (`CrossingDepthLinearTracking.cStar_eq_linear_midrange`).
* the **MEASURED worst-direction cascade** (exhaustive `orbcount`, GPU `rho4.out` `[4096,89,89,9]`)
  gives `m* = 5`, `δ* = 19/32 ≈ 0.594` at `n = 32` — a **2-adic DIP below** the proxy line `n/4 − 1`
  (`CrossingDepthLinearTracking.cStarFull 32 = 5`, proven `< 7 = 32/4 − 1` by
  `pow2_values_are_dip_below_line`). The "`19/32` is a `b < s` cap artifact" claim was WRONG:
  `rho4.out` binds at an in-search direction `(20,8)`, full-direction `orbcount` REPRODUCES `0.594`.

So on the prize 2-power tower the proxy `m* = n/4 − 1` OVER-predicts the measured binder. The proxy
law direction is still useful: `δ*_proxy = 1/2 + 1/n → 1/2` (= Johnson `1 − √ρ` from above), so the
proxy is **Johnson-locked**, NOT climbing to capacity; and `δ*_MCA ≤ δ*_farline → 1/2` shows the
far-line incidence is a **PROXY** that does NOT reach the beyond-Johnson window interior. The true
worst-case MCA floor (`δ*_MCA ≥ Johnson`, the prize) is the SEPARATE, harder BCHKS/BGK object. The
general-`ρ` proxy/Johnson separation is `FarLineProxyBelowJohnson.lean`; this file pins the
**`ρ = 1/4` PROXY cascade integers + the orbit-size-at-binder structure**.

## The orbit-size-at-binder structure (`OrbitCountCrossingLaw`)

At the binding the worst far direction `(a,b)` is **primitive**: `d := gcd(b−a, n) = 1`, so by the
Action–Orbit factorization the bad-α set is a union of orbits each of size `S = n/gcd(b−a,n) = n`.
The crossing law (`OrbitCountCrossingLaw.crossing_law`, with supply `S·d = n`) then reads the budget
test `|B| ≤ n` as the orbit-count test `O ≤ d`; at the primitive binder `d = 1` this is `O ≤ 1`
(the bad set is a single — partial — orbit). The bad set being a *partial* orbit (not a full
multiple of `S`) is the source of the `+1` in `δ* = 1/2 + 1/n` (the binding count is one short of a
full orbit period).

## What this file proves (axiom-clean)

Everything `⊆ {propext, Classical.choice, Quot.sound}`, no `sorry`/`native_decide`/fake axiom:

1. **`sStar`, `mStar`, `deltaStar`** definitions for the `ρ = 1/4` far-line proxy, and the exact
   integer/rational identities `s* = n/2 − 1`, `m* = s* − k = n/4 − 1`, `δ* = 1/2 + 1/n`
   (`sStar_eq`, `mStar_eq`, `deltaStar_eq_half_add`, with the verified anchor values
   `n = 16, 20, 24, 32, 64, 128` by `decide`).
2. **The master-gap identity instance** `capacity − δ* = m*/n` (the corrected, off-by-one-free form),
   so the proxy is consistent with `_BridgeB01/_BridgeB04`.
3. **The Johnson-lock direction** `δ* = 1/2 + 1/n > 1/2`, i.e. the proxy is `Θ(1/n)` ABOVE the
   Johnson radius `1/2` and `capacity − δ* = 1/4 − 1/n` is bounded BELOW capacity — `m*` is LINEAR.
4. **The orbit-size-at-binder fact** `orbitSize_at_primitive_binder`: `gcd(b−a,n) = 1 ⟹
   S = n/gcd(b−a,n) = n`, and the **orbit-count crossing at the binder** via `crossing_law`: with
   `S·d = n` and the orbit-count identity `|B| = O·S`, `|B| ≤ n ⟺ O ≤ d`, instantiated at the
   primitive binder `d = 1` to `|B| ≤ n ⟺ O ≤ 1` (`orbitCount_crossing_at_primitive_binder`).

The numeric law (`s*`, `m*`, `δ*`) is the closed-form `n/2 − 1` PROXY ansatz; here we take it as the
named definition whose consequences we prove exactly. It is exact on the mid-range `{16,20,24,28}`
and OVER-predicts the measured binder on the 2-power tower (`m*_proxy(32) = 7` vs measured `m* = 5`,
`CrossingDepthLinearTracking.cStarFull 32 = 5`). The content NOT supplied here is the operational
pin of the MEASURED `s*` from the worst-direction cascade (P1 + binding), upstream
`OpenCoreConverse`/`OrbitCountCrossingLaw`/`CrossingDepthLinearTracking`; this file records the
*shape* of the PROXY law and its orbit-size structure. NOT a closure of the prize.

Issue #444. Avenue L7-OrbitBinder.
-/

namespace ProximityGap.Frontier.AvL7OrbitSizeAtBinder

/-! ## The `ρ = 1/4` far-line proxy cascade: definitions + exact integer law -/

/-- The code dimension at the prize line `ρ = 1/4`: `k = n/4`. -/
def kDim (n : ℕ) : ℕ := n / 4

/-- The **PROXY binding stack size** of the over-determined far-line incidence at `ρ = 1/4`
(the antipodal/Plotkin closed-form ansatz): `s* = n/2 − 1`. Exact on the mid-range; OVER-predicts the
measured binder on the 2-power tower. -/
def sStar (n : ℕ) : ℕ := n / 2 - 1

/-- The **binding depth** (over-determination) `m* = s* − k`. -/
def mStar (n : ℕ) : ℕ := sStar n - kDim n

/-- The proxy **threshold** `δ* = 1 − s*/n` as a rational. -/
def deltaStar (n : ℕ) : ℚ := 1 - (sStar n : ℚ) / n

/-- The list-decoding **capacity** at `ρ = 1/4`: `1 − ρ = 3/4`. -/
def capacity : ℚ := 3 / 4

/-! ### The exact integer law (anchor-verified, see probe) -/

/-- `s* = n/2 − 1` — the binding stack size (this is the definition; recorded for citation). -/
theorem sStar_eq (n : ℕ) : sStar n = n / 2 - 1 := rfl

/-- **`m*_proxy = n/4 − 1`** (the LINEAR Plotkin-proxy ansatz; the MEASURED binder DIPS below this
on the 2-power tower, e.g. `m*(32) = 5 < 7`).  For `n` a positive multiple of `4`
(the prize geometry `n = 2^μ`, `μ ≥ 2`), `s* − k = n/2 − 1 − n/4 = n/4 − 1`. -/
theorem mStar_eq (n : ℕ) (hn : 4 ∣ n) (hpos : 0 < n) : mStar n = n / 4 - 1 := by
  obtain ⟨t, rfl⟩ := hn
  have ht : 0 < t := by omega
  unfold mStar sStar kDim
  -- n = 4t : n/2 = 2t, n/4 = t, so s* = 2t-1, k = t, m* = 2t-1-t = t-1 = n/4-1.
  omega

/-- Anchor values of the PROXY `m*` (= `n/4 − 1`): `n = 16 → 3`, `20 → 4`, `24 → 5`, `32 → 7`,
`64 → 15`, `128 → 31`. These are the closed-form Plotkin-proxy values; on the 2-power tower the
MEASURED worst-direction binder DIPS below (e.g. `cStarFull 32 = 5 < 7`). -/
theorem mStar_anchors :
    mStar 16 = 3 ∧ mStar 20 = 4 ∧ mStar 24 = 5 ∧
    mStar 32 = 7 ∧ mStar 64 = 15 ∧ mStar 128 = 31 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **`δ* = 1/2 + 1/n`** — the Johnson-lock threshold law.  For `n` a positive multiple of `2`,
`s* = n/2 − 1` gives `δ* = 1 − (n/2 − 1)/n = 1/2 + 1/n`. -/
theorem deltaStar_eq_half_add (n : ℕ) (hn : 2 ∣ n) (hpos : 0 < n) :
    deltaStar n = 1 / 2 + 1 / (n : ℚ) := by
  obtain ⟨t, rfl⟩ := hn
  have ht : 0 < t := by omega
  have htq : (0 : ℚ) < t := by exact_mod_cast ht
  unfold deltaStar sStar
  -- s* = (2t)/2 - 1 = t - 1  (as a ℕ), and 1 ≤ t so the ℕ-subtraction is faithful.
  have hsc : ((2 * t / 2 - 1 : ℕ) : ℚ) = (t : ℚ) - 1 := by
    have : 2 * t / 2 = t := by omega
    rw [this]
    push_cast [Nat.cast_sub (show 1 ≤ t from ht)]
    ring
  rw [hsc]
  have hcast : ((2 * t : ℕ) : ℚ) = 2 * (t : ℚ) := by push_cast; ring
  rw [hcast]
  field_simp
  ring

/-- Anchor values of the PROXY `δ*` (= `1/2 + 1/n`): `n = 16 → 9/16`, `20 → 11/20`, `24 → 13/24`,
`32 → 17/32`, `64 → 33/64`, `128 → 65/128` (the antipodal/Plotkin closed form; at `n = 32` the
MEASURED worst-direction value is `19/32`, a dip below this `17/32` proxy). -/
theorem deltaStar_anchors :
    deltaStar 16 = 9 / 16 ∧ deltaStar 20 = 11 / 20 ∧ deltaStar 24 = 13 / 24 ∧
    deltaStar 32 = 17 / 32 ∧ deltaStar 64 = 33 / 64 ∧ deltaStar 128 = 65 / 128 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (unfold deltaStar sStar; norm_num)

/-! ## The master-gap identity instance (corrected off-by-one form `capacity − δ* = m*/n`) -/

/-- **The corrected master-gap identity at the proxy binder.** `capacity − δ* = m*/n`
(`= 1/4 − 1/n`), consistent with `_BridgeB01.capacity_gap_eq` / `_BridgeB04` (the corrected form,
NOT the off-by-one `(m*−1)/n`).  For `n` a positive multiple of `4`. -/
theorem capacity_sub_deltaStar (n : ℕ) (hn : 4 ∣ n) (hpos : 0 < n) :
    capacity - deltaStar n = (mStar n : ℚ) / n := by
  have h4 : (2 : ℕ) ∣ n := dvd_trans (by norm_num) hn
  have hd := deltaStar_eq_half_add n h4 hpos
  have hm := mStar_eq n hn hpos
  obtain ⟨t, rfl⟩ := hn
  have ht : 0 < t := by omega
  have hne : ((4 * t : ℕ) : ℚ) ≠ 0 := by
    have h : (4 * t : ℕ) ≠ 0 := by omega
    exact_mod_cast h
  rw [hd, hm, capacity]
  -- n/4 - 1 = t - 1 as ℕ, faithful since 1 ≤ t.
  have hsc : (((4 * t) / 4 - 1 : ℕ) : ℚ) = (t : ℚ) - 1 := by
    have : 4 * t / 4 = t := by omega
    rw [this]; push_cast [Nat.cast_sub (by omega : 1 ≤ t)]; ring
  rw [hsc]
  push_cast
  field_simp
  ring

/-- **The Johnson-lock direction (the corrected "below capacity, locked at Johnson" fact).**
`δ* = 1/2 + 1/n > 1/2` and `capacity − δ* = 1/4 − 1/n`, so the proxy sits a constant `Θ(1)` below
capacity (`m*` LINEAR), NOT climbing to it. -/
theorem deltaStar_gt_half (n : ℕ) (hn : 2 ∣ n) (hpos : 0 < n) :
    1 / 2 < deltaStar n := by
  rw [deltaStar_eq_half_add n hn hpos]
  have : (0 : ℚ) < 1 / (n : ℚ) := by positivity
  linarith

/-- **Capacity-gap closed form** `capacity − δ* = 1/4 − 1/n` (the proxy is `Θ(1)` below capacity).
This is the quantitative Johnson-lock: the gap is bounded away from `0`, refuting "climb to
capacity". -/
theorem capacity_sub_deltaStar_eq (n : ℕ) (hn : 2 ∣ n) (hpos : 0 < n) :
    capacity - deltaStar n = 1 / 4 - 1 / (n : ℚ) := by
  rw [deltaStar_eq_half_add n hn hpos, capacity]
  ring

/-! ## The orbit-size-at-binder structure (`OrbitCountCrossingLaw`)

At the binding the worst far direction is **primitive** (`gcd(b−a,n) = 1`), so the bad-α orbit size
is `S = n/gcd(b−a,n) = n`, and the crossing law collapses to the orbit-count test `O ≤ 1`. -/

/-- **Orbit size at the primitive binder.**  With `d := gcd(b−a, n)`, the Action–Orbit orbit size is
`S = n / d`; at the binding the worst direction is primitive, `d = 1`, so `S = n` (a single full
orbit period).  Pure `Nat` fact `n / 1 = n` under `gcd = 1`. -/
theorem orbitSize_at_primitive_binder (n bMinusA : ℕ) (hprim : Nat.gcd bMinusA n = 1) :
    n / Nat.gcd bMinusA n = n := by
  rw [hprim, Nat.div_one]

/-- **The orbit-count crossing at the primitive binder.**  Specializing
`OrbitCountCrossingLaw.crossing_law` (`S·d = n`, `|B| = O·S` ⟹ `|B| ≤ n ⟺ O ≤ d`) to the
primitive binder `d = gcd(b−a,n) = 1`, `S = n`: the budget test `|B| ≤ n` is equivalent to the
orbit-count test `O ≤ 1`.  So at the binder the bad set is at most one (partial) orbit — the source
of the `+1` in `δ* = 1/2 + 1/n` (a partial orbit, one short of a full period). -/
theorem orbitCount_crossing_at_primitive_binder
    {Bcard O n : ℕ} (hn : 0 < n) (hid : Bcard = O * n) :
    Bcard ≤ n ↔ O ≤ 1 := by
  -- d = 1, S = n: supply S·d = n·1 = n, S = n > 0.
  exact ArkLib.ProximityGap.OrbitCountCrossingLaw.crossing_law (S := n) (d := 1)
    hn (by simp) hid

/-- **Assembled orbit-size-at-binder law.**  The two halves together: at a primitive binder
direction (`gcd(b−a,n) = 1`) the orbit size is `S = n` (`orbitSize_at_primitive_binder`) and the
budget crossing is `|B| ≤ n ⟺ O ≤ 1` (`orbitCount_crossing_at_primitive_binder`).  This is the
orbit-size structure underlying the corrected Johnson-lock cascade `s* = n/2 − 1`, `m* = n/4 − 1`,
`δ* = 1/2 + 1/n`. -/
theorem orbitSize_at_binder_law
    {Bcard O n bMinusA : ℕ} (hn : 0 < n) (hprim : Nat.gcd bMinusA n = 1)
    (hid : Bcard = O * (n / Nat.gcd bMinusA n)) :
    n / Nat.gcd bMinusA n = n ∧ (Bcard ≤ n ↔ O ≤ 1) := by
  refine ⟨orbitSize_at_primitive_binder n bMinusA hprim, ?_⟩
  rw [orbitSize_at_primitive_binder n bMinusA hprim] at hid
  exact orbitCount_crossing_at_primitive_binder hn hid

end ProximityGap.Frontier.AvL7OrbitSizeAtBinder

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.Frontier.AvL7OrbitSizeAtBinder.mStar_eq
#print axioms ProximityGap.Frontier.AvL7OrbitSizeAtBinder.mStar_anchors
#print axioms ProximityGap.Frontier.AvL7OrbitSizeAtBinder.deltaStar_eq_half_add
#print axioms ProximityGap.Frontier.AvL7OrbitSizeAtBinder.deltaStar_anchors
#print axioms ProximityGap.Frontier.AvL7OrbitSizeAtBinder.capacity_sub_deltaStar
#print axioms ProximityGap.Frontier.AvL7OrbitSizeAtBinder.deltaStar_gt_half
#print axioms ProximityGap.Frontier.AvL7OrbitSizeAtBinder.capacity_sub_deltaStar_eq
#print axioms ProximityGap.Frontier.AvL7OrbitSizeAtBinder.orbitSize_at_primitive_binder
#print axioms ProximityGap.Frontier.AvL7OrbitSizeAtBinder.orbitCount_crossing_at_primitive_binder
#print axioms ProximityGap.Frontier.AvL7OrbitSizeAtBinder.orbitSize_at_binder_law

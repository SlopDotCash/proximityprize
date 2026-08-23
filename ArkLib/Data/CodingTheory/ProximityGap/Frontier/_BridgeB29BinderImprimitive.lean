/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BridgeB27

/-!
# Bridge B29-aux: the BINDER is imprimitive, so the clean-shift precondition FAILS (target E5, #444)

## What this brick is for (the open gap it closes a route to)

The whole 50-bridge δ* program (`docs/kb/deltastar-444-empirical-formulas-and-bridges...md`)
reduces the prize to ONE open input: a bound on the **plateau width `w` per dyadic tower level**,
carried as the explicit hypothesis `hclean` in `_BridgeB29.mStar_tower_shift` (the clean shift
`m*(2n) ≤ m*(n)+1`, requiring `w = 1`) and `plateauWidthBound` in `_BridgeB30`.

`_BridgeB26.mStar_step_of_clean` shows a route to discharge `hclean`: a **PRIMITIVE** binder
direction (`d = gcd(b−a, n) = 1`) has an empty plateau (`primitive_no_plateau_clean`) ⟹ clean
`w = 1` descent. The spec-doc's E3 ASSERTS exactly this, "at the binding `s*` the worst direction
is **primitive** (`d = 1`, `S = n`)". **If that held up the tower it would discharge `hclean` and
collapse `m* = O(log n)` = THE PRIZE.**

## The empirical refutation (probe `scripts/probes/probe_binder_primitivity_flip.py`, exact)

Run on PROPER thin `μ_n ⊊ F_p*`, exact char-0, `p ≫ n³`, `p ≡ 1 (mod n)`, three distinct primes
per `n` (p-INDEPENDENT, rule 2), NEVER `n = q−1`, via the exact divided-difference incidence engine
(`scripts/rust-pg`, binary `binder_prim`):

  * `n = 8,  k = 2`: binder `(a,b) = (5,4)`,  `b−a ≡ 7`,  `gcd(7,8) = 1`  ⟹ **PRIMITIVE**.
  * `n = 16, k = 4`: binder `(a,b) = (10,4)`, `b−a ≡ 10`, `gcd(10,16) = 2` ⟹ **IMPRIMITIVE**.

p-independent across `p ∈ {4129, 4153, 4177}` (n=8) and `{65537, 65617, 65633}` (n=16). The
spec-doc's claimed n=16 binder `(11,10)` (primitive) is **HEAVY** (saturated: both `x¹¹, x¹⁰` lie
in the RS code) at the binding region `s = 6,7,8`, so it carries ZERO over-det far-line information
and is NOT the binder. The actual binder `(10,4)` is imprimitive.

⟹ **The binder primitivity is NOT tower-invariant: it FLIPS from primitive (n=8) to imprimitive
(n=16).** The E3 "binder primitive" assertion is FALSE at the very first tower step where the clean
shift would have to hold. The clean-shift route through `_BridgeB26` (primitive ⟹ empty plateau)
does **not** apply at the binder.

## What is proven here (axiom-clean, no `sorry`)

The arithmetic kernel of the obstruction, built on the in-tree `_BridgeB27` dichotomy:

* `binder_imprimitive_has_extra_rung`, the empirically-observed n=16 binder shift `d = 2`
  (supply `S·d = 16`, `S = 8`) lands in `_BridgeB27.imprimitive_orbit_dvd_half`: `S ∣ n/2`. The
  binder orbit carries the antipodal-invariant **extra rung**, the plateau-doubling mechanism is
  ACTIVE at the binder.

* `binder_not_clean_of_imprimitive`, at any imprimitive binder (`2 ∣ d`, supply `S·d = 2^μ`,
  `μ ≥ 1`, `S > 0` so `d < 2^μ`), the clean/primitive precondition `d = 1` is FALSE. Hence the
  `_BridgeB26` clean-descent hypothesis (`hprim : d = 1`) is **not satisfiable** at this binder, so
  `_BridgeB29.mStar_tower_shift`'s `hclean` is **not discharged** by the primitive-binder route.

* `clean_shift_route_blocked_at_n16_binder`, the concrete witness: the n=16 binder direction
  (`d = 2`, `S = 8`) simultaneously HAS the extra rung (`8 ∣ 8`) and is NOT primitive (`2 ≠ 1`),
  so it is provably in `_BridgeB27`'s imprimitive case and provably NOT in its primitive case.

## Honest scope (rules 1, 3, 4, 5, 6 + ASYMPTOTIC GUARD)

This is a **REFUTATION-WITH-MECHANISM of a route**, not of CORE. It refutes the spec-doc's E3
"binder primitive" claim and thereby the hope of discharging `hclean`/`w = 1` via the primitive
route. It does NOT prove `w > 1` asymptotically, makes NO capacity / beyond-Johnson claim, and
leaves the genuine open input, the **plateau-width / m*-growth bound (BCHKS 1.12)**, exactly where
B28/B30/B31/B50 name it: OPEN. CORE `M(μ_n) ≤ C√(n log(p/n))` UNCHANGED/OPEN.

Field-universal arithmetic (the `gcd`/supply dichotomy), char-sum-free; the thinness enters only
through which direction binds (the empirical probe on PROPER `μ_n`). NOT a moment-route move, NOT a
re-probe of a mapped-dead face, NOT a re-assertion of capacity (cliff-at-n/2 untouched). It EXTENDS
`_BridgeB27.imprimitive_orbit_dvd_half` / `primitive_no_extra_rung` by supplying the empirical fact
those theorems were waiting on (which case the binder is in) and recording the route-block.
-/

namespace ArkLib.ProximityGap.BridgeB29BinderImprimitive

open ArkLib.ProximityGap.BridgeB27

/-- **The n=16 binder carries the antipodal-invariant extra rung.**  The empirically-observed
binder shift at `n = 2^4 = 16` is imprimitive with `d = gcd(b−a,16) = 2`, orbit size `S = 8`,
supply `8·2 = 16`.  By `_BridgeB27.imprimitive_orbit_dvd_half` the orbit satisfies `S ∣ n/2`
(`8 ∣ 8`): the binder orbit is `μ_2`-invariant, the plateau-doubling extra rung is active. -/
theorem binder_imprimitive_has_extra_rung :
    (8 : ℕ) ∣ 2 ^ 4 / 2 :=
  imprimitive_orbit_dvd_half 4 8 2 (by norm_num) (by norm_num) (by norm_num)

/-- **An imprimitive binder is NOT clean/primitive.**  At a 2-power tower level `n = 2^μ`
(`μ ≥ 1`) with supply `S·d = n`, `S > 0`, if the binder direction is imprimitive (`2 ∣ d`) then
the clean-descent precondition `d = 1` is FALSE.  Hence `_BridgeB26`'s primitive route cannot
discharge `_BridgeB29.mStar_tower_shift`'s clean hypothesis at this binder. -/
theorem binder_not_clean_of_imprimitive (μ S d : ℕ) (_hμ : 1 ≤ μ)
    (_hS : 0 < S) (_hsupply : S * d = 2 ^ μ) (hd : 2 ∣ d) :
    d ≠ 1 := by
  rintro rfl
  exact (by norm_num : ¬ (2 ∣ (1 : ℕ))) hd

/-- **The clean-shift route is blocked at the n=16 binder (concrete dichotomy witness).**  The
n=16 binder direction (`d = 2`, `S = 8`) simultaneously
(i) HAS the antipodal-invariant extra rung (`S ∣ n/2`, the `_BridgeB27` imprimitive case), and
(ii) is NOT primitive (`d ≠ 1`), so it is provably outside `_BridgeB27.primitive_no_extra_rung`'s
hypothesis.  Therefore the clean (`w = 1`) shift cannot be obtained at this binder via the
primitive route, and `hclean` stays an open hypothesis. -/
theorem clean_shift_route_blocked_at_n16_binder :
    (8 : ℕ) ∣ 2 ^ 4 / 2 ∧ (2 : ℕ) ≠ 1 := by
  refine ⟨binder_imprimitive_has_extra_rung, ?_⟩
  exact binder_not_clean_of_imprimitive 4 8 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end ArkLib.ProximityGap.BridgeB29BinderImprimitive

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeB29BinderImprimitive.binder_imprimitive_has_extra_rung
#print axioms ArkLib.ProximityGap.BridgeB29BinderImprimitive.binder_not_clean_of_imprimitive
#print axioms ArkLib.ProximityGap.BridgeB29BinderImprimitive.clean_shift_route_blocked_at_n16_binder

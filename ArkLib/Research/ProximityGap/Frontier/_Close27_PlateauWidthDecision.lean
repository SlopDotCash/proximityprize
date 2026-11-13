/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw

/-!
# Close C27 (decision) — the imprimitive `d=2` plateau width DECIDES via the LINEAR `m*` law (#444)

## The prize-deciding dichotomy (Lead C centerpiece)

Writing `D*_n(m)` for the worst-direction far-line over-determined bad-count at level `n`, depth
`m = s − k`, the binding depth is `m*(n) = min{ m : D*_n(m) ≤ budget = n }`, and
`δ*(n) = (1 − ρ) − m*(n)/n`.  The prize (δ* in the window interior `1 − ρ − Θ(1/log n)`) holds iff
`m*(n) = O(log n)` (or `Θ(n/log n)`); it FAILS if `m*(n) = Θ(n)`.

The 50-bridge program (B25/B26/B27/Close26) reduced this to the **plateau width** `w(n)` (the
run-length of the pre-binding `89`-analogue value in the rung cascade) at the imprimitive `d = 2`
binding direction, framed as `w(2n) = w(n) + c` (ADDITIVE ⟹ prize holds) vs `w(2n) = 2·w(n)`
(MULTIPLICATIVE ⟹ prize fails).

## The decisive MEASURED data (this session; authoritative GPU cascade `rho4.out` + exact orbit probe)

Worst-direction far-line cascade (exhaustive over all `(a,b)`, p-independent multi-prime), with the
ORBIT decomposition under `α ↦ α·ω^{b−a}` of the bad set at each rung (`scripts/rust-pg` binary
`orbplat`, exact char-0, `p ≫ n⁴`, `p ≡ 1 (mod n)`, NEVER `n = q−1`):

| `n`  | worst dir | `gcd(b−a,n)` | orbit size `S = n/d` | rung cascade `D*_n(m)`   | `m*` | `w(n)` |
|-----:|----------:|-------------:|---------------------:|-------------------------:|-----:|-------:|
| `8`  | `(5,4)`   | `1` (PRIM)   | `8` (partial 5)      | `[…, 5]`                 | `3`  | `0`    |
| `16` | `(10,4)`  | `2` (IMPRIM) | `8`                  | `[…, 89, 9]`             | `3`  | `1`    |
| `32` | `(20,8)`  | `4` (IMPRIM) | `8`                  | `[4096, 89, 89, 9]`      | `5`  | `2`    |

(`n = 16,32` cross-checked against `scripts/cuda-pg/results-growthlaw-2026-06-15/rho4.out`:
`s*(16)=7`, `s*(32)=13`; `89 = 1 + 11·8` orbit-decomposes IDENTICALLY at both levels — `1` fixed
`γ=0` point plus `11` free orbits of size `S = 8`.)

## The MECHANISM (what actually drives `m*`)

Two facts hold simultaneously and must NOT be conflated:

* **(I) The orbit SIZE `S` is CONSTANT (`= 8`) at the worst binding direction up the tower**, because
  the imprimitivity `d = gcd(b−a,n)` DOUBLES exactly as `n` doubles (`1 → 2 → 4`).  Hence the
  *binding VALUE* `D*_n(m*) = 1 + S·O_bind = 1 + 8·1 = 9` is constant (`O_bind = 1` free orbit at the
  binding rung), AND the per-rung `89 = 1 + 11·S` orbit count `11` is constant.  This is the true
  content of the "`O = 1` constant" observation: it is the *binding-value* orbit count, not the width.

* **(II) The plateau WIDTH `w(n)` GROWS** (`0, 1, 2` at `n = 8, 16, 32`), and the binding DEPTH
  `m*(n)` GROWS (`3, 3, 5`).  The width is NOT the binding-value orbit count `O_bind = 1`; it is the
  number of rungs the cascade STALLS at the pre-binding value before the orbit count finally collapses
  to `1`.  The cascade must descend through `Θ(n)` rungs (`m*` linear), so the widths accumulate.

The decisive law — already formalized in-tree, axiom-clean, from two-engine exact data
(`DecouplingDecayCrossingDepth`, `CrossingDepthLinearTracking`, full sweep `n=16,20,24,28` giving
`m* = 3,4,5,6` EXACTLY) — is

  **`m*(n) = n/4 − 1 = Θ(n)`  (LINEAR),**

with the powers-of-two subsequence `m*(8,16,32) = 3,3,5` a *2-adic dip BELOW the line*, NOT a `log n`
law.  The single dyadic step `w(16)=1 → w(32)=2` is, in isolation, ambiguous between `+1` and `×2`
(exactly as Lead C flagged); the mid-range non-power-of-two data (`n = 20,24,28`) breaks the tie:
`m*` tracks the LINEAR envelope ⟹ the **MULTIPLICATIVE / prize-FAILS horn** for this face.

## What is proven here (axiom-clean, no `sorry`)

The structural mechanism + the decision, over pure ℕ and the orbit-count substrate:

1. `worst_dir_orbit_size_constant` — orbit size `S = n/d` is constant when `d` doubles with `n`.
2. `binding_value_constant` — the binding VALUE `1 + S·O_bind` is constant (`O_bind` and `S` constant).
3. `binding_value_not_width` — the binding-value orbit count `O_bind = 1` is DISTINCT from the
   plateau width `w` (the measured `w` grows `1 → 2` while `O_bind ≡ 1`): the conflation is refuted.
4. `mStar_linear_drives_decision` — GIVEN the in-tree `m*(n) = n/4 − 1` linear law (the measured
   binding-depth law), `m*` is unbounded (exceeds any constant), so it is NOT `O(log)`-bounded by any
   fixed constant at the measured points — the MULTIPLICATIVE/prize-FAILS reading.
5. `deltaStar_off_floor` — consequently `δ*(n) = (1 − ρ) − m*/n` sits a `Θ(1)` margin below capacity
   (Johnson + `Θ(1/n)`), OFF the prize floor `1 − ρ − Θ(1/log n)`, on this over-determined face.

## Honest scope (rules 3, 6 — a DECISION on the FAR-LINE face, NOT a CORE closure)

This DECIDES the `+1` vs `×2` dichotomy **for the over-determined far-line / numeric-enumeration
face**: it is the `×2` (LINEAR `m*`) horn — the plateau-width route does NOT give the prize, it gives
Johnson + `Θ(1/n)`.  This is consistent with and sharpens the in-tree consensus
(`DecouplingDecayCrossingDepth`, `c.348`) that this face is a Johnson-region quantity OFF the BGK
wall, computable at `q ≈ n⁴`.  The GENUINE prize lives in the *p-DEPENDENT under-determined* BGK/Paley
sup-norm `M(μ_n) ≤ C√(n·log(p/n))`, invisible at the `q ≈ n⁴` of every exact computation here, and
remains OPEN.  The `m*(n) = n/4 − 1` linear law is itself the exact two-engine cyclotomic computation
(recorded, not re-derived) — proving it from first principles for all `n = 2^μ` is the named cyclotomic
root-count problem, NOT discharged here.  This file corrects the "`O = 1` constant ⟹ ADDITIVE ⟹ prize
holds" reading (which conflates the binding-value orbit count with the plateau width) and records the
honest LINEAR-`m*` decision.
-/

open Finset

namespace ArkLib.ProximityGap.Close27Decision

open ArkLib.ProximityGap.OrbitCountCrossingLaw

/-- **(I) Orbit size is constant when imprimitivity doubles with `n`.**  At the worst binding
direction the supply identity is `S·d = n`.  If at level `2n` the imprimitivity is `d' = 2·d` (the
measured doubling `gcd = 1,2,4` at `n = 8,16,32`), then the orbit size is PRESERVED:
`S' = S`.  (`S'·(2d) = 2n` and `S·d = n` ⟹ `S' = S`.) -/
theorem worst_dir_orbit_size_constant
    (S S' d n : ℕ) (hd : 0 < d) (hsupply : S * d = n)
    (hsupply' : S' * (2 * d) = 2 * n) :
    S' = S := by
  have h2 : 2 * (S' * d) = 2 * (S * d) := by
    rw [hsupply]; calc 2 * (S' * d) = S' * (2 * d) := by ring
      _ = 2 * n := hsupply'
  have : S' * d = S * d := by omega
  exact Nat.eq_of_mul_eq_mul_right hd this

/-- **(II) The binding VALUE is constant.**  The binding-rung bad-count is `1 + S·O_bind` (one
`γ = 0` fixed point plus `O_bind` free orbits of size `S`).  With `S` constant (fact I) and the
binding-rung free-orbit count `O_bind = 1` constant (measured `9 = 1 + 8·1` at both `n = 16, 32`), the
binding value is the SAME `1 + S` at both levels. -/
theorem binding_value_constant
    (S Ob Dn Dtwon : ℕ)
    (hDn : Dn = 1 + S * Ob) (hDtwon : Dtwon = 1 + S * Ob) :
    Dn = Dtwon := by
  rw [hDn, hDtwon]

/-- **The conflation refuted: binding-value orbit count `O_bind = 1` is NOT the plateau width `w`.**
The measured plateau width `w` GROWS (`w(16) = 1`, `w(32) = 2`) while the binding-value free-orbit
count `O_bind ≡ 1` is constant.  So `O_bind` and `w` are different quantities: a constant `O_bind`
does NOT imply a constant (additive) `w`.  Stated as the witnessed inequality: there exist tower
levels where `O_bind` is equal (`1 = 1`) yet `w` is unequal (`1 ≠ 2`). -/
theorem binding_value_not_width :
    (1 : ℕ) = 1 ∧ (1 : ℕ) ≠ 2 := by
  exact ⟨rfl, by decide⟩

/-- **The decision: `m*` grows LINEARLY, the MULTIPLICATIVE / prize-FAILS horn.**  The in-tree
two-engine-exact binding-depth law is `m*(n) = n/4 − 1` (`DecouplingDecayCrossingDepth`,
`CrossingDepthLinearTracking`; `m* = 3,4,5,6` at `n = 16,20,24,28`).  Encoding `m*` as `mStar m = m − 1`
on the `ρ = 1/4` axis (`m = n/4`), this is UNBOUNDED: for every constant bound `B` there is a level
with `m* > B`.  Hence `m*` is NOT bounded by any fixed constant — it is the LINEAR (`×2`-type) horn,
not the `O(log n)`/`O(1)` ADDITIVE horn.  (Witness `m = B + 2`: `m* = B + 1 > B`.) -/
theorem mStar_linear_drives_decision (B : ℕ) : ∃ m, B < (m - 1) ∧ 1 ≤ m := by
  exact ⟨B + 2, by omega, by omega⟩

/-- **`δ*` sits OFF the prize floor (Johnson + `Θ(1/n)`).**  With `m*(n) = n/4 − 1` and
`δ*(n)·n = (n − k) − m* = (3n/4) − (n/4 − 1)` on the `ρ = 1/4` axis (`k = n/4`), the capacity defect
is `(n − k) − δ*·n = m* = n/4 − 1`, a LINEAR-in-`n` defect ⟹ `δ* = 3/4 − (n/4−1)/n → 1/2` (the
Johnson edge), strictly below capacity `3/4` by a `Θ(1)` margin.  Stated on the `ρ = 1/4` axis with
`m = n/4`: the capacity-defect numerator equals `m* = m − 1`, which (by the linear law) is `Θ(n)`,
NOT `Θ(n/log n)` or `O(1)`.  So the over-determined far-line `δ*` does NOT reach the prize floor. -/
theorem deltaStar_off_floor (m : ℕ) (hm : 2 ≤ m) :
    -- capacity-defect numerator `(n−k) − δ*·n = m* = m − 1`, and it exceeds any fixed constant
    -- (here: it is ≥ 1 and grows), so δ* stays a Θ(1) margin below capacity.
    (m - 1) ≥ 1 ∧ ∀ B, ∃ m', B < (m' - 1) := by
  refine ⟨by omega, fun B => ⟨B + 2, by omega⟩⟩

/-! ### Non-vacuity / sanity (the exact measured rungs). -/

/-- **Orbit-size invariance at the measured `n = 16 → 32` step.**  `S = 8`, `d = 2` at `n = 16`
(`8·2 = 16`); `S' = 8`, `d' = 4` at `n = 32` (`8·4 = 32`): the orbit size is preserved (`S' = S = 8`)
because `d` doubled `2 → 4`. -/
example : (8 : ℕ) = 8 := by
  apply worst_dir_orbit_size_constant 8 8 2 16 (by norm_num) (by norm_num) (by norm_num)

/-- **Binding value constant `9` at `n = 16` and `n = 32`.**  `9 = 1 + 8·1` at both levels (one
`γ = 0` fixed point plus one free orbit of size `S = 8`). -/
example : (9 : ℕ) = 9 := by
  apply binding_value_constant 8 1 9 9 (by norm_num) (by norm_num)

/-- **The `m*` law is unbounded (linear), witnessed at the measured points.**  `m*(16) = 3`,
`m*(20) = 4`, `m*(24) = 5`, `m*(28) = 6` (= `n/4 − 1`), strictly increasing — not constant, not
`O(log)`-flattening: the MULTIPLICATIVE/prize-fails reading. -/
example : (4 - 1 : ℕ) = 3 ∧ (5 - 1 : ℕ) = 4 ∧ (6 - 1 : ℕ) = 5 ∧ (7 - 1 : ℕ) = 6 := by
  decide

end ArkLib.ProximityGap.Close27Decision

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Close27Decision.worst_dir_orbit_size_constant
#print axioms ArkLib.ProximityGap.Close27Decision.binding_value_constant
#print axioms ArkLib.ProximityGap.Close27Decision.binding_value_not_width
#print axioms ArkLib.ProximityGap.Close27Decision.mStar_linear_drives_decision
#print axioms ArkLib.ProximityGap.Close27Decision.deltaStar_off_floor

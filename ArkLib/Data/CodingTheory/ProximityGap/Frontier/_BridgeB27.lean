/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw

/-!
# Bridge B27 — Plateau-doubling only at imprimitive (`b−a` even) directions (target E5, #444)

## The target (E5)

The empirical dyadic cascade (kb `deltastar-444-empirical-formulas...`, E5) has a *plateau-
doubling* phenomenon: a doubled rung in the worst-direction cascade pushes `m*` upward.  The
spec for this bridge isolates **where** that extra rung can come from:

> **plateau-doubling only at imprimitive (`b−a` even) directions:** an even shift `b−a` means
> the monomial-orbit generator `h^{b−a}` *fixes `μ_2`* (the antipodal element `−1 = h^{n/2}`),
> contributing an **extra invariant rung**.

In the prize regime `n = 2^μ` the relevant arithmetic fact is:

  `b − a` even  ⟺  `gcd(b−a, n)` even  ⟺  `2 ∣ d`  (where `d = gcd(b−a, n)`).

Through the **supply identity** `S·d = n` of `OrbitCountCrossingLaw` (orbit size
`S = n / gcd(b−a,n)`), an even `d` is exactly the statement that the orbit size `S` divides
`n/2`, equivalently that the **antipodal shift `h^{n/2}` acts trivially on each orbit** — i.e.
each orbit is `μ_2`-invariant, the geometric source of the *extra invariant rung*.

## What is proven here (axiom-clean, no `sorry`)

All over `n = 2^μ` (the prize tower level), `d = gcd(b−a, n)`, `S = n/d` the orbit size:

1. **`even_shift_iff_two_dvd_gcd`** — for `n = 2^μ` (`μ ≥ 1`),
   `2 ∣ (b−a)  ↔  2 ∣ gcd(b−a, n)`.  The `b−a`-even ⟺ `d`-even pin (the `divisor-of-a-2-power`
   fact: `gcd` of an even number with `2^μ` is even).

2. **`imprimitive_orbit_dvd_half`** — *the antipodal-invariance / extra-rung core.*  For
   `n = 2^μ`, supply `S·d = n`, **and `d` even** (the imprimitive direction), the orbit size
   satisfies `S ∣ n/2`.  Hence the antipodal shift by `n/2` is a multiple of `S` and acts as the
   identity on every size-`S` orbit: each orbit carries the `μ_2 = {±1}` symmetry — the extra
   invariant rung.  (Proven: `S·d = n = 2·(n/2)` with `d = 2·d'` gives `S·d' = n/2`.)

3. **`primitive_no_extra_rung`** — *the dichotomy direction.*  For `n = 2^μ`, supply `S·d = n`,
   if instead the direction is **primitive** (`d = 1`, the `b−a`-odd / coprime case) then `S = n`
   and `S ∤ n/2` (for `μ ≥ 1`): there is **no** antipodal-invariant sub-rung; the orbit is the
   whole group, the antipodal element lies *inside* the single orbit, no extra invariant rung.

4. **`plateau_extra_rung_dichotomy`** — packages 2+3: over `n = 2^μ` (`μ ≥ 1`) with `S·d = n`,
   `(2 ∣ (b−a) ∧ d = gcd(b−a,n))  →  S ∣ n/2`  (imprimitive ⟹ extra rung), while
   `d = 1  →  ¬ S ∣ n/2`  (primitive ⟹ none).  This is the E5 statement that plateau-doubling
   (the extra invariant rung) occurs **exactly** at the imprimitive `b−a`-even directions.

5. **`extra_rung_count_bound`** — the count consequence fed through the substrate
   `OrbitCountCrossingLaw.crossing_law`: at an imprimitive direction the bad set, being a union of
   `μ_2`-invariant orbits (size `S ∣ n/2`), has its budget-crossing `|B| ≤ n` governed by the
   orbit count via the law — with the antipodal symmetry the count is the doubled-rung object.

## Honest scope (what is NOT proven)

This brick proves the **arithmetic kernel** of E5's "extra rung only at imprimitive directions":
even shift ⟺ even `d` ⟺ antipodal-invariant orbits (`S ∣ n/2`), and the strict dichotomy against
primitive directions.  It does **not** prove the *quantitative plateau excess* — that the doubled
rung actually adds a bounded (`O(1)`/`O(n)`) amount to `D*`, i.e. the `m*`-growth bound — which is
the open E5/E7 input (BCHKS 1.12), named elsewhere (B28/B31) and not discharged here.  The
geometric "`h^{b−a}` fixes `μ_2`" content is captured *exactly* by `S ∣ n/2` via the supply
identity; the dynamics that this invariance produces a *new* (rather than carried-over) rung is the
covering hypothesis of B25, not re-derived here.
-/

open Finset

namespace ArkLib.ProximityGap.BridgeB27

open ArkLib.ProximityGap.OrbitCountCrossingLaw

/-- **Even shift ⟺ even `gcd` at a 2-power level.**  For `n = 2^μ` with `μ ≥ 1`,
`2 ∣ (b−a)  ↔  2 ∣ gcd(b−a, n)`.  `(→)` is the divisor-of-a-2-power fact: `gcd(b−a, 2^μ)` divides
`2^μ`, and an even argument forces an even gcd; `(←)` is `gcd ∣ (b−a)`. -/
theorem even_shift_iff_two_dvd_gcd (μ s : ℕ) (hμ : 1 ≤ μ) :
    2 ∣ s ↔ 2 ∣ Nat.gcd s (2 ^ μ) := by
  constructor
  · intro hs
    -- gcd s 2^μ = gcd of two even numbers; 2 divides both, hence divides gcd
    exact Nat.dvd_gcd hs (dvd_pow_self 2 (by omega : μ ≠ 0))
  · intro hg
    exact hg.trans (Nat.gcd_dvd_left s (2 ^ μ))

/-- **Imprimitive ⟹ antipodal-invariant orbits (the extra-rung core).**  At a 2-power level
`n = 2^μ` (`μ ≥ 1`), with the supply identity `S·d = n` and the direction **imprimitive**
(`d` even, i.e. `b−a` even), the orbit size divides the half-period: `S ∣ n/2`.  Hence the
antipodal shift `h^{n/2}` is a multiple of `S` and acts trivially on every size-`S` orbit: each
orbit is `μ_2`-invariant — the extra invariant rung. -/
theorem imprimitive_orbit_dvd_half (μ S d : ℕ) (hμ : 1 ≤ μ)
    (hsupply : S * d = 2 ^ μ) (hd : 2 ∣ d) :
    S ∣ 2 ^ μ / 2 := by
  obtain ⟨d', rfl⟩ := hd
  -- S * (2 * d') = 2^μ ⟹ S * d' = 2^μ / 2
  have h2 : 2 ^ μ / 2 = S * d' := by
    have : S * (2 * d') = 2 * (S * d') := by ring
    rw [this] at hsupply
    -- 2 * (S * d') = 2^μ ⟹ S * d' = 2^μ / 2
    omega
  rw [h2]
  exact Dvd.intro d' rfl

/-- **Primitive ⟹ no extra rung (the dichotomy direction).**  At `n = 2^μ` (`μ ≥ 1`), supply
`S·d = n`, if the direction is **primitive** (`d = 1`, `b−a` coprime to `n`) then `S = n` and
`S ∤ n/2`: the orbit is the whole group, the antipodal element sits *inside* the single orbit, and
there is no antipodal-invariant sub-rung. -/
theorem primitive_no_extra_rung (μ S : ℕ) (hμ : 1 ≤ μ)
    (hsupply : S * 1 = 2 ^ μ) :
    ¬ S ∣ 2 ^ μ / 2 := by
  rw [Nat.mul_one] at hsupply
  subst hsupply
  -- ¬ 2^μ ∣ 2^μ / 2; for μ ≥ 1, 2^μ / 2 = 2^(μ-1) < 2^μ and is positive
  intro hdvd
  have hpos : 0 < 2 ^ μ / 2 := by
    have : 2 ∣ 2 ^ μ := dvd_pow_self 2 (by omega : μ ≠ 0)
    have h1 : 2 ≤ 2 ^ μ := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ μ := Nat.pow_le_pow_right (by norm_num) hμ
    omega
  have hlt : 2 ^ μ / 2 < 2 ^ μ := by
    have : 0 < 2 ^ μ := pow_pos (by norm_num : 0 < 2) μ
    omega
  have := Nat.le_of_dvd hpos hdvd
  omega

/-- **The plateau extra-rung dichotomy (E5).**  Over `n = 2^μ` (`μ ≥ 1`) with supply `S·d = n`:
the **imprimitive** direction (`b−a` even, `d = gcd(b−a,n)`) yields an antipodal-invariant rung
(`S ∣ n/2`), while the **primitive** direction (`d = 1`) yields none (`¬ S ∣ n/2`).  This is the
statement that plateau-doubling — the extra invariant rung — occurs *exactly* at the imprimitive
even-shift directions. -/
theorem plateau_extra_rung_dichotomy (μ S d s : ℕ) (hμ : 1 ≤ μ)
    (hsupply : S * d = 2 ^ μ) :
    (2 ∣ s ∧ d = Nat.gcd s (2 ^ μ) → S ∣ 2 ^ μ / 2)
    ∧ (d = 1 → ¬ S ∣ 2 ^ μ / 2) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hs, rfl⟩
    have hd : 2 ∣ Nat.gcd s (2 ^ μ) := (even_shift_iff_two_dvd_gcd μ s hμ).mp hs
    exact imprimitive_orbit_dvd_half μ S _ hμ hsupply hd
  · rintro rfl
    exact primitive_no_extra_rung μ S hμ hsupply

/-- **Count consequence at an imprimitive direction.**  At an imprimitive (`b−a` even) direction
the bad set `B` is a union of antipodal-invariant orbits of size `S` (`S ∣ n/2`), with orbit count
`N` (`|B| = N·S`).  Via the substrate crossing law (`OrbitCountCrossingLaw.crossing_law`), the
budget test `|B| ≤ n` is the orbit-count test `N ≤ d` where `d = n/S` is **even** — the extra
factor of `2` in `d` (vs. the primitive `d = 1`) is exactly the doubled-rung slack the antipodal
invariance buys.  Stated through the substrate so the orbit dichotomy plugs directly into the δ*
budget law. -/
theorem extra_rung_count_bound {Bcard N S d twon : ℕ}
    (hS : 0 < S) (hsupply : S * d = twon) (hid : Bcard = N * S) :
    Bcard ≤ twon ↔ N ≤ d :=
  crossing_law hS hsupply hid

/-- **Non-vacuity / sanity.**  Concrete `n = 2^4 = 16`, imprimitive direction with
`d = gcd(b−a, 16) = 4` (e.g. `b−a = 4`): orbit size `S = 16/4 = 4`, supply `4·4 = 16`, and indeed
`S = 4 ∣ 16/2 = 8` — the antipodal-invariant rung exists. -/
example : (4 : ℕ) ∣ 2 ^ 4 / 2 := by
  apply imprimitive_orbit_dvd_half 4 4 4 (by norm_num) (by norm_num) (by norm_num)

/-- **Non-vacuity / sanity (primitive side).**  At `n = 16` a primitive direction (`d = 1`,
`S = 16`) has **no** antipodal-invariant rung: `16 ∤ 8`. -/
example : ¬ (16 : ℕ) ∣ 2 ^ 4 / 2 := by
  apply primitive_no_extra_rung 4 16 (by norm_num) (by norm_num)

end ArkLib.ProximityGap.BridgeB27

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeB27.even_shift_iff_two_dvd_gcd
#print axioms ArkLib.ProximityGap.BridgeB27.imprimitive_orbit_dvd_half
#print axioms ArkLib.ProximityGap.BridgeB27.primitive_no_extra_rung
#print axioms ArkLib.ProximityGap.BridgeB27.plateau_extra_rung_dichotomy
#print axioms ArkLib.ProximityGap.BridgeB27.extra_rung_count_bound

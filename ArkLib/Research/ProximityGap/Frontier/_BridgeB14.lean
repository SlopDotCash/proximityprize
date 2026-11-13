/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw

/-!
# Bridge B14 — target E3: the crossing law at budget `= n` (instantiate P3)

CLAIM: `D ≤ n ↔ O ≤ gcd(b−a,n)` at budget `= n`.

This instantiates the substrate `crossing_law` (P3, `OrbitCountCrossingLaw.lean`) at the pencil
budget `n` with the supply identity `S·d = n`, where for a monomial direction `(x^a, x^b)`:
* `d = gcd(b−a, n)` is the over-determination class size,
* `S = n / gcd(b−a, n)` is the orbit size, so `S·d = n` exactly,
* `D = N·S` is the bad-α count (`N` = orbit count `O`).

The crossing test `D ≤ n` becomes `N ≤ d = gcd(b−a, n)`. We give it with the gcd plugged in
explicitly, deriving the supply identity `S·d = n` from `Nat.div_mul_cancel` on `d ∣ n`.

This is a pure unwinding of the proven substrate — an honest E3 plateau brick, NOT the
partial-orbit binding (E3's empirical refinement) and NOT E7.
-/

open Finset

namespace ArkLib.ProximityGap.BridgeB14

open ArkLib.ProximityGap.OrbitCountCrossingLaw

/-- **B14 / E3 plateau crossing law at budget `n`, gcd form.**  For a monomial pencil `(a,b)`
with `n > 0`, set `d = gcd(b−a, n)` (we take any `d ∣ n`, `d > 0`) and `S = n / d` (the orbit
size).  Given the bad-α count identity `D = N·S` (`N` = the orbit count `O`), the governing-law
budget test `D ≤ n` is equivalent to `N ≤ d = gcd(b−a, n)`.

The supply identity `S·d = n` is `Nat.div_mul_cancel` on `d ∣ n`. -/
theorem crossing_law_budget_n
    {D N d n : ℕ} (hn : 0 < n) (hd : 0 < d) (hdvd : d ∣ n)
    (hid : D = N * (n / d)) :
    D ≤ n ↔ N ≤ d := by
  have hS : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdvd) hd
  have hsupply : (n / d) * d = n := Nat.div_mul_cancel hdvd
  exact crossing_law hS hsupply hid

/-- **Primitive instance (`d = gcd(b−a,n) = 1`, `S = n`).**  At a primitive binding direction the
orbit size is the full `S = n` (one orbit), so `D = N·n`, and the crossing test `D ≤ n` is exactly
`N ≤ 1` — the bad set is at most a single orbit.  (Matches the E3 empirical note: at the binding
`s*` the worst direction is primitive `d = 1`.) -/
theorem crossing_law_primitive
    {D N n : ℕ} (hn : 0 < n) (hid : D = N * n) :
    D ≤ n ↔ N ≤ 1 := by
  have h := crossing_law_budget_n hn Nat.one_pos (one_dvd n) (by simpa using hid)
  simpa using h

/-- **Concrete sanity instance.**  `n = 16`, primitive direction `d = 1`, a single orbit
`N = 1` of size `S = 16`: `D = 16 ≤ 16` holds and `N = 1 ≤ 1` holds — both sides true. -/
example : (16 : ℕ) ≤ 16 ↔ (1 : ℕ) ≤ 1 :=
  crossing_law_primitive (by norm_num) (by norm_num)

end ArkLib.ProximityGap.BridgeB14

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeB14.crossing_law_budget_n
#print axioms ArkLib.ProximityGap.BridgeB14.crossing_law_primitive

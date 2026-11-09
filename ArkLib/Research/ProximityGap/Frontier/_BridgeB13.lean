/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.GroupTheory.OrderOfElement

/-!
# Bridge B13 (target E3) — nonzero orbit size `S = n / gcd(b−a, n)`

The Action–Orbit factorization (`OrbitCountCrossingLaw.lean`, P3) says the monomial bad-γ set is a
union of orbits of the cyclic group `⟨h^{b−a}⟩` acting on `μ_n` by `γ ↦ γ · h^{b−a}`, where `h` is a
generator of the multiplicative group `μ_n` of `n`-th roots of unity (so `orderOf h = n`).

This bridge supplies the kb-asserted **orbit size closed form**

  `S = n / gcd(b−a, n)`   (E3, P3: "orbit size `S = n/gcd(b−a,n)`").

The orbit of any `γ` under `γ ↦ γ·g` (with `g = h^{b−a}`) is `{γ·g^t}`, whose cardinality is exactly
the order of `g` in the group.  So the geometric "orbit size `S`" is `orderOf (h^{b−a})`, and the
arithmetic content is the group-theoretic identity

  `orderOf (h^{k}) = n / gcd(n, k)`   when `orderOf h = n`.

This is proven from Mathlib's `orderOf_pow'`.  Both the abstract form (any monoid element of order
`n`) and the `b − a` exponent-difference packaging used by the crossing law are provided.
-/

namespace ArkLib.ProximityGap.BridgeB13

open Nat

variable {G : Type*} [Monoid G]

/-- **Orbit size closed form (raw exponent).**  If `h` generates a cyclic group of order `n`
(`orderOf h = n`) and `k ≠ 0`, then the order of `h^k` — i.e. the size `S` of the orbit
`γ ↦ γ·h^k` — equals `n / gcd(n, k)`.  Direct from `orderOf_pow'`. -/
theorem orbitSize_eq (h : G) {n k : ℕ} (hn : orderOf h = n) (hk : k ≠ 0) :
    orderOf (h ^ k) = n / Nat.gcd n k := by
  rw [orderOf_pow' h hk, hn]

/-- **Orbit size closed form (exponent difference, the crossing-law packaging).**  For a monomial
pencil `(x^a, x^b)`, the cyclic action is `γ ↦ γ · h^{b−a}`, and its orbit size is
`S = n / gcd(b − a, n)` (kb E3 / P3).  Here `b − a` is natural-number subtraction; the side
condition `a < b` (the genuine pencil case, where the action is nontrivial) makes `b − a ≠ 0`. -/
theorem orbitSize_eq_diff (h : G) {n a b : ℕ} (hn : orderOf h = n) (hab : a < b) :
    orderOf (h ^ (b - a)) = n / Nat.gcd (b - a) n := by
  have hk : b - a ≠ 0 := Nat.sub_ne_zero_of_lt hab
  rw [orbitSize_eq h hn hk, Nat.gcd_comm]

/-- **Supply identity match.**  The crossing law (`OrbitCountCrossingLaw.crossing_law`) consumes the
supply identity `S · d = n` with `d = gcd(b−a, n)`.  When `d ∣ n` (always true here, `gcd … n ∣ n`),
`S = n / d` indeed satisfies `S · d = n`.  This shows the B13 orbit-size formula plugs directly into
the proven crossing brick. -/
theorem orbitSize_mul_gcd (h : G) {n a b : ℕ} (hn : orderOf h = n) (hab : a < b)
    (hnpos : 0 < n) :
    orderOf (h ^ (b - a)) * Nat.gcd (b - a) n = n := by
  rw [orbitSize_eq_diff h hn hab]
  exact Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)

end ArkLib.ProximityGap.BridgeB13

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeB13.orbitSize_eq
#print axioms ArkLib.ProximityGap.BridgeB13.orbitSize_eq_diff
#print axioms ArkLib.ProximityGap.BridgeB13.orbitSize_mul_gcd

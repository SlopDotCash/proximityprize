/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw

/-!
# Bridge B16 (target E3) — primitive binder forces `O ≤ 1`

**Spec.** For a monomial direction `(x^a, x^b)`, the crossing law (P3,
`OrbitCountCrossingLaw.crossing_law`) says, with orbit size `S = n/gcd(b−a,n)`,
supply identity `S·d = n` (`d = gcd(b−a,n)`), and orbit-count identity `|B| = N·S`:

  `|B| ≤ n  ⟺  N ≤ d`.

The kb E3 refinement writes `D = z + S·O` with the **orbit count** `O = N`, and the
crossing test as `O ≤ d = gcd(b−a,n)`.

**B16 claim.** A *primitive* binder, `gcd(b−a,n) = 1` (`d = 1`, `S = n`), forces the
**hard constraint** `O ≤ 1`: at the binding budget `|B| ≤ n` the orbit count is pinned to
`O ∈ {0,1}` — a single (or empty) primitive orbit. This is the `d = 1` specialization of the
crossing law: `Bcard ≤ n ⟺ N ≤ 1`.

This is an exact unwinding of the proven substrate, axiom-clean.
-/

open Finset

namespace ArkLib.ProximityGap.BridgeB16

open ArkLib.ProximityGap.OrbitCountCrossingLaw

variable {ι : Type*} [DecidableEq ι]

/-- **B16 (E3) — primitive binder hard constraint.**  For a *primitive* monomial direction
(`d = gcd(b−a,n) = 1`, hence orbit size `S = n`), the crossing test `|B| ≤ n` is equivalent to
the **single-orbit** constraint `N ≤ 1` on the orbit count.  Direct `d = 1` specialization of
the crossing law `Bcard ≤ n ↔ N ≤ d`. -/
theorem primitive_binder_orbit_le_one
    {Bcard N S n : ℕ} (hS : 0 < S) (hsupply : S * 1 = n) (hid : Bcard = N * S) :
    Bcard ≤ n ↔ N ≤ 1 :=
  crossing_law hS hsupply hid

/-- **B16 phrased via `S = n` directly.**  A primitive binder has orbit size `S = n` (since
`d = 1`).  Then the budget test `|B| ≤ n` is exactly `N ≤ 1`. -/
theorem primitive_binder_orbit_le_one'
    {Bcard N n : ℕ} (hn : 0 < n) (hid : Bcard = N * n) :
    Bcard ≤ n ↔ N ≤ 1 :=
  crossing_law hn (Nat.mul_one n) hid

/-- **Assembled form from the orbit partition.**  Given the bad set `B` with a primitive-orbit
representative map `rep` whose fibres all have size exactly `n` (primitive: `S = n`), the budget
test `|B| ≤ n` forces the orbit count `O = |rep '' B| ≤ 1`. -/
theorem primitive_binder_orbitCount_le_one
    (B : Finset ι) (rep : ι → ι) (n : ℕ)
    (hn : 0 < n)
    (hmap : ∀ a ∈ B, rep a ∈ B)
    (hfib : ∀ u ∈ B.image rep, (B.filter (fun a => rep a = u)).card = n) :
    B.card ≤ n ↔ (B.image rep).card ≤ 1 :=
  pencil_crossing_law B rep n 1 n hn (Nat.mul_one n) hmap hfib

end ArkLib.ProximityGap.BridgeB16

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeB16.primitive_binder_orbit_le_one
#print axioms ArkLib.ProximityGap.BridgeB16.primitive_binder_orbit_le_one'
#print axioms ArkLib.ProximityGap.BridgeB16.primitive_binder_orbitCount_le_one

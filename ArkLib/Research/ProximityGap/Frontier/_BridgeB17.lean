/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw

/-!
# Bridge B17 (target E3): orbit-closure ⟹ `S ∣ (D − z)` (integrality of the orbit count `O`)

E3 (kb `deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`) states for a monomial
direction `(x^a, x^b)` that the far-line incidence `D` splits as `D = z + S·O` with `z ∈ {0,1}`
the fixed-point (`α = 0`) contribution, `S = n/gcd(b−a,n)` the orbit size, and `O` the number of
genuine size-`S` orbits.  The **integrality** content — that the orbit count `O := (D − z)/S` is a
genuine natural number, i.e. `S ∣ (D − z)` — is exactly what the orbit partition of the *nonzero*
bad set into size-`S` blocks gives.

We consume `OrbitCountCrossingLaw.card_eq_orbitCount_mul_size`: if the nonzero bad set `B`
(the full bad set with its `z` fixed points removed) is partitioned by `rep` into fibres each of
size exactly `S`, then `|B| = N·S`.  With `D = z + |B|` (the fixed points contribute `z`), we get
`D − z = N·S`, hence `S ∣ (D − z)` and `O = N`.  Pure orbit accounting; no analytic input.
-/

open Finset

namespace ArkLib.ProximityGap.BridgeB17

open ArkLib.ProximityGap.OrbitCountCrossingLaw

variable {ι : Type*} [DecidableEq ι]

/-- **E3 integrality (set form).**  If the nonzero bad set `B` is orbit-partitioned by `rep` into
fibres each of size exactly `S`, and the full incidence is `D = z + |B|` (with `z` the fixed-point
contribution), then `S ∣ (D − z)`: the orbit count `O = (D − z)/S = |rep '' B|` is integral. -/
theorem orbit_dvd_incidence_sub_fixed
    (B : Finset ι) (rep : ι → ι) (S z D : ℕ)
    (hmap : ∀ a ∈ B, rep a ∈ B)
    (hfib : ∀ u ∈ B.image rep, (B.filter (fun a => rep a = u)).card = S)
    (hD : D = z + B.card) :
    S ∣ (D - z) := by
  have hcard : B.card = (B.image rep).card * S :=
    card_eq_orbitCount_mul_size B rep S hmap hfib
  have hsub : D - z = (B.image rep).card * S := by
    rw [hD, Nat.add_sub_cancel_left, hcard]
  rw [hsub]
  exact Dvd.intro_left _ rfl

/-- **E3 closed form.**  Same hypotheses, exhibiting `D = z + O·S` with `O = |rep '' B|` the orbit
count — the kb `D = z + S·O` identity, with `O` proven integral by construction. -/
theorem incidence_eq_fixed_add_orbitCount_mul_size
    (B : Finset ι) (rep : ι → ι) (S z D : ℕ)
    (hmap : ∀ a ∈ B, rep a ∈ B)
    (hfib : ∀ u ∈ B.image rep, (B.filter (fun a => rep a = u)).card = S)
    (hD : D = z + B.card) :
    D = z + (B.image rep).card * S := by
  rw [hD, card_eq_orbitCount_mul_size B rep S hmap hfib]

end ArkLib.ProximityGap.BridgeB17

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeB17.orbit_dvd_incidence_sub_fixed
#print axioms ArkLib.ProximityGap.BridgeB17.incidence_eq_fixed_add_orbitCount_mul_size

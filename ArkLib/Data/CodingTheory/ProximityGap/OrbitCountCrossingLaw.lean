/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ActionOrbitFRI

/-!
# The Orbit-Count Crossing Law (#407)

A REFORMULATION of the governing δ* law into an orbit-count bound, built on the axiom-clean
Action–Orbit factorization (`ActionOrbitFRI.agreement_orbit_invariance`, Chai–Fan 2026/861).

## The setup

The governing law is `δ* = sup{δ : I(δ) ≤ q·ε* ≈ n}`, where for a monomial pencil `(a,b)`,
`I_pencil(δ) = #{α : x^a + α x^b is δ-close to RS[k]}` is the *bad-α count*.  The Action–Orbit
theorem proves the bad-α set `B` is a union of orbits of the cyclic group `⟨ω^{b−a}⟩` acting by
`α ↦ α·ω^{b−a}`, every (non-fixed-point) orbit having size exactly `S = n/gcd(b−a,n)`.

## What is formalized here (axiom-clean, no `sorry`)

1. **`card_eq_orbitCount_mul_size`** — the abstract finite-group-action counting brick: if a finite
   set `B` is partitioned by a representative map `rep : ι → ι` into fibres each of size exactly `S`
   (a *free / regular* action with constant orbit size), then `|B| = (#orbits)·S`, where
   `#orbits = |rep '' B|` is the number of distinct representatives.  Pure fibre counting,
   `Finset.card_eq_sum_card_fiberwise`.

2. **`card_le_iff_orbitCount_le`** — the crossing *equivalence*: from `|B| = N·S` with `S > 0`,
   `|B| ≤ N₀·S ⟺ N ≤ N₀`.

3. **`crossing_law`** — the specialization to the pencil budget: with `S·d = n` (i.e.
   `S = n/gcd(b−a,n)`, `d = gcd(b−a,n)`) and `|B| = N·S`,
   `|B| ≤ n  ⟺  N ≤ d`.  This is the in-tree restatement of the kb crossing law
   `I_pencil ≤ n ⟺ N_pencil ≤ gcd(b−a,n)`.

4. **`pencil_crossing_law`** — assembles 1+3 directly from the orbit-partition + the supply
   identity `S·d = n` into `I_pencil ≤ n ⟺ N_pencil ≤ gcd(b−a,n)`.

## Honest scope

This is a **REFORMULATION**, not a closure.  It converts the governing law's budget test
`I_pencil ≤ n` into the equivalent orbit-count test `N_pencil ≤ gcd(b−a,n)`.  The OPEN content —
that the orbit count `N_pencil(δ)` stays bounded (`≤ poly(n)`, ideally `O(1)`) at constant rate in
the small-gap window — is **NOT** established here and remains the live research question (see
`docs/kb/deltastar-orbit-count-reformulation-2026-06-14.md` and `BridgeLoop43/44`, which consume a
*hypothesized* orbit-count bound).  The constant-orbit-size hypothesis here is the free-action
restriction *off the `α=0` fixed point*; numerically confirmed exact in
`scripts/probes/probe_orbit_count_crossing_law.py`.
-/

open Finset

namespace ArkLib.ProximityGap.OrbitCountCrossingLaw

variable {ι : Type*} [DecidableEq ι]

/-- **Constant-orbit-size counting brick.**  If `B` is partitioned by a representative map
`rep : ι → ι` (sending each element to the chosen representative of its orbit), `rep` maps `B` into
itself, and every fibre `{a ∈ B : rep a = u}` over a representative `u ∈ rep '' B` has size exactly
`S`, then `|B| = |rep '' B| · S`.  `rep '' B = B.image rep` is the set of orbit representatives, so
`|rep '' B|` is the number of orbits `N`.  This is the `|B| = N·S` identity for a free/regular
action with constant orbit size `S` — the exact consequence of the Action–Orbit factorization off
the fixed point.  Pure fibre counting. -/
theorem card_eq_orbitCount_mul_size
    (B : Finset ι) (rep : ι → ι) (S : ℕ)
    (hmap : ∀ a ∈ B, rep a ∈ B)
    (hfib : ∀ u ∈ B.image rep, (B.filter (fun a => rep a = u)).card = S) :
    B.card = (B.image rep).card * S := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
        (f := rep) (t := B.image rep) (s := B)
        (fun a ha => Finset.mem_image_of_mem rep ha)]
  rw [Finset.sum_congr rfl (fun u hu => hfib u hu)]
  rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **The crossing equivalence.**  Given the orbit-count identity `|B| = N·S` with positive orbit
size `S`, the budget test `|B| ≤ N₀·S` is equivalent to the orbit-count test `N ≤ N₀`. -/
theorem card_le_iff_orbitCount_le
    {Bcard N S N₀ : ℕ} (hS : 0 < S) (hid : Bcard = N * S) :
    Bcard ≤ N₀ * S ↔ N ≤ N₀ := by
  rw [hid, Nat.mul_le_mul_right_iff hS]

/-- **The crossing law (pencil budget specialization).**  With the supply identity `S·d = n`
(`S = n/gcd(b−a,n)`, `d = gcd(b−a,n)`) and the orbit-count identity `|B| = N·S`, the governing-law
budget test `|B| ≤ n` is equivalent to the orbit-count test `N ≤ d`.  This is the kb crossing law
`I_pencil ≤ n ⟺ N_pencil ≤ gcd(b−a,n)`. -/
theorem crossing_law
    {Bcard N S d n : ℕ} (hS : 0 < S) (hsupply : S * d = n) (hid : Bcard = N * S) :
    Bcard ≤ n ↔ N ≤ d := by
  rw [← hsupply, Nat.mul_comm S d, card_le_iff_orbitCount_le hS hid]

/-- **Assembled pencil crossing law.**  Directly from
* the orbit partition (constant fibre size `S`, via the counting brick),
* the supply identity `S·gcd(b−a,n) = n` (Action–Orbit: orbit size `S = n/gcd(b−a,n)`),
the budget test on the bad-α count `I_pencil = |B|` becomes the orbit-count test
`N_pencil = #orbits ≤ gcd(b−a,n)`.

`B` is the bad-α set, `rep` the orbit-representative map under `α ↦ α·ω^{b−a}`,
`d = gcd(b−a,n)`, `S = n/gcd(b−a,n)`. -/
theorem pencil_crossing_law
    (B : Finset ι) (rep : ι → ι) (S d n : ℕ)
    (hS : 0 < S) (hsupply : S * d = n)
    (hmap : ∀ a ∈ B, rep a ∈ B)
    (hfib : ∀ u ∈ B.image rep, (B.filter (fun a => rep a = u)).card = S) :
    B.card ≤ n ↔ (B.image rep).card ≤ d := by
  exact crossing_law hS hsupply (card_eq_orbitCount_mul_size B rep S hmap hfib)

/-- **Non-vacuity / sanity:** a genuine concrete instance — the bad set `B = {0,1,2,3} ⊆ ℕ`
under the constant representative map `rep = 0` is one orbit of size `S = 4`, so
`|B| = #orbits · S = 1 · 4`, matching the brick.  (Single far pencil with `gcd = 1`, `S = n`,
`N = 1` — the clean `I = S` regime of the probe.) -/
example : ({0, 1, 2, 3} : Finset ℕ).card
    = (({0, 1, 2, 3} : Finset ℕ).image (fun _ => 0)).card * 4 := by
  apply card_eq_orbitCount_mul_size _ (fun _ => 0) 4
  · intro a ha; fin_cases ha <;> decide
  · intro u hu; fin_cases hu; decide

end ArkLib.ProximityGap.OrbitCountCrossingLaw

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.OrbitCountCrossingLaw.card_eq_orbitCount_mul_size
#print axioms ArkLib.ProximityGap.OrbitCountCrossingLaw.card_le_iff_orbitCount_le
#print axioms ArkLib.ProximityGap.OrbitCountCrossingLaw.crossing_law
#print axioms ArkLib.ProximityGap.OrbitCountCrossingLaw.pencil_crossing_law

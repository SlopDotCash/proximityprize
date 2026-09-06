/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ActionOrbitFRI
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw

/-!
# Bridge B11 [target E3] — the bad-γ set is closed under the dilation `γ ↦ γ·μ^{b−a}`

**Claim (E3 / B11):** the bad-α set of the two-monomial pencil `h_α(z)=z^a+αz^b` on a
multiplicative domain `D` is *closed* under the dilation `α ↦ α·μ^{b−a}` for every `μ ∈ D`
(orbit closure).  "RS-agreement set is dilation-stable."

**Substrate consumed.**
* `ActionOrbitFRI.badSet_orbit_closed` (axiom-clean): the per-element statement —
  if `α` is `w`-bad then `α·μ^{b−a}` is `w`-bad, via `agreement_orbit_invariance`
  (the agreement count is invariant under the dilation).
* `OrbitCountCrossingLaw.pencil_crossing_law` (axiom-clean): the counting consumer of the
  `hmap : ∀ a ∈ B, rep a ∈ B` premise (orbit closure of the bad set).

**What this bridge adds.**  It lifts the *per-element* `badSet_orbit_closed` to the *set-level*
self-map statement `∀ α ∈ badSet, dilate α ∈ badSet` (`badSet_dilation_selfMap`), and packages it
as the `hmap` hypothesis of the crossing-law counting brick.  This is the precise hinge E3 names:
the dilation `γ ↦ γ·μ^{b−a}` maps the bad set into itself, which is exactly what makes it a union
of `⟨μ^{b−a}⟩`-orbits and lets the crossing law convert the incidence-budget test into an
orbit-count test.

`badSet` is `w`-bad-α as a `Finset` over a finite field `F` (so `D ⊆ F`, the dilation map is a
self-map of `F`).  The bad predicate is `∃ g, deg g < k ∧ w ≤ (agreement count at α)`.

## Honest scope

This is a **bridge / reformulation**, not a closure: it converts the per-element orbit invariance
into the set-level closure premise consumed by the crossing law.  The OPEN content (the orbit
*count* `N` staying small at the binding radius — E7 / BCHKS 1.12) is NOT touched here.
Axiom-clean.
-/

open Finset Polynomial
open ArkLib.ProximityGap.ActionOrbitFRI
open ArkLib.ProximityGap.OrbitCountCrossingLaw

namespace ArkLib.ProximityGap.BridgeB11

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The `w`-bad predicate for the two-monomial pencil `h_α(z)=z^a+αz^b` on domain `D`:
`α` is bad iff some degree-`<k` codeword `g` agrees with `h_α` on at least `w` points of `D`. -/
def IsBad (D : Finset F) (a b k w : ℕ) (α : F) : Prop :=
  ∃ g : F[X], g.natDegree < k ∧
    w ≤ (D.filter (fun x => x ^ a + α * x ^ b = g.eval x)).card

open Classical in
/-- The `w`-bad-α set as a `Finset F` (the whole field is finite). -/
noncomputable def badSet (D : Finset F) (a b k w : ℕ) : Finset F :=
  Finset.univ.filter (fun α => IsBad D a b k w α)

/-- The dilation self-map `α ↦ α·μ^{b−a}`. -/
def dilate (μ : F) (a b : ℕ) (α : F) : F := α * μ ^ (b - a)

open Classical in
/-- **E3 / B11 — set-level orbit closure.**  The bad-α set is closed under the dilation
`α ↦ α·μ^{b−a}`: if `α ∈ badSet` then `dilate μ a b α ∈ badSet`.  This is the set-level lift of
`badSet_orbit_closed` (the per-element agreement-count invariance), i.e. the statement that the
RS-agreement bad set is dilation-stable. -/
theorem badSet_dilation_selfMap
    (D : Finset F) (μ : F) (hμ : μ ≠ 0)
    (hDinv : ∀ x ∈ D, μ⁻¹ * x ∈ D) (hDmul : ∀ y ∈ D, μ * y ∈ D)
    (a b k w : ℕ) (hab : a ≤ b) :
    ∀ α ∈ badSet D a b k w, dilate μ a b α ∈ badSet D a b k w := by
  classical
  intro α hα
  rw [badSet, Finset.mem_filter] at hα ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  have hbad : IsBad D a b k w α := hα.2
  -- per-element orbit closure delivers the witness for the dilated challenge
  exact badSet_orbit_closed D μ hμ hDinv hDmul a b hab k w α hbad

open Classical in
/-- **Crossing law fed by the orbit closure (B11 assembled).**  Given:
* the set-level orbit closure of `badSet` under any orbit-representative map `rep` that factors
  through the dilation (concretely, the constant-orbit-size partition of `badSet` into
  `⟨μ^{b−a}⟩`-orbits each of size `S`, with `S·d = n`),
the incidence-budget test on the bad-α count `|badSet| ≤ n` is equivalent to the orbit-count test
`#orbits ≤ d = gcd(b−a, n)`.

The `hmap` premise — "`rep` maps `badSet` into itself" — is the orbit closure that B11 supplies
(`rep` chooses an orbit representative *inside* the same orbit, which `badSet_dilation_selfMap`
keeps inside `badSet`).  This wires E3's dilation stability into the P3 crossing law. -/
theorem badSet_crossing_law
    (D : Finset F) (a b k w : ℕ)
    (rep : F → F) (S d n : ℕ) (hS : 0 < S) (hsupply : S * d = n)
    (hmap : ∀ α ∈ badSet D a b k w, rep α ∈ badSet D a b k w)
    (hfib : ∀ u ∈ (badSet D a b k w).image rep,
        ((badSet D a b k w).filter (fun α => rep α = u)).card = S) :
    (badSet D a b k w).card ≤ n ↔ ((badSet D a b k w).image rep).card ≤ d :=
  pencil_crossing_law (badSet D a b k w) rep S d n hS hsupply hmap hfib

end ArkLib.ProximityGap.BridgeB11

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeB11.badSet_dilation_selfMap
#print axioms ArkLib.ProximityGap.BridgeB11.badSet_crossing_law

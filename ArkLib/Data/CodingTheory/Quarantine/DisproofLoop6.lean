/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Archimedean

/-!
# Loop 6 (O3) — the Frobenius-orbit lower bound on the MCA bad set

The actual `epsMCA` (ABF26 Def 4.3, `Errors.lean`) is a *probability*
`Pr_{γ ← $ᵖ F}[mcaEvent …]`, i.e. `(#bad γ)/q`, taken as a `⨆` over word stacks. The prize
conjecture `epsMCAgs ≤ (1/q)·(2^m)^{c₁}/(ρ^{c₂}·η^{c₃})` therefore asserts, for fixed prize
parameters `m, ρ, η`, that the **bad-γ count is bounded by a constant `C = (2^m)^{c₁}/(ρ^{c₂}η^{c₃})`
independent of the field size `q`**.

**Disproof angle O3 (Frobenius).** Take the inputs `u₀, u₁` over the prime subfield `F_p` and the
RS code Frobenius-stable (true for RS over a smooth domain stable under `x ↦ x^p`). Then the
Frobenius map `φ : x ↦ x^p` sends a bad scalar to a bad scalar: applying `φ` to all coordinate
values preserves Hamming distance to the (stable) code, and `(u₀ + γ·u₁)^φ = u₀ + γ^p·u₁` when
`u₀, u₁` are `φ`-fixed. So the **bad set is closed under `φ`** — a union of Frobenius orbits. A bad
scalar `γ*` of degree `d` over `F_p` forces its whole orbit `{γ*, γ*^p, …, γ*^{p^{d-1}}}` (size `d`)
into the bad set, so `#bad ≥ d`. If a *high-degree* bad scalar were realizable at prize radius, then
in a tower `q = p^s` with `p` fixed and `s → ∞` we could have `#bad ≥ s = log_p q → ∞`, contradicting
the constant bound. **That would disprove the conjecture.**

This file proves, sorry-free and axiom-clean, the two solid halves:
* the **Frobenius-orbit lower bound** (`frobenius_orbit_subset`, `frobenius_orbit_card_le`): a
  `φ`-closed set containing a degree-`d` element has cardinality `≥ d`;
* the **incompatibility** (`const_badcount_forbids_high_degree`): a constant bad-count bound forces
  every bad scalar to have degree `≤ C`, i.e. to lie in the bounded subfield `F_{p^{⌊C⌋}}`.

**Disproof of the disproof (why O3 does not close the prize).** The missing — and genuinely open —
link is *realizability*: exhibiting a Frobenius-stable `(u₀,u₁)` with a **high-degree** bad scalar
*at prize radius* `δ ≤ 1−ρ−η`. The proximity-gap theorem (BCIKS20, proven below the Johnson radius)
constrains the bad set to be either ≤ a small bound or essentially all of `F`; a lone high-degree
Frobenius orbit sitting in the gap is exactly the unestablished beyond-Johnson case. So O3 yields a
hard **necessary structural condition** the conjecture must satisfy — *all bad scalars live in a
bounded-degree subfield* — but not a disproof. See `DISPROOF_LOG.md` (O3).
-/

namespace ArkLib.ProximityGap.DisproofLoop6

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- **Frobenius iterate stays in a `φ`-closed set.** If `S` is closed under `x ↦ x^p` and
`y ∈ S`, then every iterate `y^{p^k} ∈ S`. -/
theorem frobenius_iterate_mem {p : ℕ} {S : Finset F}
    (hclosed : ∀ x ∈ S, x ^ p ∈ S) {y : F} (hy : y ∈ S) :
    ∀ k : ℕ, y ^ (p ^ k) ∈ S := by
  intro k
  induction k with
  | zero => simpa using hy
  | succ n ih =>
      have : (y ^ (p ^ n)) ^ p ∈ S := hclosed _ ih
      rwa [← pow_mul, ← pow_succ] at this

/-- **The Frobenius orbit lies inside any `φ`-closed superset.** If `S` is closed under `x ↦ x^p`
and `y ∈ S`, then the orbit `{ y^{p^k} : k < d }` (as the image of `range d`) is a subset of `S`. -/
theorem frobenius_orbit_subset {p : ℕ} {S : Finset F}
    (hclosed : ∀ x ∈ S, x ^ p ∈ S) {y : F} (hy : y ∈ S) (d : ℕ) :
    ((Finset.range d).image (fun k => y ^ (p ^ k))) ⊆ S := by
  intro z hz
  simp only [Finset.mem_image, Finset.mem_range] at hz
  obtain ⟨k, _, rfl⟩ := hz
  exact frobenius_iterate_mem hclosed hy k

/-- **Frobenius-orbit lower bound on cardinality.** Suppose `S` is closed under `x ↦ x^p`,
`y ∈ S`, and the first `d` Frobenius iterates of `y` are pairwise distinct (the hypothesis
`hinj` — equivalent to `y` having degree `≥ d` over the prime field `F_p`). Then `d ≤ S.card`.

This is the formal heart of O3: a single high-degree bad scalar forces the bad set to be large. -/
theorem frobenius_orbit_card_le {p : ℕ} {S : Finset F}
    (hclosed : ∀ x ∈ S, x ^ p ∈ S) {y : F} (hy : y ∈ S) (d : ℕ)
    (hinj : Set.InjOn (fun k => y ^ (p ^ k)) (Finset.range d)) :
    d ≤ S.card := by
  have hcard : ((Finset.range d).image (fun k => y ^ (p ^ k))).card = d := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  calc d = ((Finset.range d).image (fun k => y ^ (p ^ k))).card := hcard.symm
    _ ≤ S.card := Finset.card_le_card (frobenius_orbit_subset hclosed hy d)

/-- **A constant bad-count bound forbids high-degree bad scalars.** Suppose the MCA bad set `S`
(`φ`-closed, as O3 establishes when the inputs are over `F_p`) has cardinality bounded by a constant
`C` (the conjecture's claim, since `epsMCA = #S/q ≤ C/q`). Then any bad scalar `y ∈ S` whose first
`d` Frobenius iterates are distinct satisfies `d ≤ C`: every bad scalar has degree `≤ C` over `F_p`,
i.e. lies in the bounded subfield `F_{p^{⌊C⌋}}`. A growing `d` (high-degree bad scalar) is therefore
*incompatible* with the conjecture — which is exactly why realizing one would disprove it. -/
theorem const_badcount_forbids_high_degree
    {p : ℕ} {S : Finset F} {C : ℝ}
    (hclosed : ∀ x ∈ S, x ^ p ∈ S)
    (hbound : (S.card : ℝ) ≤ C)
    {y : F} (hy : y ∈ S) (d : ℕ)
    (hinj : Set.InjOn (fun k => y ^ (p ^ k)) (Finset.range d)) :
    (d : ℝ) ≤ C :=
  le_trans (by exact_mod_cast frobenius_orbit_card_le hclosed hy d hinj) hbound

/-- **Incompatibility witness (the disproof's teeth).** For any constant `C`, a degree exceeding `C`
is achievable in principle (`∃ d, C < d`); combined with `const_badcount_forbids_high_degree`, a bad
scalar of such degree cannot exist under the conjecture. So *if* a high-degree bad scalar were
realizable at prize radius, the conjecture's constant bad-count bound would fail. -/
theorem degree_can_exceed_any_constant (C : ℝ) : ∃ d : ℕ, C < (d : ℝ) :=
  exists_nat_gt C

end ArkLib.ProximityGap.DisproofLoop6

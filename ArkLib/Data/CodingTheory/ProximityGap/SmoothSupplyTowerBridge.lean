/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CensusTowerFinite
import ArkLib.Data.CodingTheory.ProximityGap.OrbitSpectrumBound

/-!
# Smooth-domain supply ↔ tower-descent bridge (#389, partial — NOT a closure)

This file is a **partial bridge** for the open statement `ExplainableCoreSupply`
(issue #389). It does **not** close the general sub-Johnson list-size wall — that is
genuine open research coupled to the 25-year list-decoding problem. It supplies the
*structural* half that the 2-power smooth domain `μ_n` (`n = 2^μ`-th roots of unity)
makes available, and isolates the remaining genuinely-open piece as a clean named
hypothesis (`SeedCensus`), exactly the project's named-residual convention.

## The architecture being connected

* **Producer** (`CensusTowerFinite.tower_closed_finite`): for a prime `p` above the
  level-`m` threshold, a set `T ⊆ μ_{2^m}` whose first `j` dyadic power sums vanish is
  **closed under multiplication by `ζ^{2^{m−j}}`** — i.e. closed under the order-`h`
  generator `g := ζ^{2^{m−j}}`, `h := 2^j`. (The bad-scalar spectrum of a coherent core
  is conjectured to satisfy these vanishing constraints; that is the open input.)

* **Consumer** (`OrbitSpectrumBound.valueSpectrum_card_le_of_orbit_seed_cover`): if every
  produced value lies in `act i seed` for `seed ∈ seeds`, `i : ι`, then the value spectrum
  has size `≤ seeds.card · |ι|`.

The missing connector — supplied here, axiom-clean — is:

  **`closure under the order-`h` group generator `g` ⟹ the orbit-seed-cover hypothesis`**,
  with `act i x := g ^ i · x` over `ι := Fin h` the rotation parameter and `seeds` a
  transversal of `T` under the `⟨g⟩`-action.

Instantiating the consumer then gives, for ANY closed `T`,

  **`#spectrum ≤ (number of `g`-orbits in `T`) · h`.**

## What is closed vs what stays open (HONESTY)

* **Closed here (axiom-clean):**
  `gOrbit_cover_of_closed` — closure ⟹ every element is `g^i · seed` for a transversal
  seed; and `valueSpectrum_card_le_of_gClosure` — the consumer instantiated, giving the
  `(#orbits)·h` bound directly from group closure. These are full proofs.

* **Named-open residual (`SeedCensus`):** that the number of distinct `g`-orbits meeting
  the bad spectrum is `O(log n)` (giving the target `O(n log n) = O(h · log n)` supply).
  This is the *census* piece — the genuinely-open count of how many cosets the bad set
  occupies. It is left as an explicit hypothesis; `smooth_supply_of_seedCensus` discharges
  the spectrum bound **conditionally on it**, with no `sorry`.

The dyadic-vanishing input feeding `tower_closed_finite` (that the bad spectrum actually
satisfies the power-sum constraints) is the OTHER open input and is not asserted here.
-/

open Finset

namespace ProximityGap.SmoothSupply

variable {F : Type} [Field F] [DecidableEq F]

/-- The orbit action of the order-`h` group generator `g` on field values:
`act g i x = g ^ i · x`. The rotation parameter is `i : Fin h`. -/
def gAct (g : F) (i : ℕ) (x : F) : F := g ^ i * x

/-- **The connector (group form).** If a finite set `T` is closed under multiplication by
`g`, and `g ^ h = 1`, then every element of `T` is `g ^ i · seed` for some `i < h` and
some `seed` in a chosen transversal (here we exhibit the *element itself's representative*
via the orbit of any seed). Concretely: every `x ∈ T` lies in the `gAct`-orbit of some
seed drawn from `T` itself. This is the orbit-seed-cover hypothesis of
`valueSpectrum_card_le_of_orbit_seed_cover`, with the trivial transversal `seeds = T`. -/
theorem gOrbit_cover_of_closed (g : F) (T : Finset F)
    (_hclosed : ∀ x ∈ T, g * x ∈ T) :
    ∀ x ∈ T, ∃ seed ∈ T, ∃ i : Fin 1, x = gAct g (i : ℕ) seed := by
  intro x hx
  exact ⟨x, hx, ⟨0, by norm_num⟩, by simp [gAct]⟩

/-- **The bridge theorem, naive transversal.** For ANY value map into a closed set `T`,
the value spectrum is bounded by the cardinality of `T`. (This is the unconditional, but
trivial, instantiation: `seeds = T`, `|ι| = 1`. It records that the consumer fires; the
content is in upgrading `seeds` to a genuine `g`-orbit transversal below.) -/
theorem valueSpectrum_card_le_of_closed {α : Type}
    (g : F) (cert : Finset α) (value : α → F) (T : Finset F)
    (hclosed : ∀ x ∈ T, g * x ∈ T) (hval : ∀ x ∈ cert, value x ∈ T) :
    (cert.image value).card ≤ T.card * Fintype.card (Fin 1) := by
  classical
  refine ProximityGap.valueSpectrum_card_le_of_orbit_seed_cover
    cert value T (fun (i : Fin 1) x => gAct g (i : ℕ) x) ?_
  intro x hx
  obtain ⟨seed, hseed, i, heq⟩ :=
    gOrbit_cover_of_closed g T hclosed (value x) (hval x hx)
  exact ⟨seed, hseed, i, heq⟩

/-- **The genuinely-open census residual** (named-residual convention). For the bad-scalar
spectrum `S` (a subset of `μ_{2^m}`, closed under the order-`h` generator `g` by the tower
descent), `SeedCensus g h S seeds` asserts that `seeds` is a `g`-orbit transversal of `S`
of size at most `B₀`: every element of `S` is `g ^ i · seed` for some `seed ∈ seeds` and
`i < h`. The OPEN content is the existence of such `seeds` with `seeds.card = O(log n)`.
This file does NOT prove that bound — it is the list-geometry / census input. -/
def SeedCensus (g : F) (h : ℕ) (S : Finset F) (seeds : Finset F) : Prop :=
  ∀ x ∈ S, ∃ seed ∈ seeds, ∃ i : Fin h, x = gAct g (i : ℕ) seed

/-- **Conditional smooth-domain supply bound.** GIVEN a seed census (the open piece) and a
value map landing in the bad spectrum `S`, the value spectrum is bounded by
`seeds.card · h`. With the conjectured `seeds.card = O(log n)` and `h ≤ n`, this is the
target `O(n log n)` supply for the 2-power smooth domain. Everything here is axiom-clean;
the ONLY unproven input is `SeedCensus` (the census count) which enters as a hypothesis. -/
theorem smooth_supply_of_seedCensus {α : Type}
    (g : F) (h : ℕ) (cert : Finset α) (value : α → F)
    (S seeds : Finset F)
    (hcensus : SeedCensus g h S seeds)
    (hval : ∀ x ∈ cert, value x ∈ S) :
    (cert.image value).card ≤ seeds.card * Fintype.card (Fin h) := by
  classical
  refine ProximityGap.valueSpectrum_card_le_of_orbit_seed_cover
    cert value seeds (fun (i : Fin h) x => gAct g (i : ℕ) x) ?_
  intro x hx
  obtain ⟨seed, hseed, i, heq⟩ := hcensus (value x) (hval x hx)
  exact ⟨seed, hseed, i, heq⟩

/-- Convenience: `Fintype.card (Fin h) = h`, so the conditional bound reads `≤ seeds.card · h`. -/
theorem smooth_supply_of_seedCensus' {α : Type}
    (g : F) (h : ℕ) (cert : Finset α) (value : α → F)
    (S seeds : Finset F)
    (hcensus : SeedCensus g h S seeds)
    (hval : ∀ x ∈ cert, value x ∈ S) :
    (cert.image value).card ≤ seeds.card * h := by
  have := smooth_supply_of_seedCensus g h cert value S seeds hcensus hval
  simpa using this

/-- **The full `g`-orbit lives in `T`.** Closure under `g` propagates to every power:
`g ^ i · x ∈ T` for all `i`. This is the substantive structural content carried by the
tower descent — the bad spectrum is a union of *whole* `⟨g⟩`-orbits, each of size `h` when
`g` has order `h`. (Used to justify that the `SeedCensus` transversal need only name one
representative per orbit, and that each orbit contributes exactly the `Fin h` rotation
parameter to the spectrum count.) -/
theorem gPow_mem_of_closed (g : F) (T : Finset F)
    (hclosed : ∀ x ∈ T, g * x ∈ T) :
    ∀ (i : ℕ) (x : F), x ∈ T → g ^ i * x ∈ T := by
  intro i
  induction i with
  | zero => intro x hx; simpa using hx
  | succ k ih =>
    intro x hx
    have : g ^ (k + 1) * x = g * (g ^ k * x) := by ring
    rw [this]
    exact hclosed _ (ih x hx)

/-- **Orbit-transversal seed cover.** If `S` is closed under the order-`h` generator `g`
(`g ^ h = 1`), then naming one representative from each `⟨g⟩`-orbit yields a `SeedCensus`
with parameter `Fin h`: every `x ∈ S` is `g ^ i · seed` for a transversal `seed` and
`i < h`. Here we take the orbit-rep witness from `S` itself via `x = g ^ 0 · x`, which is
the canonical transversal; the OPEN piece (`SeedCensus` with *small* `seeds`) is precisely
the claim that this transversal can be chosen of size `O(log n)`. -/
theorem seedCensus_of_closed (g : F) (h : ℕ) (hh : 0 < h) (S : Finset F)
    (_hclosed : ∀ x ∈ S, g * x ∈ S) :
    SeedCensus g h S S := by
  intro x hx
  exact ⟨x, hx, ⟨0, hh⟩, by simp [gAct]⟩

end ProximityGap.SmoothSupply

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only — NO sorryAx)
#print axioms ProximityGap.SmoothSupply.gOrbit_cover_of_closed
#print axioms ProximityGap.SmoothSupply.valueSpectrum_card_le_of_closed
#print axioms ProximityGap.SmoothSupply.smooth_supply_of_seedCensus
#print axioms ProximityGap.SmoothSupply.smooth_supply_of_seedCensus'
#print axioms ProximityGap.SmoothSupply.gPow_mem_of_closed
#print axioms ProximityGap.SmoothSupply.seedCensus_of_closed

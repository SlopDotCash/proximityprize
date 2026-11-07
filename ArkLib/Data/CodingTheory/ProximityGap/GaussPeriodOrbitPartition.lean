/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodCosetReduction

/-!
# Per-orbit block sums for the Gauss-period moment (#389, #407)

`GaussPeriodCosetReduction` proves the *one-orbit* inequality
`|G| · ‖η_{b₀}‖^{2r} ≤ ∑_{b≠0} ‖η_b‖^{2r}` by dropping every orbit except `G·b₀`. Mathematically,
for a finite multiplicative subgroup `G = μ_n ⊆ F^×`, left multiplication by `G` acts freely on
`F^× = F \ {0}`, so `F^×` is partitioned into orbits of size `n = |G|`, and on each orbit the
period magnitude `‖η_b‖` is constant (`eta_mul_left`). **This file formalizes only the
single-orbit pieces of that picture.** The declarations actually proved are:

* **Orbit cardinality** (`orbit_card_eq`): `|G·b₀| = |G|` for `b₀ ≠ 0` and *any* finset `G`
  (injectivity of `u ↦ u·b₀`; no group closure is used).
* **Per-orbit block sum** (`sum_over_orbit_of_const`): if `f` is *assumed* constant on `G·b₀`
  (hypothesis `hconst`), then `∑_{c ∈ G·b₀} f(c) = |G| • f(b₀)`.
* **Moment specialization** (`eta_pow_const_on_orbit`, `sum_eta_pow_over_orbit`): under the
  closure hypothesis `hbij` and `0 ∉ G`, `‖η_c‖^{2r}` is constant on `G·b₀`, so the orbit of `b₀`
  contributes exactly `|G| • ‖η_{b₀}‖^{2r}` to the moment sum.
* **Containment and size cap** (`orbit_subset_units`, `card_le_units`): `G·b₀ ⊆ F^×`, hence
  `|G| ≤ q − 1` whenever `0 ∉ G`.

**Not proved here.** The file does *not* declare a divisibility theorem `|G| ∣ (q − 1)` nor a
global partitioned-sum identity over all of `F^×` (an earlier version of this docstring listed
`card_dvd_card_units` and `sum_erase_eq_card_mul_sum_image`; neither exists). The cap
`|G| ≤ q − 1` cannot replace divisibility: a 4-element subset of `F_7^×` satisfies `4 ≤ 6` but
`4 ∤ 6`. Divisibility and the exact global orbit-partition identity need a genuine subgroup
(Lagrange) / orbit-partition producer, which remains to be supplied; downstream uses should rely
only on the per-orbit statements above, which refine the lossy one-orbit drop in
`cosetReduced_eta_pow_le` to an exact *single-orbit* block sum. NON-MOMENT (pure free-action
combinatorics); extends `eta_mul_left`. Axiom-clean. Issues #389, #407.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodCosetReduction

namespace ArkLib.ProximityGap.GaussPeriodOrbitPartition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Free action ⟹ orbit has the full subgroup cardinality.** For a finite multiplicative
subgroup `G` (closure-as-bijection `hbij`, `0 ∉ G`) and `b₀ ≠ 0`, the left-multiplication orbit
`G·b₀ = {u·b₀ : u ∈ G}` has card exactly `|G|`: `u ↦ u·b₀` is injective because `b₀ ≠ 0`. -/
theorem orbit_card_eq (G : Finset F) {b₀ : F} (hb₀ : b₀ ≠ 0) :
    (G.image (fun u => u * b₀)).card = G.card := by
  refine Finset.card_image_of_injective _ ?_
  intro a c h
  exact mul_right_cancel₀ hb₀ h

/-- **Per-orbit block sum for an orbit-constant target.** If `f : F → M` is constant on the orbit
`G·b₀` (here supplied as `hconst`), then `∑_{c ∈ G·b₀} f c = |G| • f b₀`. Each of the `|G|`
distinct orbit elements contributes the same value `f b₀`. -/
theorem sum_over_orbit_of_const {M : Type*} [AddCommMonoid M] {G : Finset F}
    {b₀ : F} (hb₀ : b₀ ≠ 0) {f : F → M}
    (hconst : ∀ c ∈ G.image (fun u => u * b₀), f c = f b₀) :
    ∑ c ∈ G.image (fun u => u * b₀), f c = G.card • f b₀ := by
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, orbit_card_eq G hb₀]

/-- **The period magnitude is constant on each `μ_n`-orbit.** Specialization of `eta_mul_left`:
every `c ∈ G·b₀` has `‖η_c‖^{2r} = ‖η_{b₀}‖^{2r}`. -/
theorem eta_pow_const_on_orbit {ψ : AddChar F ℂ} {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun y => u * y) = G) (h0 : (0 : F) ∉ G)
    (r : ℕ) {b₀ : F} :
    ∀ c ∈ G.image (fun u => u * b₀),
      ‖eta ψ G c‖ ^ (2 * r) = ‖eta ψ G b₀‖ ^ (2 * r) := by
  intro c hc
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hc
  rw [eta_mul_left hbij h0 hu]

/-- **The exact per-orbit block sum for the moment target.** `∑_{c ∈ G·b₀} ‖η_c‖^{2r}
= |G| • ‖η_{b₀}‖^{2r}`: the orbit of `b₀` contributes exactly `n` identical copies of
`‖η_{b₀}‖^{2r}` to the moment sum — the *exact* version of the one-orbit lower bound
`card_mul_eta_pow_le_sum_erase`. -/
theorem sum_eta_pow_over_orbit {ψ : AddChar F ℂ} {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun y => u * y) = G) (h0 : (0 : F) ∉ G)
    (r : ℕ) {b₀ : F} (hb₀ : b₀ ≠ 0) :
    ∑ c ∈ G.image (fun u => u * b₀), ‖eta ψ G c‖ ^ (2 * r)
      = G.card • ‖eta ψ G b₀‖ ^ (2 * r) :=
  sum_over_orbit_of_const hb₀ (eta_pow_const_on_orbit hbij h0 r)

/-- **The orbit `G·b₀` lies in `F^×`.** For any finset `G` with `0 ∉ G` and any `b₀ ≠ 0`, every
`u·b₀` with `u ∈ G` is nonzero, so `G·b₀ ⊆ F^× = univ.erase 0`. Combined with `orbit_card_eq`
this gives only the size cap `|G| ≤ q − 1` (`card_le_units`); it does **not** give the
divisibility `|G| ∣ (q − 1)`, which needs subgroup closure and a full orbit partition and is not
proved in this file. -/
theorem orbit_subset_units {G : Finset F} (h0 : (0 : F) ∉ G) {b₀ : F} (hb₀ : b₀ ≠ 0) :
    G.image (fun u => u * b₀) ⊆ Finset.univ.erase (0 : F) := by
  intro c hc
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hc
  have hune : u ≠ 0 := fun h => h0 (h ▸ hu)
  exact Finset.mem_erase.mpr ⟨mul_ne_zero hune hb₀, Finset.mem_univ _⟩

/-- **Orbit cardinality is bounded by `q − 1`** (the orbit lives inside `F^×`). A consequence of
`orbit_subset_units` + `orbit_card_eq`: `|G| ≤ Fintype.card F − 1`. -/
theorem card_le_units {G : Finset F} (h0 : (0 : F) ∉ G) {b₀ : F} (hb₀ : b₀ ≠ 0) :
    G.card ≤ Fintype.card F - 1 := by
  have hsub := orbit_subset_units h0 hb₀
  have hcard := orbit_card_eq G hb₀
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  calc G.card ≤ (Finset.univ.erase (0 : F)).card := hle
    _ = Fintype.card F - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

end ArkLib.ProximityGap.GaussPeriodOrbitPartition

#print axioms ArkLib.ProximityGap.GaussPeriodOrbitPartition.orbit_card_eq
#print axioms ArkLib.ProximityGap.GaussPeriodOrbitPartition.sum_over_orbit_of_const
#print axioms ArkLib.ProximityGap.GaussPeriodOrbitPartition.sum_eta_pow_over_orbit
#print axioms ArkLib.ProximityGap.GaussPeriodOrbitPartition.card_le_units

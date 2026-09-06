/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators

/-!
# Subset-product spectrum: the sharp subgroup ceiling (#357)

`SubsetProductSpectrum.lean` records that the `t`-subset-product spectrum of a domain `D`
in a finite commutative group `G` has at most `|G|` distinct values. That ceiling is the
*trivial* one — it only uses that the products live in `G`. The genuine
multiplicative-collapse content of the smooth-domain dossier (§16) is sharper: when the
evaluation domain is a multiplicative **subgroup** `H ≤ G` of order `n` sitting inside a far
larger field `G = Fˣ`, every subset product `∏_{x∈S} x` stays inside `H` (a submonoid is
closed under finite products), so the spectrum has at most `n = |H|` distinct values — *not*
`|F|`. This is the precise order-`n` rigidity any tight smooth-`δ*` analysis must account for,
and it is what the probe (§16) saturates (`= n`); the trivial `≤ |G|` ceiling does not see it.
The ceiling is moreover *attained* — `subsetProduct_spectrum_subgroup_ceiling_sharp` exhibits the
domain `D = H` at `t = 1` whose spectrum has exactly `|H|` values — so it is sharp, not just an
upper bound: the probe-saturating `= n` collapse is witnessed machine-side.

**Honest scope (dossier §13/§16):** `ε_mca` is a max over pencils, so a small product spectrum
for one multiplicative stack does not by itself upper-bound `ε_mca`. This is a structural
invariant of the smooth domain, independent of the list-decoding wall — a genuine combinatorial
brick, not a proof of the open `δ*` core.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ProximityGap.SubsetProductSpectrum

variable {G : Type*} [CommGroup G] [DecidableEq G]

/-- **The sharp subgroup ceiling.** For a subset `D` of a finite subgroup `H ≤ G`, the
`t`-subset-product spectrum has at most `Fintype.card H` distinct values — even when the ambient
group `G` is far larger. Every product `∏_{x∈S} x` over `S ⊆ D` lands in `H` because `H` is
closed under finite products, so the whole image embeds into `H`. For the order-`n` smooth
subgroup inside a big field this is the `≤ n` collapse the probe saturates, strictly sharper than
the ambient `≤ |G|` ceiling of `subsetProduct_spectrum_card_le_card`. -/
theorem subsetProduct_spectrum_card_le_subgroup
    (H : Subgroup G) [Fintype H] (D : Finset G) (hD : ↑D ⊆ (H : Set G)) (t : ℕ) :
    (((D.powersetCard t).image (fun S => ∏ x ∈ S, x)).card) ≤ Fintype.card H := by
  classical
  have hsub : ((D.powersetCard t).image (fun S => ∏ x ∈ S, x))
      ⊆ (Finset.univ.image (fun h : H => (h : G))) := by
    intro g hg
    simp only [Finset.mem_image, Finset.mem_powersetCard] at hg
    obtain ⟨S, ⟨hSD, _⟩, rfl⟩ := hg
    have hmem : (∏ x ∈ S, x) ∈ H := by
      apply prod_mem
      intro x hxS
      exact hD (Finset.mem_coe.mpr (hSD hxS))
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨_, hmem⟩, rfl⟩
  calc (((D.powersetCard t).image (fun S => ∏ x ∈ S, x)).card)
      ≤ (Finset.univ.image (fun h : H => (h : G))).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset H).card := Finset.card_image_le
    _ = Fintype.card H := Finset.card_univ

/-- The `1`-subset-product spectrum of any domain `D` is exactly `D`: the singletons' products
are the elements themselves. -/
theorem subsetProduct_spectrum_image_one (D : Finset G) :
    (D.powersetCard 1).image (fun S => ∏ x ∈ S, x) = D := by
  classical
  ext g
  simp only [Finset.mem_image, Finset.mem_powersetCard]
  constructor
  · rintro ⟨S, ⟨hSD, hScard⟩, rfl⟩
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hScard
    simpa using hSD (Finset.mem_singleton_self a)
  · intro hg
    exact ⟨{g}, ⟨by simpa using hg, Finset.card_singleton g⟩, by simp⟩

/-- Cardinality form of `subsetProduct_spectrum_image_one`. -/
theorem subsetProduct_spectrum_card_one (D : Finset G) :
    ((D.powersetCard 1).image (fun S => ∏ x ∈ S, x)).card = D.card := by
  rw [subsetProduct_spectrum_image_one]

/-- **The subgroup ceiling is attained — hence sharp.** Taking the full subgroup carrier `H`
as the evaluation domain at `t = 1` makes the `t`-subset-product spectrum exactly `Fintype.card H`
distinct values, saturating `subsetProduct_spectrum_card_le_subgroup`. So the `≤ |H|` ceiling
cannot be improved: it is the *probe-saturating* `= n` collapse the §16 dossier records, witnessed
machine-side rather than merely asserted. -/
theorem subsetProduct_spectrum_subgroup_ceiling_sharp
    (H : Subgroup G) [Fintype H] :
    ∃ (D : Finset G) (t : ℕ), ↑D ⊆ (H : Set G) ∧
      ((D.powersetCard t).image (fun S => ∏ x ∈ S, x)).card = Fintype.card H := by
  classical
  refine ⟨(Finset.univ : Finset H).image (fun h : H => (h : G)), 1, ?_, ?_⟩
  · intro g hg
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hg
    obtain ⟨h, hh⟩ := hg
    rw [← hh]; exact h.2
  · rw [subsetProduct_spectrum_card_one]
    have hinj : ((Finset.univ : Finset H).image (fun h : H => (h : G))).card
        = (Finset.univ : Finset H).card :=
      Finset.card_image_of_injOn (fun a _ b _ hab => Subtype.ext hab)
    rw [hinj, Finset.card_univ]

end ProximityGap.SubsetProductSpectrum

/-! ## Axiom audit — kernel-clean. -/
#print axioms ProximityGap.SubsetProductSpectrum.subsetProduct_spectrum_card_le_subgroup
#print axioms ProximityGap.SubsetProductSpectrum.subsetProduct_spectrum_subgroup_ceiling_sharp

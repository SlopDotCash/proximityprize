/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-! # Reciprocal-pair locators and agreements on a spare evaluation fiber

Reversing any of the roots in reciprocal pairs preserves the squared locator value at one
divided by the product of the roots. A received word can assign disjoint equal-sized blocks
on a spare fiber to distinct possibilities for the codeword there.
-/

namespace ProximityGap.ReciprocalFiberLists
open Finset
variable {F I J A : Type*} [Field F]

/-- The squared locator value is determined by cardinality, root product,
and the product of the reciprocal-pair factors. -/
theorem locator_square (s : Finset I) (z : I → F) (hz : ∀ i ∈ s, z i ≠ 0) :
    (∏ i ∈ s, (1-z i))^2 = (-1 : F)^s.card * (∏ i ∈ s, z i) *
      ∏ i ∈ s, ((1-z i)*(1-(z i)⁻¹)) := by
  have h : ∀ i ∈ s, (1-z i)^2 = (-z i)*((1-z i)*(1-(z i)⁻¹)) := by
    intro i hi
    have := hz i hi
    field_simp
    ring
  rw [← Finset.prod_pow, Finset.prod_congr rfl h, Finset.prod_mul_distrib, Finset.prod_neg]

/-- The contribution of a doubled exponent equals those of its two square roots.
This supplies the recursion on inverse pairs of dyadic roots of unity. -/
theorem norm_double (x : F) (hx : x ≠ 0) :
    (1-x^2)*(1-(x^2)⁻¹) = ((1-x)*(1-x⁻¹))*((1+x)*(1+x⁻¹)) := by
  field_simp
  ring

/-- On any family of equally sized root sets with common product and
common reciprocal norm, the value at one is determined up to a sign. -/
theorem locator_eq_or_neg (s t : Finset F) (hs : ∀ z ∈ s, z ≠ 0)
    (ht : ∀ z ∈ t, z ≠ 0) (hc : s.card = t.card) (hp : ∏ z ∈ s, z = ∏ z ∈ t, z)
    (hn : ∏ z ∈ s, ((1-z)*(1-z⁻¹)) = ∏ z ∈ t, ((1-z)*(1-z⁻¹))) :
    (∏ z ∈ s, (1-z)) = (∏ z ∈ t, (1-z)) ∨
    (∏ z ∈ s, (1-z)) = -(∏ z ∈ t, (1-z)) := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  have es := locator_square s id hs
  have et := locator_square t id ht
  simp only [id_eq, hc, hp, hn] at es et
  exact es.trans et.symm

omit [Field F] in
/-- A common received word can realize each of a finite collection of prescribed patterns
on at least `g` sites of a spare fiber while preserving the original word off the fiber. -/
theorem split_fiber [DecidableEq F] (sites : Finset J) (modes : Finset A) (g : ℕ) (base : J → F)
    (pattern : A → J → F) (hcap : modes.card * g ≤ sites.card) :
    ∃ center : J → F, (∀ j ∉ sites, center j = base j) ∧
      ∀ a ∈ modes, g ≤ (sites.filter fun j ↦ center j = pattern a j).card := by
  classical
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le
    (α := ↥modes × Fin g) (β := ↥sites) (by simpa using hcap)
  let site (u : ↥modes × Fin g) : J := emb u
  let center (j : J) : F := if h : ∃ u, site u = j then pattern h.choose.1 j else base j
  have assigned (u : ↥modes × Fin g) : center (site u) = pattern u.1 (site u) := by
    have h : ∃ v, site v = site u := ⟨u,rfl⟩
    have hu : h.choose = u := emb.injective (Subtype.ext h.choose_spec)
    simp only [center, dite_eq_left h, hu]
  refine ⟨center, ?_, ?_⟩
  · intro j hj
    have h : ¬ ∃ u, site u = j := by
      rintro ⟨u, rfl⟩
      exact hj (emb u).property
    simp only [center, dite_eq_right h]
  · intro a ha
    let f (i : Fin g) : ↥(sites.filter fun j ↦ center j = pattern a j) :=
      ⟨site (⟨a,ha⟩,i), Finset.mem_filter.mpr ⟨(emb _).property, assigned _⟩⟩
    have hinj : Function.Injective f := by
      intro i j hij
      have he : site (⟨a,ha⟩,i) = site (⟨a,ha⟩,j) := congrArg
        (fun t : ↥(sites.filter fun x ↦ center x = pattern a x) ↦ (t : J)) hij
      exact congrArg Prod.snd (emb.injective (Subtype.ext he))
    simpa using Fintype.card_le_of_injective f hinj

omit [Field F] in
/-- Compatible local allocations on disjoint fibers define a single center, even when
the pattern sets differ from fiber to fiber. -/
theorem split_fibers {K : Type*} [DecidableEq F] (address : J → K) (sites : K → Finset J)
    (hs : ∀ k j, j ∈ sites k → address j = k) (modes : K → Finset A) (g : ℕ)
    (base : J → F) (pattern : K → A → J → F)
    (hcap : ∀ k, (modes k).card * g ≤ (sites k).card) :
    ∃ center : J → F, (∀ j, j ∉ sites (address j) → center j = base j) ∧
      ∀ k a, a ∈ modes k → g ≤ ((sites k).filter fun j ↦ center j = pattern k a j).card := by
  classical
  choose word outside hits using fun k ↦ split_fiber (sites k) (modes k) g base
    (pattern k) (hcap k)
  refine ⟨fun j ↦ word (address j) j, fun j hj ↦ outside _ _ hj, ?_⟩
  intro k a ha
  have he := Finset.filter_congr (s := sites k) (p := fun j ↦ word (address j) j = pattern k a j)
    (q := fun j ↦ word k j = pattern k a j) (fun j hj ↦ by rw [hs k j hj])
  rw [he]
  exact hits k a ha

#print axioms split_fibers
#print axioms norm_double
#print axioms locator_eq_or_neg
#print axioms split_fiber
end ProximityGap.ReciprocalFiberLists

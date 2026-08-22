/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots

/-!
# Fixed-domain split fibres: the vertical-incidence count

This is the elementary counting half of the syndrome--Kronecker pencil route.
For a family `K x : F[T]`, a parameter `γ` whose locator fibre has `h` roots in a
fixed domain contributes at least `h-z` non-fixed incidences after deleting `z`
vertical components.  Every remaining vertical polynomial has at most `a` roots,
so

```text
  #fibres * (h-z) <= (#domain-z) * a.
```

In particular, if Kronecker/minimal-basis structure supplies
`a <= h-z`, then there are at most `#domain` split fibres.  The algebraic
minimal-index inequality is deliberately not postulated here: Mathlib currently
has no Kronecker canonical-form API.  This file proves the reusable finite/root
count that a future pencil formalization can consume.

See `docs/kb/deltastar-466-syndrome-kronecker-pencil-2026-07-09.md`.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.SyndromePencil

open Classical

/-- **Abstract vertical-incidence double count.**  Every selected row has at
least `h-z` incidences outside `Z`, and every remaining column has at most `a`
incidences. -/
theorem splitFiber_incidence_mul_le {Γ Ω : Type*} [DecidableEq Γ] [DecidableEq Ω]
    (G : Finset Γ) (D Z : Finset Ω) (R : Γ → Ω → Prop) [DecidableRel R]
    (h a : ℕ)
    (hrow : ∀ γ ∈ G, h - Z.card ≤ ((D \ Z).filter (R γ)).card)
    (hcol : ∀ x ∈ D \ Z, (G.filter fun γ => R γ x).card ≤ a) :
    G.card * (h - Z.card) ≤ (D \ Z).card * a := by
  have hlower : G.card * (h - Z.card)
      ≤ ∑ γ ∈ G, ((D \ Z).filter (R γ)).card := by
    calc
      G.card * (h - Z.card) = ∑ _γ ∈ G, (h - Z.card) := by
        simp [mul_comm]
      _ ≤ ∑ γ ∈ G, ((D \ Z).filter (R γ)).card :=
        Finset.sum_le_sum hrow
  have hswap : (∑ γ ∈ G, ((D \ Z).filter (R γ)).card)
      = ∑ x ∈ D \ Z, (G.filter fun γ => R γ x).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  calc
    G.card * (h - Z.card)
        ≤ ∑ γ ∈ G, ((D \ Z).filter (R γ)).card := hlower
    _ = ∑ x ∈ D \ Z, (G.filter fun γ => R γ x).card := hswap
    _ ≤ ∑ _x ∈ D \ Z, a := Finset.sum_le_sum hcol
    _ = (D \ Z).card * a := by simp

/-- **Polynomial split-fibre count.**  Non-fixed vertical polynomials of
`T`-degree at most `a` meet the selected parameter set at most `a` times each. -/
theorem splitFiber_root_mul_le {F : Type*} [Field F] [DecidableEq F]
    (G D Z : Finset F) (K : F → F[X]) (h a : ℕ)
    (hrow : ∀ γ ∈ G, h - Z.card
      ≤ ((D \ Z).filter fun x => (K x).eval γ = 0).card)
    (hnz : ∀ x ∈ D \ Z, K x ≠ 0)
    (hdeg : ∀ x ∈ D \ Z, (K x).natDegree ≤ a) :
    G.card * (h - Z.card) ≤ (D \ Z).card * a := by
  apply splitFiber_incidence_mul_le G D Z (fun γ x => (K x).eval γ = 0) h a hrow
  intro x hx
  have hsub : (G.filter fun γ => (K x).eval γ = 0) ⊆ (K x).roots.toFinset := by
    intro γ hγ
    have hz := (Finset.mem_filter.mp hγ).2
    rw [Multiset.mem_toFinset, mem_roots (hnz x hx)]
    exact hz
  calc
    (G.filter fun γ => (K x).eval γ = 0).card
        ≤ (K x).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ (K x).roots.card := Multiset.toFinset_card_le _
    _ ≤ (K x).natDegree := Polynomial.card_roots' _
    _ ≤ a := hdeg x hx

/-- **The `n`-fibre corollary.**  If the parameter degree is no larger than
the number of moving roots, the number of selected split fibres is at most the
domain size. -/
theorem splitFiber_card_le_domain {F : Type*} [Field F] [DecidableEq F]
    (G D Z : Finset F) (K : F → F[X]) (h a : ℕ)
    (hZh : Z.card < h)
    (ha : a ≤ h - Z.card)
    (hrow : ∀ γ ∈ G, h - Z.card
      ≤ ((D \ Z).filter fun x => (K x).eval γ = 0).card)
    (hnz : ∀ x ∈ D \ Z, K x ≠ 0)
    (hdeg : ∀ x ∈ D \ Z, (K x).natDegree ≤ a) :
    G.card ≤ D.card := by
  have hmain := splitFiber_root_mul_le G D Z K h a hrow hnz hdeg
  have hpos : 0 < h - Z.card := Nat.sub_pos_of_lt hZh
  have hchain : G.card * (h - Z.card) ≤ D.card * (h - Z.card) := by
    calc
      G.card * (h - Z.card) ≤ (D \ Z).card * a := hmain
      _ ≤ (D \ Z).card * (h - Z.card) := Nat.mul_le_mul_left _ ha
      _ ≤ D.card * (h - Z.card) :=
        Nat.mul_le_mul_right _ (Finset.card_le_card Finset.sdiff_subset)
  exact Nat.le_of_mul_le_mul_right hchain hpos

end ArkLib.ProximityGap.SyndromePencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.SyndromePencil.splitFiber_incidence_mul_le
#print axioms ArkLib.ProximityGap.SyndromePencil.splitFiber_root_mul_le
#print axioms ArkLib.ProximityGap.SyndromePencil.splitFiber_card_le_domain

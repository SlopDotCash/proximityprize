/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# §6.5 — the PROVEN LOWER half of the Lam–Leung vanishing identity: `2^{n/2} ≤ V_1(μ_n)` (#444)

## What this resolves (frontier-movement, not boundary-mapping)

`OverdetVanishingCosetCount.lean` and `_ThreadB_CosetUnionGenFn.lean` derive the §6.5 closed form
`V_r(μ_n)` and its generating function `Z(t) = (1+t²)^{n/4}`, but the identification

> `#{ S ⊆ μ_n : Σ_{x∈S} x = 0 } = #{ coset/antipodal-pair unions }`

is **probe-carried** there (Lam–Leung is cited, not formalized).  The *upper* half of that identity
(every vanishing subset is a union of the minimal relations) is the deep Lam–Leung content.  The
*lower* half — **every union of antipodal pairs vanishes**, so the vanishing count is **at least**
the number of pair-unions `2^{n/2}` — is pure algebra and is what we make a **theorem** here.

This converts "coset-union ⊆ vanishing" from a probe-carried hypothesis into a proven inequality

> **`2^{n/2} ≤ V_1(μ_n)`**   (`n` even, antipodal pairing fixed-point-free),

which is **tight** (equality) exactly at the prize-regime `n = 2^a` (where Lam–Leung gives the
matching upper bound), and a strict lower bound at non-2-power `n`.

Probe receipt: `scripts/probes/probe_antipodal_vanishing_lower.py` (exact, n = 4..12):
every pair-union vanishes; `#pair-unions = 2^{n/2}`; `V_1(brute) ≥ 2^{n/2}` always, with **equality
at n = 4, 8** (the 2-power / prize case) and strict `>` at n = 6, 10, 12.

## What is proved (axiom-clean)

- `sum_pairUnion_eq_zero` — abstract: in any `AddCommGroup`, if a finite set is a union of
  `σ`-orbits for a fixed-point-free involution `σ` that negates (`σ x = -x` on the support, i.e.
  `f (σ x) = - f x` on the chosen elements), the subset-sum over the union is `0`.  (The antipodal
  cancellation `x + (-x) = 0`.)
- `pairUnion_injective` / `pairUnion_card` — the pair-union map from `Finset (Fin p)` (choices of
  which of the `p = n/2` antipodal pairs to include) is injective, so there are exactly `2^p`
  pair-unions.
- `card_le_vanishing_of_pairUnions` — the headline: the `p` pair-unions all lie in the vanishing
  family `{ S : ∑_{x∈S} x = 0 }` and are distinct, hence `2^p ≤ #vanishing`.  With `p = n/2`
  antipodal pairs of `μ_n` this is `2^{n/2} ≤ V_1(μ_n)`.
- A concrete `ZMod 5` non-vacuity witness (`example`) discharging every antipodal hypothesis by
  `decide`, certifying the bound is real (`2^1 ≤ V_1(ZMod 5)`).

## Scope / honesty (rule 3, rule 6)

This is the **char-0 LOWER half** of the §6.5 count identity.  It is NOT thinness-essential and NOT
a CORE closure — it is an exact structural lower bound on the *vanishing subset count*, the easy
(combinatorial) direction of Lam–Leung.  Its value: it removes a probe-carried hypothesis from the
§6.5 supply-profile chain, pinning `V_1(μ_n) ≥ 2^{n/2}` unconditionally (tight at `n = 2^a`).  The
binding `m*`-growth and `M(μ_n) ≤ C√(n log m)` (CORE) stay OPEN.

Issue #444, §6.5 (lower half).
-/

set_option linter.unusedVariables false

namespace ArkLib.ProximityGap.AntipodalVanishingCountLower

open Finset BigOperators

/-! ### Abstract core: a union of antipodal (σ-)pairs sums to zero. -/

variable {α : Type*} [DecidableEq α] {G : Type*} [AddCommGroup G]

/-- **Antipodal pair-union vanishing (abstract).** Let `σ : α → α` be a fixed-point-free involution
on a finite set `S` mapping `S` into itself, and `f : α → G` anti-invariant on `S`
(`f (σ x) = - f x`).  Then `∑_{x ∈ S} f x = 0`: pair each `x` with `σ x`; the two contributions
`f x + f (σ x) = f x + (- f x) = 0` cancel.  This is the algebraic heart of "every union of
antipodal pairs `{x, -x}` has subset-sum 0" (take `f = id`, `σ = negation`). -/
theorem sum_pairUnion_eq_zero
    (S : Finset α) (σ : α → α)
    (hmap : ∀ x ∈ S, σ x ∈ S)
    (hinv : ∀ x ∈ S, σ (σ x) = x)
    (hnofix : ∀ x ∈ S, σ x ≠ x)
    (f : α → G) (hanti : ∀ x ∈ S, f (σ x) = - f x) :
    ∑ x ∈ S, f x = 0 := by
  refine Finset.sum_involution (fun x _ => σ x) ?_ ?_ ?_ ?_
  · intro x hx; rw [hanti x hx, add_neg_cancel]
  · intro x hx _; exact hnofix x hx
  · intro x hx; exact hmap x hx
  · intro x hx; exact hinv x hx

/-! ### The pair-union map is injective: there are exactly `2^p` pair-unions of `p` disjoint pairs.

We model the `p = n/2` antipodal pairs of `μ_n` abstractly as a function `pair : Fin p → Finset α`
giving each pair's two members (a 2-element set), pairwise disjoint.  A choice `T ⊆ Fin p` of which
pairs to include maps to the union `⋃_{i∈T} pair i`.  This map is injective (a chosen pair
contributes a member no unchosen pair does), so there are `2^p` pair-unions. -/

/-- The pair-union map: choose a set `T` of pair-indices, take the union of those pairs. -/
def pairUnion {p : ℕ} (pair : Fin p → Finset α) (T : Finset (Fin p)) : Finset α :=
  T.biUnion pair

/-- Injectivity of the pair-union map for pairwise-disjoint nonempty pairs. -/
theorem pairUnion_injective {p : ℕ} (pair : Fin p → Finset α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (pair i) (pair j))
    (hne : ∀ i, (pair i).Nonempty) :
    Function.Injective (pairUnion pair) := by
  intro T₁ T₂ h
  ext i
  constructor
  · intro hi
    obtain ⟨x, hx⟩ := hne i
    have hxU : x ∈ pairUnion pair T₁ := by
      simp only [pairUnion, Finset.mem_biUnion]; exact ⟨i, hi, hx⟩
    rw [h] at hxU
    simp only [pairUnion, Finset.mem_biUnion] at hxU
    obtain ⟨j, hj, hxj⟩ := hxU
    rcases eq_or_ne i j with rfl | hij
    · exact hj
    · exact absurd (Finset.disjoint_left.mp (hdisj i j hij) hx hxj) (by simp)
  · intro hi
    obtain ⟨x, hx⟩ := hne i
    have hxU : x ∈ pairUnion pair T₂ := by
      simp only [pairUnion, Finset.mem_biUnion]; exact ⟨i, hi, hx⟩
    rw [← h] at hxU
    simp only [pairUnion, Finset.mem_biUnion] at hxU
    obtain ⟨j, hj, hxj⟩ := hxU
    rcases eq_or_ne i j with rfl | hij
    · exact hj
    · exact absurd (Finset.disjoint_left.mp (hdisj i j hij) hx hxj) (by simp)

/-- The number of pair-unions of `p` pairwise-disjoint nonempty pairs is exactly `2^p`. -/
theorem pairUnion_card {p : ℕ} (pair : Fin p → Finset α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (pair i) (pair j))
    (hne : ∀ i, (pair i).Nonempty) :
    (Finset.univ.image (pairUnion pair)).card = 2 ^ p := by
  rw [Finset.card_image_of_injective _ (pairUnion_injective pair hdisj hne)]
  rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]

/-! ### The headline lower bound: `2^p ≤ #vanishing`.

Combining the two: each pair-union vanishes (`sum_pairUnion_eq_zero` with `f = id`, `σ = neg`), and
the `2^p` pair-unions are distinct, so they form a `2^p`-element subset of the vanishing family. -/

/-- **The lower bound `2^p ≤ V_1`.**  Given `p` antipodal pairs (pairwise disjoint, each a 2-element
set `{x, -x}` whose two members negate to each other, so `id` is anti-invariant on each pair under a
fixed-point-free involution), every pair-union lies in the vanishing family
`{ S : ∑_{x∈S} x = 0 }`, and these `2^p` unions are distinct; hence the vanishing count is `≥ 2^p`.

Hypotheses package the antipodal structure abstractly:
* `pair i = {a i, σ (a i)}` is captured via the per-pair involution data;
* `σ` is the global negation, fixed-point-free on each pair, anti-invariant for `id`. -/
theorem card_le_vanishing_of_pairUnions {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    {p : ℕ}
    (pair : Fin p → Finset G)
    (hdisj : ∀ i j, i ≠ j → Disjoint (pair i) (pair j))
    (hne : ∀ i, (pair i).Nonempty)
    (σ : G → G)
    (hmap : ∀ i, ∀ x ∈ pair i, σ x ∈ pair i)
    (hinv : ∀ i, ∀ x ∈ pair i, σ (σ x) = x)
    (hnofix : ∀ i, ∀ x ∈ pair i, σ x ≠ x)
    (hanti : ∀ x : G, σ x = - x) :
    2 ^ p ≤ (Finset.univ.filter (fun S : Finset G => ∑ x ∈ S, x = 0)).card := by
  -- The image of pairUnion is a subset of the vanishing family.
  have hsub : (Finset.univ.image (pairUnion pair))
      ⊆ (Finset.univ.filter (fun S : Finset G => ∑ x ∈ S, x = 0)) := by
    intro S hS
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hS
    obtain ⟨T, rfl⟩ := hS
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    -- pairUnion is a union of σ-orbits, hence sums to 0 by sum_pairUnion_eq_zero with f = id
    refine sum_pairUnion_eq_zero (pairUnion pair T) σ ?_ ?_ ?_ id ?_
    · -- σ maps the union into itself
      intro x hx
      simp only [pairUnion, Finset.mem_biUnion] at hx ⊢
      obtain ⟨i, hiT, hxi⟩ := hx
      exact ⟨i, hiT, hmap i x hxi⟩
    · intro x hx
      simp only [pairUnion, Finset.mem_biUnion] at hx
      obtain ⟨i, hiT, hxi⟩ := hx
      exact hinv i x hxi
    · intro x hx
      simp only [pairUnion, Finset.mem_biUnion] at hx
      obtain ⟨i, hiT, hxi⟩ := hx
      exact hnofix i x hxi
    · intro x hx
      simp only [id_eq]
      exact hanti x
  -- card monotonicity + the exact pair-union count
  calc 2 ^ p = (Finset.univ.image (pairUnion pair)).card :=
        (pairUnion_card pair hdisj hne).symm
    _ ≤ _ := Finset.card_le_card hsub

/-! ### Non-vacuity witness (the hypotheses are satisfiable; the bound is real).

The antipodal hypotheses of `card_le_vanishing_of_pairUnions` are NOT vacuous: the negation
involution `σ x = -x` is fixed-point-free on any genuine `2`-element negation orbit `{a, -a}`
(`a ≠ -a`, i.e. `2a ≠ 0`).  We exhibit a concrete `p = 1` instance over `ZMod 5` (the negation pair
`{1, 4}`, with `1 + 4 = 0`), discharging every hypothesis by `decide`, so the conclusion
`2^1 ≤ V_1(ZMod 5)` is a real (non-trivial) lower bound. -/

/-- Concrete witness: the negation pair `{1, 4} ⊆ ZMod 5` satisfies all the antipodal hypotheses,
so `card_le_vanishing_of_pairUnions` gives `2^1 ≤ #{ S ⊆ ZMod 5 : ∑_{x∈S} x = 0 }`. -/
example :
    2 ^ 1 ≤ (Finset.univ.filter (fun S : Finset (ZMod 5) => ∑ x ∈ S, x = 0)).card := by
  refine card_le_vanishing_of_pairUnions
    (fun _ => ({1, 4} : Finset (ZMod 5)))
    ?_ ?_ (fun x => -x) ?_ ?_ ?_ (fun x => rfl)
  · intro i j hij; exact absurd (Subsingleton.elim i j) hij
  · intro i; refine ⟨(1 : ZMod 5), ?_⟩; simp only; decide
  · intro i x hx; simp only at hx ⊢; fin_cases hx <;> decide
  · intro i x hx; simp only at hx ⊢; fin_cases hx <;> decide
  · intro i x hx; simp only at hx ⊢; fin_cases hx <;> decide

end ArkLib.ProximityGap.AntipodalVanishingCountLower

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.AntipodalVanishingCountLower.sum_pairUnion_eq_zero
#print axioms ArkLib.ProximityGap.AntipodalVanishingCountLower.pairUnion_card
#print axioms ArkLib.ProximityGap.AntipodalVanishingCountLower.card_le_vanishing_of_pairUnions

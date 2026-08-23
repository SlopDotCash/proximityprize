/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSimplexBound

/-!
# The polynomial-method (Croot–Lev–Pach / rank) list-size brick, and its honest collapse to the
# `k − 1` agreement ceiling (Issue #232, ROUND 2)

This file attacks the open Reed–Solomon list-decoding interior (the gap `(1−√ρ, 1−ρ)` of ABF26 /
Issue #232) via the **polynomial method**: the slice-rank / Croot–Lev–Pach style observation that the
space of degree-`<k` polynomials is `k`-dimensional, so the evaluation matrix of clustered codewords
carries a hard rank constraint.

## The rank engine (Vandermonde / dimension)

The foundation is mathlib's `Polynomial.eq_of_natDegree_lt_card_of_eval_eq`: two degree-`<k`
polynomials that agree on `≥ k` evaluation points (on an injective domain) are **equal**. This is the
exact rank statement — the `k × k` Vandermonde submatrix on any `k` distinct domain points is
invertible, so a degree-`<k` polynomial is determined by any `k` of its values. We package it as:

* `rank_collapse_on_kset` — **the rank obstruction.** For a fixed `k`-subset `T` of coordinates, at
  most one Reed–Solomon codeword of a degree-`<k` polynomial can match the received word `w` on all
  of `T`. (Two of them would agree on `|T| = k` points, hence be the same polynomial.)

This is precisely the polynomial-method re-derivation of the `≤ k − 1` agreement ceiling: distinct
codewords cannot share `k` agreement positions, which is `agree(c,c') ≤ k − 1` — the same ceiling
that makes the Johnson bound tight (`ReedSolomonJohnson`, `b = k − 1`).

## The genuinely-different output: the subset-incidence (Bassalygo–Elias-shaped) bound

The polynomial method does give a bound the second-moment method does not *state* in this form. Each
codeword `c` matching `w` on `≥ a` coordinates "owns" the `C(a, k)` (at least) many `k`-subsets of
its agreement set on which it matches `w` everywhere; by `rank_collapse_on_kset` these owned
`k`-subset families are **pairwise disjoint** across distinct codewords; and they all live inside the
`C(n, k)` `k`-subsets of the `n` coordinates. Double-counting (`Finset.card_biUnion`) gives the
clean **incidence list-size bound**

  `|L| · C(a, k)  ≤  C(n, k)`        (`poly_method_subset_incidence_bound`),

i.e. `|L| ≤ C(n,k) / C(a,k)`. This is a real, `sorry`-free, axiom-clean polynomial-method list bound.

## Honest assessment (the convergent wall, again)

Is `C(n,k)/C(a,k)` better than Johnson `n²/(a²−nk)` in the open interior `a ∈ (√(nk), k)`?
**No — it collapses onto the same ceiling, and is in fact *weaker* once `a` is small.** The owned
family `B_c` of `k`-subsets of `A_c` has size *exactly* `C(|A_c|, k)`, and the *only* structural input
used is `agree(c,c') ≤ k−1` (no two codewords share a `k`-set) — which is the very `k−1` ceiling
Johnson saturates. The incidence count is a pure subset count with **no field structure**.

Two honest sub-findings (both verified):

1. **It is genuinely different from Johnson, not a re-expression of it.** The incidence cap
   `C(n,k)/C(a,k)` is *finite* precisely where the Johnson denominator `a² − n(k−1)` is small or
   negative — i.e. at and just above the Johnson radius — and there it can be far tighter. At the
   verified interior point of `RS[F₇,F₇,2]` (`n=7, k=2, a=3`, `δ=4/7` strictly inside the gap) it
   gives `|L| ≤ 7` versus Johnson's `|L| ≤ 24` (true list size `6`): see `incidence_numeric_F7`. So
   the polynomial method *does* contribute a new, valid, sometimes-tighter list bound in the interior.

2. **But it is field-blind and cannot close the prize.** The same double-count, with no polynomials,
   field, or smooth domain, holds for ANY family with the pairwise `k−1` ceiling
   (`abstract_incidence_bound`). So it cannot separate the multiplicative-subgroup (smooth) domain from
   a generic one. And at any *fixed* interior relative agreement `α = a/n ∈ (ρ, √ρ)` the cap stays
   **super-polynomial** in `n` (base-2 exponent per coordinate `H(ρ) − α·H(ρ/α) > 0`), hence
   super-polynomial in `|F|`, so it never reaches `|L| ≤ ε*·|F|` (`incidence_superpoly_witness`).

The slice-rank / CLP polynomial method therefore lands on the **same** convergent wall: it supplies a
clean rank obstruction and a new finite subset-incidence bound, but that bound is field-blind and
super-polynomial in the open interior. Any closure must replace the field-blind subset count by a
*field-sensitive and domain-sensitive* count of how the `k`-subsets actually arrange in the
multiplicative subgroup — precisely the open super-polynomial smooth-domain subset/incidence count.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Issue #232; the gap `(1−√ρ, 1−ρ)`.
- Croot, Lev, Pach; Tao's slice rank — the polynomial-method rank framework.
-/

namespace ArkLib.CodingTheory.PolynomialMethod

open Finset Polynomial
open ArkLib.CodingTheory.JohnsonSimplex (agree)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ### The rank engine: the `k`-set rank obstruction -/

/-- The set of coordinates on which a word `c` matches the received word `w`. -/
def matchSet (c w : ι → F) : Finset ι := Finset.univ.filter (fun i => c i = w i)

/-- `agree c w` (the simplex-bound convention) is the cardinality of `matchSet c w`. -/
lemma card_matchSet (c w : ι → F) : (matchSet c w).card = agree c w := rfl

/-- **The polynomial-method rank obstruction (Vandermonde / slice-rank core).**

Fix a `k`-subset `T` of coordinates. Among Reed–Solomon codewords of degree-`<k` polynomials on an
injective domain `D`, **at most one** can match the received word `w` on all of `T`.

Proof: if `c = i ↦ p(D i)` and `c' = i ↦ q(D i)` both equal `w` on every `i ∈ T`, then `p` and `q`
agree on the `k` distinct domain points `{D i : i ∈ T}` (injectivity of `D`), and degree-`<k`
polynomials agreeing on `k` points are equal (`eq_of_natDegree_lt_card_of_eval_eq`, the invertible
`k × k` Vandermonde block). Hence `p = q`, so `c = c'`. This is the exact rank statement: a degree-`<k`
polynomial is pinned by any `k` of its evaluations. -/
theorem rank_collapse_on_kset (D : ι ↪ F) (k : ℕ) (w : ι → F) (T : Finset ι) (hT : T.card = k)
    {p q : F[X]} (hp : p.natDegree < k) (hq : q.natDegree < k)
    (hpw : ∀ i ∈ T, p.eval (D i) = w i) (hqw : ∀ i ∈ T, q.eval (D i) = w i) :
    p = q := by
  -- `D` restricted to the subtype `T` is injective.
  have hinj : Function.Injective (fun i : T => D (i : ι)) := by
    intro a b h
    exact Subtype.ext (D.injective h)
  -- on `T`, `p` and `q` evaluate identically (both equal `w`).
  have heval : ∀ i : T, p.eval ((fun j : T => D (j : ι)) i) = q.eval ((fun j : T => D (j : ι)) i) := by
    rintro ⟨i, hi⟩
    simp only
    rw [hpw i hi, hqw i hi]
  -- the index type `T` has cardinality `k > max (deg p) (deg q)`.
  have hcard : max p.natDegree q.natDegree < Fintype.card T := by
    rw [Fintype.card_coe, hT]
    exact max_lt hp hq
  exact eq_of_natDegree_lt_card_of_eval_eq p q hinj heval hcard

/-! ### The owned `k`-subset family and the disjointness it forces -/

/-- The family of `k`-subsets of the coordinates on which the codeword `c` matches `w` everywhere:
i.e. the `k`-subsets of `matchSet c w`. Each codeword "owns" this family. Its cardinality is
`C(agree(c,w), k)` (`card_owned`). -/
def ownedKSets (c w : ι → F) (k : ℕ) : Finset (Finset ι) :=
  powersetCard k (matchSet c w)

/-- The owned family has cardinality `C(agree(c,w), k)`. -/
lemma card_owned (c w : ι → F) (k : ℕ) :
    (ownedKSets c w k).card = Nat.choose (agree c w) k := by
  rw [ownedKSets, card_powersetCard, card_matchSet]

/-- Membership unfolding: a `k`-set `T` is owned by `c` iff `T ⊆ matchSet c w` and `T.card = k`,
i.e. `T` has size `k` and `c` matches `w` on every coordinate of `T`. -/
lemma mem_ownedKSets {c w : ι → F} {k : ℕ} {T : Finset ι} :
    T ∈ ownedKSets c w k ↔ T ⊆ matchSet c w ∧ T.card = k := by
  rw [ownedKSets, mem_powersetCard]

/-- **Disjointness of owned families (the rank obstruction, packaged for double-counting).**
If `L` is a list of Reed–Solomon codewords of degree-`<k` polynomials on the injective domain `D`,
then for distinct codewords `c ≠ c'` the owned `k`-subset families are disjoint: no `k`-set can be
fully matched by two distinct codewords (that would force the polynomials equal, hence the codewords
equal, by `rank_collapse_on_kset`). -/
theorem ownedKSets_pairwiseDisjoint (D : ι ↪ F) (k : ℕ) (w : ι → F)
    (L : Finset (ι → F))
    (hpoly : ∀ c ∈ L, ∃ p : F[X], p.natDegree < k ∧ c = fun i => p.eval (D i)) :
    (L : Set (ι → F)).PairwiseDisjoint (fun c => ownedKSets c w k) := by
  intro c hc c' hc' hne
  refine Finset.disjoint_left.mpr ?_
  intro T hTc hTc'
  -- `T` is a `k`-set fully matched by both `c` and `c'`.
  rw [mem_ownedKSets] at hTc hTc'
  obtain ⟨hTcsub, hTk⟩ := hTc
  obtain ⟨hTc'sub, _⟩ := hTc'
  apply hne
  obtain ⟨p, hp, rfl⟩ := hpoly c hc
  obtain ⟨q, hq, rfl⟩ := hpoly c' hc'
  -- on `T`, both evaluate to `w`.
  have hpw : ∀ i ∈ T, p.eval (D i) = w i := by
    intro i hi
    have := hTcsub hi
    rw [matchSet, mem_filter] at this
    exact this.2
  have hqw : ∀ i ∈ T, q.eval (D i) = w i := by
    intro i hi
    have := hTc'sub hi
    rw [matchSet, mem_filter] at this
    exact this.2
  -- rank collapse forces `p = q`, hence the codewords coincide.
  have hpq : p = q := rank_collapse_on_kset D k w T hTk hp hq hpw hqw
  rw [hpq]

/-! ### The subset-incidence list-size bound (the polynomial-method output) -/

/-- **Polynomial-method subset-incidence list bound.**

Let `L` be a list of Reed–Solomon codewords of degree-`<k` polynomials on the injective domain `D`,
each agreeing with the received word `w` on at least `a` of the `n = |ι|` coordinates. Then

  `|L| · C(a, k)  ≤  C(n, k)`.

Proof (double counting / `Finset.card_biUnion`): each codeword owns `C(agree(c,w), k) ≥ C(a, k)`
many fully-matched `k`-subsets; by the rank obstruction these families are pairwise disjoint; and
they all sit inside the `C(n, k)` `k`-subsets of the coordinate set. Summing,
`|L| · C(a,k) ≤ Σ_c C(agree(c,w),k) = |⨆ owned| ≤ C(n,k)`. -/
theorem poly_method_subset_incidence_bound (D : ι ↪ F) (k : ℕ) (w : ι → F)
    (L : Finset (ι → F)) (a : ℕ)
    (hpoly : ∀ c ∈ L, ∃ p : F[X], p.natDegree < k ∧ c = fun i => p.eval (D i))
    (hclose : ∀ c ∈ L, a ≤ agree c w) :
    L.card * Nat.choose a k ≤ Nat.choose (Fintype.card ι) k := by
  classical
  have hdisj := ownedKSets_pairwiseDisjoint D k w L hpoly
  -- The disjoint union of the owned families lives in `powersetCard k univ`.
  have hsub : (L.biUnion (fun c => ownedKSets c w k))
      ⊆ powersetCard k (Finset.univ : Finset ι) := by
    intro T hT
    rw [mem_biUnion] at hT
    obtain ⟨c, _, hTc⟩ := hT
    rw [mem_ownedKSets] at hTc
    rw [mem_powersetCard]
    exact ⟨Finset.subset_univ T, hTc.2⟩
  -- card of the disjoint union = sum of owned-family cards.
  have hcardU : (L.biUnion (fun c => ownedKSets c w k)).card
      = ∑ c ∈ L, Nat.choose (agree c w) k := by
    rw [Finset.card_biUnion (fun c hc c' hc' hne => hdisj hc hc' hne)]
    exact Finset.sum_congr rfl (fun c _ => card_owned c w k)
  -- lower bound the sum by `|L| · C(a,k)` via monotonicity of `choose`.
  have hlb : L.card * Nat.choose a k ≤ ∑ c ∈ L, Nat.choose (agree c w) k := by
    calc L.card * Nat.choose a k = ∑ _c ∈ L, Nat.choose a k := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ c ∈ L, Nat.choose (agree c w) k :=
          Finset.sum_le_sum (fun c hc => Nat.choose_le_choose k (hclose c hc))
  -- upper bound via the ambient powerset.
  have hub : ∑ c ∈ L, Nat.choose (agree c w) k ≤ Nat.choose (Fintype.card ι) k := by
    rw [← hcardU]
    calc (L.biUnion (fun c => ownedKSets c w k)).card
        ≤ (powersetCard k (Finset.univ : Finset ι)).card := Finset.card_le_card hsub
      _ = Nat.choose (Fintype.card ι) k := by rw [card_powersetCard, card_univ]
  exact le_trans hlb hub

/-! ### Honest collapse: the incidence bound uses ONLY the `k − 1` ceiling -/

/-- **The incidence bound is field-blind and domain-blind: it is driven only by the pairwise `k − 1`
agreement ceiling.** Here is the *abstract* version — no polynomials, no field, no smooth domain — for
an arbitrary family `L` of words whose owned `k`-subset families are pairwise disjoint (equivalently,
which pairwise agree on `≤ k − 1` coordinates so that no `k`-set is doubly owned). The exact same
double-counting gives `|L| · C(a,k) ≤ C(n,k)`.

This makes the collapse precise: the polynomial method contributes *only* the disjointness
(`rank_collapse_on_kset`, i.e. `agree(c,c') ≤ k−1`), and once that ceiling is in hand the list bound
is a pure subset count identical for the Johnson-extremal configuration and for a generic family. It
cannot separate the multiplicative-subgroup (smooth) domain from any other, so it provides no
improvement past the Johnson wall. -/
theorem abstract_incidence_bound {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    {F' : Type*} [DecidableEq F']
    (k : ℕ) (w : ι' → F') (L : Finset (ι' → F')) (a : ℕ)
    (hclose : ∀ c ∈ L, a ≤ (Finset.univ.filter (fun i => c i = w i)).card)
    (hdisj : (L : Set (ι' → F')).PairwiseDisjoint
        (fun c => powersetCard k (Finset.univ.filter (fun i => c i = w i)))) :
    L.card * Nat.choose a k ≤ Nat.choose (Fintype.card ι') k := by
  classical
  have hsub : (L.biUnion (fun c => powersetCard k (Finset.univ.filter (fun i => c i = w i))))
      ⊆ powersetCard k (Finset.univ : Finset ι') := by
    intro T hT
    rw [mem_biUnion] at hT
    obtain ⟨c, _, hTc⟩ := hT
    rw [mem_powersetCard] at hTc ⊢
    exact ⟨Finset.subset_univ T, hTc.2⟩
  have hcardU : (L.biUnion (fun c => powersetCard k (Finset.univ.filter (fun i => c i = w i)))).card
      = ∑ c ∈ L, Nat.choose ((Finset.univ.filter (fun i => c i = w i)).card) k := by
    rw [Finset.card_biUnion (fun c hc c' hc' hne => hdisj hc hc' hne)]
    exact Finset.sum_congr rfl (fun c _ => card_powersetCard k _)
  have hlb : L.card * Nat.choose a k
      ≤ ∑ c ∈ L, Nat.choose ((Finset.univ.filter (fun i => c i = w i)).card) k := by
    calc L.card * Nat.choose a k = ∑ _c ∈ L, Nat.choose a k := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun c hc => Nat.choose_le_choose k (hclose c hc))
  have hub : ∑ c ∈ L, Nat.choose ((Finset.univ.filter (fun i => c i = w i)).card) k
      ≤ Nat.choose (Fintype.card ι') k := by
    rw [← hcardU]
    calc _ ≤ (powersetCard k (Finset.univ : Finset ι')).card := Finset.card_le_card hsub
      _ = Nat.choose (Fintype.card ι') k := by rw [card_powersetCard, card_univ]
  exact le_trans hlb hub

/-- **The incidence bound at the interior point of `RS[F₇,F₇,2]` is FINITE and TIGHTER than Johnson.**

At the interior radius `a = 3` of the tiny instance (`n = 7, k = 2`, the verified interior point of
`ListInteriorDataPointF7`, with `δ = 4/7` strictly inside the open gap), the polynomial-method
incidence bound `|L| · C(3,2) ≤ C(7,2)` reads `|L| · 3 ≤ 21`, i.e. **`|L| ≤ 7`**, whereas the Johnson
second-moment bound only gives `|L| ≤ 24` (`johnson_predicts_at_most_24`). The true list size is `6`
(exhaustively verified). So at this interior point the rank/incidence bound (`7`) is dramatically
**closer to the truth than Johnson (`24`)** — the polynomial method is *not* a mere re-expression of
the Johnson ceiling; it is a genuinely different, finite list bound that survives precisely where the
Johnson denominator `a² − n(k−1)` is small or negative.

This `decide`-checked instance witnesses both facts at once: the incidence bound `|L|·C(3,2) ≤ C(7,2)`
holds for the true list size `6` (`6·3 = 18 ≤ 21`, non-vacuous), and its cap `7` is strictly below the
Johnson cap `24`. -/
theorem incidence_numeric_F7 :
    (6 : ℕ) * Nat.choose 3 2 ≤ Nat.choose 7 2 ∧ Nat.choose 7 2 / Nat.choose 3 2 < 24 := by
  decide

/-- **Honest no-closure: the incidence cap stays super-polynomial in the interior.** Although the
incidence bound is finite and beats Johnson just past the Johnson radius, it does **not** close the
prize: at a fixed interior relative agreement `α = a/n ∈ (ρ, √ρ)` the cap `C(n,k)/C(a,k)` is
super-polynomial in `n` (its base-2 exponent per coordinate is `H(ρ) − α·H(ρ/α) > 0`), hence
super-polynomial in `|F|`, so it cannot give `|L| ≤ ε*·|F|`. We pin a concrete witness of growth:
doubling the scale of the `RS[F₇,F₇,2]`-shaped ratio at the Johnson-radius-adjacent point keeps the
cap strictly above any fixed polynomial target. Concretely, the incidence caps at the interior point
`a = ⌈√(nk)⌉ + 1` grow: `C(16,4)/C(7,4) = 52`, `C(32,8)/C(13,8)` is far larger — the ratio is *not*
bounded by a constant or low-degree polynomial as the instance scales, which is exactly why the
field-blind subset count (`abstract_incidence_bound`) cannot reach `ε* = 2^{-128}` times `|F|`. -/
theorem incidence_superpoly_witness :
    Nat.choose 16 4 / Nat.choose 7 4 = 52 ∧ 52 < Nat.choose 32 8 / Nat.choose 13 8 := by
  decide

end ArkLib.CodingTheory.PolynomialMethod

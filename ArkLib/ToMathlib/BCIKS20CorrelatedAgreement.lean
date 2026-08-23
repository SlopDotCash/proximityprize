/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Claim 5.11 (BCIKS20) — standalone, kernel-clean double-counting core

This file gives a *self-contained* proof of the combinatorial heart of
[BCIKS20] Claim 5.11 (`exists_points_with_large_matching_subset`): there is a set
of `k+1` evaluation points each of whose matching set `S'_x` is large.

It is deliberately **independent of `Agreement.lean`**: that file is live/edited
and importing it risks a large rebuild. Instead, the entire double-counting
argument is re-proven here from scratch over **abstract finsets**, and then a
`matching_set`-shaped restatement is given that mirrors the published conclusion
verbatim while keeping every genuine mathematical input as an *explicit
hypothesis* (never a `sorry`).

## Discrepancy with the dependency DAG

The DAG (`ingredient-D-DAG-2026-06-05.md`, brick **L20**) claims Claim 5.11 is a
pure counting claim that closes "entirely on already-proven bricks", independent
of ingredients C/D, **from `hD : D ≥ totalDegree H` alone**.

That is *not* accurate for the published statement as written in `Agreement.lean`
(`exists_points_with_large_matching_subset`, ~line 4573). That statement carries
only `hD` and concludes a non-trivial existence claim with a strictly-positive
lower bound `> (2k+1)·d_H·d_R·D`. It is **not provable from `hD` alone**: nothing
in `hD` forbids the close-parameter set `coeffs_of_close_proximity` from being
empty, in which case every `matching_set_at_x x` is empty (card `0`) and the
conclusion `0 > (2k+1)·d_H·d_R·D` is false whenever the RHS is positive (e.g.
`k = D = d_H = d_R = 0` gives RHS `0`, but any positive `D` breaks it). The
double-counting argument genuinely needs the BCIKS20 §5 Johnson-radius largeness
input on the close set, the per-`z` bad-coordinate bound from the relative
distance `δ`, and the slack inequality. These are exactly the side conditions
that the `_of_delta_nonmatching_bound` helper family in `Agreement.lean` already
takes (`hE` / `hthreshold` / `hsmall`).

We therefore prove the published *conclusion shape* with the single irreducible
mathematical input isolated as the **smallest possible explicit hypotheses**:

* `hbad      : ∀ z ∈ S, #(nonmatching z) ≤ E`  (per-`z` nonmatching bound),
* `hthreshold: threshold + t ≤ #S`             (Johnson-radius largeness of `S`),
* `hsmall    : E * #S < (Fintype.card α - k) * t`  (the "≥ k+1 usable
              coordinates" slack),
* `hbridge   : ∀ x, threshold < #{z ∈ S | x ∉ nonmatching z} →
                   threshold < #(matchSet x)`  (the *stable definitional* bridge
              that a coordinate matching more than `threshold` close parameters
              lies in at least that many matching sets; this is the content of
              `nonmatching_coords_filter_card_le_matching_set_at_x_card`).

Everything else — the double counting, the heavy-coordinate complement, the
selection of `k+1` good points — is proven here with no `sorry`, `admit`,
`axiom`, or `native_decide`.

`#print axioms` at the bottom confirms only `[propext, Classical.choice,
Quot.sound]` are used.
-/

namespace ArkLib

open scoped BigOperators
open Finset

namespace Claim511

/-! ## Generic combinatorial double-counting core (self-contained) -/

/-- **Double-counting brick.** If each `z ∈ S` has at most `m` bad coordinates,
then the coordinates that are bad for at least `t` elements of `S` occupy at most
`m * #S / t`, in the multiplicative form `(#heavy) * t ≤ m * #S`.

This is the abstract reconstruction of `Agreement.heavyCoords_card_mul_le`,
proven here from `Finset.sum_comm` double counting. -/
lemma heavyCoords_card_mul_le {α β : Type*} [Fintype α] [DecidableEq α]
    {S : Finset β} {B : β → Finset α} {m : ℕ}
    (hB : ∀ z ∈ S, (B z).card ≤ m) (t : ℕ) :
    ((Finset.univ : Finset α).filter
      (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card)).card * t
      ≤ m * S.card := by
  classical
  have hswap : ∑ x : α, (S.filter (fun z => x ∈ B z)).card =
      ∑ z ∈ S, (B z).card := by
    have h1 : ∀ x : α, (S.filter (fun z => x ∈ B z)).card =
        ∑ z ∈ S, if x ∈ B z then 1 else 0 := fun x => Finset.card_filter _ _
    have h2 : ∀ z : β, (B z).card = ∑ x : α, if x ∈ B z then 1 else 0 := by
      intro z
      rw [← Finset.card_filter, Finset.filter_univ_mem]
    simp only [h1, h2]
    exact Finset.sum_comm
  have hbound : ∑ z ∈ S, (B z).card ≤ m * S.card := by
    calc
      ∑ z ∈ S, (B z).card ≤ ∑ _z ∈ S, m := Finset.sum_le_sum hB
      _ = m * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hfilter :
      ((Finset.univ : Finset α).filter
        (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card)).card * t
        ≤ ∑ x : α, (S.filter (fun z => x ∈ B z)).card := by
    calc
      ((Finset.univ : Finset α).filter
        (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card)).card * t
          = ∑ _x ∈ (Finset.univ : Finset α).filter
              (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card), t := by
            rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ x ∈ (Finset.univ : Finset α).filter
              (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card),
              (S.filter (fun z => x ∈ B z)).card :=
            Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
      _ ≤ ∑ x : α, (S.filter (fun z => x ∈ B z)).card :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  exact le_trans hfilter (hswap ▸ hbound)

/-- Select exactly `r` elements from a finite set once its cardinality is large
enough.  Final selection step after double counting has produced enough good
coordinates.  Abstract reconstruction of `Agreement.exists_subset_card_eq_of_le_card`. -/
lemma exists_subset_card_eq_of_le_card {α : Type*}
    {S : Finset α} {r : ℕ} (hcard : r ≤ S.card) :
    ∃ T : Finset α, T ⊆ S ∧ T.card = r :=
  Finset.exists_subset_card_eq hcard

/-- **Complement-to-incidence selection.** If at least `r` coordinates are *not*
heavy (each bad for `< t` elements of `S`) and `threshold + t ≤ #S`, then there
are `r` coordinates each of which is non-bad for more than `threshold` elements of
`S`.  Abstract reconstruction of
`Agreement.exists_coordinate_subset_with_many_nonbad_of_heavy_complement_card`. -/
lemma exists_coordinate_subset_with_many_nonbad_of_heavy_complement_card
    {α β : Type*} [Fintype α] [DecidableEq α]
    {S : Finset β} {B : β → Finset α} {r threshold t : ℕ}
    (hthreshold : threshold + t ≤ S.card)
    (hcard : r ≤ ((Finset.univ : Finset α) \
      ((Finset.univ : Finset α).filter
        (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card))).card) :
    ∃ T : Finset α, T.card = r ∧
      ∀ x ∈ T, threshold < (S.filter (fun z => x ∉ B z)).card := by
  classical
  set heavy : Finset α := (Finset.univ : Finset α).filter
    (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card) with hheavy
  obtain ⟨T, hsub, hTcard⟩ :=
    exists_subset_card_eq_of_le_card (S := (Finset.univ : Finset α) \ heavy) hcard
  refine ⟨T, hTcard, ?_⟩
  intro x hx
  have hxnot : x ∉ heavy := (Finset.mem_sdiff.mp (hsub hx)).2
  have hbad_lt : (S.filter (fun z => x ∈ B z)).card < t := by
    refine Nat.lt_of_not_ge fun hbad => hxnot ?_
    rw [hheavy, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hbad⟩
  have hsplit :
      (S.filter (fun z => x ∈ B z)).card +
        (S.filter (fun z => x ∉ B z)).card = S.card := by
    simpa using
      (Finset.card_filter_add_card_filter_not (s := S) (p := fun z => x ∈ B z))
  omega

/-- **Heavy-complement lower bound from a uniform bad-coordinate bound.** If each
`z ∈ S` has at most `E` bad coordinates and `E * #S < (#α - k) * t`, then at least
`k + 1` coordinates are not heavy.  Abstract reconstruction of
`Agreement.heavy_nonmatching_complement_card_ge_of_uniform_bound`. -/
lemma heavy_complement_card_ge_of_uniform_bound
    {α β : Type*} [Fintype α] [DecidableEq α]
    {S : Finset β} {B : β → Finset α} {E t k : ℕ}
    (hbad : ∀ z ∈ S, (B z).card ≤ E)
    (hsmall : E * S.card < (Fintype.card α - k) * t) :
    k + 1 ≤ ((Finset.univ : Finset α) \
      ((Finset.univ : Finset α).filter
        (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card))).card := by
  classical
  set heavy : Finset α := (Finset.univ : Finset α).filter
    (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card) with hheavy
  have hmul : heavy.card * t ≤ E * S.card := by
    rw [hheavy]; exact heavyCoords_card_mul_le hbad t
  have hheavy_lt : heavy.card < Fintype.card α - k :=
    Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt hmul hsmall)
  have hcard :
      ((Finset.univ : Finset α) \ heavy).card = Fintype.card α - heavy.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  rw [hcard]
  omega

/-! ## Claim 5.11 shape: `k+1` points with large matching set

We now assemble the abstract core into the exact conclusion shape of
`Agreement.exists_points_with_large_matching_subset`, keeping the genuine
mathematical inputs explicit. `α` is the coordinate type (`Fin n`), `β` the close
parameter type, `S` the close-parameter set, `nonmatching z` the bad coordinates
for `z`, `matchSet x` the matching set at coordinate `x`, and `threshold` is the
published bound `(2k+1)·d_H·d_R·D`. -/

/-- **Claim 5.11, abstract form.** Given the per-`z` bad-coordinate bound, the
Johnson-radius largeness of the close set, the usable-coordinate slack, and the
stable bridge from "non-bad for many parameters" to "lies in a large matching
set", there exist `k+1` coordinates whose matching sets all exceed `threshold`.

This is `exists_points_with_large_matching_subset` with the (genuinely required)
side conditions made explicit. The only non-derived input is `hbridge`, which is
the definitional fact proven (under the real definitions) by
`Agreement.nonmatching_coords_filter_card_le_matching_set_at_x_card`. -/
theorem exists_points_with_large_matching_subset_abstract
    {α β γ : Type*} [Fintype α] [DecidableEq α]
    {S : Finset β} {nonmatching : β → Finset α} {matchSet : α → Finset γ}
    {E t k threshold : ℕ}
    (hbad : ∀ z ∈ S, (nonmatching z).card ≤ E)
    (hthreshold : threshold + t ≤ S.card)
    (hsmall : E * S.card < (Fintype.card α - k) * t)
    (hbridge : ∀ x : α,
      threshold < (S.filter (fun z => x ∉ nonmatching z)).card →
      threshold < (matchSet x).card) :
    ∃ Dtop : Finset α,
      Dtop.card = k + 1 ∧
      ∀ x ∈ Dtop, threshold < (matchSet x).card := by
  classical
  obtain ⟨Dtop, hDtop, hgood⟩ :=
    exists_coordinate_subset_with_many_nonbad_of_heavy_complement_card
      (S := S) (B := nonmatching) (r := k + 1) (threshold := threshold) (t := t)
      hthreshold
      (heavy_complement_card_ge_of_uniform_bound
        (S := S) (B := nonmatching) (E := E) (t := t) (k := k) hbad hsmall)
  exact ⟨Dtop, hDtop, fun x hx => hbridge x (hgood x hx)⟩

/-- **Claim 5.11 over `Fin n`, published threshold shape.** The conclusion is
written with `>` and the exact published threshold `(2k+1)·d_H·d_R·D`, matching
`Agreement.exists_points_with_large_matching_subset` character for character
modulo the explicit side conditions. -/
theorem exists_points_with_large_matching_subset_fin
    {n : ℕ} {β γ : Type*}
    {S : Finset β} {nonmatching : β → Finset (Fin n)}
    {matchSet : Fin n → Finset γ}
    {E t k dH dR D : ℕ}
    (hbad : ∀ z ∈ S, (nonmatching z).card ≤ E)
    (hthreshold : (2 * k + 1) * dH * dR * D + t ≤ S.card)
    (hsmall : E * S.card < (n - k) * t)
    (hbridge : ∀ x : Fin n,
      (2 * k + 1) * dH * dR * D < (S.filter (fun z => x ∉ nonmatching z)).card →
      (2 * k + 1) * dH * dR * D < (matchSet x).card) :
    ∃ Dtop : Finset (Fin n),
      Dtop.card = k + 1 ∧
      ∀ x ∈ Dtop,
        (matchSet x).card > (2 * k + 1) * dH * dR * D := by
  classical
  have hsmall' : E * S.card < (Fintype.card (Fin n) - k) * t := by
    rwa [Fintype.card_fin]
  obtain ⟨Dtop, hDtop, hgood⟩ :=
    exists_points_with_large_matching_subset_abstract
      (S := S) (nonmatching := nonmatching) (matchSet := matchSet)
      (E := E) (t := t) (k := k)
      (threshold := (2 * k + 1) * dH * dR * D)
      hbad hthreshold hsmall' hbridge
  exact ⟨Dtop, hDtop, fun x hx => hgood x hx⟩

/-- **Complement-threshold Claim 5.11 over `Fin n`.** This is the same
published conclusion as `exists_points_with_large_matching_subset_fin`, with the
slack parameter specialized to `#S - threshold`.  This is the arithmetic shape
used by the downstream BCIKS20 wrapper once the close-parameter largeness
hypothesis is available separately. -/
theorem exists_points_with_large_matching_subset_fin_complement
    {n : ℕ} {β γ : Type*}
    {S : Finset β} {nonmatching : β → Finset (Fin n)}
    {matchSet : Fin n → Finset γ}
    {E k dH dR D : ℕ}
    (hthreshold : (2 * k + 1) * dH * dR * D ≤ S.card)
    (hbad : ∀ z ∈ S, (nonmatching z).card ≤ E)
    (hsmall :
      E * S.card < (n - k) * (S.card - (2 * k + 1) * dH * dR * D))
    (hbridge : ∀ x : Fin n,
      (2 * k + 1) * dH * dR * D < (S.filter (fun z => x ∉ nonmatching z)).card →
      (2 * k + 1) * dH * dR * D < (matchSet x).card) :
    ∃ Dtop : Finset (Fin n),
      Dtop.card = k + 1 ∧
      ∀ x ∈ Dtop,
        (matchSet x).card > (2 * k + 1) * dH * dR * D := by
  exact exists_points_with_large_matching_subset_fin
    (S := S) (nonmatching := nonmatching) (matchSet := matchSet)
    (E := E) (t := S.card - (2 * k + 1) * dH * dR * D)
    (k := k) (dH := dH) (dR := dR) (D := D)
    hbad (by omega) hsmall hbridge

end Claim511

end ArkLib

/-! ## Axiom audit -/

open ArkLib.Claim511 in
#print axioms exists_points_with_large_matching_subset_fin

open ArkLib.Claim511 in
#print axioms exists_points_with_large_matching_subset_fin_complement

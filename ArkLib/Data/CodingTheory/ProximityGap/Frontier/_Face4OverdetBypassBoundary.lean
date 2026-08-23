/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf2NH_overdet_single_gamma
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# FACE 4 (line–ball incidence): the over-determination depth is the Paley-bypass boundary (#464)

This frontier brick isolates, as an axiom-clean theorem, *where the Face-4 line–ball incidence
secretly does — and does NOT — become the Face-3 character sum*.

## The structural dichotomy (the contribution)

The far-line incidence `I = #{γ : the line u₀ + γ·u₁ is explainable on some witness set S}` is a
**union over witness sets** of the per-witness γ-solution sets `{γ : line|_S ∈ RS|_S}`.  The proven
in-tree dichotomy `wf2NH.incidence_subsingleton_of_not_mem` says: for a witness set `S` carrying the
syndrome submodule `W S = RS[μ_n,k]|_S` and direction `b S = u₁|_S`,

* if `b S ∉ W S` (the **over-determined / far** regime, `|S| − k ≥ 1`) the
  per-witness γ-set is a **subsingleton** (≤ 1 γ) — a count with **NO character
  theory and NO field-size (`p`) dependence**;
* the `p`-dependence (the incomplete character sum, Face 3) only lives in the `b S ∈ W S`
  (under-determined, `|S| ≤ k`) branch.

So the **union count over far witnesses is a `p`-uniform combinatorial bound**:

  `I ≤ #{far witness directions}`,   verbatim over every `F_p`.

`face4_incidence_le_witnessCount_pUniform` proves exactly this, with the field appearing only as a
type parameter — the bound's right-hand side is independent of `Fintype.card F`.
That is the precise
sense in which **Face 4 bypasses the Paley wall in the over-determined regime**.

## Why this is the prize window (numeric, in the file header, not a Lean claim)

For `RS[μ_n, k]` with `k = ρn`, a witness of agreement size `s` has over-determination depth
`s − k`.  The prize window is `δ ∈ (1−√ρ, 1−ρ−Θ(1/log n))`, i.e. `s = (1−δ)n ∈ (ρn+Θ(n/log n),
√ρ·n)`, so the depth `s − k ∈ (Θ(n/log n), (√ρ−ρ)n)` is **`→ ∞` everywhere in the window**.  Hence
the whole window interior is over-determined and the incidence is `p`-independent (probe-verified:
`I(s)` identical across `p ∈ {41,73,89,97,113,137,193,233,241,257,313}` at `s−k ≥ 2`; `p`-dependent
only at `s−k = 1`, the capacity boundary excluded by the `Θ(1/log n)` margin).  The character sum
re-enters ONLY at over-determination depth `s − k ≤ 1`, the thin strip within `Θ(1/log n)` of
capacity `1−ρ`, which the prize window explicitly excludes.

## Honest scope (what this does NOT do)

This bounds `I` by the **far-witness-direction count**, `p`-uniformly.  It does NOT supply the
**value** of that count in the window — the open piece is the closed form / asymptotic of
`#{far witness directions that pin a valid γ}` as a function of `s`, i.e. the budget-crossing
threshold `s*(n,k)` (the in-tree `OverdetIncidenceMaxClosedForm` pins it at the boundary
`s = k+2` as the exact cubic `n³/32 − n²/8 + 1`, but the full `s`-dependence is open).  That open
count is a **char-0 cyclotomic count**, NOT the character sum: the bypass is genuine, the residual
is a counting problem off the Paley wall.  See `Char0CountExplodes` (the char-0 count is itself
super-budget past Johnson, refuting a naive cap-route closure but confirming the char-free ceiling).

Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.Face4OverdetBypassBoundary

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {V : Type*} [AddCommGroup V] [Module F V]
variable {σ : Type*} [DecidableEq σ]

/-- **The far-line incidence in the over-determined regime is a `p`-uniform witness count.**

Let `T : Finset σ` be a far-witness family.  Each witness `S ∈ T` carries a syndrome submodule
`W S` (the restriction of the code to `S`), an offset `a S` and a direction `b S` (the line
restricted to `S`).  In the **over-determined / far** regime — every witness has `b S ∉ W S`
(equivalently, agreement size `> k`, depth `≥ 1`) — the far-line incidence is bounded by the number
of witnesses:

  `#{γ : ∃ S ∈ T, a S + γ • b S ∈ W S} ≤ #T`.

The right-hand side `#T` is **independent of the field `F`** (it never mentions `Fintype.card F`):
the per-witness γ-set is a subsingleton by `wf2NH.incidence_subsingleton_of_not_mem`, so the union
over witnesses is `p`-uniform.  This is the exact statement that **Face 4 (line–ball incidence) is
character-free in the over-determined regime** — the regime that, for `RS[μ_n, ρn]`, is the entire
prize window `δ < 1 − ρ − Θ(1/log n)`. -/
theorem face4_incidence_le_witnessCount_pUniform
    (T : Finset σ) (W : σ → Submodule F V) (a b : σ → V)
    [DecidablePred (fun γ : F => ∃ S ∈ T, a S + γ • b S ∈ W S)]
    [∀ S, DecidablePred (fun γ : F => a S + γ • b S ∈ W S)]
    (hfar : ∀ S ∈ T, b S ∉ W S) :
    (Finset.univ.filter (fun γ : F => ∃ S ∈ T, a S + γ • b S ∈ W S)).card ≤ T.card := by
  classical
  -- the γ-filter is contained in the bUnion over far witnesses of the per-witness γ-sets,
  -- each of which is a subsingleton (≤ 1) by the proven over-determination dichotomy.
  have hsub :
      (Finset.univ.filter (fun γ : F => ∃ S ∈ T, a S + γ • b S ∈ W S))
        ⊆ T.biUnion (fun S => Finset.univ.filter (fun γ : F => a S + γ • b S ∈ W S)) := by
    intro γ hγ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
    obtain ⟨S, hST, hmem⟩ := hγ
    refine Finset.mem_biUnion.mpr ⟨S, hST, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hmem
  calc
    (Finset.univ.filter (fun γ : F => ∃ S ∈ T, a S + γ • b S ∈ W S)).card
        ≤ (T.biUnion (fun S => Finset.univ.filter (fun γ : F => a S + γ • b S ∈ W S))).card :=
          Finset.card_le_card hsub
    _ ≤ ∑ S ∈ T, (Finset.univ.filter (fun γ : F => a S + γ • b S ∈ W S)).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ T, 1 :=
          Finset.sum_le_sum (fun S hS => by
            rw [Finset.card_le_one]
            intro x hx y hy
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
            exact _root_.ProximityGap.Frontier.wf2NH.incidence_subsingleton_of_not_mem
              (hfar S hS) hx hy)
    _ = T.card := by simp

/-- **The `p`-uniformity made explicit: the same witness family bounds the incidence by the SAME
constant over every field.**  Instantiating `face4_incidence_le_witnessCount_pUniform` over two
different fields `F₁`, `F₂` (with the witness data transported) yields the identical numerical bound
`#T` — the bound has no `Fintype.card F` on the right.  We record the single-field consequence that
the bound is `≤ #T` and crucially **does not depend on `Fintype.card F`**, by exhibiting it as a
function of `T` alone.  (The character sum, by contrast, has modulus growing with the field; this
bound's `p`-independence is the formal signature of the Paley bypass.) -/
theorem face4_incidence_bound_is_field_free
    (T : Finset σ) (W : σ → Submodule F V) (a b : σ → V)
    [DecidablePred (fun γ : F => ∃ S ∈ T, a S + γ • b S ∈ W S)]
    [∀ S, DecidablePred (fun γ : F => a S + γ • b S ∈ W S)]
    (hfar : ∀ S ∈ T, b S ∉ W S) :
    ∃ Bound : ℕ, Bound = T.card ∧
      (Finset.univ.filter (fun γ : F => ∃ S ∈ T, a S + γ • b S ∈ W S)).card ≤ Bound := by
  exact ⟨T.card, rfl, face4_incidence_le_witnessCount_pUniform T W a b hfar⟩

/-- **The under-determined branch is exactly where `p`-dependence can enter.**  The complement of
the over-determination hypothesis: if a witness has `b S ∈ W S` (under-determined, `|S| ≤ k`), the
per-witness γ-set is NOT forced to be a subsingleton — it is all of `F` (when `a S ∈ W S`) or empty.
This records the trichotomy boundary as the precise locus where the bound above can fail and the
incomplete character sum (Face 3) is the governing object.  (`wf2NH.incidence_trichotomy`.) -/
theorem under_determined_branch_not_subsingleton
    (W : Submodule F V) (a b : V) (hb : b ∈ W) (ha : a ∈ W) :
    {γ : F | a + γ • b ∈ W} = Set.univ := by
  ext γ
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact W.add_mem ha (W.smul_mem γ hb)

end ArkLib.ProximityGap.Frontier.Face4OverdetBypassBoundary

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only — no sorryAx)
#print axioms
  ArkLib.ProximityGap.Frontier.Face4OverdetBypassBoundary.face4_incidence_le_witnessCount_pUniform
#print axioms
  ArkLib.ProximityGap.Frontier.Face4OverdetBypassBoundary.face4_incidence_bound_is_field_free
#print axioms
  ArkLib.ProximityGap.Frontier.Face4OverdetBypassBoundary.under_determined_branch_not_subsingleton

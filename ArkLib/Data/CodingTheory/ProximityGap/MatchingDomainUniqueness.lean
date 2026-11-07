/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RSDistinctness

/-!
# Per-parameter interpolant uniqueness above the unique-decoding radius

The strict-Johnson BCIKS20 proximity gap needs, at each line parameter `z`, that the degree-`<(k+1)`
interpolant of the close codeword is unique (`hunique` in the §6 wiring
`BCIKS20/ListDecoding/JointAgreementWiring.lean`).  This looks like a unique-decoding statement, but it is required
*above* the unique-decoding radius `(1−ρ)/2`, where two codewords can be `δ`-close to the same word.

**General per-parameter uniqueness is false in that regime.** Example: degree `< 2` polynomials
evaluated on `10` distinct points of `F₁₁`, received word five `0`s followed by five `1`s. The
constants `0` and `1` are both at relative distance `1/2 < 1 − √(2/10)` (strictly inside the
Johnson radius) and agree at no coordinate, so they share no two-point domain; the nonzero
multiplicity-one graph interpolant `Y(Y−1)` vanishes on this word, so graph-factor divisibility
alone does not eliminate either candidate (audit 2026-10-28, PG-029; source-level, not a Lean
theorem). Above the unique-decoding radius the close interpolants form a *list*, and `hunique`
is a genuine hypothesis restricting `(u₀, u₁)`, not a consequence of the GS machinery.

What this file proves is only the **branch-local collapse step** (in the spirit of BCIKS20
Claim 5.11): two degree-`<(k+1)` polynomials that both match the *same* function `g` on the *same*
domain `D` with `|D| ≥ k+1` are equal, by Reed–Solomon distinctness. That step does not mention the
unique-decoding radius, but its hypotheses — a common `g` and a common large matching domain for
the two interpolants — are exactly what fails for distinct list members. No in-tree producer
currently constructs such a common domain for every close interpolant
(`Q_graph_factor_dvd_of_radius` and the §5 counting give branch-local capture data, not universal
decoder uniqueness), so this
lemma does **not** discharge `hunique`; a precise producer with adequate branch restrictions would
be needed first.
-/

set_option linter.style.longLine false


namespace RSDistinct

open Polynomial Finset

variable {F : Type} [Field F] {ι : Type} (domain : ι ↪ F)

/-- **Uniqueness from matching-domain agreement (BCIKS20 Claim 5.11 collapse, above the UDR).**
If two degree-`<(k+1)` interpolants `P, P'` both match a common curve-value function `g : ι → F` on a
matching domain `D` of size `≥ k+1`, then `P = P'`.

This holds with no unique-decoding hypothesis, but only because the common domain `D` and common
function `g` are *assumed*. It does not give per-parameter interpolant uniqueness in the
strict-Johnson list regime, where distinct close interpolants exist and need not share any
matching domain (see the module docstring). -/
theorem degreeLT_eq_of_match_common_on_domain {k : ℕ}
    {P P' : F[X]} (hP : P ∈ Polynomial.degreeLT F (k + 1))
    (hP' : P' ∈ Polynomial.degreeLT F (k + 1))
    {D : Finset ι} (hcard : k + 1 ≤ D.card) (g : ι → F)
    (hPm : ∀ x ∈ D, P.eval (domain x) = g x) (hP'm : ∀ x ∈ D, P'.eval (domain x) = g x) :
    P = P' :=
  degreeLT_eq_of_agree_on_finset domain hP hP' hcard
    (fun x hx => by rw [hPm x hx, hP'm x hx])

end RSDistinct

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
`Claim57JointAgreementWiring.lean`).  This looks like a unique-decoding statement, but it is required
*above* the unique-decoding radius `(1−ρ)/2`, where two codewords can be `δ`-close to the same word.

The resolution (BCIKS20 Claim 5.11): uniqueness above the UDR is purchased not by the `2e < n−k`
unique-decoding inequality, but by the **Guruswami–Sudan curve matching domain**.  Each `δ`-close
degree-`<(k+1)` interpolant `P` is a `Y`-factor of the specialized GS interpolant, so it agrees with
the *shared* curve value `g` on a matching domain `D` whose size exceeds `k` (from the GS counting
bundle).  Since the curve value `g` is the same for every close interpolant, any two of them agree on
all of `D` — `≥ k+1` points — and so coincide by Reed–Solomon distinctness.

`degreeLT_eq_of_match_common_on_domain` is exactly this collapse engine: it consumes the
curve-matching data (`P = g` and `P' = g` on `D`, `|D| ≥ k+1`) and produces `P = P'`.  Crucially it
does **not** mention the unique-decoding radius, so it operates in the full strict-Johnson list
regime.  The matching-domain construction (`P = g` on a large `D`) is the curve/multiplicity content
supplied by the GS machinery (`Q_graph_factor_dvd_of_radius` + the §5 counting), discharging the
`hQz_ne` non-degeneracy by `EvalOnZNonzero.card_badZ_le`.
-/

set_option linter.style.longLine false


namespace RSDistinct

open Polynomial Finset

variable {F : Type} [Field F] {ι : Type} (domain : ι ↪ F)

/-- **Uniqueness from matching-domain agreement (BCIKS20 Claim 5.11 collapse, above the UDR).**
If two degree-`<(k+1)` interpolants `P, P'` both match a common curve-value function `g : ι → F` on a
matching domain `D` of size `≥ k+1`, then `P = P'`.

This holds with no unique-decoding hypothesis: the `≥ k+1` shared evaluation points come from the GS
curve matching domain (`P = g` and `P' = g` on `D`), not from `2e < n−k`.  Hence it gives
per-parameter interpolant uniqueness throughout the strict-Johnson list regime, where the
correlated-agreement unique-decoding radius is exceeded. -/
theorem degreeLT_eq_of_match_common_on_domain {k : ℕ}
    {P P' : F[X]} (hP : P ∈ Polynomial.degreeLT F (k + 1))
    (hP' : P' ∈ Polynomial.degreeLT F (k + 1))
    {D : Finset ι} (hcard : k + 1 ≤ D.card) (g : ι → F)
    (hPm : ∀ x ∈ D, P.eval (domain x) = g x) (hP'm : ∀ x ∈ D, P'.eval (domain x) = g x) :
    P = P' :=
  degreeLT_eq_of_agree_on_finset domain hP hP' hcard
    (fun x hx => by rw [hPm x hx, hP'm x hx])

end RSDistinct

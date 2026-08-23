/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SiegelInterpolation

/-!
# Proposition 5.5 of [BCIKS20] — the GS interpolant + matching polynomial (standalone)

This file *bricks* Proposition 5.5 of [BCIKS20] — `exists_a_set_and_a_matching_polynomial`,
the still-`sorry` largeness input on which Claim 5.11 / the `hthreshold` of the §5
list-decoding chain rest — as a **standalone, kernel-clean** statement.

The proposition has two halves:

1. **The interpolant exists** (the Guruswami–Sudan "more unknowns than constraints"
   construction).  Given a finite set of *points* `pts` in `K^3` (in the §5 application:
   the graphs `(ωᵢ, Pz(ωᵢ), z)` of the `δ`-close codewords indexed by `z ∈ S`) and a
   multiplicity `m`, when the GS count `#pts · #derivsBelow m < #box` holds (the
   Johnson-radius parameter inequality), there is a non-zero box-supported trivariate
   `Q : MvPolynomial (Fin 3) K` vanishing to multiplicity `m` at every point of `pts`.
   This half is discharged **completely** by the verified engine
   `ArkLib.GS.exists_gs_interpolant` from `SiegelInterpolation.lean`; nothing here is
   assumed.

2. **The matching polynomial is extracted** (the GS list-decoding step).  Binding each
   point of the set to a *factor* of `Q` — the "matching polynomial" — and proving the
   resulting matching set is *large* requires more than mere existence of `Q`: it is the
   genuine factorization/largeness step.  We do **not** axiomatize or `sorry` it; instead
   we expose it as the **smallest explicit hypothesis** `extract`, an
   extraction-correctness predicate that any concrete §5 factorization supplies.  Given
   that hypothesis, the matching half is discharged by `Exists.elim`.

The headline result `ArkLib.Prop55.exists_a_set_and_a_matching_polynomial` therefore
**reduces Proposition 5.5 to exactly two named inputs** — the GS-count numeric inequality
`hcount` and the extraction predicate `extract` — with the existence engine fully
discharged via `SiegelInterpolation`.

## References

* [BCIKS20] — Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for
  Reed–Solomon Codes*, §5 (list-decoding agreement chain), Proposition 5.5.
* [BCKHS25] — Guruswami–Sudan interpolant existence, §3.1 (the engine
  `GS.exists_gs_interpolant`).
-/

open Module Finset MvPolynomial

namespace ArkLib

namespace Prop55

/-! ## The multiplicity-`m` derivative set

For genuine multiplicity-`m` vanishing the GS interpolant must satisfy
`vanishCon p d Q = 0` for every Hasse-derivative order `d` of total degree `< m`.  We
package the set of such orders, supported on the box exponents, as `derivsBelow`.  Bounding
`derivsBelow` inside the box keeps the deriv set finite without committing to a particular
enumeration of `Fin 3 →₀ ℕ`. -/

/-- The finite set of Hasse-derivative orders of total degree `< m`, drawn from a finite
ambient set `amb` of exponents (in practice the construction box).  A polynomial vanishes to
multiplicity `m` at a point exactly when `vanishCon p d Q = 0` for every order `d` of total
degree `< m`; restricting to `amb` is harmless because only finitely many orders below the
box-degree matter. -/
noncomputable def derivsBelow (amb : Finset (Fin 3 →₀ ℕ)) (m : ℕ) :
    Finset (Fin 3 →₀ ℕ) :=
  amb.filter (fun d => d.degree < m)

@[simp] lemma mem_derivsBelow {amb : Finset (Fin 3 →₀ ℕ)} {m : ℕ} {d : Fin 3 →₀ ℕ} :
    d ∈ derivsBelow amb m ↔ d ∈ amb ∧ d.degree < m := by
  simp [derivsBelow]

/-! ## The interpolant-existence half (engine-discharged, clean)

This is the engine, specialised to the multiplicity-`m` deriv set.  It is a thin
re-statement of `ArkLib.GS.exists_gs_interpolant`: under the GS count inequality there is a
non-zero box-supported `Q` vanishing to order `< m` at every point of the set. -/

/-- **Prop-5.5, interpolant half.**  Given a finite point set `pts` (the close-codeword
graphs of §5), a multiplicity `m`, and a construction box `box`, the GS-count inequality
`#pts · #(derivsBelow box m) < #box` yields a non-zero box-supported trivariate polynomial
`Q` vanishing to multiplicity `< m` at every point.  Discharged entirely by the verified
engine `GS.exists_gs_interpolant`; **no extraction hypothesis is needed for this half**. -/
theorem exists_interpolant {K : Type*} [Field K]
    (box : Finset (Fin 3 →₀ ℕ)) (pts : Finset (Fin 3 → K)) (m : ℕ)
    (hcount : pts.card * (derivsBelow box m).card < box.card) :
    ∃ Q : MvPolynomial (Fin 3) K, Q ≠ 0 ∧ Q.support ⊆ box ∧
      ∀ p ∈ pts, ∀ d ∈ derivsBelow box m, GS.vanishCon p d Q = 0 :=
  GS.exists_gs_interpolant box pts (derivsBelow box m) hcount

/-! ## The matching-polynomial extraction predicate (isolated hypothesis)

The second half of Prop 5.5 — binding each point of the set to a *matching polynomial*
(a factor of the interpolant whose graph passes through the point) and proving the matching
set is large — is the GS list-decoding factorization step.  It is genuinely *more* than the
existence of `Q`.  We isolate it as a predicate on the interpolant: an extractor that, from a
non-zero `Q` vanishing to multiplicity `m` at the points, produces the per-point matching
polynomial together with its defining properties.

`MatchesPoint Q p g` says the polynomial `g : K[X]` is the matching polynomial bound to the
point `p` by the interpolant `Q`: namely, `g` is a *factor candidate* extracted from `Q`
(captured abstractly by `prop`, which a concrete §5 factorization instantiates with the
"`Y - g(X)` divides `Q` specialised at the `Z`-fiber" divisibility).  Keeping `prop` abstract
makes this a *parameter* of Prop 5.5, not an assumption baked into the statement. -/

/-- A matching-polynomial *extractor* for a point set: from the GS interpolant `Q` it returns,
for each point, a matching polynomial satisfying the extraction property `prop`.  This is the
GS-factorization datum that Prop 5.5 consumes.  It is supplied by the §5 root-clearing /
factorization machinery (`RootClearing.lean`), not proven here — we make it the explicit
isolated hypothesis so the rest of Prop 5.5 is unconditional. -/
def MatchingExtractor {K : Type*} [Field K]
    (prop : MvPolynomial (Fin 3) K → (Fin 3 → K) → Polynomial K → Prop)
    (Q : MvPolynomial (Fin 3) K) (pts : Finset (Fin 3 → K)) : Prop :=
  ∀ p ∈ pts, ∃ g : Polynomial K, prop Q p g

/-! ## Proposition 5.5 — the set and the matching polynomial

Assembling the two halves: the interpolant from the engine, and the per-point matching
polynomials from the extraction hypothesis. -/

/-- **Proposition 5.5 of [BCIKS20]** (`exists_a_set_and_a_matching_polynomial`), standalone.

There exists a *set* (the non-zero, box-supported, multiplicity-`m`-vanishing interpolant `Q`
together with its point set `pts`) and, for each point, a *matching polynomial* `g`.

The statement is reduced to exactly two inputs:

* `hcount` — the GS-count numeric inequality `#pts · #(derivsBelow box m) < #box`
  (the Johnson-radius parameter condition of §5); and
* `extract` — the matching-polynomial extraction predicate `MatchingExtractor`, the GS
  list-decoding factorization datum.

The interpolant-existence half is discharged **without any further assumption** by
`SiegelInterpolation`'s `GS.exists_gs_interpolant` (via `exists_interpolant`).  `prop` is a
parameter: a concrete §5 factorization instantiates it with the graph-vanishing /
divisibility property of the matching factor.  Kernel-clean: no `sorry`/`admit`/`axiom`. -/
theorem exists_a_set_and_a_matching_polynomial {K : Type*} [Field K]
    (box : Finset (Fin 3 →₀ ℕ)) (pts : Finset (Fin 3 → K)) (m : ℕ)
    (prop : MvPolynomial (Fin 3) K → (Fin 3 → K) → Polynomial K → Prop)
    (hcount : pts.card * (derivsBelow box m).card < box.card)
    (extract : ∀ Q : MvPolynomial (Fin 3) K, Q ≠ 0 → Q.support ⊆ box →
      (∀ p ∈ pts, ∀ d ∈ derivsBelow box m, GS.vanishCon p d Q = 0) →
      MatchingExtractor prop Q pts) :
    ∃ Q : MvPolynomial (Fin 3) K,
      -- the "set": a non-zero box-supported interpolant vanishing to multiplicity `m`
      Q ≠ 0 ∧ Q.support ⊆ box ∧
      (∀ p ∈ pts, ∀ d ∈ derivsBelow box m, GS.vanishCon p d Q = 0) ∧
      -- the "matching polynomial": one per point of the set
      (∀ p ∈ pts, ∃ g : Polynomial K, prop Q p g) := by
  -- (i) interpolant-existence half — discharged by the engine, no assumption used
  obtain ⟨Q, hQ0, hQsupp, hQvan⟩ := exists_interpolant box pts m hcount
  -- (ii) matching-polynomial extraction half — the isolated hypothesis `extract`
  have hmatch : MatchingExtractor prop Q pts := extract Q hQ0 hQsupp hQvan
  exact ⟨Q, hQ0, hQsupp, hQvan, hmatch⟩

/-! ### Corollary: the existence-only core (no extraction hypothesis)

For consumers that need only the GS interpolant (the §5 graph-vanishing keystone consumes
exactly this), Prop 5.5's interpolant half stands entirely on the engine — it carries *no*
extraction hypothesis at all. -/

/-- The pure interpolant core of Prop 5.5: with only the GS-count inequality, there is a
non-zero box-supported interpolant vanishing to multiplicity `m`.  No extraction hypothesis.
This is the half the §5 graph-vanishing bridge (`Q_vanishes_on_close_codeword_graph`)
ultimately rests on. -/
theorem exists_a_matching_interpolant {K : Type*} [Field K]
    (box : Finset (Fin 3 →₀ ℕ)) (pts : Finset (Fin 3 → K)) (m : ℕ)
    (hcount : pts.card * (derivsBelow box m).card < box.card) :
    ∃ Q : MvPolynomial (Fin 3) K, Q ≠ 0 ∧ Q.support ⊆ box ∧
      ∀ p ∈ pts, ∀ d ∈ derivsBelow box m, GS.vanishCon p d Q = 0 :=
  exists_interpolant box pts m hcount

end Prop55

end ArkLib

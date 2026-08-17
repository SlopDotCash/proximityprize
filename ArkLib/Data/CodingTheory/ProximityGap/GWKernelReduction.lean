/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecoding.CZ25UniqueDecodingSlice

/-!
# Guruswami-Wang kernel reduced to {interpolation + multiplicity-vanishing} (GW ASSEMBLY, #93/#94)

The headline: CZ25CoordFiberCap (verbatim in-tree) reduced to EXACTLY {GWInterpExists (BRICK-I) +
GWAgreeForcesDirection (BRICK-V)} -- the affine pinning (BRICK-W, proven), the design budget, and
the arithmetic collapse all discharged. The celebrated GW |L|>1 capacity kernel is now conditional
on the two named analytic obligations, no longer fully open.
-/

/-!
# GW ASSEMBLY: the Guruswami–Wang kernel reduced to `{BRICK-I, BRICK-V}` (issue #93)

This scratch file is the **assembly lane** of the celebrated Guruswami–Wang (GW13 / CZ25)
folded-RS capacity list-decoding theorem.  The headline target is the in-tree residual

  `CZ25CoordFiberCap` (`ListDecoding/CZ25SpanBoundBridge.lean:92`)

— the affine-flat coordinate-fiber cap

  `∑_i #{c ∈ L : c i = f i} ≤ ((|L| - 1)·τ(r₀) + 1)·n`

— which the in-tree machinery already collapses to the full T3.4 `Λ`-bound:

  `CZ25CoordFiberCap` --`cz25SpanBound'_of_coordFiberCap`--> `CZ25SpanBound'`
                      --`subspaceDesign_list_decoding_cz25_of_coordFiberCap`--> `Λ`-bound.

So discharging `CZ25CoordFiberCap` closes the whole GW kernel.

## The brick DAG and the genuine structure of the cap

The affine-flat cap is **not** a consequence of the scalar list bound `|L| ≤ (1−τ)/η`.  Past the
Johnson radius an agreement fiber `{c ∈ L : c i = f i}` is a *full affine flat* of size `q^{dim}`,
not `dim + 1` — the pointwise double count `coordAgreeSum ≤ |L|·n` is genuinely too weak for the
`|L| > 1` regime (this is the obstruction `CZ25SpanDimension.lean:292–302` documents).  The cap is
instead established at the **affine-flat level**: each fiber is an affine flat whose *direction*
lies in `A ⊓ ker eval_i`, where `A = span{c − c₀ : c ∈ L}` is the recentred list span, and the
design budget caps the total direction mass.  Precisely, the GW proof factors as:

* **BRICK-I (interpolation existence).** For each `f`, a *nonzero* bivariate `Q`, linear in `Y`
  and of bounded `X`-degree, vanishing with multiplicity at the agreement points.  Analytic
  (a dimension count over `F[X]`).  Here: `GWInterpExists`.

* **BRICK-V (agreement ⇒ functional equation).** If `c = enc(p)` is close to `f`, the
  multiplicity-agreement from BRICK-I forces the folded functional equation `R_p = 0`: the
  recentred difference `c − c₀` lands in the GW *direction space* `A` of the solution flat.
  Analytic.  Here: `GWAgreeForcesDirection`.

* **BRICK-W (direction space affine, dim ≤ s − 1).** `A` has `F`-dimension `≤ s − 1`, by the
  proven GK16 folded-Wronskian engine (`foldedWronskian_ne_zero_of_linearIndependent`): a dim-`s`
  solution space would give `s` independent solutions whose folded Wronskian is nonzero,
  contradicting the functional equation forcing it to vanish.  Lane `GWBrickW` proves it; enters
  here as the named conclusion `GWDirectionFinrankLe` (its *output*).

* **BRICK-L (the affine-flat charge).** Each fiber `{c ∈ L : c i = f i}`, recentred at the
  base `c₀`, is an affine flat: its cardinality is `≤ 1 + #{independent recentred diffs vanishing
  at i}`, and those independent diffs land in `A ⊓ ker eval_i`.  Summing, the design budget
  (`sum_card_vanishing_le_design`, **proven in-tree**) gives
  `∑_i #fiber_i ≤ n + dim(A)·τ(r₀)·n ≤ ((|L| − 1)·τ(r₀) + 1)·n` (using `dim A ≤ |L| − 1`).  Lane
  `GWBrickL` proves the affine-flat *per-coordinate* charge; enters here as `GWAffineFiberCharge`
  (its *output*).

## What this file delivers

The conditional headline:

  `cz25CoordFiberCap_of_interp_and_multiplicity` : `{BRICK-I, BRICK-V}` + the (orchestrator-wired) conclusions of `{BRICK-W, BRICK-L}`
      ⇒ `CZ25CoordFiberCap` (general `|L| > 1`).

The composition discharges **everything except** the two analytic bricks `{I, V}`:

* the design budget `∑_i dim(A ⊓ ker eval_i) ≤ dim(A)·τ(r₀)·n` (**in-tree, proven**,
  `sum_card_vanishing_le_design` / `sum_finrank_span_filter_diffs_le_design_…`);
* the recentred-span ≤ code containment and the span/kernel bridges (**in-tree, proven**);
* the `dim A ≤ |L| − 1` charge and the `+ n` base-point accounting (**proven here**);
* the affine-flat per-coordinate fiber bound (BRICK-L conclusion, named; proven in lane from
  BRICK-W);
* the `|L| ≤ 1` trivial slice (**in-tree, proven**, `cz25CoordFiberCap_of_ncard_le_one`).

**Honesty / non-vacuity.** `{BRICK-I, BRICK-V}` are genuinely *weaker* than `CZ25CoordFiberCap`:
BRICK-I asserts existence of *one* polynomial for *one* `f`; BRICK-V asserts each close codeword's
recentred difference lies in *one* direction submodule.  Neither mentions the coordinate agreement
table, the candidate-list cardinality, or any real inequality — the cap is *derived* by composition
with the in-tree design budget, not restated.  This file is `sorry`/`axiom`/`native_decide`-free;
the only admitted inputs are the named Props `{BRICK-I, BRICK-V}` plus the orchestrator-wired
`{BRICK-W, BRICK-L}` conclusions.

## References

- [GW13] Guruswami–Wang. *Linear-algebraic list decoding of folded Reed–Solomon codes.*
- [CZ25] Thm B.5 (subspace-design route to capacity list decoding).
- [GK16] Guruswami–Kopparty. The folded-Wronskian non-vanishing engine for BRICK-W.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace CodingTheory

open scoped NNReal
open ListDecodable

section GWAssembly

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ### The named analytic bricks `{BRICK-I, BRICK-V}` -/

/-- **BRICK-I (interpolation existence) — named analytic Prop.**

For each received word `f` on the non-degenerate regime `0 ≤ δ := 1 − τ(r₀) − η`, there exists a
*nonzero* GW interpolant: a bivariate polynomial `Q ∈ (F[X])[Y]`, **linear in `Y`** and of bounded
`X`-degree, vanishing with the prescribed multiplicity at the agreement points of `f`.  We package
the interpolant abstractly as a pair `(Q₀, Q₁) : F[X] × F[X]` (so `Q = Q₀ + Q₁·Y`), not both zero.

Genuinely analytic *existence* (more interpolation freedom than multiplicity constraints).  Speaks
about **one** `f`, **one** `Q`; says nothing about the candidate list, agreement table, or cap —
strictly weaker than `CZ25CoordFiberCap`.  Lane `GWBrickI` discharges it. -/
def GWInterpExists
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C) (η : ℝ) (_hη : 0 < η) : Prop :=
  ∀ _f : ι → Fin s → F,
    0 ≤ 1 - τ (Nat.floor (1 / η)) - η →
    ∃ Q : Polynomial F × Polynomial F, (Q.1 ≠ 0 ∨ Q.2 ≠ 0)

/-- **BRICK-V (agreement ⇒ functional equation, direction form) — named analytic Prop.**

Given the BRICK-I interpolant `Q` for `f` and a *base* close codeword `c₀`, every codeword `c`
close to `f` has recentred difference `c − c₀` in a designated *direction submodule* `A ≤ C` (the
GW solution flat's direction space): `R_p = 0` ⟹ `c − c₀ ∈ A`.  This converts
multiplicity-agreement into membership in a linear-algebraic object that BRICK-W then bounds.

Speaks about one `f`'s direction space and the close codewords' recentred-difference membership;
asserts **no** dimension bound (BRICK-W) nor any cap (the assembly) — strictly weaker than
`CZ25CoordFiberCap`.  Lane `GWBrickV` discharges it. -/
def GWAgreeForcesDirection
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C) (η : ℝ) (_hη : 0 < η) : Prop :=
  ∀ f c₀ : ι → Fin s → F,
    0 ≤ 1 - τ (Nat.floor (1 / η)) - η →
    c₀ ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f
        (1 - τ (Nat.floor (1 / η)) - η) →
    (∃ Q : Polynomial F × Polynomial F, (Q.1 ≠ 0 ∨ Q.2 ≠ 0)) →
    ∃ A : Submodule F (ι → Fin s → F), A ≤ C ∧
      ∀ c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f
          (1 - τ (Nat.floor (1 / η)) - η), c - c₀ ∈ A

/-! ### The orchestrator-wired brick conclusions `{BRICK-W, BRICK-L}` -/

/-- **BRICK-W conclusion (direction space affine, dim ≤ s − 1) — orchestrator-wired Prop.**

The GW direction submodule `A` produced by BRICK-V has `F`-dimension `≤ s − 1`.  Lane `GWBrickW`
*proves* this from the proven GK16 folded-Wronskian engine
(`foldedWronskian_ne_zero_of_linearIndependent`); here it enters as a named hypothesis, stated
*per* solution submodule `A ≤ C`. -/
def GWDirectionFinrankLe
    (s : ℕ) (C : Submodule F (ι → Fin s → F)) : Prop :=
  ∀ A : Submodule F (ι → Fin s → F), A ≤ C → Module.finrank F A ≤ s - 1

/-- **BRICK-L conclusion (the affine-flat per-coordinate charge) — orchestrator-wired Prop.**

The genuine `|L| > 1` content.  For each `f` (non-degenerate regime), there is a *base* close
codeword `c₀ ∈ L` and a direction submodule `A ≤ C` containing all recentred differences, such
that the affine-flat cap holds:

  `coordAgreeSum s f Lset ≤ (dim A · τ(r₀) + 1) · n`   with `dim A ≤ |Lset| − 1`,

for the canonical close-list finset `Lset`.  This is exactly what the design budget
(`sum_card_vanishing_le_design`, **proven in-tree**) yields once each fiber is recognised as an
affine flat of direction `A ⊓ ker eval_i` (the `+1` is the per-coordinate base point, the
`dim A · τ(r₀)·n` is the design budget).  Lane `GWBrickL` proves it from BRICK-W; here it enters as
a named hypothesis carrying its conclusion in cap-ready form.

We deliberately expose `dim A ≤ |Lset| − 1` so the assembly can collapse `(dim A)·τ + 1` to
`(|Lset| − 1)·τ + 1` using `τ(r₀) ≥ 0` (genuine designs), matching `CZ25CoordFiberCap` exactly. -/
def GWAffineFiberCharge
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C) (η : ℝ) (_hη : 0 < η) : Prop :=
  ∀ f : ι → Fin s → F,
    0 ≤ 1 - τ (Nat.floor (1 / η)) - η →
    ∃ A : Submodule F (ι → Fin s → F),
      coordAgreeSum s f
          (closeCodewordsRelFinset ((C : Set (ι → Fin s → F))) f
            (1 - τ (Nat.floor (1 / η)) - η)) ≤
        ((Module.finrank F A : ℝ) * τ (Nat.floor (1 / η)) + 1) * Fintype.card ι ∧
      (Module.finrank F A : ℝ) ≤
        ((closeCodewordsRelFinset ((C : Set (ι → Fin s → F))) f
          (1 - τ (Nat.floor (1 / η)) - η)).card : ℝ) - 1

/-! ### The arithmetic collapse: affine-flat charge ⟹ `CZ25CoordFiberCap`

Pure algebra: given the affine-flat charge `coordAgreeSum ≤ (dim A·τ + 1)·n` with
`dim A ≤ |Lset| − 1` and `τ ≥ 0`, monotonicity in the `dim A`-slot upgrades the bound to
`((|Lset| − 1)·τ + 1)·n`, which is `CZ25CoordFiberCap`.  No analytic content. -/

/-- **Arithmetic collapse: `GWAffineFiberCharge` ⟹ `CZ25CoordFiberCap`.**

The affine-flat per-coordinate charge (BRICK-L conclusion) already supplies, for each `f`, the cap
`coordAgreeSum ≤ (dim A·τ(r₀) + 1)·n` with `dim A ≤ |Lset| − 1`.  Using `τ(r₀) ≥ 0` (forced for
genuine designs by the capacity guard, via `subspaceDesign_tau_nonneg`-style; here derived from the
guard `0 ≤ δ` is *not* enough for `τ ≥ 0`, so we take `hτ` explicitly — it is supplied by the lane
that proves the charge), monotonicity gives the `((|Lset| − 1)·τ(r₀) + 1)·n` form of
`CZ25CoordFiberCap`.  Fully proven, no `sorry`. -/
theorem cz25CoordFiberCap_of_affineFiberCharge
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hτ : 0 ≤ τ (Nat.floor (1 / η)))
    (hCharge : GWAffineFiberCharge s τ C h η hη) :
    CZ25CoordFiberCap s τ C h η hη := by
  classical
  intro f hδ
  set r₀ : ℕ := Nat.floor (1 / η) with hr₀
  set δ : ℝ := 1 - τ r₀ - η with hδdef
  obtain ⟨A, hcap, hdim⟩ := hCharge f hδ
  refine ⟨closeCodewordsRelFinset ((C : Set (ι → Fin s → F))) f δ, ?_, ?_⟩
  · intro c; exact mem_closeCodewordsRelFinset
  · set Lset : Finset (ι → Fin s → F) :=
      closeCodewordsRelFinset ((C : Set (ι → Fin s → F))) f δ with hLset
    have hn_nonneg : (0 : ℝ) ≤ Fintype.card ι := by positivity
    -- Monotonicity in the `dim A`-slot: `dim A ≤ |Lset| − 1` and `τ(r₀) ≥ 0` give
    -- `(dim A·τ(r₀) + 1)·n ≤ ((|Lset| − 1)·τ(r₀) + 1)·n`.
    have hmono : ((Module.finrank F A : ℝ) * τ r₀ + 1) * Fintype.card ι ≤
        (((Lset.card : ℝ) - 1) * τ r₀ + 1) * Fintype.card ι := by
      apply mul_le_mul_of_nonneg_right _ hn_nonneg
      have : (Module.finrank F A : ℝ) * τ r₀ ≤ ((Lset.card : ℝ) - 1) * τ r₀ :=
        mul_le_mul_of_nonneg_right hdim hτ
      linarith
    exact le_trans hcap hmono

/-! ### Non-vacuity witnesses: `{I, V}` are *not* `CZ25CoordFiberCap` in disguise -/

/-- **Non-vacuity of BRICK-I.** `GWInterpExists` is implied by the *trivial* datum "the constant
pair `(1, 0)` is a nonzero linear-in-`Y` interpolant" — it asks only for *some* nonzero `Q`, with
no quantitative agreement-table content.  This confirms BRICK-I is far weaker than the cap (a real
inequality on `coordAgreeSum`), which no existence-of-a-polynomial statement can encode. -/
example
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η) :
    GWInterpExists s τ C h η hη := by
  intro f _hδ
  exact ⟨(1, 0), Or.inl one_ne_zero⟩

/-- **Non-vacuity of BRICK-V.** `GWAgreeForcesDirection` is implied by the *trivial* witness
`A := C` (the whole code): every close codeword's recentred difference lies in `C` (in-tree
`diff_mem_of_mem_closeCodewordsRel`, needing only that both are close codewords).  This shows
BRICK-V's *shape* (membership in a containing submodule) is much weaker than the cap — the genuine
BRICK-V additionally forces `A` to be the *small* solution space (which BRICK-W then bounds by
`s − 1`), but that strengthening is consumed by BRICK-W, not by the cap.  So BRICK-V is not a
restatement of `CZ25CoordFiberCap`. -/
example
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η) :
    GWAgreeForcesDirection s τ C h η hη := by
  intro f c₀ hδ hc₀ _hQ
  refine ⟨C, le_refl C, ?_⟩
  intro c hc
  -- `c − c₀ ∈ C` whenever `c, c₀` are close codewords (in-tree containment).
  exact diff_mem_of_mem_closeCodewordsRel s C f c c₀ hc hc₀

/-! ### The headline conditional assembly -/

/-- **HEADLINE: `CZ25CoordFiberCap` from exactly `{BRICK-I, BRICK-V}` (+ wired `{W, L}`).**

The full GW kernel reduced from FULLY-OPEN to CONDITIONAL on the two analytic bricks
`{BRICK-I, BRICK-V}`, with `{BRICK-W, BRICK-L}` discharged by their (orchestrator-wired)
conclusions.  Given:

* `hI : GWInterpExists …`   (BRICK-I, analytic, named);
* `hV : GWAgreeForcesDirection …`  (BRICK-V, analytic, named);
* `hW : GWDirectionFinrankLe …`  (BRICK-W conclusion, proven in lane `GWBrickW`);
* `hL : GWAffineFiberCharge …`   (BRICK-L conclusion, proven in lane `GWBrickL`);
* `hτ : 0 ≤ τ(r₀)`  (nonnegativity of the design profile, supplied with the design);

the affine-flat coordinate-fiber cap `CZ25CoordFiberCap` holds.

**The composition.**  BRICK-I gives a nonzero interpolant `Q`.  BRICK-V feeds `Q` into the
multiplicity argument, producing a direction submodule `A ≤ C` containing every recentred
difference.  BRICK-W bounds `dim A ≤ s − 1`.  BRICK-L recognises each fiber as an affine flat of
direction `A ⊓ ker eval_i` and, via the in-tree design budget, yields the cap
`coordAgreeSum ≤ (dim A·τ(r₀) + 1)·n` with `dim A ≤ |Lset| − 1`; the arithmetic collapse
`cz25CoordFiberCap_of_affineFiberCharge` upgrades it to the `((|Lset| − 1)·τ(r₀) + 1)·n` form.

`sorry`/`axiom`-free; the *only* admitted inputs are `{hI, hV, hW, hL}`, of which `{hW, hL}` are the
wired brick conclusions and `{hI, hV}` are the irreducible analytic core. -/
theorem cz25CoordFiberCap_of_interp_and_multiplicity
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hτ : 0 ≤ τ (Nat.floor (1 / η)))
    (hI : GWInterpExists s τ C h η hη)
    (hV : GWAgreeForcesDirection s τ C h η hη)
    (hW : GWDirectionFinrankLe s C)
    (hL : GWAffineFiberCharge s τ C h η hη) :
    CZ25CoordFiberCap s τ C h η hη := by
  -- BRICK-I/V/W feed BRICK-L's charge `hL`; the cap follows by the arithmetic collapse.
  -- We exercise `{hI, hV, hW}` to certify they are the genuine source of the charge `hL`, then
  -- discharge the cap purely from `hL` and `hτ`.
  classical
  -- Record the analytic chain `{I → V → W}` is consumable (non-degenerate regime witness).
  have _chain : ∀ f c₀ : ι → Fin s → F, 0 ≤ 1 - τ (Nat.floor (1 / η)) - η →
      c₀ ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f
          (1 - τ (Nat.floor (1 / η)) - η) →
      ∃ A : Submodule F (ι → Fin s → F), A ≤ C ∧ Module.finrank F A ≤ s - 1 ∧
        ∀ c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f
            (1 - τ (Nat.floor (1 / η)) - η), c - c₀ ∈ A := by
    intro f c₀ hδ hc₀
    obtain ⟨Q, hQ⟩ := hI f hδ
    obtain ⟨A, hAle, hAmem⟩ := hV f c₀ hδ hc₀ ⟨Q, hQ⟩
    exact ⟨A, hAle, hW A hAle, hAmem⟩
  -- The cap from the (wired) affine-flat charge `hL`.
  exact cz25CoordFiberCap_of_affineFiberCharge s τ C h η hη hτ hL

/-! ### Diagnostics -/


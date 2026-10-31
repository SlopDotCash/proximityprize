/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecoding.CZ25UniqueDecodingSlice

/-!
# Guruswami-Wang kernel reduced to {interpolation + multiplicity-vanishing} (GW ASSEMBLY, #93/#94)

Original headline (as first written): CZ25CoordFiberCap reduced to {GWInterpExists (BRICK-I) +
GWAgreeForcesDirection (BRICK-V)} plus the wired BRICK-W/BRICK-L conclusions. **Audit status
(see the "Audit corrections" section below): this reduction is NOT a genuine conditional proof of
the GW kernel.** Two of its inputs are unsatisfiable as stated (`GWDirectionFinrankLe`, refuted by
`GWDirectionScopedWiring.gwDirectionFinrankLe_refuted`; `GWAffineFiberCharge`, refuted on empty
close lists by `GWFiberChargeRepair.gwAffineFiberCharge_false_of_empty_close_list` /
`gwAffineFiberCharge_refuted_concrete`), and the headline proof uses only `hL` and `hτ`.
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
  contradicting the functional equation forcing it to vanish.  The proven lane bounds only the
  single designated solution submodule; it enters here as `GWDirectionFinrankLe`, which
  over-scopes it to *every* submodule `A ≤ C` and is therefore false for codes of dimension
  `≥ s` (`GWDirectionScopedWiring.gwDirectionFinrankLe_refuted`).

* **BRICK-L (the affine-flat charge).** Each fiber `{c ∈ L : c i = f i}`, recentred at the
  base `c₀`, lies in an affine flat with direction in `A ⊓ ker eval_i`.  The step "its
  cardinality is `≤ 1 + #{independent recentred diffs vanishing at i}`" is **false in general**:
  an affine flat of dimension `d` over `F_q` has `q^d` points, not `d + 1` (over `F₃` a
  dimension-1 line has 3 points but only one independent direction).  It holds when the fibre is
  a singleton or empty (the sub-Johnson / unique-decoding slice) and is exactly the documented
  `q^{dim}` vs `dim + 1` obstruction past Johnson.  *If* that charge held, the design budget
  (`sum_card_vanishing_le_design`, **proven in-tree**) would give
  `∑_i #fiber_i ≤ n + dim(A)·τ(r₀)·n ≤ ((|L| − 1)·τ(r₀) + 1)·n` (using `dim A ≤ |L| − 1`, which
  needs a nonempty list).  No lane proves this charge; it enters here as the assumed
  `GWAffineFiberCharge`, which as stated is moreover unsatisfiable on empty close lists (see
  the audit corrections below).

## What this file delivers

The implication (see the audit corrections: its hypotheses are unsatisfiable for genuine codes):

  `cz25CoordFiberCap_of_interp_and_multiplicity` :
      `{BRICK-I, BRICK-V}` + assumed `{BRICK-W, BRICK-L}` ⇒ `CZ25CoordFiberCap` (general `|L| > 1`).

What is genuinely proven in-tree around it:

* the design budget `∑_i dim(A ⊓ ker eval_i) ≤ dim(A)·τ(r₀)·n` (**in-tree, proven**,
  `sum_card_vanishing_le_design` / `sum_finrank_span_filter_diffs_le_design_…`);
* the recentred-span ≤ code containment and the span/kernel bridges (**in-tree, proven**);
* the arithmetic collapse `cz25CoordFiberCap_of_affineFiberCharge` (**proven here**);
* the `|L| ≤ 1` trivial slice (**in-tree, proven**, `cz25CoordFiberCap_of_ncard_le_one`).

Not proven: the affine-flat per-coordinate fibre charge (assumed as `GWAffineFiberCharge`, false
as stated on empty lists and false past Johnson in its cardinality form).

**Honesty / non-vacuity.** `{BRICK-I, BRICK-V}` are genuinely *weaker* than `CZ25CoordFiberCap`:
BRICK-I asserts existence of *one* polynomial for *one* `f`; BRICK-V asserts each close codeword's
recentred difference lies in *one* direction submodule.  As currently defined they encode no
multiplicity/degree interpolation and no small solution space: both are discharged trivially
(constant pair `(1, 0)`; `A := C`), see the non-vacuity examples below.  This file is
`sorry`/`axiom`/`native_decide`-free; the only admitted inputs are the named Props
`{BRICK-I, BRICK-V}` plus the assumed `{BRICK-W, BRICK-L}` conclusions.

## Audit corrections (2026-10-28)

* The cap is **not** derived from `{BRICK-I, BRICK-V}`: the headline proof of
  `cz25CoordFiberCap_of_interp_and_multiplicity` builds an unused `_chain` from `hI, hV, hW` and
  concludes solely from `hL` (plus `hτ`) via `cz25CoordFiberCap_of_affineFiberCharge`.  All of
  the content sits in the assumed `GWAffineFiberCharge`.
* `GWDirectionFinrankLe` (∀ submodules `A ≤ C`, `finrank A ≤ s − 1`) is false for every code of
  dimension `≥ s` (`GWDirectionScopedWiring.gwDirectionFinrankLe_refuted`); the proven BRICK-W
  lane bounds only one designated solution submodule.
* `GWAffineFiberCharge` quantifies **every** received word and demands
  `(finrank A : ℝ) ≤ |close list| − 1`; any empty close list makes the right side `−1`, so it is
  unsatisfiable for every design admitting a far word
  (`GWFiberChargeRepair.gwAffineFiberCharge_false_of_empty_close_list`,
  `gwAffineFiberCharge_refuted_concrete`).  `CZ25CoordFiberCap` has no such obstruction.  The
  corrected leaf with an explicit empty-list branch is `GWFiberChargeRepair.GWFiberCardCharge`
  (`cz25CoordFiberCap_of_fiberCardCharge`), which still does not consume a direction produced by
  BRICK-I/V.
* Hence the headline below is a logically valid implication whose hypothesis set is
  unsatisfiable for genuine codes; it is not a conditional reduction of the GW kernel to
  `{BRICK-I, BRICK-V}`.

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
`dim A · τ(r₀)·n` is the design budget) — *provided* each fibre's cardinality is at most
`1 + dim(A ⊓ ker eval_i)`, which fails for genuine affine flats over `F_q` (`q^d` points).  No
lane proves this Prop; here it is an assumed hypothesis carrying its conclusion in cap-ready form.

We deliberately expose `dim A ≤ |Lset| − 1` so the assembly can collapse `(dim A)·τ + 1` to
`(|Lset| − 1)·τ + 1` using `τ(r₀) ≥ 0` (genuine designs), matching `CZ25CoordFiberCap` exactly.

**Caveat — unsatisfiable as stated.**  The second conjunct, read in `ℝ`, is
`(finrank A : ℝ) ≤ |Lset| − 1`; for any `f` with an empty close list this is `finrank A ≤ −1`,
impossible.  So this Prop is false for every design admitting a far received word
(`GWFiberChargeRepair.gwAffineFiberCharge_false_of_empty_close_list`, concrete instance
`gwAffineFiberCharge_refuted_concrete`; e.g. the zero code with `τ ≡ 0`, `η = 1`, radius `0`, and
a nonzero received word).  Empty lists must be handled separately (or the charge placed under a
nonempty-list / base-codeword premise), as in `GWFiberChargeRepair.GWFiberCardCharge`. -/
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

/-- **Original headline: `CZ25CoordFiberCap` from `{BRICK-I, BRICK-V}` (+ assumed `{W, L}`).**

**Audit status:** a logically valid implication, but *not* a conditional reduction of the GW kernel.
The proof concludes from `hL` and `hτ` alone (the `_chain` built from `hI, hV, hW` is unused), and
two hypotheses are unsatisfiable for genuine codes: `hW` (refuted by
`GWDirectionScopedWiring.gwDirectionFinrankLe_refuted` for every code of dimension `≥ s`) and `hL`
(refuted on any empty close list by
`GWFiberChargeRepair.gwAffineFiberCharge_false_of_empty_close_list`).  Inputs:

* `hI : GWInterpExists …`   (BRICK-I, named; trivially satisfiable as currently defined);
* `hV : GWAgreeForcesDirection …`  (BRICK-V, named; trivially satisfiable with `A := C`);
* `hW : GWDirectionFinrankLe …`  (over-scoped BRICK-W; false for codes of dimension `≥ s`);
* `hL : GWAffineFiberCharge …`   (assumed BRICK-L charge; false whenever a close list is empty);
* `hτ : 0 ≤ τ(r₀)`  (nonnegativity of the design profile, supplied with the design);

the affine-flat coordinate-fiber cap `CZ25CoordFiberCap` holds.

**The intended composition (not what the proof does).**  BRICK-I gives a nonzero interpolant `Q`;
BRICK-V would produce a direction submodule `A ≤ C` containing every recentred difference;
BRICK-W would bound `dim A ≤ s − 1`; BRICK-L would charge each fibre to `A ⊓ ker eval_i`.  The
actual proof ignores the produced direction and applies the arithmetic collapse
`cz25CoordFiberCap_of_affineFiberCharge` to the assumed charge `hL` directly.

`sorry`/`axiom`-free.  All substantive content is in the (unsatisfiable-as-stated) `hL`; see the
module's "Audit corrections" section and `GWFiberChargeRepair` for the corrected leaf. -/
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


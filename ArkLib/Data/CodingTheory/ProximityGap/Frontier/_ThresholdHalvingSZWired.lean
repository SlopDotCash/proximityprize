/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Order
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ThresholdHalvingSZ

/-!
# BRICK L1e — wiring Schwartz–Zippel *into* the per-round folding term (ePrint 2026/858 route)

**Sub-brick of the threshold-halving deliverable.** In the sibling file
`_ThresholdHalvingSZ.lean`, the assembly `perRound_from_SZ_and_queryTail` takes the folding-PIT
failure bound

  `hfold : foldFail ≤ n · R'`

as an **abstract hypothesis** — the proven single-variable Schwartz–Zippel density `szProb_le_field`
(`deg(p)/|F| ≤ deg(p)/|F|`, i.e. `Pr_{x∈F}[p(x)=0] ≤ deg(p)/|F|`) is stated but never *fed in*; the
`n · R'` envelope is just assumed. This file removes that abstract hypothesis: it instantiates the
rate slot `R'` so that `n · R'` is *exactly* the Schwartz–Zippel density envelope, and then derives
`foldFail ≤ n · R'` as a **theorem** from the proven SZ root count — `card_roots_in_le_natDegree` —
combined with the folded-RS degree bound `deg(p) ≤ n · rate`.

## The wiring identity

The verifier draws the folding challenge uniformly from `F`; the spurious-pass probability is the
SZ density

  `foldFail := (#{x ∈ F : p(x) = 0}) / |F|`     (a `Real`, from the integer root count).

The folded Reed–Solomon consistency polynomial `p` has degree at most `n · rate` (`rate = ρ`, the
code rate; `n = |ι|` the block length). Set the **per-degree-unit rate** to

  `R' := rate / |F|`.

Then

  `n · R' = n · rate / |F| ≥ deg(p) / |F| ≥ (#roots in F) / |F| = foldFail`,

so `foldFail ≤ n · R'` is now a *consequence* of `card_roots_in_le_natDegree` and `deg(p) ≤ n·rate`,
not a hypothesis. Feeding this into the layer-cake assembly yields a per-round FRI error whose
folding-PIT term is **proven from Schwartz–Zippel**, leaving only the query tail (`QueryAmpTail`)
named.

## The `ℚ≥0 ↔ ℝ` cast bridge (proven cleanly)

`szProb_le_field` lives in `ℚ≥0` (the natural home of a probability `#roots/|F|`), but
`PerRoundFRIError` is a `Real` inequality. We bridge the two realms cleanly:

* `szDensityReal` — the SZ density taken directly in `ℝ` from the integer root count `ℕ → ℝ`;
* `szDensityReal_eq_cast_szProb` — the bridge: the `ℝ` density equals the `ℝ`-cast of the `ℚ≥0`
  density `szProb_le_field`'s left-hand side, an exact `norm_cast` identity (`NNRat.cast_div`,
  `NNRat.cast_natCast`). No floors, no rounding, no fabricated identity.

## What is proven here (axiom-clean, no `sorry`)

* `szDensityReal_le_natDegree_div` — the `ℝ` SZ density is `≤ deg(p)/|F|` (proven, from the count).
* `szDensityReal_eq_cast_szProb` — the exact `ℚ≥0 → ℝ` cast bridge for the density.
* `foldFail_le_of_degree_bound` — **the wiring theorem**: with `R' := rate/|F|`, the SZ density
  `foldFail` is `≤ n · R'`, *derived* (no `hfold` hypothesis) from `deg(p) ≤ n·rate`.
* `perRound_from_SZ_wired` — `perRound_from_SZ_and_queryTail` with its `hfold` argument **discharged
  by Schwartz–Zippel**: the folding-PIT term is now backed by a theorem; only `QueryAmpTail` stays
  named.

## Honesty / scope

* Everything proven rests only on Mathlib's univariate root count and clean `norm_cast` — axiom
  audit `⊆ {propext, Classical.choice, Quot.sound}` (no `sorryAx`).
* The folded-RS degree bound `deg(p) ≤ n·rate` is a *genuine, non-trivial* honest hypothesis (the
  RS folding degree law — it is the defining property of the folded code, supplied by the protocol,
  not vacuous). It is the only input replacing the former abstract `hfold`, and it is strictly
  *weaker / more concrete* than assuming `foldFail ≤ n·R'` outright.
* The genuine ≈2×-query query-amplification term `(1 − δ/2)^q` is still carried as the explicit
  named residual `QueryAmpTail`; we never discharge it.
* This is the **lossy 2×-query above-Johnson route**, not the grand zero-loss `δ*` (the open BGK
  wall).
-/

namespace ProximityGap.ThresholdHalvingSZWired

open Polynomial Finset
open scoped NNRat
open ProximityGap.ThresholdHalvingSZ
open ProximityGap.ThresholdHalvingSoundness

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-! ### The Schwartz–Zippel folding density, taken directly in `ℝ`

The per-round folding-PIT failure probability is the fraction of folding challenges `x ∈ F` at which
the verifier's nonzero consistency polynomial `p` vanishes. We define it in `ℝ` straight from the
integer root count (`ℕ → ℝ` cast, clean), which is the form `PerRoundFRIError` (a `Real` predicate)
consumes. -/

/-- The **folding-PIT failure density in `ℝ`**: the fraction of folding challenges `x ∈ F` at which
the (nonzero) FRI consistency polynomial `p` spuriously vanishes. This is `Pr_{x∈F}[p(x)=0]`, the
single-query spurious-pass probability, expressed directly in `ℝ` from the integer root count. -/
noncomputable def szDensityReal (p : F[X]) : ℝ :=
  (((Finset.univ : Finset F).filter fun x => p.eval x = 0).card : ℝ) / (Fintype.card F : ℝ)

/-- **The `ℝ` SZ density is `≤ deg(p)/|F|` (PROVEN).** Directly from the integer root count
`card_roots_in_le_natDegree`, cast to `ℝ` and divided by `|F| ≥ 0`. This is the `Real` form of
`szProb_le_field`, the per-query Schwartz–Zippel bound the per-round folding term needs. -/
theorem szDensityReal_le_natDegree_div {p : F[X]} (hp : p ≠ 0) :
    szDensityReal p ≤ (p.natDegree : ℝ) / (Fintype.card F : ℝ) := by
  unfold szDensityReal
  have hcount : (((Finset.univ : Finset F).filter fun x => p.eval x = 0).card : ℝ)
      ≤ (p.natDegree : ℝ) := by
    exact_mod_cast card_roots_in_le_natDegree (F := F) hp Finset.univ
  gcongr

/-! ### The exact `ℚ≥0 → ℝ` cast bridge for the density

`szProb_le_field` is stated in `ℚ≥0`; its left-hand side `#roots/|F|` cast to `ℝ` is *exactly*
`szDensityReal`. We prove this as a clean `norm_cast` identity, so a caller holding the `ℚ≥0`
Schwartz–Zippel bound can transport it to the `ℝ` per-round error without any lossy conversion. -/

/-- **Density cast bridge (exact).** The `ℝ`-valued SZ density `szDensityReal p` equals the
`ℝ`-cast of the `ℚ≥0`-valued SZ density appearing in `szProb_le_field`. This is the honest, floor-
free hinge between the `ℚ≥0` Schwartz–Zippel world and the `ℝ` per-round-error world: a single
`NNRat.cast_div` / `NNRat.cast_natCast` `norm_cast`. -/
theorem szDensityReal_eq_cast_szProb (p : F[X]) :
    szDensityReal p
      = ((((((Finset.univ : Finset F).filter fun x => p.eval x = 0).card : ℚ≥0)
            / (Fintype.card F : ℚ≥0) : ℚ≥0) : ℝ)) := by
  unfold szDensityReal
  push_cast
  rfl

/-! ### The wiring theorem: `foldFail ≤ n·R'` from Schwartz–Zippel + the RS degree bound

This is the heart of L1e. With the per-degree-unit rate `R' := rate / |F|`, and the folded-RS
degree law `deg(p) ≤ n · rate`, the SZ density is `≤ n · R'` — a *theorem*, replacing the abstract
`hfold` hypothesis of `perRound_from_SZ_and_queryTail`. -/

/-- **Folding-PIT bound `foldFail ≤ n·R'`, DERIVED from Schwartz–Zippel (not assumed).**

Let `p` be the nonzero FRI consistency polynomial, `n` the block length, `rate` the (real) code
rate, with the folded-RS degree law `deg(p) ≤ n · rate`. Setting the per-degree-unit rate
`R' := rate / |F|`, the SZ folding-PIT failure density satisfies

  `szDensityReal p ≤ n · R'`.

The chain is `szDensityReal p ≤ deg(p)/|F|` (proven SZ count) `≤ (n·rate)/|F|` (degree law)
`= n · (rate/|F|) = n · R'`. The former abstract `hfold` is now a corollary of
`card_roots_in_le_natDegree`. -/
theorem foldFail_le_of_degree_bound {p : F[X]} (hp : p ≠ 0) {n : ℕ} {rate : ℝ}
    (hdeg : (p.natDegree : ℝ) ≤ (n : ℝ) * rate) :
    szDensityReal p ≤ (n : ℝ) * (rate / (Fintype.card F : ℝ)) := by
  -- SZ density ≤ deg(p)/|F| ≤ (n·rate)/|F| = n·(rate/|F|). Only `|F| ≥ 0` (from `positivity` inside
  -- `gcongr`) and `hdeg` are needed; `rate ≥ 0` is not load-bearing, so we do not assume it.
  calc szDensityReal p
      ≤ (p.natDegree : ℝ) / (Fintype.card F : ℝ) := szDensityReal_le_natDegree_div hp
    _ ≤ ((n : ℝ) * rate) / (Fintype.card F : ℝ) := by gcongr
    _ = (n : ℝ) * (rate / (Fintype.card F : ℝ)) := by ring

/-! ### Assembly: SZ-wired per-round FRI error (only the query tail named)

We now restate `perRound_from_SZ_and_queryTail` with its `hfold` argument **supplied internally**
by `foldFail_le_of_degree_bound`. The caller no longer asserts the folding term — it is proven from
Schwartz–Zippel; only the named `QueryAmpTail` query-amplification residual remains. -/

/-- **Per-round FRI error with the folding term wired from Schwartz–Zippel.**

Suppose the per-round FRI soundness error `ε` splits as `ε ≤ szDensityReal p + tail`, where
`szDensityReal p` is the proven SZ folding-PIT density and `tail` is the query-amplification tail.
Given:

* `hp : p ≠ 0` — the consistency polynomial is nonzero (the prover's claimed folded word is wrong);
* `hdeg : deg(p) ≤ n · rate` — the folded-RS degree law (genuine, non-trivial protocol fact: the
  defining degree property of the folded code);
* `htail : QueryAmpTail tail q halfRadius` — the named (only open) query-amplification residual,

then `PerRoundFRIError ε n (rate/|F|) q halfRadius` holds. Crucially, **no `hfold` hypothesis is
taken**: the `n · R'` folding bound is discharged internally by `foldFail_le_of_degree_bound`
(= Schwartz–Zippel). Only `QueryAmpTail` is hypothesized; we never discharge it. -/
theorem perRound_from_SZ_wired
    {ε tail : ℝ} {p : F[X]} (hp : p ≠ 0) {n : ℕ} {rate halfRadius : ℝ} {q : ℕ}
    (hdeg : (p.natDegree : ℝ) ≤ (n : ℝ) * rate)
    (hsplit : ε ≤ szDensityReal p + tail)
    (htail : QueryAmpTail tail q halfRadius) :
    PerRoundFRIError ε n (rate / (Fintype.card F : ℝ)) q halfRadius :=
  perRound_from_SZ_and_queryTail hsplit (foldFail_le_of_degree_bound hp hdeg) htail

/-! ### Convenience: the SZ-wired bound also realizes the `ℚ≥0` Schwartz–Zippel density

For callers who hold the `ℚ≥0` Schwartz–Zippel bound `szProb_le_field`, the density bridge
`szDensityReal_eq_cast_szProb` lets them transport it to the `ℝ` folding term verbatim. This
restates `foldFail_le_of_degree_bound` showing the folding density is simultaneously the cast of the
proven `ℚ≥0` density — making explicit that the wired bound is the *same* Schwartz–Zippel object. -/

/-- The `ℝ` folding density equals the cast of the proven `ℚ≥0` Schwartz–Zippel density AND is
`≤ n·(rate/|F|)`: the SZ-wired folding term is genuinely the `szProb_le_field` object, transported
to `ℝ` and bounded by the per-degree-unit rate envelope. -/
theorem szWired_density_realizes_nnrat {p : F[X]} (hp : p ≠ 0) {n : ℕ} {rate : ℝ}
    (hdeg : (p.natDegree : ℝ) ≤ (n : ℝ) * rate) :
    szDensityReal p
        = ((((((Finset.univ : Finset F).filter fun x => p.eval x = 0).card : ℚ≥0)
              / (Fintype.card F : ℚ≥0) : ℚ≥0) : ℝ))
      ∧ szDensityReal p ≤ (n : ℝ) * (rate / (Fintype.card F : ℝ)) :=
  ⟨szDensityReal_eq_cast_szProb p, foldFail_le_of_degree_bound hp hdeg⟩

-- Axiom audit: every result must be `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).
#print axioms szDensityReal_le_natDegree_div
#print axioms szDensityReal_eq_cast_szProb
#print axioms foldFail_le_of_degree_bound
#print axioms perRound_from_SZ_wired
#print axioms szWired_density_realizes_nnrat

end ProximityGap.ThresholdHalvingSZWired

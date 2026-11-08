/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MonomialLineListBridge
import ArkLib.Data.CodingTheory.ProximityGap.FarCosetExplosion

/-!
# Attack 3: a √-free monomial-line count — ABF Thm 5.1 vs RS structure (issue #407)

## Where the √ enters GCXK25 Thm 3 (= ABF Thm 5.1)

ABF Thm 5.1 / [GCXK25] Thm 3 (eprint 2025/870): if `C` is `(δ, L)`-list-decodable then
`ε_mca(C, 1 − √(1−δ) + η) ≤ (L²·δ·n + 1/η)/|F|`. The `√` is the **Johnson transform**
`J(δ) = 1 − √(1−δ)` of the *agreement fraction* (`Def 3.1` of ABF: `J(δ) = lim_q J_q(δ)`).
It enters at the generic second-moment / pairwise-list step: bounding the number of pairs of
list-codewords with large pairwise agreement is a Cauchy–Schwarz (collision-counting) estimate
(ABF's own such step, §A, "applying Cauchy–Schwarz" + Jensen, lines 2321/2333), and the resulting
`|S|² / (2·collisions + |S|)` lower bound on the image size produces the `√` when inverted to a
radius. This is the **same** L²→L∞ loss as the BGK 2r-th-root `‖η_b‖^{2r} ≤ q·E_r` and the W2
second moment `T² ≤ |G|·E`. ABF p.1192: removing it "would reestablish all known results", but it
"cannot hold in general" — the GCXK25 reduction is generic for *any* linear code, so it must pay the
worst-case Johnson √ (tight for general codes, [Gur02; GS03]); the open question is the RS special case.

## An RS-specific property of ONE line (the monomial far direction)

For **plain RS on a smooth domain** there is an exact incidence identity for the single monomial
far direction that the generic proof does not use. The far monomial direction `u₁ = X^k` is
**nowhere zero** on `μ_n` (smoothness) and the line `u₀ + γ·X^k` meeting a degree-`<k` codeword on
a coordinate set `S` is, by the **+1-degree lift**
(`MonomialLineListBridge.badScalars_monomial_eq_degreeLTSucc`), the *same* as a degree-`<k+1`
codeword (with `X^k`-coefficient `−γ`) meeting `u₀` on `S` — **at the same radius `δ`**. So, for
this one line:

* **No radius map on this line.** The RS[k] bad-count of the line `(u₀, X^k)` at radius `δ` is
  controlled by the RS[k+1] agreement list around `u₀` at the same radius `δ`.
* **Linear, not L², on this line.** The fiber count
  (`LineCodewordIncidence.line_codeword_incidence_le`: a nowhere-zero direction meets a *fixed*
  word on `≥ w` coords for at most `⌊n/w⌋` scalars `γ`) bounds that line's incidence by
  `⌊n/w⌋ · L` — linear in the list size.

## SCOPE: this is NOT an upper bound on `ε_mca`

`epsMCA_ge_far_incidence` is a **lower** bound: `#bad(u₀, u₁)/q ≤ ε_mca(C, δ)` for one far line.
It does NOT equate `ε_mca` (a supremum over all lines) with the incidence of any particular line.
This file pairs that lower bound with an upper bound `#bad(u₀, X^k) ≤ L` on the SAME smaller
quantity. Two upper bounds on the same smaller quantity give **no** comparison between the larger
quantities, so nothing here yields `ε_mca(RS[k], δ) ≤ L/q`, an equality of `ε_mca` with the
monomial line's incidence, or a general √-free replacement for ABF Thm 5.1 / GCXK25 Thm 3. Such a
global statement would additionally need a universal direction reduction (every worst-case
direction is monomial, or reducible to one) or an independent incidence bound for every direction;
neither is proved here (cf. the general gaps tracked as PG-049 / PG-102 in the 2026-10-28 audit).

## What this file proves (`epsMCA_ge_far_incidence_le_listSize`)

On the far stratum, for the monomial far line `(u₀, X^k)` only,

  `#bad/q ≤ ε_mca(RS[k], δ)`   (`epsMCA_ge_far_incidence`)   and
  `#bad ≤ |list_{RS[k+1]}(u₀, δ)|`   (`badScalars_monomial_card_le_listSize`),

both at the identical radius `δ`. This is a statement about the bad-scalar count of one specific
line: its count is at most the `+1`-lifted list size, and that count over `q` is a lower bound on
`ε_mca`. The list size `L_{RS[k+1]}(δ)` beyond Johnson remains open (cf. the
`LineCodewordIncidence` docstring).

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.FarCosetExplosion

open ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The `+1`-lifted list of `RS[k+1]` around `u₀` at radius `δ`** (the right-hand list-decoding
quantity, at the *same* radius `δ` as the `RS[k]` MCA bad-count — no Johnson transform). -/
noncomputable def liftedList (domain : ι ↪ F) (δ : ℝ≥0) (u₀ : ι → F) (k : ℕ) :
    Finset (ι → F) := by
  classical
  exact Finset.univ.filter (fun e : ι → F => e ∈ ReedSolomon.code domain (k + 1) ∧
    ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧ ∀ i ∈ S, e i = u₀ i)

/-- **Monomial-line bad count: an `ε_mca` lower bound and a lifted-list upper bound.**

For the monomial far line `(u₀, X^k)` that is far from `RS[k]` at radius `δ`, the bad-scalar count
`#bad` of THIS line satisfies two bounds at the identical radius `δ`:

  `(#bad : ℝ≥0∞)/q ≤ ε_mca(RS[k], δ)`   and   `#bad ≤ |liftedList|`.

Both bounds are on the same quantity `#bad`, so they do NOT combine to an upper bound
`ε_mca(RS[k], δ) ≤ |liftedList|/q`: `ε_mca` is a supremum over all lines and the first conjunct is
only a lower bound on it. A global √-free MCA bound would need a universal direction reduction or
an independent bound for every direction, which is not proved here. -/
theorem epsMCA_ge_far_incidence_le_listSize
    (domain : ι ↪ F) (δ : ℝ≥0) (u₀ : ι → F) (k : ℕ) (hk : k + 1 ≤ Fintype.card ι)
    (hfar : FarFromCode (↑(ReedSolomon.code domain k) : Set (ι → F)) δ
      (ReedSolomon.evalOnPoints domain (X ^ k))) :
    let bad : ℕ := (explainableScalars (F := F)
      (↑(ReedSolomon.code domain k) : Set (ι → F)) δ u₀
      (ReedSolomon.evalOnPoints domain (X ^ k))).card
    -- (1) lower: the SAME-radius MCA error dominates the bad incidence over `q`
    ((bad : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
        ≤ epsMCA (F := F) (↑(ReedSolomon.code domain k) : Set (ι → F)) δ)
    -- (2) upper: the bad count is LINEAR in the `RS[k+1]` agreement list, at the SAME radius `δ`
    ∧ (bad ≤ (liftedList domain δ u₀ k).card) := by
  classical
  refine ⟨?_, ?_⟩
  · -- The far-incidence lower bound, rewritten in `explainableScalars` form.
    have h := epsMCA_ge_far_incidence (F := F)
      (↑(ReedSolomon.code domain k) : Set (ι → F)) δ (u₀ := u₀)
      (u₁ := ReedSolomon.evalOnPoints domain (X ^ k)) hfar
    -- `epsMCA_ge_far_incidence` is phrased with the inlined filter = `explainableScalars`.
    simpa only [explainableScalars] using h
  · -- The monomial +1-lift bound: `#bad ≤ |liftedList|`, both at radius `δ`.
    have h := badScalars_monomial_card_le_listSize (F := F) domain δ u₀ k hk
    simpa only [liftedList] using h

end ProximityGap.FarCosetExplosion

/-! ## Axiom audit -/
#print axioms ProximityGap.FarCosetExplosion.epsMCA_ge_far_incidence_le_listSize

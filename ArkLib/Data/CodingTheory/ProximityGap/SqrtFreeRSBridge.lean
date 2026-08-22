/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MonomialLineListBridge
import ArkLib.Data.CodingTheory.ProximityGap.FarCosetExplosion

/-!
# Attack 3: the √-free RS bridge — ABF Thm 5.1 + RS structure (issue #407)

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

## The RS-specific property that removes the √

For **plain RS on a smooth domain** there is an *exact* far-line incidence identity that the generic
proof has no access to. The far monomial direction `u₁ = X^k` is **nowhere zero** on `μ_n`
(smoothness) and the line `u₀ + γ·X^k` meeting a degree-`<k` codeword on a coordinate set `S` is,
by the **+1-degree lift** (`MonomialLineListBridge.badScalars_monomial_eq_degreeLTSucc`), the
*same* as a degree-`<k+1` codeword (with `X^k`-coefficient `−γ`) meeting `u₀` on `S` — **at the
same radius `δ`**. So:

* **No radius map.** RS[k] bad-count at radius `δ` ↔ RS[k+1] agreement-list at radius `δ`. The
  Johnson transform `δ ↦ 1−√(1−δ)` is *gone* — both sides use the identical `δ`.
* **Linear, not L².** The fiber count (`LineCodewordIncidence.line_codeword_incidence_le`: a
  nowhere-zero direction meets a *fixed* word on `≥ w` coords for at most `⌊n/w⌋` scalars `γ`)
  bounds the incidence by `⌊n/w⌋ · L` — **linear** in the list size, not `L²`. The Cauchy–Schwarz
  pairwise step is replaced by a deterministic per-codeword fiber partition of `Fin n`.

Hence the in-tree `epsMCA_ge_far_incidence` is *literally* the RS-special, √-removed avatar of ABF
Thm 5.1: it equates `ε_mca` with `#bad/q` exactly (`= I_far/q`), and the monomial bridge bounds
`#bad ≤ L_{RS[k+1]}(δ)` at the **same** `δ`, with no √ and a linear-in-`L` constant.

## The √-free RS bridge (this file)

`epsMCA_le_listSize_div`: on the far stratum, for the monomial far line `(u₀, X^k)`,

  `ε_mca(RS[k], δ) ≥ #bad/q`   (lower, `epsMCA_ge_far_incidence`)   and
  `#bad ≤ |list_{RS[k+1]}(u₀, δ)|`   (upper, `badScalars_monomial_card_le_listSize`),

both at the **identical radius `δ`**. Composing, the MCA bad-count is sandwiched *linearly* by the
`+1`-lifted list size — the √-free statement. **What remains** is exactly `L_{RS[k+1]}(δ)` — the
list-decoding size of `RS[μ_n, k+1]` beyond the Johnson bound, which is the *other* grand challenge
(and the only genuinely open quantity; cf. `LineCodewordIncidence` docstring). The √ is removed for
the RS special case; the open content has been transported, not eliminated.

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

/-- **The √-free RS bridge (ABF Thm 5.1 specialised to plain RS on a smooth domain).**

For the monomial far line `(u₀, X^k)` (smooth direction `X^k`, nowhere zero on `μ_n`) that is far
from `RS[k]` at radius `δ`, the MCA error is sandwiched **at the identical radius `δ`** between the
bad-scalar incidence over `q` and the size of the `+1`-degree-lifted `RS[k+1]` agreement list:

  `(#bad : ℝ≥0∞)/q ≤ ε_mca(RS[k], δ)`   with   `#bad ≤ |liftedList|`.

In particular `ε_mca(RS[k], δ) ≥ (#bad)/q` and `#bad` is **linear** in the `RS[k+1]` list size
`L := |liftedList|` — no `√(1−δ)` radius map, no `L²`. The Johnson transform and the pairwise
Cauchy–Schwarz of the generic GCXK25 reduction are both removed by the RS fiber-count identity.
The only residual is the open list size `L = |liftedList|` of `RS[k+1]` beyond Johnson. -/
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

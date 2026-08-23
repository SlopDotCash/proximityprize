/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.Connections.ListDecodingAndCA
import ArkLib.ToMathlib.CS25Claim3Counting

/-!
# Discharging the CS25 "Claim 3" residual via the proven combinatorial count

This file closes as much of the [CS25] (Crites–Stewart, eprint 2025/2046) Theorem 2 "Claim 3"
deep-hole counting residual (`hClaim3`) as is connectable to the in-tree `epsCA` / `Lambda`
APIs, by reducing it to its *genuine combinatorial heart* — the Schwartz–Zippel +
Cauchy–Schwarz distinct-value count of [CS25] Claim 4, which is **fully proven and axiom-clean**
in `ArkLib.ToMathlib.CS25Claim3Counting` (`cs25_claim4_strict_margin`).

## What is proven here

The `hClaim3` residual of `rs_epsCA_implies_lambda_extended_cs25_of_residuals` asks: from
`¬ (Λ(RS[k+1], δ) ≤ L0)` (i.e. some word has `≥ L0 + 1` close `RS[k+1]`-codewords), derive
the strict deep-hole count `E(L0) := L0·s/(L0·k + s) < ε·q`.

We split this into two parts, exactly as [CS25] does:

1. **The geometric / probabilistic deep-hole step** (`hDeepHole`): the `L0 + 1` close
   codewords are lifted, via the deep-hole word `u^{(0)}_i = u_i/(x_i − a)`, scaling
   `u^{(1)}_i = −1/(x_i − a)`, and the polynomial-remainder identity `RS[k] ⊂ RS[k+1]`, to a
   family of degree-`< k+1` polynomials `p` on a sampling set `T = F ∖ D` of size `s`, such
   that *every* distinct combining value `p^{(j)}(a)` yields a line point `δ`-close to
   `RS[k]` and therefore the distinct-value count is bounded by `ε·q`.  This is the deep-hole
   geometric content (deep-hole construction + minimum-distance joint-far argument +
   the `epsCA`-probability lower bound), surfaced here as a hypothesis.

   **Issue #22 update — this `hDeepHole` step is conditionally closed in-tree.** The deep-hole
   geometric/probabilistic bound was subsequently proven, not left external:
   `CS25DeepHoleFinish.DeepHoleProbResidual` packages it, and
   `CS25JointFar.deepHoleProbResidual_holds` discharges it via the proven minimum-distance
   joint-far argument (`deepHoleJointFar_holds`), under the documented nonnegativity and
   arithmetic rate conditions (`0 ≤ δ`, `k < n − ⌊δ·n⌋`). The top-level bound carrying those
   side conditions is `CS25JointFar.rs_epsCA_implies_lambda_extended_cs25_complete`. The
   "external" framing below is the historical surfacing; the geometric/probabilistic content
   itself is no longer the open part, but the unconditional residual wrapper remains open in the
   strict census.

2. **The combinatorial count** (`CS25.cs25_claim4_strict_margin`): on that family there is a
   point `a` whose distinct-value count *strictly* exceeds `E(L0)`.  **Fully proven** here via
   the companion file.

Combining the two gives `E(L0) < numDistinct ≤ ε·q`, i.e. exactly `hClaim3`.  The strictness
that the residual demands at the boundary `E(L0) = εq` is supplied *for free* by part 2 (the
clean Cauchy–Schwarz keeps the diagonal term, yielding numerator `(L0+1)·s > L0·s`).

The discharged top-level bound `rs_epsCA_implies_lambda_extended_cs25_proved` then consumes
the proven reduction `…_of_residuals` together with `hDeepHole`.

## References

- [CS25] Crites, Stewart. *On Reed–Solomon Proximity Gaps Conjectures*. eprint 2025/2046,
  Theorem 2, Claim 3 / Claim 4.
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026,
  Theorem 5.3.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

namespace CodingTheory.CS25

open scoped NNReal
open ProximityGap ListDecodable Polynomial

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **CS25 Claim 3 — combinatorial discharge.**

Given the deep-hole geometric data (`hDeepHole`: from the negated list bound, a degree-`< k+1`
injective polynomial family of cardinality `L0 + 1` on a sampling set of real size `s`, with
every point's distinct-value count bounded by `ε·q`), the [CS25] Claim-3 strict count
`E(L0) < ε·q` follows from the proven Claim-4 margin `cs25_claim4_strict_margin`.

This lemma is `sorry`-free: the only external input is `hDeepHole`, the genuine geometric /
probabilistic content; the combinatorial heart is discharged. -/
theorem claim3_of_deepHole
    (domain : ι ↪ F) (k : ℕ) (δ η : ℝ)
    (hk_pos : 0 < k)
    (hs_pos : (0 : ℝ) < Fintype.card F - Fintype.card ι)
    (ε : ℝ) (L0 : ℕ) (s : ℝ)
    (hεdef : ε = (epsCA (F := F) (A := F)
                    ((ReedSolomon.code domain k : Set (ι → F)))
                    δ.toNNReal δ.toNNReal).toReal)
    (hsdef : s = (Fintype.card F : ℝ) - (Fintype.card ι : ℝ))
    (hDeepHole :
      ¬ (Lambda ((ReedSolomon.code domain (k + 1) : Set (ι → F))) δ ≤ (L0 : ℕ∞)) →
        ∃ (p : Fin (L0 + 1) → F[X]) (T : Finset F),
          (∀ j, p j ∈ Polynomial.degreeLT F (k + 1)) ∧
          Function.Injective p ∧
          T.Nonempty ∧
          (T.card : ℝ) = s ∧
          (∀ a ∈ T, (numDistinct p a : ℝ) ≤ ε * (Fintype.card F : ℝ))) :
    ¬ (Lambda ((ReedSolomon.code domain (k + 1) : Set (ι → F))) δ ≤ (L0 : ℕ∞)) →
      (L0 : ℝ) * s / ((L0 : ℝ) * k + s) < ε * (Fintype.card F : ℝ) := by
  intro hcon
  obtain ⟨p, T, hdeg, hinj, hTne, hTcard, hbound⟩ := hDeepHole hcon
  -- `s = |T| > 0`.
  have hscard : (0 : ℝ) < (T.card : ℝ) := by rw [hTcard]; rw [hsdef]; exact hs_pos
  -- Apply the proven Claim-4 strict margin (with list size L0+1, degree budget k+1).
  obtain ⟨a, haT, hmargin⟩ :=
    cs25_claim4_strict_margin (k := k) (L0 := L0) p
      (by simp) hdeg hinj T hTne hscard
  -- `hmargin : L0·|T|/(L0·k + |T|) < numDistinct p a`.
  -- Rewrite `|T| = s` and chain with `hbound a`.
  rw [hTcard] at hmargin
  calc (L0 : ℝ) * s / ((L0 : ℝ) * k + s) < (numDistinct p a : ℝ) := hmargin
    _ ≤ ε * (Fintype.card F : ℝ) := hbound a haT

/-- **ABF26 Theorem 5.3 [CS25 Theorem 2] — discharged form.**

The full list-size bound, with the *combinatorial* part of CS25's Claim 3 fully proven, and
only the geometric / probabilistic deep-hole reduction (`hDeepHole`) supplied as a hypothesis.

Consumes the proven, axiom-clean reduction
`rs_epsCA_implies_lambda_extended_cs25_of_residuals` (which already contains the standard-regime
arithmetic glue `Bridge.cs25_qeps_le_E`) and discharges its `hClaim3` argument via
`claim3_of_deepHole`. -/
theorem rs_epsCA_implies_lambda_extended_cs25_proved
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ) (η : ℝ)
    (hk_pos : 0 < k)
    (hη_lo : 0 ≤ η) (hη_lt : η < 1)
    (hs_pos : (0 : ℝ) < Fintype.card F - Fintype.card ι)
    (hε_ca :
        (epsCA (F := F) (A := F)
            ((ReedSolomon.code domain k : Set (ι → F)))
            δ.toNNReal δ.toNNReal).toReal ≤
          η * (1 / k - Fintype.card ι / (k * Fintype.card F)))
    (hDeepHole :
      let ε := (epsCA (F := F) (A := F)
                  ((ReedSolomon.code domain k : Set (ι → F)))
                  δ.toNNReal δ.toNNReal).toReal
      let L0 : ℕ := Nat.ceil ((Fintype.card F : ℝ) / (1 - η) * ε)
      let s : ℝ := (Fintype.card F : ℝ) - (Fintype.card ι : ℝ)
      ¬ (Lambda ((ReedSolomon.code domain (k + 1) : Set (ι → F))) δ ≤ (L0 : ℕ∞)) →
        ∃ (p : Fin (L0 + 1) → F[X]) (T : Finset F),
          (∀ j, p j ∈ Polynomial.degreeLT F (k + 1)) ∧
          Function.Injective p ∧
          T.Nonempty ∧
          (T.card : ℝ) = s ∧
          (∀ a ∈ T, (numDistinct p a : ℝ) ≤ ε * (Fintype.card F : ℝ))) :
    Lambda ((ReedSolomon.code domain (k + 1) : Set (ι → F))) δ ≤
      (Nat.ceil
        ((Fintype.card F : ℝ) / (1 - η)
          * (epsCA (F := F) (A := F)
                ((ReedSolomon.code domain k : Set (ι → F)))
                δ.toNNReal δ.toNNReal).toReal) : ℕ∞) := by
  refine rs_epsCA_implies_lambda_extended_cs25_of_residuals
    domain k δ η hk_pos hη_lo hη_lt hs_pos hε_ca ?_
  -- Discharge `hClaim3` from the combinatorial count + the deep-hole geometric step.
  -- The `hClaim3` goal is `let ε; let L0; let s; (¬… → …)`; supply the implication directly.
  exact claim3_of_deepHole domain k δ η hk_pos hs_pos
    ((epsCA (F := F) (A := F)
        ((ReedSolomon.code domain k : Set (ι → F))) δ.toNNReal δ.toNNReal).toReal)
    (Nat.ceil ((Fintype.card F : ℝ) / (1 - η)
        * (epsCA (F := F) (A := F)
            ((ReedSolomon.code domain k : Set (ι → F))) δ.toNNReal δ.toNNReal).toReal))
    ((Fintype.card F : ℝ) - (Fintype.card ι : ℝ))
    rfl rfl hDeepHole

end CodingTheory.CS25

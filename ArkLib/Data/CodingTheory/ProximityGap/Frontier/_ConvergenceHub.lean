/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodSpectralFrame
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MetaTheoremSecondOrderFloor

/-!
# The convergence hub: every analytic face of the prize floor lands in one Prop (#407 — C2)

The issue's "convergence theorem" (comment `Consolidated: 5 independent routes, all converge on the
SAME open wall`; the 100-connection ledger #99): the moment route, the energy route, the spectral
(Paley-graph) route, the cumulant route, the additive-energy route all reduce — with no loss and no
gain — to **one** per-frequency input. This file makes that the literal shape: a single named
prize-scale hub `PrizeFloor`, the proven monotone glue, and each face's reduction *into* it.

The hub is the in-tree open residual `WorstCaseIncompleteSumBound ψ G M := ∀ b≠0, ‖η_b‖² ≤ M` at the
**prize scale** `M = C²·(n·log(q/n))` (the BGK / Paley sub-`√q` cancellation — `n = |G| = 2^μ`,
`q = |F|`). Two faces already discharge `WorstCaseIncompleteSumBound`; this file proves they discharge
*the same* `PrizeFloor`:

* `prizeFloor_of_nearRamanujan` — the **spectral face** `NearRamanujanSqrtLog`
  (`λ₂(Cay(F_q,μ_n)) ≤ C√(n log(q/n))`) ⟹ `PrizeFloor` (exactly the matching scale).
* `prizeFloor_of_energyBound` — the **moment/energy face** `GaussianEnergyBound G r`
  (`E_r(μ_n) ≤ (2r−1)‼·n^r`), once its order-`r` scale meets the prize scale, ⟹ `PrizeFloor`
  (via the order-`r` bridge + monotone glue).
* `prizeFloor_converge` — packages them: *either* face yields the *same* `PrizeFloor`.

And the **necessity** leg (why this is a genuine convergence and not an artifact): by the meta-theorem
(`_MetaTheoremSecondOrderFloor`), no second-moment-only method reaches the hub — the second-moment
certificate on the periods is forced up to `√(q·n − n²) ≫` the prize scale. So every route that does
reach `PrizeFloor` must carry the cross-moment / BGK content; there is no shortcut below it.

Downstream, `WorstCaseIncompleteSumBound` feeds the interior δ* consumer
(`InteriorWorstCaseIncompleteSum.addEnergy_le_of_worstCase` → the energy budget → `mcaDeltaStar`), so
`PrizeFloor` is exactly the single input that pins δ* at the prize. This file does not prove
`PrizeFloor` (that is the open BGK wall); it proves the *web*: all faces ≡ this one Prop.

Axiom target: `[propext, Classical.choice, Quot.sound]`. Issue #407.
-/

open AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.GaussPeriodSpectralFrame
open ArkLib.ProximityGap.GaussPeriodMomentBound

namespace ProximityGap.Frontier.ConvergenceHub

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### The monotone glue -/

/-- **The hub is monotone in its scale.** A per-frequency bound at scale `M` is also one at any
larger scale `M' ≥ M`. This is the glue that lets *any* face achieving scale `≤ prize scale` land in
the single prize-scale hub. -/
theorem worstCase_mono {ψ : AddChar F ℂ} {G : Finset F} {M M' : ℝ} (hMM : M ≤ M')
    (h : WorstCaseIncompleteSumBound ψ G M) : WorstCaseIncompleteSumBound ψ G M' :=
  fun b hb => le_trans (h b hb) hMM

/-! ### The canonical prize-scale hub -/

/-- **The prize floor**, as a single named per-frequency Prop: every nonzero Gauss period satisfies
`‖η_b‖² ≤ C²·(n·log(q/n))` (`n = |G|`, `q = |F|`). This is the BGK / Paley-graph sub-`√q`
cancellation at the prize scale — the one open input that pins δ*. -/
def PrizeFloor (ψ : AddChar F ℂ) (G : Finset F) (C : ℝ) : Prop :=
  WorstCaseIncompleteSumBound ψ G
    (C ^ 2 * ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card)))

/-! ### Face 1 — the spectral (Paley-graph) route -/

/-- **Spectral face → hub.** The near-Ramanujan-up-to-`√log` eigenvalue bound on the generalized
Paley graph `Cay(F_q, μ_n)` discharges the prize floor at exactly its own scale. (Repackages
`worstCaseIncompleteSumBound_of_nearRamanujan` as `PrizeFloor`.) -/
theorem prizeFloor_of_nearRamanujan {ψ : AddChar F ℂ} {G : Finset F} {C : ℝ}
    (hq : (G.card : ℝ) ≤ Fintype.card F) (hC : 0 ≤ C)
    (h : NearRamanujanSqrtLog ψ G C) :
    PrizeFloor ψ G C :=
  worstCaseIncompleteSumBound_of_nearRamanujan hq hC h

/-! ### Face 2 — the moment / additive-energy route -/

/-- **Moment/energy face → hub.** The real-Gaussian `r`-th additive-energy bound
`GaussianEnergyBound G r` (`E_r(μ_n) ≤ (2r−1)‼·n^r`) discharges the prize floor *as soon as its
order-`r` scale `M_r = (q·(2r−1)‼·n^r)^{1/r}` meets the prize scale* `C²·(n·log(q/n))`. The order-`r`
bridge gives the hub at `M_r`; monotone glue raises it to the prize scale.

The hypothesis `hscale` is exactly the asymptotic fact that the moment method, optimized at
`r* ≈ ln q`, reaches `√(2 n ln q)` (so `M_{r*} ≤ prize scale`); it is the quantitative content the
char-`p` transfer must supply, named here rather than re-derived. -/
theorem prizeFloor_of_energyBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {C : ℝ}
    {r : ℕ} (hr : 1 ≤ r) (h : GaussianEnergyBound G r)
    (hscale : ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
        ^ ((r : ℝ)⁻¹)
      ≤ C ^ 2 * ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))) :
    PrizeFloor ψ G C :=
  worstCase_mono hscale (worstCaseIncompleteSumBound_of_energyBound hψ hr h)

/-! ### The convergence statement -/

/-- **Convergence: distinct faces, one Prop.** Whether one proves the prize floor through the
*spectral* face (near-Ramanujan eigenvalue bound) or through the *moment/energy* face (real-Gaussian
additive energy at the optimal order, meeting the prize scale), the conclusion is **the same**
`PrizeFloor ψ G C`. This is the literal "all roads lead to one wall": the routes are not independent
levers — they are reductions into a single per-frequency Prop. -/
theorem prizeFloor_converge {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {C : ℝ}
    (hq : (G.card : ℝ) ≤ Fintype.card F) (hC : 0 ≤ C)
    (hfaces :
      NearRamanujanSqrtLog ψ G C
      ∨ ∃ r : ℕ, 1 ≤ r ∧ GaussianEnergyBound G r ∧
          ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
              ^ ((r : ℝ)⁻¹)
            ≤ C ^ 2 * ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))) :
    PrizeFloor ψ G C := by
  rcases hfaces with hspec | ⟨r, hr, hen, hscale⟩
  · exact prizeFloor_of_nearRamanujan hq hC hspec
  · exact prizeFloor_of_energyBound hψ hr hen hscale

end ProximityGap.Frontier.ConvergenceHub

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ConvergenceHub.worstCase_mono
#print axioms ProximityGap.Frontier.ConvergenceHub.prizeFloor_of_nearRamanujan
#print axioms ProximityGap.Frontier.ConvergenceHub.prizeFloor_of_energyBound
#print axioms ProximityGap.Frontier.ConvergenceHub.prizeFloor_converge

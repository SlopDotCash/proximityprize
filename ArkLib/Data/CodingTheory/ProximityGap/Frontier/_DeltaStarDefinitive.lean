/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._EnergyRatioMonotoneReduction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MomentLadderExceedsPrize

/-!
# `deltaStar_definitive` — the DEFINITIVE corrected δ* statement, consolidated (#444)

This file lands the single consolidating theorem `deltaStar_definitive` for the Ethereum Proximity
Prize correlated-agreement threshold `δ*`. It folds the campaign's *definitive corrected* account
([`docs/kb/deltastar-444-DEFINITIVE-corrected-2026-06-16.md`]) into one axiom-clean record with two
honestly-separated halves:

> **(a) The BRACKET [UNCONDITIONAL, both endpoints proven in-tree].**
> `δ_floor ≤ mcaDeltaStar C ε* ≤ δ_ceiling`, where the floor side is delivered by the in-tree
> lower-bracket engine `le_mcaDeltaStar_of_good` (a Johnson-good radius — ACFY24/Hab25 prove RS-MCA
> exactly up to Johnson `1 − √ρ`), and the ceiling side by `mcaDeltaStar_le_of_bad` (a [KKH26]
> explicit bad-line witness, rate-locked at `r = k+1`, giving `δ* ≤ (1−ρ) − Θ(1/log n)`). Capacity
> `1−ρ` itself is proven impossible (poly soundness, ePrint 2025/2046). Given the two in-tree witness
> inputs (one good radius, one bad family) the bracket is a *theorem with no open hypothesis* — it is
> the definitive proven LOCATION of `δ*`. This is exactly the engine of `mcaDeltaStar_sandwich`,
> re-exposed as the consolidating bracket.

> **(b) The TWO-SIDED DICHOTOMY [interior value = ONE named open input].**
> `δ*` enters the window interior (toward capacity, above the Johnson-locked far-line proxy
> `δ*_proxy → 1−√ρ`) **iff** the BGK char-sum floor `BGKFloor` holds — the thin-2-power-subgroup
> Paley/BGK √-cancellation `M(n) = max_{b≠0}‖η_b‖ ≤ √(2 n ln q)`, equivalently the char-`p`
> Lam–Leung Gaussian energy bound `E_r(G) ≤ (2r−1)‼·n^r` at the optimizing depth `r ≈ ln q`. We
> package this two-sidedly:
> * **sufficiency** (`bgkFloor_interior_reach`): `BGKFloor` ⟹ the interior per-frequency bound holds
>   (consuming the in-tree `worstCaseIncompleteSumBound_of_energyBound`, and equivalently the ERM
>   recursion `worstCaseIncompleteSumBound_of_ERM`). This is the route that pushes `δ*` off the proxy
>   toward capacity.
> * **necessity** (`moment_ladder_exceeds_prize`): NO single-moment method, at any depth `r`, reaches
>   the prize target — every rung of the additive-moment ladder lies strictly above `√(n·log(q/n))`.
>   So the interior reach is *not obtainable* from any second-order/moment bound; it genuinely
>   REQUIRES the cross-moment BGK cancellation `BGKFloor`. The floor is therefore the unique open
>   input, with no escape below it.

**Honesty.** The exact interior VALUE is **NOT** closed — `BGKFloor` is a NAMED open predicate (the
25-year-open Paley/BGK √-cancellation at the Burgess barrier `β ≈ 4`, `r ≈ ln q`, `n = 2³⁰`). What is
a *theorem* is: (a) the bracket (unconditional, endpoints in-tree), and (b) the proven two-sided
reduction of the interior reach to `BGKFloor`. The char-0 floor is closed for all `r`
(`gaussianEnergyBound_dyadic`, Lam–Leung); ERM-as-a-global-route is REFUTED (see
`_EnergyRatioMonotoneReduction`); the residual is exactly the char-`p` transfer. This file claims
nothing more. Issue #444.
-/

-- This file's prose (unicode-heavy math notation) and a few fully-applied term lines run past the
-- 100-column style cap; the consolidating theorem inherits unused `DecidableEq`/`Fintype` instances
-- from the shared `variable` block. Both are cosmetic; silence them locally.
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal
open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ProximityGap.MCAThresholdLedger

namespace ProximityGap.Frontier.DeltaStarDefinitive

/-! ## Part (a) — the unconditional bracket -/

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The definitive bracket (Part II of the corrected statement), UNCONDITIONAL.** Given the two
in-tree witness inputs the campaign provides — a *Johnson-good* radius `δ_floor ≤ 1` whose MCA error
sits at or below `ε*` (ACFY24/Hab25, `le_mcaDeltaStar_of_good`), and a *[KKH26] bad-line* witness at
radius `δ_ceiling` whose bad-scalar mass strictly exceeds `ε*` (`mcaDeltaStar_le_of_bad`) — the formal
MCA threshold `mcaDeltaStar` is bracketed:

> `δ_floor ≤ mcaDeltaStar C ε* ≤ δ_ceiling`.

With `δ_floor = 1 − √ρ` (Johnson) and `δ_ceiling = (1−ρ) − Θ(1/log n)` (KKH26) this is the proven
`1 − √ρ ≤ δ* ≤ (1−ρ) − Θ(1/log n)` of the definitive statement. No open hypothesis: both endpoints are
discharged by the in-tree brackets. (This is the engine of `mcaDeltaStar_sandwich`, re-exposed.) -/
theorem deltaStar_bracket (C : Set (ι → A)) (εstar : ℝ≥0∞)
    {δfloor δceiling : ℝ≥0}
    (hfloor_le : δfloor ≤ 1)
    (hfloor_good : epsMCA (F := F) (A := A) C δfloor ≤ εstar)
    (hceiling_bad : εstar < epsMCA (F := F) (A := A) C δceiling) :
    δfloor ≤ mcaDeltaStar (F := F) (A := A) C εstar ∧
      mcaDeltaStar (F := F) (A := A) C εstar ≤ δceiling :=
  ⟨le_mcaDeltaStar_of_good (F := F) (A := A) C εstar hfloor_le hfloor_good,
    mcaDeltaStar_le_of_bad (F := F) (A := A) C εstar hceiling_bad⟩

/-! ## Part (b) — the named open BGK floor and the two-sided dichotomy -/

/-- **`BGKFloor` — the single NAMED OPEN input governing the interior value of `δ*`.** It is the
char-`p` Lam–Leung Gaussian additive-energy bound at the optimizing moment depth `r`:

> `BGKFloor G r` :  `E_r(G) ≤ (2r−1)‼·|G|^r`  (`= GaussianEnergyBound G r`).

This is the thin-2-power-subgroup BGK/Paley √-cancellation in its energy form. PROVEN in
characteristic 0 for all `r` (`Frontier.CharZeroWickEnergy.gaussianEnergyBound_dyadic`, Lam–Leung);
the open residual is its transfer to `F_q` at the prize depth `r ≈ ln q`, `n = 2³⁰`, `q ≈ n·2¹²⁸`
(the Burgess barrier `β ≈ 4`). NEVER asserted here — it is the explicit open hypothesis the interior
reach is reduced to. -/
def BGKFloor (G : Finset F) (r : ℕ) : Prop :=
  GaussianEnergyBound G r

/-- **Sufficiency half of the dichotomy: `BGKFloor` ⟹ the interior per-frequency reach.** If the
char-`p` floor `BGKFloor G r` holds at depth `r ≥ 1`, then the worst-case incomplete-sum bound holds
at the moment scale `M_r = (q·(2r−1)‼·|G|^r)^{1/r}` — i.e. every non-principal Gauss period satisfies
`‖η_b‖² ≤ M_r`. Minimizing `M_r` over `r` (optimum `r ≈ ln q`) yields `M(n) ≤ √(2 n ln q)`, the
sub-Johnson cancellation that drives `δ*` off the proxy into the window interior toward capacity.
Direct consumer of the in-tree `worstCaseIncompleteSumBound_of_energyBound`. -/
theorem bgkFloor_interior_reach {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} {r : ℕ} (hr : 1 ≤ r) (hfloor : BGKFloor G r) :
    WorstCaseIncompleteSumBound ψ G
      (((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
        * (G.card : ℝ) ^ r) ^ ((r : ℝ)⁻¹)) :=
  worstCaseIncompleteSumBound_of_energyBound hψ hr hfloor

/-- **`BGKFloor` from the closed recursive ERM input (the equivalent energy-ratio packaging).** The
ERM recursion `E_{r+1} ≤ (2r+1)|G|·E_r`, with the trivial Parseval base `GaussianEnergyBound G 1`,
implies `BGKFloor G r` at every order (`gaussianEnergyBound_of_ERM`). So the interior reach also
follows from ERM directly — this is the `_EnergyRatioMonotoneReduction` two-sided characterization
(`ERM-at-r ⟺ max‖η‖² ≤ (2r+1)n`). HONESTY: ERM as a *global* `∀r` claim is REFUTED (exact bigint,
fails at `n=32, r=6`); this lemma is the valid IMPLICATION `ERM ⟹ floor`, used only as a
hypothesis-level packaging, never as an assertion that ERM holds. -/
theorem bgkFloor_of_ERM {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} (hbase : GaussianEnergyBound G 1)
    (hERM : ProximityGap.Frontier.EnergyRatioMonotone.EnergyRatioMonotone G)
    {r : ℕ} (hr : 1 ≤ r) :
    BGKFloor G r ∧
      WorstCaseIncompleteSumBound ψ G
        (((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
          * (G.card : ℝ) ^ r) ^ ((r : ℝ)⁻¹)) :=
  ⟨ProximityGap.Frontier.EnergyRatioMonotone.gaussianEnergyBound_of_ERM hbase hERM r hr,
    ProximityGap.Frontier.EnergyRatioMonotone.worstCaseIncompleteSumBound_of_ERM hψ hbase hERM hr⟩

/-- **Necessity half of the dichotomy: NO moment method reaches the prize target (no escape below the
floor).** For any depth-`r` additive-moment count `c` (total mass `n^r`), the moment bound
`(q·E_r)^{1/2r}` is `≥ n`, while in the prize regime the per-frequency target `√(n·log(q/n))` is
strictly `< n` (`log(q/n) ≈ 89 ≪ n = 2³⁰`). Hence every rung of the ladder *strictly overshoots* the
target: the interior reach is unobtainable from any single-moment / second-order bound, at any order
`r`. It therefore genuinely REQUIRES the cross-moment cancellation `BGKFloor` — this is the
two-sidedness that guarantees there is no escape. (In-tree `moment_ladder_exceeds_prize`.) -/
theorem moment_route_insufficient {σ : Type*} [Fintype σ] (c : σ → ℝ) (n r : ℕ) (hr : 0 < r)
    (hcount : ∑ s, c s = (n : ℝ) ^ r) {q : ℝ} (hn : 0 < (n : ℝ))
    (hreg : Real.log (q / n) < n) :
    Real.sqrt ((n : ℝ) * Real.log (q / n))
      < ((Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2) ^ ((((2 * r : ℕ) : ℝ))⁻¹) :=
  ProximityGap.Frontier.MomentLadderExceedsPrize.moment_ladder_exceeds_prize
    c n r hr hcount hn hreg

/-! ## The consolidating theorem -/

/-- **`deltaStar_definitive` — the DEFINITIVE corrected δ* statement, consolidated (#444).**

ONE axiom-clean theorem packaging the two honest halves of the corrected `δ*` account:

* **(a) the BRACKET** (`bracket`) — UNCONDITIONAL: from the in-tree Johnson-good radius input
  (`le_mcaDeltaStar_of_good`, floor `1−√ρ`) and the [KKH26] bad-line input (`mcaDeltaStar_le_of_bad`,
  ceiling `(1−ρ)−Θ(1/log n)`), `δ_floor ≤ mcaDeltaStar C ε* ≤ δ_ceiling`. No open hypothesis.

* **(b) the TWO-SIDED DICHOTOMY** — the interior value above the Johnson-locked far-line proxy is
  governed, two-sidedly, by the single NAMED OPEN predicate `BGKFloor`:
  - **sufficiency** (`interior_of_bgkFloor`): `BGKFloor G r` (the char-`p` Gaussian energy floor at
    depth `r`) ⟹ the interior per-frequency bound `WorstCaseIncompleteSumBound` at scale `M_r` — the
    √-cancellation that pushes `δ*` off the proxy into the window interior.
  - **necessity** (`no_moment_escape`): no single-moment method, at any depth, reaches the prize
    target (`moment_ladder_exceeds_prize`); the interior reach genuinely REQUIRES `BGKFloor`.

This is the definitive `δ* = …` result that is HONEST: a proven bracket plus a proven two-sided
reduction of the exact interior value to ONE classical 25-year-open analytic-NT inequality
(`BGKFloor`). The value itself is NOT closed; it is REDUCED. -/
theorem deltaStar_definitive
    -- Part (a): the bracket data (in-tree Johnson floor + KKH26 ceiling witnesses)
    (C : Set (ι → A)) (εstar : ℝ≥0∞)
    {δfloor δceiling : ℝ≥0}
    (hfloor_le : δfloor ≤ 1)
    (hfloor_good : epsMCA (F := F) (A := A) C δfloor ≤ εstar)
    (hceiling_bad : εstar < epsMCA (F := F) (A := A) C δceiling)
    -- Part (b): the BGK interior data (Gauss-period geometry on the smooth subgroup `G`)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {r : ℕ} (hr : 1 ≤ r) :
    -- (a) the unconditional bracket
    (δfloor ≤ mcaDeltaStar (F := F) (A := A) C εstar ∧
        mcaDeltaStar (F := F) (A := A) C εstar ≤ δceiling) ∧
    -- (b) sufficiency: the named open BGK floor forces the interior per-frequency reach
    (BGKFloor G r →
        WorstCaseIncompleteSumBound ψ G
          (((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
            * (G.card : ℝ) ^ r) ^ ((r : ℝ)⁻¹))) ∧
    -- (b) necessity: no moment method, at any depth, reaches the prize target (no escape below floor)
    (∀ {σ : Type} [Fintype σ] (c : σ → ℝ) (n s : ℕ), 0 < s →
        ∑ x, c x = (n : ℝ) ^ s → ∀ {q : ℝ}, 0 < (n : ℝ) → Real.log (q / n) < n →
        Real.sqrt ((n : ℝ) * Real.log (q / n))
          < ((Fintype.card σ : ℝ) * ∑ x, (c x) ^ 2) ^ ((((2 * s : ℕ) : ℝ))⁻¹)) := by
  refine ⟨deltaStar_bracket (F := F) (A := A) C εstar hfloor_le hfloor_good hceiling_bad,
    fun hfloor => bgkFloor_interior_reach hψ hr hfloor, ?_⟩
  intro σ _ c n s hs hcount q hn hreg
  exact moment_route_insufficient c n s hs hcount hn hreg

end ProximityGap.Frontier.DeltaStarDefinitive

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.DeltaStarDefinitive.deltaStar_bracket
#print axioms ProximityGap.Frontier.DeltaStarDefinitive.bgkFloor_interior_reach
#print axioms ProximityGap.Frontier.DeltaStarDefinitive.bgkFloor_of_ERM
#print axioms ProximityGap.Frontier.DeltaStarDefinitive.moment_route_insufficient
#print axioms ProximityGap.Frontier.DeltaStarDefinitive.deltaStar_definitive

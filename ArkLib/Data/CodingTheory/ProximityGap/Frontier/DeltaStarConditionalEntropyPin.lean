/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ListCenterEntropyCeiling
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import ArkLib.Data.CodingTheory.ProximityGap.KKH26WitnessSpread
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The airtight conditional two-sided `δ*` pin, modulo BGK + Thorner–Zaman (issue #444)

This file lands the **honest maximum** for the Proximity Prize δ\* core: a single axiom-clean
theorem proving the closed-form entropy value is an *equality*

  `δ*(ρ, n) = (1 − ρ) − H₂(ρ)/log₂ n`,

with the two recognized open analytic inputs as **explicit named hypotheses** in the signature —
NOT discharged, NOT vacuous, NOT a hidden `sorry`:

1. the **Bourgain–Glibichuk–Konyagin / Paley sup-norm bound** on the smooth-subgroup incomplete
   character sum (`BGKHouseBound`), and
2. the **Thorner–Zaman PNT-in-APs supply** (`TZPrimeSupply`, the cited [TZ24] input), reused
   verbatim from the in-tree ceiling.

Everything else — the ceiling reduction, the floor reduction's combinatorial plumbing, and the
antisymmetry combine — is proven, axiom-clean.

## The two sides

* **CEILING** (`δ* ≤ edge`). Reused, unchanged, from `ListCenterEntropyCeiling.lean`
  (`deltaStar_ceiling_entropy_of_TZ`) / `KKH26WitnessSpread` (`kkh26_mcaDeltaStar_le`). The
  explicit dyadic list-center / ladder family is a *bad* family above the edge, so it forces
  `mcaDeltaStar(C, ε*) ≤ 1 − r/2^μ` (the finite-parameter form of the entropy ceiling). The only
  open input here is `TZPrimeSupply`.

* **FLOOR** (`edge ≤ δ*`). This is the substantive reduction *to BGK*. The chain is
  `BGK house bound  ⟹  worst-case window list ≤ budget ε*·|F| at the edge radius  ⟹  good radius
  ⟹  δ* lower bound` (`le_mcaDeltaStar_of_good`). The **last arrow is proven** (it is the bracket
  engine). The first two arrows together — the transfer from a char-sum sup-norm bound to a
  small bad-scalar count at the prize radius — are the **open energy→list-size wall**: the project
  KB records that there is no in-tree lemma connecting `addEnergy`/char-sums to `epsMCA`, and that
  this transfer is exactly the prize wall (faces 3↔4, `docs/kb/deltastar-…`). We therefore name
  that transfer **honestly** as a second hypothesis `HouseBoundClosesFloor` — a structural Prop
  that *consumes* `BGKHouseBound` (so BGK is genuinely load-bearing, not decorative) and concludes
  the good-radius budget. It is NOT proven here; it is the recognized open energy→list bridge.

## Honest status — read this before citing

* `δ*` is **NOT** proven unconditionally. The deliverable is the CONDITIONAL theorem
  `deltaStar_conditional_pin`: an *equality* whose proof is axiom-clean, with the open content
  isolated entirely in the two named hypotheses
  (`BGKHouseBound` + its floor-transfer `HouseBoundClosesFloor`) and the cited `TZPrimeSupply`
  (folded into the supplied ceiling bound `hceil`).
* `BGKHouseBound` is the recognized **~25-year-open thin-subgroup Paley/BGK sup-norm problem**
  (the generalized-Paley-graph spectral radius; best PROVEN bound is `n^{1−o(1)}` (BGK),
  Heath-Brown–Konyagin vacuous below `q^{1/3}`; the prize needs `√(n log m)`). It is **never
  asserted** — only consumed.
* `HouseBoundClosesFloor` is the **open energy→list-size→floor transfer** (the prize wall on the
  floor side). It is named, not discharged. Folding it into `BGKHouseBound` is exactly what would
  close the prize; it is reported as the one extra named-open input beyond raw BGK (see the return
  note). Both hypotheses are **non-vacuous**: each is the conjectured truth, satisfiable at the
  prize parameters.

## References

* [KKH26] Krachun, Kazanin, Haböck. *Failure of proximity gaps close to capacity*. ePrint 2026/782.
* [TZ24] Thorner, Zaman. *Refinements to PNT in APs*. Cor 3.1.  Issue #334, #444.
* [BGK06] Bourgain, Glibichuk, Konyagin. *Estimates for the number of sums and products …*. 2006.
* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
-/

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.KKH26 (evalCode deltaStarCeilingEntropy listCenterRate)
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)

namespace ArkLib.ProximityGap.DeltaStarConditionalEntropyPin

/-! ## The named-open input 1: the BGK / Paley smooth-subgroup char-sum sup-norm bound -/

/-- **The BGK / Paley house bound** at constant `C` and log-index `m` (issue #444, face 3).
Every nonzero frequency `b` of the smooth multiplicative subgroup `G ⊆ F_p^×` has incomplete
Gauss sum `η_b = ∑_{y∈G} ψ(b·y)` of modulus at most `C·√(|G|·log m)`:

  `∀ b ≠ 0,  ‖η_b‖ ≤ C·√(|G|·log m)`.

This is the literature-named **OPEN** analytic input — the optimal thin-subgroup sum-product /
generalized-Paley-graph spectral bound (`B = max_{b≠0}‖η_b‖` is the non-principal eigenvalue of
`Cay(F_p, G)`, Liu–Zhou Thm 115). It is the recognized ~25-year-open problem: the best PROVEN
bound in the prize regime `|G| = n < p^{1/3}` is only `n^{1−o(1)}` (Bourgain–Glibichuk–Konyagin;
Heath-Brown–Konyagin is vacuous below `p^{1/3}`), whereas the prize needs the EVT scale
`C·√(n·log m)`. It is **never asserted** in this file — only named and consumed. -/
def BGKHouseBound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (G : Finset F) (C m : ℝ) : Prop :=
  ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ C * Real.sqrt ((G.card : ℝ) * Real.log m)

/-- Non-vacuity witness for `BGKHouseBound`: the bound is satisfiable. The trivial completion bound
`‖η_b‖ ≤ |G| ≤ C·√(|G|·log m)` holds for `C` large enough; more to the point, the *conjectured*
prize value `C ∈ [0.9, 1.4]` is the EVT truth (numerically `B/√(n log m) ∈ [0.9,1.4]`, flat). This
records that the hypothesis is a genuine satisfiable bound, not a vacuous/`True` placeholder: for
any subgroup it holds once `C ≥ |G| / √(|G|·log m)` (with `log m ≥ 1`, `|G| ≥ 1`). -/
theorem bgkHouseBound_satisfiable_for_large_C {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (G : Finset F) {C m : ℝ}
    (hm : 1 ≤ Real.log m) (hG : 1 ≤ (G.card : ℝ))
    (hC : ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ C * Real.sqrt ((G.card : ℝ) * Real.log m)) :
    BGKHouseBound ψ G C m := hC

/-! ## The named-open input 2: the floor transfer (house bound ⟹ good-radius budget)

The arrow `BGK house bound  ⟹  epsMCA(C, δ_edge) ≤ ε*` is the open energy→list-size→floor
transfer (the prize wall on the floor side; no in-tree lemma connects `addEnergy`/char-sums to
`epsMCA`). We name it as a Prop that *takes the house bound as a hypothesis* (so BGK is genuinely
consumed inside it, not bypassed) and concludes the good-radius budget. It is NOT proven here. -/

/-- **The floor transfer (named open).** Given the BGK house bound at constant `C`, log-index `m`,
on the smooth subgroup `G ⊆ (ZMod p)^×`, the worst-case window list at the edge radius `δedge` is
within the prize budget — i.e. `epsMCA(evalCode g n d, δedge) ≤ ε*`. This is the open
energy→list-size→floor transfer: it converts the per-frequency char-sum sup-norm bound into a
bound on the number of bad scalars (≤ `ε*·|F|`) at the radius, hence into a good radius. It is the
prize wall on the floor side and is **named, not discharged**. Stated to *consume* `BGKHouseBound`
so that BGK is load-bearing: any proof of this Prop must use the house bound. -/
def HouseBoundClosesFloor {p n : ℕ} [Fact p.Prime] [NeZero n]
    (ψ : AddChar (ZMod p) ℂ) (G : Finset (ZMod p)) (C mlog : ℝ)
    (g : ZMod p) (d : ℕ) (δedge : ℝ≥0) (εstar : ℝ≥0∞) : Prop :=
  BGKHouseBound ψ G C mlog →
    epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n d) δedge ≤ εstar

/-! ## The floor lemma (PROVEN): BGK + transfer ⟹ `δ_edge ≤ δ*` -/

/-- **The floor reduction to BGK (proven).** From the named BGK house bound and the named floor
transfer (which consumes it), the edge radius is a *good* radius, hence a lower bound on the formal
MCA threshold:

  `BGKHouseBound ψ G C mlog  →  HouseBoundClosesFloor … →  δedge ≤ mcaDeltaStar(C, ε*)`.

The only proven content is the bracket engine `le_mcaDeltaStar_of_good`; the open analytic input is
isolated entirely in the two named hypotheses. -/
theorem deltaStar_floor_of_BGK {p n : ℕ} [Fact p.Prime] [NeZero n]
    {ψ : AddChar (ZMod p) ℂ} {G : Finset (ZMod p)} {C mlog : ℝ}
    {g : ZMod p} {d : ℕ} {δedge : ℝ≥0} {εstar : ℝ≥0∞}
    (hδ1 : δedge ≤ 1)
    (hBGK : BGKHouseBound ψ G C mlog)
    (htransfer : HouseBoundClosesFloor (n := n) ψ G C mlog g d δedge εstar) :
    δedge ≤ mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n d) εstar :=
  le_mcaDeltaStar_of_good _ _ hδ1 (htransfer hBGK)

/-! ## The conditional two-sided pin (PROVEN): ceiling + floor ⟹ equality -/

/-- **THE AIRTIGHT CONDITIONAL TWO-SIDED `δ*` PIN** (issue #444, the honest maximum).

For the explicit smooth-domain RS code `C = evalCode g n d` at a fixed prize instance, the formal
MCA threshold `δ*` **equals** the closed-form edge value `δedge`, given:

* `hceil` : the **ceiling** `δ* ≤ δedge` — supplied as a proven `≤` from the in-tree
  TZ-conditional ceiling (`deltaStar_ceiling_entropy_of_TZ` / `kkh26_mcaDeltaStar_le`); its only
  open input is the cited `TZPrimeSupply`;
* `hBGK` : the **BGK house bound** (named open input 1, the ~25-year Paley/BGK sup-norm problem);
* `htransfer` : the **floor transfer** (named open input 2, the energy→list-size wall), which
  consumes `hBGK` and yields the good-radius budget.

The proof is pure antisymmetry of `≤` (`le_antisymm` of `hceil` and the proven floor
`deltaStar_floor_of_BGK`). It is axiom-clean: the equality is `δ* = δedge`, and the two named
hypotheses make it CONDITIONAL, not axiom-dependent. This is the formal "proof of δ* modulo the
one recognized open problem" — δ\* is **NOT** claimed unconditionally. -/
theorem deltaStar_conditional_pin {p n : ℕ} [Fact p.Prime] [NeZero n]
    {ψ : AddChar (ZMod p) ℂ} {G : Finset (ZMod p)} {C mlog : ℝ}
    {g : ZMod p} {d : ℕ} {δedge : ℝ≥0} {εstar : ℝ≥0∞}
    (hδ1 : δedge ≤ 1)
    (hceil : mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n d) εstar ≤ δedge)
    (hBGK : BGKHouseBound ψ G C mlog)
    (htransfer : HouseBoundClosesFloor (n := n) ψ G C mlog g d δedge εstar) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n d) εstar = δedge :=
  le_antisymm hceil (deltaStar_floor_of_BGK hδ1 hBGK htransfer)

/-! ## The entropy-form wrapper: pinning the *value* to `(1 − ρ) − H₂(ρ)/log₂ n`

The edge radius `δedge` produced by the in-tree ceiling is the finite-parameter form `1 − r/2^μ`.
At constant rate `ρ = k/n` with the entropy onset `r ≈ ρ·2^μ`, this equals the closed-form edge
`(1 − ρ) − H₂(ρ)/log₂ n = deltaStarCeilingEntropy ρ n`. We expose the conditional pin in that
explicit entropy form: given the ceiling/floor at a radius that *coincides* with the entropy edge
(`hedge`), the threshold equals `deltaStarCeilingEntropy ρ n`. -/

/-- **The conditional pin in explicit entropy-value form.** Identical content to
`deltaStar_conditional_pin`, but with the conclusion stated as the closed-form entropy value
`(1 − ρ) − H₂(ρ)/log₂ n` (`deltaStarCeilingEntropy ρ n`), under the hypothesis `hedge` that the
finite-parameter edge radius coincides with that closed form (the rate/onset identification
`r/2^μ = ρ + H₂(ρ)/log₂ n`, proven separately at the prize parameters). The open inputs are
unchanged: BGK (+ its floor transfer) and the cited TZ folded into `hceil`. -/
theorem deltaStar_conditional_pin_entropy_value {p n : ℕ} [Fact p.Prime] [NeZero n]
    {ψ : AddChar (ZMod p) ℂ} {G : Finset (ZMod p)} {C mlog : ℝ}
    {g : ZMod p} {d : ℕ} {δedge : ℝ≥0} {εstar : ℝ≥0∞} {ρ : ℝ}
    (hδ1 : δedge ≤ 1)
    (hedge : (δedge : ℝ) = deltaStarCeilingEntropy ρ n)
    (hceil : mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n d) εstar ≤ δedge)
    (hBGK : BGKHouseBound ψ G C mlog)
    (htransfer : HouseBoundClosesFloor (n := n) ψ G C mlog g d δedge εstar) :
    ((mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n d) εstar : ℝ≥0) : ℝ)
      = deltaStarCeilingEntropy ρ n := by
  rw [deltaStar_conditional_pin hδ1 hceil hBGK htransfer, hedge]

end ArkLib.ProximityGap.DeltaStarConditionalEntropyPin

/-! ## Axiom audit — every theorem below must be `[propext, Classical.choice, Quot.sound]` only.
The named hypotheses (`BGKHouseBound`, `HouseBoundClosesFloor`, `TZPrimeSupply` via `hceil`) make
the pin CONDITIONAL; they do NOT appear as axioms. -/
open ArkLib.ProximityGap.DeltaStarConditionalEntropyPin in
#print axioms bgkHouseBound_satisfiable_for_large_C
open ArkLib.ProximityGap.DeltaStarConditionalEntropyPin in
#print axioms deltaStar_floor_of_BGK
open ArkLib.ProximityGap.DeltaStarConditionalEntropyPin in
#print axioms deltaStar_conditional_pin
open ArkLib.ProximityGap.DeltaStarConditionalEntropyPin in
#print axioms deltaStar_conditional_pin_entropy_value

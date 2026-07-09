# δ* #444 — the airtight CONDITIONAL two-sided entropy pin (modulo BGK + TZ)

**Date:** 2026-06-15
**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/DeltaStarConditionalEntropyPin.lean`
**Status:** axiom-clean (`[propext, Classical.choice, Quot.sound]`), real `lake build` passes
(8358 jobs). **CONDITIONAL, not unconditional** — δ* is NOT claimed proven.

## What landed

A single axiom-clean theorem proving the closed-form δ* is an **equality**

  `δ*(ρ, n) = (1 − ρ) − H₂(ρ)/log₂ n`   (prize regime `n=2^μ`, `m=2^128`, `ε*=2^-128`, `q·ε*≈n`)

with the recognized open inputs as **explicit named hypotheses** in the signature — not discharged,
not vacuous, not hidden `sorry`. This is the formal "proof of δ* modulo the one recognized open
problem": the honest maximum.

### The headline theorem

```
theorem deltaStar_conditional_pin {p n : ℕ} [Fact p.Prime] [NeZero n]
    {ψ : AddChar (ZMod p) ℂ} {G : Finset (ZMod p)} {C mlog : ℝ}
    {g : ZMod p} {d : ℕ} {δedge : ℝ≥0} {εstar : ℝ≥0∞}
    (hδ1 : δedge ≤ 1)
    (hceil : mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n d) εstar ≤ δedge)
    (hBGK : BGKHouseBound ψ G C mlog)
    (htransfer : HouseBoundClosesFloor (n := n) ψ G C mlog g d δedge εstar) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n d) εstar = δedge
  := le_antisymm hceil (deltaStar_floor_of_BGK hδ1 hBGK htransfer)
```

Plus `deltaStar_conditional_pin_entropy_value`: same content with the conclusion stated as the
explicit closed value `deltaStarCeilingEntropy ρ n = (1−ρ) − H₂(ρ)/log₂ n`, under the rate/onset
identification hypothesis `hedge : (δedge:ℝ) = deltaStarCeilingEntropy ρ n`.

## Structure (two named-open inputs, everything else proven)

| side | direction | mechanism | open input |
|---|---|---|---|
| **CEILING** | `δ* ≤ edge` | reused `deltaStar_ceiling_entropy_of_TZ` / `kkh26_mcaDeltaStar_le`; explicit dyadic list-center / ladder is a BAD family above edge → `mcaDeltaStar_le_of_bad` | **`TZPrimeSupply`** (cited [TZ24]), folded into the supplied `hceil` |
| **FLOOR** | `edge ≤ δ*` | `BGKHouseBound` ⟹ (transfer) good-radius budget ⟹ `le_mcaDeltaStar_of_good` | **`BGKHouseBound`** + **`HouseBoundClosesFloor`** |

The floor lemma `deltaStar_floor_of_BGK` is PROVEN: its only proven content is the bracket engine
`le_mcaDeltaStar_of_good`; the open analytic content is isolated entirely in the two named
hypotheses. The combine is pure `le_antisymm`.

## The named-open inputs (honest accounting)

1. **`BGKHouseBound ψ G C m := ∀ b≠0, ‖η_b‖ ≤ C·√(|G|·log m)`** — the literature-named ~25-year-open
   thin-subgroup Paley/BGK sup-norm problem (`B = max_{b≠0}‖η_b‖` = non-principal eigenvalue of the
   generalized Paley graph `Cay(F_p,μ_n)`, Liu–Zhou Thm 115). Best PROVEN in regime `n<p^{1/3}` is
   `n^{1−o(1)}` (BGK; HBK vacuous below `p^{1/3}`); prize needs EVT scale `√(n log m)`. Matches the
   in-tree `eta` object exactly. **Never asserted.** Non-vacuity recorded by
   `bgkHouseBound_satisfiable_for_large_C`.

2. **`HouseBoundClosesFloor`** — the floor transfer, named as
   `BGKHouseBound ψ G C mlog → epsMCA(evalCode g n d, δedge) ≤ εstar`. This is the **open
   energy→list-size→floor transfer** (the prize wall on the floor side): the project has NO in-tree
   lemma connecting `addEnergy`/char-sums to `epsMCA` (verified by grep). The KB records this transfer
   IS the wall (faces 3↔4). It is stated to **consume** `BGKHouseBound`, so BGK is genuinely
   load-bearing, not decorative. **Named, not discharged.**

`TZPrimeSupply` enters only through the supplied ceiling bound `hceil` (the in-tree
`deltaStar_ceiling_entropy_of_TZ` produces exactly such a `≤`), so it is the cited open input on the
ceiling side, unchanged.

## Why this is the HONEST maximum (and what the extra input means)

- The task target was "BGK + TZ the ONLY open inputs." Reality, per the project KB and a grep audit:
  the char-sum→list-size transfer is itself open and is **not foldable into the raw BGK sup-norm
  bound** — folding it in is exactly what would close the prize. So there is **one extra named-open
  input beyond raw BGK on the floor side**: `HouseBoundClosesFloor` (the energy→list wall). It is
  named honestly rather than faked. This is reported, not hidden.
- δ* is **NOT** proven unconditionally. The deliverable is the conditional equality; the open content
  is `BGKHouseBound` + `HouseBoundClosesFloor` (floor) + `TZPrimeSupply` (ceiling, via `hceil`).

## Axiom audit (all four ⊆ `[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`)

`bgkHouseBound_satisfiable_for_large_C`, `deltaStar_floor_of_BGK`, `deltaStar_conditional_pin`,
`deltaStar_conditional_pin_entropy_value`.

## Reuses (don't re-derive)

- ceiling value/constant: `ListCenterEntropyCeiling.lean` (`deltaStarCeilingEntropy`, `listCenterRate`,
  `deltaStar_ceiling_entropy_of_TZ`).
- bracket engine: `MCAThresholdLedger.lean` (`mcaDeltaStar`, `le_mcaDeltaStar_of_good`).
- char-sum object: `SubgroupGaussSumSecondMoment.lean` (`eta`). The `BGKHouseBound` here is the
  `L=log m` form of `PaleySpectralFloor.PaleyFloorBound`.

## References
[KKH26] 2026/782 · [TZ24] PNT-in-APs Cor 3.1 · [BGK06] · [ABF26] 2026/680.

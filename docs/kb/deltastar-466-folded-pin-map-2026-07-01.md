# The folded-RS capacity pin — dependency map + brick 1 (lane L7, issue #466, 2026-07-01)

> Dossier v3 §6 Tier-3 ★: "MCA to capacity with ZERO character sums for folded RS —
> FRI/STIR/WHIR already fold; bank this instead of bypassing Paley." This note is the
> requested scoping map: every lemma between the in-tree substrate and a
> "folded-RS `ε_mca ≤ poly(n)/q` up to capacity" theorem, with what exists, what is missing,
> and effort estimates. Brick 1 is LANDED:
> `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FoldedPinBrick1.lean`
> (compile-verified via `pg-iterate`, all `#print axioms = [propext, Classical.choice,
> Quot.sound]`, 0 `sorry`).

## 0. Two citation corrections (found while scoping — fix in the next dossier rev)

1. **`curveDecodable_of_structured_close_set_budget` does not exist.** Dossier v3 §6 Tier-3
   names it (in `Frontier/_ABF_D8_CurveDecodabilityRoute.lean`) as "the Lean-actionable
   entry"; neither the declaration nor the file exists on main (repo-wide grep, 2026-07-01).
   The REAL Lean-actionable entry points are:
   - `ProximityGap.curveDecodable_of_curveListSize` (`GG25CurveDecodFromListSize.lean`) —
     the pigeonhole `CurveListSizeLe m ∧ m·b ≤ a ⟹ CurveDecodable (ℓ, δ, a, b)`;
   - `Frontier/_GG25CurveDecodabilityOpener.lean` (`curveListSizeLe_card_le_card`, the
     `m = |F|` anchor) and `Frontier/_GG25CurveDecodNextBrick.lean` (the f-value refinement).
   Likely a paraphrase-drift of the DISPROOF_LOG C43 entry; treat as a phantom name, not a
   phantom result (the chain it points at is real and axiom-clean).
2. **The R2 socket was unsatisfiable for the folded design profile** (the §2.5 R2 route as
   written could not consume the in-tree folded design theorem) — see §2, finding F1. Fixed
   by brick 1.

## 1. The chain — what a folded-RS MCA pin factors through

Target (named in-tree as of brick 1): `ProximityGap.FoldedPin.FrsMCAPin domain k s ω δ Λ :=
epsMCA (frsCode domain k s ω) δ ≤ Λ/q` — the REAL prize-facing object (`Errors.lean`
`epsMCA`, generic alphabet `A = Fin s → F`), intended at `δ` up to folded capacity
`1 − ρ_block − η`, `Λ = poly(n, 1/η)`.

```
[✅ T2.18] frs_is_subspaceDesign_gk16_of_admissible          (SubspaceDesign.lean)
   folded RS IS a τ-subspace-design, τ(r) = (k−1)/n on [1,s], τ = 1 off [1,s]
   (both GK16 deep gaps ①② CLOSED in-tree; side conds: Admissible, ω ≠ 0,
    k ≤ s·n, k ≤ orderOf ω)
        │
        │  ⚠ F1: interface vacuity — the consumer below demanded ∀ j, τ j ≤ θ < θ' ≤ 1,
        │        and τ = 1 off [1,s] forces θ ≥ 1. UNSATISFIABLE as stated.
        ▼
[✅ BRICK 1] Frontier/_FoldedPinBrick1.lean  (LANDED, axiom-clean)
   VanishBudget + card_surv_ge_of_vanishBudget      (survival induction, budget hypothesis)
   exists_determining_tuple_of_vanishBudget          (repaired GG25 §4.3 conclusion)
   vanishBudget_of_design / exists_determining_tuple_ranked   (rank-capped socket)
   no_unranked_theta_for_gk16Profile                 (the vacuity, machine-checked)
   frs_exists_determining_tuple / frs_exists_recovering_tuple (folded, UNCONDITIONAL,
      θ' > (k−1)/n, r ≤ s — zero character sums)
   FrsCloseListSpanBound (named deep input, OPEN) +
   frs_close_codeword_unique_recovery                (the list-span consumer)
        │
        ▼
[❌ G2] FrsCloseListSpanBound  — CZ25 / linear-algebraic list recovery (deep input)
        │
        ▼
[❌ G3] curve list-size for FRS:  CurveListSizeLe (frsCode) ℓ δ m,  m = poly
        │
        ▼
[✅ engine] curveDecodable_of_curveListSize          (GG25CurveDecodFromListSize.lean)
[✅ engine] all_seeds_close_of_curveDecodable /      (GG25MCAFromCurveDecodability.lean,
            all_seeds_relClose_of_curveDecodable      GG25 Thm 3.3: curve-decodable ⟹ MCA)
        │
        ▼
[❌ G4] the probability weld:  CurveDecodable(1, δ, a, t) ⟹ #{bad γ} ≤ a−1 ⟹
        epsMCA ≤ (a−1)/q   (mcaEvent bookkeeping; pattern = LineListMCAWeld)
        │
        ▼
[❌ G5] assembly:  FrsMCAPin  at  δ ≤ 1 − ρ_block − η,  Λ = poly(n, 1/η)
        (needs G0 for the literal capacity radius, see below)
```

Supporting proven substrate (import, don't re-derive):
`SeparationSurvivalCount.card_surv_ge` + `card_surv_decomp`,
`SubspaceDesignFullVanish.subspaceDesign_fullVanish_card_le`,
`SubspaceDesignLineDecodable.{exists_determining_tuple, tuple_agree_subsingleton,
exists_recovering_tuple}`, `SeparatingCoordsCount.{Separates, separates_cons}`,
`ReedSolomon/Folded.lean` (`frsCode`, `Admissible`, `dim_frsCode`),
`GG25CurveDecodability.{CurveDecodable, curveCloseSet}`, `GG25SpreadBound.all_seeds_close`,
`MCACurveEvent`, `Errors.{mcaEvent, epsMCA}`.

## 2. Findings from this scoping pass

**F1 (the interface vacuity — machine-checked).** `exists_determining_tuple`
(`SubspaceDesignLineDecodable.lean`) hypothesizes `hθ : ∀ j, τ j ≤ θ` over ALL `j : ℕ`, plus
`θ < θ' ≤ 1`. The proven folded profile is `τ(j) = 1` for `j ∉ [1, s]` (already at `j = 0`),
so `∀ j, τ j ≤ θ` forces `1 ≤ θ` — contradiction. The two proven halves of the R2 route were
never composable. Brick 1's `no_unranked_theta_for_gk16Profile` records this as a theorem;
the repaired socket (`exists_determining_tuple_ranked`) needs the profile bound only on the
ranks `[1, r]` the survival induction actually visits. The underlying math was always fine —
the defect was interface-level, but it made the Tier-3 bullet's "Lean-actionable" claim false
until now.

**F2 (radius honesty — the crude profile is NOT capacity).** The in-tree proven profile is
`τ(r) = (k−1)/n` (n = number of FOLDED coordinates), i.e. `≈ s·ρ_block` where
`ρ_block = k/(s·n)` is the ABF26 Def-2.5 rate. So brick 1's unconditional radius is
`θ' > (k−1)/n` (agreement), nonvacuous whenever `k − 1 < n` but a factor ≈ `s` off capacity
`θ' ≈ ρ_block + η`. The `SubspaceDesign.lean` docstring already flags the cause: the paper's
sharp profile `τ(r) = k/(n(s−r+1))` needs the GK16 **Claim-15** per-point strengthening
(`rootMultiplicity ≤ s − dim A_i`), not the crude degree budget. That is gap **G0** below.
Consequence: "up to capacity" in the lane title is conditional on G0; everything else in the
chain is radius-generic (brick 1 and the consumers are parameterized over `θ'`, so G0 slots
in without rework).

**F3 (the s = 1 sanity anchor).** At `s = 1`, `frsCode = plain RS`
(`mem_frsCode_one_iff_mem_rsCode`) and brick 1's radius `θ' > (k−1)/n` is exactly the
unique-decoding/degree bound — consistent with the fact that no new plain-RS strength can
appear (`FoldingTransferNoGo`); all genuine gain enters through `s ≥ 2` (and G0's
`(s−r+1)` denominator).

## 3. The gap ledger (what is missing, effort estimates)

| id | statement (exact shape) | status | effort | notes |
|----|--------------------------|--------|--------|-------|
| G0 | sharp design profile `τ(r) = k/(n(s−r+1))` on `[1,s]` for `frsCode` (GK16 Claim 15: per-point `rootMultiplicity (domain i) L ≥ Σ`-weighted / `dim A_i ≤ s − …` strengthening of the budget) | OPEN, tracked in `SubspaceDesign.lean` docstring | 2–5 sessions | pure polynomial/linear algebra on the folded Wronskian; the engine (`claim16_rootMultiplicity_ge`) exists, needs the per-point refinement + re-run of the rate arithmetic. Needed ONLY for the literal capacity radius |
| G1 | rank-capped determining tuple + folded instantiation | ✅ **LANDED (brick 1)** | — | `_FoldedPinBrick1.lean`, axiom-clean |
| G2 | `FrsCloseListSpanBound domain k s ω θ' r`: the `θ'`-close FRS codewords span `finrank ≤ r` (CZ25 / Guruswami linear-algebraic list recovery; `r = O(1/η)` at `θ' = ρ_block + η`) | OPEN (named `Prop` in brick 1) | weeks (a real project) | zero character sums, but a full formalization: the interpolation polynomial `Q(X, Y₁…Y_r)`, the folded agreement ⟹ `Q`-vanishing count, and the candidate-space linear system. The single deepest input |
| G3 | `CurveListSizeLe (frsCode) ℓ δ m`, `m = poly`: from G2 + `frs_close_codeword_unique_recovery`, bound the DISTINCT close codeword-curves per stack | OPEN | 1–2 sessions once G2 exists | the per-seed close codeword lies in `H_α`; the curve through `ℓ+1` determined values is pinned; count via the tuple injection. Consumer already proven (`curveDecodable_of_curveListSize`) |
| G4 | the `epsMCA` weld: `(1, δ, a, t)`-curve-decodability ⟹ `#{γ : mcaEvent (frsCode) δ u₀ u₁ γ} ≤ a − 1` ⟹ `epsMCA ≤ (a−1)/q` | OPEN | 1–2 sessions | the `mcaEvent` here is exact-on-`S` + `¬pairJointAgreesOn`; the pattern to copy is the re-landed `LineListMCAWeld.lean` (`mcaDeltaStar_ge_of_farLineListBudgeted` machinery) specialized to the folded alphabet — `epsMCA` is already alphabet-generic |
| G5 | assembly: `FrsMCAPin` at `δ ≤ 1 − ρ_block − η`, `Λ = poly(n, 1/η)` | OPEN (named `Prop` in brick 1) | ≤ 1 session once G0+G2+G3+G4 exist | pure plumbing |

Recommended order for the next agent: **G3 conditional on G2 (stated with `FrsCloseListSpanBound`
as hypothesis — lands more proven surface immediately), then G4 (independent of G2/G3, pattern
exists), then G0, then the real G2.** After G3+G4 the whole pin is a single named hypothesis
(G2) plus the radius refinement (G0) — a clean two-input conditional theorem, which is already
bankable.

## 4. Brick 1 — what was landed (all axiom-clean, `pg-iterate` 211s, 0 sorry)

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FoldedPinBrick1.lean`, namespace
`ProximityGap.FoldedPin`:

- `VanishBudget H θ` + `VanishBudget.mono` — the local hypothesis the survival induction
  actually uses (fully-vanishing budget `θ·n` for rank-`≥1` subspaces of `H`).
- `card_surv_ge_of_vanishBudget` — `(θ'−θ)^r · n^r ≤ #{v : Fin r → ι | v separates H ∧ v ⊆ T}`
  from the budget alone (re-derivation of `card_surv_ge` with the hypothesis weakened to its
  true footprint).
- `exists_surv_tuple_of_vanishBudget`, `exists_determining_tuple_of_vanishBudget` — the
  GG25 §4.3 determining-tuple conclusions under the budget.
- `vanishBudget_of_design`, `exists_determining_tuple_ranked` — the **repaired socket**:
  design + profile bound on `[1, r]` only.
- `no_unranked_theta_for_gk16Profile` — finding F1 as a theorem (the unranked socket is
  unsatisfiable for the GK16 profile).
- `frs_exists_determining_tuple`, `frs_exists_recovering_tuple` — **the headline,
  unconditional**: on the folded RS code under `Admissible + ω ≠ 0 + k ≤ s·n + k ≤ orderOf ω
  + 1 ≤ k`, any `H ≤ frsCode` with `finrank H ≤ r ≤ s` is determined by `r` folded
  coordinates inside any agreement set of density `θ' > (k−1)/n`; a `θ'`-agreeing codeword of
  `H` is uniquely recovered. The design input is the in-tree GK16 theorem — consumed, not
  hypothesized. Zero character sums.
- `FrsCloseListSpanBound` (named deep input G2, OPEN) and its consumer
  `frs_close_codeword_unique_recovery` — conditional only on G2: every `θ'`-close codeword is
  pinned by `r` folded coordinates uniquely among ALL close codewords (the line-decodability
  shape the GG25 engine consumes).
- `FrsMCAPin` (the lane target as a named `Prop` against the real `epsMCA`), plus
  `isPrizeClosure : Prop := False` and `not_prizeClosure`.

## 5. Honest framing (dossier §11.6 discipline)

- **Goal (A) vs (B):** this lane is **goal-(A)-adjacent banking** — deployment-relevant
  soundness for the codes that FRI/STIR/WHIR actually query after folding. It does **not**
  touch goal (B) = plain-RS δ\* in the window (the $1M core): `folding_transfer_no_go`
  (`FoldingTransferNoGo.lean`) proves a folded list/MCA bound at ANY radius says nothing
  about plain-close words (one corruption per orbit kills every folded agreement while
  keeping plain agreement `d/(d+1)`). `isPrizeClosure := False`.
- **Nothing here is claimed beyond its compile:** the unconditional statements are the
  determining/recovering tuples at `θ' > (k−1)/n`; "capacity" requires G0; "MCA pin" requires
  G2–G5. `FrsCloseListSpanBound` and `FrsMCAPin` are named OPEN `Prop`s — do not cite them as
  proven.
- **Relation to the CORE:** unchanged — OPEN, ON-BGK. This lane is deliberately off-core
  (Tier-3 bankable), chosen because every step is character-sum-free.

<sub>2026-07-01, lane L7 (#466 round 3). Brick 1 compile: `pg-iterate` fast path; a real
`lake-locked` build is the orchestrator's landing step. No claims beyond the axiom audit
shown in the file.</sub>

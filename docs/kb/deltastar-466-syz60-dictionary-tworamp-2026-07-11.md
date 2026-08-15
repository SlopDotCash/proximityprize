# SYZ60 — dictionary collapse + two-ramp windowed count (2026-07-11, #466)

Two independent reductions on the last bounded plumbing of the rate-`1/2` conditional δ* pin.
Both files axiom-clean (`propext, Classical.choice, Quot.sound` only); no `sorry`, no
`native_decide`.

## Task A — CountingDictionary collapses to a single scalar ceiling

File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ60Dictionary.lean`
(namespace `ArkLib.ProximityGap.Frontier.SYZ60Dictionary`).

SYZ57 had reduced wire (iv) to `SYZ57Transport.CountingDictionary`:
`∀ u, ∃ Ucard ∈ [2²⁹, 2³⁰], mcaBadCount … (u 0)(u 1) ≤ Ucard`.

**Observation:** the admissible band's *upper* edge `2³⁰` is itself admissible, so the existential
collapses — pick `Ucard = 2³⁰`. The residual is therefore exactly the plain ceiling

    BadCountCeiling := ∀ u, mcaBadCount (evalCode g (2³⁰) (2²⁹−1))
                              (predecessorRadius (2³⁰) stripNumerator) (u 0)(u 1) ≤ 2³⁰

and the reduction is an **equivalence**:

- `countingDictionary_of_badCountCeiling : BadCountCeiling → CountingDictionary`
- `badCountCeiling_of_countingDictionary : CountingDictionary → BadCountCeiling`
- `countingDictionary_iff_badCountCeiling : CountingDictionary ↔ BadCountCeiling`
- `stripCensusBound_of_badCountCeiling`, `deltaStar_bracket_of_badCountCeiling` — SYZ57's wire and
  the prize bracket re-expressed against the collapsed residual.

**Traced supply chain (named, not discharged):** `BadCountCeiling` is the target of the SYZ29
accounting route:
`SYZ29.bad_card_le_pool_of_attribution` (#B ≤ Σᵢ|Tᵢ| via `pencilImage`/`mem_pencilImage_of_root`)
+ `SYZ29.bad_card_le_pool_add_fresh` with fresh bounded by codim
(`SYZ30.fresh_card_le_codim`, `SYZ31.fresh_card_le_codim_of_private_coord`)
+ scalar↦support injectivity (`SYZ18.no_two_bad_scalars_share_witness`)
+ overlap control (`SYZ56.cross_witness_region_card_ge`).
The one concrete piece still missing is the **G87 `mcaEvent`→syndrome→pencil bridge** identifying
the concrete `mcaBadCount` with the SYZ29 root set `B`. That bridge is now the isolated Task-A
residual.

**Status:** dictionary REDUCED (equivalence) to `BadCountCeiling`; residual named =
G87 syndrome→pencil identification feeding SYZ29's `#B ≤ 2³⁰`.

## Task B — TwoRamp windowed count proved; μ-basis existence named

File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ60TwoRamp.lean`
(namespace `ArkLib.ProximityGap.SYZ60`).

SYZ44 carried `SYZ44.TwoRamp hilb δ₁ δ₂ := ∀ D, hilb D = (D+1−δ₁)+(D+1−δ₂)` as a named hypothesis.
Decomposed into (a) free+rank≤2, (b) degree-minimal μ-basis exists, (c) windowed count of a graded
free rank-2 basis. **(c) is proved in full**, and the free half of (a) is landed:

- `finrank_degreeLT : finrank K (degreeLT K m) = m` (via `Polynomial.degreeLTEquiv` + `finrank_fin_fun`).
- `finrank_window (δ D) : finrank K (degreeLT K (D+1−δ)) = D+1−δ` (the `max(0,·)` ramp = ℕ truncated sub).
- **(c)** `finrank_pair_window (δ₁ δ₂ D) :
  finrank K (degreeLT K (D+1−δ₁) × degreeLT K (D+1−δ₂)) = (D+1−δ₁)+(D+1−δ₂)` (`Module.finrank_prod`).
- `twoRamp_of_muBasisWindowIso : MuBasisWindowIso K hilb δ₁ δ₂ → SYZ44.TwoRamp hilb δ₁ δ₂`, where
  `MuBasisWindowIso hilb δ₁ δ₂ := ∀ D, hilb D = finrank K (degreeLT K (D+1−δ₁) × degreeLT K (D+1−δ₂))`.
- **(a) free half** `kernel_free (N : Submodule K[X] (Fin 3 → K[X])) : Module.Free K[X] N`
  (Mathlib `Submodule.smithNormalForm` on `Pi.basisFun`; K[X] a PID via EuclideanDomain).

**Status:** TwoRamp REDUCED — the windowed-count content (c) is discharged; the surviving residual is
`MuBasisWindowIso` = the μ-basis existence + rank-drop from 3 to 2 (coprimality; the honest (b)+(a)-rank
gap, which Mathlib lacks for coprime triples). Feeds SYZ44's `degree_sum_of_hilbert` unchanged.

## Final complete wire list for the conditional rate-½ δ* pin

The bracket `357913941/2³⁰ ≤ δ* ≤ 358612991/2³⁰` (`deltaStar_bracket_of_badCountCeiling`) is now
conditional on exactly:

1. `SYZ42.StripMasterHypothesis''` `H` (the abstract union-budget master hypothesis).
2. **Task A residual:** `BadCountCeiling` — bad count ≤ 2³⁰ per stack, i.e. the G87
   `mcaEvent`→syndrome→pencil bridge composed with SYZ29 attribution (equivalent to the old
   CountingDictionary).
3. **Task B residual:** for the SylvesterInjective side — `SYZ44.RankNullity` (large-D triple-Bézout
   surjectivity) + `MuBasisWindowIso` (μ-basis existence / rank-drop) + the imbalance bound `ι ≤ 1`.
   The windowed-count (c) is no longer assumed.

CORE remains OPEN / ON-BGK. No δ* closure claimed.

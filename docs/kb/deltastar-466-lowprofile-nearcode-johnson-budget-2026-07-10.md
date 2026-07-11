# δ* #466 — W15 part 3: the near-code Johnson budget via the offset collapse (2026-07-10)

Lane: `ll:low-profile-fiber`. File:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_W15NearCodeJohnsonBudget.lean`
(axiom-clean, 7/7 audits `[propext, Classical.choice, Quot.sound]`, no `sorryAx`,
`pg-iterate` ~40s). Companions: part 1 (floor `n − a`,
`deltastar-466-lowprofile-mcaevent-support-ladder-floor-2026-07-10.md`), part 2 (ceiling
`Λ·|supp|` + residual `LargeZeroSafeLineListBudgeted`,
`deltastar-466-lowprofile-safe-branch-ceiling-2026-07-10.md`).

## 0. The task

Discharge `LargeZeroSafeLineListBudgeted dom k a L` (the near-code line-list budget — the
single open input left on the weld's safe large-zero `mcaEvent` branch) from the in-tree
Johnson substrate.

## 1. The offset collapse

On a large-zero line (`z = |Z| ≥ a` zeros of the direction) every line word `u₀ + γ·u₁`
coincides with `u₀` on `Z`. An appearing codeword (`≥ a` agreement with some line word)
keeps at least `a − (n − z) ≥ 2a − n` of that agreement inside `Z`, where the line word IS
`u₀`. So the whole union-over-scalars line list injects into ONE per-word agreement list
of the offset `u₀` at reduced threshold `2a − n`
(`largeZero_lineAppearing_subset_offset_list`). Safety is not needed — large-zero alone.

## 2. The two discharge regimes

1. `nearCodeList_of_doubled_johnson_margin` — from the in-tree per-word Johnson bound
   (`JohnsonSplitSupply.rsCode_agreement_list_card_le`):
   `L = n² / ((2a − n)² − n(k − 1))` whenever `n(k − 1) < (2a − n)²`
   (the doubled-Johnson margin; asymptotically `α > (1 + √ρ)/2`, `a = αn`, `k = ρn`).
2. `nearCodeList_one_of_two_n_add_k_le_three_a` — `L = 1` whenever `2n + k ≤ 3a`
   (unique-decoding-plus): two distinct appearing codewords would put two
   `(a − (n − z))`-sized agree-with-`u₀` sets inside `Z` with pairwise overlap `≤ k − 1`
   (RS pairwise agreement), and inclusion-exclusion inside `Z` refutes that for all
   `z ≥ a`. Pure counting, no Johnson import.

## 3. Composed weld corollary

`mcaDeltaStar_ge_with_safe_branch_discharged`: at `2n + k ≤ 3a` the weld consumer
(`mcaDeltaStar_ge_of_farLineList_and_nearCodeList` of part 2, instantiated at
`L_near = 1`) holds with the safe large-zero branch's slot filled unconditionally by
`n − a` — EXACT against the part-1 floor. Remaining named residuals, stated honestly:

* `hfarL` — the far-line list budget (STILL OPEN; not claimed);
* `hunsafe` — the unsafe large-zero branch `mcaEvent` budget (open).

The safe large-zero branch itself is CLOSED in this regime: floor = ceiling = `n − a`.

## 4. Honesty — the uncovered window

* `campaign_shape_not_covered`: the rate-quarter campaign shape (`n=16, k=4, a=9`; above
  Johnson, `81 > 64`) satisfies NEITHER regime (`(2a−n)² = 4 < 48`, `3a = 27 < 36`).
  There the part-2 probe certifies `Λ = 1` empirically, but the offset collapse discards
  the support-side agreements a proof would need. **The window between the Johnson line
  (`a² > nk`) and the doubled-Johnson margin (`(2a−n)² > n(k−1)`) is the remaining open
  content of `LargeZeroSafeLineListBudgeted`** — the residual Prop stays, now with its
  covered/uncovered boundary machine-pinned.
* `discharge_regimes_nonvacuous`: at `n=16, k=4, a=12` both regimes hold (`L = 1`;
  general form `L = 16`).

## 5. Next targets

1. Close the Johnson-to-margin window: a per-line list bound that uses support-side
   agreements (the two-reference-word structure `c − c' = (γ − γ')u₁` on shared support
   agreements) — this is genuinely 2D/interleaved list decoding, adjacent to the open
   far-branch obligation; a probe of worst-case `Λ` over that window would locate whether
   `Λ = 1` persists down to Johnson (the part-2 probe suggests yes at the campaign shape).
2. The unsafe large-zero branch (`hunsafe`): find its analogue of the offset collapse or a
   saturation refuter.
3. The far branch (`hfarL`) remains the lane's terminal open input.

# #466 round 2, lane HLOW: the weld's `hlow` residual — exact dependency map + the witness-split shave

Date: 2026-07-01.  Status: **map + one landed axiom-clean brick**
(`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R2B_LargeZeroWitnessSplit.lean`,
namespace `ProximityGap.LargeZeroWitnessSplit`).  Nothing here closes the open core.

## 0. Object of study

The re-landed weld (`LineListMCAWeld.lean`, `mcaDeltaStar_ge_of_farLineListBudgeted`)
reduces the prize floor `δ ≤ mcaDeltaStar(RS[dom,k], ε*)` to three obligations:

- **H1 `hfarL`** — far-line list budget: every FAR direction has `#lineAppearingCodewords ≤ L`.
- **H2 `hfit`/`hBudget`** — arithmetic: `L·⌊(n−z)/(a−z)⌋ ≤ B_far` for `z < a`, and
  `max(B_far, B_near)/q ≤ ε*`.
- **H3 `hlow`** — for every `u₀` and every direction `e₁` with `#zeroSet(e₁) ≥ a`, the
  weld's exact bad object
  `#{γ : mcaEvent(rsCode dom k, δ, u₀, e₁, γ)} ≤ B_near`.

This note maps H3.  Throughout: `Z = directionZeroSet e₁`, `z = #Z`,
`s = #directionSupportSet e₁ = n − z`, `a = ⌈(1−δ)n⌉` the agreement threshold,
`k = ρn` the RS dimension.  In-window: `ρn < a < √ρ·n`, so `k < a`.

## 1. The stratification of H3 (what is in-tree, layer by layer)

Every layer below is axiom-clean on main unless marked OPEN.  Failure-scanner names
(the machine refuter that guards each layer) in brackets.

```
H3: mcaEvent filter on (u₀, e₁), z ≥ a
 │
 ├─[0] mcaEvent filter ⊆ lineBadScalars            (unconditional)
 │      LineListMCAWeld.mcaEvent_filter_subset_lineBadScalars
 │      — needs only haF (a ≤ every witness size).  From here on, H3 is pure counting
 │        on lineBadScalars; no probability or ¬pairJointAgreesOn clause remains.
 │
 ├─[1] SAFE/UNSAFE split on ZeroDirectionSafeLine dom k a u₀ e₁
 │      LineListMCAWeld.lowWeight_badCount_le_of_largeZeroSafe_budget
 │      │
 │      ├─ UNSAFE branch (∃ codeword with ≥ a zero-agreements): OPEN as a *counting*
 │      │   target — and provably NOT boundable at the lineBadScalars layer:
 │      │   lineBadScalars_eq_univ_of_codeword_directionZeroAgreement_ge saturates
 │      │   the whole field.  Any B_unsafe < q must exploit the mcaEvent-only
 │      │   structure discarded at layer [0] (the ¬pairJointAgreesOn clause; cf.
 │      │   mcaEvent_false_of_direction_mem: alignment kills badness).  See §4.
 │      │   [scanner: not_zeroDirectionSafeLine_iff_exists_codeword_zeroAgreement_ge]
 │      │
 │      └─ SAFE branch → [2]
 │
 ├─[2] lineBadScalars ≤ puncturedZeroStratifiedLineWeight        (needs safety)
 │      lineBadScalars_card_le_puncturedZeroStratifiedLineWeight
 │      = Σ_{c appearing} ⌊s/(a − zAgree(c))⌋, well-defined since safety ⟹ zAgree < a.
 │      [scanner: not_puncturedZeroStratifiedLineBudgeted_iff_weight_gt]
 │
 ├─[3] weight = Σ_{t<a} #stratum(t)·⌊s/(a−t)⌋                    (exact regrouping)
 │      puncturedZeroStratifiedLineWeight_eq_sum_zeroAgreementStrata
 │      stratum(t) = appearing codewords with EXACTLY t zero-agreements.
 │
 ├─[4] per-stratum caps:
 │      ├─ t ≥ k:  #stratum(t) ≤ choose(z, t)                     PROVEN (MDS endpoint)
 │      │   zeroAgreementStratum_card_le_choose_of_k_le_t, via
 │      │   coordinateAgreementFiber_card_le_one_of_k_le
 │      │   (fiber over ≥ k coords has ≤ 1 codeword).
 │      ├─ t < k:  #fiber(S) ≤ |F|^(k−#S)                          PROVEN but USELESS
 │      │   coordinateAgreementFiber_card_le_field_pow_sub_card — the raw field-power
 │      │   fit is FORMALLY REFUTED at any B < |F|^k whenever 2a ≤ n
 │      │   [scanners: not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_two_mul_le,
 │      │    …_of_exists_choosePow_gt, …_of_exists_zeroTerm_gt, …_of_exists_support_ge;
 │      │    also not_fieldPowFiberFit_of_zeroCount_choosePow_gt]
 │      └─ t < k, better-than-field-power: **OPEN** (the "low-profile fiber theorem")
 │          [scanner: not_zeroCoordinateAgreementFiberBudgeted_iff_exists_fiber_gt;
 │           stratum level: not_zeroAgreementStrataCardBudgeted_iff_exists_stratum_gt]
 │
 └─[5] arithmetic fit: Σ_t N(t)·⌊s/(a−t)⌋ ≤ B_near
        ZeroAgreementStrataBudgetFits / ZeroCoordinateAgreementFiberBudgetFits
        [scanner: not_zeroAgreementStrataBudgetFits_iff_sum_gt]
```

Assembly (all proven): stratum caps [4] + fit [5] → `PuncturedZeroStratifiedLineBudgeted`
(`puncturedZeroStratifiedLineBudgeted_of_zeroAgreementStrataCardBudgeted`) →
`LargeZeroSafeLineBadScalarsBudgeted`
(`largeZeroSafeLineBadScalarsBudgeted_of_uniformPuncturedZeroStratifiedLineBudgeted`) →
H3 via `lowWeight_badCount_le_of_largeZeroSafe_budget` (with the unsafe branch's `B_unsafe`).

**Pre-brick irreducible remainder of H3** = (i) the `t < k` strata on safe large-zero lines
+ (ii) the unsafe branch.  Exactly as the weld's docstring says.

## 2. NEW (this lane): the witness split — `_R2B_LargeZeroWitnessSplit.lean`

The in-tree stack bounded strata from ABOVE only.  The new brick adds the missing LOWER
bound on zero-agreement, which makes low strata *empty* rather than merely budgeted:

- `sub_support_le_zeroAgreement_card_of_agree` — agreement `≥ a` at any `γ` forces
  `zAgree(c) ≥ a − s` (γ-free!).  Dual to the in-tree upper bound
  `directionZeroAgreementSet_card_le_agreeSet_line`.
- `zeroAgreementStratum_eq_empty_of_add_support_lt` — **stratum(t) = ∅ for all
  `t < a − s`**, on every line, no hypotheses.
- `exists_mem_coordinateAgreementFiber_of_mem_lineAppearingCodewords` — the fiber form:
  for `m ≤ a − s`, every appearing codeword lies in a `coordinateAgreementFiber(u₀, T)` with
  `T ∈ Z.powersetCard m` — the SAME γ-independent fiber objects as the far branch.
- `zeroAgreementStrataCardBudgeted_thresholdChoose` — on **very-large-zero** directions
  (`s ≤ a − k`, i.e. `z ≥ n − a + k`) the empty/MDS thresholds meet: every stratum has
  `N(t) = if t + s < a then 0 else choose(z, t)` — **UNCONDITIONAL**, no `t < k` input.
- `lineBadScalars_card_le_thresholdChoose_sum` +
  `mcaEvent_filter_card_le_thresholdChoose_sum` — closed per-line cap
  `#bad ≤ Σ_{a−s ≤ t < a} choose(z,t)·⌊s/(a−t)⌋` on safe very-large-zero lines, in the weld's
  exact `hlow` filter shape.
- `MidBandSafeLineBadScalarsBudgeted` (new named residual) +
  `largeZeroSafeLineBadScalarsBudgeted_of_midBand_and_thresholdChooseFit` — the stack's
  large-zero safe residual now follows from the mid-band residual + binomial arithmetic.

**Post-brick irreducible remainder of H3** (the honest shave result):

1. **Mid band** `a ≤ z < n − a + k` on safe lines (`MidBandSafeLineBadScalarsBudgeted`):
   here `1 ≤ a − s < k` — strata `t < a − s` are empty (new brick) but strata
   `a − s ≤ t < k` still need a sub-field-power fiber bound.  Note for ρ = 1/2 this band is
   EMPTY at δ in-window whenever `n − a + k ≤ a`, i.e. `a ≥ (n+k)/2 = 3n/4` — but in-window
   `a < √ρ·n ≈ 0.707n < 3n/4`, so the band is nonempty at all prize rates.  Width:
   `z ∈ [a, n − a + k)`, i.e. `n + k − 2a` values of `z`.
2. **Unsafe branch** (`∃ c : zAgree(c) ≥ a`): must be attacked at the `mcaEvent` layer,
   not `lineBadScalars` (which saturates to `univ` there — proven).
3. **Arithmetic honesty on the very-large-zero cap:** the closed cap
   `Σ_{t ≥ a−s} choose(z,t)·⌊s/(a−t)⌋` is NOT prize-small in general: the leading term
   `choose(z, a−s)·s` is exponential in `min(a−s, z−a+s)` (e.g. `z ≈ 0.9n`, `a ≈ 0.7n`:
   `choose(0.9n, 0.6n)`).  It only fits `B_near ≈ n` near the band edges (`s` tiny: then
   `a − s ≈ a > z/2`? no — `t ≥ a − s ≈ a` and `t < a` forces `t ∈ [a−s, a)`, a window of
   width `s`; for `s = O(1)` the cap is `≤ s·choose(z, a−1)·s` — still binomial).  Only at
   `s = 0` (e₁ = 0 ∈ C) does everything vanish (`mcaEvent_false_of_direction_mem`).  So the
   brick's value is structural (γ-free fibers + empty low strata + exact residual naming),
   NOT a numeric discharge of H3.  This is consistent with the recorded choose-arithmetic
   obstructions (`LineListCodewordSupportChooseArithmeticObstruction.lean`,
   `LineListCodewordSupportDivArithmeticObstruction.lean`).

## 3. The self-similarity observation (conjecture-level; the map's main structural finding)

Restrict to `Z`: every appearing codeword agrees with `u₀|_Z` on ≥ `a − s` of the `z`
coordinates of `Z`, i.e. lies within Hamming distance `z − (a − s) = n − a` of `u₀|_Z` in the
punctured code `RS[dom|_Z, k]` (restriction is injective for `z ≥ k`, which holds on the
whole large-zero branch since `z ≥ a > k`).  So:

> **the large-zero appearing-codeword list IS a list-decoding ball of radius `n − a` in the
> length-`z` punctured RS code, around the γ-free center `u₀|_Z`.**

Radius check against Johnson for the punctured code (length `z`, dim `k`):
`n − a ≤ z − √(kz)` ⟺ `a ≥ n − z + √(kz)`.  At `z = n` this is `a ≥ √(kn) = √ρ·n` —
**exactly the Johnson boundary that defines the prize window** (in-window `a < √ρ·n`).
At smaller `z` the requirement is even harder (`n − z + √(kz)` decreases in `z`, minimized
at `z = n`).  Conclusion (honest, important): **the H3 mid-band/large-zero residual is not a
side condition — it contains a re-scaled copy of the SAME beyond-Johnson list-size problem
as H1**, on the punctured domain, with the same `Θ(1/log n)` shortfall.  Any technique that
closes H3's `t < k` fibers below field-power at prize `a` would equally close the far-line
list budget; there is no "easy near branch."  (This sharpens the dossier-v3 Tier-1 item-2
wording: the low-profile theorem is not merely "open", it is Johnson-equivalent-hard.)

Corollary of the same restriction argument (unconditional, could be a future 10-line brick):
for `n − a ≤ (z − k)/2` — unique-decoding radius of the punctured code — the appearing list
on the large-zero line has size ≤ 1.  In-window this needs `z ≥ 2n − 2a + k`, a strictly
deeper band than the brick's `z ≥ n − a + k`; it does not subsume the brick (and at prize
`a < √ρ·n`, `2n − 2a + k > n` for ρ ≤ 1/4, so the UDR band is often empty — check per rate:
ρ = 1/2: `2n − 2a + n/2 ≤ n` ⟺ `a ≥ 3n/4` > `√ρ·n` — empty in-window at ALL prize rates).
The brick's `choose`-cap band is therefore the strongest unconditional statement available
from restriction alone.

## 4. The unsafe branch (what a B_unsafe proof must look like)

`lineBadScalars` saturates (`= univ`) on unsafe lines, so layer [0]'s discard of
`¬pairJointAgreesOn` must be undone.  The available mcaEvent-level levers, both in
`LineListMCAWeld.lean`:

- `no_direction_codeword_on_witness_of_mcaEvent`: badness ⟹ no codeword matches the
  DIRECTION on the witness set.  On the large-zero branch the direction has `z ≥ a` zeros,
  so the zero codeword matches `e₁` on all of `Z`; a witness `S` with `#(S∩Z) ≥ a`… gives a
  contradiction only if `S ⊆` positions where `c = e₁`; with `c = 0` this needs `e₁ = 0` on
  `S`, i.e. `#(S ∩ Z) = #S` — not automatic.  Quantitatively: badness at `γ` forces the
  witness to avoid full containment in `Z`+direction-agreement sets for EVERY codeword.
  This is the only structure that distinguishes unsafe-bad from unsafe-saturated.
- `mcaEvent_direction_sub_codeword_iff` (coset invariance): unsafe lines with `e₁` NEAR the
  code reduce to their coset representative; the weld already routes each stack through its
  best representative, so B_unsafe is only needed for cosets ALL of whose representatives
  have `z ≥ a` (the genuinely low-weight cosets).

Named target left for a future lane: `UnsafeLargeZeroMcaBudget dom k a δ B :=
∀ u₀ e₁, a ≤ z(e₁) → ¬ZeroDirectionSafeLine dom k a u₀ e₁ → #{γ : mcaEvent …} ≤ B`
(this is the `hunsafe` slot of `lowWeight_badCount_le_of_largeZeroSafe_budget`, verbatim).

## 5. Minimal named-Prop basis for H3 at prize parameters (the deliverable-(a) answer)

H3 (`hlow` at `B_near`) ⟸ conjunction of:

| # | Prop (in-tree name) | status |
|---|---|---|
| 1 | `haF` witness-size arithmetic | trivial (proven at each instantiation) |
| 2 | `MidBandSafeLineBadScalarsBudgeted dom k a B₁` (NEW name, this brick) | **OPEN — Johnson-equivalent-hard by §3** |
| 3 | very-large-zero fit: `Σ_{t≥a−s} choose(z,t)⌊s/(a−t)⌋ ≤ B₂` for all `z ≥ n−a+k` | **pure arithmetic, but FALSE at prize `B ≈ n` in the band interior** (§2.3) — needs the cap sharpened (the `choose(z,t)` for `t ≥ k` counts fibers, not appearing-ball members; §3's ball structure says the true count is ≤ punctured list size, conjecturally poly) |
| 4 | `hunsafe` = `UnsafeLargeZeroMcaBudget` (§4) | **OPEN — must use mcaEvent-only structure** |

with `B_near = max(B₁, max(B₂, B_unsafe))` via
`largeZeroSafeLineBadScalarsBudgeted_of_midBand_and_thresholdChooseFit` +
`lowWeight_badCount_le_of_largeZeroSafe_budget`.

Item 3's honest reading: the brick's unconditional `choose` cap should be viewed as a
*certificate interface*, and §3 says the right conjecture to attack next is
**PuncturedListBudget**: `#(appearing) ≤ ℓ(z, k, n−a)` = list size of the punctured code at
radius `n − a` — one object unifying H1 (z = 0 side: far lines) and H3 (large-zero side).
That reframing (H1 and H3 are the SAME theorem at two ends of the `z`-range, with the mid
band interpolating) is this lane's main map contribution.

## 6. Scanner index guarding each layer (for future refuters)

- layer [1] safety: `not_zeroDirectionSafeLine_iff_exists_codeword_zeroAgreement_ge`,
  `not_uniformZeroDirectionSafe_iff_exists_line_codeword_zeroAgreement_ge`
- layer [2] weight: `not_puncturedZeroStratifiedLineBudgeted_iff_weight_gt`,
  `puncturedZeroStratifiedLineWeight_gt_of_lineBadScalars_card_gt`
- layer [4] strata/fibers: `not_zeroAgreementStrataCardBudgeted_iff_exists_stratum_gt`
  (+ `…_iff_exists_low_stratum_gt_of_high_choose`: with the high-`t` choose cap fixed, any
  failure is a LOW stratum), `not_zeroCoordinateAgreementFiberBudgeted_iff_exists_fiber_gt`
- layer [5] fits: `not_zeroAgreementStrataBudgetFits_iff_sum_gt`,
  `not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_two_mul_le` (kills
  raw field-power globally), `not_fieldPowFiberFit_of_zeroCount_choosePow_gt` (parametric)
- whole-route triage: `not_uniformLineBadScalarsBudgeted_iff_eligible_or_unsafe_or_largeZero_safe`,
  `unsafe_or_largeZero_safe_low_zeroAgreementStratum_gt_of_not_uniformLineBadScalarsBudgeted`
- weld consistency refuters (do NOT re-consume): `not_uniform_lineListBudgeted_of_lt_card`,
  `not_forall_nonvanishing_lineListBudgeted_of_lt_field`, `aligned_line_lambda_ge_q`
- NEW (this brick, positive-side guards): any proposed low-stratum countermodel must respect
  `zeroAgreementStratum_eq_empty_of_add_support_lt` — a scanner "hit" at `t < a − s` is a
  bug in the scanner, not a countermodel.

## 7. Verification line

`scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R2B_LargeZeroWitnessSplit.lean`
→ ✅ OK, all 8 `#print axioms` = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

# δ* #466 — W15 part 2: the safe-branch ceiling `Λ·|supp|`, the near-code list residual, and sub-Johnson q-saturation (2026-07-10)

Lane: `ll:low-profile-fiber`. Files:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_W15SafeBranchLinearCeiling.lean`
(axiom-clean, 6/6 audits `[propext, Classical.choice, Quot.sound]`, no `sorryAx`,
`pg-iterate` 40s) and probe `scripts/probes/probe_466_w15_multibase_ladder.py`
(deterministic, exit 0). Companion to
`deltastar-466-lowprofile-mcaevent-support-ladder-floor-2026-07-10.md` (W15 part 1: the
`n − a` floor).

## 0. The task

Part 1 left a two-sided obligation on the weld's safe large-zero `mcaEvent` branch: floor
`B_near ≥ n − a` closed; upper side open — prove `B_near ≤ C·n` or refute with a
superlinear construction (multi-base ladders).

## 1. Probe verdict (measure first)

Exact ground-truth `mcaEvent` counts (witness-optimality: `S = ` full agreement set is
optimal; explainer check by interpolation) on 8 shapes × (ladders + 60 random safe
large-zero lines):

* **Ceiling `count ≤ Λ·|supp|`: zero violations anywhere** (`Λ` = line-appearing-codeword
  count at threshold `a`).
* **Above Johnson** (campaign rate-quarter `q=17, n=16, k=4, a=9`; `a² = 81 > 64 = nk`):
  `count = 7 = n − a` exactly, `Λ = 1`. The part-1 floor is the truth.
* **Deep sub-Johnson** (`(13,12,2,3)`, `(13,12,3,5)`, `(29,24,2,3)`, `(29,24,3,5)`, ...):
  `count = q` on EVERY line probed — including the single-base ladder — with `Λ` exploding
  (up to `769`). Mechanism: at agreement `a ≪ √(nk)` per-scalar lists are nonempty and
  generic witnesses have no explainer. **So no unconditional `B_near ≤ C·n` theorem exists
  at sub-Johnson shapes.**
* **Constant multi-base ladders** (`M` distinct constant bases on disjoint
  `(a−1)`-anchors; safety forces `M(k−1) < a`) stay `O(n)` and never beat the ambient
  saturation: superlinearity below Johnson is `q`-saturation of the class, not a designed
  ladder.

## 2. What is proved (unconditional, all in the W15 part-2 file)

1. `mcaEvent_witness_meets_support` — on a `ZeroDirectionSafeLine`, every `mcaEvent`
   witness contains a support point of the direction: its zero-part sits inside the line
   codeword's `directionZeroAgreementSet`, which safety caps `< a ≤ |S|`.
2. `safe_mcaEvent_filter_card_le_lambda_mul_support` — **the ceiling**
   `count ≤ Λ·|supp|`: bad `γ ↦ (witness codeword w, support point i)` is injective
   because the pair pins `γ = (w i − u₀ i)/u₁ i`.
3. `safe_mcaEvent_filter_card_le_of_lineListBudgeted`, and on the large-zero class
   `safe_largeZero_mcaEvent_filter_card_le`: with per-line list budget `L`,
   `count ≤ L·(n − a)`.
4. `LargeZeroSafeLineListBudgeted` — the NEW honest named residual: a line-list budget on
   near-code (safe, non-support-eligible) lines. Disjoint class from the far-branch
   `hfarL`.
5. `mcaDeltaStar_ge_of_farLineList_and_nearCodeList` — the upgraded weld consumer: the
   W9-refuted `hsafe` slot replaced by `L_near·(n − a)`; residual set is now
   `hfarL` + `hnearL` + `hunsafe`.

## 3. State of the safe branch (bracket)

  `n − a ≤ B_near^true ≤ L_near · (n − a)` — **exact at `L_near = 1`**,
which the probe certifies at the campaign's above-Johnson rate-quarter shape. The safe
large-zero branch of the weld is reduced to a single open input: the near-code list budget
`L_near`, and its truth is **Johnson-gated** (`johnson_sign_gate` records the sign flip):

* above Johnson: `L_near = 1` empirically — safe branch effectively CLOSED there pending a
  Lean proof of the `Λ ≤ L` bound (a classical-flavored uniqueness statement: at
  `a² > nk`, a near-code line carries at most `L` codewords at agreement `a`);
* deep sub-Johnson: `LargeZeroSafeLineListBudgeted` is FALSE at every useful `L`
  (`Λ = Ω(q)`-scale, counts saturate to `q`): the mcaEvent-vocabulary route CANNOT close
  the safe branch below Johnson. This mirrors, one vocabulary up, W9's `lineBadScalars`
  verdict — but now with the exact shape boundary located.

## 4. Next targets

1. Prove `LargeZeroSafeLineListBudgeted dom k a L` in Lean for above-Johnson `a` (Johnson
   bound on the punctured/near-code class; likely from the in-tree Johnson substrate) —
   this would CLOSE the safe large-zero branch of the weld above Johnson.
2. Formalize the sub-Johnson saturation as a theorem (currently probe-level): a
   constructive family of safe large-zero lines with `mcaEvent` count `ω(n)` below
   Johnson. The probe's random lines all saturate, so a construction should exist; the
   constant-base cap shows it cannot be a constant-base ladder.
3. Propagate the upgraded consumer into the workbench ledger (replace the `hsafe`-shaped
   items by `hnearL`).

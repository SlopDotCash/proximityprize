# A26 — Reverse LD⇔MCA dictionary: beyond-Johnson interleaved list lower bounds from exact MCA values

Date: 2026-06-14. Actionable A26 (merged 357-T16). Status: **PARTIAL** (axiom-clean Lean
artifact landed; magnitude is `O(1)` at the explicit finite instance; asymptotic prize open).

## The task

Run the list-decoding ⇔ mutual-correlated-agreement dictionary **backward**: the repo only ever
consumes it *forward* (interleaved list **upper** bound `Λ₂ ≤ L` ⟹ `ε_mca` **upper** bound). The
reverse engine `exists_interleavedList_card_gt_of_epsMCA_gt` (`ReverseDictionary.lean`) is the
contrapositive — an `ε_mca` **lower** bound forces a list **lower** bound. A26 asks to exercise it
on exact in-window MCA values to produce explicit **beyond-Johnson interleaved** list lower bounds.

## The mechanism, precisely

Reverse dictionary (in-tree, axiom-clean):
```
(1 + (n − a)·L)/q  <  ε_mca(C, δ)      ⟹    ∃ f₁ f₂,  L < |interleavedList(C, f₁, f₂, a)|
```
with **collapse floor** `a = 2·⌈(1−δ)·n⌉ − n`.

Forward interleaved Johnson cap (`interleavedList_card_le_johnson`):
```
|interleavedList(C, f₁, f₂, a)|  ≤  n²/(a² − n·e)      WHEN  n·e < a²    (e = k−1)
```
so the **interleaved Johnson radius** is `a_J = ⌊√(n·e)⌋`; at `a ≤ a_J` the divided cap is N/A.

**Key structural observation (the honest constraint).** `interleavedList_card_le_johnson` is a
*proven theorem*. Therefore the reverse dictionary can only force a list size that *exceeds the
Johnson prediction* in the region where the Johnson cap does **not** apply — i.e. `a² ≤ n·e`,
**at/below the Johnson radius**. A "beyond-Johnson" firing inside the gap (`n·e < a²`) would
contradict the proven cap; the probe confirms **zero** such firings. So "beyond-Johnson" here
means precisely: *a certified interleaved list lower bound `> 1` at an agreement radius the
second-moment (Johnson) method is vacuous at.*

## The explicit instance and result

`RS[ZMod 17, μ₁₆, k=2]`, `n=16=2⁴`, rate `ρ=1/8`, `e=k−1=1`, interleaved Johnson radius
`a_J = ⌊√16⌋ = 4`. Row-0 = the in-tree hard word `w0` of `DeltaStarExactCrossoverF17`; row-1 =
a second four-line block-stitch `w1`.

**Probe `sweep_A26_interleaved_subjohnson.py` (exact enumeration, 0 sampling):**

| floor `a` | `\|interleavedList(w0,w1,a)\|` | Johnson gap `n·e<a²`? | Johnson cap |
|---|---|---|---|
| 2 | **94** | false | N/A (sub-radius) |
| 3 | **5**  | false | N/A (sub-radius) |
| 4 | **4**  | false (`16≮16`) | N/A (at the radius) |
| 5 | 1  | true | 28 (Johnson-clean) |

Base-code single-row companion on `w0` (reproduces in-tree `listSize_four=5`,
`listSize_three=15`): list `5` at `a=4`, `15` at `a=3`, both sub-Johnson.

**Lean artifact** `Frontier/Sweep_A26_ReverseLDFromMCA.lean` (self-contained, `Mathlib.Tactic`,
all by `decide`, axiom-clean `[propext, Classical.choice, Quot.sound]`): exhibits **four explicit
pairwise-distinct** codeword pairs each jointly agreeing with `(w0,w1)` on `≥4` points, and proves
the Johnson gap is **false** at `a=4`. Capstone `interleaved_list_ge_four_beyond_johnson`:
interleaved list at floor 4 has size `≥4>1` **while** the divided Johnson cap is inapplicable.

## Why the forced magnitude is small (the honest gap)

The reverse dictionary's **floor doubling** (`a = 2t − n`, `t = ⌈(1−δ)n⌉`) is the limiting factor.
The large exact list sizes live at *small* single-row agreement floors (`listSize(2)=63`,
`listSize(3)=15`), but the dictionary reads the interleaved list at the *doubled* collapse floor.
Where `a_coll ≤ a_J` (so beyond-Johnson is even logically possible) the collapse floor is `≤4`, and
on this tiny `n=16` instance the forced `L` from a `≤ a few`/q explosion-band `ε_mca` is `O(1)`.
The probe `sweep_A26_reverse_ld_from_mca.py` tabulates `L_J(a_coll)` and the firing thresholds at
both `q=17` and prize `q≈n·2¹²⁸` — the firing condition is `q`-independent at the integer level
(`1+(n−a)·L < #cluster`), so a *large-n* instance with a large explosion-band cluster at a
sub-Johnson collapse floor is what would scale the bound; that does not exist at `n=16`.

## Verdict

PARTIAL. The **direction** is the deliverable: an explicit, axiom-clean, sub-Johnson interleaved
list lower bound for a fixed smooth RS code, extracted by running the dictionary backward — new
combinatorial data the forward Johnson machinery structurally cannot produce. The magnitude is
`O(1)` at this finite instance; the asymptotic prize family (`|F|<2²⁵⁶`, `ε*=2⁻¹²⁸`) is untouched.
The reusable lever: a future *large-n* exact (or certified-lower) explosion-band `ε_mca` value at a
collapse floor below `⌊√(n(k−1))⌋` would, via the same engine, scale this to a super-constant
interleaved list lower bound below the Johnson radius.

Artifacts:
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/Sweep_A26_ReverseLDFromMCA.lean`
- `scripts/probes/sweep_A26_reverse_ld_from_mca.py`
- `scripts/probes/sweep_A26_interleaved_subjohnson.py`

# δ\* — Round 14 essay: the relationship of the two open inputs, and the two-sided iff certificate

> Issue #466 · dossier v3. Round-14 companion to `docs/kb/deltastar-DOSSIER-v3-2026-07-01.md`
> (§0, §2, §13, §22–23) and to the round-13 record (`_R13HyperplaneSecondMoment.lean`,
> `_WallCapstone.lean`, `_MomentOptimizedSupNorm.lean`).
>
> **Honesty contract (non-negotiable, restated).** "Proven" = axiom-clean Lean
> (`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`, no `sorryAx`) via
> `scripts/pg-iterate.sh`. Everything else is a labeled conjecture / reduction / probe. The open
> core is a recognized open problem in analytic number theory; carrying it as a named `Prop` is
> **modularity, not incompleteness**. Nothing below claims the wall or the prize is closed.

---

## 0. Where round 13 left us, and what round 14 does

Round 13 established that the prize does **not** localize to a single open input. The
`_WallCapstone.lean` capstone reduces the entire prize to `WallHolds ∧ RealizedIncidenceBudget`;
round 13's `_R13HyperplaneSecondMoment.lean` then proved that the second conjunct is a **genuinely
distinct** open Prop — the sup-norm `M` that the wall delivers is *phase-blind*, so it controls only
the `s₀`-average of the far-coset hyperplane incidence, never the worst case. The two open inputs
are:

- **`WallHolds G := ∀ r, DCEnergyCorrection.DCEnergyBound G r`** — the DC-subtracted char-`p`
  Wick/moment tower at every rung. Round 13's `_MomentOptimizedSupNorm.supNorm_le_of_wallHolds`
  proves, axiom-clean, that `WallHolds ⟹ M = max_{b≠0}‖η_b‖ ≤ √(2e·n·(ln q+1))`. This is the
  **phase-blind moment face** (BGK proper).
- **`HyperplaneCancellation := ∀ s₀, ‖∑_{b∈H} conj(η_b) ψ(b·s₀)‖ ≤ √|H|·M`** — the worst-case
  per-frequency `√q·B` cancellation over the far-coset frequency hyperplane `H`. This is the
  **phase-correlation face** (BCHKS Conj 1.12 / the Paley-graph worst case).

Round 14 completes the thread. It does **not** hunt for new escape routes — all decided across
rounds 1–13. It answers exactly two remaining structural questions:

- **Lane D:** what is the *relationship* between `WallHolds` and `HyperplaneCancellation`?
  Equivalent, one strictly stronger, or independent? Which is the real bottleneck?
- **Lane I:** is the full two-sided iff machine-checked? What is proven in each direction, and what
  named glue remains?

---

## 1. Lane D — the two open inputs are INDEPENDENT

**Verdict: INDEPENDENT.** Neither `WallHolds` nor `HyperplaneCancellation` implies the other. This
completes a two-direction non-implication:

| direction | status | evidence |
|---|---|---|
| `WallHolds ⟹ HyperplaneCancellation` | **FALSE** | round 13 (`_R13HyperplaneSecondMoment.incidenceSum_sq_sum_offsets`): `M` is phase-blind — it controls only the `s₀`-average |
| `HyperplaneCancellation ⟹ WallHolds` | **FALSE** | round 14 (this lane, `_R14SupNormWeakerThanWall.lean`): `HyperplaneCancellation`'s only spectral input is `M`, and `M ≤ B` gives a strictly-lossy Hölder projection |
| `WallHolds` vs "`M` small" | `WallHolds` **STRICTLY STRONGER** | round 14: the `M`-bound is a lossy projection of the moment tower |

### 1.1 Direction 1 (already round 13): the wall's `M` is phase-blind

`_R13HyperplaneSecondMoment.incidenceSum_sq_sum_offsets` is the axiom-clean additive-character
second-moment identity

> `∑_{s₀∈F} ‖I_H(s₀)‖² = q · ∑_{b∈H} ‖η_b‖²`,  where  `I_H(s₀) := ∑_{b∈H} conj(η_b) ψ(b·s₀)`.

Dividing by `q`, the *average* over offsets `s₀` of `‖I_H(s₀)‖²` is exactly `∑_{b∈H}‖η_b‖² ≤ |H|·M²`
— the √-cancelled World-I scale `√|H|·M`. But the far-coset adversary picks the **worst** `s₀`,
which can be a factor `√|H|` above the rms. The counterexample-to-derivability is decisive:
replacing `{η_b}` by any spectrum of *identical moduli* but different phases leaves `M` and the
entire RHS of the identity unchanged, yet collapses `worst‖I_H‖` from `≈|H|·M` down to the √-scale.
Hence the worst case is **not a function of `M`** (nor of the moduli at all): `WallHolds` does not
imply `HyperplaneCancellation`.

### 1.2 Direction 2 (round 14): the sup-norm bound is a lossy Hölder projection

`_R14SupNormWeakerThanWall.lean` settles the reverse at the moment/energy layer, axiom-clean (three
theorems, all `#print axioms = [propext, Classical.choice, Quot.sound]`, no `sorryAx`; verified via
`pg-iterate`, OK 25s):

- **`supBound_sumPow_le`** — from `∀ b∈H, ‖η_b‖ ≤ B` (`0 ≤ B`), the *only* per-rung consequence is
  the term-wise Hölder projection

  > `∑_{b∈H} ‖η_b‖^{2r} ≤ |H|·B^{2r}`   (via `pow_le_pow_left₀`, `x^{2r} ≤ B^{2r}`).

  This is the entire content a sup-norm bound carries at rung `r`.
- **`wick_lt_supProjection_r1`** — the clean `r = 1` witness: with the wall's own constant
  `B² = 2e·n·(L+1)` (`L = ln q ≥ 0`, `n ≥ 1`) and full-size hyperplane `|H| = q`, the Wick RHS
  `q·(2·1−1)‼·n = q·n` is **strictly less** than the projection `q·B²` (since `2e(L+1) > 2 > 1`).
- **`wallConst_sq_ge_n`** — `B² = 2e·n·(L+1) ≥ n`, certifying the projection has the *wrong shape*
  `(2e·n·log q)^r` versus the Wick shape `(2r−1)‼·n^r`, over-shooting by `(2e·log q)^r/(2r−1)‼ ≫ 1`.

The interpretation is sharp: `HyperplaneCancellation`'s only spectral input is `M`; the strongest
per-rung fact `M ≤ B` supplies is the projection `A_r ≤ |H|·B^{2r}`, which strictly exceeds the Wick
RHS `q·(2r−1)‼·n^r`. A spectrum saturating `‖η_b‖ = B` therefore respects `M ≤ B` while carrying `A_r`
far above the tower — so `HyperplaneCancellation ⟹ WallHolds` is **false**. `WallHolds` is strictly
stronger than "`M` small" by the standard one-way eigenvalue–moment interchange.

### 1.3 Probe corroboration and literature

`scripts/probes/probe_466r14_relationship.py → _out_466r14_relationship.txt` reproduces the numbers
exactly (regime `p ≡ 1 mod n`, `p ≥ n⁴`, ≥2 primes with distinct `v₂(p−1)`, `β ≈ 4.00`): the ratio
`B²/Wick₁ = 45.3` at `r = 1`, growing to `~10⁷` by `r = 10`. Crucially, a **Parseval-respecting**
counterexample (keep `A_1 = n(q−1)` exact but pile the `L^{2r}` mass onto `k = n(q−1)/B²` frequencies
at the cap) violates `WallHolds` at every `r ≥ 2` — so even the admissible, Parseval-correct spectrum
class separates the two. Literature is accurate and in-tree
(`docs/references/proximity-gap-paley-spectrum/README.md`, arXiv 1809.09829): `M` is the
non-principal eigenvalue of the generalized Paley graph `Cay(F_q, μ_n)` (Liu–Zhou Thm 115); the
Paley Graph Conjecture `M ≤ 2√n` is OPEN, best-proven BGK `n^{1−o(1)}`.

### 1.4 Which is the real bottleneck?

**Neither alone.** They are orthogonal faces — moment/energy versus phase-correlation — and both are
needed. `WallHolds` is even strictly stronger than the Paley-Graph-Conjecture-strength sup-norm bound
on the sup-norm axis (moment method is one-way). So the prize localizes to `WallHolds ∧
HyperplaneCancellation`, two **irreducibly independent** named open Props, with **no named glue**
between them: neither is the sole bottleneck.

---

## 2. Lane I — the two-sided iff certificate

**Verdict: IFF-PARTIAL-NAMED-GLUE.** The outer layer is a genuine, machine-checked, axiom-clean
two-sided iff; the inner reduction to the two open Props stays a named, honestly-flagged glue.

`_TwoSidedCapstone.lean` (six theorems, all `#print axioms = [propext, Classical.choice, Quot.sound]`,
no `sorryAx`; verified via `pg-iterate`, OK 37s) proves:

### 2.1 The outer iff (proven both directions, axiom-clean)

> **`epsMCA_le_iff_worstCaseIncidenceBounded`** :
> `ε_mca(C, δ) ≤ B/q  ⟺  WorstCaseIncidenceBounded C δ B`.

- **Forward** (`mp`) is the in-tree `epsMCA_le_of_worstCaseIncidence`.
- **Reverse** (`mpr`, `worstCaseIncidenceBounded_of_epsMCA_le`, proved here) unfolds `ε_mca` as the
  `iSup` of per-stack probabilities `Pr = (#bad)/q ≤ ε_mca ≤ B/q`, then cancels the positive finite
  denominator `q`. No named glue, no circularity.

Specialized to `ε* = E/q` this is `deltaStar_good_iff_worstCaseIncidenceBounded_budget`: a radius
`δ` is `ε*`-good — i.e. `δ` lies in the `δ*` good-radius set `mcaGoodRadii` whose `sSup` is
`mcaDeltaStar` — **iff** `WorstCaseIncidenceBounded C δ E`. The incidence Prop and the governing-law
budget are the **same object**, both ways.

**Honest caveat (disclosed, not a defect).** This iff is near-*definitional* — "sup ≤ bound ⟺ every
summand ≤ bound" — not a deep reduction. Its value is that it makes the budget side **exact**, so all
open content is correctly pushed into the named glue below, none of it laundered through a soft step.

### 2.2 Sufficiency (⟸): FULLY PROVEN

`deltaStar_floor_of_incidence` : `WorstCaseIncidenceBounded C δ E ⟹ δ ≤ mcaDeltaStar C (E/q)`, via
the in-tree `worstCaseIncidence_pin_budget` at an **abstract** natural budget `E` — **not** the
vacuous `⌈|G|+q·B⌉`. Every step is an in-tree theorem; the iff makes the budget side exact.

### 2.3 Necessity (⟹): PROVEN, but only in local/pointwise form

`incidence_of_deltaStar_good` : if `δ` is itself `ε*`-good (`ε_mca(C, δ) ≤ E/q`, the named hypothesis
`hGoodAt`) then `WorstCaseIncidenceBounded C δ E`. This is the `.mp` of the iff.

The honest subtlety, stated in-file: the raw floor `δ ≤ mcaDeltaStar C (E/q)` says the *supremum* of
good radii is `≥ δ`; monotonicity (`mca_good_set_downward_closed`) then forces goodness only for radii
*strictly below* the floor, and at the non-attained `sSup` boundary the incidence Prop can fail *at*
`δ*`. So the necessary condition is consumed as the explicit named hypothesis `hGoodAt` (goodness AT
`δ`), **not** silently upgraded from `δ ≤ δ*`. Necessity is therefore honestly labeled
pointwise/local only.

### 2.4 The inner reduction to the two open Props (named glue, NOT re-proved here)

The incidence Prop `WorstCaseIncidenceBounded C δ E` is the δ\*-side shadow of BOTH open inputs
composed. Via `CharSumDeltaStarBridge`, the naive route bounds `#bad ≤ ⌈|G| + q·B⌉` from `M` alone
— but this budget is **VACUOUS at the prize** (`E ≈ n` forces `B ≈ 0`; the `q·B` is the
triangle-summed naive bound, exactly the absence of √-cancellation). Making it non-vacuous needs the
worst-case `√q·B` cancellation `HyperplaneCancellation` on top of `WallHolds`'s `M`. This reduction is
kept as the named `def IncidenceFromWallGlue` — a pure `Prop`, never consumed by any theorem in the
file — so no vacuous budget is laundered into the certificate.

---

## 3. Correction to dossier §0 (honesty item)

Dossier v3 §0 asserts "**`ERM-at-r ⟺ M ≤ √((2r+1)n)`, two-sided**". This is **prose in a docstring**
(`_EnergyRatioMonotoneReduction.lean` line 48), **not** a proven Lean iff. That file:

- proves only the **forward** `gaussianEnergyBound_of_ERM` (ERM ⟹ the Gaussian energy bound), and
- states in its own docstring that **ERM is REFUTED as a global claim** — by exact bigint
  computation, `E_7/(n·E_6) = 13.60 > 13` at `n = 32`, `r = 6→7`, inside the window `r < (n−1)/2`.

A grep across the whole cone finds **no** `energyRatioMonotone_iff` / ERM⟺M anywhere. So the reverse
(sup-norm ⟹ ERM/moment-tower) is correctly **not** in-tree — fully consistent with Lane D's finding
that the sup-norm is strictly weaker than the tower. No laundering; the §0 line should be read as a
heuristic, not a machine-checked iff. The campaign's **real** machine-checked two-sidedness is the
Lane-I `epsMCA ⟺ incidence` iff (outer, definitional), not an ERM⟺M iff.

---

## 4. The honest final state after 14 rounds — the tightest machine-checked certificate

The complete reduction, stated precisely, with each link's honest status:

```
                 ┌─────────────────────────────── OUTER: two-sided iff, axiom-clean ────┐
   δ*-floor  ⟺   WorstCaseIncidenceBounded C δ E                (epsMCA_le_iff_…, both ways)
  (δ ≤ mcaDeltaStar C (E/q))          │                          SUFFICIENCY ⟸ FULLY PROVEN
                                      │                          NECESSITY   ⟹ PROVEN (local, hGoodAt named)
                                      │
                 ┌── INNER: named glue IncidenceFromWallGlue (NOT re-proved; open) ──────┐
   WorstCaseIncidenceBounded  ⟸  WallHolds  (supplies M via supNorm_le_of_wallHolds)
                                      ∧  HyperplaneCancellation  (supplies the √q·B step)
```

- **Outer layer** — machine-checked BOTH directions, axiom-clean: `δ*`-floor ⟺ the in-tree
  incidence Prop `WorstCaseIncidenceBounded C δ E`. Sufficiency fully proven; necessity proven in
  pointwise form with `hGoodAt` named.
- **Inner layer** — the reduction of the incidence Prop to `WallHolds ∧ HyperplaneCancellation` is a
  one-directional named glue (`IncidenceFromWallGlue`), with the vacuous naive `q·B` budget honestly
  quarantined and the non-vacuous `√q·B` step correctly kept open (BCHKS Conj 1.12).
- **The two inner inputs are INDEPENDENT** (Lane D): neither implies the other, no glue between them.

**Scope caveat (explicit).** "Two-sided/iff" applies to the OUTER layer (δ\*-floor ⟺ incidence
Prop), **not** to δ\*-floor ⟺ (`WallHolds ∧ HyperplaneCancellation`). The inner reduction to the two
open Props remains a one-directional named glue. The master-gap identity `δ* = (1−ρ) − m*/n` and the
`Θ(n/log n)` ceiling (`kkh26_mcaDeltaStar_le_of_TZ`) frame the arithmetic target; they are unchanged.

---

## 5. The open core(s), named

Both open inputs remain named open Props; nothing is discharged, silently or vacuously:

- **`WallHolds G := ∀ r, DCEnergyCorrection.DCEnergyBound G r`** — the per-rung DC-subtracted char-`p`
  Wick/moment tower. Non-vacuous (`DCEnergyBound G r := q·E_r − |G|^{2r} ≤ q·(2r−1)‼·|G|^r`). Supplies
  the sup-norm `M` via `supNorm_le_of_wallHolds`. **OPEN, ON-BGK** (best proven `n^{1−o(1)}`).
- **`HyperplaneCancellation := ∀ s₀, ‖∑_{b∈H} conj(η_b) ψ(b·s₀)‖ ≤ √|H|·M`** — the worst-case
  per-frequency `√q·B` cancellation, = BCHKS Conj 1.12 / Paley-graph worst case. A phase-correlation
  object, proven distinct from `WallHolds` in BOTH directions. **OPEN.**
- **`PaleyGraphConjecture := M ≤ 2√n`** — the sup-norm / non-principal Paley-graph eigenvalue bound;
  weaker than `WallHolds` by the eigenvalue–moment interchange. **OPEN.**

Supporting named hypotheses inside the certificate: `hGoodAt` (goodness AT `δ`, for full necessity at
the non-attained sup point) and `IncidenceFromWallGlue` (the inner reduction, containing the open
`√q·B` step). Both are correctly kept named.

**The prize is NOT closed. The wall is NOT closed.** After 14 rounds the reduction is capstoned,
tightened, and now fully characterized: the entire open surface is exactly two independent named
Props, with the outer δ\*-reduction machine-checked two-sided and axiom-clean, and every remaining
obligation named — modularity, not incompleteness.

---

## Abstract

Round 13 established that the prize localizes to two distinct open inputs rather than one; round 14
completes that thread by characterizing their relationship and assembling the tightest honest
two-sided certificate. **Lane D** proves the two open Props are **INDEPENDENT**: `WallHolds ⟹
HyperplaneCancellation` is false (round 13 — the wall's sup-norm `M` is phase-blind, controlling only
the `s₀`-average of the hyperplane incidence), and `HyperplaneCancellation ⟹ WallHolds` is false
(round 14, `_R14SupNormWeakerThanWall.lean` — `HyperplaneCancellation`'s only spectral input is `M`,
and the sole per-rung fact `M ≤ B` yields is the Hölder projection `A_r ≤ |H|·B^{2r}`, which strictly
exceeds the Wick RHS `q·(2r−1)‼·n^r` at `r = 1`, so the moment tower cannot be recovered). Neither is
the sole bottleneck; both are needed, with no named glue between them. **Lane I**
(`_TwoSidedCapstone.lean`) certifies, axiom-clean both directions, the outer iff `ε_mca(C,δ) ≤ E/q ⟺
WorstCaseIncidenceBounded C δ E`, whence δ\*-floor sufficiency is fully proven and necessity is proven
in pointwise/local form with the named hypothesis `hGoodAt`; the inner reduction of the incidence Prop
to `WallHolds ∧ HyperplaneCancellation` stays a one-directional named glue (`IncidenceFromWallGlue`)
with the vacuous naive `q·B` budget quarantined and the non-vacuous `√q·B` step honestly open. A
verified honesty correction: dossier §0's "ERM-at-r ⟺ M ≤ √((2r+1)n), two-sided" is docstring prose,
not a Lean iff — ERM is globally REFUTED and only the forward implication is in-tree — consistent with
Lane D. After 14 rounds the open surface is exactly the two independent named open Props (`WallHolds`
ON-BGK, `HyperplaneCancellation` = BCHKS Conj 1.12), with the outer δ\*-reduction machine-checked
two-sided; the wall and prize remain OPEN, and every obligation is named.

## Round-14 artifact files

- `docs/kb/deltastar-466-essay-round14-2026-07-04.md` (this essay)
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R14SupNormWeakerThanWall.lean` (Lane D; axiom-clean, OK 25s)
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_TwoSidedCapstone.lean` (Lane I; axiom-clean, OK 37s)
- `scripts/probes/probe_466r14_relationship.py` (Lane D probe)
- `scripts/probes/_out_466r14_relationship.txt` (Lane D probe output)

### Round-13 / substrate files load-bearing for round 14 (verified, not new this round)

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R13HyperplaneSecondMoment.lean` (Direction 1)
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_MomentOptimizedSupNorm.lean` (`WallHolds ⟹ M`)
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_WallCapstone.lean` (`WallHolds`, `RealizedIncidenceBudget`)
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_EnergyRatioMonotoneReduction.lean` (§3 correction; ERM refuted)
- `ArkLib/Data/CodingTheory/ProximityGap/CharSumDeltaStarBridge.lean` (vacuous naive `q·B` budget)
- `ArkLib/Data/CodingTheory/ProximityGap/OpenCoreConditionalPin.lean` (`WorstCaseIncidenceBounded`, `worstCaseIncidence_pin_budget`)
- `ArkLib/Data/CodingTheory/ProximityGap/DCEnergyCorrection.lean` (`DCEnergyBound`, `WallHolds` per-rung)
- `ArkLib/Data/CodingTheory/ProximityGap/MCAThresholdLedger.lean` (`mcaDeltaStar`, `mcaGoodRadii`, `le_mcaDeltaStar_of_good`)

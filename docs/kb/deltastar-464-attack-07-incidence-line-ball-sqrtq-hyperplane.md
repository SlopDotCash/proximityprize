# Attack #07 — Line-ball incidence / WorstCaseIncidenceBounded via hyperplane √q cancellation

**Issue:** #464 (Ethereum Proximity Prize). **Date:** 2026-06-27. **Status:** partial; the angle's
only structural lever is REFUTED axiom-clean; the residual is exactly the Paley/BCHKS-1.12 wall.

## 0. Target theorem (what closing this angle would prove)

Discharge open input (2) of the two-sided conditional pin
(`Frontier/_PrizeFloorOfBGK.lean`, `OpenCoreConditionalPin.WorstCaseIncidenceBounded`):

> For the explicit smooth-domain RS code `C` (`n=2^30`, `q≈n·2^128`), at the window-interior
> radius `δ`, every word-stack `u=(u₀,u₁)` has
> `#{γ : mcaEvent C δ (u 0) (u 1) γ} ≤ B` with `B/q ≤ ε* = 2^-128`,
> i.e. `I ≤ |G| + √q·B` with the **per-frequency √q cancellation** over the annihilator
> hyperplane (BCHKS Conjecture 1.12).

Proving this unconditionally closes the prize. The angle's premise: the **L²/Parseval (average)**
half of this is already proven; maybe a *structural maximizer* argument upgrades the proven
average to the worst case without invoking full Paley.

## 1. The substrate, precisely

The incidence↔period dictionary is fully proven and axiom-clean:

- `IncidencePeriodBridge.lineIncidence_period_sum`:
  `I(s₀,s₁) = ∑_{b : b·s₁=0} conj(η_b)·ψ(b·s₀)` (term-by-term, over the annihilator hyperplane).
- `IncidenceDeviationCharSum.incidence_sub_mean`: subtract the `b=0` principal term `η₀=|G|`,
  leaving `D(s₀) := I(s₀,s₁)−|G| = ∑_{b∈dev} conj(η_b)·ψ(b·s₀)`.
- **The L²-over-offset cancellation is PROVEN** (`IncidenceDevL2Offset.dev_l2_offset_eq`):
  `∑_{s₀} ‖D(s₀)‖² = q·∑_{b∈dev} ‖η_b‖²`,
  so the **root-mean-square deviation over offsets is exactly `√q·B`-scale** — the prize scale,
  for free, by additive-character orthogonality (`incidence_dev_meansq_offset_le_sqrtq`).
- The naive pointwise bound (`incidence_dev_le`) is the triangle `(#dev)·B ≤ q·B`, **vacuous**
  at the prize budget for any `B>0` (`CharSumDeltaStarBridge`: budget forces `B≲0`).

So the gap between proven and prize is *exactly* `L²(offset) → L∞(offset)`: turning the proven RMS
`√q·B` into a bound at the single worst offset `max_{s₀}‖D(s₀)‖`.

## 2. Proof attempt (the three levers from the directive)

**(a) Maximizer domination (`StackMaximizerDomination`).** A global maximizer stack `uMax`
always exists (`exists_stackDominates`, nonconstructive `Finite.exists_max`), and
`WorstCaseIncidenceBounded C δ B ⟺ StackBadCount uMax ≤ B`. This reduces the universal bound to
ONE stack — but *identifying* `uMax` and *bounding* its count is the whole problem; the existence
is content-free. No structured candidate dominates: `not_stackDominates_of_exists_strictly_larger`
is the exact warning that a "symmetric/convenient" stack is not the maximizer.

**(b) Hyperplane √q without full Paley (Weil on the restricted curve).** The hope: `D(s₀)` is a
character sum over the `s₁^⊥` hyperplane; a Weil/Bombieri square-root bound on the restricted
incidence variety might give `‖D(s₀)‖ ≲ √q·B` pointwise. But the restriction collapses the
geometry: over `V=F` a far direction `s₁≠0` makes the line fill `F`, so `deviationSupport = ∅`
and `D ≡ 0` (`RealizerL2NotSup.farLine_incidence_eq_card` — incidence is exactly `|G|`,
sup-blind). The only spectrum-sensitive direction is the degenerate `s₁=0` ("line" = point),
where `D(s₀) = q·[s₀∈G] − |G|` is the **explicit integer step** — no curve, no Weil, just a delta
spike of height `q−|G|` at every `s₀∈G`.

**(c) Stepanov on the incidence variety.** Same collapse: the variety in the spectrum-sensitive
direction is the 0-dimensional point set `G`, on which Stepanov's auxiliary-polynomial method has
no traction (it counts roots of a curve; here the "curve" is a finite point set with a genuine
mass spike).

## 3. The refutation (axiom-clean Lean brick)

`Frontier/_Attack07L2LinfGap.lean` proves, with NO field-size/regime hypothesis:

- `devField_zero_dir`: `D(s₀) = q·[s₀∈G] − |G|` (explicit step), via `lineIncidence_zero_dir`.
- `devField_zero_dir_mem`: `‖D(s₀)‖ = q − |G|` for every `s₀∈G` (the spike, `Θ(q)`).
- `linf_ge_q_sub_card`: `max_{s₀}‖D(s₀)‖ ≥ q − |G|` (explicit witness offset in `G`).
- `meansq_zero_dir`: `(1/q)∑_{s₀}‖D(s₀)‖² = |G|·(q−|G|)` (the EXACT mean-square; matches
  `dev_l2_offset_eq` with `∑_{b∈dev}‖η_b‖² = q|G|−|G|²`).
- `linf_sq_over_meansq_eq`: `(q−|G|)² / (|G|(q−|G|)) = (q−|G|)/|G|` (exact deficit factor).
- `linf_sq_gt_meansq` (**headline**): once `q > 2|G|` (the prize regime `q≈n·2^128 ≫ |G|=n`),
  the squared sup `(q−|G|)²` STRICTLY exceeds the mean-square `|G|(q−|G|)`.

**Conclusion:** the worst offset's squared deviation is `(q−|G|)/|G| ≈ q/n ≈ 2^128` times the
mean-square. The proven L² (RMS `√q·B`) cancellation **cannot** bound the L∞ worst offset — the
deficit is the full budget. The L²→L∞ upgrade is genuinely unavailable; it is not an artifact of
the loose triangle bound. (Axioms: `propext, Classical.choice, Quot.sound`; real `lake build` of
`...Frontier._Attack07L2LinfGap` passes under `autoImplicit=false`.)

## 4. Numerical corroboration

- `scripts/probes/probe_2d_annihilator_incidence_supVSavg.py`: in the genuine ≥2-D MCA geometry
  the worst-case incidence `maxI2` re-couples to `B` (both p-dependent) and `maxI2 ≈ q` —
  the L∞ spike is `Θ(q)`, NOT `√q·B`.
- Direct offset-L∞ probe (this session, `n∈{8,16}`, `p∈{41,73,241,257}`): for the
  spectrum-sensitive direction, `max_{s₀}‖D(s₀)‖ = q−n` exactly (= `225` at `p=241,n=16`, etc.),
  while RMS `= √(n(q−n))`; the ratio `maxD/RMS = √((q−n)/n)` grows as `√q` — matching
  `linf_sq_over_meansq_eq`.

## 5. Lever analysis — where it reduces to the wall

The exact reduction point: the worst-case offset can have **all `#dev≈q` phases align
constructively**. In the degenerate direction the spike is the trivial `s₀∈G` mass collapse; in
the genuine ≥2-D MCA direction the spike is the **off-diagonal constructive interference of the
`η_b` phases**, and bounding it by `√q·B` (forbidding the alignment for the actual `μ_n` periods)
is precisely BCHKS Conj 1.12 = the generalized-Paley-graph eigenvalue bound `B ≤ 2√n` /
`n^{1/2}`-regime BGK. The L² average is phase-blind (Parseval kills cross terms); the L∞ sup is
phase-sensitive (one offset realizes the alignment). This is the same phase-cancellation wall
that ~60 prior sessions hit from every analytic route.

**No lever crosses.** (a) is content-free existence; (b) and (c) collapse because the
spectrum-sensitive geometry is 0-dimensional (a point/mass spike), so there is no curve for
Weil/Stepanov to act on — the cancellation that the prize needs lives entirely in the
archimedean phases of the `η_b`, which the L² bridge cannot see.

## 6. Honest verdict

- **NOT a closure.** The prize input (2) is NOT discharged.
- **Does NOT bypass Paley.** The residual sup-over-offset IS BCHKS-1.12 / Paley.
- **Genuine partial result:** an axiom-clean, regime-free theorem that the L²→L∞ upgrade — the
  one structural lever this angle offers over the proven average — is *quantitatively
  unavailable*, with the exact deficit `(q−|G|)/|G|`. This sharpens `IncidenceDevL2Offset`'s
  honesty header from a remark into a proved obstruction, and complements `RealizerL2NotSup`
  (sup-blind in 1-D) by exhibiting the `Θ(q)` L∞ spike that the average hides.
- **Named open input remaining:** `OpenCoreConditionalPin.WorstCaseIncidenceBounded C δ B` (= the
  per-frequency `√q·B` sup-over-offset / BCHKS Conjecture 1.12).

**Survives adversarial self-refutation:** the brick proves a strict inequality with explicit
witnesses, machine-checked; the only way it could be "wrong" is if the prize did not actually need
the L∞ sup (it does — `epsMCA_le_of_worstCaseIncidence` consumes the worst-case count, not the
average).

# #444 Residue Census Update — 2026-06-18

**Scope.** Consolidation snapshot for the Reed–Solomon proximity-gap prize (#444) after the
char-`0` / transfer-identity formalization wave. This entry records what is now **discharged
(axiom-clean)**, the **single remaining open obligation**, and the **proven foreclosures**. It is a
documentation entry only; no Lean is changed by it.

**Honesty contract.** #444 remains a recognized OPEN problem. Nothing below closes it. The open
core is the for-all-`q` BGK/Paley sup-norm wall

> `M(μ_n) = max_{b ≠ 0} |Σ_{y ∈ μ_n} e_p(b y)| ≤ C · √(n log m)`

for `μ_n = ` the `2^μ`-th roots of unity in `F_p^*` (`n = 2^μ`, thin regime `n ∼ p^{1/4}`).
This is unconditionally OPEN. The work below isolates that wall behind ONE named hypothesis and
records the routes proven NOT to reach it.

---

## 1. Discharged named hypotheses (axiom-clean, `[propext, Classical.choice, Quot.sound]`)

These were previously consumed as free inputs by the ladder / slack route and are now proven
unconditionally in-tree. "Discharged" here means: a concrete provider with no `sorryAx`, no
residual deps, all binders explicit, non-vacuous.

| Hypothesis | Carrier brick(s) | What is proven |
|---|---|---|
| **Char-`p` → moment transfer identity** | `Frontier/_AvCP_WrEqMomentIdentity.lean` (`collision_count_eq_moment`, `moment_split_off_dc`, `Wr_eq_moment_transfer`) | The char-`p` energy excess `W_r` equals the off-DC `2r`-th moment of the period sums. Establishes that the char-`p` side **is** the BGK `2r`-moment object — no separate analytic wall is introduced by the transfer. |
| **Char-`0` Lam–Leung 2-power balance** | `Frontier/_AvX_LamLeungTwoPowerAntipodalBalan.lean`, `_AvX_VanishingTwoPowSumIsAntipodalP.lean`, `_AvX_AntipodalPairSumZero.lean`, `_AvX_AntipodalHalfShiftNeg.lean` | Vanishing sums of `2^μ`-th roots are exactly antipodal-paired (Lam–Leung specialized to prime-power `2`); the char-`0` collision structure is pinned. |
| **Cyclotomic bridge `Φ_{2^{k+1}} = X^{2^k}+1`** | `Frontier/_AvX_CyclotomicTwoPowEqXPowAddOne.lean`, `_AvX_PrimitiveTwoPowRootHalfPowerEq.lean` | The minimal polynomial / half-power identity used to reduce char-`0` energy to closed form. |
| **Mean-zero / first-moment** | `Frontier/_AvY_subgroup_gaussSum_firstMomen.lean`, `_AvY_negationClosed_double_count_.lean`, `_AvY_worstCase_period_lower_bound.lean`, `_AvY_card_large_frequencies_le_pr.lean` | Subgroup Gauss-sum first moment, negation-closure double count, Parseval `√n` period lower bound. |
| **Sidon-except-negation rep count** | `Frontier/_AvY_SidonNegRepCountLeTwo.lean`, `_AvX_AntipodalTransversalEvenCardLe.lean` | `μ_n` is Sidon apart from the single additive obstruction (antipodal `σ = 0`): every non-zero sum has ≤ 2 representations. |
| **Char-`0` energy closed forms `E_r`, `r = 7..33`** | `Frontier/_AvL2_E{7..14,16..33}ClosedForm.lean` (gap at `r = 15`), `REnergyThreeCharZero.lean` / `CharZeroEnergyThreeExact.lean` (`T_3`) | Exact integer closed forms for the char-`0` energies along the ladder, feeding the Wick ceiling discharge. Earlier rungs `r = 2..6` already discharged (`_CharZeroEnergyClosedForm.lean`); the ladder covers `r = 7..33` with a single gap at `r = 15`, well past `r ≈ ln q` scale. The general-`r` Wick bound `E_r ≤ (2r-1)‼·n^r` is the per-rung polynomial inequality on this ladder; the uniform-in-`r` form needs the Bessel/Lam–Leung analytic input (a separate named obligation). |
| **No-Excess onset framework** | `Frontier/_NoExcessOnsetThreshold.lean`, `_AvCP_W3UnconditionalOutsideD3.lean`, `_AvW3_Depth3BadPrimeSet.lean` | `W_r = 0` outside a finite "bad-prime" set at fixed shallow `r` (onset-threshold structure, not a birthday power law); `W_3 = 0` unconditionally outside an explicit depth-3 bad-prime set. |
| **Good-prime saddle assembly** | `Frontier/_AvLadderSaddleAssembly.lean` (`energyCharP_eq_char0_add_wrapExcess`, `noWraparound_imp_energy_eq`, `energyCharP_le_of_noWraparound_of_char0_le`, `uniform_wick_of_uniform_wrapExcess_zero`), `_AvT3a_DiBenedettoBeatAssembly.lean`, `_AvCP_DiBenedettoGoodPrimeBridge.lean` | Assembles char-`p` energy `= ` char-`0` energy `+ ` wrap-excess; given no-wraparound + char-`0` Wick bounds, the good-prime prize-scale sup bound follows. di Benedetto good-prime bridge / beat assembly attached. |
| **Moment → sup transfer (capstone)** | `Frontier/_AvPrize_MomentToSupCapstone.lean` (`moment_to_sup_budget`, `prize_sup_sqrt`, `prize_sup_of_saddle`) | The `r`-th-root step from a `2r`-moment bound to the `√(n log m)` sup bound at `r ≈ log K`. The analytic plumbing from "moment ladder holds" to "prize sup bound" is closed; only the moment-ladder input is open. |

---

## 2. The single remaining open obligation

> **`UniformNoWraparoundUpTo r*`**
> (`Frontier/_AvLadderSaddleAssembly.lean`, `def UniformNoWraparoundUpTo`, consumed by
> `moment_route_uniform_wick_of_onset` / `ladder_prefix_subsumed`).

Plain reading: the char-`p` energy has **no wraparound excess** uniformly for every depth `r` in
the prize window `(29, r*]`, at the prize prime, in the thin regime. This is exactly the BGK / Paley
char-`p` wall re-expressed as the vanishing of `wrapExcess` up the ladder to `r* ≈ ln q`.

Status: **GENUINELY OPEN.** This is the prize core. The ladder discharges every other input and
reduces the good-prime prize sup bound to this one hypothesis, but does NOT prove it. It is refuted
to hold *unconditionally at all r* at the prize prime via the No-Excess bad-prime sets being
non-empty deep in the ladder — i.e. the obligation is the honest residual, not a stub.

---

## 3. Proven foreclosures (routes that provably do NOT reach the wall)

These are not gaps; they are theorems that a class of approaches cannot close the open core.
Recording them prevents re-running dead routes.

- **Ideal-theoretic / exotic two-bucket dichotomy.** Every "exotic" off-BGK invention sorts into
  one of two buckets — reduces to the BGK `2r`-moment, or is refuted by exact char-`p` computation.
  Brick family: `_AvM1_HalaszSignedMomentNoGo.lean` (Halász signed-moment no-go),
  `_AvN1_MonomialWeylVMVTVacuous.lean`, `_AvN3_GumbelTailRefuted.lean`,
  `_AvN4_PadicMahlerSupplyGap.lean`, `_AvSieve1_SplitPrimeSieveVacuous.lean`,
  `_AvE1_WraparoundCofactorVacuous.lean`, `_AvE2_PaleyRamanujanSubseqRefuted.lean`,
  `_AvE3_SubgroupGrowingRWall.lean`, `_AvE4_SidonOffSpikeFloor.lean`,
  `_AvE5_ExistsGoodPrimeNonSequitur.lean`, `_AvE6_LargeSieveVacuous.lean`.

- **Moment / energy route is necessity-only.** No moment method at any depth reaches the target
  `√(n log(q/n))` (in-tree `moment_ladder_exceeds_prize`); the moment ladder is a *necessary*
  reformulation (`_AvCP_WrEqMomentIdentity` shows it IS the wall), not a sufficient bypass.
  `_AvK1_EnergyKUniformityExtrapolation.lean` records the `k`-uniformity extrapolation limit.

- **For-all-`q` exponent floor.** `_AvUNIF_BestForallQExponent.lean`
  (`weil_weaker_than_trivial_in_prize_regime`, `prize_needs_subtrivial_uniform`, `sota_gap_for_forallq`):
  in the thin prize regime Weil is weaker than the trivial bound, and the prize requires a
  sub-trivial uniform exponent that current SOTA (di Benedetto `H^{1−31/2880}`, vanishing at
  `|H| > p^{1/4}`) does not deliver for-all-`q`. Quantifies the residual half-power gap.

- **Distinct-γ / orbit growth side (off-BGK, separate).** The `p`-independent distinct-γ union-count
  governing `δ*` is a SEPARATE frontier from the sup-norm wall; its growth law is open but off the
  char-sum route (`_AvC1_DistinctGammaCyclicOrbit.lean`, `_AvC3_GrowthVsBudgetMStar.lean`,
  `_AvL7_OrbitSizeAtBinder.lean`, `_AvL12_BindingDiagonalOrbitCountConstant.lean`,
  `_AvPD_PerDirectionOrbitCount.lean`). Recorded for completeness; not part of the sup-norm
  obligation in §2.

---

## 4. One-line ledger

Discharged (axiom-clean): transfer identity, Lam–Leung 2-power, cyclotomic bridge, mean-zero,
Sidon-neg, `E_r` ladder `r ≤ 33`, No-Excess onset, saddle assembly, moment→sup capstone.
**Single open obligation:** `UniformNoWraparoundUpTo r*` (= BGK/Paley char-`p` wall).
**Foreclosed:** ideal-theoretic/exotic (two-bucket), moment route (necessity-only), for-all-`q`
exponent floor. **closesOpenCore = false.**

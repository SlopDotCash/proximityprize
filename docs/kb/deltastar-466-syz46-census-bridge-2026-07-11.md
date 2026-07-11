# SYZ46 — the census bridge: strip per-stack bad-count ⇒ the δ* bracket (2026-07-11, corrected)

Issue #466 (Proximity Prize / proximity-gap). Rate `1/2`, `n = 2³⁰`, `k = 2²⁹`,
`ε* = 2⁻¹²⁸`, first certified prize field `P = PrizeShapePrimeP30.P`,
smooth-domain code `evalCode g (2³⁰) (2²⁹ − 1)`.

File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ46CensusBridge.lean`
(axiom-clean: `[propext, Classical.choice, Quot.sound]`; no `sorry`, no `native_decide`).

## RETRACTION of the first draft (commit `1f12870b6`) — credit: the SYZ3 witness

The first SYZ46 draft placed the strip census hypothesis at the `31/64`-predecessor radius
`predecessorRadius (2³⁰) (31·2²⁴)` and concluded a two-sided pin `δ* = 31/64`. **That hypothesis is
unsatisfiable**: `_SYZ3OverBudgetStackWitness.lean` (`firstPrime_predecessor_cap_refuted`) exhibits
an explicit degenerate stack with `3·31·2²⁴ = 1,560,281,088 > 2³⁰` bad scalars at exactly that
radius. The draft's conditional theorem `deltaStar_pinned_of_strip_master_hypothesis` was therefore
vacuously true — the laundering pattern the campaign forbids — and its conclusion `δ* = 31/64` even
contradicted the unconditional SYZ4/SYZ6 ceiling `δ* ≤ 358612991/2³⁰ ≈ 0.334`. That theorem is
**deleted**; the retraction is machine-checked in-file:

- `RefutedPredecessorCensusBound` (the old hypothesis, kept only as a labelled tombstone), and
- `refutedPredecessorCensusBound_is_false : ¬ RefutedPredecessorCensusBound`
  (proved from the SYZ3 witness).

Root cause: the strip machinery bounds bad counts at radii **inside the strip** (`δ < 1/3`), not at
the `31/64` predecessor. Caught by the coordinator audit against SYZ3.

## What this file is (corrected)

SYZ33's header names four "not-cheap" wires still needed to chain the strip theorem to a production
δ* statement at `n = 2³⁰`. SYZ46 formalizes **wire (iv)**, verbatim from that header:

> "the `MCAThresholdLedger` bridge from the count bound `#bad ≤ n − 1` to the `δ*` floor."

Nothing here is open math — pure re-assembly of landed pieces, now at the correct strip radius.

## Deliverables

1. **Task 1 — the general census bound** (`epsMCA_le_of_bad_count_le`). A `mcaBadCount`-phrased
   re-export of `ProximityGap.epsMCA_le_of_badCount_le`:
   `(∀ u, mcaBadCount C δ (u 0) (u 1) ≤ B) → epsMCA C δ ≤ B / |F|`, straight from
   `epsMCA_eq_iSup_mcaBadCount` (the worst-case-uniform-probability definition of `epsMCA`).

2. **`StripCensusBound`** — the single Lean hypothesis, at the corrected radius. With
   `stripNumerator := 357913941 = (2³⁰ − 1)/3` (largest `a` with `a/2³⁰ ≤ 1/3`):

   ```
   def StripCensusBound : Prop :=
     ∀ u : WordStack (ZMod P) (Fin 2) (Fin (2 ^ 30)),
       mcaBadCount (F := ZMod P)
           (evalCode g (2 ^ 30) (2 ^ 29 - 1))
           (predecessorRadius (2 ^ 30) stripNumerator)
           (u 0) (u 1) ≤ 2 ^ 30 - 1
   ```

   Census radius `= 357913940/2³⁰ < 1/3`, strictly inside the strip. No in-tree witness refutes it
   (unlike the retracted variant).

3. **Conditional floor** (`deltaStar_ge_stripBoundary_of_census`), **floor only**:

   ```
   theorem deltaStar_ge_stripBoundary_of_census (h : StripCensusBound) :
       ((stripNumerator : ℕ) : NNReal) / ((2 ^ 30 : ℕ) : NNReal) ≤
         mcaDeltaStar (F := ZMod P) (A := ZMod P)
           (evalCode g (2 ^ 30) (2 ^ 29 - 1))
           (ProximityGap.epsStar : ENNReal)
   ```

   i.e. `δ* ≥ 357913941/2³⁰ = 1/3 − 1/(3·2³⁰)`. Chain: census clears
   `(2³⁰−1)/P ≤ 2³⁰/P ≤ 2⁻¹²⁸ = ε*` (the `hbudget` arithmetic) ⟹ `ε_mca ≤ ε*` at the predecessor
   ⟹ `latticeBoundary_le_mcaDeltaStar_of_predecessor_good`.

4. **Two-sided bracket** (`deltaStar_bracket_of_census`): floor + the **unconditional** SYZ6
   ceiling (`firstPrime_rateHalf_mcaDeltaStar_le_exact`):
   `357913941/2³⁰ ≤ δ* ≤ 358612991/2³⁰` — both endpoints near `1/3`, width
   `699050/2³⁰ ≈ 6.5·10⁻⁴`. **No equality / pin is claimed.**

## THE conditional bracket — verbatim statement

```
theorem deltaStar_bracket_of_strip_master_hypothesis
    (H : ArkLib.ProximityGap.SYZ42.StripMasterHypothesis'' (ZMod P) V (2 ^ 30) (2 ^ 29))
    (transport :
      ArkLib.ProximityGap.SYZ42.StripMasterHypothesis'' (ZMod P) V (2 ^ 30) (2 ^ 29) →
        StripCensusBound) :
    (357913941 : NNReal) / (2 ^ 30 : NNReal) ≤
        mcaDeltaStar (F := ZMod P) (A := ZMod P)
          (evalCode g (2 ^ 30) (2 ^ 29 - 1))
          (ProximityGap.epsStar : ENNReal) ∧
      mcaDeltaStar (F := ZMod P) (A := ZMod P)
          (evalCode g (2 ^ 30) (2 ^ 29 - 1))
          (ProximityGap.epsStar : ENNReal) ≤ (358612991 : NNReal) / (2 ^ 30 : NNReal)
```

with `{V : Type*} [AddCommGroup V] [Module (ZMod P) V] [Module.Finite (ZMod P) V]`,
`P = ArkLib.ProximityGap.PrizeShapePrimeP30.P`, `g = ...PrizeShapePrimeP30.g`.
Proof: `deltaStar_bracket_of_census (transport H)`. The ceiling half is unconditional (SYZ6);
only the floor consumes the hypotheses.

## Complete, scrupulously honest hypothesis list

`StripCensusBound` is **not proved** here; it is the transported strip conclusion, folded into one
`Prop`. Its discharge requires, verbatim (SYZ33 header items (i)–(iv); SYZ40/42/43):

- **(i) `StripMasterHypothesis''.uniformSylvester`** — `SYZ40.UniformSylvesterInjective (ZMod P) n k`.
  The sole substantive open input: SYZ38 generalized-Sylvester injectivity, characterized by SYZ39
  as a bounded-height resultant non-vanishing (BGK type / additive cancellation over `μ_n`) at
  `n = 2³⁰`. Controls only the **spread branch** (`m ≥ 4`) of the strip. The **merged branch**
  (`m ≤ 3`) is already unconditional (`SYZ40.merged_branch_unconditional`).
- **(ii)** the SYZ18 / `twist_pair_indep` disjoint-residual support control (SYZ33 lemma-1 input (a)).
- **(iii) `StripMasterHypothesis''.realizabilityCore`** — the SYZ22 `SuperadditiveUnion`
  production-ledger join, in generation language. SYZ43 (`realizabilityCore_of_mcaEvent_witnesses`)
  proves its existence residue is **auto-instantiated** by any over-budget `mcaEvent` stack via the
  G87 syndrome bridge, leaving only the union-rank lower bound `hrank`
  (`realizabilityCore_of_overBudget_stack`'s sole hypothesis) — a residual **separate** from (i).
- **(iv)** the abstract-to-concrete **transport** itself: routing SYZ40's abstract band-triple /
  union-budget strip conclusion, through the G87 `mcaEvent`→syndrome bridge, to the per-stack
  `mcaBadCount` cap at the concrete smooth-domain `evalCode` **at the strip radius**
  `357913940/2³⁰`. Not formalized; it is the `transport` hypothesis of the capstone.

None of (i)–(iv) is asserted; SYZ46 delivers **no** unconditional δ* movement and **no**
conditional-on-`uniformSylvester`-alone δ*. Its gain is wire (iv): the census-count ⇒ δ*-floor
bridge at the correct radius, the machine-checked retraction of the vacuous first draft, and the
one-statement assembly of the conditional bracket with every residual named.

## Reused substrate (all pre-landed)

- `ProximityGap.epsMCA_le_of_badCount_le`, `epsMCA_eq_iSup_mcaBadCount` (`MCABadCount.lean`,
  `MCALowerBound.lean`).
- `MCAThresholdLedger.mcaDeltaStar`, `le_mcaDeltaStar_of_good`.
- `PrizeShapeRateHalfBracket.latticeBoundary_le_mcaDeltaStar_of_predecessor_good`,
  `predecessorRadius`, `natCast_div_le_inv_of_mul_le`, `epsStar_coe_eq_natCast_inv`.
- `SYZ3OverBudgetStackWitness.firstPrime_predecessor_cap_refuted` (drives the retraction).
- `SYZ6FinerGradingCeiling.firstPrime_rateHalf_mcaDeltaStar_le_exact` (the unconditional ceiling).
- `SYZ42.StripMasterHypothesis''`, `SYZ43.realizabilityCore_of_mcaEvent_witnesses`,
  `SYZ40.merged_branch_unconditional`.

## Addendum — post-SYZ53 empirical status (2026-07-11, SYZ54 consolidation)

The conditional bracket above is now backed by decisive empirical evidence that the δ*=1/3 target
it brackets **survives** — while remaining, honestly, conditional on the four named wires.

- **The floor's non-BGK residual is fully calibrated.** SYZ44 removed the μ-basis degree-sum law
  from the empirical column (Hilbert-function corollary of Bézout surjectivity + graded μ-basis),
  collapsing the rate-1/2 `uniformSylvester` to the single imbalance bound `ι ≤ 1`. The concurrent
  swarm SYZ53 (`_SYZ53GeneratorGapCalibration.lean`) proved the exact identity `ι = ⌊(δ₂−δ₁)/2⌋`, so
  the sole remaining non-BGK obligation is the crisp Hilbert–Burch gap `δ₂−δ₁ ≤ 1` on the balanced
  interior (referee-confirmed field-independently on 1080 triples). This does not close wire (i); it
  makes it a standard commutative-algebra statement rather than an opaque resultant computation.

- **The BGK wall is where the interior obstruction genuinely lives.** SYZ49 reduced the
  balanced-interior obstruction exactly to the max level set of `R = W_BC/W_AC` on `μ_n`, and showed
  it **is** the BGK additive-character wall (`L(R(ω)) = Σ_{S_BC}L(ω−s) − Σ_{S_AC}L(ω−s)`). So wire (i)
  at the balanced interior = the CORE Paley/BGK object; the census bracket cannot be discharged
  BGK-free.

- **The apparent refutation candidate was a small-field artifact.** SYZ52 measured on `μ₁₄⊂𝔽₂₉` a
  max `mca`-bad count `19` on band-realizable `ι=2` interior witnesses — above the pencil ceiling
  `12`, the SYZ22 budget `13 = n−1`, and `n`. Taken at `𝔽₂₉` this reads as beating the very
  `#bad ≤ n−1` census bound `StripCensusBound` asserts at production. **SYZ53 `p`-scaling**
  (`probe_syz53_p_scaling.py`, exact per-subset RS-parity, rigorous at every prime) showed the excess
  peaks `+9` near `p≈113..197`, then collapses through `p* ∈ (197,1009)` to the generic pencil floor
  `3` and stays flat through `p=2³¹`, non-growing in `n`. At the production field `P ~ 2¹⁵⁸ ≫ p*`
  the `ι=2` excess contributes **zero**: the per-stack bad count sits at `O(1) ≪ 2³⁰−1`, consistent
  with `StripCensusBound`. **The `31/64`… correction stands and δ*=1/3 survives; no refutation.**

- **Discipline note (G84/SYZ53).** The SYZ52 episode is why small-p verdicts are untrustworthy in
  both directions. The census bound `StripCensusBound` must **never** be affirmed or refuted from a
  small field; the honest test is the `p`-sweep to `≫ p*`. SYZ53's exact-count tool and first-moment
  collapse law are the reusable method.

Net: `StripCensusBound` and the bracket remain **conditional** on wires (i)–(iv); no unconditional
δ* movement. But the empirical record after SYZ53 is that the bracketed δ*=1/3 conjecture **survives**
every stack test at honest field size, and the sole non-BGK obligation feeding the floor is now a
named Hilbert–Burch gap. **CORE remains OPEN / ON-BGK.**

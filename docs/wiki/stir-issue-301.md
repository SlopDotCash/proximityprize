# STIR Issue 301 Scratchpad

> **CLOSED 2026-06-10.** The named open soundness math (`stirCheckingCABridge`) was
> discharged OUTRIGHT at a genuinely sub-unit budget in
> `ArkLib/ProofSystem/Stir/SubUnitRbr.lean` (14 declarations, all axiom-clean), and the
> issue was closed. Keystone facts for future readers:
>
> - **The in-tree wire model needs no correlated agreement**: with the single-domain
>   identity fold and one challenge-derived point per binding check, the checking
>   verifier'''s rbr knowledge soundness is provable directly. The proximity gap is only
>   needed when folding genuinely reduces degree (paper-STIR; tracked by #304/#302).
> - **The budget** `stirEpsStar`: 0 at fold/shift challenges, `(|F|-(⌊δ|ι|⌋+1))/|F|` at
>   the round-2 input-link challenge, `(|F|-1)/|F|` at later pair-binding out-challenges.
>   Essentially tight (switch-prover); `2^{-secpar}` budgets at large secpar need the
>   t-repetition wire model (follow-up portfolio item A1).
> - **The reusable machinery**: `ThresholdKSF.rbrKnowledgeSoundness_of_flipBounds` — the
>   generic multi-flip KSF lemma with genuine conjunction flip events (the upgrade
>   `Whir/SubUnitRbr.lean`'''s honesty note asked for); the '''retired-prefix winnable'''
>   state-predicate pattern (the pending-pair lock clause defeats the one-point-copy
>   adversary); the salvage-game peeling recipe (mirror `probEvent_salvage_game_le`);
>   the `hFull`-from-acceptance idiom (`probEvent_pos_iff` + run-collapse +
>   `simulateQ_optionT_pure_run'''`).
> - **Front doors**: `stirCheckingRbrSoundness_genuine`, `stirCheckingCABridge_genuine`,
>   `stirCheckingIOP_isSecureWithGap_genuine` (hypothesis-free), and
>   `stir_main_of_checkingIOP_genuine`, alongside the regime-conditional families
>   (window/window_corner/small_field/card_le/e7/large/CA).
>
> Everything below is the historical scratchpad from the assembly campaign.


Status notes for GitHub issue #301: assembling the multi-round STIR Vector IOPP and
discharging `stir_main` / `stir_rbr_soundness`.

## Source Trail

- Issue: <https://github.com/lalalune/ArkLib/issues/301>.
  Rechecked on 2026-06-10: still open; the body still splits mechanical STIR assembly from
  the non-fabricated Johnson-regime correlated-agreement core.
- STIR paper page: <https://gfenzi.io/papers/stir/>. STIR is an IOPP for Reed-Solomon
  proximity testing; the round-by-round soundness proof relies on Reed-Solomon proximity-gap /
  correlated-agreement machinery.
- STIR ePrint: <https://eprint.iacr.org/2024/390>.
- BCIKS20 proximity gaps: <https://par.nsf.gov/servlets/purl/10467091>. Theorem 1.4 is the
  correlated-agreement theorem; the unique-decoding part is Theorem 4.1 and the list-decoding
  / Johnson-regime core is Theorem 5.1.
- Recent RS proximity-gap context: <https://www.math.toronto.edu/swastik/rs-proximity-gaps-2025.pdf>
  and <https://eprint.iacr.org/2025/2046>. These emphasize that beyond-Johnson / near-capacity
  proximity gaps remain an active research frontier, not a routine import.
- Related Lean, not a direct STIR solution:
  <https://github.com/iotexproject/rs-proximity-gaps> contains a Lean formalization for FRI
  proximity-gap results above Johnson, but it is not an ArkLib STIR Vector IOPP proof.

## Local State

- `ArkLib/ProofSystem/Stir/MainThm.lean` still defines the headline claims as `Prop`
  front doors: `stir_main` and `stir_rbr_soundness`.
- `ArkLib/ProofSystem/Stir/MultiRoundSpec.lean` realizes the `2 * M + 2` challenge count.
- `ArkLib/ProofSystem/Stir/Round3Block.lean`, `Round3Compose.lean`, and `FullChain.lean`
  assemble the literal STIR round shape.
- `ArkLib/ProofSystem/Stir/MultiRoundAssembly.lean` constructs `stirMultiRoundIOP`, proves
  perfect completeness for its shell verifier, and provides conditional front doors:
  `stir_rbr_soundness_of_secure_vectorIOP`, `stir_rbr_soundness_of_residuals`,
  `stir_main_of_secure_vectorIOP`, and `stir_main_of_residuals`.
- The shell verifier accepts unconditionally. Its completeness proof is useful, but an
  unconditional small-error soundness theorem for that exact verifier should not be claimed.
- `ArkLib/ProofSystem/Stir/CheckingVerifier.lean` builds a real checking verifier over the
  landed multi-round wire shape, proves `stirCheckingIOP_perfectCompleteness`, packages the
  checking IOP as `stirCheckingIOP`, and exposes checking-specific front doors:
  `stir_rbr_soundness_of_checkingIOP_CA` and `stir_main_of_checkingIOP_CA`.
- Acceptance of `checkingBool` is now decomposed into reusable checked facts:
  `checkingBool_true_implies_fold_check`,
  `checkingBool_true_implies_round_consistency` (with out/shift projections), and
  `checkingBool_true_implies_final_in_code`. The bidirectional theorem
  `checkingBool_eq_true_iff` now gives the exact local spec of the checker: fold agreement,
  all sampled out/shift adjacent-round agreements, and final Reed-Solomon membership. These
  are the local verifier facts the protocol-level bridge must feed into the probabilistic
  CA/proximity-gap argument.
- The same facts are now exposed at verifier-support level:
  `checkingVerifier_support_iff`,
  `checkingVerifier_acceptance_iff_checkingBool`,
  `checkingVerifier_acceptance_implies_checkingBool`,
  `checkingVerifier_acceptance_implies_fold_check`,
  `checkingVerifier_acceptance_implies_round_consistency` (with out/shift projections), and
  `checkingVerifier_acceptance_implies_final_in_code`. These turn an accepting value in
  `support ((stirCheckingVerifier M φ deg).toVerifier.verify stmtIn tr)` into the transcript
  consistency facts required by an eventual RBR bridge.
- The checking front doors consume the named residual
  `stirCheckingRbrSoundnessResidual`, which is exactly the remaining RBR knowledge-soundness
  theorem for the checking verifier, and the bridge residual `stirCheckingCABridge`, which
  isolates the STIR/BCIKS correlated-agreement plus per-round accounting proof.
- `CheckingVerifier.lean` has a CA-small-field route:
  `strictCoeffPolysResidual_all_of_card_le` discharges the whole positive-width
  `StrictCoeffPolysResidual` family from `|F| <= |ι|` and
  `δ < 1 - sqrtRate`, using the in-tree vacuous-regime BCIKS theorem. The front doors
  `stir_rbr_soundness_of_checkingIOP_card_le` and `stir_main_of_checkingIOP_card_le`
  consume that route, so in this regime the remaining soundness hypothesis is only the
  protocol-level checking bridge `stirCheckingCABridge`.
- `CheckingVerifier.lean` also has the stronger small-field unconditional route:
  `one_le_proximityError_of_card_le` proves the STIR proximity error is at least `1` under
  `|F| <= (m - 1) * |ι|` and `δ <= (1 - ρ) / 2`; hence
  `stirCheckingRbrSoundness_of_small_field`,
  `stirCheckingCABridge_of_small_field`,
  `stirCheckingIOP_isSecureWithGap_small_field`,
  `stir_rbr_soundness_of_checkingIOP_small_field`, and
  `stir_main_of_checkingIOP_small_field` consume no Johnson-CA residual, no bridge residual, and
  no per-round-gap keystone. This is vacuous-budget security: for positive `secpar`, the `hε`
  upper bound conflicts with an `ε_rbr` lower bound at least `1`.
- The sharp vacuous route is also wired:
  `strictCoeffPolysResidual_all_of_card_le_e7`,
  `stir_rbr_soundness_of_checkingIOP_card_le_e7`, and
  `stir_main_of_checkingIOP_card_le_e7` discharge the BCIKS residual family under
  `|F| <= deg^2 * 10^7`.
- The #304 large-sector route is wired:
  `strictCoeffPolysResidual_all_of_large`,
  `stirCheckingRbrSoundness_of_large`,
  `stirCheckingIOP_isSecureWithGap_of_large`,
  `stir_rbr_soundness_of_checkingIOP_large`, and
  `stir_main_of_checkingIOP_large` consume the honest large-good-set
  `StrictCoeffPolysLargeResidual` family plus the same checking bridge.
- `ArkLib.ProofSystem.Stir.ErrorAccumulation.PerRoundProximityGap.refl` is the reflexive
  budget identification (`∀ i, e i = B i` with `e := B`) used when front doors choose
  accounting errors equal to the proximity-gap bounds. Despite the historical name,
  `PerRoundProximityGap` is an equation between chosen numbers, not the BCIKS20 proximity-gap
  theorem; discharging it does not discharge any soundness obligation (audit L77). The
  per-round soundness content is carried separately (`StrictCoeffPolysResidual` families and
  the `SubUnitRbr` route above).
- `stir_main` now states input-query complexity as
  `(qNumtoInput : ℝ) >= secpar / (- Real.log (1 - δ))`; the multi-round and checking front
  doors are aligned with this inequality form rather than the older exact equality.

## Honest Blockers

- The round-by-round knowledge-soundness proof must connect the checking verifier's sampled
  consistency checks to the STIR/BCIKS proximity-gap keystones.
- The Johnson / sqrt-rho correlated-agreement leg remains a genuine mathematical residual in
  ArkLib's BCIKS pipeline outside the vacuous/small-field and `deg^2 * 10^7` routes. Do not
  replace it with an ad hoc or assumed proof.
- The complexity and per-round error inequalities in the headline statements are free-parameter
  constraints; the current front doors consume them as hypotheses.

## Validation Notes

Targeted checks used while avoiding a full rebuild:

- `lake env lean ArkLib/ProofSystem/Stir/MainThm.lean`
  - Last run after checker-local changes: passed, with only pre-existing unused-variable
    warnings and standard axiom prints for `stir_main` / `stir_rbr_soundness`.
- `lake build ArkLib.ProofSystem.Stir.RbrFrontDoor`
- `lake build ArkLib.ProofSystem.Stir.MultiRoundAssembly`
- `lake env lean ArkLib/ProofSystem/Stir/ErrorAccumulation.lean`
  - Passed after adding `PerRoundProximityGap.refl`.
- `lake build ArkLib.ProofSystem.Stir.ErrorAccumulation`
  - Passed, making the new accounting lemma visible to downstream imports.
- `lake env lean --stdin` importing `ErrorAccumulation` and printing axioms for
  `PerRoundProximityGap.refl`
  - Passed; only `[propext, Classical.choice, Quot.sound]`.
- `lake env lean ArkLib/ProofSystem/Stir/MultiRoundAssembly.lean`
  - Passed after aligning `hQin` with the inequality form.
- `lake env lean ArkLib/ProofSystem/Stir/CheckingVerifier.lean`
  - Last run after adding verifier-support acceptance lemmas: passed, and all newly printed
    axioms are only `[propext, Classical.choice, Quot.sound]`.
  - Re-run after adding the exact support/acceptance equivalence: passed with the same axiom
    footprint.
  - Re-run after adding `checkingBool_eq_true_iff`: passed with the same axiom footprint.
  - Re-run after `PerRoundProximityGap.refl`, inequality `hQin` alignment, and the large-sector
    route: passed; all printed checking front doors use only standard axioms.
  - Re-run after adding `stir_rbr_soundness_of_checkingIOP_small_field`: passed; the new axiom
    print reports only `[propext, Classical.choice, Quot.sound]`.
- `lake build ArkLib.ProofSystem.Stir.CheckingVerifier`
  - Passed after adding `stir_rbr_soundness_of_checkingIOP_small_field`.
  - Re-run after normalizing `(-Real.log ...)` spacing: passed. Build replayed cached
    dependencies and reported only unrelated pre-existing warnings; the `- Real.log` whitespace
    warnings are gone.
- `lake env lean ArkLib/ProofSystem/Stir/MainThm.lean`
  - Re-run after the new checking front door: passed, with the same pre-existing unused-variable
    warnings and standard axiom prints for `stir_main` / `stir_rbr_soundness`.
  - Re-run after normalizing `(-Real.log ...)` spacing in the canonical `stir_main` statement:
    passed with the same unused-variable warnings.
- `rg -n -g '*.lean' -- "- Real\\.log" ArkLib/ProofSystem/Stir`
  - Clean after normalizing the `hQin` spacing in `MainThm.lean` and `CheckingVerifier.lean`.
- `rg -n "\\bsorry\\b|\\badmit\\b|^\\s*axiom\\b|^\\s*opaque\\b" ArkLib/ProofSystem/Stir ArkLib/Data/CodingTheory/ProximityGap/BCIKS20 -g '*.lean'`
  - Latest scan found no actual `sorry` / `admit` proof steps in these targets; hits were
    documentation comments, axiom-audit text, or ordinary words such as "admits".

## Cleanup Notes

- Removed a stray post-namespace block of attempted `sorry` theorems
  (`stirCheckingCABridge_holds`, `stir_main_thm`, `stir_rbr_soundness_thm`) from
  `CheckingVerifier.lean`. It was outside the namespace, did not elaborate, and would have
  fabricated precisely the CA/RBR bridge that issue #301 says not to fabricate.
- `lake build ArkLib.ProofSystem.Stir.FullChain ArkLib.ProofSystem.Stir.ProximityGapProof ArkLib.ProofSystem.Stir.ProximityGapSmallField`
- Earlier context also checked `Round3Block`, `Round3Compose`, `FullChain`,
  `ProximityGapProof`, and `ProximityGapSmallField`.

## Gotchas

- The tail `stir_rbr_soundness` inequalities are indexed by `j : Fin M`, where `j.succ`
  corresponds to paper round `i = j + 1`. Do not guard these obligations with `j.val != 0`;
  that would accidentally skip the first shifted round.
- Statement repairs of 2026-10-28 (audit L36), mirrored in every front door:
  `ParamConditions` requires `degree < |ι|` (rate `< 1`; the old reversed condition forced rate
  `1` and left `stir_rbr_soundness` without admissible parameters); the shift term applies
  `proximityError` at `repeatParam j.castSucc + s`; the final-round bound is a separate
  conjunct (`hfin`) outside the tail quantifier; and `stir_main`'s `hF` is the lower-bound
  `FieldSizeCondition` with a real exponent `7/2`. `stir_main` still quantifies over an
  arbitrary protocol, and its complexity conjuncts constrain free parameters with
  per-instance constants (`ComplexityLegs.lean`).

## 2026-06-10 protocol-object campaign (session summary)

Landed inventory (all axiom-clean, on `main`):

- Completeness track COMPLETE for the function-payload chain: per-block
  (`BlockCompleteness.lean`, `Round3Completeness.lean` — includes the generic `[P,V,V]`
  3-message unroll + `FullTranscript.mk3`), phase (`BlocksCompleteness.lean`, n-ary engine),
  tail seam (`TailCompleteness.lean`), full chain (`ChainCompleteness.lean`:
  `stirFullReduction_perfectCompleteness`).
- Vector wire format: block kit (`VectorBridge.lean`), chain-composable mid variants
  (`VectorBridgeMid.lean`), assembled chain + `2(M+1)+2` budget (`VectorChain.lean`),
  and the packaging bridge (`VSpecBridge.lean`: `VectorSpec.vsAppend`/`vsSeqCompose` +
  `toProtocolSpec` commutation + `stirChainVSpec_toProtocolSpec` +
  `stirChainVSpec_toProtocolSpec_card_challengeIdx`).  The literal `VectorSpec` budget
  theorems live in `ChainVSpecCount.lean`
  (`stirChainVSpec_card_challengeIdx`, `stirChainVSpec_card_messageIdx`).
- Soundness track: init-block RBR at error 0 (`InitRbrSoundness.lean`), chain RBR composition
  through the first seam for a generic tail (`InitAppendRbr.lean`), block RBR budgets + THE
  FOLD SEAM consuming the residual-free Lemma 4.13 (`BlockRbrBudgets.lean`:
  `stirFold_seam_all_close`), and `combine_theorem` unconditional/errStar forms
  (`Combine.lean`). Front door: `RbrFrontDoor.lean` reduces Lemma 5.4 to
  (π over `stirVSpec`, `IsSecureWithGap`, budget bounds).

### Composition-at-concrete-specs recipe (hard-won; follow it)

1. Oracle-level append/seqCompose security keystones DIVERGE in whnf at concrete compound
   specs. Step down: `unfold OracleReduction.perfectCompleteness` (equation lemmas, never
   `show`/`change` defeq), rewrite with `appendToReductionResidual_proof`, apply the
   `Reduction`-level keystone via `have`-then-`exact`.
2. Compound-head instances are MISSED by search: register by name; for data-carrying classes
   (`SampleableType`!) use thin `@[reducible]` aliases `fun i => globalInst i` so both sides
   elaborate to the same canonical term — a Prop mentioning a data-carrying instance depends
   on the instance term (see `InitAppendRbr.lean`'s explicit-`@` conclusion).
3. Seam-direction lemmas: `(p₁ ++ₚ p₂).dir = Fin.vappend …` as an `rfl`-`have` then `rw`;
   boundary index via `Fin.natAdd m ⟨0,_⟩` + `Fin.append_right`; inside `seqCompose` via
   `Fin.castAdd` + `Fin.embedSum` in MK-FORM (literals do not iota-match) +
   `seqCompose_dir` + `Fin.vflatten_embedSum`.
4. Combined-oracle seam instances: `haveI`s from `ChallengeOracleFintype` helpers
   (`appendCombinedOracle_fintype`, `seqComposeCombinedOracle_fintype`, …).

### Known open packaging detail

`OracleReduction.cast` of the vector chain onto `(stirChainVSpec).toProtocolSpec F` needs the
pointwise interface-equality side condition `hOₘ` between the append-derived message
interfaces (`instOracleInterfaceMessageAppend` route) and the `toProtocolSpec` ones
(`instOracleInterfaceMessageToProtocolSpec`); both reduce to `instVector` per slot but not
definitionally — needs the index-case lemma (castAdd/natAdd split). Latest probe:
`OracleReduction.cast` works after importing `ArkLib.OracleReduction.Cast`, and the only
remaining goal is exactly
`instStirVecFullMsgInterface M i = dcast ... (VectorSpec.instOracleInterfaceMessageToProtocolSpec
...)`; `simp` does not close it after unfolding because the append side becomes nested
`Fin.fappend₂` / `Fin.fconcat₂` cases.
One generic route was probed for `VectorSpec.toProtocolSpec_vsAppend`: splitting by
`MessageIdx.sumEquiv.symm` leaves left/right goals where `Fin.fappend₂_left/right` reduce the
append side to a casted `fun h => OracleInterface.instVector`; the remaining obstacle is
normalizing that casted proof argument and the transported vector length on the RHS.  The existing
`OracleVerifier.Append.instAppend_inl_heq` / `instAppend_inr_heq` lemmas are the closest local
template (`dcongr_heq` over the direction proof).

### 2026-06-10 packaging validation

- `lake env lean ArkLib/ProofSystem/Stir/VSpecBridge.lean`
  - Passed after renaming the protocol-spec count theorem to
    `stirChainVSpec_toProtocolSpec_card_challengeIdx`; axiom audit reports only
    `[propext, Classical.choice, Quot.sound]`.
  - Existing warning remains on `stirChainVSpec_toProtocolSpec` for unused section variables.
- `lake build ArkLib.ProofSystem.Stir.VSpecBridge`
  - Passed after the rename; build replayed cached dependencies and reported existing
    style/unused-instance warnings in the vector packaging stack.
- `lake env lean ArkLib/ProofSystem/Stir/ChainVSpecCount.lean`
  - Passed after refreshing the `VSpecBridge` `.olean`; the earlier duplicate-name failure was
    caused by the protocol-spec count theorem colliding with the existing literal-`VectorSpec`
    theorem `stirChainVSpec_card_challengeIdx`.

# Verified-zkEVM Grants — ArkLib Progress Report (2026-06-07)

Status snapshot of the six [verified-zkevm.org](https://verified-zkevm.org/#grants) grants that
target ArkLib, measured against the actual repository state on `main`.

**Repo-wide invariants at time of writing** (from `scripts/sorry_census.py` and
`scripts/forbidden_tokens.py`):

- `sorry`/`admit` holes: **0** (370 `sorry` tokens are all doc-comment mentions).
- `native_decide`/`bv_decide`/undocumented axioms: **none**.
- Documented residual axioms: **10**, all isolated in two leaf files
  (`ProximityGap/CapacityBoundsProofs.lean` ×9, `ToyProblem/Leaderboard.lean` ×1). Each is a
  genuine external-paper antecedent, not a concealed gap. See
  [open-problems-list-decoding-and-correlated-agreement.md](open-problems-list-decoding-and-correlated-agreement.md).

> **Reading guide.** "Proved" = closed Lean theorem, kernel-checked. "Proved-modulo-residual" =
> closed proof that consumes an explicit hypothesis (a `…Residual` `Prop` or one of the 10 allow-listed
> axioms). "Stated" = a named declaration / `Prop` with the obligation owed. "Genuine open math" =
> a paper antecedent (list-decoding / correlated-agreement core) that **cannot be discharged without
> a new mathematical result** — these are deliberately *not* fabricated.

---

## Grant 1 — STIR & WHIR constructions in ArkLib (executable specifications)
*Awarded: Nethermind · Q4 2025*

### STIR (`ArkLib/ProofSystem/Stir/`, `website/blueprint/src/proof_systems/stir.tex`)

| Component | Lean | Status |
|---|---|---|
| Proximity bound / error fns | `STIR.Bstar`, `STIR.proximityError` | **Proved** |
| Quotienting (Lemma 4.4) | `Quotienting.quotienting` | **Proved** |
| Out-of-domain sampling (4.5.1–2) | `OutOfDomSmpl.out_of_dom_smpl_1/2` | **Proved** |
| Combine (Def 4.11 + theorem) | `Combine.combine`, `Combine.combine_theorem` | **Proved-modulo-residual** (`StrictCoeffPolysResidual`) |
| Single-round oracle reduction | `StirIOP.Round.stirRoundReduction` | **Proved** (executable, sorry-free) |
| Single-round completeness | `StirIOP.Round.stirRoundReduction_completeness` | **Stated** (mechanical: heterogeneous `processRound` round-peeling) |
| Proximity gap (monomial) | `STIR.proximity_gap` | **Stated** — reduces to BCIKS20 list-decoding-regime correlated agreement (genuine open math) |
| Main IOPP (Thm 5.1) | `StirIOP.stir_main` | **Stated** (needs full (M+1)-round `VectorIOP` object + the two inputs above) |
| RBR soundness (Lemma 5.4) | `StirIOP.stir_rbr_soundness` | **Stated** (same blockers) |

**Executable-spec deliverable:** the single fold-and-combine round is a real, runnable
`stirRoundReduction`; the full multi-round IOPP object is not yet assembled. Blueprint `stir.tex`
is structurally complete and cross-linked to the Lean names above.

### WHIR (`ArkLib/ProofSystem/Whir/`, `whir.tex`) — also open issue #113

| Component | Lean | Status |
|---|---|---|
| Folding (Def 4.14–4.15, degree bounds) | `fold_k`, `foldf_step_mem_smoothCode`, `fold_f_g`, `fold_f_g_poly` | **Proved** (axiom-clean) |
| Folding preserves list-decoding (L4.21–4.23) | `folding_preserves_listdecoding_base(_of_mca_bridge)`, `…_bound`, `…_ne_subset` | **Proved** (hypotheses explicit; repaired 2026-06-04) |
| OOD sampling (L4.24–4.25) | `crs_equiv_rs_random_point_agreement`, `oodSampling_crs_eq_rs` | **Proved** |
| Proximity generator / MCA (Def 4.7–4.10) | `ProximityGenerator`, `hasMutualCorrAgreement`, `mca_linearCode(_udrFree)` | **Proved-modulo-residual** (proximity-gap hyp) |
| Johnson MCA scaffolding (10 `MCAJohnson*` files) | — | **Proved** (axiom-clean envelope; awaits external bridge) |
| MCA for RS, UDR (Cor 4.11) | `mca_rsc` | **Stated** (`Prop`) — needs ABF26 §4 proximity-gap→CA→MCA chain |
| Johnson MCA bound (Conj 4.12) | `mca_johnson_bound_CONJECTURE` | **Open conjecture** — RS Johnson list-decoding (genuine open math) |
| Capacity MCA bound (Conj 4.12) | `mca_capacity_bound_CONJECTURE` | **Refuted** (BSS'25 et al.) — kept as historical record only |
| Vector IOPP + RBR soundness (Thm 5.2) | `whir_rbr_soundness` | **Stated** — needs the IOPP object + `mca_rsc` |

**Honest gap:** WHIR's algebraic spine (folding, list-decoding lemmas, OOD, Johnson envelope) is
proved and independently useful. The remaining content bottoms out in the Reed–Solomon Johnson
list-decoding bound + the proximity-gap→MCA bridge — genuine open math, then a mechanical IOPP
assembly on top.

---

## Grant 2 — Blueprint STIR and WHIR security theorems
*Awarded: Least Authority · Q1 2025*

- `website/blueprint/src/proof_systems/stir.tex`: **complete & cross-linked** (proximity gap, quotient,
  OOD, folding facts, combine, degree correction, main thm, RBR soundness).
- `website/blueprint/src/proof_systems/whir.tex`: **complete & cross-linked** (MCA defs/lemmas, folding,
  block distance, list-decoding lemmas, OOD, Thm 5.2). The two `*_CONJECTURE` items are correctly
  flagged as open/refuted rather than hidden behind a `sorry`.
- Blueprint accurately tracks proof status; no fabricated `\leanok` on open statements.

---

## Grant 3 — Fiat-Shamir specification (duplex-sponge based)
*Awarded: Article 12, LLC (Michele Orrù) · Q4 2025* — also open issues #116, #112

**Closeout update (2026-06-10, issue #314): CORE SPEC DELIVERABLE DONE.** A full duplex-sponge
construction exists and the FS transform is built on it (not a generic RO model):

- Sponge primitive: `ArkLib/Data/Hash/DuplexSponge.lean` (`SpongeUnit`, `DuplexSpongeInterface`,
  `SpongeSize`, `CanonicalDuplexSponge`).
- Transform: `Reduction.duplexSpongeFiatShamir` + salted variants (CO25 Construction 4.3) in
  `OracleReduction/FiatShamir/DuplexSponge/Defs.lean`, over `duplexSpongeChallengeOracle` (CO25 Eq 16).
- Codec/salt layer: `ProtocolSpec.Codec`, `SaltCodec`, `uniformSalt`, and the salted/random
  DSFS wrappers.
- Security infra: `KeyLemma.lean` (CO25 Lemma 5.1), `KeyLemmaFoundations.lean`,
  `Soundness.lean`, prover/trace transforms, abort/bad-event analysis.

| Security transfer | Lean | Status |
|---|---|---|
| Completeness-unroll (#116) | `duplexSpongeFiatShamir_completeness_unroll_discharged`, `duplexSpongeFiatShamirSalted_completeness_unroll_discharged` | **Proved** |
| DSFS soundness via key lemma | `DuplexSponge/Security/Soundness.lean` | **Proved-modulo-residual** (`DuplexSpongeFS.KeyLemmaResidual`) |
| SR-soundness => soundness (#116, basic FS) | `fiatShamir_soundness_of_stateRestoration`, canonical close theorem in `StateRestorationTransport.lean` | **Proved** for the canonical implementation |
| SR-knowledge soundness => knowledge soundness (#116, basic FS) | `fiatShamir_knowledgeSoundness_of_stateRestoration`, canonical close theorem in `StateRestorationTransport.lean` | **Proved** for the canonical implementation |
| HVZK => ZK (#116/#112, basic FS) | `fiatShamir_isHVZK_canonical`, `fiatShamir_isStatHVZK_canonical` | **Proved** for the canonical implementation |
| HVZK/ZK definitions (#112) | `perfectHVZK`, `statisticalHVZK`, `isHVZK`, `isStatHVZK` | **Proved/defined** |

**Closeout classification:** the grant's executable/specification target is met. The remaining
strict DSFS residuals are post-grant security hardening for the full CO25 Lemma 5.1 hybrid proof:
`DuplexSpongeFS.KeyLemmaResidual`,
`Lemma5_12HonestResidual`, `Lemma5_14HonestResidual`, `Lemma5_16HonestFalseAsStated`,
`SimulatedProverChallengeBudgetResidual`, `SimulatedProverSharedBudgetResidual`,
`KeyLemmaEagerResidual`, `D2sQueryStepGSpecBudgetResidual`, and
`D2fOuterImplSharedBudgetResidual`. See
[`issue-314-fiat-shamir-closeout-2026-06-10.md`](issue-314-fiat-shamir-closeout-2026-06-10.md).
**Blueprint gap closed:** `website/blueprint/src/oracle_reductions/fiat_shamir.tex` now covers the
canonical and duplex-sponge constructions, codec/salted variants, and proof/residual status.

---

## Grant 4 — Binius in ArkLib
*Awarded: Chung Thai Nguyen* — also open issues #33, #29, #19

| Component | Lean | Status |
|---|---|---|
| BinaryBasefold Steps (fold/commit/relay/finalSumcheck) | `*OracleReduction_perfectCompleteness`, `*_rbrKnowledgeSoundness` | **Proofs written, sorry-free** — blocked from green build by upstream `ReductionLogic`/`Soundness/` drift (#33) |
| RingSwitching generic reduction | `fullOracleReduction_perfectCompleteness`, `fullOracleVerifier_rbrKnowledgeSoundness` | **Stated** (instance-independent); leaf phase proofs in progress (#19) |
| `binaryTowerProfile` instance + reconstruction laws | `Prelude.lean` | **Proved** |
| KState coordination across phases (#29) | batching↔sumcheck `…KStateProp` | **Design-blocked** (5 coordination points — spec contract, not a math hole) |

**Issue #33's 9 named residuals** are written tactic proofs; the blocker is upstream API drift
(`ReductionLogic` sumcheck lemmas + the 7-module `Soundness/` subtree), *not* the residuals
themselves. **Closeable (mechanical):** repair `ReductionLogic` (≈6 sumcheck lemmas) and the
`Soundness/` build cascade. **Design-blocked:** the #29 KState weakening contract needs a design
decision before it can be formalized. Blueprint `ring_switching.tex` covers Defs 19–21 + Thms 1–2.

---

## Grant 5 — Blueprint for FRI & Coding Theory prerequisites
*Awarded: Nethermind · Q1 2025* — also open issue #14

### FRI (`ArkLib/ProofSystem/Fri/`, `BatchedFri/`)

| Component | Lean | Status |
|---|---|---|
| Round protocol specs (fold/final/query) | `Fri.Spec.SingleRound.*`, `Fri.Spec.General.reduction` | **Proved** (constructor-complete) |
| Perfect completeness | `reduction_perfectCompleteness` (via residual bricks + composition keystones) | **Proved-modulo-residual** (per-round honest-protocol bricks) |
| Soundness error accounting | `roundError`, `queryError`, `totalError` + projection lemmas | **Defined + projections proved**; full soundness theorem **open** |
| Batched FRI query soundness (#14) | `BatchedFri/Security.lean` (coset machinery) | **Stated** — lifts to base-FRI soundness; coset-bijection injectivity owed |

### Coding theory (`ArkLib/Data/CodingTheory/`)

Mature and broad: Reed–Solomon (+ FFT/folded/interleaved/multilinear variants), relative distance
& MDS, Berlekamp–Welch decoding, Johnson-bound machinery, Guruswami–Sudan list decoding,
proximity gaps (BCIKS20, Polishchuk–Spielman, DG25, CS25). All `sorry`-free; the only residual
axioms are the 9 capacity/correlated-agreement antecedents.

### Blueprint coverage

- `website/blueprint/src/coding_theory/defs.tex`: **definitions covered** (code distance, RS code,
  proximity gap, list-decodability, smooth/constrained codes).
- **FRI blueprint section: MISSING** (`proof_systems/fri.tex` did not exist) — **addressed in this
  pass**, see [`fri.tex`](../../../website/blueprint/src/proof_systems/fri.tex) (added grounded in the Lean
  names above). Batched-FRI section still TODO.

---

## Grant 6 — ArkLib (library + VCVio)
*Awarded: Quang Dao, Devon Tuma, zkSecurity · Q4 2024*

**Foundation: mature.**

- Core IOR framework (`OracleReduction/`): `ProtocolSpec`, `Prover`/`OracleProver`,
  `Verifier`/`OracleVerifier`, `OracleInterface`, `Execution`, `Reduction`/`OracleReduction` — all
  defined and usable.
- Security definitions: completeness, soundness, knowledge soundness, **round-by-round** (knowledge)
  soundness, zero-knowledge, state-restoration. Implications (`Security/Implications.lean`) proved:
  RBR-KS ⇒ RBR-S ⇒ S, KS ⇒ S, RBR-KS ⇒ KS.
- Composition (`Composition/Sequential/`): append + n-ary `seqCompose` with **all** security
  properties preserved (proved). Parallel composition: structure only.
- Context lifting (`LiftContext/`): lenses + preservation theorems — mature.
- VCVio integration (`ToVCVio/`): `OracleComp`/`OracleSpec`/`QueryImpl`/`simulateQ`/`EvalDist`
  bridge wired up; probabilistic execution semantics usable.
- Commitments (`CommitmentScheme/`): Merkle (batch/extraction/hiding), KZG (correctness/binding),
  Ajtai — sorry-free.
- Breadth: 9+ protocol families with specs (Sum-Check, FRI, Binius, STIR, WHIR, Spartan, Logup,
  Batched FRI, constraint systems).

**Framework-level remaining gaps:** BCS compiler security preservation (#62), DSFS completeness/ZK,
state-restoration tier, AGM. None block library usability.

---

## Consolidated picture: what is genuinely closeable vs. genuine open math

**Genuine open math (paper antecedents — must NOT be fabricated; tracked as the 10 residual axioms
+ the named conjectures):**
1. BCIKS20 list-decoding-regime correlated agreement for affine lines/curves (feeds STIR
   `proximity_gap`/`StrictCoeffPolysResidual` and WHIR `mca_rsc`).
2. Reed–Solomon Johnson list-decoding bound (WHIR `mca_johnson_bound_CONJECTURE`).
3. The 9 capacity/CA/MCA bound axioms in `CapacityBoundsProofs.lean` (GKL24/BGKS20/BCHKS25/CS25/GG25).

**Mechanically closeable (no new math; protocol assembly / Lean infra / blueprint):**
- STIR/WHIR multi-round `VectorIOP` object construction + the existential security theorems on top.
- STIR `stirRoundReduction_completeness` (heterogeneous round-peeling).
- DSFS CO25 Lemma 5.1 post-grant security hardening: dispatcher budgets, honest bad-event
  implications, simulated-prover budgets, and the eager key lemma.
- Binius `ReductionLogic` sumcheck lemmas + `Soundness/` build-cascade repair (#33, #19).
- Batched-FRI coset-bijection injectivity + FRI soundness composition (#14).
- Blueprint: FRI section (added here), Batched-FRI section, DSFS section of `fiat_shamir.tex`.

**Design-blocked (needs a decision, not a proof):** Binius RingSwitching KState weakening contract (#29).

### Honest scope note

Each grant is a multi-person-month effort, and the deepest obligations are open research results
that the project deliberately carries as documented residual axioms / named conjectures rather than
laundering through `sorry`. This report tracks status truthfully; the concrete code/blueprint
down-payment made alongside it is the FRI blueprint section (Grant 5) plus this audit. Closing the
remaining *mechanical* items is the right next tranche; the *genuine open math* items are gated on
external results and should not be "completed" by fabrication.
</content>
</invoke>

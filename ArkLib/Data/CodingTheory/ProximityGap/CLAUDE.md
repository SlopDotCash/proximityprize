# The δ* Programme — Agent Guide (issue lineage #232 → #334 → #357 → #444 → #464 → #466)

> # ⚠️ 2026-07-09: CAMPAIGN HOME IS MOVING → branch `research/proximity-prize`
> A structural refactor is in progress (issue **#499**, see root `REFACTOR_NOTICE.md`).
> **Push all δ*/#466 campaign work (rungs, Frontier files, DISPROOF_LOG entries, kb notes) to the
> branch `research/proximity-prize`, NOT `main`.** `main` keeps only the upstream-canonical
> ProximityGap surface; everything else in this directory lives on the research branch
> (snapshot tag `archive/pre-refactor-2026-07-09`). Nothing is deleted from history.


> ## 🎯 CURRENT CAMPAIGN: issue #466 · dossier v3 (2026-07-01)
> The live issue is **#466** ("Prove δ* — complete research dossier (v3)"). Its body = the
> canonical dossier **`docs/kb/deltastar-DOSSIER-v3-2026-07-01.md`** — read it FIRST: the exact
> target (incl. the `δ* = (1−ρ) − m*/n` master-gap form), the four faces of the open core, the
> complete no-go landscape, the **ranked live frontier (§6)**, the substrate API map, and the
> honesty audit (the v2 "phantom bricks" recovered + landed 2026-07-01). Predecessors
> #232/#334/#357/#444/#464 are all CLOSED, each distilled into its successor.

> ## ⚡ START HERE TO SOLVE THE PRIZE: `PROXIMITY_PRIZE_WORKBENCH.lean`
> The single self-contained "write your solution here" file:
> [`PROXIMITY_PRIZE_WORKBENCH.lean`](PROXIMITY_PRIZE_WORKBENCH.lean). It has, in one place:
> the **exact non-degenerate target** (`mcaConjecture` / `mcaDeltaStar`, NOT the radius-one-
> degenerate `grandMCAChallenge`), the **prize regime** (`ρ∈{1/2,1/4,1/8,1/16}`, `ε*=2^-128`,
> `q≈n·2^128`, smooth `μ_n`, window interior `(1−√ρ, 1−ρ−Θ(1/log n))`), the **proven substrate**
> (the law, capacity-for-constant-DIM, granularity ladder, boundary law, ownership bracket,
> energy chain, paper bridges) **all imported and `#check`-verified accessible**, the **proven
> walls** (per-witness counting exhausted, energy √-loss, confluent-Stepanov, Weil/√q), the
> **closure contract** (§4 — what a winning conjecture must do), and a `▼ YOUR CONJECTURE HERE ▼`
> slot. Open it, write the closed-form `δ*(ρ,ε*,n)` + proof, validate with
> `scripts/pg-iterate.sh`, wire to `mcaConjecture`/`GrandMCAResolution`/the LD bridge. The
> conjecture must be **CLOSED** — no residual, no incomputable lemma — and must beat wall W1.

> This file is auto-loaded when you work under `ArkLib/Data/CodingTheory/ProximityGap/`.
> It is the **single source of truth** for attacking the mutual-correlated-agreement
> threshold (δ*) formalization. `AGENTS.md` in this directory is a verbatim copy.
>
> **Knowledge base (read in this order):**
> - `docs/kb/deltastar-DOSSIER-v3-2026-07-01.md` — **the canonical dossier (v3)**: everything
>   proven / refuted / open, the ranked live frontier, and the substrate API map.
> - `ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md` (73 tagged entries as of
>   2026-07-02, `466-r*` rounds still landing) + `docs/kb/deltastar-*.md` (333 dated notes across
>   the campaigns, 121 of them #464-era) — every refuted approach with its
>   constraint lemma. Check BOTH before re-trying anything.
> - Historical layers (each superseded by the next, kept for depth):
>   `docs/kb/deltastar-DOSSIER-v2-2026-06-22.md` (#464) ·
>   `ArkLib/…/docs/kb/deltastar-444-complete-map-25x25-2026-06-17.md` (#444 25×25 map) ·
>   `docs/kb/deltastar-357-compiled-knowledge.md` · `docs/kb/deltastar-research-map.md`.

## 0. The 30-second orientation

You are formalizing residuals around the **Ethereum Proximity Prize** ([ABF26], ePrint
2026/680, proximityprize.org). The $1M open core — pin the *mutual correlated agreement*
list-decoding threshold `δ*` for explicit smooth-domain Reed–Solomon codes in the window
`(1−√ρ, 1−ρ−Θ(1/log n))` at `ε* = 2^-128` — is **genuine open research, blocked on the
literature** (no known technique bridges Johnson→capacity for explicit fixed RS codes).
Propose bold closed-form `δ*` conjectures and attack the core freely — just **don't *claim* a
closure is *proven* when its input is unresolved** (see the §6 contract: bold in exploration,
strict only in proof-claims). Predecessors #232, #334, #357, #444, #464 are CLOSED (each distilled
into the successor); the live issue is #466 and the current state is dossier v3 §0/§6 (the
§3.5 below is the older #357-era layer, still accurate on the substrate it lists).

## 1. ⚡ BUILD — read this FIRST or you will clog the machine

This cone is **~3,500 files** (3,489 `.lean` files as of 2026-07-02, 1,643 of them in
`Frontier/`; it was 808 in the #334 era and keeps growing). `lake build <module>` traces a
3000+-job graph (**~2-3 min even with no changes**) AND takes the `.lake` build lock, which
**serializes every agent** on this 16-core box. Never iterate with `lake build`.

**Iterate with the single-file fast path** — elaborates ONE file against existing oleans,
~30s, **no lock**, fully parallel across agents:

```bash
scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/<YourFile>.lean
# (= lake env lean <file>, + error filter + axiom audit; -q for errors-only)
```

Rules that keep iteration fast and parallel-safe:
- **Minimal imports.** Your frontier file imports ONLY the substrate modules you actually
  consume (§4), never `import`-the-whole-cone. Each extra heavy import adds olean-load time.
- **Build deps once.** Run `scripts/pg-warm.sh` ONCE per machine — it pre-builds all #334
  substrate oleans (not the 808-file cone) so `pg-iterate.sh` never stalls on a missing olean.
  (Or `lake build <ThatSubstrateModule>` for a single dep; `lake exe cache get` for mathlib.)
- **Only run `lake build` to land.** Run a real `lake build <YourModule>` exactly once,
  right before committing, to confirm it passes the project build (`autoImplicit=false`,
  which `lake env lean` does NOT enforce — see pitfall (a)). Stagger these across agents.
- **Scratch files** go in `Frontier/` and start with `_`. They are NOT gitignored — 1,300+
  `_*` files are git-tracked lane state; treat `_` as "lane scratch, minimal imports", not
  "throwaway" (see `Frontier/README.md` lane hygiene).

## 2. ⚠️ Concurrency hazards on this shared tree (learned the hard way)

- **Race-deletions are real.** Bad merge resolutions have collaterally deleted in-flight
  lane files (issue #334 documents `c990bfa68` wiping three). After ANY conflicted rebase:
  re-pull, and `git show fork/main:<yourfile>` to confirm your last push survived. Keep a
  `/tmp` copy of any file before a reset/checkout loop.
- **Push loop** (origin is 403; push to remote `fork`, branch `main`):
  ```bash
  cp <file> /tmp/keep.lean
  for i in 1 2 3; do git fetch fork -q; git reset -q fork/main; cp /tmp/keep.lean <file>; \
    git add <file>; git commit -q -m "..."; git push -q fork HEAD:main && break; done
  ```
- **Files get renamed under you.** Locate declarations by THEOREM name, not filename
  (`grep -rln 'theorem <name>'`), never assume a path is stable.
- **Never `git checkout fork/main -- <dir>` over your own uncommitted work** — it clobbers.

## 3. The work (issue #334 ledger; ✓ = landed, → = actionable, ⊘ = blocked-on-literature)

**Class A — the δ* breakthrough.** Pin `δ*` above Johnson for explicit RS codes.
- A1 δ=0 forced-equality slice ✓ · A2 ✓ · A3 ✓ (Parseval threshold; **s=64 prize rows now
  open UNCONDITIONALLY**) · A4 ✓ · A5 exact n=12 profile ✓.
- → **A5 stretch:** the Lean equivariance pin for the orbit-reduction probe.
- ⊘ **The core δ* pin** (window interior, matching upper+lower): blocked on literature.
  Formalize *here* the moment a paper moves either side of the window.

**Class B — known-result residuals (formalizable today).**
- B1 [Jo26] Thm 4.2 general-generator factor ✓ (affine-line exact = `epsMCA_interleaved_eq`).
- B2 [Jo26] curve-decodability half: opener ✓; → **full [GG25] Def 3.1 (curve decodability)
  from scratch — its own multi-brick project.**
- B3 [KKH26] asymptotics: ✓ (+ s=64 unconditional via A3). → **s=128 rows need the
  Thorner–Zaman PNT-in-APs input** for polynomial field sizes `p=Θ(n^β)` (analytic number
  theory, independent of coding theory; route stub `KKH26PolyFieldCeiling.lean`).
- ⊘ B4 LD⇒MCA collapse ([ABF26] §5): does a good interleaved list-decoding bound imply a
  good MCA bound? Open research, same blocked status as A.

**Best entry points for a fresh agent (concrete, unblocked):** B3 s=128 Thorner–Zaman
formalization · B2 curve-decodability bricks · A5 equivariance pin · sharpening any A3/KKH26
threshold constant. The δ* core and B4 are blocked — only touch them when new literature lands.

## 3.5 The δ* state of knowledge (post-#357; the current frontier)

**Exact, machine-checked, axiom-clean (`propext, Classical.choice, Quot.sound`):**

| Result | File |
|---|---|
| δ* = j/n closed form on granularity bands (3(j−1)+k ≤ n), any smooth RS | `GranularityLadderRS.lean` |
| First exact pin: δ*(RS[F₅,4,2], 2/5) = 1/4 | `DeltaStarExactPinF5.lean` |
| Maximal second pin: δ* = 1/4 on ε* ∈ [2/17, 7/17) at RS[F₁₇,⟨2⟩,4] | `DeltaStarSecondPinF17{,Widened,Maximal}.lean` |
| Five-window curve at n = 16 (rate 1/4) | `VVectorN16.lean` |
| First exact explosion-band value: ε_mca(C84, 1/4) = 7/17 | probe + `FarCosetExplosion.lean` |
| Far-coset law: mcaEvent ⟺ line-explainability; ε_mca ≥ incidence/q | `FarCosetExplosion.lean` |
| Production bracket: δ* ≥ ladder reach uncond.; Johnson reach mod ONE residual, budget proven | `ProductionRegimeBracket.lean`, `ProductionJohnsonBudget.lean` |
| Johnson lane = ONE named Prop (CellPackageSupply), consumer chain fully proven | `Hab25JohnsonPackageSupply.lean` |
| Character-sum kernel closed at √q both sides (Parseval avg + completion worst case) | `SubgroupGaussSum{SecondMoment,WorstCase}.lean` |
| Quartet-tower law (census 4-adic recursion); strata classifications + mod-p transfers | `QuartetTowerLaw.lean`, `SlantedTransferThreshold.lean` |
| Tower monotonicity (ε_mca monotone up the 2-adic tower), crossing pin, Sperner ceiling | `TowerMonotonicity{,RS}.lean`, `CrossingPin.lean`, `SpernerCeiling.lean` |

**The open core — four equivalent faces (pick your attack surface):**
1. **CellPackageSupply** (`Hab25JohnsonPackageSupply.lean`): the BCIKS20 §5 per-cell
   package production. Everything downstream to `JohnsonDischargeStatement` is proven.
2. **The bad-side family**: a stack with > q·2⁻¹²⁸ bad scalars at some δ < 1 — every
   landed family is O(n)/q (silent at production budget).
3. **Sub-√q incomplete character sums** over smooth multiplicative subgroups
   (per-frequency; the average is already √|G|). **[CHARACTERIZED 2026-06-13 — read first:**
   `docs/references/proximity-gap-paley-spectrum/README.md` + memory `issue389-gauss-sum-reformulation`,
   `issue389-paley-graph-dictionary`.] The object `B = max_{b≠0}‖η_b‖`, `η_b=Σ_{y∈μ_n}ψ(by)`, IS the
   non-principal eigenvalue of the **generalized Paley graph** `Cay(F_q,μ_n)` (Liu–Zhou Thm 115);
   `B≤2√n ⟺ Ramanujan` = the **Paley Graph Conjecture** (open; best PROVEN is BGK `n^{1-o(1)}`, HBK
   vacuous below `q^{1/3}`). TWO axiom-clean named-conditional bridges land it: `GeneralizedPaleyRamanujan.lean`
   (`‖η_b‖≤2√n ⟹ WorstCaseIncompleteSumBound`) and `GaussPeriodMomentBound.lean` (the **moment method**:
   a Gaussian moment bound for the nontrivial spectrum implies `WorstCaseIncompleteSumBound` at `M_r`; min over
   `r≈ln q` gives `B≤√(2n ln q)`). **Important correction (#444):** the raw full-energy predicate
   `GaussianEnergyBound G r := E_r(μ_n)≤(2r-1)‼·n^r` includes the DC term `η_0=n`, and is now known false past
   the DC crossover at prize depth (`DCEnergyEssential.not_gaussianEnergyBound_of_deep`). The usable residual is
   the **DC-subtracted** transfer recorded by `DCEnergyCorrection.DCEnergyBound` and
   `DCSubtractedMoment.sum_nonzero_moment`: prove the char-`p` nontrivial-period surplus stays Wick-like for
   `r≈ln q`. The char-0 shadow is Lam–Leung/Bessel (not yet fully Lean-formalized — Mathlib lacks Lam–Leung);
   the prize case `n=2^30` remains open because it asks whether short `≤2ln q`-term `±1`-relations of
   `2^μ`-th roots vanish mod the prize prime. Same wall as faces 3↔4 and the additive-energy CRUX, but the
   canonical statement is DC-subtracted, not the raw `GaussianEnergyBound`.
4. **Line–ball incidence** (`epsMCA_ge_far_incidence`): max incidence of an affine
   line with far-coset direction against the weight-⌊δn⌋ syndrome ball in F_q^{n−k}.
   The explosion-band dichotomy (far cosets: every explainable scalar is bad;
   near cosets: unique-rep support correction) computes exact band values.

## 4. Substrate API — what's already proven, build on it (don't re-derive)

The bracket engine (everything routes through `mcaDeltaStar`):
- **`MCAThresholdLedger.lean`** — `mcaDeltaStar C ε*` (the threshold), `le_mcaDeltaStar_of_good`
  (lower from a good radius), `mcaDeltaStar_le_of_bad` (upper from a bad witness),
  `mca_good_set_downward_closed`. Plus `*_REFUTED` bricks recording dead ends — **read these
  before proposing a δ* form; `candidate_floor_is_exact_REFUTED` / `candidate_uptocapacity_REFUTED`
  already kill the naive guesses.**
- **`KKH26WitnessSpread.lean`** — the current ceiling: `kkh26_mcaDeltaStar_le`
  (`δ* ≤ 1 − r/2^μ` for the explicit eval code) + `kkh26_epsMCA_lower_bound` (+ `_of_not_dvd`
  divisibility-route variants — prefer these).
- **`MCAWitnessSpread.lean`** — `unique_bad_gamma_common_witness`: the structural obstruction
  any future lower bound must respect. Your δ* lower-bound attempt MUST be consistent with it.
- **`JohnsonListBound.lean`** — the up-to-Johnson side (the only unconditional regime).
- **`InterleavingStabilityMCA(P).lean`** — `epsMCA_interleaved_eq`: brackets transfer verbatim
  to interleaved codes (B1 substrate).
- **`Connections/ListDecodingAndCA.lean`** — the LD↔CA bridges (B4 consumer plumbing; the
  `*_residual` wrappers are PROVEN consumers, the hard witness-cover residuals are NOT).

## 5. References (papers; check `~/papers/arklib` and `PAPERS_NEEDED.md` before requesting)

| tag | ePrint | what |
|-----|--------|------|
| [ABF26] | 2026/680 | the Proximity Prize paper; §4.5 `mcaConjecture`, §5 LD⇒MCA, Thm 4.17 |
| [KKH26] | 2026/782 | the explicit bad-line ceiling; Lemma 1 prime threshold, Thm 1 η=Θ(1/log n) |
| [Jo26]  | 2026/891 | Thm 4.2 general-generator factor; curve-decodability half |
| [GG25]  | 2025/2054 | Def 3.1 curve decodability (B2 needs this from scratch) |

If a needed paper is absent, append a row to `/PAPERS_NEEDED.md` with the DOI/ePrint id and
leave the dependent residual as an explicit named hypothesis — never guess the statement.

## 6. The honesty contract (be BOLD in exploration, STRICT in claims)

The contract governs **two different axes** — be maximally liberal on the first, strictly
conservative only on the second. They are not in tension; conflating them is what stalls the work.

**(A) EXPLORATION — be bold, creative, and liberal.** Conjectures are *encouraged*, including ones
that may well be false. Invent novel routes, propose closed-form `δ*` formulas, state speculative
laws, attempt the open core directly, follow analogies from other fields. **You do NOT need to know
a conjecture is true before stating and attacking it** — that is the whole method (propose → try to
refute → if it survives, try to prove). A conjecture that turns out false is a *successful* grind
iteration, not a violation. Label such things clearly as `conjecture`/`Conjecture`/`def … : Prop`
(a named hypothesis) or a `docs/kb` note, give them honest novelty/feasibility scores, and explore
freely. Speculative `docs/kb` writeups and `scripts/probes` numerics need no proof at all.

**(B) PROOF CLAIMS — be strict; this is the only non-negotiable.** The discipline applies *only* to
what you assert is **proven**:
- **No `sorry`/`admit`/`native_decide`/fabricated `axiom` inside a theorem you present as proved.**
  The fast script's axiom audit must show only `[propext, Classical.choice, Quot.sound]` (no
  `sorryAx`). (A `sorry`-stubbed *work-in-progress*, clearly labeled as not-yet-proved, is fine —
  just never call it proven or commit it as "axiom-clean".)
- **Do not claim the open core is closed when it is not.** Stating a closed-form `δ*` *as a
  conjecture* (with the open input named) is encouraged (A); claiming `δ* = …` is *a theorem* with
  the open input silently discharged by a vacuous hypothesis or hidden `sorry` is the one forbidden
  move. The open core may live as an explicit named `Prop`/hypothesis indefinitely; naming an
  obligation and proving it elsewhere (`*_holds`/`*_of_*`) is the project's modularity convention
  (see `/docs/wiki/residual-census.md` before treating a `*Residual` as incomplete).
- **A statement found false gets a machine-checked countermodel** (`*_REFUTED`), then stays
  documented-refuted (tier-b) — don't "prove" it. (Finding the countermodel is good work.)

**One-line rule:** *explore anything; only the word "proven" (and an axiom-clean build) is sacred.*

## 7. Common pitfalls (each has cost a real debugging session)

- **(a) `lake env lean` ≠ `lake build`.** `lake env lean` runs `autoImplicit=true`; the project
  build is `autoImplicit=false`. An auto-bound variable passes the fast path and FAILS the real
  build. Declare every binder explicitly; do a real `lake build` before landing.
- **(b) Fintype instance clashes.** For `CanonicalSpongeState`/`Vector U N`, rely on the derived
  `instFintypeVector`; don't add an explicit `[Fintype …]` binder that desyncs.
- **(c) `ℝ≥0∞` arithmetic:** `ENNReal.natCast_sub` orientation, `tsub`, `absDiff`; `div_le_div₀`
  variants. Prefer the `_of_not_dvd` KKH26 route (cleaner divisibility lemmas).
- **(d) Probe scripts** (`scripts/probes/probe_*.py`) generate exact/sampled numerical evidence;
  a theorem must MATCH a probe before you trust it. Don't formalize a sampled value as exact.

---
Deeper math: `docs/wiki/` · the in-tree `*_REFUTED`/`*Genuine.lean` files · issue #334 thread
(64+ comments of live frontier state — read the latest before starting a lane).

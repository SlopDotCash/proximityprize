# The δ* Programme — Agent Guide (successor of issues #334 → #357)

> This file is auto-loaded when you work under `ArkLib/Data/CodingTheory/ProximityGap/`.
> It is the **single source of truth** for attacking the mutual-correlated-agreement
> threshold (δ*) formalization. `AGENTS.md` in this directory is a verbatim copy.
>
> **Knowledge base (read before starting):**
> - `docs/kb/deltastar-357-compiled-knowledge.md` — the full #357 campaign distilled
>   by theme (every exact result, refutation, probe, and the open core).
> - `docs/kb/deltastar-research-map.md` — paper inventory + adjacent-math survey +
>   ranked attack vectors.
> - `ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md` — every refuted approach
>   with its constraint lemma. Check it before re-trying anything.

## 0. The 30-second orientation

You are formalizing residuals around the **Ethereum Proximity Prize** ([ABF26], ePrint
2026/680, proximityprize.org). The $1M open core — pin the *mutual correlated agreement*
list-decoding threshold `δ*` for explicit smooth-domain Reed–Solomon codes in the window
`(1−√ρ, 1−ρ−Θ(1/log n))` at `ε* = 2^-128` — is **genuine open research, blocked on the
literature** (no known technique bridges Johnson→capacity for explicit fixed RS codes).
**Do not fabricate a closure of the open core.** Predecessors #232, #334, #357 are
CLOSED (each distilled into the successor); see §3.5 for the current state.

## 1. ⚡ BUILD — read this FIRST or you will clog the machine

This cone is **808 files**. `lake build <module>` traces a 3000+-job graph (**~2-3 min
even with no changes**) AND takes the `.lake` build lock, which **serializes every agent**
on this 16-core box. Never iterate with `lake build`.

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
- **Scratch files** go in `Frontier/` and start with `_` (gitignored pattern) until proven.

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
   (per-frequency; the average is already √|G|).
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

## 6. The honesty contract (non-negotiable; the whole project depends on it)

- **No `sorry`/`admit`/`native_decide`/fabricated `axiom`.** The fast script's axiom audit
  must show only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
- **A false statement gets a machine-checked countermodel**, then stays documented-refuted
  (tier-b), e.g. `Lemma5_8EagerBirthdayResidual`, the `*_REFUTED` bricks. Do not "prove" them.
- **The open core (δ*, B4) stays an explicit named `Prop`/hypothesis** until literature lands.
  Naming an obligation and proving it elsewhere (`*_holds`/`*_of_*`) is the project's modularity
  convention — see the generated `/docs/wiki/residual-census.md` ledger before treating a
  `*Residual` name as incomplete.

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

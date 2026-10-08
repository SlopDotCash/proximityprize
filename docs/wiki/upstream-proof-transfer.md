# External proof transfer

The native campaign and the public Proximity Prize benchmark have different
toolchains, definitions, and targets. Import reusable results into the native
library with explicit provenance. Keep complete incompatible proof packages in
pinned submodules with their original dependency lock and license. Do not replace
the native campaign's definitions merely because a benchmark uses similar names.

## Proximity Prize reference

`external/proximity-prize` pins
[`ed2b68c4a330d76dc4ab6693eec81b685b493270`](https://github.com/proximity-prize/proximity-prize/tree/ed2b68c4a330d76dc4ab6693eec81b685b493270).
It retains the Apache-2.0 license, attribution, protected targets, both complete
submission proof trees, and the optional arithmetic helper. The pin uses Lean
4.32.2 and ArkLib `e65197892890b8fd9b0dc05b8980273cf1d595cc`; the native project
is being migrated to Lean 4.34.0. Their oleans and Lake package directories must stay separate.

The [file inventory](../upstream/proximity-prize-2026-10-06.json) records hashes,
imports, line counts, declaration counts, and native short-name match counts.
Short-name matches are discovery hints, not proof of semantic equivalence.
The package contains 153 lower-submission files (149,662 lines), five upper files
(2,256 lines), and three protected benchmark files. Review includes the terminal
certificates, their dependency graph, the profile and score semantics, the
kernel-evaluation helper, source-policy scan, and the verification harness.

| Surface | Finding / treatment |
| --- | --- |
| `IRSProfile` | Concrete size-`2^18`, dimension-`2^20`, eight-row IRS over the KoalaBear sextic extension; retain its exact domain/encoder/distance proofs. Our four-coordinate Koala toy anchor is a different code. |
| Lower candidate | `ProtocolClaim 6815 331366399 1073741824`; retain the complete selected-pencil, function-field, packing, and literal-certificate chain. Its 68.15-bit score is a spot-check quantity derived from a certified safe radius. |
| Upper candidate | `ProtocolClaimUpper 11613 122369`; retain the collision, prescribed-top-coefficient and 512-fibre rational-pencil constructions. Its 116.13-bit claim certifies a whole unsafe suffix for winning-set density. |
| Arithmetic helper | Backported to `ArkLib.ToMathlib.KernelEval`, preserving recursive sums, exact affine/nested-sum formulas, prefix subtraction, and inexpensive sufficient-condition lemmas. |
| Linear projection | Backported to `ArkLib.ToMathlib.LinearProjection`: collision averaging, image density at least `N/(q+N-1)`, and surjective projection when `N > (q-1)^2`. The last proof is shortened to a corollary of the quantitative bound. |
| Publication scripts/workflows | Retained inside the reference, never run by the native wrapper. They are specific to the organizer's verifier service and do not establish local campaign completion. |
| README baselines | The source README still lists starting baselines of 53 and 128 bits. The actual candidate theorem types above are the appropriate snapshot record. |

The retained benchmark scores are neither a proof of the native production δ*
conjecture nor a full-protocol security claim. The upper target also explicitly
distinguishes winning-set density from an equality with minimal game error and
does not construct an end-to-end attacking prover.

## Reproduce the separate package

```sh
git submodule update --init external/proximity-prize
scripts/proximity-prize-reference.sh cache
scripts/proximity-prize-reference.sh targets
scripts/proximity-prize-reference.sh lower
scripts/proximity-prize-reference.sh upper
scripts/proximity-prize-reference.sh replay-upper
```

The wrapper checks the reviewed commit and clean tracked source, selects the
submodule's own toolchain, and uses the shared `lake-locked.sh` concurrency gate.
The default `ProximityPrize` target imports **only protected targets**, so building
it alone does not check either submission. The two explicit candidate builds are
required. The wrapper never submits a score, contacts the ranking service, or
pushes a branch. Native backports are covered by `scripts/flagship_axioms.txt` and
the native `scripts/validate.sh` gate.

## Verification boundary

The pinned reference's comparator patch removes whole-environment replay and
quotient post-checks in favor of submission-module checking against trusted
imports. An axiom whitelist or a successful ordinary compilation does not replace
fresh replay of the dependency closure. The open
[reference PR #569](https://github.com/proximity-prize/proximity-prize/pull/569)
proposes Lean 4.34, restoration of replay and quotient checks, and a CompPoly
proof-body repair. Its description reports local replay but explicitly leaves
new hosted profiles and verification pending. It also predates the latest 68.15
lower candidate. Do not silently promote that proposed upgrade or use its older
replay claim as evidence for this pin.

Report source retention, native compilation, candidate compilation, axiom audits,
fresh kernel replay, and hosted ranking separately. In particular, a pin and an
inventory make the source reproducible; they do not certify the entire package.

All publishing for this project must target `SlopDotCash/proximityprize`.
`Verified-zkEVM/ArkLib` and the organizer's repository are read-only sources.

## ArkLib main and all open PRs

`external/arklib` pins the reviewed October 8 upstream main at
[`745e77939ac4cecf0333af8410a2463c5c7cb655`](https://github.com/Verified-zkEVM/ArkLib/tree/745e77939ac4cecf0333af8410a2463c5c7cb655).
The [refreshed file inventory](../upstream/arklib-main-2026-10-08.json) compares it with
native commit `c5846e1d8ace7df60f0c1b057cfbe55cf91b353c`; byte differences are discovery hints, not semantic gaps.
The [main file inventory](../upstream/arklib-main-2026-10-06.json) records all
920 upstream library files against the native starting commit: 655 absent paths
and 265 byte-different paths. These are discovery counts, not a semantic count
of missing results.
The [PR manifest](../upstream/arklib-prs-2026-10-06.json) records all 51 open PRs,
including drafts, with immutable heads, base commits and complete file lists.
A fetched head is not a claim that the PR has been merged or checked locally.

```sh
git submodule update --init external/arklib
python3 scripts/arklib-reference.py list
python3 scripts/arklib-reference.py fetch
python3 scripts/arklib-reference.py worktree --pr 1285 --path /tmp/arklib-pr-1285
```

The script only fetches pinned revisions from the read-only upstream and creates
separate detached checkouts. Run the native checkout's `scripts/lake-locked.sh`
from an external PR checkout for serialized builds. Never publish upstream.

Upstream Fin induction, insertion, coding-theory preliminary and polynomial
interface proof repairs are adopted without changing their mathematical
statements. The `AffSpanSet.instFinite` lemma remains available explicitly;
its invalid instance registration is removed because `Set.Finite` is not a class.

Native transfers under validation include the generic linear-budget,
line-injectivity, finite-set cardinality, pairwise incidence and sample incidence
lemmas from main, tuple-intersection bounds from PR #1285, and main's 28-file
interaction layer plus sequential probability bounds. The latter replaces the
parked `Interaction.Reduction` implementation with the current PolyFun API.
The two other historical parked modules remain untouched. Module visibility
markers and `import all` modifiers are removed in native copies to match this
repository's legacy module layout (Lean loads legacy imports at private level);
original authors and licenses are retained.

PRs [#1259](https://github.com/Verified-zkEVM/ArkLib/pull/1259) and
[#1260](https://github.com/Verified-zkEVM/ArkLib/pull/1260) supply the native
backward-extraction and knowledge-composition layer. Their immutable heads are
recorded in the PR manifest. The imported certificates quantify over every
concrete intermediate path, including false middle claims, and retain named
witness transports; they do not assume an online middle witness or claim
unrestricted stateful-world composition. The original ordinary-import client is
in `ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean` and is
built by `scripts/validate.sh`. `ArkLibTest` is an optional Lake library so its
concrete execution checks stay separate from production imports. The modules and client
passed a local Lean 4.34 Lake build on 2026-10-07, including concrete true- and
false-middle-path executions. Four selected extraction, sequential-certificate,
and appended-challenge theorem roots passed a complete axiom audit with only
`propext`, `Classical.choice`, and `Quot.sound`.

## Lean 4.34 migration

The native toolchain is pinned to `leanprover/lean4:v4.34.0`, with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, VCVio
`91386ad88ed72292d0f4e3153a444336920fc565`, and PolyFun
`3710d71b28404a151b8d1f0ce080ea448778dec0`.
CompPoly is pinned to the proposed replay repair
[`da1e1b5d048d26eca4583ff930f248c5e2bb5d9e`](https://github.com/yudduy/CompPoly/commit/da1e1b5d048d26eca4583ff930f248c5e2bb5d9e).
Compared with upstream `v4.34.0-patch2`, it supplies explicit concrete field and
finiteness instances in the quintic and sextic irreducibility proofs, preserves
their statements and certificates, and adds fresh-closure replay regressions.
The native `CompPolyTests.Fields.KoalaBear.FreshReplay` target passed locally on
2026-10-07: it replays both complete irreducibility dependency closures in an
empty kernel environment and checks the quotient declarations against the originals.
Both irreducibility roots also passed a separate local axiom check with only
`propext`, `Classical.choice`, and `Quot.sound`, and are registered in the
independent flagship axiom-whitelist gate. This result does not establish replay of either full prize
candidate or import the benchmark PR's hosted-release claims.

The native compatibility edits use these Mathlib API correspondences:

| Lean 4.30 spelling | Lean 4.34 spelling |
| --- | --- |
| `mul_le_mul_left' h a` | `mul_le_mul_right h a` |
| `mul_le_mul_right' h a` | `mul_le_mul_left h a` |
| `Finset.prod_le_prod hnonneg hle` | `Finset.prod_le_prod₀ hnonneg hle` |
| `Finset.prod_le_prod' hle` | `Finset.prod_le_prod hle` |
| Multivariate `coeff index polynomial` | `polynomial.coeff index` |

These rename existing proof applications; they do not remove the nonnegativity
premise from real-valued product comparisons. Native proofs and the imported
linear-projection helper also use narrower imports where checked, reducing the
number of unrelated modules loaded by each Lean process.

The VCVio migration also requires semantic care: the former `HasEvalSPMF`
interface is split across operational support, a lawful lift into `SPMF`, and
support/distribution compatibility. In the new API, `𝒟[...]` denotes a measure;
`𝒮[...]` denotes the discrete subprobability computation. Existing uses must be
checked against those meanings rather than changed solely to satisfy elaboration.
`ArkLib.ToVCVio.SupportOfSPMF` derives the pure, bind, and map support equations
from a lawful discrete lift and support/distribution compatibility; its direct
Lean 4.34 check reports only the standard axioms. This avoids imposing
`ExactMonadAttach` on the older probability helpers. Uniform oracle proofs use
VCVio's explicit `IsUniformSpec` interface rather than installing a global
uniform interpretation for every finite inhabited oracle. `OptionT` simulation
bridges explicitly apply `.run` when measuring the underlying computation's
failure and `none` mass, preserving the old statements' run-level meaning.
The oracle-interface module follows upstream in removing the retired
`OracleSpec.DecidableEq`/`Fintype`/`Inhabited` dictionaries; ordinary per-response
instances now supply that data. VCVio now supplies the more general
`OptionT.probEvent_eq_of_run_map_eq`; the duplicate native specialization is
removed while its public name remains available through the existing import.
`MarginalBound` now imports the probability API directly rather than the protocol
security layer; its six printed marginal-domination theorems pass the local
Lean 4.34 axiom check with only standard axioms.

The native migration and new transfers are still under validation. Do not treat
the updated pins or the earlier Lean 4.30 checks as a successful Lean 4.34 build.

### Native executor soundness (PR #1261)

The generic portion of upstream PR #1261 at `433513c9d8126c4f93a1d0b79d8fd8ce2ad3e2aa`
is imported with its ordinary-import client. It bounds the actual interpreted executor by the
sum of local challenge errors, retaining prover private continuations, verifier receive effects,
and failure-induced loss of probability mass. The uniform corollary gives `count * error`;
the zero-challenge case only assumes initial falsity for false inputs. The client exercises an
empty response type interpreted as failure, whose successful output mass is zero.

The generic modules and ordinary-import client passed a local Lean 4.34 build on
2026-10-07. Both executor soundness roots passed a complete axiom audit with only
`propext`, `Classical.choice`, and `Quot.sound`. The
Sumcheck specialization is not yet imported because its legacy Sumcheck dependencies need
reconciliation with this repository. This is a partial PR transfer, not validation of that
specialization.

### Additional native compatibility checks

The native runtime-soundness, composition, terminal-measure, bind-one, marginal-bound,
and OptionT helper targets passed a focused Lean 4.34 Lake build on 2026-10-07.
`ArkLib.ToVCVio.Lemmas` also passed its native module build. Distance and multilinear
polynomial repairs preserve theorem statements while adapting minimum APIs and
explicit conditional reduction to Mathlib 4.34. Full-library and Research validation
remain outstanding; these focused results do not certify the complete migration.

The coset FFT-domain definitions now incorporate upstream main
`35ddcaa83f683011f944f58904be779495a5709a`'s explicit additive/multiplicative index
conversion and subgroup-unit API. This removes unnecessary finite/decidable
constraints from the abstract domain interface and provides checked reconstruction
and evaluation lemmas; the adapted native module passes a direct Lean 4.34 check.
The native bivariate-polynomial port uses the public monomial constructors instead
of relying on the former internal polynomial representation. Its direct check passes,
as do the linear-code and relative-distance compatibility repairs.

The indexed and vector-product marginal helpers and probability-one bind composition
now use the split lawful-SPMF interfaces. Direct/source-composed checks pass; all
12 vector-product/counting roots report only standard axioms in the unabridged Lean
output. Their ordinary native module builds remain to be completed. The two new
coset reconstruction roots also pass the complete axiom whitelist check and are
registered in the persistent flagship gate.

### Corrected Johnson radius and alphabet generality

Upstream main's Johnson foundation removes the field assumption from the absolute
Johnson bound, using coordinatewise alphabet equivalences for recentering. Its
`Expectations`, `Lemmas`, and `Basic` changes are adapted natively while retaining
our additional Plotkin lemmas and the existing `J'` spelling. A composed-source
Lean 4.34 check passes; the two Johnson bound roots and our retained Plotkin
average-distance root have only standard axioms.

`ArkLib.Data.CodingTheory.JohnsonBound.CorrectedFamily` imports upstream's
list-budget correction under `JohnsonBound.Corrected.Jqℓ`: the factor is
`(ℓ - 1) / ℓ`. The older native `JohnsonBound.Jqℓ` uses the reciprocal factor;
its documented refutation remains valid and its meaning is preserved. The new
`CodingTheory.Corrected.johnson_bound_lambda_le_ell` covers arbitrary finite
alphabets and every natural list budget at least one, with the negative-radicand
case proved through Plotkin. It uses the native `ListDecodable.Lambda`, including
its natural-cardinality representation. Its composed-source check and full axiom
report pass. Ordinary native module builds are still queued.

PR #792's useful witness constructors are now adapted in
`Research.ProximityPrize.ListDecodingWitnesses`. They use native `ListLowerWitness`,
minimum-distance preservation for nonempty interleaving, and the new alphabet-general
unique-decoding list bound. The Johnson constructor uses the corrected factor and
interleaved alphabet cardinality `|F|^m`. Existing generic wrappers and the distinct
native `GrandListResolution` remain in place. A strict composed-source Lean 4.34
check passes for all six interleaving/witness roots with only standard axioms;
ordinary module and Research build validation remains pending.

Further direct migration checks pass for divisor-list injectivity, antipodal half-sums,
iterated-fold membership, unconditional joint independence, and correlated agreement.
The divisor proof now explicitly uses the Euclidean-domain GCD API. The binding-depth
norm proof compares symbolic exponents before specialization, avoiding kernel evaluation
of an integer with more than two billion bits while preserving the theorem statement.

The mechanical migration also removes the obsolete explicit placeholder from
`zero_le _` across 96 remaining library/Research files (150 applications/comments),
matching Mathlib's now-implicit argument. This is a proof-API edit; the statements
and existing conditional premises are unchanged. Whole-tree validation remains
pending. Additional direct checks pass for the ball-intersection translation,
Lam–Leung independence, combinatorial probability, chord census, root-height,
Gauss-sum norm, and subgroup-sumset repairs. The Gauss-sum file now reuses Mathlib's
conjugation lemma, and an unusable hypothesis-dependent instance is exposed as an
explicit theorem.

## State-restoration and Appendix A review

PR #1263 adds native adaptive state-restoration extraction, verifier replay, closed-oracle
outputs, and independent pre-sampled private coins. Its five source modules and ordinary-import
client are adapted locally. Its required VCVio revision is
`fe608a46c3df4608ea774611662a255326b5d1ff`, an extension of the previous pin with dependent
uniform tables and fresh-query bounds. Isolated dependency and native source/client checks pass, with nine full standard-only axiom
closures. The client evaluates both accepted and rejected oracle outputs. All six combined
restoration modules and both clients now pass ordinary builds with the installed VCVio pin. The later security
stack through #1283 uses `6bf6c91b66dfa159342c355a4b81d65b55cb54a4`, a substantially broader
VCVio change requiring a separate compatibility review.

The restoration event is tied to the actual cached completion and verifier execution.
Closed-output rejection is unsuccessful, and private-coin failure contributes missing mass.
The pre-sampled coin theorem does not assert equivalence with arbitrary interleaved coin effects.
These distinctions must survive the native adaptation and its test client.

PR #787 fixes the paper-facing Appendix A interface: separability after specialization is over
`RatFunc F`, and specialization content contributes to the cleared derivative/numerator weights.
Our `RationalFunctionsCore.Hypotheses` still uses the stronger polynomial-ring separability
assumption. Its existing results must remain available while the weaker fraction-field interface
and corrected content bounds are adapted. The Section 5 exceptional-set/content bridge and the
degree-one direct-root branch must remain explicit obligations; importing the PR must not turn
its conditional interfaces into unconditional claims.

PR #1264's nonuniform-round budget is adapted alongside #1263. With local errors `e_j`,
the bound is `Q * max_j e_j + sum_j e_j`. The isolated VCVio extension at
`91386ad88ed72292d0f4e3153a444336920fc565`, six native modules, and both clients pass.
Three additional extraction/game/client roots have only standard axioms. The two-round client
proves the strict improvement `7/16 < 1/2`. The native VCVio pin now includes this revision;
all other dependency revisions were preserved. Both ordinary clients and all six source modules now pass against the installed pin.
A separate raw audit of 19 roots covering restoration, candidate bounds, native packing, and
concrete trapdoor recovery reports only `propext`, `Classical.choice`, and `Quot.sound`.

The Lean 4.34 migration also renames the removed finite-set partition-count lemma to
`Finset.card_filter_add_card_filter_not` across 56 library/Research files (61 uses).
The statement is unchanged. Direct checks pass for the two-power fibre count, explicit
cyclotomic towers, and the subset-sum character interface; whole-tree validation is pending.

## Consuming numeric bounds

The useful authoring rule from upstream PR #776 is to carry the target comparison in Lean.
A theorem `carrier ≤ formula` does not by itself establish the desired error/list budget.
At a consumer, combine it with a proved `formula ≤ target`, then construct the native
`MCALowerWitness` or `ListLowerWitness`. The existing `ofLe` interfaces and the new unique-
decoding/Johnson constructors already require this evidence. All 17 formula-specific wrappers
in #776 were reviewed: they add transitivity and, for list counts, an `ENat` coercion bridge;
they do not add a mathematical bound. The native transfer uses the existing witness interfaces
instead of duplicating these wrappers.

Preserve the source statement and its domain hypotheses when adapting a bound. An admitted
formula does not become a proved result by wrapping it. Check denominator positivity, natural
versus real division, the probability ceiling for lower bounds, and whether existence guards
are satisfiable. Keep the corrected Johnson formula distinct from the refuted legacy formula.
The upstream rule is documented at
[PR #776's bound-statement guide](https://github.com/Verified-zkEVM/ArkLib/blob/133f72bfb1b4f1e828cfcf253f9d947f18498252/docs/wiki/bound-statement-hygiene.md).

The PR manifest now records each reviewed head's exact Lean toolchain and core dependency
revisions. These are compatibility evidence, not build certificates. A newer PR can require a
large dependency migration even when its own file diff is small.

## Native packing and fixed-candidate bounds

The native `RingSwitchingProfile` already contains additive and atomic extraction laws.
`ProfileCoordinates` derives both reconstruction inverses and agreement of the two embeddings
on the base ring without adding assumptions. These are the useful data laws introduced in
upstream #1257, adapted to the native orientation: native rows correspond to upstream packing
columns. Three strict composed-source axiom reports pass with standard axioms only. The
remaining packing refactor and protocol consumers are still under review.

The generic probability lemmas from #1289 and their empty/correct-candidate client are adapted
in `ArkLib.ToVCVio.EvalDist.ProbabilityBounds`. They cover a candidate set fixed before sampling,
exclude correct candidates, and expose the exact-functional case. Both roots have standard-only
axioms in a strict composed-source check. The ring-switching consumers and their tight and
challenge-dependent negative tests remain pending; this is not an adaptive-list security claim.

PR #926 closes structural context-lifting gaps in upstream, but the native implementation
already proves execution transport, completeness, and all four soundness transports.
Its state function uses outer-language membership at round zero, then projects to the
inner state at positive rounds. This preserves the empty-state biconditional without
adding the language-completeness hypothesis needed by the PR's direct projection.
Preserve that native interface; its legacy dependency closure still needs Lean 4.34 validation.

PR #1266 regenerates declaration and citation indices for upstream main. Those outputs
cannot describe the native tree and must not replace native generated files. Regenerate
native indices from the integrated source. Its four stub paper pages add bibliographic
scaffolding, not formal results; add native stubs when native citations require them.

The FFT-domain definitions now follow the reviewed main revision's explicit additive-index
to multiplicative-unit interface, matching the earlier coset-domain transfer. This removes
unneeded finiteness/decidable-equality assumptions and repairs the Lean 4.34 type-tag boundary.
Direct checks pass for the FFT module, matrix multilinear evaluation, linear multivariate
extension, puncture/filter membership, and the nontrivial additive-character sum proof.
The proximity-generator positivity proof is updated to the current finite-infimum API;
its direct Lean 4.34 check now passes after explicitly supplying the nonempty-finset proof.

PR #737 targets `q^((α-β²) * logb 2 q)` and still admits the hard-regime theorem.
The native `BKR06BareT312` front door proves the natural-log variant, using the slack
from `log 2 < 1` in its band argument. These are different bounds when `β² < α`.
The native theorem does not settle the stronger base-two target. Preserve the proved
native construction while reviewing upstream finite-field and good-window helpers;
never import the admitted target as a proved improvement.

The function-field regularity bridge now uses the existing explicit quotient witness
instead of relying on simplifier reduction across the two embedding definitions.
`RationalFunctionsCore.lean` passes its direct Lean 4.34 check after this repair.

PR #655 identifies a concrete limitation of the native KZG hardness assumptions:
private setup sampling still exposes concrete SRS group elements to unrestricted Lean
functions. `ConcreteTrapdoor.lean` adapts its choice-defined discrete logarithm and
inversion proof, and proves recovery from the native generated verifier SRS leg.
A strict composed-source Lean 4.34 check of native `PrimeOrder`, `KZG.Algebra`, and the
new module passes; the inversion and recovery roots use only standard axioms.
`ConcreteVacuity.lean` now adapts both actual-game probability-one attacks, both giving-up
controls, and the meaningful-error refutations. The ARSDH refutation explicitly requires
`D + 2 ≤ p`. All compile in an ordinary Lean 4.34 build against the native game definitions;
all 11 selected attack/refutation/control roots pass a raw standard-only axiom audit.
The restricted generic-group security repair remains pending.

Coset-domain membership transport now uses the proved `toCosetFftDomain_apply`
interface rather than unfolding unit and type-tag representations. This preserves the
native `mem_def` equality orientation and passes a direct Lean 4.34 check.

The Reed–Solomon migration now unfolds code length and the evaluation linear map explicitly
in the minimum-distance and interpolation proofs. Both direct checks pass. Two local oracle
lifting lemmas are removed because the installed VCVio revision supplies them under the same
names and signatures; native association/coherence lemmas remain and pass their direct check.

The KZG sampler and hardness definitions no longer import the whole VCVio umbrella; their
specific dependency imports suffice in the passing native build. Seven additional local
OptionT/StateT simulation lemmas are removed in favor of the installed upstream definitions.
The retained simulation fusion and support code passes its direct check. Interleaved-code
constructions are definitions rather than invalid instances, and matrix/subtype boundaries
are made explicit; that module and folded Reed–Solomon both pass direct Lean 4.34 checks.

Further direct Lean 4.34 checks pass for the folded-Wronskian determinant factorization,
folded-RS evaluation/vanishing transport, and correlated-agreement floor/probability bounds.
These repairs expose the existing matrix/evaluation interfaces and avoid broad simplification
of a probability expression. The Research witness build is being rerun against these repairs;
none of these focused checks establishes a complete native/Research build. The citation index
was regenerated from native source, and both freshness and strict knowledge-base lint pass.


## Further Lean 4.34 coding-theory repairs

The native Research list-decoding witness target now passes an ordinary build (3,494 jobs).
The full native/Research build remains incomplete: its third attempt encountered both source
compatibility failures and repeated macOS open-file failures, and was stopped with its cache
preserved. A focused pass is not evidence that the whole repository builds.

The reviewed main revision supplies shorter Polishchuk–Spielman degree proofs that reuse the
shared bivariate interface. Its Guruswami–Sudan update adds the first-moment bound and a shared
arbitrary-degree counting criterion, and consolidates the multiplicity/divisibility proofs.
Both modules pass direct Lean 4.34 checks. Eight GS and three PS roots pass raw axiom audits
with only `propext`, `Classical.choice`, and `Quot.sound`. Native `weigthBoundIndices` and
`codewordToPoly` names are retained so existing research clients keep their interfaces.

The Berlekamp–Welch truncation now uses the current polynomial coefficient representation.
The folding-polynomial degree bound uses upstream's direct termwise degree estimate instead
of reconstructing the folding polynomial first. Both pass direct Lean 4.34 checks, as does
AHIV22 support after avoiding unnecessary simplifier normalization across matrix boundaries.
The even/odd evaluation proof now exposes composition of evaluations explicitly. The weighted
bivariate product bound composes the finite-sum degree inequality directly; this avoids an
expensive rewrite without raising the heartbeat limit. Localized place evaluation supplies
explicit algebra-map instances. These three modules pass direct checks as well.

The interleaved-list projection now applies the existing distance projection in the needed
orientation, removing two symmetry conversions. It explicitly transports the row equality
decision instance to the classical instance used by the Hamming ball. Its direct check passes.
All nine repaired modules now pass ordinary dependency-aware builds. The final interleaved-list
build completed successfully (3,414 jobs). A separate audit importing the compiled GS, PS,
weighted-degree, and localized-place modules reports only standard axioms for all 14 selected
roots. The next full native/Research build is still in progress.


## Protocol-port and literature review rules

The documentation-only PRs [#1258](https://github.com/Verified-zkEVM/ArkLib/pull/1258),
[#1273](https://github.com/Verified-zkEVM/ArkLib/pull/1273), and
[#800](https://github.com/Verified-zkEVM/ArkLib/pull/800) contain no Lean declarations to import.
Their useful review rules apply to the remaining ports:

- Preserve statements, witness carriers, oracle interfaces, challenge distributions, and rejection.
  Prove execution correspondence including private state, shared oracle state, and query logs.
  Equal public outputs alone do not establish the required correspondence.
- Keep named extraction and explicit error bounds. An ordinary soundness result with a trivial
  witness does not replace knowledge extraction. Runtime requires executable realizers and their
  measured execution; query charges alone do not prove extraction complexity.
- For restoration, retain the actual cached completion and closed output. Adaptive completion
  cannot be charged as an independent fresh event. Expected cost under independent replies is
  not expected cost under the actual cache. The unqueried-ancestor argument needs all-background
  resampling, not conditioning on the absence of earlier bad events.
- Replace legacy consumers only after correspondence, security, query accounting, full builds,
  and axiom audits. Upstream roadmaps and CI claims are not evidence for the native port.
- Record the paper version alongside statement numbers. Compare alphabet-normalized rate with
  base-field dimension rate, and record when folded-code admissibility is stronger than a printed
  hypothesis. Audit the named theorem's dependency closure; neither an unrelated admission nor a
  source-level zero-hole census determines that theorem's mathematical completion status.

The upstream ABF26 audit uses a different `Lambda` API and admission ledger. Its native status
labels must therefore be recomputed rather than copied. The native residual census remains the
source for documented residuals.


The new `ArkLib.Data.Polynomial.ResultantDegree` module comes from the reviewed upstream main
revision. It generalizes the field-only PS resultant bound to commutative coefficient rings,
explicit coefficient budgets, and padded resultants, and includes total-degree/Bezout and
positive-characteristic derivative bounds. The native PS theorem now delegates to that shared
result. The new module and its PS consumer pass an ordinary 2,293-job build; eight selected
roots pass a strict source-composed standard-only axiom audit. Native public PS statements are
preserved.

Repeated open-file failures in the full build were traced to three research modules importing
all of Mathlib. Their imports are being narrowed to the actual mathematical and tactic
libraries. The three-prime packet refutation, value-spread second-moment proof, and Sudan list bound pass
direct Lean 4.34 checks with these narrower imports. This reduces the loaded dependency set without
changing their statements or proofs. Their ordinary build now also passes (3,098 jobs); the
full build still needs verification.


The PS existence proof now uses Mathlib's polynomial `natDegree_mul` for the outer variable
and upstream's explicit arithmetic estimates. Its public hypotheses and conclusions are
unchanged. The direct Lean 4.34 check passes; both `ps_exists_p_nonzero` and `ps_exists_p`
report only standard axioms in the source check. Its ordinary rebuild also passes (2,294 jobs).


Four more whole-Mathlib imports are narrowed to the finite-field, polynomial, root-counting,
and linear-algebra dependencies used by `StepanovWeilSubstrate`, `StepanovNonVanishing`,
`SmoothFiberCount`, and `SeparatingCoordinates`. All four pass direct Lean 4.34 checks. The latter
three also pass ordinary builds; the substrate now passes its ordinary rerun with the explicit
`DegreeLT` dependency.
No theorem statement or proof is changed by this import cleanup.

PR #1256's independent coordinate layer is adapted under `RingSwitching.Packing`:
`PackingData` supplies separate finite bases over a common commutative ring; `transpose` is a
linear equivalence with both inverse laws; finite observations commute with this transpose.
No embedding between the two algebras is assumed. `CheckedObservation` gives honest checking
and inverse-witness readback under an explicit honest-message premise. It does not prove that
an arbitrary accepted message is honest. The upstream clients exercise unequal ranks over
`ZMod 6`, zero divisors, empty observations, and a three-cycle plus an accepted dishonest-message
counterexample. All three packing modules and both clients pass an ordinary Lean 4.34 build (3,098 jobs).
They are included in routine validation. Polynomial packing and coefficient transport are also
adapted: both packing/unpacking round trips and Boolean evaluation identities pass a strict
source-composed Lean check, including the upstream unequal-rank, zero-divisor polynomial client.
The 14 compiled coordinate/observation roots and eight installed polynomial roots use
only standard axioms. The ordinary polynomial and BW matrix build passes (3,543 jobs). The subsequent relation/batching integration is recorded below; scalar layouts, multiplier
protocol consumers, and protocol integration remain pending; #1256 is partial.

The BW matrix minor and row-update proofs are adapted to Lean 4.34 using explicit matrix
application and finite-sum rewrites, preserving their statements. The direct check passes.

The divergence/concentration proofs also pass direct Lean 4.34 checking after adapting
probability-map definitional equality, affine-span coercions, polynomial finrank, and
nonnegative-rational casts. The ordinary rebuild also passes. Public hypotheses and conclusions
are unchanged.


PR #1256's relation and batching layers are now adapted with their original clients. The
relation layer preserves and reflects the full family of opening claims, reconstructs openings
from honest slices, and derives weighted sumcheck claims in a compatible challenge algebra.
It does not infer slice correctness from an arbitrary accepted coordinate check. The client
independently checks incorrect claims, slices and sumcheck targets over unequal-rank algebras
with zero divisors, including the zero-variable edge case.

Batching provides deterministic singleton separation over any commutative ring, reindexing,
injective coefficient transport, and power/equality strategies over finite domains. Its client
attains the `2/5` bound over `ZMod 5` and demonstrates the invalidity of the domain bound over
`ZMod 6` at the actual probability level. Both production modules and both clients pass ordinary
Lean 4.34 builds. The existing PMF root bounds are reused through the new `SampledPolynomial`
adapter to VCVio's sampler.

The supporting Boolean interpolation uniqueness and algebra-evaluation theorems work over
commutative rings, including rings with zero divisors; the older domain-specialized native
interface remains available. The read-once multiplier evaluator, scalar layouts, and protocol
integration from #1256 are still pending.

All 27 selected roots from this relation/batching batch pass the installed-module axiom audit
with only `propext`, `Classical.choice`, and `Quot.sound`. The repository census finds zero
live proof holes. These clients and roots are included in the routine validation commands.


PR #1256's remaining independent algebra is adapted: `ReadOnce`, the public multiplier evaluator,
block splitting/reassembly, prefix/suffix scalar layouts, and Flock's quirky Lagrange layout.
The multiplier build and both clients pass (2,070 jobs); both scalar-layout clients pass
(1,815 jobs). Thirty additional installed roots report only standard axioms. The clients show
that packing/opening/challenge fields need not embed into one another, distinguish a linear
observation from a ring map, and compute both sides independently at non-Boolean points.
The quirky example also distinguishes non-Boolean interpolation nodes from Boolean nodes.

All nine client files added by #1256 are native and included in routine validation. The new
packing umbrella exports only this framework-independent algebra; existing native protocol
files and their stronger/different interfaces remain separate. This finishes the PR's algebra
additions, without claiming Binius, Hachi or Flock protocol conformance. BRW26/RSG bibliography
and KB pages retain source provenance; no paper artifact or new protocol-security theorem is
implied by those references.

The new packing umbrella also builds. The combined all-client rerun encountered macOS
vnode exhaustion while rebuilding the previously passing batching client (the live count
equalled `kern.maxvnodes`, 263168). Individual successful builds are not a claim that the
combined repository gate or the full Lean migration has passed.

After the isolated batching-client retry passed (3,130 jobs), the packing umbrella and all
nine clients passed the combined build (3,197 jobs). This closes the local packing integration
gate; the full repository migration and exact-head hosted checks remain separate requirements.


PR #1257's profile-coordinate bridge is adapted to the native orientation: transposing native
rows gives native columns. Both coordinate maps are additive equivalences derived from existing
native reconstruction/additivity/atomic laws; no new profile fields or assumptions are added.
Finite tensor observations agree with the shared packing observations and slices. The carrier
cardinality is `|L|^(2^κ)`, and the upstream negative client excludes a carrier equivalent to `L`
at positive rank over a finite nontrivial `L`. The module and client pass an ordinary Lean 4.34
build (1,227 jobs). The polynomial-layout bridge and protocol algebra split remain pending.

All eight selected installed profile-bridge roots use only standard axioms. The carrier
negative client and these roots are included in routine validation.

The next native Lean 4.34 support batch repairs dependent folds and tuple casts, variable-degree
polynomial restrictions, and Sumcheck cube sums. The five modules pass the ordinary build
(3,069 jobs). Tuple proof adaptations reuse reviewed upstream main while preserving native
statements. Polynomial restrictions use public support/coefficient APIs rather than the old
internal `Finsupp` representation; their definition is now noncomputable as required by Mathlib.

The vector-support helper uses the core `LawfulMonadAttach` bind/pure implications without
requiring `ExactMonadAttach`. Its result-monad universe is generalized so the existing
OracleComp caller remains applicable. Both helper and caller pass the ordinary build
(3,096 jobs). Sixteen selected installed roots from this batch have only standard axioms.
The repository source census still has zero live proof holes and nine documented residual
axioms. The remaining protocol-specification interface errors prevent claiming the full
RingSwitching Prelude or repository migration has passed.

Finite-index sums and flattening also pass their ordinary build (1,213 jobs). Explicit dependent
rewrites and a cast/append identity preserve the native flattening and inverse laws, including
the native last-block theorem absent from current upstream. Six installed inverse, flattening,
and quotient-bound roots use only standard axioms.

The native protocol specification and oracle-reduction core now pass ordinary compilation.
A permanent client verifies query equality and finite/decidable answers through VCVio's direct
type instances after removal of the retired bundled oracle classes (3,177-job client build).
The core build passes 3,181 jobs. Transcript reconstruction proofs preserve their native
statements, and the non-adaptive verifier conversion retains its original query behavior.

Logged execution also passes ordinary compilation, after adding the now-required explicit
logging import, expressing OptionT lifting through the lawful bind/map identity, and repairing
dependent casts in one-round transcripts. The structured Sumcheck projection also compiles
with its existing degree bound. Its previous broad simplifier exposed incompatible dimension
representations; the original degree theorem applies directly without that simplification.
These execution roots are added to the routine axiom manifest. The larger RingSwitching build
reaches the security layer; no full-repository success is implied.

The security-basic target now passes (3,205 jobs). The straightline monotonicity definition
uses equivalent per-answer finite/inhabited instances and explicitly constructs the same
uniform probability interpretation previously selected implicitly. It does not add a
uniformity assumption to callers or silently use an unrelated custom oracle interpretation.

All eleven selected compiled protocol/execution roots pass the axiom audit: ten use only
standard axioms and the non-adaptive verifier conversion uses none. Two audit attempts hit
the macOS system open-file limit; the separate retry passed. The changed-source forbidden-token
check, repository zero-hole census, imports, docs and KB checks pass. A concurrent full-source
forbidden-token scan encountered the same system limit, so its incomplete run is not a pass.

Round-by-round security now passes ordinary compilation on Lean 4.34. Its finite union bounds,
failure-monotone trailing bind, and heterogeneous event comparison use VCVio's separate
`MonadAttach`, SPMF lift, lawful lift and distribution-compatibility interfaces in place of the
retired `HasEvalSPMF` bundle. No exact-support or additional security hypothesis is introduced.
The OptionT success event still excludes failure, and the one-shot extractor conversion keeps
its existing monotonicity requirement. The identity oracle-verifier knowledge theorem retains
its zero error. The broader build has advanced to RingSwitching Prelude itself.

All eight selected installed round-by-round roots use only standard axioms. They are included
in the routine axiom manifest. The changed-source forbidden-token check and docs checks pass.

Older PRs #458 and #465 are covered by native source rather than copied over it. At the reviewed
#458 head, the permutation constructor and copy-constraint product theorem are already present
natively; native SendWitness also has actual knowledge-soundness and oracle-completeness proofs
where the donor retains admissions or `True` placeholders. #465's constraint-system abstraction
and examples match byte-for-byte, while native Plonk additionally implements its admitted
permutation. The PR manifest records exact source evidence. These dispositions establish source
coverage, not a claim that the entire Plonk/SendWitness dependency cone builds on Lean 4.34.

PR #459 is likewise source-covered: both Plonk checking protocols and perfect-completeness
results exist natively, with additional verifier-support, soundness and knowledge-soundness
proofs. Native namespace repairs and generated-file ownership are preserved. This records the
comparison of all four Lean source files, not a completed build of that protocol cone.

RingSwitching Prelude now passes both its direct check and the ordinary build (3,236 jobs).
The OptionT simulation law is imported explicitly, and the polynomial currying proofs use
Mathlib's public `sumAlgEquiv` generator identities rather than an obsolete definitional equality
to `sumToIter`. Existing theorem statements and profile orientation are preserved.

A fresh 2026-10-07 upstream read lists 54 open ArkLib PRs, including drafts. New PRs #1290,
#1291 and #1293 and changed heads for #1289 and #1266 are fetched and pinned in the inventory.
Earlier reviewed heads remain recorded; `latest_refresh` stores changed revisions separately.
Both ArkLib main and the public prize main remain at the previously recorded commits. Fetching
these revisions does not establish native integration or validation of their results.

Six selected installed Prelude roots pass the standard-axiom audit, including simulation of
message queries, polynomial evaluation under currying, variable fixing, round transition and
row decomposition. They are included in the routine axiom manifest.

PR #1257's polynomial-layout bridge now connects native `packMLE` and `unpackMLE` to the
independent basis-packing API. It proves both round trips, the packed-prefix interpretation,
and equality-weighted evaluation reconstruction. The source-dimension cast and native
prefix/suffix orientation are explicit. The native Prelude supplies the existing definitions;
this transfer adds no profile fields or security hypotheses.

The direct Lean 4.34 check and ordinary 3,242-job build pass. The module is explicitly included
in routine validation because the generated campaign umbrella does not include every protocol
module. The remaining protocol algebra split and protocol integrations are still pending.

All seven installed polynomial-layout theorem roots use only standard axioms and are included
in the routine flagship audit.

PR #1291's STIR parameter corrections are adapted to the native statements. A smooth domain
must have cardinality strictly larger than the degree, and the repetition bound uses the next
round's degree for transitions only. The last round's repetition parameter is unconstrained.
The new `degree_zero` lemma connects the folded-degree function to the initial degree.

The parameter client constructs a consistent zero-transition instance over `ZMod 5`, with a
four-point smooth domain, degree two and final repetition count 100. It proves that the old
reversed domain inequality makes the proximity range empty, and rejects both that inequality
and a non-power-of-two degree. Its direct check and ordinary 3,620-job build pass on Lean 4.34.
The client is included in routine validation.

The donor's three admitted theorem bodies are not imported: native `stir_main`,
`stir_rbr_soundness` and `proximity_gap` remain statement definitions with separately documented
conditional proof routes. Further #1291 work remains on degree-zero boundary tests, error-budget
arguments, the strict soundness relation and the main theorem's quantifier/complexity statement.

Five installed parameter-lemma and client roots use only standard axioms; all are included in
the flagship audit.

The #1291 proximity-gap boundary tests now pass their ordinary Lean 4.34 build (3,540 jobs).
They prove the one-word case, reject the former free-generator counterexample under the pinned
power generator, and establish counterexamples at the excluded proximity boundary and at degree
zero. The native statement therefore now explicitly requires positive degree. It remains a
statement definition; its general existence conclusion is not asserted as a proved theorem.

Two upstream nearest-codeword polynomial helpers are added to native Quotienting. They expose
polynomial witnesses realizing absolute and relative distance to a Reed–Solomon code. The tests
use the current native polynomial-membership API and the pinned VCVio uniform-sampling laws.
All nine selected installed helper, boundary-test and conclusion-equivalence roots use only
standard axioms, and the test module and roots are registered for routine validation.

Four support modules also pass an ordinary 3,664-job build: BCIKS20 GoodCoeffs now uses explicit
evaluation and submatrix identities, WHIR BlockRelDistance uses the current nonnegativity API,
the empty oracle uses pointwise inhabited ranges, and the declaration-free SimOracle support
file imports only the query-implementation API. Four selected BCIKS20/WHIR roots pass installed
standard-axiom audits. The broader STIR completeness migration and #1291 budget/statement
corrections remain in progress.

The simulation compatibility layer now passes an ordinary Lean 4.34 build alongside BCIKS20
JointAgreement (3,737 jobs). Retired bundled oracle instances become pointwise range instances;
uniform finite-answer semantics are derived locally. Probability-support loop laws are derived
from distribution compatibility, without requiring an extra exact-support assumption. The generic
vector support equivalence uses the current exact-support interface. Transformer and query-lift
proofs use explicit run/lift identities where required by the newer elaborator.

WHIR's ten typed transcript payload constructors now explicitly unfold their slot lengths.
Their ordinary build passes 3,654 jobs. Ten installed simulation/JointAgreement roots and all ten
payload constructors use only standard axioms and are registered for routine auditing. No source
admissions or custom axioms are added. The broader completeness and sequential-append migrations
still have source errors, so these passes do not establish the full STIR or repository build.

The generic completeness module now passes its ordinary Lean 4.34 build (3,228 jobs).
The finite uniform interpretation is activated locally from the simulation compatibility layer;
query-lift support and optional-transformer membership use explicit current API identities.
The zero-, one-, two- and general-message completeness characterizations retain their conclusions.
The PMF bridge hypotheses use `evalSPMF`, the renamed legacy evaluator, rather than the new
measure-valued `evalDist`. Eleven selected installed completeness, unrolling and PMF roots have
standard-only axiom closures and are registered for routine auditing. Sequential composition and
the downstream STIR completeness consumers remain unvalidated.

Sequential composition now passes the ordinary Lean 4.34 build (3,217 jobs). The migration makes
transcript casts at the protocol boundary explicit, replaces obsolete nested-lift proof steps
with the current direct-lift congruence, and proves lift composition where definitional equality
no longer suffices. Existing statement assumptions are preserved. Eleven installed roots use
only standard axioms, including the round-by-round extractor and verifier-state constructors,
threaded round identities, and the message-first appended-run theorem. General `append_run`
retains its existing right-block residual hypothesis; this validation does not discharge it for
all protocols. The downstream STIR build remains in progress.

Unique decoding, general sequential composition and the challenge-seam bridge now pass their
ordinary Lean 4.34 build (3,751 jobs). Explicit singleton sums and filter membership restore the
zero-degree curve case. The sequential completeness induction keeps its original assumptions;
the bridge preserves public lemma names while using the legacy evaluator's current `evalSPMF`
name. A private stateful simulation congruence is proved by OracleComp induction, adapted from
Apache-licensed VCVio `SimSemantics/StateT/Basic.lean` at
`576766ab24a044af560b05c58d2a1229857c7c07`. Fifteen selected installed roots have standard-only
axiom closures and are registered for routine auditing. The broader STIR build remains in
progress; these checks do not establish a full repository pass.

The BCIKS20 curve module passes its ordinary build (3,548 jobs) after explicitly unfolding
the coordinate interpolant in the degree proof. Its two pre-existing large-agreement axioms
remain unchanged. The distributional bind-commutation helper also builds as an installed
STIR dependency, and both exported roots have standard-only axiom closures. It now reuses
VCVio's independent-draw swap theorem and imports only the evaluator modules, removing the
whole-VCVio dependency from these STIR composition paths. The broader STIR attempt encountered
macOS file-table exhaustion and artifact-write failures, plus an unported challenge-finiteness
interface; it is not a successful STIR or repository validation.

PR #818's polynomial line-restriction and layered-circuit foundations are imported unchanged
from `4dc5142fdcca586ae499cd9d1b1d6dd4b48c8fce`, preserving authorship and Apache licensing.
The polynomial library proves evaluation along the line and the multilinear degree bound;
the circuit library relates successive layers and the circuit's input/output evaluations.
Both modules pass ordinary Lean 4.34 compilation, alongside the challenge-oracle instance
migration (3,221 jobs). All nineteen selected installed roots use only standard axioms.
The challenge helpers now construct pointwise answer-type instances, retaining their names
and finite/inhabited requirements. All nineteen roots are registered in routine validation.
The generated prize umbrella is unchanged, since these modules are outside its import surface.

This is not yet the full GKR protocol transfer: its Sumcheck, context-lifting and sequential
composition consumers still require integration with the native framework. The donor's final
completeness proof inherits admitted upstream framework dependencies; it must be adapted to
native proved or explicitly conditional routes before claiming full completeness.

PR #466's Clean adapter was also reviewed. It would connect an external `FormalCircuit` to
the existing native constraint-system interface, but the native dependency set has no Clean
package. The donor pins a Lean 4.28-era Clean revision, so copying its lockfile is not suitable
for this Lean 4.34 migration. Its completeness construction additionally assumes witness
environment existence (`hWitGen`); the adapter does not prove that obligation. A compatible
Clean dependency and adapter validation remain pending.

Run unrolling and its distributional seam laws now pass an ordinary Lean 4.34 build
(3,207 jobs). The migration retains public theorem names and their assumptions while replacing
the legacy evaluator calls and notation with `evalSPMF` / `𝒮`. Explicit state-transformer
identities restore challenge-state preservation and marginal equality. All thirty installed
roots printed by the module have standard-only axiom closures and are registered for routine
auditing, including completeness unrolling, challenge coherence, state-preserving simulation,
short-circuit commutation and the seam union bound. These laws do not by themselves establish
full STIR completeness or discharge arbitrary state-preservation assumptions.

Distributional append factoring now passes its ordinary Lean 4.34 build (3,220 jobs), and
all thirteen exported theorem/lemma roots have standard-only installed axiom closures.
The port replaces retired bundled oracle instances with pointwise answer instances and derives
the same finite uniform semantics locally. It normalizes direct lifts at the challenge seam
and collapses both nested output lifts with proved composition identities. In particular,
`appendRunRightDistResidual_holds` and the challenge-first `append_run_evalDist_challenge`
are validated. These are equalities of distributions; they do not assert the false general
syntactic ordering equality. Public names and statement assumptions are retained.

STIR's combination module now passes its ordinary Lean 4.34 build, together with the
append-completeness interface file (3,766 jobs). The proof repair makes block disjointness
arithmetic explicit, unfolds the geometric-sum definition before case splitting, and constructs
filter membership explicitly. All six selected installed combination roots have standard-only
axiom closures and are registered for routine auditing. The existing strict coefficient
residual in the general combination theorem is retained; the small-field corollaries retain
their stated regime restrictions. The message-first completeness proof remains in migration.

Message-first sequential completeness passes its ordinary Lean 4.34 build (3,234 jobs).
The port uses pointwise finite/inhabited answer types and an explicit local uniform
interpretation. Seven challenge-query support steps use the current query representation;
optional-transformer support is transported explicitly. The three installed completeness
roots use only standard axioms. The prover/verifier support reconstruction helper also
builds and has a standard-only installed axiom closure. All four roots are registered for
routine auditing. Initialization, support-faithfulness and message-seam assumptions remain
unchanged. The separate public wrapper is being simplified to reuse this theorem; its
remaining helper migration is not included in this validation.

The public message-seam completeness wrapper now also passes its ordinary Lean 4.34 build
(3,238 jobs) and a seven-root installed axiom audit. All seven roots use only standard axioms
and are registered in routine validation. The public completeness theorem delegates to the
validated message-first theorem, removing its duplicate support/probability proof while
preserving the statement and hypotheses. Its optional-transformer lift and failure-support
helpers are migrated to the current API. Empty-tail completeness and further soundness
consumers remain under validation.

Prover seam decomposition passes its ordinary Lean 4.34 build (3,219 jobs). All 35 exported
theorems have standard-only installed axiom closures and are registered for routine auditing.
The repair proves nested-lift collapse using query coherence, transports send/receive steps
through the current lift operation, and makes the initial-state projection explicit. Existing
seam direction and state hypotheses remain unchanged. This validates decomposition and
reassembly; it does not by itself discharge downstream soundness or STIR obligations.

Empty-tail completeness now passes its ordinary Lean 4.34 build (3,239 jobs). The shared
support-decomposition proof is exposed as `append_perfectCompleteness_of_run_factor`;
the existing message and empty-tail theorems discharge its factoring hypothesis with their
proved run identities. Both retain their original mathematical hypotheses. This removes
another duplicated proof instead of maintaining separate support calculations. The soundness
seam-transfer module also builds with the legacy evaluator explicitly named `evalSPMF` and
lift coherence derived from the proved composition identity. All ten selected installed
completeness/transfer roots have standard-only axiom closures; the six new roots are added
to routine auditing. Initial validation attempts hit macOS file-table exhaustion; the final
empty-tail build and installed audit passed. Full STIR and full-repository builds remain pending.

ArkLib PR #1287 (head `3323359736dd521ee77073ebdaa89057822839f9`) contributes the
Hachi coefficient-packing layer. Its inverse matrix reshape and round-trip/evaluation proofs
are added to native `PolynomialEvalSplit`, preserving the existing additivity/scalar lemmas.
The computable monomial and Lagrange evaluators are connected to Mathlib polynomial evaluation;
coefficient packing/unpacking, evaluation reconstruction and the shared scalar claim layout
are imported, with `PackingData.ofBaseOpening` for the one-coordinate opening algebra.
The native Lean 4.34 build passes 1,873 jobs; twenty selected installed declarations have
standard-only axiom closures and are registered for routine auditing. Module-mode wrappers
are removed and the existing native split-module path is reused. The generated prize umbrella
is unchanged. This is a partial protocol transfer: cyclotomic trace coordinates, the trace-head
protocol and its completeness/committed-opening/conformance consumers remain to be integrated.

The oracle-reduction message-seam completeness interface passes its ordinary Lean 4.34
build (3,239 jobs) and four-root installed audit with standard-only axioms. Retired bundled
oracle instances are replaced by pointwise finite/inhabited response types, including omitted
section hypotheses. The existing verifier-factorization residual is retained explicitly;
this bridge does not claim to discharge that separate obligation. Its three theorem roots
and residual definition are registered for routine auditing.

Non-perfect message-seam completeness now passes its ordinary Lean 4.34 build (3,241 jobs).
The port replaces retired bundled oracle instances and names the legacy distribution evaluator
`evalSPMF` explicitly in the two game-bridge hypotheses. Both installed theorem roots have
standard-only axiom closures and are registered for routine auditing. Existing distributional
factoring, stage-bridge and state-preservation hypotheses remain explicit. The unchanged
`SeamCompleteness` dependency also passed direct and ordinary compilation; this does not yet
validate all downstream challenge-seam or STIR consumers.

The univariate CompPoly compatibility module now builds on the pinned dependency revision.
Eight duplicate declarations already supplied by CompPoly are removed; their public names
remain available through the existing imports. The local monic division and remainder bridges
are preserved. Their proof uses a single recursive-step rewrite and direct algebra, avoiding
an unnecessary definitional-equality expansion; zero-polynomial transport is explicit. The
module built successfully in the Hachi dependency build, and all twelve selected installed
API roots (eight upstream replacements and four local theorems) use only standard axioms.
The encompassing Hachi coordinate build subsequently failed opening a Mathlib artifact due to
macOS file-table exhaustion, so full coordinate validation is not claimed here.

Message-seam game factoring passes its ordinary Lean 4.34 build (3,242 jobs). The port
replaces retired oracle instance bundles and legacy evaluator references. All five selected
installed roots use only standard axioms, including natural run factoring, the two phase-game
constructors and the completeness theorem using seam factoring. They are registered for
routine auditing. State preservation and the phase-one simulation bridge remain explicit
hypotheses. Challenge-first factoring and full STIR validation remain pending.

PR #848's Section 6 capstones were reviewed at
`1c5c5bd7ed9d4a6407974a12ff95893fbdbc02bb`. The native duplex-sponge `Soundness` file
contains documentation without the capstone declarations; `KnowledgeSoundness` is absent.
The donor soundness proof assumes an explicit `KeyLemmaSecurityWitness` and coin-bearing
state-restoration soundness. Its knowledge theorem supplies one extractor across budgets,
but extraction may use randomness and oracle queries and receives both prover and verifier
logs. It does not prove the deterministic prover-log-only Definition 3.6 contract or an
extraction-time bound. These are useful missing results; importing them requires the key-lemma
witness interface, single-salt coin/extractor semantics, query-log transports and normalization
helpers. This review records the transfer requirements, not a native compilation result.

Challenge-first sequential game factoring passes its ordinary Lean 4.34 build (3,245 jobs)
and all four exported theorem roots have standard-only installed axiom closures. The migration
uses pointwise oracle instances and the explicit legacy `evalSPMF` evaluator. It normalizes
both nested output lifts via proved query coherence and closes the transcript/output equality
explicitly. Completeness and soundness factoring preserve the existing state-preservation and
simulation hypotheses. The result remains distributional: it does not assert the false general
syntactic reordering of a challenge and a prover output. All four roots are registered for
routine auditing; downstream perfect-completeness and full STIR validation remain pending.

The STIR fold-round completeness module passes a focused Lean 4.34 source check, with
all five printed theorem closures using only standard axioms. The port uses pointwise
oracle instances, a local finite-uniform interpretation, and an explicit universe for the
empty oracle specification. It preserves the non-failing initialization assumption and
proves the original input/output relation through the single-codeword combination identity.
This is a focused result; the full migration build still has downstream compatibility failures.


The seam-support and message-soundness modules pass Lean 4.34 compilation: the support build
completed 3,247 jobs, and the joint message-soundness/Hachi build completed 3,641 jobs.
All fifteen selected installed soundness/support declarations have standard-only axiom closures.
The port preserves message-seam, state-preservation, never-failure and value-distribution
hypotheses. The generic optional-transformer event lemma now uses the current lawful SPMF-lift
interface. Query-lift transitivity is proved through the common lift-composition theorem.

PR #1287's cyclotomic trace coordinates are now adapted at
`3323359736dd521ee77073ebdaa89057822839f9`. The transfer adds the linear packing map and
equivalence, cancellation of the unit trace scale, and the binary coefficient equivalence.
The trace check is proved equivalent to a coefficient inner product and then to evaluation
of the decoded scalar polynomial. Three obsolete simplification steps in native trace-vanishing
proofs were removed. The joint build completed 3,641 jobs; all twenty selected installed roots
(eleven new coordinate/substrate declarations and nine trace-vanishing theorems) have
standard-only axiom closures. They are registered for routine auditing. Full trace-head protocol,
completeness, committed-opening and conformance integration remain pending.


The [October 8 refresh](../upstream/arklib-prs-2026-10-08.json) records all 55 open PRs,
including drafts. Exact heads were fetched for new PRs #1294–#1296 and updated PRs #1293,
#1289, #1268, #1267, #1266, #1264, #1263 and #1261. Upstream main is now
`745e77939ac4cecf0333af8410a2463c5c7cb655`, incorporating #1259 and #1260 since the
prior main snapshot. Both merged PRs were already adapted and validated from their PR heads
on October 7. Comparing all four affected source/client files finds the same declaration
inventory; native elaboration repairs are retained. The eleven new or changed open-PR heads
remain pending substantive review. The older inventory retains detailed transfer evidence
for its reviewed revisions.


Challenge-seam perfect and error-ful completeness now pass an ordinary Lean 4.34 build
(3,251 jobs). All fourteen exported declarations across `AppendSeamBridges` and
`AppendPerfectCompletenessChallenge` have standard-only installed axiom closures and are
registered for auditing. The migration uses pointwise oracle answer instances, explicit
SPMF evaluation, proved query-lift composition and explicit unfolding of the success
predicate. Existing completeness, state and sampling hypotheses are preserved. The broader
six-target STIR build is the next validation gate; these focused results do not prove it.

The monic-quotient linearity compatibility module now imports the five declarations supplied
by the pinned Mathlib dependency instead of redeclaring them. The existing ArkLib import path
is retained. The import-only module passes a focused Lean 4.34 check; downstream research
clients still require the full integration build.

The subset-spectrum total-mass module passes Lean 4.34 compilation against an isolated build
of its unchanged closed-form prerequisite. Its printed theorem closures use only standard
axioms. The port uses the current binomial-coefficient lemma and makes the natural-number
subtraction bounds explicit. In filter proofs, simplify membership before unfolding a
predicate with its own decidability instance, then use `change` to state the arithmetic
predicate explicitly; unfolding both together can expose list-filter implementation terms.
This focused result does not replace full repository compilation and auditing.


The new #1294–#1296 sequence supplies a useful missing route for guarded round-by-round
knowledge composition. #1294 relocates the guard interface; #1295 proves binary and iterated
composition for worst-case component bounds. The first verifier must return a deterministic
verdict when its check passes and abort otherwise. The composed knowledge state retains that
check after the seam, preventing a rejected first transcript from passing via a fallback verdict.
#1296 uses this route for the full ring-switching composite under an explicit
`MLIOPCS.RbrKnowledgeSoundWorstCase` hypothesis and a functional opening relation. Its older
averaged-only capstone still uses admitted arbitrary-verifier composition and carries `sorryAx`.
The new proved route does not discharge that older contract. Native adaptation requires the
worst-case security API, guarded composition and phase modules, plus validation of the intended
downstream opening witness. This is a source review, not a native build claim.


Message-first n-ary sequential completeness now builds on Lean 4.34. The ordinary adapter
build compiled `SeqComposeMsgCompleteness` successfully in 14 seconds; that joint run later
failed in `AppendOracleAdapters`, so no adapter result is claimed here. All eight installed
exports (six theorems and two challenge-instance constructors) have standard-only axiom
closures. Retired oracle bundles are replaced with pointwise instances, and the empty-chain
base case directly uses identity completeness instead of simplifying its definition. The
message/empty-tail shape conditions and component completeness hypotheses are unchanged.


Randomized state-restoration support from #1267 (`6c26172f0c11d3ef97fcedd1461034e46889b949`)
and randomized knowledge security from #1268 (`ce1e20b3d3c2bb2934bb0beebee00f43e7c347f4`)
now build natively on Lean 4.34 (3,278 jobs). Five local support modules backport logged runs,
finite-key/cache transports and expected distinct-query charges from VCVio
`e417e35ac452c3994173eda268a8eee0d26115d2`, retaining the existing dependency pin.
The model retains the joint output, ordered query log and final cache, including when selection
returns `none`. Bounds charge actual distinct cached queries; the infinite-key argument uses
finite execution support rather than sampling an infinite uniform table. Extraction and
component-security hypotheses remain explicit. All 129 selected installed declarations
(59 support and 70 protocol exports) have standard-only axiom closures and are registered
for routine auditing. The separate source-composed checks are supplementary evidence.
Other #1267 changes, including its Ajtai integration, remain under review.

The STIR round-completeness and sequential oracle-adapter modules also pass ordinary Lean 4.34
builds (3,764 and 3,254 jobs). Their seventeen selected installed roots have standard-only
axiom closures. Repairs use pointwise oracle instances, explicit empty-oracle universes and
current optional-transformer simulation laws. Completeness and security hypotheses remain
unchanged. The broader six-target STIR build still has downstream migration failures and is
not certified by these focused results.

The pinned Lean 4.32.2 reference upper candidate now passes its complete ordinary build
(3,906 jobs). Candidate axiom auditing and fresh dependency-closure replay are separate gates;
this build alone does not establish them, native campaign completion or hosted ranking.


STIR initial/final boundary-block completeness and threaded message-seam composition now
compile as separate modules on Lean 4.34 (7.2 and 4.9 seconds in the broader build).
Their three installed theorem roots have standard-only axiom closures. The port uses
pointwise challenge instances, explicit empty-oracle universes and current simulation laws;
the empty composition uses identity completeness directly. Existing relation, sampling and
component completeness hypotheses are retained. The joint STIR build still fails in later
modules, which remain under migration.


Focused review rechecked all eleven randomized restoration and STIR/composition modules
from the latest donor commits under Lean 4.34. All 149 selected installed declarations
have standard-only axiom closures; the checked source matches the donor cache source.
The integration retains the previous audit roots while adding the new declarations.

A further compatibility batch checks closed period-profile arithmetic in the kernel,
normalizes the small totient explicitly, imports the complex primitive-character module,
and repairs function, quotient and finite-set coercions without changing theorem statements.
Seven full modules pass focused compilation. Five other edited modules cannot yet be
checked locally because prerequisite artifacts are missing; isolated cyclotomic numeric
checks pass but do not certify that full module. Full hosted migration validation remains
required.
The pinned upper candidate now passes fresh replay on Lean 4.32.2: all 38,274 declarations
in its complete dependency closure are present in the fresh kernel environment, and all
quotient declarations match the originals. Its candidate, score and integer certificate also
pass the standard-axiom audit. The reproducible `replay-upper` command imports the pinned
compiled candidate, checks the axiom whitelist, rejects unsafe/partial dependencies and
replays the closure into an empty environment. Post-checks use the kernel environment directly;
the higher-level environment interface can hide private declarations and produce false
missing-name reports. This is local verification of the exact pinned upper benchmark,
not a hosted ranking result or completion of the native production proximity-gap conjecture.
The lower candidate remains under compilation and requires its own audit and replay.

The integration review independently reproduced the pinned upper-candidate replay:
38,274 declarations were exported and the fresh kernel check passed on Lean 4.32.2.
It also verified every path and SHA-256 in the refreshed 923-file upstream inventory
against the pinned Git objects and its stated native comparison commit.

A further Lean 4.34 compatibility batch repairs finite-set membership, pointwise function
computation, polynomial evaluation imports, and definitional-equality boundaries. Thirteen
complete edited modules pass focused checks. Twenty other edited modules still lack local
prerequisite artifacts. Closed moderate arithmetic uses kernel computation; larger primality
proofs retain `norm_num` with a recursion limit scoped to the affected declaration, avoiding
expensive direct trial-division reduction. A standalone check verifies the `4294967377` prime
certificate, but does not replace the missing full-module check. These results do not certify
the full migration; known follow-up diagnostics and exact-head hosted validation remain open.

Threaded n-ary oracle completeness now compiles as an ordinary Lean 4.34 module (20 seconds).
Its three installed theorem roots have standard-only axiom closures and are registered for
routine auditing. Only the retired ambient oracle bundles and matching `omit` clause change
to pointwise instances; the theorem hypotheses and composition proof remain intact.
The joint Ajtai build failed independently in its lattice norm dependency, whose migration
is still under repair. Refreshed #1266 has identical knowledge-base content to its reviewed
prior revision, so the earlier decision to regenerate native indices remains applicable.


The next #1291 budget corrections now compile with native STIR front-door, assembled and
checking-IOP clients. Folding errors use `foldingParam`; the shift term passes
`repeatParam + s` into `proximityError`, rather than adding `s` to its returned error.
The final error bound sits outside the transition quantifier, so it is still required when
`M = 0`; a concrete regression theorem checks that case. The five budget/regression audit
roots, all 49 checking-verifier exports, seven assembled-protocol roots and three round-three
completeness roots have standard-only installed axiom closures. These modules compile
ordinarily; the joint build still failed in vector-chain completeness, whose separate repair
is under validation. The port preserves existing explicit soundness residuals. #1291's stricter
soundness relation and uniform main-theorem quantifiers/complexity remain under review.
No donor admitted theorem has been substituted for a proof.


The focused six-target STIR build now passes completely (3,826 jobs), including vector-chain
completeness and the error-budget regression. All eleven selected installed vector-chain
roots have standard-only axiom closures and are registered for auditing. The chain migration
uses pointwise oracle instances, explicit empty-oracle universes and current failure-probability
lemmas, preserving component completeness and sampling hypotheses. This focused build does
not replace the full native/Research validation, which is running separately.

Refreshed #1263 (`70f23f721672995b61c6e900c4300948f2f60294`) and #1264
(`eb9bfaf9ff2bfb2305ee239ac94f7e02a904de0f`) remove elaboration-option workarounds in
three restoration modules through explicit proof steps. Both concrete clients and the
randomized downstream modules compile after the cleanup. A fresh installed audit of all
129 randomized support/protocol roots and 19 base/client roots still finds only standard
axioms. The actual experiments and explicit extraction assumptions are unchanged. The
joint build's independent Ajtai failure is being repaired; it does not invalidate the
successful restoration module builds and installed audits.

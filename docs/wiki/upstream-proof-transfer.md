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

`external/arklib` pins upstream main at
[`35ddcaa83f683011f944f58904be779495a5709a`](https://github.com/Verified-zkEVM/ArkLib/tree/35ddcaa83f683011f944f58904be779495a5709a).
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

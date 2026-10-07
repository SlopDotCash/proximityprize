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
`d7089e46d69e07640fa23b5ae6b1b966f1d4b949`, and PolyFun
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

This is also a dependency for PR #792's Johnson witness constructor. Its other
generic witness wrappers overlap our existing Research constructors. The unique-
decoding/interleaving lemmas and adapted witness constructors remain to be
integrated; upstream's whole grand-challenge module must not replace our distinct
Research resolution definitions merely because some declaration names coincide.

The mechanical migration also removes the obsolete explicit placeholder from
`zero_le _` across 96 remaining library/Research files (150 applications/comments),
matching Mathlib's now-implicit argument. This is a proof-API edit; the statements
and existing conditional premises are unchanged. Whole-tree validation remains
pending. Additional direct checks pass for the ball-intersection translation,
Lam–Leung independence, combinatorial probability, chord census, root-height,
Gauss-sum norm, and subgroup-sumset repairs. The Gauss-sum file now reuses Mathlib's
conjugation lemma, and an unusable hypothesis-dependent instance is exposed as an
explicit theorem.

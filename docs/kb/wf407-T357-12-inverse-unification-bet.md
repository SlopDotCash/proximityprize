# wf407 / T357-12-inverse — the inverse-theorem unification bet: single-orbit test negative; bet NOT refuted

**Date:** 2026-06-14 · **Verdict (corrected 2026-10-28 audit, T128): unresolved.** A
single-rotation-orbit structure test came out negative on small hill-climbed lists, and the
tool assessment raised real concerns, but neither axis refutes the bet: no precise
structured-cover predicate was stated or tested, the search maxima are lower bounds, and the
Axis-2 parameter calculation conflated density, doubling and list agreement and misstated the
budget and the cited theorem. Corrections are inline below. No fabricated closure, and no
universal method no-go.

## The bet (357-T12 / 334-T07, ranked #8 in `UNFINISHED_THREADS_407.md` §(d))

"Every ε*-bad family for δ* lives on coset/orbit (affine-subgroup) structure. If any ε*-bad
stack is poly(1/ε)-covered by affine-subgroup-structured families, δ* stops being analytic and
becomes a FINITE ENUMERATION; import Bogolyubov-Ruzsa/Sanders to close it." Three sub-tasks:
(1) catalogue all known bad families & verify each lives on coset/orbit structure; (2) state the
structure conjecture as a Lean Prop; (3) assess whether Sanders' quantitative B-R is strong
enough at prize parameters.

## Assessment on two axes (original "each independently fatal" verdict withdrawn)

### Axis 1 — the best-found lists are not covered by one rotation orbit (a narrow test)

The catalogue splits into two radius regimes, and the bet conflates them:

- **Johnson regime (the LOWER-bound / ceiling families):** O137/O138 (DISPROOF_LOG) showed the
  *extremal lower-bound* family at exactly-solved instances IS the twisted-monomial orbit of the
  KKH26 stack (`ε_mca` attained on the orbit; census = `−{subset sums}`). So the *known
  counterexample/ceiling* families (CS25, KK25, KKH26, prime-field) genuinely live on coset/orbit
  structure. The bet's catalogue claim is TRUE — but only for the ceiling, not the binding object.

- **Window-interior regime (the BINDING worst case that actually pins δ*):** the object that
  determines δ* is the *maximum* list / densest bad cluster, not the algebraic ceiling family.
  `probe wf407_T357-12-inverse_unification.py` (each word's list computed exactly; the maximum
  over words found by hill-climbing; proper subgroups = prize shape):

  | p | n | k | radius δ | best coset/power-word list | hill-climb best found (lower bound) | share of best-found list in the largest single rotation orbit |
  |---|---|---|---|---|---|---|
  | 17 | 8 | 2 | 0.625 | 2 | **≥ 7** | 0.14 |
  | 41 | 8 | 2 | 0.625 | 2 | **≥ 7** | 0.14 |
  | 97 | 16 | 2 | 0.500 | 4 | **≥ 6** | 0.17 |

  The hill-climbed words beat every coset/power-word construction tried, and each best-found
  list has only a 14–17% share in its **largest single** rotation orbit. The "≥" entries are search
  lower bounds: without exhaustive enumeration over words or a global upper certificate they are
  not the true maximum (compare T127). This is consistent with DISPROOF_LOG O161/O162/O163
  ("H-MAX is a combinatorial densest codeword cluster, NOT the algebraic power-word fibre").

  Radius sweep (`/tmp/johnson_boundary.py`, not retained in-tree; p=17,n=8,k=2): at δ=0.625 the
  best-found list (7) exceeds the coset construction (2); at δ≤0.375 lists are 0–1.

  **Conclusion (axis 1, corrected):** a single-orbit test is not a test of the bet's actual
  hypothesis. "Poly(1/ε)-covered by affine-subgroup-structured families" allows a union of
  polynomially many orbits, translated progressions, or other structured families; a 14–17%
  share in one orbit says nothing about such unions. What the data show is narrower: at these
  small cells the best-found lists are not single orbits and are not reached by the
  coset/power-word constructions tried. To test the bet, one must first state the structured-cover
  predicate precisely (which families, how many, which group action, which ε-budget) and then test
  that predicate, ideally on exhaustively certified worst lists. This does not assert that a
  polynomial cover theorem holds for actual prize stacks either.

### Axis 2 — the Sanders / Bogolyubov–Ruzsa tool: hypotheses and budget not yet matched

**Corrected 2026-10-28 (T128; evidence
`docs/audits/repository-review-2026-10-28/kb43-structure-cover-scope-check.json`).** The
original text made three separate inferential errors; the tool question is open, not walled.

- **The cited theorem.** Sanders, "On the Bogolyubov–Ruzsa lemma" (Anal. PDE 5 (2012),
  Theorem 1.1): for a finite set `A` in an abelian group with `|A+A| ≤ K|A|`, the difference
  sumset `2A−2A` contains a large coset progression whose dimension is bounded by a power of
  `log(2K)` (statement checked; the proof was not re-audited). It is **not** the statement "A is
  covered by subspace translates with rank `K·polylog K`", nor directly a covering of `A`.
  Deducing a cover of `A` needs a further covering argument (e.g. Ruzsa covering) with its own
  count of translates; the group, theorem, deduction and constants must all be stated before
  judging the tool at prize parameters.
- **Density is not doubling.** Thinness `|A|/|G| = ε` does not fix the doubling `K`. In `F_101`,
  `A = {0,1,2,3}` has density `4/101` but doubling `|A+A|/|A| = 7/4`, not `101/4`. So "K = 1/ε* =
  2¹²⁸" does not follow.
- **Low pairwise agreement is not Sidon.** Pairwise codeword agreement `≤ 1` does not make a set
  of codewords Sidon or high-doubling: the whole dimension-2 RS code over `F_17` has pairwise
  agreement `≤ 1`, yet it is an additive group with doubling `1`. (This only refutes the
  inference from pairwise agreement; the doubling of the specific best-found lists was not
  measured and is unretained.) Whether the relevant bad set has small doubling — and which set
  (bad scalars, or the agreeing codewords) is the right carrier — remains to be determined.
- **The budget.** At `ε* = 2⁻¹²⁸`, a polynomial in `1/ε*` such as `(1/ε*)³` has `log₂ = 384`;
  `log₂(128³) ≈ 21` is the logarithm of a polynomial in `log₂(1/ε*)`, a different (much smaller)
  complexity target. The note's "gap ≈ 2¹²⁸" compared mismatched quantities. And even a very
  large finite enumeration is still finite; the issue is cost, not finiteness.

The original "premise and tool are mutually exclusive" claim is withdrawn: it relied on the
Sidon inference above. A heuristic tension remains plausible — a bad family far from any
structured family would need to be shown to have large doubling for the tool to fail — but
that is unproved here.

## Where this lands relative to the named walls

Heuristically, the bet points at the **same wall the whole campaign bottoms out at**: the
explicit-smooth-RS sub-Johnson list-decoding bound / additive-energy core (W2-adjacent, the
`E_Fp(μ_n)=n^{2+o(1)}` Shkredov open problem). O162 records "H-MAX, the subset-sum fibre supply,
and `E=O(n²)` are the SAME irreducible core." Whether the inverse-theorem route needs that same
energy/structure input is plausible but not shown here; it is not a proved circularity.

## Artifacts

- `scripts/probes/wf407_T357-12-inverse_unification.py` — axis-1 exact per-word lists with a
  hill-climbed maximum + single-orbit share of the best-found list + the original axis-2
  computation (superseded by the corrections above: its K = 1/ε, rank `K·polylog K` and
  `log₂(128³)` budget, and Sidon inference are not valid).
- `/tmp/johnson_boundary.py` — radius sweep locating the structured/unstructured boundary
  (reproduce in-tree as a probe if desired).

## What remains (honest)

This route is **not** a clean kill. Retained: the finite best-found list witnesses (≥ 7, ≥ 7, ≥ 6)
and their small single-orbit shares. Open: (1) state the structured-cover predicate precisely and
test it (unions of polynomially many orbits / progressions, not one orbit), on exhaustively
certified worst lists where feasible; (2) identify the carrier set and measure or bound its
doubling; (3) state the exact inverse theorem, covering deduction and constants, and compare with
a correctly stated budget (polynomial in `1/ε*` versus polylogarithmic); (4) the realization /
transfer step from a structured cover to a δ* enumeration, which is genuinely unproved. The
explicit-smooth-RS beyond-Johnson worst-case list bound remains the open core. No Lean brick:
there is no refutation to record.

# δ* #466 — SYZ55: the μ-basis generator-gap SPLIT (near-balance ⊔ constant-syzygy, empty middle)

**Date:** 2026-07-11
**Lane:** codex/syz55-generator-gap (Opus 4.8)
**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ55GeneratorGap.lean`
**Probe:** `scripts/probes/probe_syz55_generator_gap.py`
**Branch:** `codex/syz55-generator-gap` (off `fork/research/proximity-prize` @ ab7ca81a1; `main`
untouched)

## One-line

The balanced-interior residual does **not** obey a uniform gap bound `δ₂−δ₁ ≤ 3`; it **splits**
into a near-balance branch (`g ≤ 3 ⟹ ι ≤ 1`, spread route) and a constant-syzygy branch
(`δ₁ = 0`, maximal gap `g = S`, harmless pencil-floor lift). Probe forensics pin the killing
mechanism per-scalar (structural floor `3` + accidental parallelism that vanishes at large `p`), and
a coverage census shows the split has an **empty middle** on the realizable interior: every
band-realizable interior witness has `δ₁ = 0`, zero middle-gap witnesses.

## Why the split (the SYZ45 counterexample reconciled)

SYZ53 gave `ι = ⌊(δ₂−δ₁)/2⌋`, `ι ≤ 1 ↔ g ≤ 3`. But "gap ≤ 3 for all realizable triples" is FALSE:
the SYZ45 `f = 3g − 2h` triple and the SYZ50/52 on-domain `ι=2` witnesses carry a genuine
**constant** syzygy `W_BC = R·W_AC + c·W_AB` (`R,c ∈ 𝔽` constants). A constant syzygy is a
**degree-0** element of the rank-2 syzygy module, so `δ₁ = 0` and, by the degree-sum law
`δ₁+δ₂ = S`, the gap is **maximal** `g = S`. So the honest object is a dichotomy, not a bound.

## The killing mechanism (verbatim per-scalar forensics)

Probe forensic pass, `n=14, k=7, (4,4,4), t=2, s=10`, exact `exact_badz` on a degenerate SYZ32
stack, each bad scalar attributed to its closing size-s subset(s) — **structural** (subset forced by
one of the three degenerate cores; present at every prime) vs **accidental** (subset whose two
RS-parity vectors `a₀, a₁` are only coincidentally parallel `mod p`; present with prob `~1/p`):

```
p=29      (log2 4.9)  witness#0  δ1=0 gap=12 ι=6   |bad|=4 = 3 structural + 1 accidental   ceiling=12
    z=5      #subsets=1   STRUCTURAL(core)
    z=11     #subsets=1   STRUCTURAL(core)
    z=13     #subsets=11  STRUCTURAL(core)
    z=15     #subsets=1   ACCIDENTAL          <-- the clause that dies at large p
p=1000133 (log2 19.9) witness#0  δ1=0 gap=12 ι=6   |bad|=3 = 3 structural + 0 accidental   ceiling=12
    z=158177 #subsets=1   STRUCTURAL(core)
    z=339564 #subsets=1   STRUCTURAL(core)
    z=993909 #subsets=1   STRUCTURAL(core)
```

**Mechanism:** the SYZ52 small-field over-count is entirely the accidental clause — a non-core
subset `S` on which `a₀ ∥ a₁ (mod p)` by coincidence. That coincidence has probability `~1/p`, so it
is gone at honest field size, leaving exactly the **3 structural** core-forced pencil points = the
generic floor `3 ≪ ceiling ∑(n−sᵢ) = 12`. Even at δ₁=0 (maximal gap) the constant-syzygy witness
lifts harmlessly. This is the per-scalar form of the `_SYZ53PScaling.lean` first-moment collapse.

## The split coverage (empty middle) — census verdict

Probe split-coverage pass computes each witness's minimal syzygy degree `δ₁` by exact linear algebra
over `𝔽_p` (`min_syzygy_degree` of the three band polynomials), hence `g = S − 2δ₁`:

```
n=14 (4,4,4) t=2  S=12   21 witnesses : ALL δ1=0 (gap 12)   MIDDLE(g∈{4..11},δ1≥1) = 0
n=16 (4,4,4) t=3  S=12  150 witnesses : ALL δ1=0 (gap 12)   MIDDLE = 0
n=20 (5,5,5) t=4  S=15   12 witnesses : ALL δ1=0 (gap 15)   MIDDLE = 0
(n=18 (5,5,5) t=3: syzygy-empty on domain)
```

**No middle-gap realizable witness exists** in any enumerated config. The `gap_split` dichotomy is
therefore not merely exhaustive but has an **empty middle on the realizable interior**: a realizable
balanced-interior triple is EITHER near-balance (`g ≤ 3`, generic non-witness, `ι ≤ 1`) OR fully
constant-dependent (`δ₁ = 0`, a level-set witness, maximal gap). There is no intermediate
low-degree-syzygy triple (`δ₁ ∈ {1..}`) that escapes both branches. This removes the "middle case"
worry the route raised: the split is binary and complete on the measured realizable interior.

## Lean (axiom-clean, pure ℕ) — `Frontier/_SYZ55GeneratorGap.lean`

§1 combinatorial split (omega over SYZ53's exact identity):
- `gap_split` — exhaustive dichotomy `(ι≤1 ∧ g≤3) ∨ (2≤ι ∧ 4≤g)`.
- `low_syzygy_of_gap_ge_four` — `4≤g ⟹ δ₁ ≤ ⌊S/2⌋−2` (product-degree drop; SYZ45 low-syzygy regime).
- `constant_syzygy_maximal_gap` — `δ₁=0 ⟹ g = S` (constant syzygy = maximal gap).
- `constant_syzygy_imbalance_maximal` — `δ₁=0 ⟹ ι = ⌊S/2⌋`.
- `near_balance_branch_imbalance_le_one` — the `g≤3 ⟹ ι≤1` branch consumer (via SYZ53).
- `split_verdict` — packaged: near-balance ∨ low-syzygy, both accounting-closing.

§3 forensic table (`decide`, NO axioms): `forensicTable (p, badTotal, structural, accidental)`;
`badTotal_eq_structural_add_accidental`, `structural_floor_eq_three`,
`accidental_vanishes_largefield` (p≥1009 ⟹ accidental=0), `bad_eq_floor_largefield`
(p≥1009 ⟹ badTotal=3 ≤ 12).

§4 coverage census (`decide`, NO axioms): `coverageCensus (n, S, nWit, nMiddle)`;
`no_middle_gap_witnesses` (nMiddle=0 ∀), `census_nonvacuous` (nWit≥1 ∀).

Axiom audit (in-build `#print axioms`): omega/SYZ53 theorems `{propext, Quot.sound}`
(+`Classical.choice`
via iff-imports); **all six `decide` table theorems depend on NO axioms**. No `sorry`,
`native_decide`, or vacuous-`True`. Focused locked build: 8321 jobs, exit 0.

## Scope (honest)

Closes the **combinatorial split**: realizable interior = near-balance branch (`g≤3`, `ι≤1`) ⊔
constant-syzygy branch (`δ₁=0`), empty middle (census-measured), with the per-scalar killing
mechanism recorded. Does NOT prove the large-field floor bound in general (that is the sampled
first-moment content of `_SYZ53PScaling.lean`), and `ι≤1` closes `uniformSylvester` only at rate ½;
production δ* still needs SYZ18 supports, `hrank` realizability, strip-radius transport,
`MCAThresholdLedger` BGK lower bound. **CORE remains OPEN / ON-BGK.** The BGK wall is untouched.

## Downstream handoff

G56/Opus-core: the interior residual is now a two-branch object with no middle. Branch (b) `g≤3` is
SYZ53/SYZ44/SYZ47 (`ι≤1` at rate ½). Branch (a) `δ₁=0` witnesses need only the floor bound
`bad = 3 ≤ ceiling` (SYZ53-pscaling first-moment law); the empty-middle census means no third case.
The remaining genuinely-open input is unchanged: whether an over-budget stack can beat the pencil
accounting at honest field size (SYZ42 existence core), which the forensics show the constant-syzygy
witnesses do not.

## Reuse hooks

- `probe_syz55_generator_gap.py::min_syzygy_degree` — exact minimal syzygy degree `δ₁` of a triple
of
  univariate polys over `𝔽_p` by linear algebra (Hilbert–Burch rank-2 module); bucket any witness
  set by generator gap `g = S − 2δ₁`.
- `forensic_stack` — per-bad-scalar structural/accidental attribution against a core set; reuse to
  separate generic-floor pencil points from small-field parallelism artifacts on any degenerate stack.

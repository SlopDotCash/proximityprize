# Delta Star dossier v4 — standalone state and post-v3 evidence

**Snapshot:** `elizaOS/proximityprize` `main` at `b72890393a68745ecc43f6b39470509b630c7192`
(2026-08-16 audit).

This is the current entry point for the standalone repository. It does not replace the detailed
mathematical and no-go record in
[`deltastar-DOSSIER-v3-2026-07-01.md`](deltastar-DOSSIER-v3-2026-07-01.md); v3 remains the full
campaign dossier through its 2026-07-11 §45 addendum. This document records the repository
migration, reconciles the current ledgers, and classifies the verified results that landed after
the v3 session-final snapshot.

## 1. Current verdict

The production δ* conjecture is **OPEN / ON-BGK**.

The repository contains exact finite-instance pins, unconditional lower and upper components,
conditional production brackets, equivalent reductions, reproducible counterexamples, and a
large machine-checked no-go map. None of those artifacts alone proves the sponsor-equivalent
production statement. Issue
[#4](https://github.com/elizaOS/proximityprize/issues/4) remains blocked on the mathematical CORE
tracked by issue [#1](https://github.com/elizaOS/proximityprize/issues/1).

The exact production-completion gate remains:

1. state the sponsor-equivalent production parameters and quantifiers;
2. assemble both threshold inequalities through the canonical ledger;
3. discharge every production-facing hypothesis without `sorry`, `admit`, a new axiom, or
   hypothesis laundering;
4. audit `#print axioms`, the imported assumptions, and the parameter translation independently;
5. run the focused Proximity Gap checks, locked module build, and repository validation.

A toy instance, a bracket, an equivalent open `Prop`, or a conditional theorem is not closure.

## 2. Canonical repository and control plane

- Repository: [`elizaOS/proximityprize`](https://github.com/elizaOS/proximityprize).
- Integration branch: `main`; feature work uses focused branches.
- Mathematical CORE and campaign tracker:
  [#1](https://github.com/elizaOS/proximityprize/issues/1).
- Cleanup and upstream-carveout ledger:
  [#2](https://github.com/elizaOS/proximityprize/issues/2).
- Documentation and residual-census maintenance:
  [#3](https://github.com/elizaOS/proximityprize/issues/3).
- Production assembly and independent audit gate:
  [#4](https://github.com/elizaOS/proximityprize/issues/4).

The historical `lalalune/ArkLib` issues #466/#499/#505–#509, its
`research/proximity-prize` branch, and the former project board remain provenance only. They are
not current routing instructions.

## 3. Live mathematical surfaces

### 3.1 CORE Paley/BGK face

The binding analytic target remains square-root-scale cancellation for the adversarial smooth
multiplicative subgroup, equivalently the deep DC-subtracted-energy/orbit-class mass profile.
Two important no-go results carried forward from v3 are:

- `_G70DudleyFlatChainingLowerBound.lean`: flat-Dudley chaining already contains the desired
  pointwise control and cannot manufacture it from a weaker metric certificate.
- `_G73ShkredovMultiShiftExponentFloor.lean`: every finite Shkredov–Vyugin multi-shift choice
  stays strictly above exponent `1/2` at prize shape.

These are axiom-clean closures of proposed routes, not a proof of the missing cancellation bound.
The positive certificate still has to control a signed/correlated cross-arc, an orbit-class mass
profile, or an equivalent weighted single-embedding functional at the required scale.

### 3.2 Rate-`1/2` strip face

The conditional strip assembly exposes three production-facing open surfaces:

| face | current open content | status |
|---|---|---|
| F1 | Hilbert–Burch near-balance `ι ≤ 1`; parity-corrected gap is `≤ 2` for even total degree and `{1,3}` for odd total degree | OPEN / BGK-equivalent |
| F2 | `StripSyzygyControlledCeiling` on the dependent-stack range; the independent regime is capped at five | OPEN |
| F3 | union-rank realization `hrank` for the witness-support family | OPEN; overlap chaining is refuted |

The earlier parity-free generator-gap target `δ₂−δ₁ ≤ 1` is false. Consumers use `ι ≤ 1`, so
the parity correction changes the public description without silently changing a landed theorem.

## 4. Verified additions after the v3 session-final snapshot

The entries below are classified by what the checked artifact actually establishes. Migration and
Lean-4.30 repair commits preserve or restore existing results and are not counted as new
mathematical closures. The grouped ledger is the routing layer; theorem-by-theorem details remain
in [`DISPROOF_LOG.md`](../../DISPROOF_LOG.md), the frontier module docstrings, and the exact probes
under `scripts/probes/`.

### 4.1 Post-v3 grouped ledger

The v3 dossier's session-final snapshot was written on 2026-07-11 before the later G205+ and F1
arcs. The following table prevents those landed results from disappearing between that historical
snapshot and the standalone repository. A range denotes a related sequence, not a claim that every
integer in the range names a file.

| arc | machine-checked or reproducible outcome | honest classification and remaining wall |
|---|---|---|
| G205–G215 | Exact integer countermodels realize all late-Newton sign quadrants; collision-free weighted support does not control alignment; the partition engine, dyadic class-count cap, and sharp depth-two wall floor are proved. | Exact no-gos plus an unconditional lower floor. They do not give the signed upper/cancellation estimate. |
| G217–G250 | Mellin-phase, physical-space diagonal, near-definiteness, quotient-Jacobi fanout, bounded-mass eigenfamily, carrier-normalization, and Cartesian row-selection shortcuts are audited; the carrier-correct Parseval layer is discharged; a degree-two Krylov countermodel and sponsor discrepancy calibration are reproducible. | Exact reductions and route closures. The correlated signed row remains uncontrolled. |
| G252–G291 | Phase-histogram, balanced-move, conjugation, multiplier-sign, positivity, gauge/origin, joint-rank, DC-coordinate, single-Plancherel, termwise-Weil, carry-localization, bounded-conductor, and canonical-feature separators are refuted or sharply delimited. The sponsor covariance is isolated as a real signed inner product with a positive-Radon obstruction. | A broad no-go map; none of the refutations proves the required covariance inequality. |
| G295–G309 | The rank palindrome `A_r = A_(n+1-r)` and its reduced census are proved; the production rank lies inside the window; depth-one energy, sign oscillation, dilation transport, bounded-conductor, and odd-cubic transfer routes are calibrated or closed as shortcuts. | Structural identities and no-gos. The in-window sign genuinely oscillates, so no monotone/single-band certificate results. |
| G310–G318 | Exact-stdlib finite audits reach a prize-scale Proth prime for the dimension-two ceiling and below-ceiling pin; companion scale, carry, dilation, all-rank, antipodal-model, depth-three-floor, and rank-five/six guard checks record their precise finite scope. | Computational evidence plus small closed arithmetic pins. No field-uniform or production theorem is inferred from the probes. |
| G320–G326/G329 | G320 reproduces and extends the degree-two Krylov countermodel; G321 gives a second exact rank-palindrome witness; G322/G325 extend the `I_max` value pin through `m=50`; G326/G329 prove the finite and then universal tight decoupling chain; G324 records the naive depth-four floor `8m-7` with its extension hypothesis explicitly unproved. | Reproducibility improvements, exact algebraic extensions, and one hypothesis-scoped numerical floor. They sharpen p-independence/over-budget structure, not CORE. |
| G328/G330 | G328 gives the exact `p=17` spectrum collision; G330 proves injectivity and the 40-value image for every other prime `p = 1 mod 8`. | Exact spectrum-boundary classification. The full MCA census remains executable per-prime evidence. |
| BGK `C12` alignment audit | The favourable collision is reduced to the centered correlation of the actual shifted-intersection and adjacent-rank rows; cyclotomic half caps, separate spectral magnitudes, dilation-orbit compression, and canonical local support floors are all made exact. Countermodels show the marginal data do not fix the needed sign. | Exact reduction and no-go package. The missing input is joint arithmetic alignment of the two actual rows. |
| G139 `Phi` contract audit | The Sidon/accident bridge, injectivity/equivalence layers, arithmetic contract, and exact witness verifier make the proposed certificate reproducible at the stated fields. | A checked interface and finite witness audit, not a universal production certificate. |
| F1 middle-band arc | The numeric polytope exclusion is refuted by an infinite family; the region-syzygy interface separates numeric, region/syzygy, and genuine-stack realizability; SYZ70/SYZ71 locate and occupy the first algebraic/on-domain middle slot. | Refutation and narrowing. The over-budget genuine-stack lift and near-balance theorem remain open. |
| all-depth cyclic floor | The depth-three cyclic energy floor is lifted through every common-tail depth, with strict improvement over the swap floor on nontrivial support. | Unconditional lower-bound component, not the required upper/cancellation bound. |

This grouping records all post-v3 research families visible on canonical `main` at the snapshot;
the detailed ledgers remain authoritative for individual theorem names, hypotheses, probe-only
claims, and axiom reads.

### 4.2 SYZ70/SYZ71 — first middle slot and on-domain occupation

Landed by [PR #5](https://github.com/elizaOS/proximityprize/pull/5), merge
`73c2e17ddb63c374bb62c08297075a9b1aed9a5f`.

**Lean theorems:**

- `_SYZ70FirstOpenMiddleSlot.lean` proves that a balanced middle band first becomes
  arithmetically possible at degree profile `(6,6,6)`, where the singleton product degree is `7`,
  gap is `4`, imbalance is `2`, and the convention bridge gives cofactor degree `1`.
- `_SYZ71LinearMiddleSlot.lean` proves the linear-cofactor interface, the band-realizable
  `(n,k,t)=(20,10,2)` home, and the associated degree and budget facts.

**Computational evidence:**

- `probe_syz71_linear_middle_slot.py` and `probe_syz71_verify_f41.py` exhibit and verify an
  on-domain `F_41`, `μ_20` occupant. The explicit finite-field witness is not replayed as a Lean
  theorem.

**Consequence:** the first middle slot is not empty at the algebraic/domain-counting level. This
refutes an emptiness route and narrows F1 to the over-budget-stack lift. It does **not** discharge
`UniformSylvesterInjective`, `ι ≤ 1`, or production δ*.

### 4.3 All-depth cyclic energy floor

Landed by [PR #7](https://github.com/elizaOS/proximityprize/pull/7), merge
`24060188e843d66dc93cfaa87be2ee41686d7c4e`.

`REnergyCyclicFloorAllDepth.lean` proves

```text
3 * |G|^(m+3) - 2 * |G|^(m+1) ≤ rEnergy G (m+3)
```

for every common-tail length `m`, by iterating the exact characteristic-`p` recursion from the
depth-three cyclic floor. It also proves strict improvement over the adjacent-swap floor for
nontrivial support. This is an unconditional reusable **lower** bound. It is not an upper energy
bound, characteristic transfer, capacity result, or CORE closure.

### 4.4 G330 order-eight spectrum boundary

Landed in standalone `main` by the port of ArkLib PR #541, merge
`7415bf4abcde33e756c1193f4b388e2b61fac8a1`.

`_G330SpectrumExactBoundary.lean` proves that for every prime `p ≡ 1 (mod 8)`, `p ≠ 17`, the
order-eight weight-{1,3} signed spectrum map is injective and its image has exactly `40` values.
Together with the explicit G328 collision, the spectrum-collision exceptional prime is exactly
`17`; the former tested-range cutoff is removed.

The full MCA bad-scalar census and the below-ceiling maximum remain per-prime executable evidence.
G330 is an exact spectrum boundary, not a field-uniform MCA or production δ* theorem.

### 4.5 Standalone migration and repair commits

Commit `8f68adbe652f54641269f8c4ae118f9cf88cb757` establishes the standalone repository and its
Lean-4.30 build surface. Subsequent repair, import, index, and generated-ledger commits restore the
campaign corpus on `main`. They are build and provenance facts; they do not upgrade conditional
mathematical claims to unconditional ones.

## 5. Residual census versus production completion

The 2026-08-16 regeneration at `b72890393` reports:

- 117 strict `def ...Residual ... : Prop` declarations;
- 69 open, 47 discharged, and one refuted;
- 79 residual-like near misses outside the strict suffix/type convention.

The historical 2026-07-11 snapshot was 108 total, 62 open, 45 discharged, one refuted, and 76
near misses. Both snapshots are retained and explicitly dated in
[`docs/wiki/residual-census.md`](../wiki/residual-census.md); only the 2026-08-16 figures are the
current totals.

The strict census is not the production completion ledger. In particular,
`UniformSylvesterInjective`, `StripSyzygyControlledCeiling`, and `hrank` are theorem-facing named
Props or structure fields outside the strict `*Residual : Prop` pattern. A stable or falling
strict count therefore cannot by itself certify δ* closure.

## 6. Honesty classification

Use these categories in issues, PRs, and future dossier updates:

- **Exact pin:** both required inequalities or an exact finite classification are proved for the
  stated parameters.
- **Unconditional component:** a theorem with no new campaign assumption, but not the end-to-end
  target.
- **Conditional reduction/bracket:** a useful theorem whose named hypotheses remain open.
- **Computational evidence:** reproducible finite computation that is not a universal Lean theorem.
- **Refutation/no-go:** a theorem or reproducible witness that closes an attempted route.
- **Open residual:** a precisely stated missing input; naming it does not discharge it.

The v4 ledger includes unconditional components, exact reductions and finite classifications,
reproducible computational evidence, and a large family of refutations/no-gos. The production
conjecture remains open.

## 7. Reproduction and maintenance

Use the repository wrappers; never run a bare concurrent Lake build.

```bash
scripts/pg-warm.sh
scripts/pg-iterate.sh <changed-proximity-file>
./scripts/lake-locked.sh build <module>
python3 scripts/residual_census.py --wiki-out docs/wiki/residual-census.md
./scripts/validate.sh --docs
```

Residual regeneration preserves blockquotes whose first line begins with `Campaign addendum`.
Keep historical snapshots explicitly dated, add a current audited block, and ensure the summary
and `scripts/residual_census.json` agree before publication.

## 8. Next work

1. For F1, address the over-budget-stack lift/near-balance surface without reusing the refuted
   empty-middle or uncorrected parity target.
2. For F2, control the syzygy-carrying dependent bulk rather than the already capped independent
   regime.
3. For F3, seek a span certificate that does not rely on the refuted overlap-chaining route.
4. For the analytic CORE, supply the missing square-root-scale signed/orbit-class certificate.
5. Attempt issue #4 only after one of those routes produces an unconditional production input.

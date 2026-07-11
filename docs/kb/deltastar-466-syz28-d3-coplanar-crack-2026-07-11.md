# δ\* / #466 — SYZ28: the D=3 over-budget coplanar crack, settled

Date: 2026-07-11
File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ28D3CoplanarCrack.lean`
Probes: `scripts/probes/probe_syz28_d3_coplanar_crack.py` (enumeration),
`probe_syz28_verify_classification.py` (exact classification + first lift test),
`probe_syz28_part3.py` (mismatch analysis + mca-filtered lift test)
Branch: `codex/syz28-d3-coplanar-crack` (off `fork/research/proximity-prize` @ 028946e92)

## The question

SYZ27 confined interior-band (`1/4 < δ < 1/3`, rate 1/2) deficiency to under-budget `D = 2`
covers **except** for a "rare D=3 over-budget coplanar shape with d ≤ 1" — the last object that
could falsify the rate-1/2 strip. SYZ28 enumerates, classifies, field-tests, and lift-tests it.

## Verdict: REAL-BUT-UNDER-BUDGET, with an exact yield law. The strip is NOT falsified.

### 1. Enumeration (~10⁶ over-budget D=3 full covers, n ∈ {16,20,24,28,32}, k=n/2, band + ⌈2n/3⌉ boundary)

- Deficient (`d ∈ {1,2}`) D=3 over-budget covers exist at **every** n, including **strictly
  interior** ones (n=24, all cores size 17 > ⌈2n/3⌉=16; n=28 size 20; n=32 size 23).
- **Every hit is field-independent** over `p ∈ {101, 1009, 65537, 10⁶+3, 2³¹−1}`. The SYZ27
  "rare coplanar shape" is neither a small-characteristic accident nor sporadic. (This
  *corrects* the impression left by SYZ26/27 that interior deficiency might be accidental.)

### 2. Classification — EXACT

In 61 654/61 654 strict-interior trials (n=24, all-17 cores) and 106 299/106 300 band trials:

```
d = max(0, (n+k) − min over pairings (|Cᵢ ∪ Cⱼ| + |C_l|))
```

Interior D=3 deficiency **is precisely the pair-union subadditivity defect**: the joint
syndrome span sits inside the envelope `A_{Cᵢ∪Cⱼ} ⊔ A_{C_l}` of dimension
`≤ (|Cᵢ∪Cⱼ|−k) + (|C_l|−k)`; when that count is below the ceiling `n−k`, deficiency is FORCED
— over every field, because it is a dimension count. Field-independence is thereby *explained*
(and proven, §Lean below), not merely observed. Signature shape: a **near-duplicate pair** —
two cores with overlap ≈ `s−1`, union ≈ `s+1`, collapsing the envelope.

The **single** exception (1/106 300) lies ON the excluded `δ = 1/3` boundary: n=24, all cores
size 16 = ⌈2n/3⌉, symmetric overlaps (11,11,11), triple 9, all pair-unions 21 (envelope count
13 ≥ 12 = n−k, mechanism inapplicable); field-independent d=1 — the SYZ25/26 three-coplanar
incidence shape, which never enters the open strip (consistent with SYZ26).

Scaling law (proven arithmetic): for every k ≥ 10 the band size `s = ⌊(4k+3)/3⌋` supports the
near-duplicate-pair defect (band + over-budget + full-cover feasibility + envelope count
< n−k). The shape exists at every n = 2k ≥ 20.

### 3. Lift test — word-level, exhaustive

n=16 witness (cores sizes 11, overlaps (6,7,10), d=1 over five primes incl. 2³¹−1), GF(17):
pencil-structured stacks (`u₀ + zᵢu₁` polynomial on core `Cᵢ`, i.e. locally-poly per core, not
globally), every line point `u₀ + z·u₁` (z ∈ F_p ∪ {∞}) list-decoded exhaustively (agreement
≥ s=11 ⟺ δ-close, δ=5/16), stacks with mutual correlated agreement filtered out:

- **max verified mca-bad scalars = 15 = n − 1 = the SYZ22 budget, exactly** (achieved,
  z-set explicit); never 16, never more.
- Unfiltered all-close lines (18 = |F_p|+1 "bad") occur but always carry correlated agreement
  (both u₀,u₁ poly on a common core) — degenerate, not mca-bad.

And the cap is now a theorem: over-budget D=3 at rate 1/2 forces pencil yield
`∑(n−sᵢ) ≤ n`; **strictly interior cores force `∑(n−sᵢ) ≤ n−1`** — the budget. Even if every
pencil candidate were a distinct verified bad scalar, a strict-interior D=3 deficient cover
cannot exceed `n−1 < n < n+1`. No over-budget hit is arithmetically possible; no new ceiling;
δ\* status untouched. The witness saturates the cap with **zero slack** (15 = n−1) — the strip
budget is tight at the D=3 deficient shapes.

## Proven verbatim in Lean (all axiom-clean: propext/Classical.choice/Quot.sound; no sorry, no native_decide)

1. `partialSup_three_le_envelope` — `A₀ ⊔ A₁ ≤ B ⟹ ⨆ᵢ<₃ Aᵢ ≤ B ⊔ A₂`.
2. `partialSup_three_finrank_le` — envelope rank cap `finrank(⨆ᵢ<₃ Aᵢ) ≤ finrank B + finrank A₂`
   (via `Submodule.finrank_sup_add_finrank_inf_eq`); valid over EVERY field.
3. `envelope_forces_deficiency` — envelope count < ceiling ⟹ `⨆ Aᵢ ≠ W` (the classification's
   rigorous form; instantiated at RS with `B = A_{C₀∪C₁}`, `finrank B = |C₀∪C₁|−k`).
4. `d3_yield_cap` — n=2k, over-budget D=3 ⟹ `∑(n−sᵢ) ≤ n` (omega).
5. `d3_yield_cap_strict_interior` — + strict interior (`3sᵢ > 2n`) ⟹ `∑(n−sᵢ) ≤ n−1` (omega).
6. `forced_defect_scaling` — ∀ k ≥ 10, `s = (4k+3)/3` satisfies band ∧ envelope-defect ∧
   feasibility ∧ over-budget (omega with Nat division).
7. `finrank_cePlane` (= 2, rank–nullity) + `overbudget_envelope_deficient` — over-budget
   (∑ finrank = 4 ≥ 3) family failing to generate ℚ³, derived THROUGH the envelope theorem
   (near-duplicate-pair caricature: two copies of the plane + ⊥).
8. Concrete `decide` witnesses: `syz28Witness` (n=16: sizes 11, full cover, over-budget 9 ≥ 8,
   pair-union card 12, envelope count 7 < 8, yield 15 = n−1) and `syz28BoundaryShape` (n=24
   boundary: sizes 16, full cover, all pair-unions 21, envelope mechanism inapplicable).

## Honest residuals

- **Pencil-yield law** (SYZ3 substrate): every mca-bad scalar of a deficient stack arises from
  a core pencil (bad count ≤ ∑(n−sᵢ)) — word-level verified here (saturation at 15, never 16),
  Lean proof not in hand. This is the bridge from the yield-cap theorem to the scalar count.
- **D ≥ 4 over-budget gluing law** — unchanged from SYZ27 (probe: d=0 always).
- The classification equality (probe-exact) is formalized as the ≥ direction (forced
  deficiency); the ≤ direction (no deeper interior degeneracy) is probe-supported
  (61 654/61 654 strict-interior), with the lone deeper shape pinned to the δ=1/3 boundary.

## Reuse hooks

- `envelope_forces_deficiency` is the general-D=3 upgrade of SYZ25's coordinate counterexample:
  any support-envelope collapse forces deficiency field-independently.
- The mca filter in `probe_syz28_part3.py` (agreement-set intersection ≥ s) distinguishes
  degenerate all-close lines from genuine mca-bad scalars — reuse for any future lift test.
- Pigeonhole list-decoding trick: agreement-`s` set meets the first `n−(n−s)+2` positions in
  ≥ k points — cuts brute-force interpolation subsets 10×.

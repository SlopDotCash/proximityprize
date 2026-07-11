# δ\* / #466 — SYZ31: the two strip set-geometry facts — one REFUTED, one reduced

Date: 2026-07-11
File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ31SetGeometryFacts.lean`
Probe: `scripts/probes/probe_syz31_two_block_floor_refutation.py`
Branch: `codex/syz31-set-geometry-facts` (off `fork/research/proximity-prize` @ 17df32dde)
Predecessors: `deltastar-466-syz30-lemmas-2026-07-11.md`, `deltastar-466-syz28-d3-coplanar-crack-2026-07-11.md`

SYZ30 reduced strip lemma 3 to a single **two-block cross-intersection floor** (`|U₀∩U₁| ≥ k`)
and lemma 1 to a single **fresh independence-mod-`E`** hypothesis. SYZ31 settles both as far as
the honest arithmetic allows.

## Fact 3 — the two-block floor is **FALSE as stated** (near-duplicate cluster crack)

The SYZ30 residual — `|U₀∩U₁| ≥ k` for *every* two-block split of a `D≥4` over-budget band full
cover, "probe slack exactly 0" — was pinned by **random** sampling that missed an adversarial
shape.

**Counterexample `syz31Crack`** (`decide`-verified, `n=16`, `k=8`, all four cores size `11` = the
unique strict-interior band `2n/3 < s < 3n/4`):

```
C₀ = {0..10},  C₁ = {0..5, 11..15},  C₂ = {0..4,6, 11..15},  C₃ = {0..3,5,6, 11..15}
```

`C₁,C₂,C₃` are pairwise **near-duplicates** (all three pairwise overlaps `= 10 > k`). The split
`{0} | {1,2,3}` gives `U₀ = C₀` (11), `U₁ = C₁∪C₂∪C₃ = {0..6,11..15}` (12 — only one above a
*single* core, the cluster degeneracy), full cover, over-budget `∑(sᵢ−k)=12≥8`. Then
`|U₀∩U₁| = |{0..6}| = 7 < 8 = k`, and the two-block envelope `(11−8)+(12−8) = 7 < 8 = n−k` — the
all-partition minimum dips **below** the ceiling. Probe: actual rank deficiency **`d = 1`,
field-independent** over `p ∈ {101,1009,65537,2³¹−1}` — a genuine deficient shape, not a counting
artifact.

This is the **SYZ28 `D=3` near-duplicate *pair* crack replicated as a near-duplicate *triple***
**block inside a `D=4` cover**, and it **scales to every `n`**: strict-interior band
`s = ⌊(3n−1)/4⌋` gives `minI = k−1`, `d = 1` at `n ∈ {16,20,24,28,32,…}` (probe (1)). So SYZ27's
"`D≥4` over-budget deficiency-free" is a **sampling artifact**, and the two-block floor is not a
theorem. Adversarial random sampling (probe (2)) also finds the violation directly (`n=16`,
`minI=7`, 2 hits / 108 129 over-budget covers — rare, hence SYZ30's miss).

**No landed theorem is refuted.** SYZ29 `d4_over_budget_deficiency_zero` and SYZ30
`partition_envelope_ge` both carry the floor as an *explicit hypothesis*; it is the conjectured
*residual* that falls. (SYZ29 `d4_pairing_envelope_ge` already needed the overlap bound
`|Cᵢ∩Cⱼ| ≤ k`, but only for *pairing* partitions — nothing there forces a *triple*-block union to
be large, which is exactly the gap.)

## Fact 3 — the **corrected** floor, PROVED (the discriminating hypothesis)

The counterexample localizes the missing hypothesis exactly: some block is an **all-near-duplicate
cluster** (no pair inside it has union `≥ 2s−k`). The honest minimal hypothesis is a **spread
pair**: some block contains two cores with union `≥ 2s−k` (overlap `≤ k`). Under it the floor holds
with room to spare — for `D≥4` at least one block is multi-core, and if it carries a spread pair,

  `|U₀|+|U₁| ≥ (2s−k) + s = 3s−k > 3k = n+k`  (band `3s>4k`)  ⟹  `|U₀∩U₁| = |U₀|+|U₁|−n > k`.

Probe (3): under the global no-near-duplicate condition (all pairwise overlaps `≤ k`) the floor
holds with `minI ≥ k+1` and **zero** violations across `>3·10⁵` trials, whereas the raw floor is
violated. The excluded near-duplicate clusters are absorbed exactly as at `D=3` — by the SYZ28
**pencil-yield cap**, not by set geometry.

## Fact 1 — fresh independence mod `E`: the provable geometric core

SYZ30 reduced lemma 1 to "fresh syndrome contributions linearly independent modulo the core
envelope `E`" (abstract codim bound `fresh_card_le_codim` proved). SYZ31 supplies the linear-algebra
core that discharges the independence from support data: a **private escaping coordinate** `c i`
per fresh functional — outside the core support `U'` (so every `e ∈ E` vanishes there: `escape`),
where `f i` does not vanish (`hit`) and every *other* fresh functional does (`private`). Then the
images `E.mkQ (f i)` are linearly independent (`indep_mod_of_private_coord`), hence
`#fresh ≤ finrank W − finrank E` (`fresh_card_le_codim_of_private_coord`). SYZ18 distinct supports +
the syndrome-pair `γ`-twist are the intended source of the private coordinates; the lemma isolates
the exact linear algebra, leaving *that* support-combinatorial input as the reduced residual.

## Proven verbatim in Lean (axiom-clean: propext/Classical.choice/Quot.sound; no sorry, no native_decide)

- Refutation: `syz31_core_sizes`, `syz31_full_cover`, `syz31_over_budget`,
  `syz31_cluster_overlaps` (all pairwise overlaps 10 > k), `syz31_two_block_floor_fails`
  (`|U₀∩U₁| = 7 < 8`, envelope `7 < 8`), all `decide`.
- Corrected floor: `two_block_floor_of_spread_pair`, `two_block_floor_of_two_spread_pairs`,
  `envelope_two_blocks_ge_of_spread_pair` (omega), and `decide` witness `syz31_spread_pair_floor`
  (SYZ29 four-cover, block `{0,1}` overlap 6 ≤ k, union 16 ≥ 2s−k, floor `11 ≥ 8`).
- Fact 1: `indep_mod_of_private_coord`, `fresh_card_le_codim_of_private_coord`.

## Scoreboard after SYZ31

1. **Fresh independence-mod-`E`** (lemma 1) — reduced to a *private escaping coordinate* per fresh
   functional (`indep_mod_of_private_coord` discharges the linear algebra; SYZ18 + the `γ`-twist
   supply the coordinates).
2. **Formula `≤` direction** (lemma 2, unchanged) — MDS genericity (SYZ25/26). The one substantive
   open analytic residual.
3. ~~Two-block cross-intersection floor~~ **REFUTED as stated** (near-duplicate cluster crack,
   `d=1` field-independent, all `n`); corrected floor holds under the **no-near-duplicate-cluster /
   spread-pair** hypothesis (`two_block_floor_of_spread_pair`); the excluded clusters are
   yield-cap-absorbed (SYZ28), not set-geometrically forbidden.

Net: lemma 3's residual is **corrected** (the raw floor was false — a genuine sampling gap; the
strip's `D≥4` gluing needs the spread-pair condition that SYZ29 used only for pairs), and lemma 1's
residual is sharpened to one support-combinatorial input. Only lemma 2 remains a substantive open
analytic residual. Unconditional δ\* status untouched; strip not falsified (near-dup clusters route
to the yield cap, as at `D=3`).

## Reuse hooks

- `syz31Crack`: the canonical `D=4` near-duplicate-triple counterexample; use to stress-test any
  "`D≥4` deficiency-free" or two-block-floor claim before conjecturing it.
- `two_block_floor_of_spread_pair`: the corrected floor — plug the spread-pair (some block union
  `≥ 2s−k`) to close the SYZ30 `partition_envelope_ge` `m=2` disjunct.
- `indep_mod_of_private_coord`: generic "distinct private escaping coordinates ⇒ independent modulo
  a coordinate-confined subspace" — reuse for any support-geometry independence-mod-`E` count.

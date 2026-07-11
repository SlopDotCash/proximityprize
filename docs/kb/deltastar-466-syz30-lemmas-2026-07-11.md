# δ\* / #466 — SYZ30: strip-scoreboard lemmas 3 and 1 (the tractable pair)

Date: 2026-07-11
File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ30LemmasOneThree.lean`
Branch: `codex/syz30-lemmas-one-three` (off `fork/research/proximity-prize` @ 94e3b2fb5)
Predecessor: `docs/kb/deltastar-466-syz29-yield-d4-2026-07-11.md` (the 3-lemma scoreboard)

SYZ29 left three named lemmas for the unconditional rate-`1/2` strip. SYZ30 attacks the two
tractable ones — **lemma 3** (`D ≥ 4` all-partition minimization, pure combinatorics) and
**lemma 1** (fresh-scalar accounting, a rank/codimension count) — working out the honest
arithmetic, proving the theorem-pieces, and reducing each to a single sharp residual.

## Lemma 3 — all-partition minimization ⤳ ONE two-block inequality

Claim: for a `D ≥ 4` over-budget band full cover (`k = n/2`, band `2n/3 < sᵢ < 3n/4`, full cover),
every set-partition `P` into `m` blocks with union sizes `U₀,…,U_{m−1}` has
`∑_{j<m}(Uⱼ − k) ≥ n − k`.

**Case split (probe + this-file `min_envelope` analysis, `n∈{16,20,24}`, `D∈{4,5}`, over-budget):
the argmin is ALWAYS `m = 1`.** Per block-count minimum slack `env − (n−k)`:

| block-count m | min slack | status |
|---|---|---|
| 1 (whole cover) | **0** (exact) | PROVED `envelope_whole` |
| ≥ 3 | ≥ 2 | PROVED `envelope_ge_of_three_blocks` (band size floor, no over-budget needed) |
| 2 | **0** (tight, never below) | REDUCED to floor `|U₀ ∩ U₁| ≥ k` |

- `m = 1`: `U₀ = n` ⟹ `∑ = n − k` exactly.
- `m ≥ 3`: `s ≤ Uⱼ` (each block ≥ a band core) + `2n < 3s` ⟹ `∑ ≥ m(s−k) ≥ 3(s−k) ≥ k+1 > n−k`.
  Pure band size floor — unconditional, `n`-uniform omega/`sum_le_sum`.
- `m = 2`: inclusion–exclusion `a + b = n + |U₀∩U₁|` gives envelope `(a−k)+(b−k) = |U₀∩U₁|`
  **exactly** (`envelope_two_blocks_eq_inter`). So `∑ ≥ n−k ⟺ |U₀∩U₁| ≥ k`.

The `D = 3` crack (SYZ28) is precisely the `m = 2` case with a **near-duplicate pair** block
(`|C₀∪C₁| = s+1`) + singleton, where `|U₀∩U₁| = k − 1` (slack `−1`). For `D ≥ 4` the probe finds
`|U₀∩U₁| ≥ k` with slack **exactly 0**, never below. The size floors alone do NOT force it (a
near-dup pair block + singleton gives only `2k/3`), so it is a genuine set-geometry fact — the
single residual. **Net: lemma 3 "min over all set-partitions" ⤳ "one two-block intersection
≥ k".**

Witness (`syz30_two_block_floor`, `decide`): the SYZ29 `n=16` four-cover — the tightest `m=2`
split `{0,1,2}|{3}` has `|U₀∩U₁| = 11 ≥ 8 = k`, envelope `8+3 = 11 ≥ 8 = n−k`. No `D=4` crack.

## Lemma 1 — bound `#fresh` ⤳ independence modulo the core envelope

Claim: `#fresh` bounded so `#bad ≤ ∑(n−sᵢ) + #fresh` closes under budget. G87 substrate: each bad
scalar's `t`-witness → a block of `t−k` functionals on `SyndromePair C`, total dim `2(n−k)`
(`G87.finrank_syndromePair`). A **fresh** scalar (witness support `S ⊄` core union `U'`) carries a
functional escaping `U'`, hence NOT in the core envelope `E` (functionals confined to `U'`); each
fresh block adds ≥ 1 independent dim mod `E`; SYZ18-distinct supports keep them independent.

Load-bearing accounting = a **codimension count**: `p` fresh vectors with images linearly
independent in `W ⧸ E` obey `p ≤ finrank W − finrank E` (`fresh_card_le_codim`, from
`LinearIndependent.fintype_card_le_finrank` + rank–nullity). Syndrome specialization
(`fresh_scalars_card_le_syndrome`): `#fresh ≤ 2(n−k) − finrank E`. Composed with SYZ29's
unconditional split (`bad_card_le_pool_add_fresh_rank`):

  `#bad ≤ ∑(n − sᵢ) + (2(n − k) − finrank E)`.

**Net: lemma 1 "bound `#fresh`" ⤳ "fresh contributions independent modulo the core envelope `E`"**
— the support-geometry + SYZ18 input, the residual.

## Proven verbatim in Lean (axiom-clean: propext/Classical.choice/Quot.sound; no sorry, no native_decide)

Lemma 3: `envelope_whole`, `envelope_ge_of_three_blocks`, `envelope_two_blocks_eq_inter`,
`envelope_two_blocks_ge_of_inter_floor`, `partition_envelope_ge` (packaged 3-case), and the
`decide` witness `syz30_two_block_floor`.
Lemma 1: `fresh_card_le_codim`, `fresh_scalars_card_le_syndrome`, `bad_card_le_pool_add_fresh_rank`.

## Scoreboard after SYZ30

1. **Fresh independence-mod-`E`** (reduced lemma 1): fresh syndrome contributions linearly
   independent modulo the core envelope `E` (support-geometry + SYZ18). [was "bound `#fresh`"]
2. **Formula `≤` direction** (lemma 2, unchanged): joint span reaches the min-envelope — SYZ25/26
   MDS genericity. The one substantive open analytic residual.
3. **Two-block cross-intersection floor** (reduced lemma 3): `D ≥ 4` over-budget band covers have
   `|U₀ ∩ U₁| ≥ k` for every two-block split. [was "min over all partitions"; probe slack `0`]

All statements `n`-uniform (omega / finrank counts) ⇒ production `n = 2³⁰` residual is the same
three. Unconditional δ\* status untouched; strip NOT falsified. Lemmas 3 and 1 reduced from
quantifier-heavy minimizations to single sharp probe-pinned inequalities; only lemma 2 remains
substantive.

## Reuse hooks

- `fresh_card_le_codim`: any "distinct objects independent mod a subspace ⇒ card ≤ codim" count.
- `envelope_two_blocks_eq_inter`: two-block envelope = cross-intersection (the crack localizer).
- `partition_envelope_ge`: 3-case packaged all-partition floor, plug the `m=2` floor to close.

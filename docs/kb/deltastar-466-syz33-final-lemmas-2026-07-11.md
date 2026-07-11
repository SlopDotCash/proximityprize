# δ* #466 — SYZ33: the final two strip lemmas (lemma 1 closed, lemma 2 isolated, strip assembled)

Date: 2026-07-11
File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ33FinalTwoLemmas.lean`
Branch: `codex/syz33-final-two-lemmas` (off fork `research/proximity-prize` tip `b747c6b1f`)

## Context — the scoreboard SYZ33 inherits

SYZ29–32 reduced the unconditional rate-`1/2` interior-band strip theorem to **two** named
residuals (lemma 3 — the two-block floor / cluster routing — was CLOSED as a case split in SYZ32
by the RS-uniqueness merge, `routed_bad_le_budget`):

1. **Lemma 1 — fresh independence mod `E`.** SYZ31 `indep_mod_of_private_coord` proved the
   linear-algebra core: a *private escaping coordinate* per fresh functional forces
   `LinearIndependent F (fun i => E.mkQ (f i))`. Residual = the **support-combinatorial supply** of
   those coordinates.
2. **Lemma 2 — formula `≤` / MDS generation.** SYZ25/26 pinned it as local-to-global polynomial
   rigidity, *strictly stronger* than the over-budget count (the counting corollary is REFUTED,
   `overbudget_not_imp_generation`). Clean overlap route (`incremental_of_large_cores`) covers only
   `δ ≤ 1/4`; strip interior `1/4 < δ < 1/3` deficiency-free by probe only.

## What SYZ33 proves (10 theorems, all axiom-clean: propext/Classical.choice/Quot.sound; no sorry, no native_decide)

### Lemma 1 — CLOSED to two crisp inputs
- `exists_private_positions` — the combinatorial supply: if the **residual supports** `S i \ U'`
  are pairwise **disjoint** and nonempty, a private system `c : Fin p → κ` exists with `c i ∈ S i`,
  `c i ∉ U'`, `c i ∉ S j` (j≠i). Disjointness is the load-bearing content.
- `exists_fresh_indep_family` — **lemma 1 closed.** Given blocks `Blk i` (the `S i`-anchored dual
  annihilator) that are anchored (`hanch`), MDS-non-degenerate at each escaping coordinate
  (`hMDS : ∀ x ∈ S i \ U', ∃ g ∈ Blk i, g x ≠ 0`), plus disjoint nonempty residuals, there is a
  choice `f i ∈ Blk i` with `LinearIndependent F (fun i => E.mkQ (f i))`. Built from SYZ31 +
  `exists_private_positions`.
- `fresh_card_le_codim_of_disjoint` — composes with SYZ30 `fresh_card_le_codim`:
  `p ≤ finrank (κ→F) − finrank E`.
- `twist_pair_indep` — the **γ-twist**, proved outright: two shared-support scalars with distinct
  `γ₀ ≠ γ₁` are already independent in the syndrome **pair** space (`a·L(γ₀)+b·L(γ₁)=0 ⟹ a=b=0`).
  So support-sharing costs at most the `F²` factor, never collapses independence.

Net: lemma 1's residual is now the two **crisp** inputs — (a) fresh residual supports pairwise
disjoint off the core (SYZ18 distinct supports + γ-twist are the intended source; `twist_pair_indep`
proves the twist half), and (b) each block MDS-non-degenerate (RS duals are — the same genericity
lemma 2 needs). `DisjointResidualSupports` names input (a).

### Lemma 2 — isolated (the ONE open analytic residual, NOT closed)
- `spread_generation_realizes_budget` — re-export: generation `⨆Aᵢ=W` ⟹ span attains ceiling
  `finrank W` (SYZ22 realizability ⟹ union budget `|U|≤n−1`).
- `spread_incremental_of_large` — the proven `δ ≤ 1/4` sufficient condition (SYZ26 overlap route).
- Strip interior `1/4 < δ < 1/3` generation remains OPEN (probe `d=0` only, no gluing proof).

### Strip theorem — assembled as a case split (merged branch n-uniform)
- `strip_certified_bad_le_budget` — the n-uniform merged closure: strict-interior over-budget band
  family, bad set block-attributed to `m ≤ 3` merged blocks (union `Uⱼ∈[s,n]`, `|Tj|=n−Uⱼ`) ⟹
  `#B ≤ n−1`. Unconditional linear algebra (= `SYZ32.routed_bad_le_budget`).
- `strip_spread_budget_of_realizability` — spread branch (`m≥4`): realizability `SuperadditiveUnion`
  ⟹ `Ucard ≤ n−1` (= `SYZ22.strip_budget_of_realizability`); the input (generation) is lemma 2.
- `strip_routed_budget_n32` / `_n64` — concrete: `n=32,k=16,s=22,m=3` ⟹ `∑(32−Uⱼ)≤31`;
  `n=64,k=32,s=43,m=3` ⟹ `∑(64−Uⱼ)≤63`.

## Honest status

- **Lemma 1: CLOSED** modulo (a) disjoint-residual supports + (b) MDS non-degeneracy — both crisp,
  both instantiable for RS; the γ-twist half proved.
- **Lemma 2: OPEN** in the strip interior (unchanged; the single substantive analytic residual).
- **Strip theorem: assembled as a case split.** Merged branch (`m≤3`) proven unconditionally in the
  linear algebra; spread branch (`m≥4`) rests on lemma 2. So the strip is closed **iff** lemma 2 is.
- **No new unconditional δ* statement.** Chaining to `mcaDeltaStar ≥ 1/3−lattice` at `n=2³⁰` still
  needs: lemma 2 (interior generation), lemma-1 input (a) instantiated, SYZ22 `SuperadditiveUnion`
  realizability filled, and a `MCAThresholdLedger` bridge from the count ceiling `#bad ≤ n−1` to the
  δ* floor. The ledger consumes a *lower* bound (BGK/incidence floor, `_PrizeFloorOfBGK`); the strip
  supplies the *count* ceiling — joining them is the still-open realizability step. NOT a cheap wire.

## Pitfalls hit
- `twist_pair_indep`: F is a general (unordered) field — `linarith` fails; use `linear_combination`.
- `.lake` symlinked to the main checkout; deps (SYZ32/SYZ26/SYZ22) built once via `lake-locked build`
  (8674 jobs) then iterate lockless with `pg-iterate.sh` (~10s).

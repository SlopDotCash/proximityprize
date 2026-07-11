# δ* / #466 — THE ONE-QUESTION MAP (SYZ67 canonical consolidation, 2026-07-11)

**This is the single entry point** for a future prover (human or agent) picking up the rate-`1/2`
strip route of the Proximity Prize (#466). It states, in final coordinates, the one question the
whole SYZ arc has converged to, names the Lean object for every face, gives their exact logical
relations, records the classical surrounding theory that is now **proved** (not assumed), the
empirical status of each face, and the precise sense in which the faces are **one** question.

Everything below is in-tree on `research/proximity-prize` (fork tip `f71099aa6`, SYZ66). The
production δ* conjecture (`mcaDeltaStar` at rate `1/2` equals the strip value ≈ `1/3`) remains
**OPEN / ON-BGK**. Nothing here is a closure. Read the parent
[`CLAUDE.md`](../../ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md) build/honesty rules and
`docs/kb/deltastar-DOSSIER-v3-2026-07-01.md` §6 (SYZ54 + SYZ67 addenda) before touching the cone.

---

## 0. The headline in one paragraph

The rate-`1/2` strip theorem is now a **single assembled theorem** whose conditional δ* bracket
`357913941/2³⁰ ≤ δ* ≤ 358612991/2³⁰` (`SYZ46.deltaStar_bracket_of_strip_master_hypothesis`,
sharpened by `SYZ60Dictionary.deltaStar_bracket_of_badCountCeiling`) depends on exactly **three
open Props**. The entire classical scaffolding that used to sit under them — the μ-basis of a
coprime band triple, its freeness, rank, graded exchange, windowed Hilbert function, two-ramp
shape, and degree-sum law — is now **unconditional Lean theory** (SYZ61→SYZ65, ~1000 Mathlib-worthy
lines). What remains is three *faces of one object*: the **syzygy structure of the witness-support
family `{Sᵢ} ⊂ μ_n`**. SYZ49 proved the governing quantity is the **BGK additive-character level
set** — so the three faces, and the CORE Paley/BGK wall, are the same wall in different coordinates.

---

## 1. THE ONE QUESTION (final coordinates)

> **Over `μ_n` (`n = 2³⁰`, rate `1/2`), does the syzygy structure of an over-budget MCA
> witness-support family force the bad-scalar count below the strip budget?**

Concretely this is the conjunction of three Props, each a *face* of that syzygy structure:

| # | face | Lean Prop | one-line content |
|---|------|-----------|------------------|
| **F1** | imbalance / generator-gap | `SYZ40.StripMasterHypothesis''.uniformSylvester` = `SYZ38.UniformSylvesterInjective K n k`; sole open sub-fact `ι ≤ 1`, equivalently **Hilbert–Burch gap `δ₂−δ₁ ≤ 1`** | the μ-basis of a balanced pairwise-coprime band triple `(W_AB,W_AC,W_BC)` on `μ_n` is near-balanced |
| **F2** | bad-count ceiling | `SYZ66.StripSyzygyControlledCeiling` (≡ `SYZ60Dictionary.BadCountCeiling` ≡ `SYZ57Transport.CountingDictionary`) | a stack with `≥ 6` bad scalars carries a syzygy among the G87 bridge functionals; does that syzygy keep the count `≤ 2³⁰`? |
| **F3** | union-rank realizability | `hrank` (SYZ42/SYZ43 `RealizabilityCore` residue): `finrank F (span F (range φ)) = 2(Ucard − k)` | the `Sᵢ`-anchored doubled shortenings of the witness family span their union |

**Claim of unity (§4):** F1, F2, F3 are three readings of one statement — the level-set / rank
behaviour of the witness-support family `{Sᵢ}` over `μ_n` — and SYZ49 identifies the common
governing quantity with the BGK additive-log-phase coincidence bound. This is the sense in which
they are one question, made precise below.

---

## 2. THE PROVEN SURROUNDING THEORY (the μ-basis classical chain — COMPLETE)

This is the campaign's largest self-contained mathematical deliverable: the **entire commutative-
algebra column** under F1's imbalance bound is now unconditional Lean theory. It is Mathlib-worthy
(the syzygy module of a coprime polynomial triple, from scratch). All files axiom-clean
(`propext, Classical.choice, Quot.sound` only; no `sorry`, no `native_decide`).

| step | commit | file | theorem (verbatim headline) | status |
|------|--------|------|-----------------------------|--------|
| SYZ61 | `9cca95f2a` | `_SYZ61MuBasisExistence.lean` | `syzygyKernel_free_rank_two` — `ker (syzygyMap f g h)` is `Module.Free` of `finrank = 2` | **UNCONDITIONAL** |
| SYZ62 | `623aaeb4b` | `_SYZ62GradedExchange.lean` | `span_of_gradedExchange` — `GradedExchange ⟹` `{e₁,e₂}` generate; product-degree grading `pdeg`, leading vector `lv` | reduces to `GradedExchange` |
| SYZ63 | `6074262f8` | `_SYZ63ExchangeStep.lean` | `exists_gradedExchange` / `syzygyKernel_muBasis_span` — `GradedExchange` **discharged** for every rank-2 submodule; μ-basis span is a theorem | **UNCONDITIONAL** |
| SYZ64 | `d401c974e` | `_SYZ64WindowBookkeeping.lean` | `twoRamp_windowKD` — `SYZ60.MuBasisWindowIso` / `SYZ44.TwoRamp` **discharged**; `pdeg_combo_eq` no-cancellation | **UNCONDITIONAL** |
| SYZ65 | `5c8782254` | `_SYZ65RankNullity.lean` | `rankNullity_windowKD`, `degree_sum_unconditional` — `SYZ44.RankNullity` **discharged** ⇒ degree-sum law `n₁+n₂ = d₀+d₁+d₂` **unconditional** | **UNCONDITIONAL** |

**Net:** SYZ44's `degree_sum_of_hilbert` (`δ₁+δ₂ = a+b+c`) — once conditional on two named textbook
Props `RankNullity ∧ TwoRamp` — is now **an unconditional theorem** given only coprimality and that
`dᵢ` is the generator degree. Combined with the concurrent-swarm **SYZ53** exact identity
`ι = ⌊(δ₂−δ₁)/2⌋` (`_SYZ53GeneratorGapCalibration.lean`, consuming only the degree-sum law), the
imbalance bound has been reduced to a **single crisp Hilbert–Burch statement**:

> **the μ-basis of a balanced pairwise-coprime band triple has generator gap `δ₂−δ₁ ≤ 1`.**

That is the *entire* open content of F1. Everything else on the Sylvester side is proved.

**Convention note (SYZ59, `840279493`):** two degree conventions coexist — PRODUCT-degree
(SYZ44/45/47, `δ₁+δ₂=S`, floor `δ₁ ≥ max(a,b,c)`) and COFACTOR-degree (SYZ55 prose, `δ₁=0` for a
constant syzygy). Bridge: `product_δ₁ = cofactor_δ₁ + max(a,b,c)`. The SYZ55 census "all realizable
witnesses have `δ₁=0`" reads in product convention as "floor **attained** (`δ₁ = max`)" — the SYZ47
floor is tight, not violated. Use the product convention when reasoning about the gap; do **not**
re-open the apparent SYZ55/SYZ47 contradiction (SYZ59 resolved it).

---

## 3. THE THREE FACES — exact statements, relations, empirical status

### F1 — imbalance / generator gap  (the Sylvester / spread branch)

- **Object:** `SYZ38.UniformSylvesterInjective K n k` = `SylvesterInjective` over every rate-`1/2`
  band-degree profile; SYZ39 characterizes it as a bounded-height **resultant non-vanishing of BGK
  type at `n = 2³⁰`**. It enters the assembled theorem as
  `StripMasterHypothesis''.uniformSylvester` (SYZ40/SYZ42).
- **Reduced open content:** the merged branch (`m ≤ 3`) is **unconditional**
  (`SYZ40.merged_branch_unconditional`). The spread branch (`m ≥ 4`) reduces — via the now-complete
  §2 μ-basis chain + SYZ53's `ι = ⌊(δ₂−δ₁)/2⌋` — to the **Hilbert–Burch gap** `δ₂−δ₁ ≤ 1` on
  band-realizable balanced interior profiles.
- **Empirical status:** SYZ53 `p`-scaling (`22100394c`) ran the mandatory rigorous prime sweep: the
  ι=2 balanced-interior excess **collapses** to the generic pencil floor `3` by `p* ∈ (197,1009)`
  and stays flat through `p = 2³¹`; at production field `P ~ 2¹⁵⁸ ≫ p*` the excess contributes
  **zero**. δ*=1/3 **survives**. The referee-measured near-balance gap is `δ₂−δ₁ ≤ 1`
  (one unit tighter than SYZ52's loose `δ₂ ≤ ⌈S/2⌉+1`). SYZ55's coverage census: **empty middle** —
  every band-realizable interior witness is either near-balance (`gap ≤ 3`, `ι ≤ 1`) or a
  constant-syzygy level-set witness (`δ₁ = max`, harmless floor lift); no intermediate case.
- **Not closed:** the gap-`≤1` bound is not a polynomial identity — SYZ45 showed it needs band
  realizability, not just coprimality. This is where BGK enters (§4).

### F2 — bad-count ceiling  (the census / transport branch)

- **Object:** `SYZ66.StripSyzygyControlledCeiling : ∀ u, 6 ≤ mcaBadCount … (u 0)(u 1) →
  mcaBadCount … (u 0)(u 1) ≤ 2³⁰`, at the strip predecessor radius `357913940/2³⁰ < 1/3`.
- **Equivalences (all axiom-clean, proved):**
  `StripSyzygyControlledCeiling → SYZ60Dictionary.BadCountCeiling`
  (`SYZ66.badCountCeiling_of_syzygyControlled`, case-splitting on the proven `≤ 5` cap)
  `↔ SYZ57Transport.CountingDictionary` (`SYZ60.countingDictionary_iff_badCountCeiling`)
  → the wire-(iv) census bound `SYZ57.stripCensusBound_of_master_hypothesis` → the δ* bracket.
  So F2 is **the entire transport wire (iv)** of the SYZ33 header, collapsed to one scalar residual.
- **What is PROVEN unconditionally (SYZ66, `f71099aa6`):** the **non-syzygy / independent-position
  regime is capped at 5**. `strip_independent_cap`: if the `r` G87 bridge functionals annihilating
  the nonzero syndrome pair are linearly independent, then `r ≤ 5` (arithmetic
  `r·(715827884−k)+1 ≤ 2(2³⁰−k)`, `k ≤ 2²⁹`; **sharp** — `r=5` realizable, `r=6` impossible).
  Dually `strip_count_ge_six_forces_syzygy`: any stack with `mcaBadCount ≥ 6` carries an explicit
  nontrivial syzygy among the functionals. So the **whole `2³⁰` budget lives in syzygy-carrying
  stacks**; the residual interval is exactly `[6, 2³⁰]`.
- **Empirical status:** SYZ29 accounting gives `#B ≤ #pencilPool + #fresh` with
  `#pencilPool ≤ Σ(n−sᵢ)` unconditional; forensics (SYZ55, `4e43268dd`) show large-field bad
  scalars are exactly the `3` structural core-forced pencil points (accidental parallelism vanishes
  `~1/p`). The gap is the **attribution** `#fresh = 0` + pool-sum `≤ 2³⁰` on the dependent bulk.
- **Not closed:** the "does a syzygy return a core-attributed pencil root" step (SYZ29 (d)); SYZ56
  proved the cross-witness **chaining** route to force it is a **NO-GO inside the strip**.

### F3 — union-rank realizability  (the `hrank` residue)

- **Object:** `hrank : finrank F (span F (range φ)) = 2(Ucard − k)` — the sole surviving analytic
  field of `SYZ42/SYZ43 RealizabilityCore` after SYZ43 auto-instantiated the other five from any
  over-budget `mcaEvent` stack via the G87 syndrome bridge. **Provably independent** of F1.
- **Structure (SYZ22):** `span (range φ) = ⨆ᵢ (Sᵢ-anchored doubled shortening)`, each block a full
  basis of its `S`-anchored doubled punctured dual (`block_source_dim_eq_shortening`); so `hrank`
  is **union-generation over the witness-support family `{Sᵢ}`**, `|Sᵢ| ≥ t`, pairwise-distinct
  (SYZ18).
- **What is PROVEN (SYZ56, `d995e2e3f`):** cross-witness algebra
  `cross_witness_u1_codeword_agreement` (distinct scalars force `u₁` near one codeword on `Sᵢ ∩ Sⱼ`)
  is genuine; but forcing a size-`≥k` rigidity region by **chaining** overlaps is a **NO-GO**: the
  `m`-fold minimal overlap `mfoldMin = n − m(n−t)` is **antitone** in `m` and already `< k` at the
  pairwise `m=2` in the strip (`no_rigidity_certificate_in_strip`). `hrank` does not discharge on
  this route.
- **Empirical status:** random families show large average overlaps `~t²/n ~ k` near `t = 3n/4`,
  but `hrank` is adversarial, so the worst-case pairwise bound governs.
- **Not closed:** `hrank` remains an independent realizability residual (not reducible to F1, not
  dischargeable by chaining).

---

## 4. THE SENSE IN WHICH THEY ARE ONE QUESTION

All three faces are readings of **the syzygy / level-set structure of the witness-support family
`{Sᵢ} ⊂ μ_n`**, and SYZ49 pins the common governing quantity:

- **SYZ49 (`_SYZ49CyclotomicGcd.lean`) — the BGK unification.** The balanced-interior obstruction
  (F1) reduces *exactly* to the max level set of the cyclic rational function
  `R(ω) = W_BC(ω)/W_AC(ω)` on `μ_n`, and level-set constancy **is literally the BGK additive-
  character wall**: over `𝔽_p`, `L(R(ω)) = Σ_{s∈S_BC} L(ω−s) − Σ_{s∈S_AC} L(ω−s) (mod p−1)` with
  `L =` discrete log. So `R` constant on a set `A` ⟺ the additive discrete-log-sum **phase** is
  constant on `A`. The μ-basis imbalance residual (non-BGK strip route, F1) and the BGK character-
  sum bound (CORE Paley/BGK route) are **the same object**.

The unity, face by face:

- **F1** is the *degree* structure of the rank-2 syzygy module of `(W_AB,W_AC,W_BC)` restricted to
  its `μ_n` level sets. The whole classical column is proved (§2); the residual `δ₂−δ₁ ≤ 1` is,
  via SYZ49, the additive-log-phase level-set coincidence bound — **BGK-literal**.
- **F2** asks whether a *syzygy among the witness-support functionals `φ`* (forced once `≥6` bad
  scalars appear) keeps the count in budget. The functionals are the `Sᵢ`-anchored doubled
  shortenings; a syzygy among them is a linear dependence over the same `{Sᵢ}` family — the rank/
  level-set structure again, one level up (SYZ56 makes the F3↔F2 link explicit: the overlap bound
  `cross_witness_region_card_ge` is cited in both).
- **F3** asks whether that same family `{Sᵢ}` **spans** (union-rank). Independence (F2's `≤5` cap)
  and generation (F3's `hrank`) are the two sides of the rank of the family; F2's proven
  independent-position cap and F3's proven chaining NO-GO are the **dual** unconditional facts,
  with the open bulk in both being the *dependent* regime `[6, 2³⁰]` / the adversarial worst case.

**Therefore:** the one question is the behaviour of the witness-support family `{Sᵢ}` over `μ_n` —
its degree-balance (F1), its dependence-count (F2), its span (F3) — and the single scalar that
governs all three is the **BGK additive-log-phase level set** (SYZ49). A proof of the BGK wall
closes F1 directly and constrains the syzygy structure feeding F2/F3; conversely any BGK-free route
would have to route through one of these three combinatorial faces. **CORE remains OPEN / ON-BGK.**

---

## 5. THE HONEST PRODUCTION WIRE LIST (what a prover must supply)

The conditional bracket `357913941/2³⁰ ≤ δ* ≤ 358612991/2³⁰` (ceiling half **unconditional** via
SYZ6; only the floor consumes hypotheses) is conditional on **exactly** these, and nothing hidden:

1. **F1** `StripMasterHypothesis''.uniformSylvester` — reduced open content = Hilbert–Burch gap
   `δ₂−δ₁ ≤ 1` (≡ `ι ≤ 1`) on band-realizable balanced interior; = BGK level-set (SYZ49). The
   entire μ-basis classical column beneath it is **proved** (§2).
2. **F2** `StripSyzygyControlledCeiling` (≡ `BadCountCeiling` ≡ `CountingDictionary`) — non-syzygy
   regime **proved** capped at 5; open = the dependent bulk `[6, 2³⁰]` = SYZ29 `#fresh = 0` +
   pool-sum, SYZ56-blocked on chaining.
3. **F3** `hrank` union-rank lower bound — independent realizability residue; chaining route
   **proved** NO-GO.
4. **Support control** — SYZ18 `twist_pair_indep` / `no_two_bad_scalars_share_witness` (disjoint
   supports) — **landed**, consumed as substrate.

Anything **not** on this list is proved theory: the merged branch, the degree-sum law, TwoRamp,
RankNullity, μ-basis freeness/rank/span/window count, the SYZ46 census-bridge wiring, the ceiling
half, the SYZ49 BGK identification, the SYZ58 rate-`1/4` curve-event scope barrier.

### Out of scope — do NOT re-attempt
- **Rate-`1/4` curve events (`ℓ>2`)** — SYZ58 (`31e50c2c7`): `epsMCACurve` is a distinct error
  function; a curve-channel bound would contradict the proven `3/8 ≤ mcaDeltaStar`. The higher
  pencil yield dissolves the SYZ5 integer-`D` floor only for the object the prize does **not**
  consume. Barrier, not a pin.
- **`hrank` via cross-witness chaining** — SYZ56 NO-GO (arithmetically obstructed in the strip).
- **The full dead ledger** — DISPROOF_LOG.md + `deltastar-DOSSIER-v3` §8.

---

## 6. Where to start (for the next prover)

- **If you attack F1 (recommended, non-BGK-looking but BGK-equivalent):** target `δ₂−δ₁ ≤ 1` on the
  balanced band-realizable interior. The classical apparatus is all in `_SYZ61…`–`_SYZ65…`;
  `_SYZ53GeneratorGapCalibration.lean` gives `ι = ⌊(δ₂−δ₁)/2⌋`. Remember SYZ49: it is the BGK
  level-set — a genuinely-BGK-free proof would be a breakthrough on the CORE wall.
- **If you attack F2:** the isolated residual is `StripSyzygyControlledCeiling`; the proven `≤5` cap
  (`SYZ66.strip_independent_cap`) is your base case; the open is core-attribution on `[6, 2³⁰]`.
- **If you attack F3:** `hrank`; chaining is dead — need a genuinely different span certificate.
- **Files:** `Frontier/_SYZ*.lean` (lane record); build with
  `scripts/pg-iterate.sh <file>` (lockless, ~8–30s). Never bare `lake build`.

---

*Cite this map as the primary entry point; cite `deltastar-DOSSIER-v3-2026-07-01.md` §6 (SYZ54 +
SYZ67 addenda) for the surrounding narrative and the CORE Paley/BGK line.*

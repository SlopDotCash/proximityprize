# δ\* #466 — SYZ56: the `hrank` residual via cross-witness chaining is a NO-GO (2026-07-11)

## Setup: what `hrank` is

SYZ43 (`_SYZ43AutoInstantiation.lean`) refactored the rate-`1/2` strip's `realizability`
obligation into `RealizabilityCore` (SYZ42) and proved that an actual over-budget `mcaEvent`
stack `(u₀, u₁)`, fed through the G87 syndrome bridge, **auto-instantiates five of the six
fields**. The sole surviving analytic field is the union-rank **lower bound**

```
hrank : finrank F (span F (range φ)) = 2 (Ucard − k)
```

on the G87 bridge functionals `φ`. G87's `plantable_span_cap` gives only the *upper* bracket
`finrank (span) + 1 ≤ 2(n − k)`. SYZ22 (`block_source_dim_eq_shortening`,
`doubled_shortening_dim`) proved each per-witness block is a **full** basis of its `S`-anchored
doubled punctured dual, so

```
span (range φ)  =  ⨆ᵢ (Sᵢ-anchored doubled shortening) ,
```

i.e. **`hrank` = union-generation over the `mcaEvent` witness-support family `{Sᵢ}`** — each
`|Sᵢ| ≥ t`, pairwise-distinct (SYZ18). `hrank` is provably **independent** of `uniformSylvester`
(SYZ42/SYZ43): it is its own realizability residual.

## The route probed: cross-witness chaining ⇒ `u₁` near a codeword

- **(a) cross-witness algebra.** For two witnesses with **distinct** scalars `γᵢ ≠ γⱼ`,
  differencing the explained lines on `Sᵢ ∩ Sⱼ` gives `(γᵢ − γⱼ)·u₁ = cᵢ − cⱼ`, so `u₁` agrees
  with the single codeword `(γᵢ − γⱼ)⁻¹ • (cᵢ − cⱼ) ∈ C` on all of `Sᵢ ∩ Sⱼ`.
- **(b) chaining.** If an over-budget family fused these regions into one of size `≥ k`, MDS
  rigidity would force `u₁` globally near a codeword ⇒ the near-degenerate *merged branch* ⇒
  `hrank` discharges off the strip.

## Verdict: (a) TRUE, (b) NO-GO — the band obstruction recurs one level up

**(a) is genuine algebra and is a direct corollary of SYZ18's `shared_witness_forces_pairJoint`
applied to the intersection.** Landed as `cross_witness_u1_codeword_agreement`.

**(b) does not close inside the strip.** The forced single-codeword agreement regions are the
**pairwise** overlaps, `|Sᵢ ∩ Sⱼ| ≥ 2t − n` (`cross_witness_region_card_ge`). To fuse two
pairwise codewords `cᵢⱼ`, `cᵢₗ` into one (so `u₁` agrees with a *single* codeword on a bigger
region) MDS rigidity needs them equal, hence agreeing on `≥ k` common points — an `m`-fold
intersection of size `≥ k`. But the minimal `m`-fold overlap is

```
mfoldMin n t m = m·t − (m−1)·n = n − m(n − t) ,   decreasing in m  (mfoldMin_antitone).
```

So the **largest** guaranteed region is the pairwise one at `m = 2`. In the strip
(`k = n/2`, `t < 3n/4`, i.e. `2t < n + k`) that is already `< k` (`pairwise_region_lt_k`), and
every deeper merge only shrinks (`chain_region_lt_k`, `no_rigidity_certificate_in_strip`).
**No chain of cross-witness merges ever certifies a size-`≥ k` region, so `u₁` is never forced
near a codeword, and `hrank` does not discharge on this route.**

Escalation table (probe `probe_syz56_hrank_cross_witness_chain.py`): the threshold `t` needed for
an `m`-fold overlap to reach `k` climbs `n·(1 − 1/2m) → n`, outside the strip for every `m`:

| n   | k  | strip t< | 2-fold t≥ | 3-fold t≥ | m→∞ t→ |
|-----|----|----------|-----------|-----------|--------|
| 32  | 16 | 24       | 24.00     | 26.67     | 32     |
| 64  | 32 | 48       | 48.00     | 53.33     | 64     |
| 128 | 64 | 96       | 96.00     | 106.67    | 128    |

(Random families *do* show large average overlaps `~ t²/n ~ k` near `t = 3n/4`, but `hrank` is an
existential/adversarial obligation, so the worst case governs — the pairwise bound.)

## What landed (`_SYZ56Hrank.lean`, axiom-clean)

- `cross_witness_u1_codeword_agreement` — (a), via SYZ18.
- `cross_witness_region_card_ge` — `|Sᵢ ∩ Sⱼ| ≥ 2t − n`.
- `mfoldMin_antitone` — the merge escalation is antitone in `m` (chaining gives no gain).
- `pairwise_region_lt_k`, `chain_region_lt_k`, `no_rigidity_certificate_in_strip` — the NO-GO.
- `strip_hypothesis_iff_three_quarter` — `2t < n + k ⇔ t < 3n/4` at `n = 2k`.

Axioms: `propext, Classical.choice, Quot.sound` only. No `sorry`, no `native_decide`.

## Honest status

No `δ*` gain. `hrank` remains **open** — an independent realizability residual, not reducible to
`uniformSylvester`, and *not* dischargeable by cross-witness chaining (arithmetically obstructed
in the strip). The master hypothesis stays at two open inputs (`uniformSylvester` + the `hrank`
union-rank lower bound), exactly as SYZ42/SYZ43 recorded. The cross-witness route is now closed
with a proof, not left as a hope.

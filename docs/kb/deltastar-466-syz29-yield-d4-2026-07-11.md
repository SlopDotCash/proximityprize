# δ\* / #466 — SYZ29: the pencil-yield law (honest accounting) + the D≥4 gluing formula

Date: 2026-07-11
File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ29YieldLawD4Gluing.lean`
Probes: `scripts/probes/probe_syz29_d4_defect_formula.py` (part ii, exact defect formula),
`scripts/probes/probe_syz29_yield_law_accounting.py` (part i, honest global accounting)
Branch: `codex/syz29-yield-law-d4-gluing` (off `fork/research/proximity-prize` @ 5cd0d2d52)

SYZ28 left the two last strip residuals as *named* (word-level verified, Lean not in hand):
(i) the pencil-yield law, (ii) the D≥4 over-budget gluing law. SYZ29 makes both precise, proves
the parts that are theorems, and pins the exact residual that remains.

## Part (i) — the honest global accounting for the pencil-yield law

### The naive statement is NOT a law; the honest one is `#bad ≤ ∑(n−sᵢ) + #fresh`

A bad scalar γ carries an mca-witness set `Sᵧ` (line explained on `Sᵧ`, `¬ pairJointAgreesOn`).
SYZ18 already gives the injection γ ↦ Sᵧ (distinct bad scalars ⇒ distinct witness sets — the
SYZ22 budget engine). The *pencil* refinement (SYZ2/SYZ3): a bad γ **attributed** to a
degenerate core C (local codeword pair `(v₀,v₁)`) satisfies `d₀(x)+γ·d₁(x)=0` for some `x∉C`,
`d₀=u₀−v₀`, `d₁=u₁−v₁`, so `γ=−d₀(x)/d₁(x)` lies in the **pencil image** of C, of size ≤ n−|C|.

**The honest subtlety (probe-confirmed).** A bad scalar's witness need NOT contain a core on
which the *pair* jointly agrees — the core is where the *line* agrees, not the pair. The
operational "witness ⊇ pair-agreement core" attribution detector is **vacuous**
(`probe_syz29_yield_law_accounting.py`, n=16, GF(17), SYZ28 witness, 25 pencil + 25 adversarial
stacks): `#fresh = #bad` in every stack. So `#bad ≤ ∑(n−sᵢ)` cannot be *derived* from crude
core-containment — it must take attribution as a hypothesis. Yet the bound itself held with
**zero violations**: `#bad ≤ ∑(n−sᵢ) = 15 = n−1` on every pencil stack (max #bad = 13 < 15) and
every adversarial random stack (`#bad > n−1` never occurred).

### The honest decomposition (the answer worked out)

```
#bad  =  #(pencil-attributed)  +  #fresh
#(pencil-attributed)  ≤  ∑ᵢ (n − sᵢ)        [pencil-image union bound — a theorem]
#fresh                =  #(B \ pool)          [the residual; probe = 0]
```

The middle line is `bad_card_le_pool_of_attribution`: *given* the attribution hypothesis (every
bad γ has a core i and a witness point `x ∈ Tᵢ=Cᵢᶜ` with `d₁ᵢ(x)≠0`, `d₀ᵢ(x)+γ·d₁ᵢ(x)=0`), then
`#B ≤ ∑ᵢ|Tᵢ| = ∑ᵢ(n−sᵢ)`. The bottom line is `bad_card_le_pool_add_fresh`, an *unconditional*
split `#B ≤ #P + #(B\P)`. Composed with SYZ28's strict-interior yield cap
(`bad_card_le_budget_of_attribution_d3`): an *attributed* strictly-interior over-budget D=3 stack
obeys `#bad ≤ n−1` — the SYZ22 budget, zero slack. The residual is exactly **attribution
completeness** (`#fresh = 0`), probe-pinned but not read off geometry.

## Part (ii) — the exact D≥4 defect formula: VERDICT CONFIRMED

The SYZ28 D=3 formula is the `m=2` case of the **partition-envelope subadditivity defect**:
for a set-partition P of the cores into blocks,
`dim(joint span) ≤ ∑_{B∈P}(|⋃B| − k)` (the block spans lie in `A_{⋃B}`), hence

```
d  =  max(0, (n − k) − min over set-partitions P of ∑_{B∈P}(|⋃ B| − k))
```

`probe_syz29_d4_defect_formula.py` (n∈{16,20,24}, D∈{3,4,5}, ≈45k full covers, d recomputed
over p∈{101,1009,65537}, min over ALL partitions):

| n | D | tested | formula-agree & field-indep | over-budget d>0 | min(env−(n−k)) |
|---|---|---|---|---|---|
| 16 | 3 | 2368 | 2368 | 29 | **−1** |
| 16 | 4 | 3391 | 3391 | **0** | **0** |
| 16 | 5 | 3816 | 3816 | 0 | 0 |
| 20 | 3 | 2148 | 2148 | 4 | −1 |
| 20 | 4 | 3414 | 3414 | 0 | 0 |
| 20 | 5 | 3816 | 3816 | 0 | 0 |
| 24 | 3 | 1721 | 1717 (4 small-char) | 14 | −1 |
| 24 | 4 | 3139 | 3139 | 0 | 0 |
| 24 | 5 | 3709 | 3709 | 0 | 0 |

- **Formula is exact and field-independent for D=3,4,5.** The only 4 "mismatches" (n=24 D=3) are
  `p=101`-only small-characteristic accidents (`d=[1,0,0]` over the three primes) where the
  field-independent d is 0, matching the formula — not genuine.
- **D≥4 over-budget ⇒ d=0 in every trial, with `min(env − (n−k)) = 0` exactly** — the minimizing
  partition envelope count is *exactly* the ceiling n−k, never below. Contrast **D=3**: slack −1
  (one below) is the SYZ28 crack. This is the sharp arithmetic reason D≥4 cannot deficient.

### What this reduces the D≥4 gluing to

`d = 0` needs: (a) the formula's **≤ direction** `d ≤ defect` (generation reaches the
min-envelope — SYZ25/26 MDS-genericity, unchanged residual), and (b) the arithmetic
`min_P ∑(|⋃B|−k) ≥ n−k` for over-budget D≥4. The whole-cover partition (m=1) already realizes
`∑ = |⋃all|−k = n−k` (a full cover), so the min is ≤ n−k always; the claim is that no finer
partition beats it. The **≥ direction** (envelope confinement, field-independent) is proven here
in full for arbitrary D and any block family.

## Proven verbatim in Lean (all axiom-clean: propext/Classical.choice/Quot.sound; no sorry, no native_decide)

Part (i):
1. `pencilImage_card_le` — one core donates ≤ |T| = n−|C| scalars (`Finset.card_image_le`).
2. `mem_pencilImage_of_root` — a pencil root `d₀(x)+γd₁(x)=0`, `d₁(x)≠0`, `x∈T` gives
   `γ=−d₀(x)/d₁(x) ∈ pencilImage` (`eq_div_iff`, `linear_combination`).
3. `bad_card_le_pool_of_attribution` — attribution ⇒ `#B ≤ ∑ᵢ(n−sᵢ)` (biUnion + `card_biUnion_le`).
4. `bad_card_le_pool_add_fresh` — unconditional split `#B ≤ #P + #(B\P)`
   (`card_inter_add_card_sdiff`).
5. `bad_card_le_budget_of_attribution_d3` — attributed strict-interior over-budget D=3 ⇒
   `#B ≤ n−1` (composes 3 with `SYZ28.d3_yield_cap_strict_interior`).

Part (ii):
6. `finrank_partialSup_le_sum_envelopes` — `finrank(⨆ⱼBⱼ) ≤ ∑ⱼ finrank Bⱼ`, any finite family,
   any field (induction via `finrank_sup_add_finrank_inf_eq`).
7. `envelope_family_forces_deficiency` — confinement to m block envelopes with total count
   `< finrank W` ⇒ `partialSup A D ≠ W`. The general-D `≥` direction of the formula (SYZ28's
   `envelope_forces_deficiency` is the D=3, m=2 instance).
8. `d4_pairing_envelope_ge` — over-budget D=4 band ⇒ pairing envelope `(u−k)+(s₃−k)+(s₄−k) ≥ n−k`
   (omega, with pair-union floor `s₁+s₂ ≤ u+k`).
9. `d4_over_budget_deficiency_zero` — `d ≤ defect ≤ 0 ⇒ d = 0` (the packaged reduction, omega).
10. Concrete `decide` witnesses `syz29FourCover` (n=16, 4×11-cores, full cover, over-budget
    12≥8, whole envelope = n−k = 8).

## Strip-theorem scoreboard — remaining named lemmas for the unconditional rate-1/2 strip

Closed / proven (SYZ22–29): budget `|U|≤n−1`; span ceiling; clean gluing δ≤1/4; D=2-under-budget
& D≥3 forcing; D=3 envelope classification + strict-interior yield cap; pencil-image bound +
general-D envelope confinement + D≥4 reduction (this file).

Remaining named lemmas for **full unconditional strip closure at rate 1/2**:
1. **Attribution completeness** — every mca-bad scalar of a band stack is pencil-attributed to a
   cover core (`#fresh = 0`). [probe: 0; part-(i) residual]
2. **Formula ≤ direction** — `d ≤ min-envelope defect` (joint span reaches the min-envelope;
   SYZ25/26 MDS/generation genericity). [probe-exact for D=3,4,5]
3. **All-partition minimization (D≥4 over-budget)** — `min_P ∑(|⋃B|−k) ≥ n−k`. [probe: slack
   exactly 0; pairing + whole-cover cases proven here]

For **production n = 2³⁰** the residual is the *same three* named lemmas — every SYZ29 statement
is n-uniform (omega / dimension counts), so no per-n gap is added. Unconditional δ\* status
untouched; strip NOT falsified.

## Reuse hooks

- `pencilImage` + `mem_pencilImage_of_root`: any pencil-root count reduces to `card_image_le`.
- `finrank_partialSup_le_sum_envelopes` / `envelope_family_forces_deficiency`: the general-D
  envelope machinery — the `≥` direction of any partition-envelope defect formula, field-free.
- The probe's `min over set-partitions` envelope evaluator (`set_partitions`, `envelope_count`,
  `min_envelope`) is the exact-defect oracle for any D.

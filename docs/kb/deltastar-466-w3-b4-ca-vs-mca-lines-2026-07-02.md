# #466 Lane W3 / B4: the CA ⇒ MCA collapse at LINES — localized, floored, and its obstruction exhibited (2026-07-02)

First campaign movement on the named open problem (dossier v3 §6, Crites–Stewart flag /
ABF26 §5): *"correlated agreement ⇒ mutual correlated agreement, unknown even for lines."*

**Deliverables**
- Lean brick (axiom-clean, `[propext, Classical.choice, Quot.sound]`, 0 `sorry`):
  `ArkLib/Data/CodingTheory/ProximityGap/Frontier/CAtoMCALineLocalization.lean`
- Probe (exact per-scalar enumeration, brute-force cross-validated):
  `scripts/probes/probe_466_ca_vs_mca.py` → `scripts/probes/_out_466_ca_vs_mca.txt`

## 1. The localization identity: B4 at lines *is* one named quantity (Lean, proven)

`epsMCA_eq_max_epsCA_jointlyProximateContribution` (any linear code, any radius):

```
ε_mca(C, δ) = max ( ε_ca(C, δ, δ) , jointlyProximateContribution C δ )
```

The `≤` half was in-tree (`Errors.lean`); the brick adds the `≥` half
(`epsCA_le_epsMCA` + `jointlyProximateContribution_le_epsMCA`), upgrading the bracket to an
identity. **Consequence: the CA ⇒ MCA collapse at lines holds with constant κ iff
`jointlyProximateContribution C δ ≤ κ · ε_ca(C, δ, δ)`.** All open content of B4-at-lines
now lives in a single supremum over *jointly δ-close* stacks.

## 2. The per-scalar trichotomy (Lean, proven; probe-verified exactly)

`line_close_imp_mcaEvent_or_jointProximity` — the shape B4 asks for:
**CA-bad ⟹ MCA-bad ∨ joint-agreement-everywhere**, and the third case is *classified*: it
is precisely `jointProximity` of the stack (the γ-independent condition zeroing the `ε_ca`
body). On any NON-jointly-close stack the identity is exact scalar-by-scalar
(`mcaEvent_iff_line_close_of_not_jointProximity`): a scalar is MCA-bad **iff** its line
point is δ-close.

Probe: on **every** non-joint stack tested (random / monomial / designed, n = 8 and 16,
two primes each, window-interior a), #CA-bad = #MCA-bad with gap ≡ 0, and the fast
enumeration engine matches an independent brute-force per-γ list decoder at n = 8 (16/16
config matches). The CA-vs-MCA gap at lines is **empty off the joint locus** — the collapse
question is purely about jointly-close stacks.

## 3. The floor (Lean, proven): the transfer can never be lossless

`jointlyProximateContribution_ge_of_supported_stack` / `epsMCA_ge_of_supported_stack`:
a jointly-close stack in shifted normal form (rows supported on `E`, `|Eᶜ| ≥ (1−δ)n`, no
nonzero codeword vanishing off `E` — for RS automatic whenever `|Eᶜ| ≥ k`, i.e. the entire
window `δ < 1−ρ`) fires `mcaEvent` at every distinct **ratio scalar** `γ = -u₀ i/u₁ i`
(`i ∈ E`, witness = zero codeword on `insert i Eᶜ`). Generic values give `⌊δn⌋` of them:

```
jointlyProximateContribution(C, δ) ≥ ⌊δn⌋ / |F|   throughout the window.
```

So the in-tree UDR ceiling `⌊δn⌋/|F|` is TIGHT where it applies, and any CA ⇒ MCA transfer
at lines carries at least this additive `~δn/q` term. Probe: designed sparse stacks fire
exactly their `e = ⌊δn⌋` ratio scalars at every below-gate slice.

## 4. The below-gate ratio-scalar law (Lean, proven; gate empirically SHARP)

New in this round (`badScalar_is_ratio_of_supported_below_gate`,
`badScalar_card_le_support_of_below_gate`): for an `E`-supported stack over a code whose
nonzero codewords have ≤ z zeros (RS_k: z = k−1), **below the excess gate**
`z + |E| < (1−δ)n` every MCA-bad scalar is a ratio scalar and the bad set injects into `E`
(`#bad ≤ |E|`, via `NoZeroSMulDivisors`). Together with §3: below the gate the per-stack
bad set is *exactly* the ratio-scalar set. For tight support `|E| = ⌊δn⌋` the gate reads
`a > (n+k−1)/2` — the UDR line — but the law extends INTO the window for stacks of small
support.

Probe sharpness check (per prediction, before measurement):
- k=2, a=5, e=3: gate holds (2 > 1) → **zero excess fires found** (both primes). ✓
- k=3, a=5, e=3: gate boundary (a−e = k−1 = 2) → the stochastic hill-climb finds
  **exactly one** excess fire (J = 4 vs e = 3, at p = 4153; the p = 4129 climb stayed at
  J = 3 — search is heuristic, existence is what matters). ✓ sharp at the first slice
  where it can fail.
- everything deeper in-window: excess fires everywhere (below).

## 5. B4's obstruction, exhibited: the excess channel (probe; the open quantity)

Past the gate, *nonzero*-codeword witnesses (vanishing on part of `Eᶜ`, agreeing with the
line on part of `E`) fire far beyond the floor. Max #MCA-bad J on JOINT stacks vs the floor
e = ⌊δn⌋ vs max #CA-bad on NON-joint stacks (identical at both primes tested unless noted):

| n | k | a | δ | e=⌊δn⌋ | J (joint) | zero-type / excess | CA_max (non-joint) | J/CA_max |
|---|---|---|---|---|---|---|---|---|
| 8 | 2 | 3 | 5/8 | 5 | 45 | 5 / 40 | 56 | 0.80 |
| 8 | 2 | 4 | 1/2 | 4 | 8 | 0 / 8 | 9 | 0.89 |
| 8 | 2 | 5 | 3/8 | 3 | **3** | 3 / 0 | 8 | 0.38 |
| 8 | 3 | 4 | 1/2 | 4 | 57 | 4 / 53 | 70 | 0.81 |
| 8 | 3 | 5 | 3/8 | 3 | 4 (p=4153; 3 at p=4129) | 3 / 1 | 8 | 0.50 |
| 16 | 4 | 5 | 11/16 | 11 | 4199–4204 | ~11 / ~4190 | 4238–4247 | 0.99 |
| 16 | 4 | 6 | 10/16 | 10 | 16 | 0 / 16 | 89 | 0.18 |
| 16 | 4 | 7 | 9/16 | 9 | **16** | 0 / 16 | 9 (family-limited) | 1.78* |

Structure of the strongest excess family: at n=16, a ∈ {6,7}, the maximizers are
**jointly-explainable monomial stacks** (e.g. (X⁹, X¹⁰), (X⁸, X⁹)) firing **exactly n = 16**
scalars, ALL excess-type (zero ratio-type) — the antipodal/parity witness structure (same
mechanism family as the P5/SumsetExtremal spread kill). Deeper in the window J explodes
(57 at n=8 vs e=4; ~4200 at n=16, a=5).

## 6. Collapse verdict so far (honest)

- **Not refuted**: the only within-probe ratio > 1 (16/9 at n=16, a=7, both primes) is
  against a *family-limited* CA side: the P5-referee lane already exhibits non-joint stacks
  with ≥ 21 bad scalars at the same (n,k,a,q) (`deltastar-466b-p5-referee-2026-07-01.md`),
  which restores JPC/ε_ca ≤ 16/21 < 1 there. No tested slice certifies ε_mca > ε_ca.
- **Not proven**: J tracks CA_max at 0.8–0.99 in the deep window; nothing here bounds the
  jointly-proximate contribution above the gate. A κ = O(1) collapse at lines is CONSISTENT
  with all data and is the natural conjecture (label: CONJECTURE):
  `jointlyProximateContribution(RS, δ) ≤ ε_ca(RS, δ, δ)` for all window δ — i.e. κ = 1,
  i.e. **ε_mca = ε_ca at lines** (per §1 identity). Attack surface for refutation: make the
  excess channel (J = n monomial family) beat the best non-joint line; attack surface for
  proof: every excess witness set carries ≤ 1 bad scalar (`unique_bad_gamma_common_witness`),
  so J ≤ #{admissible witness sets}; count witness sets of jointly-close normal forms.
- The J = n exactness at n=16 (a=6,7, all four prime×a slices) suggests a per-domain-point
  bijection for the antipodal monomial family — unproven (CONJECTURE), one fire per
  domain coordinate.

## 7. Pointers

- Lean: `Frontier/CAtoMCALineLocalization.lean` — 13 theorems, all axiom-clean; consumes
  `Errors.lean` (`mcaEvent`, `jointProximity`, `epsCA/epsMCA`, `jointlyProximateContribution`)
  and is consistent with `MCAWitnessSpread.unique_bad_gamma_common_witness` (the
  witness-spread obstruction: our excess fires all use *distinct* witness sets, as they must).
- Probe regime discipline: μ_n proper (m = (p−1)/n ≥ n³), p ≡ 1 mod n, p ≥ n⁴, two primes
  per n (4129/4153; 65617/65633), generalized-Fermat p=65537 skipped and flagged,
  X^{n/2}-correlated directions flagged inline.
- Caveats: J values from finite families + hill-climbs are LOWER bounds on the true JPC
  numerator; CA_max likewise on ε_ca. Only the ≡0 gap on non-joint stacks and the
  zero-excess claim at (k=2, a=5) are exhaustive over the tested stack lists.

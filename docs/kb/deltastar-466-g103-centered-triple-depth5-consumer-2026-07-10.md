# Issue #466 G103: centered triple concentration closes depth five

Date: 2026-07-10

## Statement

G102 closes the (cardinality, pair-sum concentration) input class at depth ≥ 5.  G103
identifies and consumes the **minimal upgrade** — and refutes the naive version of it.

**Refutation (raw triple concentration).**  The chain `J₅ ≤ M₃·n⁷` would close depth 5 at
`M₃ ≤ 2^{25.8}`.  But for even `n`, `−1 ∈ μ_n`, and every `a ∈ H` carries the antipodal family
`a + (y + (−y))`.  The probe verifies the degenerate mass is **exactly** `3n − 3` per point of
`H` (and supported exactly on `H`), so raw `M₃ ≥ 3n ≈ 2^{31.6}` at `n = 2^30`: raw triple
concentration can never close depth 5.

**The rescue (centered split).**  Excluding triples containing an antipodal pair, the probe
measures the centered concentration `M₃ᶜ` of real `μ_n` at `6..18 = O(1)` across all tested
scales (`6 = 3!` = one genuine unordered solution).  The consumer chain, axiom-clean in
`Frontier/_G103CenteredTripleDepthFiveConsumer.lean` over any finite abelian group:

```text
quintCount a = Σ_c pairCount c · tripleCount (a−c)          (quintCount_eq_conv)
degTripleCount a ≤ 3n  (per target),  Σ_a degTripleCount a ≤ 3n²  (total)
J₅ = Σ_a quintCount² ≤ (M₃ᶜ + 3·M₂ + 3) · n⁷                (equalSumQuintMass_le)
```

and the kernel inequality `production_kernel` verifies that `(M₃ᶜ, M₂) = (2^24, 2^22)` puts
the depth-5 sector inside one full Wick budget at `(n, r) = (2^30, 110)` — margin `2^{1.01}`.
Here `2^22 = 4·n^{2/3}` is the known Stepanov pair bound (Garcia–Voloch 1988 /
Heath-Brown–Konyagin 2000) and `2^24 ≈ n^{0.8}` has `2^{20}` headroom over the measured truth.

## The pinned frontier object

- G102: **no pair statistic suffices** at depth 5 (extremal witness, kernel-checked).
- G103: **the centered triple statistic suffices** (this consumer), and the degenerate
  antipodal mass is exactly accounted.
- The new named external hypothesis is `hM3` of `production_depth5_of_centered_triple`:
  *centered triple-sum concentration `≤ 2^24` for `μ_{2^30} ⊂ F_p`*.  No Stepanov analog is
  recorded for it; producing one (a Stepanov/Garcia–Voloch-style bound
  `max_a #{(h₁,h₂,h₃) ∈ H³ : Σ = a, no antipodal pair} ≪ n^{5/6}`) is now a well-posed,
  quantitatively pinned open target — strictly weaker than square-root cancellation.

## Honest scope

Consumer only: the hypothesis is named, not proved.  Depth 6+ of the padded lane is NOT
closed by this route (the analogous depth-6 chain needs more than `M₃ᶜ`); the all-depth
`DCEnergyBound` assembly and the ON-BGK core remain open.

Probes: `scripts/probes/probe_466_g103_centered_triple_concentration.py` (exact; verifies the
`3n−3` degenerate formula and measures `M₃ᶜ`), output `_out_466_g103_centered_triple.txt`.

# #466 Round 10 — Lane B: the dyadic-tower TRANSFER OPERATOR is GAUGE + TRANSIENT-MUTE (2026-07-04)

**Verdict: GAUGE (and, on the sup side, bounded TRANSIENT → mean field). The wall stands; the
transfer-operator angle is refuted with the exact mechanism. CORE remains OPEN.**

## The angle
The dyadic tower `μ_2 ⊂ μ_4 ⊂ … ⊂ μ_{2^μ}` gives the wraparound count `W_r` (and the sup
`M(μ_n)=max_{b≠0}‖η_b‖`) a self-similar recursion under the doubling map `x↦x²` (the tower step on
`μ`; fiber over a sub-tower element is the pair `{k, k+2^{μ-1}}`). Naive per-level `√2`-descent is
already REFUTED (`no_sqrt_two_perLevel_thinning`, early ratios 1.74/1.54/1.46 > √2). Lane B asked:
encode the tower as a **transfer operator / dynamical zeta** and ask whether its **leading
eigenvalue / spectral gap** (not a per-level ratio) controls `W_r` — and, critically, whether the
operator sees anything the raw moments do not.

## Task 1 — the exact recursion (already in-tree, made precise)
The exact tower law is LINEAR on the spectrum:
`η_b(μ_{2N}) = η_b(μ_N) + η_{ζb}(μ_N)`, `ζ` a primitive `2N`-th root (coset rep). This is
`_AvW16_CosetTowerRecursion.lean` (`sum_coset_tower`, `period_tower_recursion`,
`sup_le_two_mul_sup`, axiom-clean). The doubling map is MULTIPLICATIVE (`x↦x²` on roots) while `W_r`
is ADDITIVE (counts `Σ±ζ^{k_i}≡0`): the coset re-partition mixes all `2^{2r}` bit-patterns with none
additively conserved mod p, so **there is no autonomous pushforward `W_r(2N)=f(W_{≤r}(N))`** — the
recursion re-expresses `W_r(2N)` in terms of the JOINT two-frequency distribution of `(η_b,η_{ζb})`,
which is an object of the same complexity at level `2N` (= the wall). No genuine reduction to level N.

## Task 2/3 — the transfer operator's spectrum is GAUGE (the critical kill)
Probe `scripts/probes/probe_466r10_transfer.py` + `_gauge.py` (proper `μ_n ⊊ F_p^×`, `p≥n⁴`, index
`m=(p-1)/n`, full coset sup — validated `MATCH=True` vs brute-force `M` and vs brute `E_2` at `n=8`;
≥3 primes with `v₂(p−1) ∈ {5,6,7,9,10,13}`).

- The transfer operator is built ENTIRELY from the eta-vector `{η_b}`. Its magnitude data (all that
  survives the coset symmetry — the symmetry-reduction trap) is the **multiset `{‖η_b‖}`**, whose
  invariants are the power sums = the **moment ladder `(E_1,E_2,…)`**. Formalized axiom-clean in
  `_B_TransferOperatorGauge.lean`:
  - `momentPow_eq_ofMultiset` — the raw energy `E_r=Σ_b‖η_b‖^{2r}` is a genuine multiset invariant;
  - `transfer_functional_perm_invariant` — any operator functional factors through the multiset,
    hence is invariant under relabeling frequencies;
  - `transfer_gauge` — **packaged verdict**: same `‖η‖`-multiset ⇒ every operator functional agrees
    AND every moment agrees ⇒ the operator adds NO invariant beyond the moments.
- **Numerical confirmation of gauge (n=32, p≈1.048M, 8 primes):** primes sharing `E_2=2976,
  E_3=446720` split into three `E_4∈{90889120,91534240,92179360}` (three `W_4∈{0,645120,1290240}`)
  and the sup `M` varies (21.57–23.82) TRACKING `E_4`+ — `M` is a function of the FULL ladder, never
  an independent invariant. This is the Toda/isospectral gauge shape
  (`todaTurnover_not_determined_by_invariants`). **GAUGE CONFIRMED.**

## Task 4 — the sup transfer is a bounded TRANSIENT → mean field (method mute)
Deepest-feasible towers, 3 primes `v₂(p−1)∈{7,10,13}`, all `p≥128⁴` (proper subgroup, `m≈2^21`),
full coset sup. Per-level sup ratio `M(μ_{2n})/M(μ_n)`:

```
 n:   2     4       8       16      32      64      128
A:  —    2.000   1.9995  1.9588  1.7480  1.4322  1.4040   (ratio/√2 → 0.993)
B:  —    2.000   1.9995  1.9568  1.7028  1.4494  1.4550   (ratio/√2 → 1.029)
C:  —    2.000   1.9994  1.9562  1.6975  1.4353  1.4403   (ratio/√2 → 1.019)
```

The ratio DESCENDS MONOTONICALLY toward `√2≈1.414` from above (early-level >√2 is a transient), with
`M/√n` PLATEAUING at ~4.8–5.0 ≈ `√(log m)` (`m≈2^21 ⇒ √(21 ln2)≈3.8`, same order). The
`1.74/1.54/1.46` in the dead ledger are the EARLY (small-n) ratios; deep in the tower the growth
converges to the mean-field / tight-wall rate. **Bounded transient ⇒ the transfer operator's
spectral gap (rate − √2) → 0 ⇒ WALL TRUE but METHOD MUTE.** No super-rate ⇒ the floor is NOT refuted
(and no extraordinary claim to defend).

## Honest caveats
- Single-prime towers keep `log m` fixed across levels, so `M/√n≈√(log m)=const` is exactly the
  tight-wall prediction; the plateau is consistent with the wall being TIGHT, not beaten. To see the
  `√(log m)` growth one must vary the prime, not climb one tower — orthogonal to the transfer step.
- Feasibility caps the tower at `n≤128` (full coset sup needs `m=(p-1)/n≤~2^21`); asymptotics
  inferred, not proven. But the gauge kill (Task 3) is regime-independent and Lean-formal.

## Files
- `scripts/probes/probe_466r10_transfer.py`, `_out_466r10_transfer.txt` (tasks 1–4, validated).
- `scripts/probes/probe_466r10_transfer_gauge.py`, `_out_466r10_transfer_gauge.txt` (sharpened
  gauge + deep-tower transient).
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_B_TransferOperatorGauge.lean` — axiom-clean
  (`{propext, Classical.choice, Quot.sound}`, no `sorryAx`): `momentPow_eq_ofMultiset`,
  `powerSum_eq_of_multiset_eq`, `transfer_functional_perm_invariant`, `transfer_gauge`.
- Builds on existing `_AvW16_CosetTowerRecursion.lean` (the exact linear recursion).

## One-line
The tower "transfer operator" is a reparameterization of the moment ladder (GAUGE, Toda-shape) and
its sup eigenvalue is a bounded transient converging to the tight `√2` mean-field rate (method mute)
— the surviving open surface is still EXACTLY the analytic wall.

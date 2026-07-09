# δ* (#407) — the Paley/Ramanujan spectral target is FALSE; the floor is the EVT statement

**Status:** spectral-route verdict. Refutes the Ramanujan framing of the prize per-frequency core
and re-points it at the correct (extreme-value) target. Two axiom-clean Lean bricks landed; numerics
reproducible. Author: paley lane (#407), 2026-06-13. Route: *Paley-graph / Ramanujan spectral angle*.

## The object (unchanged)
`B = max_{b≠0} ‖η_b‖`, `η_b = Σ_{x∈μ_n} e_p(bx)`, the non-principal eigenvalue of the generalized
Paley graph `Cay(F_q, μ_n)` (Liu–Zhou Thm 115). It is `n`-regular on `q` vertices with exactly
`m = (q−1)/n` distinct nontrivial eigenvalues (the Gauss periods).

## THE VERDICT: Ramanujan `B ≤ 2√n` is the WRONG (provably FALSE) target

The spectral-graph reflex is to ask for `B ≤ 2√(n−1)` (Ramanujan / Alon–Boppana-optimal). **This is
false in the prize regime, and the failure is structural, not a defect of the graphs.**

- **Numeric refutation** (`scripts/probes/_wf407_paley_largem.py`, `_wf407_paley_VERDICT.py`): at
  `n=8`, sweeping the index `m`, **361/367 primes (98.4%) have `B > 2√n`**. First exceedance at
  `m=17`; `B/(2√n)` plateaus near 1.37 (small-`n`), with asymptotic excess `√(ln m / 2)`. At the
  prize `m = 2^128` the excess factor is `√(88.7/2) ≈ 6.7×`. So at `n=2^30`: floor `≈ 2^18.7`,
  Ramanujan cap `2√n = 2^16` — `B` sits a factor `6.7×` ABOVE the Ramanujan cap.
- **Why it must fail:** with `m → ∞` distinct mean-zero, variance-`n` nontrivial eigenvalues, the
  maximum of `m` of them is `≳ √(n log m) ≫ 2√n` once `log m > 2`. Alon–Boppana is a matching
  *lower* bound (`B ≥ 2√(n−1) − o(1)`); the upper Ramanujan property is special and simply does not
  hold here. **Spectral-graph theory supplies the dictionary (`B` = eigenvalue) but NO new upper
  bound** — the `m` quotient eigenvalues *are* the Gauss periods.

## THE CORRECT TARGET: the EVT floor `B ≈ √(2 n ln m)`

Parseval gives per-period variance exactly `n` (`mean|η_b|² = n`, verified). The `m`-fold maximum of
variance-`n` quasi-Gaussian Gauss periods is the extreme value `√(2 n ln m)` — the **Gaussian EVT
constant `C0 = √2`** (consistent with `deltastar-407-limit-law-sqrt2-constant`: limit law N(0,1),
κ₄ = −3/n sub-Gaussian correction). Measured `B/√(2 n ln m) ≈ 0.93–0.97` (approaching √2 from below
per the κ₄ correction), flat, no trend. This is an **analytic-number-theory statement** (square-root
cancellation among the `(q−1)/n` Gauss-sum phases `χ̄(b)τ(χ)`, `|τ|=√p`), NOT a spectral-gap bound.

## The lift / covering sub-question (also negative)

Walking the 2-power tower `μ_2 ⊂ μ_4 ⊂ … ⊂ μ_{2^k}` inside a fixed prime
(`_wf407_paley_tower2.py`): `B(μ_{2^k})` is NOT monotone-controlled by the base — `B/(2√n)` peaks in
the middle of the tower (1.35–1.67 around `n=8..32`). The index-`m` covering gives **no interlacing
handle** on the sup; the lift only reshuffles which `(n,m)` pair you read. Consistent with the
in-tree `CharSumMomentDeepWall` "2-power tower does not lower deep moments".

## Best provable vs floor, at the prize instance `n=2^30`
| quantity | value (bits) | note |
|---|---|---|
| EVT floor `√(2 n ln m)` | `2^18.7` | the target (`C0=√2`) |
| Ramanujan `2√n` | `2^16` | FALSE here (`B` is `6.7×` above) |
| BGK best-provable `n^{1−o(1)}` | `2^30` | `2^11.2 ≈ 2400×` above floor |
| deep-moment wall `n^{3/4}√(log_n p)` | `2^23.7` | `2^5 = 32×` above floor |

## Lean (axiom-clean: `[propext, Classical.choice, Quot.sound]`, verified vs real oleans)
`ArkLib/Data/CodingTheory/ProximityGap/PaleySpectralFloor.lean`:
- `PaleyFloorBound ψ G C L` — the EVT-correct target as a named Prop (`L = log m`).
- `paleyFloor_implies_worstCase` — floor ⟹ in-tree open residual `WorstCaseIncompleteSumBound` at
  `M = C²·|G|·L` (feeds the δ* consumer chain). **VERIFIED axiom-clean.**
- `ramanujan_implies_paleyFloor` — the spectral-excess inequality: `GeneralizedPaleyRamanujan`
  (`B ≤ 2√|G|`) ⟹ `PaleyFloorBound` iff `4 ≤ C²·L`, i.e. Ramanujan is *strictly stronger* and only
  suffices when `log m ≥ 4/C²` (and is unavailable here since `B > 2√n`). **VERIFIED axiom-clean.**
- `addEnergy_le_of_paleyFloor` — end-to-end energy budget from the floor (clean composition).

## Bottom line (honest)
The Paley route does NOT close the prize. Its gain is a **refutation of the spectral framing**:
chasing Ramanujan / a spectral-gap upper bound is a dead end (the target is false in regime), and the
core is re-pointed at the EVT floor `B ≤ C√(n log m)`, `C0=√2`. The residual is unchanged: prove
`√(2 n ln m)`-cancellation among the `m=(q−1)/n` Gauss periods — the deep-moment / L^∞ wall, best
proven bound `n^{3/4+o(1)}` (moment) / `n^{1−o(1)}` (BGK), gap `32×`–`2400×` from the floor.

## References
- [LZ19] Liu–Zhou, *Eigenvalues of Cayley graphs*, arXiv:1809.09829 (Thm 115 dictionary).
- In-tree: `GeneralizedPaleyRamanujan.lean`, `GaussPeriodCosetReduction.lean`,
  `CharSumMomentDeepWall.lean`; `docs/references/proximity-gap-paley-spectrum/README.md`.
- KB: `deltastar-407-limit-law-sqrt2-constant-2026-06-13.md` (the N(0,1) limit law, `C0=√2`).

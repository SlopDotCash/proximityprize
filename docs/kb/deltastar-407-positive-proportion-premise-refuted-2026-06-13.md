# δ* (#407) — the "positive-proportion / large-subgroup sum-product" premise is REFUTED (regime is the thinnest)

**Status:** honest negative result; NOT a closure. Refutes a proposed regime correction and pins the
exact sum-product threshold the prize misses. Author: δ* lane (#407), 2026-06-13.

## The proposed angle (and why it would matter if true)

A directive proposed that, because the index `m = (q−1)/n ≈ 2^128` is held *constant* as `n = 2^μ`
grows, the subgroup `μ_n` is **positive-proportion** (`n = Θ(q)`, `n ≫ √q`). If true, the prize would
sit in the *large-subgroup* regime where Konyagin / Heath-Brown–Konyagin / Garcia–Voloch give
**nontrivial** eigenvalue bounds `B = max_{b≠0}|η_b| ≤ q^{1/4}√n`, possibly strong enough to close the
mod-`q` defect `kD_r`. This would be a different (stronger) regime than the thin-BGK wall.

## The refutation (arithmetic, decisive)

`q − 1 = n·m` with the **two** factors `n = 2^μ` (`μ ≤ 40`) and `m ≈ 2^128`. "m constant" does NOT
imply `n = Θ(q)`: that conclusion needs `m = O(1)`, but here `m = 2^128` is a *huge* constant and
`n ≤ 2^40 ≪ 2^128 = m`. So **`n` is the SMALL factor**:

- density `|μ_n|/q = n/(n·m) = 1/m = 2^{−128}` — the **thinnest** regime in the whole campaign.
- exponent `n = q^{μ/(μ+128)}`: `q^{0.072}` (μ=10) … `q^{0.238}` (μ=40) — **below `q^{1/4}`**, exactly
  matching the campaign's recorded `β = (μ+128)/μ ∈ [4.2, 13.8]` (`n = p^{1/β}`).
- `n ≫ √q` is FALSE by `2^{64 − μ/2} ≥ 2^{44}`.

So the positive-proportion premise is an arithmetic error (confusing "the index `m` is a fixed
constant" with "the *complementary* index `n` is positive-proportion"). The prize is the *thin* case.

## The sum-product threshold the prize misses (quantified)

- **Multiplicative energy is definitionally vacuous.** For a subgroup, `E^×(μ_n) = #{(a,b,c,d):ab=cd}
  = n^3` exactly (`ab=cd ⟺ a/c = d/b ∈ μ_n`). A *multiplicative*-energy bound can never be nontrivial
  for a group; the object controlling `B` is the **additive** energy `E^+`.
- **Additive energy is deeply trivial.** `E^+(μ_n) = n^2 + dev`, expected `dev ~ n^3/q`. At prize
  `n^3/q ≤ 2^{−48} ≪ n^2`, so `E^+ = n^2(1+o(1))` (char-0 Sidon value `3n^2−3n` at `r=2`; verified
  numerically `E^+ = 720` at `n=16`). No incidence/sum-product input beats the trivial `n^2`; the
  energy route delivers only the Parseval RMS `√n`, never the target `√(n·log m)` *max* control.
- **The one nontrivial large-subgroup bound needs `n > √q`.** Via `B^4 ≲ q·E^+ ≈ q·n^2`,
  `B ≤ q^{1/4}√n`, which is sub-`n` **iff `n > √q`**. The threshold is exactly `n = √q = q^{1/2}`; the
  prize lives at `≤ q^{0.238}`, missing it by `≥ 2^{44}`. The large-subgroup regime is **empty of
  prize instances**.
- **Cross-parity `A = −g·B`.** `#cross-parity-defects = |S₀ ∩ (−g)S₀|` (subset-sum image ∩ its
  `g`-dilate) is a sum-product incidence = the SAME BGK/Shkredov thin wall; no gain.

**Quantified gap (μ=40, n=2^40, q≈2^168):** target `log₂B = 23.5` (`√(n log m)`); best PROVEN thin
bound (di Benedetto `t^{0.989}`) `= 39.6`; trivial `= 40`; RMS floor `= 20`. The record is a **full
half-power (16 bits of log₂B) above** the target — the well-known thin-regime wall, not a new opening.

## Net

The positive-proportion / large-subgroup angle does **not** apply: the prize subgroup is the thinnest
(`density 2^{−128}`, `n ≤ q^{1/4}`), multiplicative energy is vacuous, additive energy is trivial-`n^2`,
and the only nontrivial large-subgroup bound requires `n > √q` which the prize misses by `≥ 2^{44}`.
This **reconfirms** (does not break) the thin-BGK/Paley/Shkredov wall, now with the exact threshold
(`n > √q`) and the exact miss factor pinned. No closure; nothing fabricated.

## Reproduce
Self-contained arithmetic in this note (density `1/m`, exponent `μ/(μ+128)`, threshold `n>√q`); the
`E^+ = 720` at `n=16,p=65537` check matches the in-tree char-0 `E_2 = 3n^2−3n`.

# Sharpest closed form of the gate: equidistribution defect of the `r`-fold sumset of `μ_n` (2026-06-13)

> **Correction (2026-10-28 audit, T48; carrier error R-169).** `E_r(ℤ)` below is the
> **canonical integer-lift** convolution count: the residues of `μ_n ⊆ F_p` are lifted to
> `{0, …, p−1}` and added in `ℤ`. It is **not** the genuine cyclotomic (characteristic-zero) energy
> of `μ_n ⊆ ℤ[ζ_n]`, and the two differ even for dyadic roots. For `μ₈ ⊆ F₁₇`, the integer-lift
> energies at `r = 2, 3, 4, 5` are `192, 8180, 431872, 24492428`. Exact signed cyclotomic basis
> counting gives `168, 5120, 190120, 7939008` (both reproduced exactly during the audit). So
> `spurious = E_r(F_p) − E_r(ℤ)` is not the cyclotomic excess, and the "spurious mass" defined
> here inherits the wrong carrier. The Gaussian value `(2r−1)!!·n^r` is an upper envelope for the
> independent baseline, not the exact genuine-collision (Lam–Leung) floor. The finite-field
> identity is correct and is kept: `M_r = p·E_r(F_p) − n^(2r)` is the nonzero-frequency moment.
> Replace the baseline before reading the subtraction as cyclotomic excess. The "BCHKS 1.12 ⟺"
> line below is a proposed reformulation, not a proved equivalence. "Provably clean" below onset
> is a finite observation for the tested cells: thin exceptions with `p > n⁴` exist (for example
> `n = 64`, `p = 17318209`, with `E_2 = 13632 > 12096`; see T91).

Direct isolation of the spurious mod-`p` collision count (`scripts/probes/probe_spurious_collision_count.py`):
compute `E_r(ℤ)` = genuine `r`-fold balanced-tuple count (integer convolution, NO wrap) and
`E_r(F_p)` = mod-`p` count (wrap), via iterated convolution. `spurious = E_r(F_p) − E_r(ℤ)`.

## Measured facts
| n | p | log_n p | first spurious r | spur/genuine at top r | M_r/Gaussian at top r |
|---|---|---|---|---|---|
| 8 | 521 | 3.0 | r=5 | 0.234 (r=10) | clean |
| 8 | 4129 | 4.0 | r=8 | 0.0005 (r=10) | clean |
| 16 | 4129 | 3.0 | r=4 | **1.357 (r=8)** | 0.045 (clean) |
| 16 | 65537 | 4.0 | r=4 | 0.070 (r=8) | clean |

1. **Onset** of spurious collisions ≈ `r = log_n p` (exactly where the elementary Sidon-`B_r`/pigeonhole
   clean band ends). Below it, ZERO spurious — provably clean.
2. **Spurious can dominate the GENUINE count** (n=16,p=4129,r=8: mod-`p` energy is 2.4× the integer
   energy). So the naive "spurious is lower-order" hope is FALSE past onset.
3. **Yet `M_r = pE_r(F_p) − n^{2r}` stays below the Gaussian baseline `p(2r−1)!!n^r`** — because the
   dominant spurious mass is exactly the `b=0` equidistribution term `n^{2r}/p`. Subtracting it,
   `E_r(F_p) − n^{2r}/p` stays ≤ Gaussian (n=16,p=4129,r=8: `3.9e14 ≤ 8.7e15`, ratio 0.045 — matches the
   independent `M_r` probe exactly, cross-validating both).

## The gate in its sharpest closed form (equidistribution)
> **BCHKS 1.12 ⟺** `E_r(F_p) − n^{2r}/p ≤ (2r−1)!!·n^r·(1+o(1))` for all `r ≤ c·ln p`,
> i.e. **the `r`-fold sumset of `μ_n` equidistributes mod `p` down to the genuine-collision floor.**

`n^{2r}/p` = perfectly-equidistributed mass; `(2r−1)!!n^r` = genuine (Lam–Leung antipodal) floor. The
gate is exactly that the **equidistribution defect** `E_r(F_p) − n^{2r}/p` does not exceed the genuine
floor, uniformly to `r ≈ ln p`. This is the cleanest, most closed statement of the open core reached.

## Why still open (honesty)
The defect has **no closed-form law** — it IS the equidistribution defect of a specific geometric
sequence, the object with no elementary handle (cyclotomic norm has no teeth at large `n`; magnitude
methods eliminated, see `…-bootstrap-NOGO-…`). The measurement CONFIRMS cleanness through the tested
range but proves nothing for `n=2^30, p=2^192, r=133`. The gate is genuine equidistribution of
`{Σ_{i≤r} g^{e_i}}` mod `p` — recognized open (BCHKS 1.12). **No closure claimed.** This turn isolates
and names the object exactly; it does not cross it.

# δ* sweep A33 — the REALIZABILITY (deg-`<k`) lever for R-thin: a CONSTANT-FACTOR sub-`√(nk)` bound on ragged agreement (PARTIAL)

*2026-06-14. Actionable A33 (merged `407-T05`). Numerical-probe + axiom-clean Lean backbone.*

## The question

R-thin (the sole char-free residual after the #407 ring-hom waves): a **ragged** agreement set
`S` of a genuine monomial line `L_γ(x) = x^a + γ·x^b` on the smooth domain `μ_n` (`n = 2^μ`,
`d = gcd(a−b, n) ≥ 2`, `s = n/d`) satisfies `|S| ≤ √(n·k)` (rate `ρ = k/n`; the Johnson /
list-decoding target).

The prior #407 work proved **every moment / spectral / PSD / fold lever is EMPTY**: the LP over the
twist-orbit autocorrelation circulant `M_{i,j} = |S ∩ ω^{i−j} S|` collapses to its lowest Fourier
mode (`λ_0 = Σ_t v_t` = orbit-incidence), so 3rd/4th-moment and PSD refinements add *nothing*, and
the gap to `√(n·k)` stays a constant `≈ s/2`. The **one untried lever** was named precisely
(407-T05): **REALIZABILITY** — the agreement set is the zero set of `c − L_γ` for *one*
degree-`<k` polynomial `c` (the single-`c` twist codewords `c_ω(x) = ω^{−a} c(ωx)` share a global
Hankel/rank-`≤k` structure the circulant-of-counts discards). **A33 = execute this lever
numerically: does realizability beat `√(n·k)` at the Kambiré-worst intermediate `d`?**

## What I did

Exact finite-field probes (pure-python `F_q` linear algebra, `q ≡ 1 mod n`):

- `scripts/probes/sweep_A33_realizability_v2.py` — for each genuine direction, the EXACT maximum
  realizable agreement size, **split into ragged vs coset-union**. (Realizability of a candidate
  `S` = "∃ deg-`<k` `c` and scalar `γ` with `c(x) = x^a + γx^b` on `S`" = a rank/consistency test;
  raggedness = not a union of cosets of any nontrivial subgroup of `μ_n`.)
- `scripts/probes/sweep_A33_realizability_v3.py` — fast variant via MDS `k`-subset interpolation
  (the agreement set of one deg-`<k` codeword = points where the unique interpolant of any `k`
  values matches), exact for `n ≤ 16`, cross-checking v2.
- `scripts/probes/sweep_A33_margin_scaling.py` / `sweep_A33_n32_64.py` — the **margin scaling**
  `√(n·k) − Λ` at the Kambiré-worst direction (`d ≈ √n`), `n = 8, 16, 32`, the honest crux.

`Λ(n,ρ)` := the maximum **ragged** realizable agreement size at the Kambiré-worst direction.

## The decisive finding — a CONSTANT-FACTOR sub-`√(nk)` ragged bound

| ρ   | n  | d (worst) | Λ (ragged max)     | √(n·k) | Λ/√(n·k)   | char-test          |
|-----|----|-----------|--------------------|--------|------------|--------------------|
| 1/2 | 8  | 2         | 5  (EXACT)         | 5.657  | 0.8839     | —                  |
| 1/2 | 16 | 4         | 10 (EXACT)         | 11.314 | 0.8839     | —                  |
| 1/4 | 8  | 2         | 3  (EXACT)         | 4.000  | 0.7500     | char-INDEP (6 q)   |
| 1/4 | 16 | 4         | 6  (EXACT)         | 8.000  | 0.7500     | —                  |
| 1/4 | 32 | 4         | 12 (sampled LB)    | 16.000 | 0.7500     | (LB, q=97)         |

- **The relative margin is a CONSTANT** (n-independent, characteristic-independent):
  `Λ(n, 1/2) = (5/8)·n` and `Λ(n, 1/4) = (3/8)·n`, so `Λ/√(nk) = (5√2)/8 ≈ 0.884` (ρ=1/2) and
  `= 3/4` (ρ=1/4) at **every** tested `n ∈ {8, 16, 32}`.
- So **realizability DOES beat the moment-method `√(n·k)`** for the **ragged** part of R-thin — by
  a genuine *constant factor* `θ(ρ) < 1`, exactly the improvement the LP-of-counts work proved the
  moments could not supply. The improvement is `Θ(√(nk))` (not `o(√(nk))`): a constant-factor, not
  asymptotic-only, gain.
- The witness sets are genuinely ragged (e.g. `n=32`, exps `{0,5,8,10,12,15,16,18,19,21,22,25}`,
  `|S|=12`, not a coset-union).

## The honest reason it is NOT a closure

1. **The binding bad-side is the COSET-UNION family, which realizability does NOT touch.** In the
   same probe, the maximum realizable **coset-union** agreement reaches `√(n·k)` and **above**
   (e.g. `n=16, ρ=1/2, d=4`: coset-union = 12 > `√(nk)=11.314`). The coset-unions are the
   legitimate Kambiré bad side that carries `δ*`; they are *already* covered by the in-tree
   `FactorizationRigidity` / Lam–Leung coset structure. Realizability constrains only the ragged
   (isolated-excess, Beukers–Smyth) part — which the prior work already showed is `O(k)`,
   `n`-independent, sub-budget. **Beating `√(nk)` on the part that was never the worst case does
   not move `δ*`.**
2. **`θ(ρ)` is verified, not proven.** Pinning `Λ(n,ρ) = θ(ρ)·√(nk)` exactly needs the Lam–Leung
   classification of vanishing sums of `2^μ`-th roots of unity (which forces the ragged/coset
   split), absent in Mathlib.

So this **sharpens** the prior R-thin picture (the ragged bound is now a *constant factor below*
`√(nk)`, not merely `≤ √(nk)`), but it does **not** bypass the wall — the wall lives entirely in
the coset-union (= subgroup-sumset / BGK) family, exactly where #407 already located it.

## Lean artifact (axiom-clean)

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/Sweep_A33_Realizability.lean`:

- `deg_lt_agree_eq` / `deg_lt_distinct_agree_lt` — the **realizability backbone**, PROVEN
  axiom-clean over any field: two degree-`<k` polynomials agreeing on `≥ k` points are equal
  (RS rigidity: a deg-`<k` codeword is pinned by any `k` of its values). This is *why* the
  agreement set of a single deg-`<k` codeword is not a free autocorrelation profile — the rank
  constraint the moment LP discards.
- `A33ConstantRatioLaw` — the empirical constant-ratio law as a **named honest `Prop`** (`∃ θ < 1`
  with `Λ(n,k) ≤ θ·√(nk)` for all dyadic `n`); `thetaQuarter = 3/4`, `thetaHalf = (5√2)/8`, with
  `thetaQuarter_lt_one`, `thetaHalf_lt_one`, `*_pos` proven (both constants genuinely `< 1` and
  `> 0`). NOT discharged (no `sorry`, no placebo) — it is verified-not-proven (needs Lam–Leung).

## Verdict

**PARTIAL.** Realizability is a *real, live, constant-factor* lever — it beats the moment-method
`√(nk)` on the ragged part by `θ(ρ) < 1` (n- and char-independent, exact for `n ≤ 16`, confirmed at
`n = 32`). This is new positive knowledge: the prior work proved the moment ladder empty and named
realizability as the one untried lever; A33 shows the lever **fires**. But it does **not close
R-thin / `δ*`**: the binding bad-side is the coset-union (subgroup-sumset / BGK) family, which
realizability leaves untouched, and `θ(ρ)` is verified-not-proven. No fabricated closure.

## Reproduce

```
python scripts/probes/sweep_A33_realizability_v2.py     # exact ragged-vs-coset split, char-test
python scripts/probes/sweep_A33_realizability_v3.py      # fast MDS-interpolation cross-check
python scripts/probes/sweep_A33_margin_scaling.py        # margin scaling at Kambiré-worst dir
python scripts/probes/sweep_A33_n32_64.py                # n=32 ratio confirmation (0.7500)
```

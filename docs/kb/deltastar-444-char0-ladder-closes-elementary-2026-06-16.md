# The elementary combinatorics CLOSES the char-0 DC-Wick ladder (#444, 2026-06-16)

> **Scope correction (2026-10-28 audit, T48; cross T87/T104).** The antipodal (Lam–Leung)
> combinatorics is valid, and no failure of the characteristic-zero Bessel inequality is alleged.
> - **Finite data are not the generating function.** The cumulant and coefficient data through
>   depth 8 (`κ_{2r} = c_r·n` "linear to r=8"; ratios `a_{r+1}/a_r → L ≈ 0.6`) do not prove an
>   all-depth convergence radius or the advertised coefficient pattern at every depth. "Analytic of
>   radius `1/√L`" and "CLOSES" need the actual generating function and its established domain
>   before the MGF inequality is claimed.
> - **No transfer to raw finite-field energy.** At deep `r`, the raw energy is bounded below by the
>   principal-mode floor `n^(2r)/p`, so the "char-p faithfulness of E_r to depth log m" reduction is
>   meaningful only for the DC-subtracted nonzero-period energy (as the honest-scope paragraph
>   below begins to say).
> - **"Reduces to exactly" overstates.** The prize does not reduce to exactly this statement; the
>   MCA bridge and other inputs are separate.

**Status: a genuine structural advance — the char-0 floor closes via elementary combinatorics. NOT the
prize (which is char-p); the prize gap is now ISOLATED to a single char-p-faithfulness statement.**

## What was computed (exact, `scripts/probes/probe_dcwick_ladder_closure_char0.py`)
The char-0 r-fold additive energy of `μ_n` (`n=2^μ`) is `E_r = B_{2r}(n/2)` EXACTLY, where `B` obeys the
**add-one-class recursion** `B k (m+1) = Σ_{j} C(k,2j)·C(2j,j)·B(k−2j) m` (a new antipodal class occupies
`2j` of the `k` positions, `j` `+`/`j` `−`), with `E_r = B_{2r}` by **Lam–Leung** (the only primitive
vanishing relation among `2^μ`-th roots is the antipodal pair `z+(−z)=0`, so every balanced multiset is a
union of antipodal pairs). Solving the recursion:
```
E_1=n, E_2=3n²−3n, E_3=15n³−45n²+40n, E_4=105n⁴−630n³+1435n²−1155n,
E_5=945n⁵−9450n⁴+39375n³−77175n²+57456n, E_6=10395n⁶−…+ (−4370520)n, …
```

## The result: `κ_{2r} = c_r·n` EXACTLY LINEAR (depth r=1..8, i.e. through `κ₁₆`)
The additive-energy Wick cumulants `κ_{2r}` (treating `E_r` as the `2r`-th moment) are **exactly linear
in `n`** — every higher-degree term cancels:
```
κ₂=n, κ₄=−3n, κ₆=40n, κ₈=−1155n, κ₁₀=57456n, κ₁₂=−4370520n, κ₁₄=471556800n, κ₁₆=−68492499075n
c_r = 1, −3, 40, −1155, 57456, −4370520, 471556800, −68492499075   (sign (−1)^{r−1})
```
**Structural reason (linearity for all r):** `κ_{2r}` counts *connected* balanced configurations (cumulant
= connected correlation); a connected union of antipodal pairs over `μ_{2^μ}` is `O(n)` (pick the base
point `ζ^a` in `~n` ways; the relative structure of the pairs is an `n`-free count `= c_r`).

## Why this CLOSES the char-0 floor
`K(t) = Σ_r κ_{2r} t^{2r}/(2r)! = n·g(t)`, `g(t)=Σ_r c_r t^{2r}/(2r)!`. The MGF coefficients
`a_r=|c_r|/(2r)!` DECREASE (0.50, 0.125, 0.056, 0.029, 0.016, 0.009, 0.005, 0.003) with ratios
`a_{r+1}/a_r → L≈0.6 < 1`, so `g` is analytic of radius `1/√L > 1`. The max-over-`m` saddle sits at
`t* ~ √(2 log m / n) → 0` (since `log m ~ β log n`), well inside the radius, where `K(t*) ≈ n·t*²/2`
(the `t²` term, `a_1=½`) ⟹ sub-Gaussian with proxy `n` ⟹ **`M_char0 ≤ √(2n·log m)(1+o(1))`** = the floor.
This is consumed by the in-tree axiom-clean SG-MGF bridge (`DCWickMGFFromTermwise`, `I031SubGaussianMaxBridge`).

## Honest scope — this is CHAR-0, not the prize
`M(μ_n)` is **char-p** (`Σ_b|η_b|^{2r}=q·E_r^{Fp}`); the above uses the **char-0** energy `E_r^{char0}`
(the `ℂ` count). So this closes the *char-0 analog*. The PRIZE gap is now ISOLATED to ONE statement:
**char-p faithfulness of the (nonzero-period) energy at depth** — does `E_r^{Fp}=E_r^{char0}` (or stay
within an `o(1)`-relative factor) for `p≫n³` up to `r~log m`? The forced anomaly says `E_r^{Fp}>E_r^{char0}`
past `r≈β+1` for the FULL energy (the `b=0` spike), but the nonzero-period energy may be faithful deeper
(I099: the standardized nonzero-period cumulants stay sub-Gaussian). That faithfulness-at-depth is the
remaining open core — now a clean char-p-vs-char-0 transfer question, NOT the monolithic BGK sup.

## Net
The elementary combinatorics (recursion + Lam–Leung) resolves the char-0 side COMPLETELY and EXACTLY
(κ_{2r}=c_r·n linear to r=8, g analytic, saddle→floor). The $1M prize reduces to exactly: **char-p
faithfulness of E_r to depth `log m`.** Remaining to formalize: the recursion + Lam–Leung as Lean lemmas
(elementary), and the c_r-growth/MGF-radius bound (provable from the recursion's generating function).

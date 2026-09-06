# The char-0 additive energy of the 2-power subgroup — exact closed form (#444)

**Status: PROVED** (modulo the standard cyclotomic min-poly fact, Mathlib-available), independently
exact-verified for `r ≤ 8`. Landed axiom-clean for `r ≤ 6` in
`Research/ProximityPrize/Frontier/_CharZeroEnergyClosedForm.lean` (fork/main `7e63de278`).

## Statement

Let `n = 2^μ`, `m = n/2`, `ζ = ζ_n` a primitive `n`-th root of unity, `μ_n = {ζ^a : 0 ≤ a < n}`. The
`r`-fold **char-0 additive energy** is
```
E_r(ℂ) = #{ (x,y) ∈ μ_n^r × μ_n^r : Σ_i x_i = Σ_i y_i   exactly in ℂ }.
```

**Two equivalent exact closed forms** (degree-`r` polynomials in `n`):

1. **Generating function.**  `E_r(ℂ) = (2r)! · [z^r] f(z)^{n/2}`,  `f(z) = Σ_{k≥0} z^k/(k!)²`.
   Equivalently `E_r(ℂ) = CT[ (Σ_{j=1}^{m} (x_j + x_j^{-1}))^{2r} ]` (constant term of a Laurent polynomial)
   — the `2r`-th additive-energy moment of the cross-polytope vertices `{±e_j : j<m} ⊂ ℤ^m`.

2. **Binomial basis.**  `E_r(ℂ) = Σ_{s=1}^{r} A(r,s) · C(m, s)`,  where
   `A(r,s) = (2r)! · [z^r] (f(z)−1)^s` are positive integers with `A(r,1) = C(2r,r)`, `A(r,r) = (2r)!`.

**Leading term** `= (2r−1)‼ · n^r` (the real-Gaussian / Lam–Leung "Wick" value), so the **deficit**
`D_r := (2r−1)‼·n^r − E_r(ℂ) ≥ 0` has leading coefficient `C(r,2)·(2r−1)‼`, i.e. `D_r/Wick → C(r,2)/n`.

### Explicit polynomials (verified n = 8,16,32,64,128)
```
E_2(ℂ) = 3n² − 3n
E_3(ℂ) = 15n³ − 45n² + 40n
E_4(ℂ) = 105n⁴ − 630n³ + 1435n² − 1155n
E_5(ℂ) = 945n⁵ − 9450n⁴ + 39375n³ − 77175n² + 57456n
E_6(ℂ) = 10395n⁶ − 155925n⁵ + 1022175n⁴ − 3534300n³ + 6246471n² − 4370520n
```
`A(r,s)` table: `r=2:[6,24]`, `r=3:[20,360,720]`, `r=4:[70,4760,30240,40320]`,
`r=5:[252,63000,982800,3628800,3628800]`, `r=6:[924,851928,29937600,232848000,598752000,479001600]`.

## Proof

**Step 1 — antipodal bijection (the ONLY place 2-power is used).** For `n = 2^μ`, the minimal polynomial
of `ζ` over `ℚ` is `Φ_{2^μ}(X) = X^{n/2} + 1` (degree `φ(2^μ) = n/2`), so `{1, ζ, …, ζ^{n/2−1}}` is a
`ℚ`-basis of `ℚ(ζ)`. The only `ℚ`-linear vanishing relation among the powers `{ζ^a}` is the **antipodal**
one `ζ^{a+n/2} = −ζ^a` (Lam–Leung). Define `Ψ : μ_n → {±e_j} ⊂ ℤ^m` by `ζ^a ↦ +e_a` (`0≤a<m`),
`ζ^a ↦ −e_{a−m}` (`m≤a<n`). Then `Σ_i x_i = Σ_i y_i` in `ℂ` **iff** `Σ_i Ψ(x_i) = Σ_i Ψ(y_i)` in `ℤ^m`
(both sides expand in the basis `{ζ^j}_{j<m}` with coefficients = signed net multiplicities). Hence
`E_r(ℂ) = ` additive energy of the multiset `Ψ(μ_n) = {±e_j : j<m}` (each with multiplicity 1).

> **Essentiality check (load-bearing, not decoration).** For non-2-power `n` the form FAILS: at `n=6, r=3`
> the true energy is `2040` but the GF form gives `1860`; at `n=12, r=3`, `23160 ≠ 19920`. The breakage is
> exactly the extra cyclotomic relation `1 + ζ² + ζ⁴ = 0`, which violates "antipodal is the only relation."

**Step 2 — energy = constant term (general, no 2-power).** The additive energy of `S = {±e_j : j<m}` is
`Σ_v c(v)²` with `c(v) = #{r-tuples of S summing to v}`. By Parseval / constant-term,
`Σ_v c(v)² = CT[ P(x)^r P(x^{-1})^r ]` with `P(x) = Σ_{j<m}(x_j + x_j^{-1})`; since `P(x^{-1}) = P(x)`,
`E_r(ℂ) = CT[ P(x)^{2r} ]`. Expanding multinomially: a monomial survives the constant term iff every
variable `x_j` is balanced, i.e. appears with equal `+`/`−` exponents. If `x_j` is used `2k_j` times
(`Σ_j k_j = r`), it contributes `C(2k_j, k_j)` balanced choices and the multinomial weight is
`(2r)!/∏_j (2k_j)!`. Using `C(2k,k)/(2k)! = 1/(k!)²`:
```
E_r(ℂ) = (2r)! · Σ_{k_1+…+k_m = r} ∏_j 1/(k_j!)² = (2r)! · [z^r] (Σ_k z^k/(k!)²)^m,
```
which is form (1). Grouping by the number `s` of used coordinates (`k_j ≥ 1`) and choosing them
(`C(m,s)` ways) gives form (2) with `A(r,s) = (2r)! [z^r](f−1)^s`. The leading term (`s = r`, all
`k_j = 1`): `A(r,r)·C(m,r) = (2r)!·m^r/r! · (1+o(1)) = (2r-1)‼·n^r`. ∎ (modulo Step-1's standard fact)

## Why it matters (the #444 context)

`E_r(ℂ)` is the **char-0 deficit/cushion** `D_r = Wick − E_r(ℂ)` that the char-`p` excess
`W_r = E_r(F_p) − E_r(ℂ)` must beat for the moment/Wick energy bound `E_r(F_p) ≤ (2r−1)‼·n^r` to hold.
Pinning `D_r` exactly (`D_r/Wick → C(r,2)/n`) is what localized this session's **refutation of the energy
route at the prize**: at the moment-optimal depth `r* ≈ ln q ≈ 110`, `n = 2³⁰`, the cushion collapses to
`C(110,2)/2³⁰ ≈ 5.6×10⁻⁶`, negligible against the positive char-`p` excess — so the `(2r−1)‼` energy bound
gives no per-frequency bound at `r*`. This char-0 result is the **provable boundary**: the bound is *true*
over `ℂ`; only the char-`p` transfer (which the prize needs) fails. It is a genuine exact result, **not** a
prize closure — the prize remains on the direct BGK/sup-norm wall (`max|η_b| ≈ 0.7·√(2n ln q)`).

## Lean status
- **Landed axiom-clean** (`_CharZeroEnergyClosedForm.lean`): explicit `E_2..E_6`; the char-0 Gaussian
  energy bound `E_r(ℂ) ≤ (2r−1)‼·n^r` for `r = 2..6`; exact deficit lemmas (leading `C(r,2)(2r−1)‼`).
- **General-`r` formalization (scoped, feasibility ~6/10):** headline `energy_le_wick`, load-bearing
  `energy_eq_gf` / `energy_eq_constantTerm`, cyclotomic bridge `charZeroEnergy_eq_crossPolytope`. Needs:
  `IsPrimitiveRoot.powerBasis` (the `ℚ`-basis / linear independence — no off-the-shelf lemma, build from
  `minpoly` degree `n/2`); derive `Φ_{2^μ} = X^{n/2}+1` (no pre-named lemma); constant-term combinatorics
  (`constantCoeff` is a `RingHom` on power series, not `Finset.constantCoeff`).

# The far-line binding object = subset sums / Schur-ratios of μ_n (#444, sharpening)

*Status: VERIFIED reframing of the c=1 binding object; reduces to the additive structure of μ_n =
the BGK wall. Honest: a clean concrete identity, not a closure.*

## The identity (verified exact, n=16, k=2/3/4)

The far-line MCA incidence `#bad γ` for the non-symmetric binomial direction `x^{k+1}+γx^k`
(agreement `s=k+1`, so `c=s−k=1`) equals **EXACTLY** the number of distinct `(k+1)`-subset sums
of `μ_n`:
> `#bad γ = #{ Σ_{t∈T} t : T ⊆ μ_n, |T|=k+1 }` (verified: 464/1233/2256 at n=16, k=2/3/4, p=65537).

*Derivation:* a bad `γ` ⟺ some `(k+1)`-subset `T` has `x^{k+1}+γx^k` interpolable by deg-`<k`,
i.e. the order-`(k+1)` divided difference vanishes: `DD(x^{k+1}) + γ·DD(x^k) = 0`. Since
`DD_{k+1}(x^{k+1}) = h_1(T) = Σ_{t∈T} t` and `DD_{k+1}(x^k) = h_0(T) = 1`, this gives
`γ = −Σ_{t∈T} t`. So distinct bad `γ` ⟺ distinct subset sums. ∎

For a general binomial `x^a+γx^b`: `γ = −h_{a−k}(T)/h_{b−k}(T)` (ratio of complete homogeneous
symmetric functions = Schur `s_{(a−k)}/s_{(b−k)}`), so `#bad γ = #distinct Schur-ratios over T`.

## Why this is the wall (not a crack)

- At `c=1` (`s=k+1`) the count is `#distinct subset sums ≈ C(n,k+1) − (additive-energy correction) ≫ n`
  (verified `464 ≫` budget `16`). So `c=1` is FAR over budget — a bad (sub-δ*) radius.
- δ* sits at **deeper `c = s−k = Θ(n/log n)`**, where the binding object is the count of
  `s`-subsets `T` for which the `c` divided-difference conditions on `x^a+γx^b` are *simultaneously
  consistent* for some `γ` (an over-determined, codimension-`(c−1)` condition on `T`). This is the
  **additive energy of `μ_n` at depth `c`** = the BGK / thin-subgroup character-sum wall.
- The number of distinct subset sums (and its concentration as `s` grows) is governed by the
  additive structure / additive energy of `μ_n`, which is exactly the open object.

## What this adds

A clean, classical-flavored framing: the prize binding object is the **subset-sum / Schur-ratio
distribution of the multiplicative subgroup `μ_n`** — connecting it to additive-combinatorics
literature on subset sums of structured sets (Erdős–Heilbronn, Davenport constant, sumsets of
subgroups). It does NOT bypass the wall (the concentration of these sums = the additive energy),
but it is a concrete reformulation that may invite tools from that literature. δ\* OPEN.
Reproduce: `python3 -u scripts/probes/probe_444_subsetsum_binding.py`.

## UNIFICATION with the O_P orbit thread (Schur-ratio dilation-equivariance ⟹ the orbit formula)

The bad-γ Schur-ratio is a **dilation eigenvector**: under `T ↦ gT` (`g∈μ_n`),
`γ(gT) = −h_{a−k}(gT)/h_{b−k}(gT) = g^{(a−k)−(b−k)}·γ(T) = g^{a−b}·γ(T)`. So the dilation `×g`
acts on bad-γ values by `×g^{a−b}`, and the bad set is a union of orbits of the cyclic group
`⟨g^{a−b}⟩` of size `n/d`, `d=gcd(a−b,n)`. Therefore:

> **`#bad γ = [γ=0 is bad] + (n/d)·O_P`**, where `O_P` = # distinct nonzero Schur-ratio cosets.

VERIFIED exact (n=16, k=2, p=65537): `x^5+γx^3` (d=2): `233 = 1 + 8·29`; `x^9+γx^7` (d=2):
`129 = 1 + 8·16`; `x^6+γx^4` (d=2): `232 = 0 + 8·29`; `x^3+γx^2` (d=1): `464 = 0 + 16·29`.

This **DERIVES the campaign's orbit law `#bad = 1 + (n/2)·orbits`** (the `d=2` / imprimitive case,
0xSolace/lalalune) from the Schur-ratio's dilation-equivariance — a cleaner, additive-side reason
for it. The open **`O_P=1` persistence** (binding `d=2` direction = a single Schur-ratio coset for
all `n=2^μ`) is exactly "the nonzero bad Schur-ratios `−h_{a−k}(T)/h_{b−k}(T)` collapse to one
`μ_{n/2}`-coset." A descent attack: under squaring `μ_n→μ_{n/2}`, `h_j(T)` of antipodal-symmetric
`T` relates to `h` on the squared half (the even/odd descent), so the single-coset structure may be
provable by induction — a concrete route to `O_P=1` (the Johnson-proxy face; the p-dependent BGK
sup-norm prize stays separate/open).

## The symmetric-function descent identity (VERIFIED — the engine for an O_P=1 proof)

For any `T ⊆ μ_n` closed under negation (`T = −T`, antipodal-symmetric), with half-set `H` (one of
each `±` pair, so `T = H ⊔ (−H)`):
> **`h_{2j}(T) = h_j(H²)` and `h_{2j+1}(T) = 0`** (where `H² = {t² : t∈H} ⊆ μ_{n/2}`).
*Proof:* `Σ_j h_j(T) x^j = ∏_{t∈T} 1/(1−tx) = ∏_{t∈H} 1/((1−tx)(1+tx)) = ∏_{t∈H} 1/(1−t²x²) =
Σ_j h_j(H²) x^{2j}`. ∎ VERIFIED exact: 180/180 trials (n=16, j=1,2,3, antipodal-symmetric T).

**Consequence for `O_P=1`.** The bad Schur-ratio `γ(T) = −h_{a−k}(T)/h_{b−k}(T)`: for
antipodal-symmetric `T` with `a−k, b−k` even, `γ(T) = −h_{(a−k)/2}(H²)/h_{(b−k)/2}(H²)` = the
Schur-ratio of the descended direction on `μ_{n/2}`. So if the binding bad set is antipodal-symmetric
(or reduces to it) and the descended direction's `O_P` is `1`, then `O_P(n) = O_P(n/2)` and `O_P=1`
follows by induction from a small base case. **This is a concrete proof ENGINE for the open `O_P=1`
persistence statement** — NOT a completed proof (it still needs: (i) the binding `d=2` direction's
exact `(a,b)` and agreement; (ii) that its bad set is antipodal-symmetric with even `a−k,b−k`; (iii)
the base case). Offered as a tool. (Johnson-proxy face; the BGK sup-norm prize stays separate/open.)

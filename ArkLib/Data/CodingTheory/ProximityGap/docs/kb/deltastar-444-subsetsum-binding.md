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

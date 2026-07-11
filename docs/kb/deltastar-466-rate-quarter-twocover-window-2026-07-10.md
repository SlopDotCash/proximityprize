# Rate-quarter predecessor: the two-cover window is REALIZED — cyclotomic Davenport triples occupy the 87.5% packing window

## Status

Decides `three_heavy_twoCover_window`, the minimal open statement left by the
layer-cake file: **the window is OPEN/REALIZED, not excluded.**  Three distinct
near-threshold-aligned pencil pairs through one base codeword exist at the
literal P1 canonical domain, kernel-checked and generator-symbolic.

Formal kernel (pg-iterate ✅ OK 25s, 10 audited theorems, all on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`axiom`):

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterTwoCoverWindow.lean
```

Probes: `scripts/probes/probe_rate_quarter_p1_twocover_frustration.py`
(combinatorial LP + scaled RS searches),
`scripts/probes/probe_rate_quarter_p1_twocover_realization.py` (base triple in
the literal `F_P`, lift verification at `μ_32/μ_64/μ_128`, exact bookkeeping).

## 1. The two attacks and what they found

**Combinatorial side (exact integers).**  The window is trivially satisfiable
as a bare set system: three subsets of `[N]` of size `T−1` with equal pairwise
overlaps `234881024 < k` and empty triple intersection fit in
`N − 1` coordinates.  So counting alone never closes it; the question was
purely RS-algebraic.

**RS side — the key reduction.**  Take the shared base codeword as the *stack's
first row* (`u₀ = w₀ = 1`).  Then each aligned region is the agreement set of a
single codeword `g_i` with `u₁`, and the triple realization reduces to: three
distinct codewords whose pairwise differences `f = g₁−g₂`, `g = g₂−g₃`,
`f+g = g₁−g₃` all have *many roots in the domain* (degree `≤ k−1` each).  This
is a multiplicative-domain Davenport/abc question: maximize
`r(f) + r(g) + r(f+g)`.

## 2. The cyclotomic Davenport triple

Exhaustive search at `n = 16` (both in `F_17` and in the literal `F_P`) found a
**full-cap triple** — and it is an exact `char-0` identity in
`ℤ[w]/(w⁸+1)` (`w` a primitive 16th root of unity):

```text
(y−1)(y−w)(y−w⁸) + (−w²)·(y−w²)(y−w⁹)(y−w¹⁰) = μ·(y−w³)(y−w⁵)(y−w⁷)
```

(384 such triples over ℂ; the probe verified `λ = −w²` matches the F_P search
output exactly.)  In Lean the three vanishing identities and the nonvanishing
witness `H(w¹¹) = 4w` are proved by `linear_combination` with explicit
`ℤ[w]`-cofactors of `w⁸ + 1` — no numerals, no `binaryPow`.

**The lift.**  `f(x) ↦ (x−ρ)·f(x²)` with a common fresh linear factor maps a
fully split triple on `μ_n` (degree `n/4 − 1`, triple-root count `t`) to one on
`μ_2n` (degree `2n/4 − 1`, `t' = 2t+1`) — verified brute-force in `F_P` at
`μ_32`, `μ_64`, `μ_128`.  The formal file collapses the chain into closed form:
substitute `y = X^(2^26)` and multiply by
`E(X) = (X^(2^23)−z¹⁵)(X^(2^24)−s¹⁴)(X^(2^25)−v¹²)`, giving differences of
degree `31·2^23 = 260046848 < k = 2^28`, all `2^23`-sparse, hence **periodic
mod 128 on the power domain**.

## 3. The realized configuration (period 128)

Residue classes mod 128 (each of size `2^23`): per difference 24 pair-only
classes + 7 common classes = 31.  Stack `u₀ = 1`, `u₁` = mod-128-periodic
selection table; second rows `P₁ = Df`, `P₂ = 0`, `P₃ = −Dg`.

* aligned regions ⊇ 71 full classes each: `595591168 ≥ T − 1 = 592794965`
  (indeed `≥ T` — one class above; the window demands only `T−1`);
* pairwise aligned overlaps `≤ k − 1 < k` (pairs distinct + in-tree
  `alignedSet_inter_card_lt_k`);
* weighted two-cover surplus `Σ|Aᵢ| − |A₁∪A₂∪A₃| ≥ 3·595591168 − N =
  713031680 ≥ 704643071` — the 87.5% window is occupied.

Main theorems: `three_heavy_twoCover_window_realized` (symbolic generator) and
`three_heavy_twoCover_window_realized_literal` (at the certified `g` of
`_PrizeShapePrimeP30`).

## 4. Honest scope

* **Weighted vs plain.**  The `704643071` figure of the window prose is the
  weighted overlap mass `e₂ + 2e₃` — exactly what `union ≤ N` forces.  The
  plain `≥2`-covered coordinate count of this configuration is
  `79·2^23 = 662700032 < 704643071`; they differ only at `t > 0`.  A
  plain-count-saturating triple would need a `t = 0` full-cap Davenport base on
  `μ_32` (deg-7 `f, g, f+g` fully split, disjoint, 21 of 32 points) — searches
  (random + structured, `F_97` and scaled) did not find one; OPEN and
  irrelevant to the exclusion question.
* **No bad scalars.**  The construction exhibits dense *aligned regions*, not
  riders; it does NOT refute `#bad ≤ N` and does not move
  `3/8 ≤ mcaDeltaStar ≤ 43/96 + ε` — it removes the last hope that counting +
  RS rigidity at this window could close the predecessor pin.

## 5. Consequence for the P1 lane

The entire pencil/counting arc is now **closed with a realization**, not a gap:
every uniform counting cap was already kernel-refuted, and the packing window
that remained is occupied by explicit cyclotomic triples.  The predecessor
branch must proceed via `PredecessorStructuredFloorResidual` (structured-floor
route) or genuinely new algebraic input (e.g. rider/vote structure of the
realized triples — note the realized pencils sit at alignment `≥ T`, where the
joint list is `≤ 5`; whether *sub-threshold* pencils can also carry full fibers
of bad scalars is untouched).

## 6. Reusable engineering

* Elaborator/kernel deep-recursion with `Polynomial`-typed big powers
  (`X^(2^23)`): never `rw [defname]` on defs containing them and never
  decimal-literal exponents in `WithBot ℕ` casts — pass explicit polynomial
  terms to `refine`, keep exponents in `(2:ℕ)^n` power form, count one
  `degree_mul` per `*`, and finish `exact_mod_cast (by norm_num [k] : ...)`.
* `(powDomain …) i = gen ^ (i:ℕ)` as an `rfl`-`have` fed to `simp only` avoids
  the `show`-across-defeq recursion; `Prod.mk.injEq` beats `congrArg Prod.snd`
  for pair-distinctness under heavy component terms.
* Section `variable (hg : …)` used only in proofs is NOT auto-included —
  make hypotheses explicit.
* The mod-`2^s` residue machinery of the shared-fresh file generalizes verbatim
  (`residueSet128`, cards `71·2^23` by `biUnion` + `card_nbij'`); case splits
  over explicit residue Finsets by a single bounded `decide`
  (`∀ r < 128, r ∈ S → …`).

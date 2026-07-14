# [466-G298] The depth-1 CORE covariance is a subgroup additive-energy threshold, and its sign is not fixed by thinness (2026-07-13)

## Summary

G295/G296 studied the CORE covariance sequence `A_r` in the *rank* variable and proved the
reflection palindrome `A_r = A_{n+1-r}`, which is vacuous at the true prize depth `r ≈ log p`. G298
turns to the opposite endpoint of the sequence, the **depth-1 boundary value `A_1`**, and pins it to
an exact subgroup additive count.

At `r = 1` the adjacent-rank row degenerates: `dp_1 = 1_G`, `dp_0 = 1_{0}`, so `R_1 = dp_1 ⋆ dp_0 =
1_G`. Substituting into the centered covariance
`A_r = p·∑_x W_G(x) R_r(x) - (∑ W_G)(∑ R_r)` gives the exact closed form

```text
A_1 = p · T₃(G) - n³,      T₃(G) = ∑_{x ∈ G} W_G(x) = #{(y,z) ∈ G² : 2y - z ∈ G}
                                  = #{(y,z,w) ∈ G³ : 2y = z + w},
```

using `∑ W_G = n²` and `∑ 1_G = n`. Here `T₃(G)` is the number of 3-term arithmetic progressions
with midpoint in the multiplicative subgroup `G` — the additive-energy-adjacent structural count of
the thin sponsor set. Equivalently

```text
A_1 = n² · (p·T₃/n² - n),   so   sign A_1 = sign(T₃/n² - n/p):
```

the depth-1 CORE covariance is exactly the subgroup's **additive-3AP density measured against the
random density `n/p`**. This is the BGK/Paley object at depth one, expressed as a single scalar, not
a rank-blind polynomial feature.

## The no-go: the sign is a prime-scale threshold, not a thinness invariant

`sign A_1` is not determined by the thinness `n` alone. The sharpest witness holds `n` **and** the
additive count `T₃` fixed, and flips the sign purely by moving the prime across the threshold
`n³/T₃ = 512/24 ≈ 21.33`:

* `p = 17`, `G = ⟨9⟩ ≤ F₁₇^*` (order 8): `T₃ = 24`, `A_1 = 17·24 - 8³ = 408 - 512 = -104 < 0`.
* `p = 41`, `G = ⟨3⟩ ≤ F₄₁^*` (order 8): `T₃ = 24`, `A_1 = 41·24 - 8³ = 984 - 512 = +472 > 0`.

Both are `n = 8` sponsor cells with the **identical** additive structure `T₃ = 24`; only the scale
`p` differs. Therefore no depth-1 (rank-1) energy functional of the fixed shape `p·T₃ - n³` can
certify a fixed sign of the CORE covariance across sponsor primes: the simplest imaginable
certificate — the depth-1 boundary covariance itself — is sign-indeterminate. A surviving
certificate must use the rank-labelled row at genuine depth, not the depth-1 boundary energy.

The probe confirms both signs occur over all sponsor cells `n ∈ {8,16}`, `p ≡ 1 (mod n)`, `p < 500`,
and that the closed form `A_1 = p·T₃ - n³` is exact on every one.

## Why this is new, non-overlapping content

* Orthogonal to G289/G291 (dimension-forced canonical-feature Radon no-gos) and G293 (rank-blind
  ordered label list): those constrain *rank-blind features* of the census; G298 pins a specific
  *depth value* to a named subgroup additive energy and analyzes its sign.
* Orthogonal to G295/G296 (the rank palindrome and its census collapse): those relate `A_r` to
  `A_{n+1-r}` in the *rank* variable and vanish at prize depth. G298 works at the fixed *depth-1*
  endpoint and gives its exact arithmetic value plus a sign no-go.
* It is thinness-essential: `A_1` is literally the additive-3AP density of the thin 2-power subgroup
  versus the random density, i.e. the Paley/BGK quantity at the shallowest depth, and the no-go
  shows even that quantity's sign is not a thinness invariant.

## Scope and honesty

This is an exact identity plus a sign no-go for the depth-1 boundary covariance. It is **not** a
Jacobi covariance estimate at production primes, **not** a bound on the covariance at genuine prize
depth `r ≳ n`, and **not** a prize closure. It rules out only the depth-1 fixed-shape energy
certificate. CORE OPEN / ON-BGK, issue #466.

## Formal payload

`Frontier/_G298Depth1EnergyThreshold.lean`:
- `centeredCov` : the centered covariance pairing (matches G295).
- `centeredCov_indicator` : the depth-1 reduction to `p·∑_{x∈S} W x - (∑W)|S|` for an indicator row.
- `W17`, `G17`, `T3_17 = 24`, `sumW17 = 64`, `card_G17 = 8`, `A17_neg : centeredCov 17 W17 ind17 =
  -104`, `A17_lt_zero`.
- `W41`, `G41`, `T3_41 = 24`, `sumW41 = 64`, `card_G41 = 8`, `A41_pos : centeredCov 41 W41 ind41 =
  472`, `A41_gt_zero`.
- `depth1_sign_indeterminate` : the depth-1 covariance is `< 0` at `(17,8)`, `> 0` at `(41,8)`, and
  the two share `T₃ = 24`.

Axioms exactly `[propext, Classical.choice, Quot.sound]`; no `sorry`/`sorryAx`/custom axioms/
`native_decide`. Exact probe `scripts/probes/g298_depth1_energy_threshold.py` (closed form on all
sponsor cells, both-signs check, identical-`T₃` witness pair, threshold placement; hard
`SystemExit(1)` on violation; PASS).

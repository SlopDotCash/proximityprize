# Attack #04 — BCHKS Conjecture 1.12 via minimal vanishing weight / additive energy (algebraic)

**Issue:** #464 / #444 / #407 · **Date:** 2026-06-27 · **Angle:** algebraic minimal-vanishing-weight
**Verdict:** `reduces-to-paley` (the route is provably vacuous as a prize-closer; the lever that
would crack it equals the BGK/Paley floor, not a bypass).

## 1. The target theorem

Discharge BCHKS Conjecture 1.12 (`WorstCaseIncidenceBounded`) for the smooth 2-power domain
`μ_n ⊂ F_q`, `n = 2^30`, `q ≈ n·2^128`, by the **algebraic** route: bound the minimal Hamming
weight `w` of a vanishing `F_p`-linear combination of the cyclotomic columns of `μ_n`, equivalently
control the additive energy `E(μ_n)`. The concrete closure target would be:

> **(T04)** For the prize prime `p`, every `F_p`-vanishing sum `Σ_{x∈R} x = 0` with `R ⊆ μ_n` and
> `Σ_{x∈R} x ≠ 0` over `ℤ[ζ_n]` (a *spurious* vanishing) has weight `w = |R| ≥ √n` (or any
> superconstant lower bound). Combined with the char-0 antipodal structure (Lam–Leung) this would
> bound `E(μ_n)` and hence the Paley-graph eigenvalue `M(n) = max_{b≠0}|η_b|`.

## 2. The proof attempt (the strongest algebraic lever)

The in-tree route is clean and already partially landed:

- **Char-0 Lam–Leung** (`LamLeungTwoPower.antipodal_coeff_of_dvd`): every vanishing sum of `2^μ`-th
  roots of unity decomposes into antipodal pairs `{ζ, −ζ}`; the *minimal* char-0 vanishing weight is
  exactly `2`. No exotic minimal block exists (those need prime factors 5, 7).
- **Lift to char-p via norm height** (`SidonModNegEnergyEquality`, `VanishingRootSumHeightGate`): a
  char-`p` vanishing beats the char-0 weight-2 floor only by a **spurious** vanishing — `R` with
  char-0 sum `S = Σ_{x∈R} x ∈ ℤ[ζ_n] \ {0}` but `p ∣ N(S)`, `N(S)` the nonzero integer field norm.
- **The height bound.** For a weight-`w` sum of roots of unity on the unit circle, every archimedean
  conjugate of `S` has `|σ(S)| ≤ w` (triangle inequality), so `0 < |N(S)| ≤ w^{φ(n)} = w^{n/2}`.
  A spurious weight-`w` vanishing therefore **forces** `p ≤ w^{n/2}`, i.e.

  > **(★)** minimal spurious weight `w_min ≥ p^{2/n}`.

This is exactly the engine that proves `E(μ_n) = 3n²−3n` for `p > 2^n` (the norm regime): a weight-4
parallelogram is the first possible spurious block, and it needs `p ≤ 4^{n/2} = 2^n` to fire, so for
`p > 2^n` the energy is forced down to its char-0 antipodal minimum `3n(n−1)`. The route is real,
unconditional, and axiom-clean **in that regime**.

## 3. Adversarial refutation (this is where it dies)

Evaluate (★) at the **prize order** `n = 2^30`, `p ≈ 2^158`:

```
w_min ≥ p^{2/n} = 2^{(158·2)/2^30} = 2^{316/1073741824} = 2^{2.94·10⁻⁷} ≈ 1.0000002 .
```

So (★) **forbids nothing beyond weight 1**: even a weight-2 spurious vanishing is permitted. The
available norm budget for spurious vanishings is `2^{n/2} = 2^{2^29}` (bit-length `2^29 ≈ 5.4·10⁸`),
while the prize prime has bit-length only `158`. The height gate `p > 𝓗_n` (with
`𝓗_n ≈ (n/2−1)^{n/4}`, bit-length `~(n/4)·log₂(n/2)`) is satisfied with a slack of **six orders of
magnitude in bit-length** — meaning it is satisfied *vacuously*: it cannot fire to bound the weight.

The crossover is sharp and already documented in `VanishingRootSumHeightGate`: the gate closes the
energy equality at `n ∈ {8,16,32,64}` (where `𝓗_n < 2^128`) and goes **marginal/fails at n = 128**.
At `n = 2^30` it is off by `2^29 / 158 ≈ 3.4·10⁶`×.

**Why the lever fails structurally.** The norm/height bound is a *char-0* invariant: it measures how
large `N(S)` can be over `ℤ`, and divides it by the *single* prime `p`. But the prize regime is
precisely `n ≫ log p` — there are `~ n/2` independent archimedean conjugates whose product (the
norm) has `Θ(n)` bits, while `p` has only `Θ(log n + 128)` bits. A single prime cannot be forced to
miss a norm with `2^29` bits unless the weight `w` is itself `Θ(p^{2/n}) = 1 + o(1)`. The whole
"forbid short spurious relations" content collapses to nothing once `n/2 ≫ log₂ p`.

## 4. The lever analysis — what would actually crack it, and why it IS Paley

To beat (★) you would need a **char-`p` Lam–Leung** theorem: a bound on the minimal weight of a
spurious (`p`-vanishing-but-not-`ℤ`-vanishing) sum of `2^μ`-th roots that does NOT pass through the
archimedean norm — because the norm bound is provably vacuous at prize scale (§3). But:

- A char-`p` minimal-weight bound `w_min ≥ f(n)` with `f(n) → ∞` is **equivalent** to the additive-
  energy / DC-subtracted moment statement `E_r(μ_n) ≤ Wick` at the relevant depth, which is
  **equivalent** to the BGK/Paley sup-bound `M(n) ≤ √(2n log q)` (the `_AvBGK_TwoSidedPin` /
  `GaussPeriodMomentBound` equivalence). This is the prize floor itself.
- The char-`p` "wraparound" collisions are isolated *exactly* as the open residual `τ` in
  `_LamLeungCharPInjection` (the wraparound-tag multiplicity = the `W_r` excess). That file's honesty
  note already states `τ ≤ τ₀(r)` at saddle depth `r* ≈ log p` **is** the genuine open core.
- The full-energy moment hypothesis is PROVEN FALSE past the DC crossover (`DCEnergyEssential`), so
  even the energy face only survives in DC-subtracted form — again the same wall.

There is no algebraic-geometry escape on this face either: the GM-MDS / higher-order-MDS generic
vanishing route reduces to `RIMKernelTrivialFromLovett` (a different open AG problem), and the
gapped-Vandermonde minors literally vanish at `μ_n` in char 0 (antipodal `1 + ζ^{n/2} = 0`,
Lam–Leung) — no Dirichlet prime helps (memory `issue334-algebraic-floor-reduces-cyclotomic-wall`).

## 5. Honest verdict

The minimal-vanishing-weight / additive-energy face of BCHKS 1.12 is the **same wall** as the
char-sum face, and at the prize order `n = 2^30` it is strictly weaker than vacuous: the only
unconditional algebraic lever (the norm height, (★)) cannot even force the minimal spurious weight
above `2`. It is genuinely productive at `p > 2^n` (`n ≲ 40`), where it pins `E(μ_n) = 3n²−3n`
exactly — but that regime is exactly the *useless* one for the prize (`√(n log p) ≥ n` there). The
lever that would close T04 — a norm-free char-`p` Lam–Leung — is *equivalent to* the BGK/Paley floor,
not a bypass of it.

**Bypasses Paley:** NO. **Status:** reduces-to-paley (refuted as an independent prize route).
**Named open input:** `WraparoundTagBounded` / the char-`p` minimal-spurious-weight bound
`w_min ≥ f(n), f → ∞` = the DC-subtracted moment/BGK floor.

## 6. Landed artifact

`Frontier/_Attack04MinimalVanishingWeightVacuous.lean` — axiom-clean
(`propext, Classical.choice, Quot.sound`), proves:
- `prime_le_of_spurious_weight` — the height gate `p ≤ w^{n/2}` from a spurious vanishing;
- `prizeWeight2_gate_vacuous` — at prize half-degree `2^29`, every `p < 2^158` satisfies the
  weight-2 norm gate `p ≤ 2^{2^29}` with colossal slack;
- `prize_bitlength_gap` — `158·3·10⁶ < 2^29` (six-order vacuity);
- `minimal_weight_route_vacuous_at_prize` — the packaged refutation.

# wf-ND (#407): the theta / approximate-functional-equation route is PINNED (no contraction)

**Lane ND** — generalize Demirci–Akarsu–Marklof (DAM, arXiv:1207.1607) past the quadratic
incomplete Gauss sum, to the subgroup Gauss sum `η_b = Σ_{x∈μ_n} e_p(bx)`.

**Verdict: PINNED** (`conjecture refuted` for the contraction premise; `proven` for the
structural no-contraction skeleton). The theta / Poisson functional-equation lens provides **no
new input** to the δ* core: the value distribution is i.i.d. complex Gaussian (NOT a self-similar
theta law), and the Poisson transform is a length-preserving fixed point (no contractive
renormalization to the floor).

## The lens (genuinely new in-tree)

The classical quadratic incomplete Gauss sum `Σ_{x≤N} e_p(x²)` has a van der Corput /
Hardy–Littlewood approximate **functional equation**, and DAM give its limiting **value
distribution**: a self-similar theta law on the metaplectic horocycle in `SL(2,ℤ)\SL(2,ℝ)`, with a
**heavy tail `P(|·|>R) ~ c·R^{-4}`** and cusp excursions of order `m^{1/4}`. If our subgroup sum
shared such a self-similar law, its renormalization (continued-fraction driven for the quadratic
case) could give a **convergent recursion to the floor** — distinct from the false magnitude
descent `M² ≤ 2M(n/2)²` and from the additive FFT butterfly (whose in-tree honest caveat already
notes the theta machinery does not directly apply, because the phase is geometric `j→j+1`, not
quadratic).

## Decisive test (exact, `scripts/probes/probe_wf2ND_theta_fe.py`)

Computed all `η_b` exactly (no sampling), `n=8,16,32,64`, multiple primes including the thin prize
regime `p/n³ = 256` (β≈5).

### TEST A — value distribution of `{η_b/√n}_{b≠0}`

| metric | complex Gaussian | DAM theta law | measured (n=16→64) |
|---|---|---|---|
| `E|z|⁴/(E|z|²)²` | **2.0** | diverges (heavy tail) | 1.94 → 1.96 → 1.98 |
| `E|z|⁶/(E|z|²)³` | **6.0** | diverges | 5.54 → 5.76 → 5.85 |
| Re-part kurtosis | **3.0** | non-Gaussian | 2.90 → 2.95 → 2.97 |

Converges to the **complex Gaussian** values as `n` grows. (The `n=8` rk=2.62 vs 1.875
bimodality is a small-n arithmetic artifact gated by `v₂(p−1)≥3`; both branches are
Rayleigh-light-tailed and the constant → 2.0 with `n`.)

### TEST A tail — Rayleigh, not `R^{-4}` (the decisive separator)

`P(|z|>R)` empirical vs Rayleigh `e^{-R²}` vs DAM `R^{-4}`, at `p/n³=256` (thin), n=16:

| R | empirical | Rayleigh `e^{-R²}` | DAM `R^{-4}` |
|---|---|---|---|
| 2.0 | 1.6e-2 | 1.8e-2 | 6.3e-2 |
| 2.5 | 1.1e-3 | 1.9e-3 | 2.6e-2 |
| 3.0 | 2.3e-5 | 1.2e-4 | **1.2e-2** |
| 3.5 | 0 | 4.8e-6 | 6.7e-3 |

The tail tracks **Rayleigh** and is **~2–3 orders of magnitude BELOW the DAM heavy tail** at R=3,
and vanishes past R=3.5 — the *opposite* of a power-law tail. Identical shape at β≈3.4, 4, 5. The
extreme value `max|η|/√n ≈ 3.4` tracks the Gaussian `√(2 log p)` (≈5.3 ceiling), **not** the DAM
cusp `m^{1/4} ≈ 8–16`.

**⇒ There is no self-similar theta limit law for the subgroup sum.** It is the generic CLT of a
sum of `n` quasi-random unit phases. Nothing to renormalize against.

### TEST B — no contraction in the sup

`sup_b|η_b|` descent ratios hover at `√2 = 1.414` but do not drop contractively below it; `sup/√n`
is **flat** (≈3.4–3.7, the √log creep). No level-uniform contraction `< √2`.

### TEST C — Poisson/theta self-duality is a FIXED POINT

The additive DFT of `1_{μ_n}` is `η` itself; applying the DFT again recovers a reflected copy of
`1_{μ_n}` (Fourier inversion). The "dual" sum therefore has support of the **same size n** —
verified `dual_support_size = n` exactly, `= μ_n` setwise (n=16, two primes). The theta/Poisson
transform does **not shorten** the sum: a fixed point, not a contraction. No recursion to a smaller
modulus exists.

## The proven structural skeleton (Lean, axiom-clean)

`Research/ProximityPrize/Frontier/_wf2ND_theta_fixedpoint.lean` —
`lake build` green (autoImplicit=false, 855 jobs), `#print axioms` = `[propext, Classical.choice,
Quot.sound]`, no `sorryAx`:

- `isLengthPreserving_of_inversion` : if `T(T f) = c • (f ∘ σ)` for a bijection `σ` and `c ≠ 0`
  (the Fourier-inversion shape), then `#support(T(T f)) = #support f`.
- `theta_no_contraction` : hence `¬ ∃ f, #support(T(T f)) < #support f` — **no contraction is
  available** from a Fourier-inversion-type involution. With `T = DFT`, `σ = neg`, `c = |F_p|`,
  this is exactly "the theta transform does not shorten the subgroup sum."

This brick proves *why the avenue cannot contract*; it does NOT bound `B = max_b|η_b|` (honesty
contract: the core stays open).

## Why this is a clean pin, not a wall re-label

It is a **new lens** with a **new measurement** (the DAM value-distribution test, never run
in-tree before): the in-tree finding "η_b/√n → Gaussian" was asserted; here it is shown to be the
*non-DAM* branch specifically, killing the theta-renormalization hope at its root. The pin's reason
is precise and intrinsic to the theta object (geometric vs quadratic phase ⇒ no metaplectic
horocycle ⇒ no self-similar law ⇒ Poisson is a fixed point), not a reduction to BGK/energy.

## Files

- `Research/ProximityPrize/Frontier/_wf2ND_theta_fixedpoint.lean` (proven, axiom-clean)
- `scripts/probes/probe_wf2ND_theta_fe.py` (exact, reproducible)
- this note.

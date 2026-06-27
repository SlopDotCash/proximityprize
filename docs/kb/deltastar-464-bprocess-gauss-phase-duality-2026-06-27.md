# The B-process Gauss-phase duality — the wall as a pure-phase problem (2026-06-27)

The single most useful reformulation surfaced by the 3-workflow assault (the
`bombieri-iwaniec-second-spacing` novel angle, verified here numerically to machine precision).
It is **not** a bypass of the Paley wall, but it is the sharpest available statement of it: it
removes the magnitude red herring entirely and relocates the entire difficulty into the
equidistribution of Gauss-sum **phases**, a problem in the Katz / Fouvry–Kowalski–Michel
"sums of products" framework.

## The exact duality (verified to 1e-14)

Let `d = (p−1)/n` (the number of cosets of `μ_n` in `F_p^×`), `g` a generator of `F_p^×`,
`ζ_d = e^{2πi/d}`. Index the period values by coset `c ∈ ℤ/d`: `η(c) = η_{g^c}`. Define the
Gauss-sum vector `τ_s = Σ_{c=0}^{d−1} η(c) ζ_d^{sc}` (the finite Fourier transform on `ℤ/d`). Then:

```
   η(c) = (1/d) Σ_{s=0}^{d−1} τ_s ζ_d^{−sc},     τ_0 = −1,     |τ_s| = √p exactly for all s ≠ 0.
```

(The `τ_s` are, up to normalization, the Gauss sums of the `d` multiplicative characters trivial
on `μ_n`; `|τ_s| = √p` is the classical Gauss-sum modulus. Numerically exact: `n=16,p=1009,d=63`
and `n=8,p=4001,d=500` both give duality error `< 2e-13` and `|τ_s| = √p` to `1e-6`.)

## Consequence: the wall is 100% phase

Because **every** nonzero `τ_s` has the **same magnitude `√p`**, the period vector `η` is `(1/d)`
times the DFT of a *constant-magnitude* sequence. Writing `w_s = τ_s/√p` (a **unit** sequence,
`|w_s| = 1`):

```
   B = max_{c≠0} |η(c)| = (√p / d) · max_c |D(c)| + O(1/d),    D(c) = Σ_{s≠0} w_s ζ_d^{−sc}.
```

(Verified: `B` vs `(√p/d)·max|D|` agree to 2 decimals — `8.66 ≈ 8.68`, `12.04 ≈ 12.04`,
`7.56 ≈ 7.56`.) The prize bound `B ≤ √(2n ln p)` is therefore **equivalent** to

```
   max_c |D(c)| ≤ √(2 d ln d) · (1+o(1)),
```

i.e. **the unit Gauss-phase sequence `(w_s)` has square-root-cancellation in its DFT to depth
`ln d ≈ ln p`** — exactly the behavior of a random unit sequence. Numerically `max|D|/√(2d ln d)
≈ 0.75–0.9` (below the bound, as for a sub-random sequence).

## Why this matters (and why it is not a bypass)

**Removes the phase-blind floor.** The proven no-go "any magnitude/`L²`/energy functional gives
exponent `≥ 1`" is *vacuous on the dual side*: `|w_s| = 1` is constant, so magnitude functionals
of `w` carry **zero** information. Any bound here is *forced* to be phase-aware — which is exactly
the kind of argument the primal side could not support. This is genuine structural clarity: the
problem is 100% about `arg(τ_s)`, and the magnitude (the √q wall, the energy floor) is a red herring.

**But the wall persists as a dual excess.** The dual moments `M_r = Σ_c |D(c)|^{2r}` are *not*
exactly Wick: `M_r/(r!·d^r)` grows with `r` (e.g. `d=253`: `252 → 348 → 507 → 730` for `r=1..4`).
This excess is the dual analog of the primal wraparound `W_r`, and it equals (exact identity,
verified to `1e-9` by the source agent) the `L²`-energy of the `r`-fold additive self-convolution
of the **Jacobi-sum phase function** on `ℤ/d`: `R(l) = Σ_s w_s \bar w_{s−l} = (1/√p) Σ_s ± J(ψ_s,ψ_{l−s})`,
a sum of Jacobi sums along a line. Each Jacobi sum is Deligne-bounded (`|J| ≤ √p`), and the `r=2`
line-sum is provably controlled; the open part is the **uniform-in-`r`** bound to depth `r ≈ ln d`.

## The reduction (honest status)

```
   PRIZE FLOOR  ⟺  M_r := Σ_c |D(c)|^{2r} ≤ C^r · r! · d^r   uniformly for 1 ≤ r ≲ ln d,
```

where `M_r` is the `r`-fold additive self-convolution moment of the unit Jacobi-sum phase function
on `ℤ/d`. This is a **named problem in the Katz / Fouvry–Kowalski–Michel framework** (moments of
sums of products of Gauss/Jacobi sums; "trace functions" and their correlations). It is **the same
wall** (the Gauss-sum-phase equidistribution is open at this depth), so honestly it
`REDUCES_TO_PALEY` — but it is the reformulation that (i) escapes the phase-blind floor, (ii)
connects to the one body of *proven deep technology* (Deligne/Katz/FKM) with any traction, and
(iii) is the correct target for any future phase-aware attack. It is the Fourier-dual of the primal
energy picture: primal `B = sup|DFT(1_{μ_n})|` (varying magnitude, energy method → wall) vs dual
`B = (√p/d)·sup|DFT(Gauss phases)|` (constant magnitude, phase method → Katz/FKM).

## Landable Lean increment

The **B-process duality identity** `η(c) = (1/d) Σ_s τ_s ζ_d^{−sc}` with `|τ_s| = √p` is exact and
Lean-formalizable (it is the Gauss-period/Gauss-sum inversion, = WF1's `automorphic-theta`
`m·η_b = Σ_t χ̄_{nt}(b) τ(χ_{nt})` made into a clean DFT on `ℤ/d`, plus the classical
`|τ(χ)| = √p` from Mathlib's Gauss-sum API). Corollary `B = (1/d)·‖DFT_d(τ)‖_∞`. This pins the
prize floor to a constant-magnitude DFT sup-norm — the cleanest statement of the open core.

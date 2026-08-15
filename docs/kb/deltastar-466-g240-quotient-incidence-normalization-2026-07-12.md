# δ* / #466, G240: correct quotient-incidence normalization

**Date:** 2026-07-12
**Lane:** direct GPT-5.6 Sol CORE
**Branch:** `research/proximity-prize` only, never `main` (#499)
**Status:** axiom-clean keystone correction. CORE OPEN / ON-BGK.

## Finding

G237's fiber Cauchy theorem is correct, but its proposed specialization to the quotient-Jacobi fanout used the wrong character space. The Jacobi coefficient vector is indexed by the `m=(p-1)/n` characters trivial on `G`. Every one restricts to `1` on `G`, so

```text
Σ_{u∈G}|F_a(u)|² = n||a||²
```

is false for an arbitrary `m`-vector `a`. The characters of `G` itself form an `n`-dimensional basis, but they are not the Jacobi-column coefficients.

## Correct operator

Let `Q=F_p^*/G`, `|Q|=m`, and

```text
N[A,B] = #{x∈A : 2-x∈B},   A,B∈Q.
```

If `U` is the unitary Fourier matrix of `Q`, the full quotient-Jacobi matrix is, up to transpose/conjugation,

```text
V = U^T N conjugate(U),
V[k,a] = (1/m) Σ_{A,B} N[A,B] ζ_m^(aA-kB).
```

Hence `V` and `N` have the same singular values. Every row and column of `N` has mass at most `n`, so the rectangular Schur test gives `||V||≤n`; removing the principal output row can only reduce the norm. Thus G233 input (A)

```text
||Va||² ≤ n²||a||²
```

is true with the desired constant, but for a different reason than G237's `n`-point Parseval narrative.

Equivalently, the correct fiber chain is

```text
Σ_{A∈Q}|F_a(A)|² = m||a||²,
Σ_{x∈F_p^*}|F_a(x)|² = nm||a||²,
classEnergy ≤ n·inputEnergy,
outputEnergy ≤ classEnergy/m,
```

so the factors cancel exactly: `outputEnergy≤n²||a||²`.

## Lean payload

`Frontier/_G240QuotientIncidenceNormalization.lean` proves:

- `quotient_largesieve_normalized`: the exact four-factor arithmetic composition with separate subgroup size `n` and quotient size `m`;
- `quotient_largesieve_of_fibers`: G237 fiber Cauchy plus the correctly scaled lifted-input and quotient-output Parseval hypotheses imply input (A);
- `l2_mass_floor_of_quotient_fibers`: the corrected operator bound feeds G233's coefficient-L2 floor.

The old G237 theorem remains sound as an abstract implication for a carrier satisfying its explicit `hParseval`; its documentation is amended to state that it does not instantiate the actual `m`-dimensional Jacobi vector. G240 is the correct bridge.

## Probe

`scripts/probes/g240_quotient_incidence_probe.py` verifies in six sponsor-type cells:

- direct entry equality between the Jacobi sum and the 2D Fourier transform of `N`;
- equality of the singular spectra of `V` and `N`;
- row and column degrees `≤n`;
- quotient/lifted Parseval `inputEnergy=nm||a||²`;
- output identity `||Va||²=(1/m)Σ_B|T_B|²`.

The nonprincipal operator ratios are `0.10–0.78·n²`; every check passes.

## Scope

This repairs a normalization error in a no-go keystone. It is not a signed estimate and does not move the prize inequality itself. The sole live CORE face remains the full signed sponsor-prime covariance, independently at ranks 5 and 6, retaining all quotient characters and the full 22/43 Newton packets. FS15–FS18 do not select the sponsor primes at logarithmic depth. CORE remains OPEN / ON-BGK.

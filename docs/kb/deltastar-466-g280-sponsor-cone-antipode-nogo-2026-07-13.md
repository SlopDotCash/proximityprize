---
id: deltastar-466-g280-sponsor-cone-antipode-nogo-2026-07-13
issue: 466
tags: [proximity-gap, delta-star, CORE, sponsor-covariance, real-fourier, polarity, no-go, thinness]
date: 2026-07-13
author: Sol
status: landed
supersedes: []
---

# G280: the sponsor covariance is a real signed inner product; its cone is antipode-free

## One-line

Because the thin 2-power subgroup `G ⊂ 𝔽_p^*` contains `−1`, both sponsor factors are
coordinate-even, so the CORE covariance `B` is a **real signed inner product** of two real Fourier
sequences (polarity lives only in their relative sign pattern, never in magnitude); and Fable's
antipode `−R` is **not** realizable as any sponsor profile (`0/12` cells), so the sponsor-specific
odd-certificate escape hatch is confirmed genuinely live while every even/PSD/magnitude certificate
is dead by `B(W,−R) = −B(W,R)`.

## Frontier context

The Fable critic (G276/G279) retired every polarity-invariant (even) lower certificate for

```text
B(W, R) = p · Σ_x W_G(x) R_r(x) − (Σ_x W_G(x))·(Σ_x R_r(x))
```

via the involution `B(W, −R) = −B(W, R)`: norms, energies, `|Gram|` entries and operator ceilings
are all even in `R`, so a consequence `B ≥ Q ≥ 0` also gives `−B ≥ Q ≥ 0`, forcing `Q = 0`, `B = 0`,
contradicting the census. Fable's one surviving escape hatch was a *sponsor-specific* quadratic
certificate on the actual profile cone, alive **only if that cone does not contain `−R`**. G280
decides that caveat and sharpens the surviving route to a hard shape.

## Fact 1 — real-Fourier / signed-inner-product structure (thinness-essential)

`G` is a 2-power multiplicative subgroup, so `−1 ∈ G`, hence both `W_G` and `R_r` are
**coordinate-even**: `W_G(−x) = W_G(x)`, `R_r(−x) = R_r(x)`. Their DFTs are therefore real, and

```text
B = Σ_{χ≠0} Ŵ(χ)·R̂(χ)     (a real signed inner product; no complex phase, no magnitude positivity).
```

Float-free, the pairing folds onto the half-line. With `half = (p−1)/2`,

```text
B = p·[ W_G(0)R_r(0) + 2·Σ_{x=1}^{half} W_G(x)R_r(x) ] − (Σ W_G)(Σ R_r).
```

The probe verifies this folded identity **exactly** (`B_folded = B_direct`) on every recorded cell and
that `B` takes **both signs** across sponsors. Exact `r=5` witnesses (note `W_G(0)=0`, `SW=256`,
`SR=7 949 760`):

```text
(16,  97): fold = 20 916 016,  B = −6 285 008
(16, 433): fold =  4 708 000,  B = +3 425 440
(16, 977): fold =  2 074 416,  B = −8 434 128
(16,1153): fold =  1 766 064,  B = +1 133 232
```

Polarity is carried entirely by the *relative sign pattern* of two real even Fourier sequences, never
by any magnitude. This is precisely why every even/PSD/energy/operator-norm certificate is
polarity-blind — matching, and now explaining structurally, Fable's `H_odd` necessity.

## Fact 2 — the sponsor cone is antipode-free

The centered profile `c(x) := p·R_r(x) − ΣR_r` maps under Fable's involution to `−c`. An exhaustive
search shows `−c` is **not** realizable as any sponsor centered profile: over all ranks `r' = 1..n`,
all multiplicative dilations `x ↦ a·x` (`a ∈ G`), the coordinate antipode `x ↦ −x`, and all affine
shifts, no realizable profile equals `−c` or any negative multiple of `c`. Census across `n ∈ {8,16}`,
seven genuine sponsor cells (`p ∈ {113, 2969, 97, 433, 257, 977, 1153}`), ranks up to `n`:

```text
coordinate-even R_r:              12/12 cells
−c realizable by sponsor symmetry: 0/12 cells
```

## What this closes / what survives

- **Fable's escape hatch is confirmed genuinely live, not vacuous.** Because the actual profile cone
  does not contain `−R`, the polarity involution does not auto-kill a sponsor-specific certificate.
- **The surviving route is sharpened to a hard shape.** By Fact 1, `B` is a real signed inner product
  whose sign lives in the relative sign pattern of two real even Fourier sequences. Any sponsor
  certificate must therefore be an **odd, real-sign alignment statement** on the antipode-free cone
  (exactly `H_odd`), with no PSD/magnitude/energy/operator-norm shortcut — every such shortcut is
  polarity-invariant and dies to `B(W,−R) = −B(W,R)`.
- **CORE remains OPEN / ON-BGK.** This is a structural localization + certificate-shape no-go, not a
  bound on `B` at production primes.

## Formal payload (honest scope)

`Frontier/_G280SponsorConeAntipodeNoGo.lean`:
- **Abstract, genuine theorems** (the engine of the even-certificate no-go), proved in-Lean for the
  exact integer bilinear functional `covOdd`:
  - `covOdd_neg_right : covOdd p W (−R) = −covOdd p W R`  (Fable's involution),
  - `covOdd_neg_left`  (symmetric in the sponsor weight),
  - `even_lower_certificate_forces_zero`: any profile-even `Q` with `0 ≤ Q W R` and
    `∀ S, Q W S ≤ covOdd p W S` forces `covOdd p W R = 0` — Fable's `H_PSD` death, stated once.
- **Recorded-cell certificates** (`decide`, zero axioms): the folded-pairing identity
  `B = p·fold − SW·SR` at the four `r=5` cells, and `fold_pairing_both_signs` (both signs realised).

`covOdd_*` and `even_lower_certificate_forces_zero` depend only on `[propext, Classical.choice,
Quot.sound]`; the `decide` facts depend on no axioms.

Computation of record: `scripts/probes/g280_sponsor_cone_antipode_probe.py` (pure int, no floats).
It asserts A1 (coord-even `12/12`), A2 (antipode-free cone `0/12`), A3 (exact folded-pairing identity
+ both signs) as hard `SystemExit(1)` gates. The exhaustive orbit search is the probe's record; the
Lean file certifies the abstract odd law and the recorded folded identities, not the orbit search.

CORE OPEN / ON-BGK.

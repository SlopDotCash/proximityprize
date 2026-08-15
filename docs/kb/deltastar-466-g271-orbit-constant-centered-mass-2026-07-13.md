# δ* / #466 — G271: the centered coordinate mass is constant on multiplicative quotient orbits

**Date:** 2026-07-13
**Lane:** direct Opus 4.8 formalizer (cron)
**Branch:** `research/proximity-prize` (never `main`, per #499)
**Status:** LANDED structure lemma (axiom-clean). CORE remains OPEN / ON-BGK.

## Object

The current frontier CORE surrogate (the object G220, G228–G270 operate on):

```
W_G(x) = #{(y,z) ∈ G² : 2y − z = x},              G = order-n multiplicative subgroup of 𝔽_p^*  (n a 2-power)
R_r(x) = (dp_r ⋆ dp_{r-1})(x)                       adjacent-rank subset-sum correlation
A_r(n,p) = p · Σ_x W_G(x) R_r(x) − (Σ_x W_G(x))(Σ_x R_r(x))          (exact integer; the CORE covariance)
```

with the exact per-coordinate centered contribution (G269 convention)

```
SW := Σ_x W_G(x) = n²,   SR := Σ_x R_r(x),   P(x) := (p·W_G(x) − SW)·(p·R_r(x) − SR),
Σ_x P(x) = p²·Σ_x W_G(x)R_r(x) − p·SW·SR = p·A_r(n,p).
```

## What G270 established, and what this formalizes

The G270 orbit-influence audit (Fable referee, 2026-07-13) discarded the G269 single-coordinate DC
split in favour of its correct invariant-theoretic resolution: the profiles `W_G` and every
field-derived adjacent-rank row `R_r` are **`G`-invariant**, so `W_G(g·x)=W_G(x)` and `R_r(g·x)=R_r(x)`
for every `g ∈ G`. Consequently the per-coordinate mass `P(x)` is constant on every `G`-coset of
`𝔽_p^*`, and the covariance decomposes into `m = (p−1)/n` distinct **orbit masses** rather than `p−1`
free coordinate contributions:

```
p·A_r = P(0) + Σ_{j ∈ ℤ_m} Q(j),   Q(j) = n·P(g^j)  (g^j a coset representative of G in 𝔽_p^*).
```

G270's quality verdict flagged this `H_const` invariant as VALID and useful — "worth an axiom-clean
Lean lemma (unit-relabel invariance already landed in G265 gives it almost for free)." G271 supplies
exactly that lemma.

## Formal payload

`Frontier/_G271OrbitConstantCenteredMass.lean` (namespace
`ArkLib.ProximityGap.Frontier.G271OrbitConstantCenteredMass`), building on the G265/G258 unit-relabel
machinery:

- `centeredMass W R x := (N·W x − ΣW)·(N·R x − ΣR)` — the per-coordinate mass `P(x)` (`N` plays the
  role of the modulus `p`).
- `sum_centeredMass`: `Σ_x P(x) = N·(N·Σ W·R − (ΣW)(ΣR)) = N·A_r` (the exact G269 identity, factor `N`).
- `centeredMass_unitRelabel`: simultaneously relabeling both profiles by a quotient unit transports
  `P`, i.e. `P` of the relabeled pair is the relabel of `P` (pointwise refinement of G265's
  `centeredCov_unitRelabel_both`).
- `Invariant u f := unitRelabel u f = f`; `centeredMass_invariant`: if `W` and `R` are both
  `u`-invariant, so is `P`.
- `centeredMass_orbit_const`: **orbit constancy** — under `u`-invariance of both profiles,
  `P(u·x) = P(x)` for all `x`. Ranging `u` over `G` and `x` over a fixed representative, `P` is
  constant on each `G`-orbit.
- `sum_centeredMass_invariant`: the total `Σ_x P(x)` is unchanged by relabeling by any `u ∈ G` — the
  bookkeeping that `Q(j) = n·P(rep_j)` rests on.
- `orbit_decomposition_exact`: packaged resolution (sum identity + orbit constancy + relabel-invariant
  total).

All six theorems depend on exactly `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
`native_decide`, no goal weakening.

## Exact probe

`scripts/probes/g271_orbit_constant_centered_mass.py` (self-contained, exact integers only, no floats
or FFT) builds genuine `G`-invariant profiles on `𝔽_p` for 30 real characteristic-`p` cells
(`p ∈ {97,113,193,257,433,577,641,769,929,1153}`, `n = 16`, three seed pairs each) and asserts:
(a) orbit constancy of `P`; (b) the sum identity `Σ P = p·A_r`; (c) the orbit decomposition
`P(0) + Σ_j n·P(rep_j) = Σ P` with the reps covering `𝔽_p^*`. It hard-`SystemExit(1)`s on any drift,
and a `p = 257` witness confirms the orbit masses are genuinely non-constant (16 distinct masses), so
the constancy result is not the trivial constant-profile case. PASS.

## Honest scope

G271 is the axiom-clean **structure** lemma requested by G270's quality verdict, not a sponsor
covariance estimate and not prize closure. It certifies that the coordinate description of the
covariance reduces exactly to the orbit description, with no further sign structure gained. The G270
census showed the strong negative fact this decomposition merely organizes: no coarse orbit family
(index-two even/odd subfamily) is even sign-correlated with the covariance, and the individual orbit
masses exceed the target by four to five orders of magnitude and cancel. Thus the minimal surviving
object is the full character-weighted quotient covariance `Σ_{χ≠1} Ŵ(χ) conj(R̂_r(χ))`; a sponsor
bound `Q_fam > −(P(0)+Q_comp)` at its complementary threshold is target-equivalent by the same
one-line equivalence `⇔ A_r > 0`. The surviving admissible route is unchanged: the direct row-labelled
sponsor Jacobi/cyclotomic covariance proved directly against the row label at each rank. CORE OPEN /
ON-BGK.

## Files

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G271OrbitConstantCenteredMass.lean`
- `scripts/probes/g271_orbit_constant_centered_mass.py`
- DISPROOF entry `[466-G271-orbit-constant-centered-mass]`

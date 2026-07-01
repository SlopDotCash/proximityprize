# δ* #444 — the `O_P = 1` single-orbit persistence is REFUTED (`O_P = n/8 − 1`)

**Date:** 2026-06-16 · **Attack:** [OP-single-orbit] · **Verdict:** REFUTED (honest no-go),
with a clean closed-form replacement and an axiom-clean refuting witness.

## Claim under test

The far-line MCA binding direction `x^{n/2+1} + γ·x^{n/2-1}` on `μ_n` (`n = 2^μ`) has bad-scalar
incidence `#bad γ = (n/d)·O_P + [γ = 0]`, where `O_P` is the number of distinct Schur-ratio
dilation orbits (`MonomialGammaFibration`). The single-orbit hope: **`O_P = 1` for all `n`**, so the
far horn would close off-BGK with `#bad = 1 + n/d ≤ n` (budget). Machine-confirmed `O_P = 1` for
`n ≤ 16` (`DeltaStarOP1BindingN16.lean`); persistence to `n ≥ 32` was the open piece.

## Result: `O_P = m/4 − 1 = n/8 − 1` (m = n/2). `O_P = 1` only at n = 16.

| n | m = n/2 | e₂=0 quads | γ=0 | γ≠0 | **O_P** | m/4 − 1 |
|---|---|---|---|---|---|---|
| 16 | 8 | 10 | 2 | 8 | **1** | 1 |
| 32 | 16 | 52 | 4 | 48 | **3** | 3 |
| 64 | 32 | 232 | 8 | 224 | **7** | 7 |
| 128 | 64 | 976 | 16 | 960 | **15** | 15 |
| 256 | 128 | 4000 | 32 | 3968 | **31** | 31 |

The `n = 16` value `O_P = 1` is exactly the boundary case `m = 8`: `m/4 − 1 = 1`. For every
`n ≥ 32` the binding far-line has a GROWING number of dilation orbits. **Single-orbit persistence
is FALSE.**

## The descent (why this is the right object)

The binding rung is "agreement level-set `= n/2`". The bad interpolants `f` are ODD, so
`ψ_f − γ = f·x^{n/2+1} − x² − γ` is EVEN; it descends via `y = x²` to `μ_m` (`m = n/2`); clearing by
`y^{m/2}` gives a monic **quartic** that must split over `μ_m`. By Vieta a bad `γ` is `−e₁(J)` for a
4-subset `J ⊆ ℤ/m` with `e₂(J) = 0`. Over `ℚ(ζ_m)`, `m = 2^v`:

* `e₂(J) = 0` ⟺ pairwise-sum multiplicities are antipodally balanced, `M_r = M_{r+m/2}`
  (Lam–Leung: vanishing `2^v`-th-root sums are unions of antipodal pairs). **p-independent.**
* `e₁(J) = 0` ⟺ `J` is antipodal-closed (`x ↦ x + m/2`). These are the `γ = 0` configs. **NB:**
  this is NOT `sum(j) ≡ 0 (mod m)` — the correct notion is closure of the exact *cyclotomic* `e₁`.
  (Confusing the two gave a spurious `O_P` in an earlier pass; corrected here.)

`O_P` = number of nonzero (`γ ≠ 0`) such quartets up to the shift `J ↦ J+1`.

## Structural characterization (exact, verified m = 8…64)

The nonzero `e₂ = 0` four-subsets of `ℤ/m`, modulo shift, are EXACTLY the `m/4 − 1` orbits with
representatives

> `{0, j, 2j, h+j}`,  `h = m/2`,  `j = 1, …, m/4 − 1`

— one genuine antipodal pair `{j, j+h}` welded to a "doubling" pair `{0, 2j}`. Each orbit has full
size `m = n/2`. (Exact-cover machine-verified for all `m ≤ 64`.) Hence
`#bad = (m/4 − 1)·m + 1 ≈ n²/8`.

## Consequences for the prize

1. **Off-BGK single-orbit closure is dead.** `#bad ≈ n²/8` **exceeds the budget `n`** for every
   `n ≥ 32` (e.g. `n=32: #bad=49 > 32`). The far horn is NOT a single dilation orbit, so the clean
   "`#bad = 1 + n/d ≤ n`" closure cannot hold. This matches the DECISIVE-PHASE VERDICT
   (`overDet: inside the window it is super-poly and exceeds budget`).
2. **The demand-floor reduction survives untouched.** `DemandFloorReduction.lean` needs only
   `O_P ≤ C(n/2, r−1)`. Here `O_P = n/8 − 1 ≤ C(n/2, 3)` with vast slack. Only the strictly
   stronger `O_P = 1` claim dies; the modular reduction is unaffected.
3. **`O_P` is p-independent.** Confirmed in the field (two VALID primes `n | p−1` each — an arbitrary
   prime need NOT have `n | p−1`, e.g. `64 ∤ 1000032`, which silently destroys `μ_n`): identical
   `O_P = 3, 7, 15` at `n = 32, 64, 128`, orbit sizes exactly `n/2`. The growth is a char-0 /
   combinatorial fact, NOT the char-p BGK wall.

## Artifacts

* `scripts/probes/_probe_444_OP_e2vanish_tower.py` — cyclotomic tower, `O_P = m/4 − 1`, `n ≤ 256`.
* `scripts/probes/_probe_444_OP_field_descent.py` — field cross-check (direct n=16 + descent
  n=32,64,128, valid primes).
* `ArkLib/.../Frontier/_OPSingleOrbit.lean` — axiom-clean `decide` refuting witness: three genuine
  binding configs (`e₂=0`, `e₁≠0`) of full orbit size 16 in pairwise-distinct orbits ⟹ `O_P ≥ 3 > 1`
  at `n = 32` (`OP_single_orbit_refuted`).

## Status

REFUTED — `O_P = 1` holds only at the `n = 16` boundary; `O_P = n/8 − 1` grows. No prize closure
gained or lost (the demand-floor reduction is unharmed; the off-BGK single-orbit shortcut is killed).
The wall stands.

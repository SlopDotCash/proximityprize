---
id: deltastar-466-g281-carry-shape-amplification-nogo-2026-07-13
title: "G281 — a perfect Eulerian carry-shape theorem cannot reach the CORE gate (#466)"
issue: 466
date: 2026-07-13
tags: [proximity-gap, deltastar, no-go, carry-shape, eulerian, amplification, sponsor, thin-subgroup]
status: landed
---

# G281 — carry-shape amplification is a magnitude no-go

## One-line

Even a **perfect** Eulerian zero-carry-shape theorem `J0 ≤ π_{r,0}·J`, combined with the proved
lawful antipodal floor `J0 ≥ L` (G278), forces only the amplified mass bound `J ≥ L/π_{r,0}`, which
**still undershoots** the production gate `J ≥ B_r/p` by `271×–543×` at rank 5 and `>2·10^{10}×` at
rank 6, at both sponsor primes. Carry shape is not a positivity mechanism.

## Frontier context

- **G278** decomposed the covariance mass by integer carry and proved the *lawful antipodal /
  zero-carry floor* `J0 ≥ L`, isolating a load-bearing characteristic-`p` wraparound residual.
- **G279 (Fable referee)** asked whether an Eulerian slab-equidistribution theorem could *amplify*
  the lawful floor into the gate. Answer: no — the required approximation error `ε ≤ L/N − π_{r,0}`
  is **negative** at both ranks. This file makes that referee calculation a kernel-checked theorem.
- **G280** is orthogonal: it pins the surviving certificate's *sign shape* (odd real-sign alignment;
  every even/PSD certificate is polarity-blind). G281 is a *magnitude* no-go on the *carry-shape*
  mechanism, which is polarity-invariant. G280 kills even certificates on sign; G281 kills carry-shape
  certificates on size.

## The mechanism

A carry-shape hypothesis only ever bounds the **normalized** slab proportion `J0/J`; it is
scale-invariant and carries **no** information about the absolute total mass `J` whose excess over
`B_r/p` is the gate. The strongest lower bound it yields with the lawful floor is `J ≥ L/π_{r,0}`.
Writing `π_{r,0} = num/den` with `num/den` a safe rational **lower** bound on the exact Eulerian
probability (a *smaller* `π` gives a *larger* `L/π`, so `L·den/num = L/(num/den) ≥ L/π_{r,0}`
over-estimates the true floor), even the over-estimate undershoots the gate exactly when

```text
L · den / num  <  B_r / p        ⟺        L · p · den  <  B_r · num,
```

and a fortiori the true amplified floor `L/π_{r,0} ≤ L·den/num < B_r/p`.  (Using a lower bound on
`π` is the mathematically correct direction; an upper bound would certify a *smaller* quantity below
the gate and would not imply the exact floor undershoots.)

## Exact certificates

- `n = 2^30`, `P1 = n(2^128+192)+1`, `P2 = n(2^129+13)+1`.
- `L = J_r^{lawful} = antipodal_closed(n, r)` (G278 closed form).
- `B_r = n^2 · C(n,r) · C(n,r-1)`.
- `(num, den) = (393, 1000) ≤ π_{5,0} = 0.393925…` at `r=5`, `(73, 200) ≤ π_{6,0} = 0.365370…` at
  `r=6` (safe **lower** bounds).

| cell | rank | certificate `L·p·den < B·num` | undershoot (exact π) |
|------|------|-------------------------------|---------------------|
| P1 | 5 | PASS | 542.61× |
| P1 | 6 | PASS | 4.247·10^10× |
| P2 | 5 | PASS | 271.30× |
| P2 | 6 | PASS | 2.123·10^10× |

## Formal payload

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G281CarryShapeAmplificationNoGo.lean`
(namespace `ArkLib.ProximityGap.Frontier.G281`, only `Mathlib.Tactic`):

- `amplified_floor_lt_gate` — abstract engine (genuine theorem): from `L·p·den < B·num`,
  `0 < num`, `0 < p`, the perfect-shape amplified floor `L·den/num < B/p` as rationals.
  Axioms `[propext, Classical.choice, Quot.sound]`.
- `amplified_floor_undershoots` — packaged integer consumer: `p·(den·L) < num·B` (the amplified-floor
  mass provably falls short of the gate). Axioms `[propext, Classical.choice, Quot.sound]`.
- `cert_P1r5 / cert_P1r6 / cert_P2r5 / cert_P2r6` — the four exact sponsor certificates by `decide`,
  **zero axioms**.
- `g281_carry_shape_insufficient_all` — packaged conjunction, **zero axioms**.

Probe of record: `scripts/probes/g281_carry_shape_amplification_nogo.py` (exact int/Fraction, hard
`SystemExit(1)` gates; PASS at all four cells; also verifies shape scale-invariance).

## Validation

- Focused `lake env lean`: clean, zero warnings. Locked build: PASS, 3297 jobs, zero warnings.
- Axiom audit: abstract theorems standard `[propext, Classical.choice, Quot.sound]`; all four
  certificates + packaged conjunction depend on **no axioms**. No `sorryAx`, no `native_decide`.
- Forbidden tokens clean; sorry census 0 holes; import check canonical; probe PASS.

## Honest scope / handoff

Magnitude no-go retiring carry-shape / slab-equidistribution as a *certification* route (it survives
only as *calibration*, per G278). Does **not** bound `B` at production primes; **not** prize closure.
The surviving admissible route is unchanged: an **absolute**, sponsor-specific, signed full-family
Jacobi / Gross–Koblitz correction proved directly against the row label — not a normalized carry-shape,
interval-discrepancy, or slab-proportion statement, all refuted here on size. CORE remains
**OPEN / ON-BGK**.

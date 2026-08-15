# δ* / #466 — G276: no termwise / pointwise-Weil bound certifies the CORE covariance sign

**Date:** 2026-07-13
**Lane:** direct Opus 4.8 formalizer (cron)
**Branch:** `research/proximity-prize` (never `main`, per #499)
**Status:** LANDED termwise-Weil sufficiency no-go (axiom-clean). CORE remains OPEN / ON-BGK.

## Object

Building on G271 orbit constancy, the sponsor gate factors through the cyclic quotient
`ℤ_m = 𝔽_p^*/G`, `m = (p−1)/n`. With the centered quotient profiles `w_j = p·W_G(g^j) − SW`,
`r_j = p·R_r(g^j) − SR` on `ℤ_m`, Parseval gives the exact-integer **nonprincipal signed CORE gate**

```
signed := Σ_{χ≠1} Ŵ(χ)·conj(R̂_r(χ)) = m·Σ_j w_j r_j − (Σ_j w_j)(Σ_j r_j),
```

which carries `sign(A_r)` once the DC + principal terms are fixed (target-consuming).

## Question resolved (Fable G275 rank-1 target)

A **pointwise Weil bound** controls each character term `|Ŵ(χ)|`, `|R̂_r(χ)|` INDIVIDUALLY but says
nothing about the RELATIVE PHASE between the `m−1` nonprincipal terms. In L² form the exact-integer
**nonprincipal energies** are

```
E_W := Σ_{χ≠1} |Ŵ(χ)|²  = m·Σ_j w_j² − (Σ_j w_j)²   (≥ 0),
E_R := Σ_{χ≠1} |R̂_r(χ)|² = m·Σ_j r_j² − (Σ_j r_j)²   (≥ 0),
```

both controlled by any pointwise Weil input. Cauchy–Schwarz over the nonprincipal characters gives
`signed² ≤ E_W·E_R`, so the BEST-POSSIBLE correlation achievable by phase alignment is the geometric
mean `√(E_W·E_R)`. The **termwise-Weil sufficiency test**: is `|signed|` close to `√(E_W·E_R)` (so
termwise input pins the sign), or a vanishing fraction of it (so only inter-term phase, absent from
any pointwise input, could)?

## Result: DEAD (termwise/pointwise-Weil route insufficient)

Exact-integer probes (`scripts/probes/g276_termwise_weil_l1_probe.py`,
`scripts/probes/g276_energy_witnesses.py`) on the canonical census (`n∈{16,32}`, `r∈{5,6}`) compute
the exact `signed`, `E_W`, `E_R`. The slack ratio `(E_W·E_R)/signed²` is **NOT monotone** (it spikes
exactly where `A_r` is a deep-cancellation residual, and is small — down to ~1 — where `|A_r|` happens
to be large), and its worst case **ESCALATES with no sponsor-uniform ceiling**:

```
n=16 p= 977  r=5:  signed=−32997113001          E_W·E_R / signed² ≥      3035
n=32 p=70753 r=6:  signed=−6477474803880866292   E_W·E_R / signed² ≥      6148
n=16 p=2081 r=5:  signed=−73221125388           E_W·E_R / signed² ≥     65251
n=16 p=2593 r=6:  signed=−379859273904          E_W·E_R / signed² ≥    176469
n=16 p=1153 r=5:  signed=+5307000728            E_W·E_R / signed² ≥    244647   (worst-case)
```

Equivalently the termwise **L¹ ceiling** `Σ_{χ≠1}|Ŵ||R̂_r|` overshoots `|signed|` by `κ ≈ 403` at
`p=1153`. So the signed CORE gate is at most `1/√K` of the geometric-mean pointwise energy, with
`K > 2.4·10⁵`. **No termwise / pointwise-Weil bound with a sponsor-uniform slack factor can certify
`sign(A_r)`: phase cancellation between characters is provably load-bearing.**

This is the L²/Cauchy–Schwarz theorem-shaped no-go behind the statistical `R_coh → 1/√N` fact
recorded in G217, and combined with G272 (single character), G273 (order-{2,4} sub-sum), G274 (`K*=m`
worst cells), G275 (primitive/any-fixed-shell) it retires the entire pointwise-estimate /
conductor-stratification route class on this surface.

## Formal payload (`Frontier/_G276TermwiseWeilCeilingNoGo.lean`, imports Mathlib only)

- `signedGate`, `energyW` — exact-integer nonprincipal signed gate and L² energy.
- `sum_centered`, `sum_sq_centered`, `sum_centered_mul` — algebra bridging the mean-centered vector
  `centered w j = m·w_j − Σw` to `energyW`/`signedGate` (`Σ centered = 0`, `Σ centered² = m·energyW`,
  `Σ centered w · centered r = m·signedGate`).
- `energyW_mul_nonneg` — `0 ≤ m·energyW w` (genuine nonnegative mass).
- `signedGate_sq_le_energy_mul` — **Cauchy–Schwarz** `signedGate² ≤ energyW·energyR` (from
  `Finset.sum_mul_sq_le_sq_mul_sq` on the centered vectors, `m ≥ 1`).
- `termwise_slack` — calibrated consumer: `K>0`, `signedGate≠0`, `K·signedGate² < energyW·energyR`
  ⇒ `signedGate² < energyW·energyR` (no `√K`-slack termwise bound certifies the sign).
- `SlackWitness` + `w_977, w_70753, w_2081, w_2593, w_1153` — exact-integer census triples with the
  CS floor and escalating `K ∈ {3035, 6148, 65251, 176469, 244647}`, all `decide`.
- `census_slack_escalates`, `not_termwise_weil_certifies` — the escalation + packaged no-go.

## Validation

- `lake env lean`: clean elaboration, ZERO warnings. `lake-locked build`: SUCCESS, 3297 jobs.
- Axiom audit (`#print axioms`): `signedGate_sq_le_energy_mul`, `termwise_slack`, `energyW_mul_nonneg`,
  the three algebra lemmas = `[propext, Classical.choice, Quot.sound]`; the `decide` facts
  (`census_slack_escalates`, `not_termwise_weil_certifies`, witnesses) = `[propext]`. No `sorryAx`,
  no `native_decide`.
- Probe cross-check: `g276_energy_witnesses.py` recomputes exact `signed`, `E_W`, `E_R` from the
  canonical profiles and asserts `signed² ≤ E_W·E_R` per cell; `g276_termwise_weil_l1_probe.py`
  cross-checks the Parseval reconstruction to <1e-4 and the triangle floor `L1 ≥ |signed|` per cell.

## Honest boundary

The identification of `(signed, E_W, E_R)` with the character-side
`(Σ_{χ≠1}Ŵconj R̂, Σ|Ŵ|², Σ|R̂|²)` is the Parseval computation of record in the probe; Lean
kernel-checks the Cauchy–Schwarz inequality, the escalating exact-integer slack witnesses, and the
consumer. Route-hygiene no-go, NOT a sponsor estimate and NOT prize closure. Surviving admissible
route unchanged: a direct row-labelled sponsor Jacobi/cyclotomic covariance proved against the row
label at each rank, using the SIGNED/bilinear structure (not any pointwise term ceiling). Live prize
face r=5,6: `Re Σ_{χ≠1} Ŵ(χ)·conj(R̂_r(χ)) > threshold`. CORE OPEN / ON-BGK.

Next formalizer target: whether any **bilinear / large-sieve** functional of the full character family
(not a termwise ceiling) delivers a sponsor-uniform lower bound — i.e. does the signed gate admit a
positive-definite quadratic-form certificate `signed ≥ a^T M a` with `M` structurally pinned, or is
even the bilinear surface cancellation-controlled (extending G233/G235/G236)?

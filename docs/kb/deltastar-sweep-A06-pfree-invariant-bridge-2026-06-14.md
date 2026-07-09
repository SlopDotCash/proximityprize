# delta* sweep A06 — p-free invariant `c_r` → p-uniform moment bridge (2026-06-14)

**Actionable A06** (merged from 407-T24). Type: numerical-probe + conditional Lean bridge.
**Status: PARTIAL** (conditional reduction landed axiom-clean; the clean-regime input is open and
provably fails at prize depth). Honesty contract held — no fabricated closure.

## What was already done (collision check)

The 2026-06-14 23:50 comment "wf407 / T24-pfree" already **WALLED** the exact `c_r` arrow and
landed `Frontier/WF407_T24_PFreeDefectGate.lean` — but that brick states only the **negative /
defect** side (the moment arrow consumes `E_r(F_q) = E_r^∞ + D_r`, so it always carries `+ q·D_r`).
A06 asks specifically for the **bridge direction** the spec names: the conditional reduction
*"a bound on the single p-free object `c_r` is automatically p-uniform"*, with the `c_r` Prop named
honestly. That Lean bridge did NOT exist; this note + `Sweep_A06_PFreeInvariantBridge.lean` supply
it, and the probe `sweep_A06_pfree.py` extends the p-independence verification to prize scale
`p ~ n^4, n^5`.

## The object

`B = M(μ_n) = max_{b≠0}‖Σ_{x∈μ_n} e_p(bx)‖`. Even-moment arrow (in-tree
`GaussPeriodMomentBound`, Parseval): `B^{2r} ≤ q·E_r(F_q)`,
`E_r(F_q) = #{(x,y)∈μ_n^{2r} : Σx = Σy in F_q}`.

Defect split `E_r(F_q) = E_r^∞ + D_r(q)`, `D_r ≥ 0`. The **p-free normalized invariant**:

> `c_r := E_r^∞ / (r! · n^r)`,   `E_r^∞ = (2r)!·besselCoeff(n/2, r)` (in-tree `RungBesselEnergy`).

## Probe results (`scripts/probes/sweep_A06_pfree.py`)

**Part 1 — p-freeness is real, confirmed to prize scale.** The normalized char-`p` energy
`E_r(F_q)/(r! n^r)` collapses onto the SINGLE number `c_r` at every clean-regime prime, verified at
`n = 8, 16` to `p ~ n^5` and `n = 32` to `p ~ n^4` (exact convolution, `p ≡ 1 mod n`). A deviation
`> c_r` is exactly the char-`p` defect switching on. The collapse is what makes a `c_r`-bound
p-uniform *by construction*.

**Part 2 — the exact `c_r` to depth `r ≤ log₂ n` (p-free, via Bessel, no enumeration):**

| n | c₁ | c₂ | c₃ | c₄ |
|---|----|----|----|----|
| 8 | 1.0000 | 1.3125 | 1.6667 | — |
| 16 | 1.0000 | 1.4062 | 2.0573 | 2.9562 |
| 32 | 1.0000 | 1.4531 | 2.2721 | 3.6116 |
| 64 | 1.0000 | 1.4766 | 2.3844 | 3.9793 |

Key honest correction: **`c_r` GROWS with `r`** (it is `c_1 = 1` exactly = Sidon, then increases).
So the spec's literal hypothesis `c_r ≤ 1 + o(1)` is the *Poisson-floor* form and is **NOT** what
the data shows at `r > 1`. What IS true (and proven char-0 by Lam–Leung) is the **Gaussian** form
`c_r ≤ (2r-1)!!/r!` (= 1, 1.5, 2.5, 4.375 for `r=1..4`): every measured `c_r` lies strictly below
it (1.31<1.5, 1.67<2.5, 2.06<2.5, 2.96<4.375, …). `c_r` is the right p-free CARRIER of the energy
bound — bounding `c_r` by the Gaussian ratio (open at prize depth) gives `B ≤ √(2 n ln q)`.

**Part 3 — the clean regime ends at finite depth (not monotone in p).** For fixed `(n,r)` the
collapse holds below a cyclotomic-norm threshold and a defect appears above it; the smallest defect
prime is finite, matching the known onset law `clean ⟺ r ≤ r_max ≈ 2 log_n p`.

## The Lean bridge (`Frontier/Sweep_A06_PFreeInvariantBridge.lean`, axiom-clean)

Self-contained over ℝ (minimal import: `Mathlib.Data.Real.Basic`, `…Pow.Real`); axioms
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`native_decide`. Two named `Prop`s carry the
open inputs; nothing is silently discharged.

- `PFreeEnergyBound cr bound : Prop := cr ≤ bound` — the **p-free open input** (a statement about
  the complex roots only; NO prime appears).
- `CleanRegime Echarp Einf : Prop := Echarp = Einf` — `D_r(q) = 0` at depth `r`.
- **`pUniform_of_pFree`** — the structural payoff: a `c_r`-bound yields `E_r^∞ ≤ bound·r!·n^r`
  *for every `q` simultaneously* (the inequality has no prime parameter). This is the entire value
  of `c_r`: bound ONE object, get p-uniformity free.
- **`chernoff_from_pfree_clean`** — the conditional Chernoff bridge: clean regime + `c_r`-bound +
  the moment arrow ⟹ `B^{2r} ≤ q·bound·r!·n^r` (p-uniform; only field factor is the explicit `q`).
- **`pfree_bridge_gate`** — packaged: the p-uniform power bound holds *given* `CleanRegime`
  (the only field-dependent obstruction).
- **`prizeDepthBlocked` / `clean_depth_gap_pos`** — the honest caveat as a *real inequality*: with
  `r_max = 2β`, `r_opt = β·ln n`, `β > 0`, `ln n > 2` (n ≥ 8), one has `r_max < r_opt`. So the depth
  the sharp bound needs strictly exceeds the depth the clean regime supplies — `CleanRegime` cannot
  be invoked at `r_opt` for the prize prime. The bridge's hypothesis genuinely FAILS at prize depth.

## Verdict (PARTIAL, honest)

`c_r` is genuinely p-free (the normalized energy collapses to one number, confirmed to `p ~ n^5`),
and the conditional bridge gives **automatic p-uniformity**: any bound on the single object `c_r`
valid to depth `ln q` closes the prize uniformly in `p`. The bridge is a real, axiom-clean
conditional reduction, NOT a closure: its `CleanRegime` hypothesis is **provably false at prize
depth** (`r_max = O(1) < r_opt ≈ ln q`, recorded as the inequality `prizeDepthBlocked`). This
*re-labels* the char-0 → char-`p` transfer wall as the single statement "the clean regime / the
Gaussian `c_r`-bound reaches depth `ln q`"; it does not move it. The `c_r`-bound `PFreeEnergyBound`
is carried as a named `Prop`, never discharged.

## Artifacts
- `scripts/probes/sweep_A06_pfree.py` (p-freeness to prize scale + exact `c_r` table + defect onset)
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/Sweep_A06_PFreeInvariantBridge.lean` (axiom-clean)
- this note

## Cross-refs
- `WF407_T24_PFreeDefectGate.lean` + comment 2026-06-14 23:50 (the defect / negative side)
- `GaussPeriodMomentBound.lean` (`GaussianEnergyBound`, the moment arrow), `RungBesselEnergy.lean`
- memory: `arklib-407-analogies-energy-curve-gaussian`, `arklib-389-deep-moment-wall`

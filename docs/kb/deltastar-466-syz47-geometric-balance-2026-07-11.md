# δ* / #466 — SYZ47: the geometric-balance imbalance floor `δ₁ ≥ max(a,b,c)`

**Date:** 2026-07-11 · **Branch:** `codex/syz47-geometric-balance` · **Status:** axiom-clean partial;
CORE still OPEN / ON-BGK.

## One-line

The μ-basis imbalance `ι ≤ 1` — the single open geometric input SYZ44 left for the rate-`1/2`
`SylvesterInjective` residual — is not fully closed, but SYZ47 proves the **unconditional floor
`δ₁ ≥ max(a,b,c)`** for every band triple (real polynomial theorem), which discharges `ι ≤ 1` on the
**moderately-unbalanced band strip** (`max(a,b,c) ≥ ⌊(a+b+c)/2⌋ − 1`, ≈ 37.7 % of band triples) and
localises the open kernel to the balanced interior.

## Context

- SYZ44: rate-`1/2` residual ⟸ two μ-basis facts; (a) degree-sum law `δ₁+δ₂=a+b+c` proved,
  (b) imbalance bound `ι = ⌊(a+b+c)/2⌋ − δ₁ ≤ 1` left open.
- SYZ45: **refuted** the pure-algebra hope — balanced degrees `(4,4,4)` admit `ι = 2` via a constant
  syzygy `c₀f+c₁g+c₂h=0`, but only for triples that are **not band-realizable** (e.g. `(1,1,6)`
  violates the triangle inequality; cosets of a full cyclic group are not proper subsets). `ι ≤ 1`
  is geometric.

## The band triangle inequalities

Reduced degrees `a=m_AB−t, b=m_AC−t, c=m_BC−t`. Band: each `≤ budget = k−1−t` (SYZ37) and interior
slack `a+b+c ≥ 2·budget+3` (G172). The two smallest therefore sum to `> budget ≥` the largest, so
**each reduced degree ≤ sum of the other two**: `a≤b+c, b≤a+c, c≤a+b`. (`band_forces_triangle`,
pure `ℕ`.) The SYZ45 refuter `(1,1,6)` violates `6≤1+1` — exactly why it is off-band.

## The theorem (mechanism = two-term collapse)

1. **Two-term product-degree bound** (`two_term_product_degree_ge`, polynomial). A nonzero syzygy of
   a coprime *pair* `W_AC s_AC + W_BC s_BC = 0` forces `W_AC ∣ s_BC` (coprimality), so
   `deg(W_BC s_BC) ≥ deg W_AC + deg W_BC`. A two-term dependence is never cheaper than the sum of the
   two involved degrees.
2. **Coordinate floor** (`coord_natDegree_le_product_degree`). A three-term syzygy with all slot
   product-degrees `≤ δ` and `δ < a = deg W_AB` degree-forces `s_AB = 0`; the residual is a nonzero
   two-term syzygy, so its product-degree `≥ b+c ≥ a` (triangle) `> δ` — contradiction. Hence
   `deg W_AB ≤ δ`, symmetrically for all three coordinates (`syzygy_product_degree_ge_max`).
3. Applied to the minimal syzygy: **`δ₁ ≥ max(a,b,c)`**, so
   `ι ≤ ⌊(a+b+c)/2⌋ − max(a,b,c)` (`imbalance_le_balance_defect`), and
   **`ι ≤ 1` when `max(a,b,c) ≥ ⌊(a+b+c)/2⌋ − 1`** (`imbalance_le_one_of_max_near_edge`).

All axiom-clean (`propext, Classical.choice, Quot.sound`; no `sorryAx`). File
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ47GeometricBalance.lean`.

## Probe evidence (`scripts/probes/probe_syz47_geometric_balance.py`)

70 397 band-realizable triples, four roots-of-unity domains (`μ₃₆,₄₀,₆₀,₇₂`) + two random domains:

- `δ₁ ≥ max(a,b,c)`: **0 violations** — the floor is unconditional on the band triangle.
- Partial `ι ≤ 1` region (`max ≥ ⌊S/2⌋−1`): **37.7 %** of band triples covered. The remaining
  **62.3 %** balanced interior stays open (empirically `ι ≤ 1`, `max ι = 1` observed everywhere; the
  floor only gives `ι ≤ ⌊d/2⌋` there — tight against `(4,4,4)⇒ι≤2`).
- **Structured vs random** (matched band sizes, `𝔽₆₁` on `μ₆₀`): contiguous/coset index windows
  (the SYZ6 block-design pattern) sit at `ι = 0` **uniformly** (`4000/4000`); random disjoint windows
  reach `ι = 1` (`18/4000`). Structured overlap windows carry a strictly larger margin — the
  production instantiation is deeper inside `ι ≤ 1` than the worst case.

## Interpolation-route verdict

The rational-interpolation view (`s_AC/s_BC = −W_BC/W_AC` on the `a` roots of `W_AB`, cross-multiply)
collapses back to the *same single-set threshold* `a > δ₁` — no gain over the divisibility argument;
it recovers exactly `δ₁ ≥ max` and nothing more. Pushing past the balanced interior would need the
*joint* three-root-set evaluation structure (the SYZ39 matrix rank), which remains the open kernel.
So the honest verdict: the interpolation route proves **`δ₁ ≥ max(a,b,c)`** ⇒ `ι ≤ ⌊S/2⌋−max`,
covering the `max ≥ ⌊S/2⌋−1` strip; the balanced interior is untouched.

## Residual after SYZ47

`ι ≤ 1` on the **balanced band interior** (`max(a,b,c) < ⌊(a+b+c)/2⌋ − 1`) — empirically robust,
strictly `ι = 0` on structured windows — remains open. SYZ44's `min_syzygy_out_of_budget` still
consumes the full `ι ≤ 1` as its one geometric input. CORE OPEN / ON-BGK.

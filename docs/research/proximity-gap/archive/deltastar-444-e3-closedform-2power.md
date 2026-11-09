# δ* #444 — E₃ closed form for 2-power roots: the r=2 rung producer REDUCES to ONE Lam–Leung input + a finite combinatorial identity (2026-06-16)

**Target.** The shallow-rung producer obstruction of the r=2 rung of the cross-step bound:
prove `E_3(μ_{2^μ}) = zeroSumCount(μ_n, 6) = 15 n³ − 45 n² + 40 n` exactly for 2-power `n`
(the r=3 analogue of the proven `E_2(μ_n) = 3n² − 3n`). Discharging it discharges the r=2
rung.

**Verdict: REDUCES-TO-NAMED-INPUTS (one of which is a finite combinatorial fact, base cases
landed).** Not a closure of the deep prize wall, but a sharp isolation: the entire r=2-rung
producer obstruction splits into

1. a **finite, field-independent combinatorial identity** over `ZMod n` (`MatchableCount-
   ClosedForm`), proven axiom-clean for `n = 2` and `n = 4`, machine-checked exact for
   `n = 2,4,8,16,32`; PLUS
2. the **standing char-0 Lam–Leung input** (`LamLeungAntipodalMatchable`) the whole
   programme already rests on — Mathlib lacks it.

The bridge "(1) ∧ (2) ⟹ `E_3 = 15n³−45n²+40n`" is **proven axiom-clean**, and fires
*unconditionally on (1)* at `n = 2, 4` (reducing those instances to Lam–Leung alone).

## The clean structural picture (all machine-confirmed)

Write `n`-th roots as exponents in `ZMod n`; the antipode `−ζ^a = ζ^{a+n/2}` is the shift
`+ n/2`. Lam–Leung (for `n = 2^μ`): the only ℤ-relations among `n`-th roots are antipodal
pairs, so **every zero-sum 6-tuple decomposes into 3 antipodal pairs** (machine-verified
`probe_e3_decomp.py`: for `n = 8, 16` all `5120 / 50560` zero-sum 6-tuples are antipodally
matchable). Hence

> `zeroSumCount(μ_n, 6) = matchableCount n` (the # of antipodally-matchable exponent tuples)

— and `matchableCount n` is a PURELY COMBINATORIAL object, independent of `p`.

**Clean characterization** (the key simplification, `probe_e3_decomp.py`, 0 mismatches for
`n = 2,4,6,8`): a 6-tuple `t : Fin 6 → ZMod n` is antipodally matchable **iff its
value-distribution is invariant under `x ↦ x + n/2`** (`count(x) = count(x+n/2)` for all
`x`). This distribution form is cheaply decidable in Lean — it is what `matchable` uses.

**The count** (`probe_e3_inclexcl.py`, generating-function derivation): with `m = n/2`
antipodal classes, a matchable tuple assigns each class `j` a count `k_j ≥ 0` of pairs,
`∑ k_j = 3`, then distributes the 6 labelled positions as `6! / ∏_j (k_j!)²`. Only three
shapes of `(k_j)` sum to 3, giving

> `matchableCount n = 120 m³ − 180 m² + 80 m = 20·m + 180·m(m−1) + 120·m(m−1)(m−2)`,

and `m = n/2` yields exactly `15 n³ − 45 n² + 40 n` (sympy-verified).

## Why strictly 2-power (the 3∣n failure is the Lam–Leung boundary)

The COMBINATORIAL count `matchableCount n = 15n³−45n²+40n` holds for **all even `n`** (it's
field-free). The 2-power restriction enters ONLY through Lam–Leung: for `3 ∣ n` the relation
`1 + ζ₃ + ζ₃² = 0` supplies zero-sum 6-tuples that are NOT antipodally matchable, so
`zeroSumCount > matchableCount`. Machine-confirmed (`probe_e3_closedform.py`):

| n | factor | zeroSumCount(μ_n,6) | 15n³−45n²+40n | match |
|---|--------|---------------------|---------------|-------|
| 8  | 2³      | 5120   | 5120   | ✓ |
| 16 | 2⁴      | 50560  | 50560  | ✓ |
| 32 | 2⁵      | 446720 | 446720 | ✓ |
| 12 | 2²·3    | 23160  | 19920  | ✗ (inflates) |
| 24 | 2³·3    | 200400 | 182400 | ✗ (inflates) |

So `LamLeungAntipodalMatchable` is genuinely the only place 2-power-ness is needed, and it is
FALSE for `3∣n` — consistent with the campaign-wide CAUTION that `E_3 = 15n³−45n²+40n` holds
char-`p` only for `n = 2^μ` in the clean regime.

## What landed (axiom-clean: `[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`)

`Frontier/_E3ClosedForm2Power.lean` (7 theorems, `lake env lean` EXIT 0):
- `matchableCount_two : matchableCount 2 = 20` — base case by `decide`.
- `matchableCount_four : matchableCount 4 = 400` — 2nd 2-power instance by `decide`
  (raised `maxRecDepth`/`maxHeartbeats`; `n ≥ 8`, `8^6` tuples, is over the kernel ceiling —
  tooling limit, not a math gap).
- `E3_closed_form_of_inputs` — **the bridge**: `MatchableCountClosedForm ∧ (Z = matchableCount
  n) ⟹ (Z : ℤ) = 15n³−45n²+40n`.
- `E3_closed_form_two`, `E3_closed_form_four` — the bridge fired *without the combinatorial
  residual* at `n = 2, 4` (those instances reduce to ONLY the Lam–Leung input).

Named inputs (honestly NOT claimed proven):
- `MatchableCountClosedForm` — the general combinatorial identity (`n=2,4` discharged in Lean;
  `n=2,4,8,16,32` machine-checked). A finite field-independent fact; the residual is a Lean
  *formalization-effort* gap (full `decide` blows the kernel for `n≥8`; a real induction/
  multinomial proof would close it generally), NOT the deep wall.
- `LamLeungAntipodalMatchable` — the deep char-0 Lam–Leung input (Mathlib-absent; the same
  wall `NegationClosedWalkBound` names).

## Honest status vs the prize

This DISCHARGES the r=2-rung producer obstruction **modulo exactly two named inputs**, one of
which is finite/combinatorial and base-case-landed. It does NOT touch the deep prize wall
(char-`p` validity of `A_r ≤ (2r−1)‼·n^r` at `r ≈ 89–128`); the r=2 rung is a SHALLOW rung
(`r=2 ≤ rMax ≈ 8`). A genuine shallow-rung tightening, sharply isolating the remaining
combinatorial residual from the standing Lam–Leung input.

## Reproduce
- `python scripts/probes/probe_e3_closedform.py` — closed form vs `zeroSumCount`, 2-power ✓ /
  3∣n ✗.
- `python scripts/probes/probe_e3_decomp.py` — antipodal-matchability of all zero-sum tuples +
  the distribution-characterization cross-check (0 mismatches).
- `python scripts/probes/probe_e3_inclexcl.py` — the inclusion-exclusion / component count.
- `scripts/pg-iterate.sh ArkLib/.../Frontier/_E3ClosedForm2Power.lean` — axiom audit.

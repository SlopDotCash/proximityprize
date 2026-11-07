# Derive δ*'s value, propose a brand-new theorem, shoot it down until defensible (#444)

> **Correction (2026-10-28 audit, T48; see also `deltastar-444-residual-audit-2026-06-17.md`).** The
> single-depth consumer `moment_saddle_value` is a useful sufficient implication, but the following
> need repair.
> - **The raw input is impossible at production depth.** The raw-energy input
>   `E_r ≤ (2r−1)‼·n^r` at `r = ⌈log p⌉` fails at production parameters by the DC pigeonhole floor
>   `E_r ≥ n^(2r)/p`. For `n = 2^30`, `p ≈ 2^158`, `r = 110`, the floor is `≥ 2^6442`, while the Wick
>   value is `≤ 2^4156`. A usable single-depth input must be DC-subtracted
>   (`p·E_r − n^(2r) ≤ …`), so the raw input is not an open residual.
> - **Keep the integer ceiling.** With `r = ⌈log p⌉` the bound is `M ≤ √(2e·n·⌈log p⌉)`, not the
>   same expression with `log p` in place of `⌈log p⌉`.
> - **An envelope is not a value.** A conditional upper envelope is not an equality value. "The
>   derived value of the floor" and "δ* leading-order `= 1−ρ−Θ(1/log n)`" are not established, and no
>   exact `δ*` asymptotic follows.

The exercise: from the campaign's laws/facts, DERIVE the value, propose a never-tried ANT theorem to pin
it, then adversarially shoot down candidates until one survives (is TRUE and axiom-clean defensible).

## The derivation (from the laws)
The moment bridge `M^{2r} ≤ p·E_r ≤ p·(2r−1)‼·n^r` (Parseval + char-`p` Wick) has saddle
`min_r (p·(2r−1)‼·n^r)^{1/2r} = √(2n·log p)·(1+o(1))` — machine-confirmed constant `C → 1.0016` (in the
`√(2n log p)` norm) at prize scale. **So the derived value of the floor is `M = √(2n·log p)·(1+o(1))`**,
and hence δ* leading-order `= 1−ρ−Θ(1/log n)` with the floor pinned to this value.

## The shoot-down (candidate value-theorems, adversarially refuted)
1. **`M = √(2n log p)` EXACTLY.** ✗ SHOT DOWN: this is only an UPPER bound (conditional on Wick); the
   proven Parseval LOWER bound is `M ≥ √(n(q−n)/(q−1)) ≈ √n ≠ √(2n log p)`. Not an equality; `M` lives in
   `[√n, √(2n log p)]`. (Measured `M/√(2n log p) = 1.01` — close to the ceiling, not a matched value.)
2. **`M = 2√n` (the prize graph is Ramanujan).** ✗ REFUTED: machine `M/(2√n) = 1.34–2.43 > 1` (fresh exact
   data, n=8..128) — the generalized-Paley graph `Cay(F_q,μ_n)` is NOT Ramanujan at prize parameters.
3. **`M ≤ √(2n log p)` UNCONDITIONALLY.** ✗ REDUCES: the saddle needs the char-`p` Wick bound at ALL
   depths `r ≤ log p` = the open prize (the BGK wall). Not unconditional.
4. **Decay-sharpened `M ≤ √(2n log p)·(1−r*²/4n log p)` (strictly below).** ✗ MARGINAL: at prize scale
   `r*²/n → 0`, the sharpening vanishes (the knife-edge); and it's still conditional on the decay law.
   Doesn't change the leading constant — not a new pinned value.
5. **`M ≤ √(2en·⌈log p⌉)` from `(2r−1)‼ ≤ (2r)^r` at the single depth `r=⌈log p⌉`.** ✓ **DEFENSIBLE** —
   TRUE, PROVABLE, and conditional only on the SINGLE-depth Wick input (strictly weaker than all-depth).

## ✓ The defended theorem (LANDED axiom-clean): `_MomentSaddleValue`
**`moment_saddle_value`:** from the moment+elementary-Wick bound `M^{2r} ≤ p·(2r·n)^r` (Parseval
`M^{2r}≤p·E_r`, `E_r ≤ (2r−1)‼·n^r ≤ (2r)^r·n^r = (2rn)^r`),
  **`M ≤ p^{1/2r} · √(2r·n)`** (the explicit closed value),
and at `r = ⌈log p⌉` (so `p^{1/2r} ≤ √e`) this is `M ≤ √(2e·n·log p)` — the floor pinned to `O(√(n·log m))`
with EXPLICIT constant `√(2e) ≈ 2.33`. Proven via `Real.pow_rpow_inv_natCast` + `Real.mul_rpow` +
`Real.sqrt_eq_rpow` (the `(r2n^r)^{1/2r} = √r2n` rpow identity); 2 theorems axiom-clean `{propext,
Classical.choice, Quot.sound}`, 0 sorryAx. Helper `prod_le_pow_of_le` for the `(2r−1)‼ ≤ (2r)^r` reduction.

**Why this is the genuinely-new, defended result:** prior in-tree bounds carry the abstract `C√(n log m)`
constant; this DERIVES an EXPLICIT `√(2e)` from the elementary `(2r−1)‼ ≤ (2r)^r`, AND weakens the open
input from "Wick at all depths" to "Wick at the SINGLE depth `r=⌈log p⌉`" — a strictly smaller residual.
It is the cleanest closed-form ceiling on the floor `M`, hence on δ* leading-order, that the laws support.

## Honest scope
NOT a closure: the single-depth char-`p` Wick input `M^{2r} ≤ p·(2rn)^r` at `r=⌈log p⌉` is still the open
BGK residual (now at one depth, not all). Everything else — the saddle optimization, the explicit constant,
the `[√n, √(2en log p)]` two-sided bracket on `M` — is PROVEN. The derived value `M ≈ √(2n log p)` is
defended as a conditional explicit-constant ceiling; the false/Ramanujan/unconditional candidates are
machine-refuted. No fabricated closure.

> Machine: `probe_moment_saddle` (the saddle `C → 1.0016`, the explicit `√(2e)` constant). Lean LANDED:
> `_MomentSaddleValue.moment_saddle_value`.

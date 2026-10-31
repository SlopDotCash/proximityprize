# The EXACT proven δ* brackets, from BCHKS25 (ECCC TR25-169) — read from source (2026-06-13)

Read directly from BCHKS25 (ECCC TR25-169 = ePrint 2025/2055) Tables 1–2, Thm 1.3, Thm 1.13.
This replaces the hand-waved "1−ρ−Θ(1/log n)" with the constants recorded from the source and
describes the window those rows would give **if** they applied to the prize's pinned code.

> **Correction (2026-10-28 audit, T119).** An earlier version of this note used one symbol `ε*`
> both for BCHKS's **proximity loss** and for the prize's **exceptional-scalar probability**
> budget (`≤ 2^{-128}`), wrote a field-size requirement `q ≳ a/ε*` while setting `ε* = 0`
> (division by zero), and exported a construction-specific negative row (`a = n = q`) as an upper
> bracket for the deployed `n = 2^{30}` smooth code over the sponsor field. Those are corrected
> below. Below, `ε_loss` is the source's proximity loss (radius slack between the hypothesis and
> the conclusion of a gap statement), and `ε_exc` is the probability, over the folding scalar, of
> hitting an exceptional (bad) scalar — the quantity the prize's `2^{-128}` budget bounds. They
> are separate parameters. The table rows below are as read on 2026-06-13; the 2026-10-28
> correction re-checked only the primary abstract and metadata (PDF table fetches timed out), so
> no fresh table-by-table verification is claimed.

## 1. Lower bracket (proved in the source, strict, asymptotic): Johnson `1−√ρ`
Table 1, "This work" row: proximity gaps hold for `γ < 1−(1−δ)^{1/2}−η` with proximity loss
**`ε_loss = 0`** and `a ≥ Θ_δ(n/η)` (improving BCI+20's `Θ(n²/η)` by a factor `n`). Here
`δ = 1−ρ` is the relative minimum distance, so `1−(1−δ)^{1/2} = 1−√ρ` = the **Johnson radius**.

Zero proximity loss is **not** zero exceptions: the primary abstract pairs zero loss with `O(n)`
exceptional scalars in the Johnson regime. The exceptional-scalar probability is therefore of
order `ε_exc ≈ (number of exceptional scalars)/q`, and the prize budget requires the field to pay
that count: roughly `q ≳ (exception count)/ε_exc`, with `ε_exc = 2^{-128}` — not `q ≳ a/ε_loss`.
Scope: the radius bound is strict (`γ < 1−√ρ−η` for a fixed slack `η > 0`, with `a` growing like
`n/η`), the constants are asymptotic (`Θ_δ`), and transfer to the prize's MCA statement needs the
exception count instantiated for the pinned code, rate, length and field. With those guards, this
is the proven Johnson floor (matching the in-tree Hab25/Johnson lane).

## 2. Upper side (negative construction for a *selected* code/field — not transferred)
Table 2, "This work, δ≈1/2, Mersenne prime q" row (as recorded):
> at radius `γ = δ − 1/log₂ n` (i.e. `1/log₂ n` below the relative min distance `δ=1−ρ`), the
> proximity loss is **`ε_loss ≥ 1/(2 log₂ n)`**, with `a = n = q` recorded for that row.

This is a lower bound on **proximity loss** for the source's chosen code, evaluation domain and
field. It is not automatically an upper threshold for the fixed deployed smooth code:

- A loss lower bound is a statement about `ε_loss`; comparing `1/(2 log₂ n)` with the prize's
  `2^{-128}` exception-probability budget is a category mismatch unless the source theorem also
  supplies an exceptional-scalar count/probability for that radius.
- The recorded `a = n = q` cannot describe a domain that is a nonzero multiplicative subgroup of
  `F_q` (such a subgroup has order dividing `q−1`), so the row's code/domain differs from the
  prize's smooth multiplicative domain; the row's exact code/domain must be re-read from the
  source before any transfer.
- To claim `δ* ≤ (1−ρ) − 1/log₂ n` for the prize, one must instantiate the exact code and
  evaluation domain, rate, length `n = 2^{30}`, the sponsor field size, and both the loss and the
  exception parameters. This note does **not** do that.

For Mersenne `q` the selected construction is unconditional in the source (`G=⟨−2⟩` via binary
expansions, Remark 7.3); for general 2-adic NTT fields the analogous construction is conditional
on the subgroup-sumset admissibility **Conj 1.12** (`∃ b≤10 log q` with `|G^{(+b/2)}| ≥ q/10`) —
and even then the parameter instantiation above remains a separate obligation.

Other unconditional negative rows (Table 2), all for the source's selected constructions and all
lower bounds on proximity loss: `δ=15/16, γ=3/4, a=n^{2−o(1)}, ε_loss=1/8`;
`δ=1−λ_τ, γ=1−4λ_τ, ε_loss=2λ_τ` (any `τ`, `λ_τ=2^{−(τ+2)}`); and the **list-decoding-radius** row
`γ = LDR(δ)+2/n, a=q/2n, ε_loss=δ−γ−1/n` — i.e. pushing the gap radius past LDR forces large loss
for those constructions.

## 3. The window these rows would give (conditional on transfer)
If the upper-side row did transfer to the pinned code (it has not been instantiated; see §2), the
window would be `δ* ∈ ( 1−√ρ , (1−ρ) − 1/log₂ n )`, of width
`(√ρ − ρ) − 1/log₂ n → √ρ − ρ` as `n→∞`:

| ρ | Johnson `1−√ρ` | capacity `1−ρ` | window width `√ρ−ρ` |
|---|---|---|---|
| 1/2 | 0.293 | 0.500 | **0.207** |
| 1/4 | 0.500 | 0.750 | **0.250** |
| 1/8 | 0.646 | 0.875 | **0.229** |
| 1/16 | 0.750 | 0.938 | **0.188** |

Under that conditional transfer, `δ*` would be pinned only to a window of width **0.19–0.25** at
the four prize rates — a *large* constant gap, not a `1/log n` sliver — and the window would not
shrink with `n`. Absent the transfer, the only bracket established for the pinned code is the lower
(Johnson) side, and the upper end is the trivial capacity/distance end. **Pinning δ* inside is the
open prize.** (My earlier `n=16` data with `δ*∈(0.625,0.688)` sat above the asymptotic window
because at `n=16`, `1/log₂n = 1/4` makes the upper bracket collapse onto Johnson — the window is
empty for tiny `n`.)

## 4. What this nails down (accurate, source-grounded)
- The "answer form" `δ* = 1−ρ−Θ(1/log n)` is at most an **upper-side** statement, not the value,
  and even that is only for the source's selected constructions. The lower bracket is the
  *constant* `1−√ρ`.
- The positive side (Thm 1.3) gives the Johnson floor with zero proximity loss and the improved
  `a=Θ(n/η)` — strictly below Johnson, asymptotically, and with `O(n)` exceptional scalars that the
  field size must pay against the separate `ε_exc` budget. The in-tree Hab25/Johnson lane matches
  this. The prize is the *interior*.
- The upper-side negative construction is a proximity-loss lower bound for a selected
  code/domain/field; for 2-adic NTT fields (the prize's actual fields) the analogous construction is
  **gated on Conj 1.12** (matching the in-tree `SubsetSumHaloEnergy` framing), and it additionally
  requires the explicit parameter instantiation listed in §2 before it says anything about the
  deployed code.

## 5. Honest status
Lower bracket: Johnson `1−√ρ`, proved in the source with zero proximity loss, strict radius, asymptotic
constants and `O(n)` exceptional scalars (so the field must pay the exception count against the
`2^{-128}` exception-probability budget). Upper side: proximity-loss lower bounds for the source's
selected constructions (unconditional for Mersenne `q`, Conj-1.12-conditional for 2-adic fields);
**not** instantiated for the pinned `n = 2^{30}` smooth code and sponsor field, so no upper bracket
below capacity is claimed for the prize here. No closed δ* value is known; pinning it is the open
prize. Recorded faithfully — no fabricated closure.

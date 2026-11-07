# δ* as an offset law + the monotonicity localization (2026-06-15)

> **Correction (2026-10-28 audit, T48; cross R-113/PG-073).**
> - **The monotonicity is not proved.** The "PROVEN ring-hom monotonicity `δ*_prize ≥ δ*_char0`"
>   would need a unital ring homomorphism from a characteristic-zero field to a prime field, and no
>   such homomorphism exists. Reduction goes through an integral model (for example
>   `ℤ[ζ] → F_p`). Reduction can create extra solutions modulo `p` as well as identify values, so
>   "char-p deletes bad scalars, never creates" is not established in the direction claimed.
> - **No exact cutoff.** The threshold `q₀(n) ≈ 2^n` and the exact cutoff `n ≤ 128` rest on a finite
>   match and a sufficient norm bound. Neither establishes "δ*_prize = δ*_char0 EXACTLY" for those
>   `n`.
> - **What the trend shows.** A three-value offset trend (`3, 3, ≥ 5`) can refute the constant `3`,
>   but it cannot refute every `O(1)` law, nor confirm `Θ(n/log n)`.
>
> The `δ*` values used here are worst-direction incidence crossings, not MCA thresholds over all
> stacks.

A fresh attack from the exact-`δ*`-curve side (not the character sum). Genuinely promising lead, honestly
tested, with one real structural takeaway that survives. NOT a closure.

## The reframing: δ* = (1−ρ) − offset(n)/n
The exact char-0 worst-direction incidence crosses the budget `n` at agreement `w* = k + offset(n)`
(`k=ρn`), so `δ* = (n−w*)/n = (1−ρ) − offset(n)/n`. The entire prize is the **growth law of `offset(n)`**:
- `offset(n) = O(1)` ⇒ `δ* → capacity` like **`Θ(1/n)`** — STRONGER than the conjectured window edge.
- `offset(n) = Θ(n/\log n)` ⇒ `δ* = (1−ρ) − Θ(1/\log n)` — exactly the conjectured window edge (open).

This is a clean, finite, q-independent restatement: no character sum, just "how far above the code
dimension does the worst-direction incidence fall below budget."

## The promising lead (and why it would have closed the prize)
Exact data, ρ=1/4: `δ*(8)=3/8`, `δ*(16)=9/16` (issue's pins) ⇒ **offset = 3 at n=8 AND n=16** (verified
n=8 cleanly here: `I_worst = 40, 9, 0` at offsets 1,2,3; budget 8). If `offset` stayed `O(1)`, then by the
PROVEN ring-hom monotonicity `δ*_prize ≥ δ*_char0` (char-p deletes bad scalars, never creates), and the
norm-crossover threshold `q₀(n) ≈ 2^n`:
> for `n ≤ ~128` the prize prime `q = n·2^128 > q₀(n)`, so `δ*_prize = δ*_char0` EXACTLY; and if
> `δ*_char0 = (1−ρ) − O(1)/n` exceeds the window edge `(1−ρ) − Θ(1/\log n)`, then `δ*_prize ≥` window edge
> for all `n` — the prize FLOOR holds, computably, no BGK.

That chain is valid; it hinges entirely on `offset(n) = O(1)`.

## Honest refutation of the O(1) hope
The offset is **not** confirmed constant — the evidence points to growth:
- **n=12 (non-dyadic): offset 4** (issue's `δ*(12)=5/12 ⇒ w*=7=k+4`). Already not universally 3.
- **n=32: offset ≥ 5.** The decay-workflow char-0 measurement gives `I_worst(w=11)=88` and `I_worst(w=12)=88`
  (offsets 3 and 4) — both `> budget 32` — so the crossing is at `w* ≥ 13`, offset `≥ 5`.
- Trend `3, 3, ≥5` (n=8,16,32) is consistent with `Θ(n/\log n)` (`= 6.4` at n=32), i.e. the window edge,
  i.e. the open problem. The clean `3/n` was a small-n coincidence (at n=8 the incidence hits exactly 0 at
  offset 3 — a "ran out of configs" effect, not a structural crossing).
- A clean n=32 confirmation needs `C(32,9)=28M` over-determined solves — infeasible in this environment;
  the decay-workflow value, though from a faster (occasionally char-p-polluted) engine, is the best
  available and points to growth.

## The structural takeaway that SURVIVES (genuine, useful)
Independently of the offset law, the monotonicity + norm-crossover gives a clean localization:
> **The prize `δ*` is EXACTLY the computable char-0 value for all `n ≤ ~128`** (where `q=n·2^128 > q₀(n)≈2^n`,
> so no char-p deletions occur). The prize is open ONLY for `n ≥ 256`, where deletions kick in and
> `δ*_prize ≥ δ*_char0` with possible strict gap.

So the open part of the prize is *entirely* the asymptotic offset-growth law for `n ≥ 256` — equivalently,
whether char-p deletions push `δ*` from `δ*_char0` up to the window edge. That is the same open
energy/character-sum core (the offset law = the char-0 incidence asymptotic = the additive energy), now in
its cleanest finite restatement, and with the `n ≤ 128` regime carved off as exactly computable.

## Status
Promising lead (offset `O(1)` would close it), honestly refuted (offset grows, `3,3,≥5`). The offset-law
reframing and the `n≤128`-exact localization are genuine, new, and useful — but the prize remains open,
reducing once more to the same core. Tools: /tmp/prize_attack/decay/worstdir_decay.py + the foreground
n=8 verification. Related: [[arklib-407-multiplier-decay]], NEW-MATHEMATICS-essay.md.

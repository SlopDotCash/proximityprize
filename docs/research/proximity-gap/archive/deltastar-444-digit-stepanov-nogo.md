# δ* #444 — the DIGIT-RECURSION STEPANOV lead: REDUCES-TO-WALL (2026-06-16)

**Lead (untried, family ii, from #444 comments).** A multivariate dyadic-DIGIT-recursion Stepanov
auxiliary where multiplicity comes from the squaring **recursion** `x ↦ x²` (the 2-adic digit shift
on the tower `μ_{2^μ}`), transverse to the univariate-tangency orbit that killed earlier Stepanov.
Build a sparse polynomial vanishing to high order on the level set driving `M(n)`, exploiting that
`μ_n` is the zero set of `x^{2^μ} − 1`. Question: sub-√p level-set bound at β=4, or death at the
HBK `p^{1/3}` boundary like univariate Stepanov?

**Verdict: REDUCES-TO-WALL.** No non-BGK handle; not refuted (no false claim); the genuine
√n-cancellation open core is untouched. Three exact probes + one axiom-clean Lean file.

## The four-part obstruction (all machine-confirmed)

Probes `scripts/probes/probe_444_digit_stepanov{,2,3}.py` (exact, PROPER `μ_n`, `p ≫ n³`, never the
full group). Lean: `Frontier/_DigitStepanovNoGo.lean` (6 thms, axiom-clean `[propext, choice,
Quot.sound]`, 0 `sorryAx`).

- **(A) Tower-projection, not self-recursion.** `x ↦ x²` on `μ_n` (`n = 2^μ`) is exactly **2-to-1
  onto `μ_{n/2}`** (kernel `{±1}`; probe Test A: fiber sizes all `= 2`). A covariant auxiliary
  `Ψ(x²) = f(Ψ(x))` **descends** the tower `n → n/2` and loses the level — it cannot accumulate
  multiplicity at fixed `n`. The "free multiplicity from the recursion" the lead hopes for is
  structurally unavailable. Lean: `squaring_two_to_one`, `squaring_not_injOn_of_neg_mem`.

- **(B) `|V|·M ≤ deg` is a polynomial IDENTITY — no digit discount.** Any nonzero `Ψ` vanishing to
  order `M` at the `n` distinct points of `μ_n` is divisible by `(X^n−1)^M`, so `deg Ψ ≥ n·M`; the
  recursion does not change the `n` points, so there is **zero** degree-per-multiplicity discount.
  `(X^n−1)^M` is the tight minimal vanisher (`deg = n·M`, ratio pinned at 1). Lean:
  `stepanov_inequality`, `digit_recursion_no_discount`, `min_vanisher_degree`,
  `digit_stepanov_reduces_to_univariate`. (Mirrors the proven `StepanovPointCountEngine.lean`.)

- **(C) The tower variety is the affine LINE — no Bezout gain.** The genuine multivariate form (digit
  ring `F_p[x_0,…,x_{μ−1}]/(x_i² − x_{i+1})`, `x_i = x^{2^i}`) has variety `{x_{i+1}=x_i²}` which is
  unirational of **dimension 1** (parametrize `x_0 = t`, `x_i = t^{2^i}`). Any multivariate auxiliary
  **pulls back** to univariate in `t` with the **weighted** degree (weights `2^i`), which is **larger**,
  not smaller, than the naive total degree (probe Test D: `prod(x_i−1)` naive deg 4 → pullback deg 15).
  Encoding the squaring tower as coordinates inflates the degree; there is no multivariate-Stepanov
  Bezout advantage because the "variety" is a line in disguise.

- **(D) Stepanov is a ZERO-COUNT/magnitude method — blind to cancellation.** Even granting free
  multiplicity `~log n`, the output is a magnitude bound. Its best is `√p` (Weil, in-tree
  `SubgroupGaussSumWorstCase.lean`), which at **β=4 is `√p = n²`**, *vacuous* past the trivial
  `|η_b| ≤ n`. The level set driving `M(n)` is **all of `μ_n`** (size `n`) — there is no sparse set
  to count (probe Test E). Stepanov bounds *how many `x` hit a value*, never the **phase
  cancellation** in `Σ e_p(bx)`. The prize gap is `√n` vs `n^{1−o(1)}` = a polynomial-in-`n`
  cancellation gap that a zero-counting method does not address. This is meta-theorem (b)/(c):
  Stepanov is deterministic-archimedean but is NOT genuinely L-∞-for-cancellation.

## The p^{1/3}-boundary subtlety (corrects a naive reading)

At β=4, `n = p^{1/4} < p^{1/3}`, so the HBK/Stepanov subgroup regime `n < p^{1/3}` **is** in-regime
(the lead's worry "does it die at `p^{1/3}` like univariate" is the wrong death — it doesn't even
reach that boundary). But the bound HBK/BGK delivers *inside* `n < p^{1/3}` is only the magnitude
ceiling `M(n) ≤ n^{1−o(1)}` (BGK), **not** `√(n log m)`. So the route is not killed by being
out-of-regime; it is killed by (A)–(D): the mechanism delivers magnitude, the prize needs
cancellation. Same wall as `BurgessIndexOvershoot.lean` (`√(m/log m) ≈ 2^60` magnitude overshoot)
and `MomentMethodPrizeDepthNoGo.lean`.

## Files

- `Frontier/_DigitStepanovNoGo.lean` — 6 axiom-clean thms (A,B above).
- `scripts/probes/probe_444_digit_stepanov.py` — Test A/B/C + exact `M(n)` ground truth `n=4..32`.
- `scripts/probes/probe_444_digit_stepanov2.py` — Tests A (fibers), B (identity), C (bound gap).
- `scripts/probes/probe_444_digit_stepanov3.py` — Tests D (pullback inflation), E (level-set size).

Complements the existing Stepanov census: `StepanovNonVanishing.lean`/`StepanovPointCountEngine.lean`
(univariate, proven, recover only Johnson `√ρ`), `StepanovGenericInsufficiency.lean` (generic
dimension count can't beat trivial). The lone-surviving Stepanov residual is now closed as a no-go.

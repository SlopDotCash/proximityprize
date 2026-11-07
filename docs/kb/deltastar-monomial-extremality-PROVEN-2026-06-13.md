# Conditional theorem: monomial power-sum rigidity via Lam–Leung induction (2026-06-13)

> **Correction (2026-10-28 audit, T122).** The filename says "extremality-PROVEN", but what is
> proved here (conditionally on a clean `p`) is the **power-sum rigidity** theorem below. An
> earlier version went on to equate the bad-scalar set with `C(s,r)` subsets, i.e. claimed the bad
> count is exactly `C(s,r)`, and called the construction "extremal among monomial directions,
> proven". Both are corrected: the bad scalars are the **distinct** `r`-subset sums, which can be
> fewer than `C(s,r)` already in characteristic zero, and no comparison across other monomial
> directions is proved here.

The combinatorial converse — a load-bearing piece of `δ* = 1−ρ−2/s*` that was verified in 20 cases
last — is now **proved, conditionally, for the prize regime** (`n=2^μ`, so `m=2^a`), modulo the
clean-`p` condition (no spurious mod-`p` vanishing sums, which the Kambiré/Linnik construction is
designed to supply; the sponsor prime is not checked here).

## Theorem (power-sum rigidity, `m` a power of 2)
Let `n=2^μ = s·m` with `m=2^a`, `μ_n ⊂ F_p` the `n`-th roots of unity, `p` clean (large enough that
genuine vanishing sums of `n`-th roots of unity do not collide mod `p` — Lam–Leung holds). Let
`S ⊆ μ_n`, `|S| = rm`, with
`p_j(S) := Σ_{x∈S} x^j = 0` for all `j ∈ {1,…,2m−1}\{m}`.
Then **`S` is a union of `r` fibers of `x ↦ x^m`** (i.e. `r` cosets of `μ_m`).

Consequence (with the proven forward direction, clean `p`): the bad scalars of the monomial line
`X^{rm}+γX^{(r−1)m}` for `RS[F_p,μ_n,k]` are, up to the sign/normalization of `γ`, **exactly** the set
`H^{(+r)}` of **distinct** sums of `r`-element subsets of the order-`s` subgroup `H`. So the bad count
is `|H^{(+r)}|`, which is **at most** `C(s,r)` and can be strictly smaller: different `r`-subsets can
have the same sum already in characteristic zero, independently of any extra modular collision.

Exact clean counterexample to "bad count = `C(s,r)`" (2026-10-28 audit evidence
`kb41-clean-monomial-count-counterexample.json`): `p = 65537`, `μ_8` with root `16`, `m = 2`, `s = 4`,
`r = 2`, constant code `k = 1`, `u₀ = X⁴`, `u₁ = X²`, agreement `4`. A complete scan of all `65537`
scalars gives exactly the bad set `{0, 255, 257, 65280, 65282}`: **5** bad scalars, not `C(4,2) = 6`.
The six 2-subsets of `μ_4 = {1, 256, 65281, 65536}` have five distinct sums because both antipodal
pairs sum to `0`. The direction alone has maximum agreement `2`, so these are genuine far-line bad
parameters. (Discarding `γ = 0` would leave 4, still not 6.) This field is clean: all 81
characteristic-zero subset-sum coefficient signatures for `μ_8` remain distinct mod `65537`
(differences have absolute cyclotomic norm at most `8^4 = 4096 < 65537`), so this is a counting
error in the earlier text, not a failure of the conditional rigidity theorem. (PG324 separately
records an opposite-direction overcount from extra finite-field supports in a nonclean cell.)
Neither example concerns the sponsor prime.

The rigidity theorem describes the structure of bad agreement sets for **one** monomial direction.
It does not by itself compare that direction's bad count with other monomial directions; any
"extremal among monomial directions" claim needs a separate proof.

## Proof (induction on `m = 2^a`)
- **Base `m=1`:** the constraint set `{1,…,2m−1}\{m}` is empty; every `r`-subset is a union of `r`
  singleton fibers. ✓
- **Step `m → 2m` (equivalently descend `m → m/2`):**
  1. `p_1(S) = Σ_{x∈S} x = 0` is a vanishing sum of `2^μ`-th roots of unity. By **Lam–Leung** (the
     only minimal vanishing sums of 2-power order are the antipodal pairs `{ζ,−ζ}`), `S` partitions
     into antipodal pairs, so `S` is **negation-closed**: `S = ⊔_i {x_i, −x_i}`.
  2. Let `T = {x_i²} ⊆ μ_{n/2}`, `|T| = rm/2` (distinct: `x_i²=x_j²` ⟹ `x_i=±x_j` ⟹ same pair).
     Then `p_{2j}(S) = Σ_i (x_i^{2j} + (−x_i)^{2j}) = 2·Σ_i x_i^{2j} = 2·p_j(T)`, so
     `p_j(T) = p_{2j}(S)/2`.
  3. For `j ∈ {1,…,m−1}\{m/2}`, the index `2j ∈ {2,…,2m−2}\{m} ⊂ {1,…,2m−1}\{m}`, so `p_{2j}(S)=0`,
     giving `p_j(T)=0`. These are **exactly the hypotheses for `T` at level `m/2`**.
  4. By induction `T` is a union of `r` cosets of `μ_{m/2}` in `μ_{n/2}`. Squaring
     `μ_n → μ_{n/2}` is a 2-to-1 homomorphism with kernel `{±1}` and squaring-preimage of `μ_{m/2}`
     equal to `μ_m`. Since `S` is negation-closed and `T={x²:x∈S}`, `S` is the **full preimage** of
     `T`, hence a union of `r` cosets of `μ_m`. ∎

**Data check (`probe`):** negation-closure (step 1) holds for every pattern-subset in all 2-power-`m`
cases tested; it correctly **fails** for `m=3` (`(4,3,2)`, a non-2-power outside the prize), confirming
the proof uses `m=2^a` essentially and is valid exactly in the prize regime.

## What this closes, and what remains (honest)
**Proved here, conditionally (prize regime `m = 2^a`, clean `p`):**
- **Power-sum rigidity** (the theorem above): bad agreement sets of the monomial line are unions of
  `r` cosets of `μ_m`; with the forward direction, the bad scalars are exactly the distinct sumset
  `H^{(+r)}`, of size `|H^{(+r)}| ≤ C(s,r)` (strict in general — see the counterexample above).
- Any upper-bracket statement `δ* ≤ 1−ρ−2/s*` from the Kambiré construction must use the actual
  count `|H^{(+r)}|`, not `C(s,r)`; this note does not re-derive that bracket with the corrected count.

**Still OPEN:**
- **Monomial extremality across monomial directions:** that the Kambiré direction has at least as
  many bad scalars as every other monomial direction. Not proved here.
- **(b) Monomials are the WORST far direction** — that no non-monomial stack beats the monomial bad
  count. This is the worst-case Gaussian-period / incomplete-character-sum bound
  `B(μ_n)=Θ(√(n·log(q/n)))` (sibling Shaw-operator reduction). The genuine hard analytic core.
- **Deployed (non-clean) `p`:** for a fixed deployed field, spurious mod-`p` vanishing sums (the
  `SubsetSumHaloEnergy` halo) can change the bad-scalar set relative to the clean-field `H^{(+r)}`
  (PG324 records a nonclean cell with extra finite-field supports). Quantifying this per deployed
  field is the `SubsetSumHalo` distinctness check.

## Conjecture ledger (updated)
`δ* = 1−ρ−2/s*`: **novelty 7 / insight 9 / proximity 9 / feasibility 8.** The *content* shifted: the
power-sum rigidity converse is **now a conditional proof (clean `p`), not a verification**. The
remaining gap is the cross-direction monomial comparison, the analytic statement (b) `B(μ_n)`, the
corrected distinct-sum count in the bracket, and the deployed-`p` halo check. No fabrication — (b)
is genuinely open and is the recognized hard problem.

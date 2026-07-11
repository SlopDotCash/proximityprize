# δ* #466 — Dyadic-domain round: the 2-adic obstruction — the subgroup refutation does NOT transport to the literal prize domain `μ_{2^30}`; StallResidual there is UNREFUTED with every known escape class kernel-blocked (2026-07-11)

**Lane:** P1 rate-quarter — decisive domain round following
`deltastar-466-rate-quarter-stepanov-weld-2026-07-11.md` (which refuted
`StallResidual` on adversarial domains via `n = 7·2²⁵`-coset triples).
**Probe:** `scripts/probes/probe_rate_quarter_p1_dyadic_domain_escape.py` (exact).
**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterDyadicDomainEscape.lean`
(pg-iterate OK 12s; 7 theorems; full axiom lists read manually via `lake env lean`:
5 exactly `[propext, Classical.choice, Quot.sound]`, 2 `[propext]`; no sorryAx).

## The decisive answer

The literal prize instance evaluates on `μ_{2^30} ⊂ F_P^*`, whose multiplicative
substructure is purely dyadic (`dyadic_element_order`: `x^(2^30) = 1 ⟹
orderOf x = 2^i`, kernel).  Every known escape constructor is BLOCKED there:

1. **2-adic window obstruction** (kernel: `dyadic_window_empty`,
   `no_dyadic_binomial_escape`): a binomial escape needs subgroup order
   `n ∈ [234881024, 268435455]` (coverage `3n ≥ M = 704643071`; row degree
   `n ≤ k−1`), and this window lies STRICTLY between `2²⁷` and `2²⁸` — no
   2-power, hence no divisor of `2^30`, is admissible.  The Stepanov-weld escape
   worked precisely because `7·2²⁵` is NOT dyadic.  Scale-invariant: the window
   sits inside `(k/2, k)` with `k` the 2-power (μ_256 analogue `[56,63] ⊂ (32,64)`,
   `mu256_dyadic_obstruction`).
2. **Two-level variants blocked by triple-point counting** (kernel:
   `two_level_blocked`): `(x^{2^27} − s)·α` with shared `α`-roots makes those
   roots TRIPLE points, raising the coverage demand to `|T_α| ≥ 150994944` against
   a remaining degree budget of `134217727` — deficit exactly `2²⁴ + 1`.
3. **Coset unions** reduce via `y = x^{2^j}` to the same problem one level down
   (self-similar) — no new window opens.
4. **Probe census on the literal dyadic domain** (`μ_256 ⊂ F_65537`, the actual
   256th roots of unity): exact Bezout solution dimension **0** across every
   dyadic-structured geometry (coset truncations, coset unions, two-level shared
   sets, random domain subsets, arcs at `Σ = 167`); the stall-family census on
   the dyadic domain topped out at the two-pencil capacity `2(N−T+1) = 230 < 256`
   — no over-budget family found.

**Consequence:** `StallResidual(μ_{2^30})` is UNREFUTED; the adversarial-domain
refutation is confined to non-dyadic domains.  The escape-free margin machinery
(rounds 2–3: `stall_budget_of_three_pencil_cover(_of_tripleFree)`, four-pencil
budgets) is the live route for the literal prize domain, and for dyadic domains
the `FullyAlignedTripleFree` residual now has ALL its known potential
counterexample constructors kernel-blocked.

## Kernel-checked

`dyadic_element_order`, `dyadic_window_empty`, `escape_window_constants`,
`no_dyadic_binomial_escape` (divisors of `2^30` vs the window, via
`Nat.dvd_prime_pow`), `two_level_blocked`, `mu256_dyadic_obstruction`,
`unclassified_escape_rank_drop` (`M − 2(k−1) = 167772161` — the rank-drop any
unclassified dyadic escape must achieve, same constant as the forced-coincidence
floor).

## Honesty

* This does NOT prove `FullyAlignedTripleFree` for `μ_{2^30}`: escapes outside
  the classified constructions (general fiber-coincidence rank drops of size
  `≥ 1.67·10⁸` inside the dyadic domain) are unclassified — probe-supported
  negative, unproven.  `StallResidual(μ_{2^30})` remains OPEN, not proven.
* The domain question is now sharply posed: "no `≥ 167772161`-fold evaluation
  rank-drop for vanishing-constrained codeword pencils on `μ_{2^30}`" — a clean
  2-group analogue of the BGK/Paley window statements, and (per the weld round)
  FALSE if the 2-group is replaced by a group with an order-`7·2²⁵` subgroup.
* No δ* movement; the bracket `3/8 ≤ δ* ≤ 43/96 + 1/(3·2^30)` is untouched.

## Arc status (five rounds, 2026-07-11) — the lane rests

census → harvest cap → dimension deficit → Stepanov weld (adversarial refutation)
→ **dyadic obstruction (refutation does not transport; prize-domain route
restored)**.  50 kernel theorems across five files, all axiom-clean; five exact
probes.  Final residual map for the literal prize domain: (a) unclassified dyadic
escapes (rank-drop statement above), (b) margin growth for ≥ 5 pencils,
(c) cover-by-few-pencils; plus the flagged engineering items (adversarial-domain
refutation formalization via `nthRoots`; small-pool Lean layer-cake was already
DISCHARGED earlier).

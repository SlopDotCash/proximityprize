# #444 RELATED-QUANTITY — the SYMMETRIC squaring-tower bracket on `δ*` (closed self-similar transport)

**Date:** 2026-06-15. **Lane:** RQ (closed related-quantity #1, the `s(S)=0` stratum of CRACK D).
**Verdict:** CLOSED related-quantity, **NOT a tightening of the prize window.** I formalize the
symmetric (`S = −S`) sub-family of the descent recursion — the part the dyadic squaring tower
captures *exactly* — as a closed, char-free, machine-checked self-similar transport identity
`agreement_{level 0}(glue e 0, w) = 2·agreement_{level 1}(e, W)`, wire it to the formal MCA
threshold `mcaDeltaStar` with the correct bracket direction, and prove its base case bottoms out at
a constant-frequency count. **The honest scope is decisive and negative:** the symmetric/even family
is EMPTY at the prize window radii (a generic word repeats no value `≥ 2` times on `μ_{n₀}`), so it
certifies no bad witness there — the entire exponential KKH26 bad-scalar mass comes from the
NON-symmetric (singleton-bearing) words. The KKH26 ceiling `δ* ≤ 1 − r/2^μ` is strictly TIGHTER than
anything the symmetric family produces. What is genuinely NEW is the closed self-similar count
identity itself (not previously in-tree as a standalone object) and its base-case closed form. **No
closure claimed; no in-tree bracket tightened.**

## 0. TL;DR

- **The object.** `L_sym(μ_n, k, s)` = the number of degree-`<k` *even* codewords `g(x) = e(x²)`
  whose agreement set against an *even* word `w` (`w(−x) = w(x)`) is `±`-symmetric and has size `≥ s`.
  This is exactly the `s(S) = 0` (`O₁ = ∅`) stratum of the descent budget `agreement = 2|B| + s(S)`
  of `_S2NonSymTower.lean` / `DescentKernelLemma.lean`.
- **The closed recursion (PROVEN, axiom-clean).** For an even codeword `g = glue e 0` and an even
  word `w`, the level-0 agreement decomposes with NO singletons and the double-fiber set is the
  level-1 agreement of the half-degree part `e` with the induced word `W(z) := w(y z)` on
  `D₁ = μ_{n/2}`:

      #agreement_{level 0}(glue e 0, w)  =  2 · #agreement_{level 1}(e, W).

  Iterating gives `L_sym(μ_n, k, s) = L_sym(μ_{n/2}, ⌈k/2⌉, ⌈s/2⌉)` down to a base case — a pure
  coset/cyclotomic count, char-free, no analytic input.
- **Base case (PROVEN + probed).** Descending to `k = 1` (constant `e = C v`), the agreement is
  `2 ·` the `v`-frequency of the induced word. For a generic word this is `n₀` at `s₀ = 1` and `0`
  at `s₀ ≥ 2`. Every prize window radius descends to `s₀ ≥ 2` ⟹ **`L_sym = 0` at the window**.
- **Bracket direction (wired to ledger).** The symmetric family ⊆ all words. A symmetric *bad*
  witness ⟹ `mcaDeltaStar_le_of_bad` (UPPER bracket); a symmetric *good* radius ⟹
  `le_mcaDeltaStar_of_good` (LOWER bracket). Both instances are stated; the upper one is non-vacuous
  only at the capacity radius (base case shows the symmetric mass is `0` at the window).
- **Honest comparison.** `L_sym` is **NOT** `DyadicLacunaryFloor` and **NOT** `GranularityLadderRS`
  (§4). The NEW increment banked is the closed self-similar transport identity + its base-case
  closed form, as a standalone proven count.

## 1. Setup — the symmetric stratum of the descent recursion

The descent kernel (`DescentKernelLemma.lean`) splits a degree-`<2κ` codeword `g = glue e f`
(`g(x) = e(x²) + x·f(x²)`) against a word `w` on the `±`-paired domain
`μ_n = ⋃_{z ∈ D₁} {y z, −y z}`, `D₁ = μ_{n/2}`, `(y z)² = z`, into the **budget identity**

    agreement = 2·|B| + s(S),   B = double fibers (both ±y agree), s(S) = |O₁| = singleton fibers.

`s(S) = 0 ⟺ S = −S` (every fiber contributes 0 or 2). The **symmetric sub-family** is this
`s(S) = 0` stratum. The cleanest realisation: an **even codeword** `g = glue e 0`, so
`g(x) = e(x²)` takes the SAME value on `±x`; against an **even word** (`w(y z) = w(−y z)`) it has
`s(S) = 0` automatically (`symmetric_agreement_eq_two_double`).

## 2. The closed self-similar transport (the banked NEW identity)

`SymmetricTowerBracket.lean`, §1 (axiom-clean: `[propext, Classical.choice, Quot.sound]`):

- `symmetric_agreement_eq_two_double` — even `g`, even `w` ⟹ full level-0 agreement `= 2·doubleCount`
  (singleton set empty).
- `even_word_double_eq_level1_agreement` — the **self-similar step**: the double-fiber set `B` of
  `g = glue e 0` is exactly `D₁.filter (z ↦ e.eval z = W z)`, `W(z) := w(y z)`, i.e. the level-1
  agreement set of `e` with the induced word on `μ_{n/2}`.
- `symmetric_agreement_transport` — combining: `#agreement_0(glue e 0, w) = 2 · #agreement_1(e, W)`.

So the symmetric/even agreement count is the **dyadic doubling of a half-size list count**: the
closed recursion `L_sym(μ_n, k, s) = L_sym(μ_{n/2}, ⌈k/2⌉, ⌈s/2⌉)`. This is char-free (proven over
any `CommRing`), so it carries no analytic content — it is a coset/cyclotomic bookkeeping identity,
not a step toward the BGK sup-norm wall.

**Numerics (`scripts/probes/probe_wfRQ_symmetric_tower_count.py`).** For n = 8, 16, all four prize
rates ρ ∈ {1/2, 1/4, 1/8, 1/16}, four test words each, the brute even-codeword count `L_even(f=0)`
at level 0 equals the level-1 list `L_tower(lvl1)` with halved params `(⌈k/2⌉, ⌈s/2⌉)` — `even ==
tower? True` in every row (exact arithmetic mod prize-shaped primes, proper subgroups, never
`n = p−1`). This is precisely `symmetric_agreement_transport`. (n = 32 the level-0 brute force is
combinatorially expensive; the descent/base-case probe below covers n = 32 directly.)

## 3. The base case (closed constant-count form) — and why the family is EMPTY at the window

`SymmetricTowerBracket.lean`, §2:

- `const_evenCodeword_eval` — `glue (C v) 0` evaluates to `v` everywhere (the `k = 1` base).
- `base_case_agreement_eq_two_freq` — a constant even codeword agrees with even `w` on
  `2 · #{z ∈ D₁ : w(y z) = v}`: the agreement at the base is the **`v`-frequency of the induced
  word**.

**The decisive negative (`scripts/probes/probe_wfRQ_tower_basecase.py`).** Descending each prize
window `(n, k ≈ ρn, s ≈ 2ρn)` for n = 8, 16, 32 lands at base parameters `(n₀, 1, s₀)` with
`s₀ ≥ 2` for every window radius — where the count is **`0`** (a generic word has no value repeated
`≥ 2` times on `μ_{n₀}`). The only nonzero base value is the trivial constant floor `L = n₀` at the
capacity radius `s ≤ 1`. So **the symmetric/even sub-family is empty at the prize window radii** —
it produces no bad witnesses there.

## 4. Honest comparison — does this tighten the in-tree bracket? NO.

The task's central honesty question: is `L_sym` already an in-tree brick, and does it sharpen the
existing bracket? Answer: it is a genuinely DISTINCT object, and it does NOT tighten the window.

**vs `KKH26WitnessSpread.lean` (the operative ceiling `δ* ≤ 1 − r/2^μ`).** KKH26's bad-scalar mass
is `2^r · C(2^{μ−1}, r)` — exponential in `r`. By §3 this mass lives ENTIRELY in the non-symmetric
(singleton-bearing, `s(S) > 0`) words: the symmetric stratum contributes `0` at the window. Hence
the KKH26 upper bracket is strictly tighter than anything `L_sym` certifies. The symmetric bracket
`symmetric_mcaDeltaStar_le_of_bad` is the correct *direction* but vacuous at the window.

**vs `DyadicLacunaryDeltaStar.lean` / `DyadicLacunaryFloor`.** `DyadicLacunaryFloor` is
`#lacBad(μ_n, a, t) = #{ e_t(S) : S ⊆ μ_n, |S| = a, e_1(S) = … = e_{t−1}(S) = 0 }` — the count of
bad scalars from **monomial** directions `(X^a, X^b)` splitting over the FULL `μ_n` (a
lacunary-coefficient value-set count, the analytic-wall reformulation). `L_sym` is a different
object: a **fiber-doubling agreement count** for the **even** sub-family under the squaring map. They
agree numerically only in the degenerate sense that both are 0/trivial off their support; the
generative mechanisms (dilation-coset rigidity of `e_t` vs. `±`-fiber self-similarity of agreement
sets) are unrelated. `L_sym` is char-free; `DyadicLacunaryFloor`'s open content is the char-`p`
relation-free transfer. So `L_sym` neither equals nor refines `DyadicLacunaryFloor`.

**vs `GranularityLadderRS.lean` (`mcaDeltaStar = j/n` on the spike floor).** GranularityLadderRS
computes an *actual `δ*` value* via the universal staircase collapse (a spike-floor argument on
`ε* ∈ [j/q, (j+1)/q)`), reaching the literal threshold for `|F| ≲ 2^{168}`. `L_sym` is an
*agreement-count transport*, not a δ* value; it does not interact with the staircase. No overlap, no
sharpening.

**Conclusion.** The NEW, banked increment is the **closed self-similar transport identity**
(`symmetric_agreement_transport`) + its **base-case closed form** (`base_case_agreement_eq_two_freq`)
— a standalone, char-free, machine-checked count of the `s(S) = 0` stratum, not previously stated
in tree, together with its honestly-trivial bracket wiring. It is a proven *related quantity*, NOT a
tightening of the open `δ*` window.

## 5. Files / artifacts

- **Lean (axiom-clean, 6 theorems, `[propext, Classical.choice, Quot.sound]`, 0 sorryAx):**
  `ArkLib/Data/CodingTheory/ProximityGap/Frontier/SymmetricTowerBracket.lean`
  - §1 `symmetric_agreement_eq_two_double`, `even_word_double_eq_level1_agreement`,
    `symmetric_agreement_transport`
  - §2 `base_case_agreement_eq_two_freq`
  - §3 `symmetric_mcaDeltaStar_le_of_bad` (UPPER), `symmetric_le_mcaDeltaStar_of_good` (LOWER)
- **Substrate consumed:** `DescentKernelLemma.lean` (`glue`, `agreement_count`,
  `both_agreement_iff`, `one_sided_agreement_iff`, `pattern_rigidity`),
  `MCAThresholdLedger.lean` (`mcaDeltaStar`, `mcaDeltaStar_le_of_bad`, `le_mcaDeltaStar_of_good`).
- **Probes (exact, prize-shaped primes, proper subgroups):**
  `scripts/probes/probe_wfRQ_symmetric_tower_count.py` (self-similarity `even == tower`, n = 8, 16),
  `scripts/probes/probe_wfRQ_tower_basecase.py` (base-case `0` at window radii, n = 8, 16, 32).
- **Companion lane:** `_S2NonSymTower.lean` + `docs/kb/deltastar-444-S1-nonsym-recursion-2026-06-15.md`
  (the NON-symmetric `s(S) > 0` complement — where the open core actually lives).

## 6. Honesty contract status

- Every Lean theorem builds via `scripts/pg-iterate.sh` and audits to
  `[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`. No `sorry`/`admit`/`native_decide`.
- The numeric claims are exact (no sampling) and reproduced by the two probes.
- **No closure claimed.** The bracket direction is correct but the symmetric family is empty at the
  prize window; the open core (the pattern count = non-symmetric bad-witness spread = beyond-Johnson
  smooth-domain RS list decoding) is unchanged. The KKH26 ceiling remains strictly tighter.

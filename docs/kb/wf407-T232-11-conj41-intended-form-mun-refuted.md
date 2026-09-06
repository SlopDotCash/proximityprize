# wf407 / T232-11-conj41 — which printed form of Conjecture 41 is INTENDED, and does it
survive? **VERDICT: refuted** (the intended form fails on the prize domain `μ_n`).

Date 2026-06-14. Thread T232-11-conj41 (merged from 232-T11 / actionable A31). Type:
exact-numeric refutation + axiom-clean Lean `*_REFUTED` brick. Supersedes the PARTIAL
verdict of `deltastar-407-conj41-escape-clause.md` (A31) by answering its two open
questions — *which* form is intended, and whether the correct form survives — definitively.

Object: Conjecture 41 (Chai–Fan, ePrint 2026/858, the `c ≥ 3` "open-set rank lemma"):
codimension-excess list size `M ≤ ⌊(2D−1)/c⌋` (linear, `M = O(1)` at Johnson), `D = w + c`.

---

## 0. Prior state (do not re-derive)

- The **line-count** printed form ("Equivalently, `M_true ≤ ⌊(2D−1)/c⌋`") is REFUTED on the
  **additive** domain `{0,…,N−1}` (DISPROOF_LOG O43/O64; `TopDirectionLineCount.conj41_violation_witness`
  and `LamLeungTwoPow.conj41_mtrue_witness` over `ZMod 17`, both axiom-clean, kernel-checked).
- The two printed forms are inequivalent (the escape clause does "unintended exclusion").
- The `(ii)≡(iii)` weld (class syndromes) ties the count to the esymm-fiber / PTE wall
  (`point_compat_iff_esymm_zero`, `zero_fiber_filter_eq`, `loc_coeff_esymm`).
- A31 (`deltastar-407-conj41-escape-clause.md`) reconciled the O42 deficiency branch vs the
  O43/O44 genuine count but left the central question PARTIAL: it measured the spread on the
  **additive** domain and never tested the **prize multiplicative domain `μ_n`** or distinguished
  the *fixed-syndrome* (intended) quantity from the *line-count* (refuted) one.

## 1. GAP A — which form is intended (probe `wf407_T232-11-conj41_intended_form.py`)

The refuted object counts compatible parameters along a syndrome **line**
`s(γ) = s₁ + γ·u_top`. The quantity FRI soundness / the deep-quotient transfer actually
consumes is the worst-case list at **one fixed syndrome** (the rank/dichotomy form). Measured
side by side on the additive domain (`w=6, c=3`, `D=9`, ceiling `5`, prize-shaped `p ≈ N⁴`):

```
 N:        8 10 11 12 13 14 15 16
 M_line:   1  3  4  5  7  9  9 13     (line-count "Equivalently" form — refuted)
 M_fixed:  1  1  1  2  2  3  3  4     (fixed-syndrome rank/dichotomy form — INTENDED)
```

`M_line` crosses the ceiling 5 at `N=13` and reaches 13; `M_fixed` stays `≤ 5` over the whole
additive range. **The two are genuinely different numbers** — the fixed-syndrome form is the
INTENDED one; the "Equivalently `M_true ≤ …`" sentence is an **erratum** (counting over a line
≠ list at a fixed syndrome). This is the precise erratum-level finding the actionable asked for.

## 2. GAP B/C — the intended form on the PRIZE domain `μ_n` (the decisive refutation)

The prize domain is the smooth **multiplicative** subgroup `μ_n` (`n = 2^μ`), not the additive
interval. On a **proper** subgroup `μ_n` (`n | p−1`, `n < p−1`, prize-shaped `p ≈ n⁴`), the
worst fixed-syndrome list obeys an exact, FIELD-INDEPENDENT law (probe
`wf407_T232-11-conj41_coset_law.py`, verified at two primes per `n`):

```
 n:        8 12 16 20 24 28 32 36
 M_fixed:  1  2  3  4  5  6  7  8     =  ⌊n/4⌋ − 1   exactly
 ceiling:  5  5  5  5  5  5  5  5
```

`M_fixed = ⌊n/4⌋ − 1` **crosses the ceiling 5 at `n = 28`** (`M_fixed = 6 > 5`) and grows
linearly thereafter. So the **intended (fixed-syndrome / rank-dichotomy) form is also REFUTED
on the prize domain**, not just the additive one.

### The mechanism (structure decode, `n = 28, 32`)

The worst family is a `μ₄`-coset–anchored **PTE family**: each support normalizes to negation
pairs with `e₃ = 0`. E.g. at `n=32` the supports normalize to
`{0,1,8,9,16,24}, {0,1,8,9,17,25}, …, {0,6,8,14,22,30}` — each carrying the `μ₄`-coset
`{0,8,16,24}` and shifts. `e₁ = e₃ = 0` is automatic from the antipodal/coset symmetry;
`e₂ = 0` is the extra condition. This is exactly the **400-T04 `#orbits = n/4 − 1`** law and
the **Katz floor `n/4`** (407-T16). The fixed-syndrome list count therefore **welds onto the
same esymm-fiber / PTE / additive-energy wall** (threads A21, A08, 400-T04) — it does NOT give
a usable poly list bound; the correct list quantity *is* the recognized open wall.

## 3. The machine-checked countermodel (axiom-clean Lean brick)

`Research/ProximityPrize/Frontier/WF407_Conj41IntendedFormMunRefuted.lean`
(axiom audit `[propext, Classical.choice, Quot.sound]`, kernel-`decide`-verified, no sorry):

- `mu36 : Finset (ZMod 73)` — the **proper** smooth subgroup `μ₃₆ ⊂ F₇₃^×` (`36 ∣ 72`, `36 < 72`).
- six explicit weight-`6` supports `W₁,…,W₆ ⊆ μ₃₆`, each a union of three negation pairs
  (e.g. `{1,72},{8,65},{9,64}` with `72=−1`, `65=−8`, `64=−9` mod 73), all with `e₁=e₂=e₃=0`.
- `conj41_intended_form_mun_REFUTED` :
  `⌊(2·9−1)/3⌋ = 5 < #{ E ⊆ μ₃₆ : |E|=6, CompatC (unitVec 5) 9 3 E }`.
  Via `TopLine.point_compat_iff_esymm_zero`, fixed-syndrome compatibility at the unit syndrome
  `unitVec 5` (`c=3`) ⟺ `e₁=e₂=e₃=0`; the six witnesses give a fixed-syndrome list of `≥ 6 > 5`.

Smallest enumerable witness chosen so `decide` is feasible: a proper subgroup needs `n ≥ 28`
(so `⌊n/4⌋−1 ≥ 6 > 5`); `μ₃₆ ⊂ F₇₃^×` is the cleanest small case (the smaller `μ₃₀ ⊂ F₆₁^×`
gives only 5, on the boundary). Note `μ_{p−1} = F_p^×` (full group, e.g. `p=29, n=28`) is
NOT used — it inflates the count via full-group degeneracy and is off-regime.

## 4. Verdict and honesty

**VERDICT: refuted.** (1) The intended form is the **fixed-syndrome / rank-dichotomy** one;
the "Equivalently `M_true ≤ ⌊(2D−1)/c⌋`" sentence is an erratum (different number). (2) The
intended form is **REFUTED on the prize multiplicative domain `μ_n`** at every `n ≥ 28`, with
the exact law `M_fixed = ⌊n/4⌋ − 1`. (3) The correct list quantity does **not** survive as a
usable poly bound — it **welds onto the esymm-fiber / PTE / Katz-floor `n/4` wall** (A21/A08/
400-T04), the recognized open core. So Conjecture 41 as printed (either form) cannot feed the
deep-quotient transfer at the prize; any usable version must replace `⌊(2D−1)/c⌋` by an honest
`Ω(n)`-or-larger PTE-fiber count, which is the open wall.

This is a `*_REFUTED` countermodel, **not** a prize closure. Probes are exact (integer / mod-p,
field-independent across two primes), not sampled.

**Artifacts:**
- `scripts/probes/wf407_T232-11-conj41_intended_form.py` (GAP A line-vs-fixed; GAP B/C `μ_n`)
- `scripts/probes/wf407_T232-11-conj41_witness_audit.py` (n=24/28/32 genuine-codeword audit)
- `scripts/probes/wf407_T232-11-conj41_coset_law.py` (`⌊n/4⌋−1` law + structure decode + field-indep)
- `scripts/probes/wf407_T232-11-conj41_zerofiber_witness.py` (small-prime decide-able witness search)
- `Research/ProximityPrize/Frontier/WF407_Conj41IntendedFormMunRefuted.lean` (the brick)

**In-tree substrate consumed:** `TopDirectionLineCount.lean`
(`point_compat_iff_esymm_zero`, `zero_fiber_filter_eq`, `unitVec`, `CompatC`, `loc_coeff_esymm`).
**Cross-refs:** DISPROOF_LOG O42/O43/O44/O45/O64; `deltastar-407-conj41-escape-clause.md` (A31,
superseded to "refuted"); UNFINISHED_THREADS_407 232-T11, 400-T04 (`n/4−1` orbit law),
407-T16 (Katz floor `n/4`).

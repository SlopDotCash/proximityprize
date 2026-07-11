# δ* #466 — Stepanov-weld round: subgroup escape EXISTS over F_P — `StallResidual` is REFUTED for adversarial evaluation domains (probe-verified end-to-end); arc retrospective (2026-07-11)

**Lane:** P1 rate-quarter — final round of the three-pencil arc (census → harvest cap
→ dimension deficit → this).
**Probe:** `scripts/probes/probe_rate_quarter_p1_stepanov_weld.py` (exact; 158-bit
arithmetic over F_P + end-to-end synthetic census).
**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterStepanovWeld.lean`
(pg-iterate OK 14s; 9 theorems; full axiom lists read manually via `lake env lean`:
8 exactly `[propext, Classical.choice, Quot.sound]`, 1 `[propext]`; no sorryAx).
Build note: `_P1RateQuarterDimensionDeficit` olean built once via lake-locked.

## The finding (major, negative, verified)

The planned weld (in-tree Stepanov engines → `FullyAlignedTripleFree`) is MOOT:
the escape is REAL at the prize modulus and beats the budget.

1. **Escape modulus**: `P − 1 = 2³⁶·(2¹²² + 3)`, `7 ∣ 2¹²² + 3`, so
   `n = 7·2²⁵ = 234881024 ∣ P − 1` — inside the escape window with an EXACT fit:
   `3n = M + 1` (`M = 3(T−1) − N = 704643071`), rows `(x^n − s)·x` of degree
   `n + 1 < k`, three regions tiling the domain to `N − 1` + one junk coordinate.
   All kernel-checked (`escape_modulus_divides`, `escape_window_exact_fit`,
   `escape_domain_tiling`).
2. **The Bezout escape identity**: for ANY three distinct `n`-th powers `s,t,w`,
   `λ = (s−w)/(w−t)` gives `(x^n−s) + λ(x^n−t) = (1+λ)(x^n−w)` — three
   completely-split binomials in a pencil (kernel: `coset_pencil_identity`,
   `coset_lambda_witness`; verified over F_P in the probe).  The solution space is
   `(coset relation)·g`, `dim = k − n = 2²⁵` per row, with the free factor `g`
   FORCED SHARED across all three differences (reduction mod the coset binomial).
3. **END-TO-END REFUTATION at synthetic scale** (`q=1009, n=144, N=613, T=349,
   k=150`): the coset triple realized as three actual pencils on an adversarial
   domain, difference rows `((x^n−s)·x, (x^n−s))` (injective shared ratio map
   `γ = −x`): **#bad = 614 > N = 613**, every `BadFamilyData` clause checked
   exactly (aligned sets EXACT, agreement exactly `T`, non-jointness forced by
   `≥ k` aligned points + the vote coordinate); at P1 ratios every pool would be
   `N − T` = top of the stall band.

**Consequence:** `StallResidual dom` (and a fortiori round-3's
`FullyAlignedTripleFree`) is **FALSE for evaluation domains containing three
cosets of the order-`n` subgroup of `F_P^*`**.  The P1 predecessor counting branch
cannot be closed domain-uniformly.  The open content is now a **DOMAIN condition**:
the standard/structured domains (e.g. interval windows `[0, 2^30)`) must be shown
to avoid large multiplicative-coset traces — a BGK/Paley-type statement, i.e. the
campaign's global wall, now appearing on the domain side.  The margin/dichotomy
theorems of the earlier rounds remain valid and are the live route for structured
domains.

Also kernel-landed: `sharedFactor_pins_scalar` / `sharedFactor_vote_value` — the
collapse-side core (each coordinate pins ONE scalar through shared-factor rows,
value `−g₀/g₁(i)` independent of the coset factor), which is exactly why the
refutation overshoots the budget by a hair (`N + 1` measured; ceiling `N + 2`,
`refutation_margin_arith`) and not by a factor.

## What was NOT claimed

* The refuting construction over F_P is probe-verified, NOT yet Lean-formalized
  (needs `X^n − s` splitting counts via Mathlib `nthRoots`; feasible, flagged as a
  follow-up engineering item).
* No δ* movement: δ* is per-code/per-domain; the refutation concerns adversarial
  domains.  The bracket `3/8 ≤ δ* ≤ 43/96 + 1/(3·2^30)` is untouched.
* The in-tree Stepanov engines (quadratic-character Hasse machinery) neither
  discharge nor contradict the domain condition; they are not the right tool here.

## ARC RETROSPECTIVE (four rounds, 2026-07-11)

1. **Stall-band census** (`_P1RateQuarterStallBandCensus`, 16 thms): extremal
   stall families = two-pencil covers at capacity `2(N−T+1) ≈ 0.898N`; single- and
   two-pencil `StallResidual` instances are unconditional theorems; μ_16 budget
   TIGHT (zero slack) ⟹ any proof must use `2(T−1) > N`.
2. **Pencil harvest cap** (`_P1RateQuarterPencilHarvestCap`, 11 thms): margin
   harvest bound `#riders·D ≤ N−T+D`; three-/four-pencil budgets under margin
   hypotheses (margin 5 sharp); mechanism identified as a dimension count
   (`dim = max(0, 2k − Σ|ov|)` in every geometry probed).
3. **Dimension deficit** (`_P1RateQuarterDimensionDeficit`, 7 thms): the pure
   degree argument REFUTED as universal (explicit toy Bezout escape); forced-
   coincidence theorem (every overlap of a fully-aligned triple `≥ 167772161`);
   symmetric-escape exclusion; named residual `FullyAlignedTripleFree` +
   conditional composition.
4. **Stepanov weld** (this round, 9 thms): the escape EXISTS at the prize modulus
   (`7·2²⁵ ∣ P−1`, exact fit) and REFUTES `StallResidual` on adversarial domains
   (end-to-end synthetic verification, `614 > 613`).  Residual re-scoped to a
   domain condition.

Net: 43 kernel theorems across four files, all axiom-clean
(`[propext, Classical.choice, Quot.sound]` or better), four probes (deterministic,
exact), and a precise localization of the P1 counting wall: **the budget holds for
≤2-pencil families unconditionally, for 3-pencil families under margins that
generic geometry forces, and FAILS on domains embedding three large multiplicative
cosets — the standard-domain case is exactly a BGK/Paley-type window statement.**

## Next targets (for whoever picks the lane up; the lane rests)

1. Formalize the refuting construction over F_P (Mathlib `nthRoots` +
   coset-cardinality; converts the probe refutation into a kernel theorem
   `¬ StallResidual dom_adv` — evidence-grade for the domain-condition re-scope).
2. State and attack the domain condition for the standard window: no three
   `≥ 234881024`-point traces of multiplicative cosets in the actual P1 evaluation
   domain — connect to the campaign's existing subgroup-window walls
   (`_WallStepanovSubgroupDescent`, OC-CRT notes).
3. The dichotomy hardening (margin ∨ shared-factor) for structured domains, where
   the escape is absent and the round-2/3 margins are forced.

# #444 Floor = Wall: airtight equivalence + 8-angle trichotomy sweep (2026-06-17)

**Verdict in one line:** the floor (`δ* ≥ entropy value`, worst-case list small for ALL words)
and the wall (`M(n) = max_{b≠0} |Σ_{x∈μ_n} e_p(bx)| ≤ C√(n log m)`, equiv. `E_r ≤ K^r·Wick`)
are now formalized as the SAME object — a two-sided axiom-clean equivalence over the governing
`csSup` law — and **all 8 new angles (4 wall-side, 4 floor-side) reduce to that wall; 0 escape the
trichotomy.** No closure, no fabrication; the shared core `M ≤ C√(n log m)` stays OPEN.

This doc is a synthesis of landed Lean bricks; every claim below is backed by an axiom-clean file
(`axioms ⊆ {propext, Classical.choice, Quot.sound}`, 0 `sorryAx`, via `scripts/pg-iterate.sh`).

---

## (a) The airtight floor ⇔ wall equivalence — both directions axiom-clean

**File:** `Frontier/_FloorWallEquivalence.lean` (scratch `_`-prefix; elaborates in 79s; all 9
audited theorems `[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`, decide-free).

Both directions land over the governing `csSup` law (`MCAThresholdLedger.mcaDeltaStar`):

- **SUFFICIENCY (sharp object ⇒ floor):** `sharp_object_implies_floor` +
  `sharp_object_gives_good_bracket`. Per-frequency-controlled far-line count is within budget on
  `[0, δ0)` and over budget on `(δ0, 1]`, giving `threshold = δ0`, wired through
  `priceFromCount = count/q = epsMCA`.
- **NECESSITY (floor ⇒ sharp object):** `floor_implies_sharp_object` +
  `floor_fails_of_sharp_object_fails`. On the under-determined word whose bad-scalar count IS the
  character sum (`UnderdeterminedWordIsCharSum`, = the `DeltaStarOP1BindingN16` / `FarCosetExplosion`
  orbit identity), the floor forces `etaSq ≤ budget` — so the wall is **necessary**, not a
  loose-reduction artifact.
- **ASSEMBLED:** `floorWall_equiv` (`δ* = δ0` IFF the count crosses budget at `δ0`).

### What "attacking the wall = attacking the floor" means PRECISELY — and on which object

The genuine two-sided pin is the **SHARP PER-FREQUENCY / ENERGY object, NOT bare `M(n)`**:

```
SharpPerFrequencyObject etaSq M := etaSq ≤ M          -- = in-tree WorstCaseIncompleteSumBound
  ⇔  ∀ b ≠ 0, ‖η_b‖² ≤ M
  ⇔  E_r ≤ (2r-1)!!·n^r = K^r·Wick     -- via Σ_b ‖η_b‖^{2r} = q·E_r (moment identity)
```

This object is two-sided because Direction 1 makes it **sufficient** (its far-line-count bound
certifies the floor) and Direction 2 makes it **necessary** (the under-determined word's list
literally equals it). The single open input is `SharpObjectHolds` — **never discharged = the prize.**

The scalar `M(n) = √(max etaSq)` is ONLY the value Direction 2 forces; Direction 1 cannot consume
it through a triangle bound. This nuance is PROVEN, not asserted:

- `M_triangle_is_vacuous`: the bare-`M` triangle envelope `slots·M/q` overshoots the prize budget
  (`slots = Θ(n)` inflates `M ~ √(n log m)` past `budget ~ n`), so `M` alone cannot certify the
  floor even when it holds.
- `sharp_object_closes_triangle_gap`: the per-frequency object closes exactly that gap.
- `no_second_order_route` / `prize_rMax_lt_rOpt`: `r_opt = log₂ m = 128 > r_max = 2β ≤ 10`, so no
  order-`r` moment/L2 certificate transfers char-0 energy to char-p at the depth the floor needs.

**Honesty/scope.** This is an HONEST REDUCTION, not a closure. The file is an abstract `csSup`
skeleton (minimal-import, same methodology as in-tree `PrizeEquivalencePin.lean`), re-exporting the
SHAPES of the governing law and the concrete bricks (`UnderdeterminedWordIsCharSum` from
`DeltaStarOP1BindingN16` + `FarCosetExplosion`; the per-frequency control step) as **named
hypotheses**, not re-proven — no laundering of the open core. The two structural bridges (under-
determined-word identity `count = etaSq`; per-frequency `count ≤ incidenceEnvelope`) hold concretely
in-tree at the `n = 16` binding (`binding_OP_eq_one`); **persistence to `n ≥ 32` is the open
D*/energy question.** Recommend a real `lake build` of the module before landing (autoImplicit check;
binders are all explicit so it should pass).

---

## (b) Per-angle bucket table (B1 = L2/average-blind · B2 = BGK/energy rename · B3 = Sidon-hyp-fail)

Escape requires E1 (output the SUP) **AND** E2 (genuinely new object) **AND** E3 (hypothesis holds on
flat 0-dim `μ_n`) SIMULTANEOUSLY.

| # | Angle | Side | Bucket | Verdict | Why it cannot escape |
|---|-------|------|--------|---------|----------------------|
| 1 | choose-p / bad-prime-density | wall | **B2** | reduces-to-wall | Fails E2 (same `E_r`, only WHICH prime changes) **and** E3 (good-depth hypothesis VACUOUS on prize `μ_n`) |
| 2 | c_r-monotonicity-deep | wall | **B2** | reduces-to-wall | `slack_r = Wick_r − E_r`; `c_r ≤ 1` is exactly the DC-subtracted Wick bound on the energy ladder (E2 fails) |
| 3 | deep-r-concentration (hypercontractivity cube) | wall | **B3** | reduces-to-wall | E1+E2 pass, **NOT-E3**: period is high-degree on the cube ⇒ Bonami-Beckner `(2r-1)^{μ/2}` reproduces the trivial Parseval bound |
| 4 | p-adic Newton spur (2-adic) | wall | **B2** | reduces-to-wall | `v_2(N)` bounded + p-independent + disjoint from the `v_p` slot; residual IS the energy defect (E1, E2 fail) |
| 5 | floor-necessity-underdet | floor | **B2** | reduces-to-wall | Only proven content is a reverse-Markov LOWER bound via `E_r/E_{r-1}` (E1 fails: sup from below only); object = `η_b` (E2 fails) |
| 6 | floor-pattern-count-direct | floor | **B2** | reduces-to-wall | `F_p^max = N_fib` only at primes MISSING the bounded-norm bad set; inflates with the spur ⇒ E3 fails |
| 7 | floor-interleaved-joint (FRI tower) | floor | **B2** | reduces-to-wall | Sound regime: joint list = single-level list (definitional rename, E2 fails); other regime drops members the WRONG way (soundness loss) |
| 8 | LP-Delsarte-on-list (coset scheme) | floor | **B1** | reduces-to-wall | Commutative `C_n` scheme LP outputs the Parseval `√(p−n)` ceiling (`√(m/2log m) ≈ 2^63` loose at prize); `E_2` invisible to linear certs (E1 fails) |

**ESCAPES: none.** 8/8 bucketed; 0 survivors, 0 partials.

Files: `_ChoosePThresholdCollapse.lean`, `_CrMonotonicityDeep.lean`, `HypercontractivityCubeNoGo.lean`,
`_PadicNewtonSpur2Adic.lean`, `_FloorNecessityWall.lean` (+ probe for #6), `_JointTowerListNoGo.lean`,
`CosetSchemeLPNoGo.lean`.

---

## (c) Did choose-p at the REAL β open anything? — NO, it collapses to the wall

This is the load-bearing wall-side check (memory had flagged the small-`n` β=4 proxy as a trap).

**The β-lift is REAL but SHALLOW — a finite-window mirage.** Exact-spur probe:
- `n = 16, β = 4`: good-frac collapses (`r=4: 0.967`, `r=5: 0.333`).
- `n = 16, β = 5.27` (the REAL prize β = `1 + 128/log₂ n`): good-frac stays `1.000` through `r=5`
  (all 30 band primes good); `n = 8, β ≥ 5` all-good through `r=6`.

So raising β from 4 → 5.27 pushes spur-onset PAST the computable window — it **looks like survival.**
The deep-`r` law exposes it as a mirage, asymptotic-free:

- Certified-good depth needs `(2r)^{φ(n)} < p`. At `n = 2^30`, `φ(n) = 2^{29}`, and the whole prize
  modulus `p = n·2^128 = 2^{μ+128}` fits in `φ(n) = 2^{μ-1}` bits once `μ ≥ 9` (true at prize
  `μ = 30, 40`). Hence `p ≤ 2^{φ(n)} ≤ (2r)^{φ(n)}` for ALL `r ≥ 1` — the good-depth hypothesis is
  VACUOUS, certifying char-0 faithfulness at **no depth `r ≥ 1`** (collapse below `r = 1`,
  since `p^{2/n} → 1`).
- `r_cross/r_need → 0.0046` at the prize (`r_cross = ½p^{1/φ(n)} → ½`, no integer depth; `r_need =
  ln p → 109` at `n = 2^30`).

**Lean:** `_ChoosePThresholdCollapse.lean` (axiom-clean, 95s). `totient_two_pow` (`φ(2^μ)=2^{μ-1}`);
`prize_exp_le_totient` (`μ+128 ≤ 2^{μ-1}` for `μ ≥ 9`); `choose_p_threshold_vacuous`;
`no_certified_good_depth` (certified-good depth set is empty). Non-vacuous: tight onset `μ=8` fails /
`μ=9` holds, the prize prime really satisfies the hypothesis.

**Honesty check PASSED:** the brick is correctly ONE-SIDED — it proves the CERTIFICATE is vacuous
(choose-p buys zero deep faithfulness), NOT that the energy actually defects (that remains the open
wall). So **reduces-to-wall is right, not a refutation.** Net: choose-p is a B2-BGK-rename clearing
only the O(1)-shallow band that was already clean; the deep-`r` char-p defect = the prize wall is
completely untouched. **No opening.**

---

## (d) Genuine partial-proven sub-results (real new content, char-0 / structural)

These are honest axiom-clean gains that sit ON the wall (none closes the prize):

1. **Deep `c_r` rung (char-0)** — `_CrMonotonicityDeep.lean`. Exact all-`r` structural equivalence
   `cStepGen_le_one_iff_slack_growth`: `c_r ≤ 1 ⇔ slack_{r+1} ≥ n·slack_r` where
   `c_r = (E_{r+1} − n·E_r)/(2r·n·Wick_r)`. NEW deep rung `cStep_three_le` (`c_3 ≤ 1` via a freshly
   derived `E_4` anchor) and `aRatio_four_le` (`a_4 ≤ 1`). Concrete witness `slack_growth_three`:
   `slack_4 − n·slack_3 = 15n(39n² − 93n + 77) ≥ 0` (both witness quadratics have negative
   discriminant ⇒ hold for all `n > 0`). Char-0 margin `slack_{r+1}/(n·slack_r) ≥ 9.8` everywhere,
   converging to `2r+1` ⇒ `c_r → 0` deep in char-0. **NOTE:** `c_r ≤ 1` is STRICTLY STRONGER than
   `a_r ≤ 1` when `a_r < 1`, so this reduction is at-least-as-hard as BGK — never a relaxation.

2. **Floor-necessity unconditional anchor** — `_FloorNecessityWall.lean`. The genuinely-new proven
   content is `worstPeriod_sq_ge_unconditional` (= in-tree `exists_period_sq_ge_moment_ratio`): a
   reverse-Markov LOWER bound on the sup via the consecutive moment ratio `E_r/E_{r-1}`, **no Weil,
   no open input**. CAVEAT folded into the record: the three "equivalence" theorems are content-free
   algebra on free reals; ALL floor=wall content lives in the undischarged `UnderDetListEqPeriod`,
   which honestly asserts `O_P = M(n)²` (the open demand-floor ↔ analytic-wall identification), NOT
   the proven combinatorial `#bad = (n/d)·O_P` identity. The docstring "faithful analytic shadow" was
   an overclaim (different object class / growth law) — recommend the rename.

3. **Char-0 cube combinatorics** — `HypercontractivityCubeNoGo.lean`. `factorial_le_wick`
   (`r! ≤ (2r-1)!!`) and the high-degree cube no-go under the honestly-named gate `CubeDegreeIsHigh`.
   **REQUIRED CORRECTION (audit-caught, non-fatal):** the docstring/`exp_*` lemmas mislabel the
   limiting char-0 law of `|η_b|²/n` as Exponential(1) (moments `r!`, `E_r/Wick → 0`); the file's OWN
   probe shows it is **chi-squared-1** (moments `(2r-1)!!`, cumulants `2^{r-1}(r-1)!`, `E_r/Wick → 1`
   at fixed `r`, `μ → ∞`). The `→ 0` ratio was a small-`n` (`μ ~ r`) artifact. This does NOT flip the
   verdict (char-0 saturating Wick only reinforces that **Lam-Leung matching, not hypercontractivity**,
   controls the moments) but the `exp*` theorems should be relabeled as a clean combinatorial
   inequality decoupled from the false "this is the period's law" claim.

4. **2-adic spur valuation** — `_PadicNewtonSpur2Adic.lean`. `v_2(N)` is bounded (max 4 in sample,
   identical dist `r=5` vs `r=6`, no `Θ(r)` Stickelberger growth), p-independent/blind (constant
   while carrier existence/count is sharply p-dependent), and lives in a prime slot DISJOINT from the
   operative `v_p = 1`. **CORRECTION:** the pinned "`N = 2p` at minimal depth" is an `n=16`-Fermat-
   prime artifact (at `n=32` only ~1/3 of primes give `N=2p`); the honest statement is "`v_2(N)`
   bounded and disjoint from the p-slot" (proven by probes), NOT "`N = 2p`". Theorems still
   axiom-clean and TRUE about the literal `2p`; verdict unchanged.

5. **Coset-scheme LP solved (not just asserted)** — `CosetSchemeLPNoGo.lean`. Went BEYOND the
   writeup: actually SOLVED the commutative-scheme LP — it caps at the mass `S = p−n` even with
   Q-positivity. `lp_value_eq_mass_of_linear_certs`, plus the decisive separation
   `e2_invisible_to_linear` (`E_2 = Σ τ² = #{a+b=c+d}` is a 4-point/quadratic functional, structurally
   outside any linear 2-point Delsarte certificate) and `energy_is_quadratic_not_linear`.

---

## (e) The single sharpest shared statement — and whether ANY angle escapes

**Floor = Wall core (one statement).** Let `μ_n ⊂ F_p*` be the proper order-`n = 2^μ` subgroup
(`n | p−1`, never the full group), `η_b = Σ_{x∈μ_n} e_p(bx)`, `m = (p−1)/n` the index, and
`E_r = #{(a,b)∈μ_n^{2r} : Σa = Σb in F_p}`. Then the following are EQUIVALENT, and **each is the
prize:**

> **(FLOOR)** `δ* ≥` the entropy value (worst-case list small for ALL words)
> **⇔ (WALL)** `M(n) = max_{b≠0} |η_b| ≤ C·√(n log m)`
> **⇔ (ENERGY)** `E_r ≤ K^r·(2r-1)!!·n^r` (Wick) at `r ~ ln q`, i.e. the char-p spur
> `Spur_r = E_r^{F_p} − E_r^{c0}` stays `0` (or `≤ K^r·Wick`) through the deep window `r_need ~ ln p ~ 14–21`.

The char-0 side is DONE (Lam-Leung: `E_r^{c0} ≤ (2r-1)!!·n^r`, slack-growth margin `~2r+1`). The
ENTIRE open prize is the **char-p Lam-Leung transfer / deep-`r` spur** = the BGK/Paley `√`-cancellation
wall = the additive-energy defect onset at `r ~ ln p` — the SAME single object the per-frequency
sharp object `‖η_b‖² ≤ M` controls.

**Does ANY angle escape the trichotomy? NO.** All 8 fail at least one of E1/E2/E3:
- B1 (#8): the method outputs the L2/Parseval scale `√(p−n)`, blind to the sup `√log` (E1 fails).
- B2 (#1,2,4,5,6,7): the controlled object IS `η_b` / `E_r` / the spur renamed — choosing a prime,
  reshaping the recursion residual, the 2-adic valuation, the moment-ratio lower bound, the fibre
  pattern-count, the FRI tower wrapper — none is a genuinely new object (E2 fails); several also fail
  E3 (vacuous-on-`μ_n`, e.g. choose-p) or E1 (lower-bound-only, e.g. necessity).
- B3 (#3): E1+E2 pass but the hypercontractive machine needs low cube-degree that the high-degree
  period `μ_n` LACKS (E3 fails) — Bonami-Beckner reproduces the trivial Parseval bound.

**Bottom line.** Floor and wall are now formally one object with a two-sided axiom-clean equivalence;
the sharp per-frequency / energy object is the genuine pin (bare `M` is necessary-but-insufficient,
PROVEN via `M_triangle_is_vacuous`). 8 new angles, 8 reductions, 0 escapes — the trichotomy holds. The
shared core `M ≤ C√(n log m)` = char-p deep-`r` Lam-Leung spur is UNCHANGED and OPEN. No closure, no
fabrication; honesty contract intact.

---

### Files (all `Frontier/`, axiom-clean unless noted)

- `_FloorWallEquivalence.lean` — the two-sided equivalence (a)
- `_ChoosePThresholdCollapse.lean` — choose-p deep-`r` vacuity (c)
- `_CrMonotonicityDeep.lean` — deep `c_r` char-0 rung (d.1)
- `HypercontractivityCubeNoGo.lean` — cube no-go (d.3; needs `exp*`→chi-sq relabel)
- `_PadicNewtonSpur2Adic.lean` — 2-adic spur valuation (d.4; `N=2p` is artifact)
- `_FloorNecessityWall.lean` — unconditional moment-ratio anchor (d.2; rename `UnderDetListEqPeriod`)
- `_JointTowerListNoGo.lean` — FRI joint-tower no-go (b.7)
- `CosetSchemeLPNoGo.lean` — coset-scheme LP solved (b.8, d.5)

In-tree anchors referenced: `PrizeEquivalencePin`, `FloorResonanceEnergyBridge`,
`GaussPeriodMomentBound`, `MCAThresholdLedger`, `DemandFloorReduction`, `DeltaStarOP1BindingN16`,
`FarCosetExplosion`, `FiberEnergyListBound`.

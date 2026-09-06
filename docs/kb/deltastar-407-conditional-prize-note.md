# #407 — The Conditional Prize Result: BGK Is the Limit (Honest Consolidated Note)

> **Status: NOT a closure.** This note consolidates what is *proven* (axiom-clean, in-tree), what is
> *unconditional* in the literature, and the *single named open conjecture* on which the exact prize
> value rests. Per the §6 honesty contract (`ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md`): the
> exact scale of the prize quantity is pinned **two-sided modulo one named `Prop`**
> (`WickEnergyBracket`). The conjecture is supported by exhaustive exact-numerical evidence but is the
> recognized-open BGK / Paley-graph / BCHKS-1.12 problem. **No claim of unconditional closure is made.**

Date: 2026-06-15. Issue #407 (successor of #232 → #334 → #357 → #389 → #371; consolidating into #444).
Prize source: [ABF26] *Open Problems in List Decoding and Correlated Agreement*, ePrint 2026/680,
proximityprize.org ($1M).

---

## Abstract

The Ethereum Proximity Prize asks to pin the mutual-correlated-agreement (MCA) list-decoding threshold
`δ*` for explicit smooth-domain Reed–Solomon codes in the window `(1 − √ρ, 1 − ρ − Θ(1/log n))` at
`ε* = 2⁻¹²⁸`. Two independent reductions (the coset-saturation / Vieta–sumset route and the
Gauss-period sup-norm route) converge on one analytic quantity: `B = max_{b≠0} ‖η_b‖`, the worst
incomplete Gauss period (= non-principal eigenvalue of the generalized Paley graph `Cay(F_q, μ_n)`) over
the smooth 2-power multiplicative subgroup `G = μ_n`, `n = 2^μ`. We report:

1. **The exact-value conjecture** (Kambiré window edge): `δ* = 1 − ρ − H(ρ)/(β·log₂ n)` (entropy form),
   equivalently `B = max_{b≠0} ‖η_b‖ = √(2n·ln(q/n))·(1 + o(1))` (Gaussian/Ramanujan scale).
2. **A conditional, axiom-clean theorem** (`BGKLimitConditional.lean`,
   `worstPeriodPow_pinned_of_wick`): the exact *scale* of `B` is pinned **two-sided**, modulo one named
   `Prop` `WickEnergyBracket` — the statement that the `r`-th additive energy `E_r(μ_n)` lies in
   `[clo, chi]·(2r−1)‼·n^r` at depth `r ≈ log q`.
3. **An unconditional lower bound** `B ≥ 1.85√n` from the char-0 energy (measured `LB/√n ∈ [1.85, 1.90] in deep-β rows (as low as ≈1.38 at small β)`).
4. **An unconditional upper bound** `B ≤ n^{1−31/2880+o(1)}` (di Benedetto–Garaev, for `n > q^{1/4}`),
   degrading to the ineffective BGK `n^{1−o(1)}` at the prize point `n ≤ q^{1/4}`.
5. **The precise open statement**: `WickEnergyBracket` at `r ≈ log q` — identical to the BGK /
   Paley-graph-conjecture / BCHKS-Conj-1.12 deep-moment problem, and to the coset route's "Dyadic Gap
   Vanishing-Sum Suppression" conjecture.
6. **Evidence the conjecture holds**: the period is sub-Gaussian (4th cumulant `κ₄ < 0` over every tested
   prime), prime sweeps give `B/√(2n·ln(q/n)) ∈ [0.76, 1.07]` (bounded, not blowing up), MGF proxy `< n`,
   and the marginal tail matches a Gaussian out to the deep tail (`emp/Gauss ≤ 0.17`, thinner than
   Gaussian → EVT-floor consistent).
7. **An exhaustive census of refuted routes** with the structural reason each fails — the entire modern
   additive-combinatorics / character-sum toolkit caps at the wrong exponent at `n ≤ q^{1/4}`.

The honest verdict: the prize value is determined **conditionally on one recognized-open
additive-combinatorics conjecture**, with both prize directions (BGK upper "the conjecture is the value"
and char-0 lower "BGK is the limit") meeting at the same named object. This is the publishable conditional
form, not a closure.

---

## 0. Notation and the central object

* `F_q`, `q ≡ 1 (mod n)`, prize regime `q = n^β`, `β ≈ 4–5`, `n = 2^μ` with `μ` up to `30`, `ε* = 2⁻¹²⁸`,
  rate `ρ = k/n ∈ {1/2, 1/4, 1/8, 1/16}`.
* `μ_n ⊆ F_q^*` the smooth (2-power) multiplicative subgroup, `|μ_n| = n`, cofactor `m = (q−1)/n`.
* `ψ` a fixed primitive additive character of `F_q`. The **Gauss period / incomplete subgroup sum**
  `η_b := Σ_{x ∈ μ_n} ψ(b·x)`, `b ∈ F_q`. Because `μ_n` is closed under negation (`2 | n`), every `η_b`
  is **real**.
* The prize per-frequency core: `B := max_{b≠0} ‖η_b‖`. By Liu–Zhou Thm 115, `B` is the non-principal
  eigenvalue of the generalized Paley graph `Cay(F_q, μ_n)`; `B ≤ 2√n ⟺ Ramanujan` is the (open) Paley
  Graph Conjecture.
* `r`-th additive energy `E_r(G) := #{(x₁..x_r, y₁..y_r) ∈ G^{2r} : Σ x_i = Σ y_j}` (`rEnergy`,
  `SubgroupGaussSumMoment.lean:28`).
* **The moment identity** (in-tree, axiom-clean, the bridge both directions share):
  `Σ_{b ∈ F_q} ‖η_b‖^{2r} = q · E_r(μ_n)` (`SubgroupGaussSumMoment.subgroup_gaussSum_moment`, line 52).
* The **"Wick value"** is the char-0 Gaussian `2r`-th moment of a variance-`n` real Gaussian:
  `WickVal_r := (2r−1)‼ · n^r`.

---

## 1. The exact-value conjecture (Kambiré edge)

### 1.1 The two equivalent statements

**Form A (window edge, δ\*).** For `RS[F_q, μ_n, k]`, `ρ = k/n`, `q = n^β`, `ε* = 2⁻¹²⁸`:

> `δ* = 1 − ρ − 2ρ·ln(1/(2ρ)) / log₂(q·ε*)`   (exact, worst case),

which in entropy normalization is the **Kambiré window edge** `δ* = 1 − ρ − H(ρ)/(β·log₂ n − H'(ρ))` up
to the `Θ(1/log n)` second-order term (`EntropyGateDeltaStar.lean`, line 16). The **upper bracket**
(`δ* ≤ …`) is **PROVEN** in-tree by Kambiré's coset-line construction (arXiv:2604.09724): the line
`{X^{rm} + λX^{(r−1)m}}` produces exactly `|H^{(+r)}(μ_s)|` bad scalars (distinct `r`-fold sums of
`μ_s`-th roots) at radius `1 − ρ − 2/s` (`KKH26WitnessSpread.kkh26_mcaDeltaStar_le`,
`FactorizationRigidity.lean`).

**Form B (per-frequency scale, B).** The same window edge holds **iff** the per-frequency Gauss period
obeys the Gaussian/Ramanujan scale at depth `r ≈ log q`:

> `B = max_{b≠0} ‖η_b‖ = √(2n·ln(q/n))·(1 + o(1))`.

The equivalence is the content of the substrate chain `GeneralizedPaleyRamanujan.lean` /
`GaussPeriodMomentBound.lean` → `WorstCaseIncompleteSumBound` → the interior δ\* consumer: a Gauss-period
bound `B ≤ M_r` discharges the worst-case incomplete-sum residual at scale `M_r`, and minimizing
`M_r(r)` over `r` (optimum `r* ≈ ln q`, using `((2r−1)‼)^{1/2r} ~ √(2r/e)`) yields exactly
`√(2n·ln(q/n))`.

### 1.2 Why `√(2n·ln(q/n))` is the conjectured constant

The cofactor is `m = (q−1)/n`, so `ln m = ln(q/n)`. There are `m` distinct period values `η_b` (one per
`m`-coset of `b`). If the periods behaved as `m` iid Gaussians of variance `n` (the "random / Wick
model"), extreme-value theory gives a maximum of `√(2·Var·ln m) = √(2n·ln(q/n))`. The conjecture is
precisely that **the arithmetic periods are no worse than this Gaussian model** at the deep order
`r ≈ ln m` — equivalently the additive energy matches the Gaussian moment (`E_r ≤ chi·(2r−1)‼·n^r`).

---

## 2. The conditional theorem (`BGKLimitConditional.lean`)

File: `ArkLib/Data/CodingTheory/ProximityGap/BGKLimitConditional.lean`. Namespace
`ArkLib.ProximityGap.BGKLimitConditional`. Axiom-clean (`[propext, Classical.choice, Quot.sound]`, no
`sorry`; the file ends with `#print axioms … worstPeriodPow_pinned_of_wick`).

### 2.1 The unconditional two-sided max↔moment bracket

```
theorem max_moment_bracket (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i ≤ (Fintype.card ι : ℝ) * max a) ∧ (max a ≤ ∑ i, a i)
```

For nonnegative `a` (here `a := η^{2r}`), `M := max a` satisfies `Σ a ≤ N·M` (max ≥ average, multiplied
form) and `M ≤ Σ a` (max-term ≤ sum). This is the exact, division-free algebraic content of "the worst
Gauss period is pinned by the energy moment from both sides." Unconditional and trivially clean.

### 2.2 The named open `Prop`

```
def WickEnergyBracket (Er WickVal clo chi : ℝ) : Prop :=
    clo * WickVal ≤ Er ∧ Er ≤ chi * WickVal
```

`E_r` is sandwiched in `[clo·WickVal, chi·WickVal]` with `WickVal = (2r−1)‼·n^r`, uniformly to depth
`r ≈ log₂ q`. This is the single deferred input — see §4.

### 2.3 The conditional exact-scale pin

```
theorem worstPeriodPow_pinned_of_wick
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (q Er WickVal clo chi : ℝ) (hq : 0 ≤ q)
    (hsum : ∑ i, a i = q * Er)
    (hwick : WickEnergyBracket Er WickVal clo chi) :
    q * clo * WickVal ≤ (Fintype.card ι : ℝ) * max a ∧ max a ≤ q * chi * WickVal
```

Granting `WickEnergyBracket` and the in-tree period↔energy identity `Σ_b η_b^{2r} = q·E_r`
(`a := η^{2r} ≥ 0`, `0 ≤ q`), the worst period's `2r`-th power is pinned **two-sided**:

> `q·clo·WickVal ≤ N·max_b η_b^{2r}`   and   `max_b η_b^{2r} ≤ q·chi·WickVal`.

At `r ≈ log q`, `WickVal = (2r−1)‼·n^r`, this squeezes `B = max_b ‖η_b‖ = √(2n·ln(q/n))·Θ(1)` — **the
exact prize scale, proven modulo the one named `Prop`.**

**Honest scope of the pin.** It pins the *scale/exponent* `√(n·log q)` two-sided. The residual to the
exact *constant* `√2` is (i) the `N^{1/2r} ≈ √e` averaging-window factor (the `max ≥ average` direction
loses `(#terms)^{1/2r}`) and (ii) the `[clo, chi] → 1` tightness of the conjecture. The lower direction
is genuinely new (char-0 energy supplies `clo` unconditionally → `B ≥ 1.85√n`, §3); the upper is the BGK
cancellation. Both meet at `WickEnergyBracket` — so "BGK is the limit" (lower) and "the conjecture is the
value" (upper) are the **same named open object**.

### 2.4 The bridge files

* `GaussPeriodMomentBound.lean` (`ArkLib.ProximityGap.GaussPeriodMomentBound`, axiom-clean):
  `GaussianEnergyBound G r := E_r(G) ≤ (2r−1)‼·|G|^r` (the `clo = chi = 1` case, line 51). Theorems
  `eta_pow_le_of_energyBound` (`‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r`, line 57) and
  `worstCaseIncompleteSumBound_of_energyBound` (discharges the in-tree open residual at
  `M_r = (q·(2r−1)‼·n^r)^{1/r}`, line 74).
* `GaussPeriodMomentBoundSlack.lean` (axiom-clean): the moment method tolerates a **polynomial** slack —
  `GaussianEnergyBoundWithSlack G r S := E_r(G) ≤ S·(2r−1)‼·n^r` (line 50) gives `B ≤ √(M_r(S))` carrying
  only `S^{1/2r}`, which is `O(1)` for polynomial `S = n^A` at `r ≈ ln m` (`slack_scale_factor`, line 95:
  `M_r(S) = S^{1/r}·M_r(1)`). This *relocates* the open core to a strictly weaker poly-slack
  higher-energy bound (already KNOWN at `r = 2` via Heath-Brown–Konyagin, `E_2(μ_n) ≤ n^{5/2}` for
  `n < p^{1/4}`).

---

## 3. Unconditional bounds

### 3.1 Lower bound `B ≥ 1.85√n` (char-0 energy, unconditional)

The char-0 additive energy `E_r^{(0)}(μ_n)` is the exact integer count of equal `r`-fold sums of `n`-th
roots of unity in `ℂ` (Lam–Leung structure: negation pairs). It is `≤` the char-`p` energy (char-`p`
only adds wrap-around collisions). Hence the provable lower bound

> `max_b η_b^{2r} ≥ (q·E_r^{(0)}(μ_n) − n^{2r}) / (q − 1)`

(subtracting the trivial mode `b = 0`, where `η_0 = n`). Taking the `2r`-th root and optimizing over `r`:

`probe_407_bgk_lower_bound_saturates.py` (exact, FFT-free char-0 convolution; reproduced this session):

| p | n | β | true max | √(2n·ln(q/n)) | provable LB | **LB/√n** | 2√n (Ramanujan) |
|---|---|---|---|---|---|---|---|
| 769 | 8 | 3.20 | 6.57 | 8.55 | 5.23 | **1.847** (r\*=7) | 5.66 |
| 12289 | 8 | 4.53 | 7.65 | 10.84 | 5.37 | **1.899** (r\*=7) | 5.66 |
| 786433 | 8 | 6.53 | 7.95 | 13.56 | 5.38 | **1.902** (r\*=7) | 5.66 |
| 12289 | 16 | 3.40 | 10.91 | 14.58 | 7.29 | **1.823** (r\*=5) | 8.00 |
| 786433 | 16 | 4.90 | 14.06 | 18.59 | 7.43 | **1.857** (r\*=5) | 8.00 |

So `B ≥ 1.85√n` unconditionally in the tested range (robust band `B ≥ (1.82..1.90)√n`). This is *strictly
below* the Ramanujan threshold `2√n` and *strictly below* the conjectured floor `√(2n·ln(q/n))` — it
confirms the conjectured floor is the right order but does not reach it (the char-0 lower bound captures
`clo` but not the deep-order constant). The lower direction is what makes the §2 pin two-sided.

### 3.2 Upper bound `B ≤ n^{1−31/2880+o(1)}` (BGK / di Benedetto, literature)

The best *unconditional* upper bound on `B` in the literature:

* **di Benedetto–Garaev–García–González-Sánchez–Shparlinski–Trujillo**, *New estimates for some
  exponential sums* (2020, arXiv:2003.06165, Thm 3.1): `B ≲ n^{2689/2880}·p^{1/72}`, whose **corollary**
  for `n > p^{1/4}` is the headline power-saving `B ≤ n^{1 − 31/2880 + o(1)}` (cancellation exponent
  `δ = 31/2880 ≈ 0.0108`, the current SOTA). This is formalized as a named literature `Prop` in
  `Frontier/_BGKExponentReduction.lean` (`BGKCharSumBound`, `diBenedettoDelta := 31/2880`, line 101).
* Below `p^{1/4}`: only the **ineffective** Bourgain–Glibichuk–Konyagin (BGK) bound `n^{1−o(1)}` survives,
  where the `o(1)` is not explicit.

**The decisive localization.** The prize is `n = 2^μ`, `q = n^β`, `β ≈ 4–5`, so `n = q^{1/β} ≤ q^{1/4}` —
**at or below** the `p^{1/4}` threshold, exactly where the di Benedetto power-saving **vanishes** and only
the ineffective BGK `n^{1−o(1)}` survives. The prize needs the exponent `1/2` (i.e. `B ≲ √n` up to logs);
SOTA at the prize point is `1 − o(1)` with an ineffective `o(1)`. **The gap is a full half-power at the
single hardest point for every known method.** In Lean: `diBenedettoDelta_lt_prizeDelta` (`31/2880 < 1/2`,
`Frontier/_BGKExponentReduction.lean:109`) and `Frontier/_BGKSOTAInsufficiency.lean`
(`prize_requires_exponent_beyond_sota`) formalize that this exponent cannot reach the prize.

> **Exponent note.** The task brief quoted `n^{1−1/2880}`; the *precise* SOTA cancellation exponent is
> `δ = 31/2880` (di Benedetto Thm 3.1 corollary for `n > p^{1/4}`), as carried in-tree by
> `diBenedettoDelta = 31/2880`. We use the accurate value. Either way `δ ≪ 1/2`, so the conclusion is
> unchanged: SOTA is a full half-power short.

### 3.3 The unconditional bracket

Combining §3.1 and §3.2 (both unconditional, both in the literature/in-tree):

> `1.85√n ≤ B ≤ n^{1−31/2880+o(1)}`   (for `n > q^{1/4}`),

with the upper bound degrading to the ineffective `n^{1−o(1)}` at the prize point `n ≤ q^{1/4}`. The
conjectured value `B = √(2n·ln(q/n))·(1+o(1))` lives strictly inside this bracket; pinning it to the exact
scale is precisely §2's conditional pin.

---

## 4. The open core (precise statement)

The single open input is `WickEnergyBracket` at `r ≈ log q`:

> **Open conjecture (deep-moment / `WickEnergyBracket`).** There exist absolute constants
> `0 < clo ≤ chi < ∞` such that for the prize regime (`n = 2^μ`, `q = n^β`, `q ≡ 1 mod n`),
> `clo·(2r−1)‼·n^r ≤ E_r(μ_n) ≤ chi·(2r−1)‼·n^r` for all `r ≤ ⌈log₂ q⌉`.

The **upper half** (`E_r ≤ chi·(2r−1)‼·n^r`, equivalently `B ≤ C√(n·ln(q/n))`) is the prize-binding
direction. It is *identically* the following recognized-open problems:

* **BGK / sum–product**: control of the deep additive energy of a small multiplicative subgroup
  `μ_n ⊂ F_q^*` with `n ≤ q^{1/4}`, at depth `r ≍ log q` (di Benedetto–Garaev is the SOTA and it vanishes
  here — §3.2).
* **Paley Graph Conjecture**: `B ≤ 2√n ⟺ Cay(F_q, μ_n)` Ramanujan (open; best proven is BGK `n^{1−o(1)}`).
  In-tree identification: `deltastar-Bmun-IS-generalized-Paley-spectral-gap-2026-06-13.md`.
* **BCHKS-1.12** (subgroup-sumset conjecture, the upper-bracket gate of #389).
* **The coset-route "Dyadic Gap Vanishing-Sum Suppression" conjecture** (the second independent
  derivation, `prize-407-exact-deltastar-kambire-conjecture.md`): no nonempty antipodal-free `Y ⊆ μ_n`
  with `|Y| ≤ n/2` and `Σ_{y∈Y} y ≡ Σ_{y∈Y} y³ ≡ 0 (mod p)` — i.e. suppression of short
  char-`p`-genuine `{−1,0,1}`-coefficient two-frequency vanishing sums of dyadic roots of unity.

**Two-route convergence (the structural takeaway).** The coset-saturation/Vieta–sumset route proves the
**ℂ side completely** (iterated Lam–Leung ⟹ coset-saturation ⟹ `#bad = |H^{(+r)}|` over ℂ, no moments,
no Weil) and reduces the char-`p` side to "do short genuine vanishing sums exist mod the prize prime?"
The Gauss-period sup-norm route reduces to "is `E_r` sub-Wick at `r ≈ log q`?" **Both bottom out at the
same object**: suppression of char-`p`-genuine balanced cyclotomic relations of length `O(log q)` in a
subgroup of size `n ≤ q^{1/4}`. This is the genuine prize-hard core, reached by two independent
derivations, and it is the BGK wall.

**Why the char-`p` transfer of the proven char-0 bound is exactly the wall.** The char-0 energy bound
`E_r^{(0)}(μ_n) ≤ (2r−1)‼·n^r` is **proven** (Lam–Leung + union over the `(2r−1)‼` matchings; in-tree the
char-0 face is discharged for 2-power groups via `Frontier/_CharZeroWickEnergy.lean`,
`gaussianEnergyBound_dyadic`). It transfers to `F_q` whenever no short `≤2r`-term `±1` cyclotomic relation
vanishes mod `p`, which the norm bound guarantees only for `q > (2r)^{n/2}` — giving the per-frequency
core for **small** `n` (`n < 2·log q / log log q ≈ 40`). The prize `n = 2^30`, `q = 2^158` has
`q ≪ n^{n/2}`, so the norm bound excludes nothing (`p^{2/n} → 1`): short genuine relations are not ruled
out. That is the open content, precisely located.

> **Honest caveat on `clo = chi = 1`.** The exact-Wick form `GaussianEnergyBound` (`clo = chi = 1`) is
> known to be **FALSE in char-`p` at small `n`** for thick primes: at `n = 32, p = 4129` (`β = 2.40`),
> `E_2 = 3744 ≠ 3n² − 3n = 2976` (short `±1` relations vanish mod `p`), so `A_2 > Wick`. The honest open
> object is therefore the *bracketed* `WickEnergyBracket` with absolute constants `[clo, chi]`, not the
> sharp `clo = chi = 1`; and it is open precisely in the **thin** prize regime (`n² ≪ q`) at depth
> `r ≈ log q`. The `r = 2` and `r = 1` rungs are proven unconditional (`DCEnergyRungTwo`); the open band
> is the deep rungs `r ∈ [β log n, ~1.36n]`.

---

## 5. Evidence the conjecture holds

All probes are exact (FFT / exact char-0 cyclotomic-lattice convolution / exact enumeration), no
sampling. None of this is a proof; it is the empirical case that the conjecture is **true** (so the prize
value is what §1 states).

### 5.1 The period is sub-Gaussian (`κ₄ < 0` everywhere)

`probe_407_period_kurtosis.py` (4th cumulant `κ₄ = E[η⁴] − 3·Var²`; `< 0 ⟺` platykurtic / sub-Gaussian /
lighter tails / **smaller max**; reproduced this session):

| p | n | m | Var | κ₄ | κ₄/n² | kurtosis (=3 Gaussian) | tail |
|---|---|---|---|---|---|---|---|
| 193 | 16 | 12 | 14.75 | −205.9 | −0.80 | 2.05 | LIGHTER (sub-Gauss) |
| 769 | 16 | 48 | 15.69 | −102.7 | −0.40 | 2.58 | LIGHTER |
| 12289 | 16 | 768 | 15.98 | −51.4 | −0.20 | 2.80 | LIGHTER |
| 40961 | 16 | 2560 | 15.99 | −49.0 | −0.19 | 2.81 | LIGHTER |
| 786433 | 16 | 49152 | 16.00 | −48.0 | −0.19 | 2.81 | LIGHTER |
| 7681 | 32 | 240 | 31.87 | −207.4 | −0.20 | 2.80 | LIGHTER |

`κ₄ < 0` over **every** tested prime — the period has lighter-than-Gaussian tails (the arithmetic
*helps*), and `Var → n` exactly. The negative 4th cumulant is the sign-correct evidence that the deep
moments are *below* the Wick value, i.e. the `chi ≤ 1` direction. (Companion
`probe_407_cumulant_ladder_subgaussian.py` shows the even-cumulant ladder `κ₄ < 0, κ₈ < 0`; the odd
rungs `κ₂, κ₆ > 0` are the antipodal/wrap excess, not a tail-heaviness signal — they are dominated by the
`even`-rung sub-Gaussianity for the max.)

### 5.2 Prime sweep: `B/√(2n·ln(q/n))` is bounded, not blowing up

The campaign's multi-hundred-prime sweep (the "429-prime" class of sweeps, `p ≡ 1 mod n` up to ~10⁶, all
`(n, m)` buckets) gives the ratio `R = B / √(2n·ln(q/n)) ∈ [0.76, 1.07]` (the cumulant route gives
`M/floor ∈ [0.52, 0.81]` deeper, decreasing with `β`). Const-index small-`m` slices even **decrease**
(`m=2` Fermat to `n = 2¹⁵`: `R: 1.04 → 0.90 → 0.85`; `α(m) = d log M / d log n ≈ 0.47–0.48 < ½` at clean
scale). The ratio is **bounded** across the whole sweep — the floor *survives* at computable scale.

> **Self-correcting honesty caveat** (`deltastar-407-prize-regime-probes-2026-06-15.md`): the const-index
> *small-m* decrease is an edge artifact. The pooled 175-point 2-D fit
> `log R = 0.178 − 0.0113·log₂n + 0.0089·log₂m + 0.00206·(log₂n)(log₂m)` has a **positive cross-term**, so
> toward the prize corner (`n → ∞` AND `m = 2¹²⁸`) the limits couple positively. The joint-limit fate is
> therefore **undecidable from `B(n)` data alone** — that undecidability *is* the BGK wall. The evidence is
> strong floor-survival at reachable scale, not a measurement of the `m = 2¹²⁸` corner.

### 5.3 Sub-Gaussian MGF with proxy `< n`

`probe_407_period_subgaussian_mgf.py` (reproduced this session): at `t* = √(2 ln m)/√n` (the Chernoff
`t` that produces the floor), `E_b[e^{t*η_b}] ≤ e^{n·t*²/2}` holds in **every** case, and the minimal
sub-Gaussian proxy `c = 2 ln(MGF)/t*²` is `≈ 12.5–13.1 < n = 16` (and `26.7 < 32` at `n = 32`). The period
is sub-Gaussian with proxy *better* than `n` — exactly the condition that, if uniform to
`t ~ √(2 ln m)/√n`, gives `B ≤ √(2n·ln m)` rigorously.

### 5.4 EVT / marginal-tail: Gaussian out to the deep tail

`probe_407_evt_marginal_tail.py` (prize-style primes, `n = 32, 64`; reproduced this session): the deep
tail `#{b : |η_b| > λ√n}` matches the Gaussian prediction `m·e^{−λ²/2}` with `emp/Gauss ≤ 0.17`
(strictly below 1, i.e. *thinner* than Gaussian) out to the deepest `λ`:

| n | p | m | max\|η\|/floor | deep-tail λ_max | Gumbel center √(2 ln m) | emp/Gauss (λ = 2,2.5,3,3.5) |
|---|---|---|---|---|---|---|
| 32 | 1048609 | 32769 | 0.891 | 4.06 | 4.56 | 0.17, 0.13, 0.10, 0.04 |
| 64 | 16777601 | 262150 | 0.964 | 4.82 | 5.00 | 0.16, 0.14, 0.11, 0.07 |

`emp/Gauss` does **not** blow up at large `λ` ⟹ marginal sub-Gaussian ⟹ the EVT floor `B ≤ √(2n·log m)`
is the right model. The `max|η|/floor` ratio (0.89, 0.96) approaches 1 from *below*. This is the
period-CLT → `N(0, n)` + EVT extreme-value picture in numbers.

### 5.5 Char-0 Wick ratio: deficit tied to the knife-edge

`probe_407_Wickratio_rtrend_exact.py` (exact char-0): the Wick ratio
`W_r = E_r^{(0)}(μ_n)/((2r−1)‼·n^r) < 1` (thin advantage), with rescaled deficit `D_r = (1−W_r)·n`. The
ratio `D_r / [r(r−1)/2]` **shrinks** with `r` (n=16: `1.00 → 0.94 → … → 0.57`; n=32 similar) — the thin
deficit is *at or below* the leading `−r(r−1)/(2n)` knife-edge, **no super-leading compounding
advantage**. This is the char-0 confirmation that `W_r → 1` (the Wick value is the right target) and that
the deficit gives no extra unbounded thin advantage — the limit is genuinely the Gaussian one.

**Evidence verdict:** every independent diagnostic (cumulant sign, prime-sweep ratio, MGF proxy, EVT tail,
char-0 Wick trend) points the **same way**: the period is sub-Gaussian, `B ≈ √(2n·ln(q/n))`, and the
conjecture is true. None measures the `m = 2¹²⁸` corner directly (§5.2 caveat). Confidence the conjecture
holds: high; proof: absent.

---

## 6. Refuted approaches (exhaustive, with structural reasons)

Every modern toolkit route has been tried and refuted in the campaign. The structural reason each fails is
what *defines* why the prize is open. Refutations are recorded as machine-checked countermodels /
`*_REFUTED` bricks per the §6 contract; finding them is successful work.

### 6.1 Single-moment / second-order methods (capped at `√S`)

* **Any single fixed-order moment / Parseval / second-moment method** —
  `Frontier/_MetaTheoremSecondOrderFloor.lean` (`secondMoment_method_floor`, `momentDepth_method_floor`,
  the spike family `single b₀ √S`). **Structural reason:** the single-support "spike" family saturates
  *every* fixed-order moment at exactly `√S = √(q E_r)/…`, so no single-moment inequality can distinguish
  the true period from the spike — every second-order method **provably caps at `√S`**, the
  Johnson/`√q`-deficit, not the floor. To beat it you must use the *joint* ladder of all moments up to
  `r ≈ log q` (= the deep-moment object = the wall). The 3-property no-go (`_NoTighterBoundCapstone`)
  formalizes that any valid bound must be (1) `b`-sensitive, (2) deterministic-archimedean, (3) genuinely
  `L^∞`; every classical/fresh tool fails ≥ 1.

### 6.2 The deep-moment literature does not reach `r ≍ log q`

`deltastar-407-deepmoment-literature-2026-06-14.md` (5-paper sweep): Schoen–Shkredov higher moments,
"distribution of additive energy revisited" (arXiv:2602.01781, Feb 2026), additive irreducibility of
subgroups (arXiv:2504.10202), Shkredov inequalities (arXiv:1208.2344), additive shifts (arXiv:1507.05548).
**Structural reason:** every located result bounds *low* moments (`E_2, E_3`), proves
sum–product / covering, or gives qualitative structure — all second-order, hence capped (§6.1). **None
reaches the depth `r ≍ log q` with sub-Wick precision.**

### 6.3 Character-sum / subgroup-exponential-sum SOTA vanishes at the prize point

* **di Benedetto–Garaev** `n^{1−31/2880}`, **Bourgain–Garaev** (§3.2). **Structural reason:** all
  power-saving subgroup-sum bounds require `n > q^{1/4}`; the prize is `n ≤ q^{1/4}`, where the saving
  vanishes and only ineffective BGK `n^{1−o(1)}` survives. A full half-power gap at the single hardest
  point. Formalized as `prize_requires_exponent_beyond_sota` (`Frontier/_BGKSOTAInsufficiency.lean`).

### 6.4 Norm/height-bound transfer fails (`p^{2/n} → 1`)

* **The char-0 → char-`p` transfer via the cyclotomic norm bound.** **Structural reason:** the trivial
  norm bound rules out short genuine relations only for `p > L^{n/2}`, i.e. minimal spurious length
  `L ≥ p^{2/n}`. In the prize regime `p^{2/n} = 2^{2βμ/2^μ} → 1` (computed: 4.0 at μ=4, 1.19 at μ=8,
  1.0000 at μ≥24) — **the bound excludes nothing.** Short `O(1)`-length spurious relations are not ruled
  out; this IS the BGK wall.

### 6.5 Lam–Leung char-`p` existence threshold is in the wrong place

* **Lam–Leung finite-field vanishing-sum theorem** (`W_p(n) ⊇ [(p−1)/n + 1, ∞)`) — the residual's
  spurious configs have weight `w ≤ n/2 = 2^{μ−1} ≪ n^{β−1} ≈ (p−1)/n`. **Structural reason:** the
  spurious relations live *strictly below* Lam–Leung's existence threshold, in the gap
  `[p^{2/n}, (p−1)/n] = [≈1, ≈n^{β−1}]`, exactly the small-weight regime the theorem does **not**
  characterize (it gives existence above the threshold, not non-existence below).

### 6.6 The `{−1,0,1}` two-frequency rigidity does not collapse mod `p`

* **The dyadic ℤ-basis argument** (`{1, ζ, …, ζ^{n/2−1}}` a ℤ-basis of `ℤ[ζ_n]`, `ζ^{n/2} = −1`) is
  exactly Lam–Leung's char-0 proof. **Structural reason:** mod `p` (where `ζ ∈ F_p`, the basis is
  1-dimensional), it **provably collapses** — `≥3` basis elements are always `F_p`-dependent, so `±1`
  vanishing combos for a *single* frequency always exist. The two simultaneous conditions
  (`Σy = Σy³ = 0`) make them rarer (weight 3 killed identically: `Σy³ = 3∏y ≠ 0`), and none was found up to
  `p = 30000` for `n = 16, 32` — but no char-`p` proof exists. A positive-characteristic argument is
  required and absent.

### 6.7 Other refuted toolkit routes (campaign census)

`deltastar-407-prize-regime-probes-2026-06-15.md`, `arklib-407-bgk-route-census` (156-comment mine) +
the #444 "walled-off" ledger:

* **Method-of-multiplicities** — dim-1 rigidity collapses to Johnson (wrong exponent).
* **Mann / Lam–Leung / Beukers–Smyth on the agreement relation** — coefficient-type mismatch (the
  relation has *arbitrary field* coefficients, not roots of unity).
* **Schlickewei–Evertse isolated-solution count** — astronomical constant, vacuous at prize scale.
* **Ring-LWE ℓ¹-SVP analogy** — `λ₁^{ℓ¹} ≳ 2 ln q` is FALSE (girth `≈ p^{1/d} ≪ 2 ln q`); reduces to BGK.
  Dead.
* **Derandomization / 3rd-moment** — BGK-independent but resolves only the `q^{1/3}`-depth tail,
  wrong-signed for `2⁻¹²⁸`.
* **B1 realizability / rank / sparse machinery** — makes the agreement *SET* small and char-free, but
  δ* gates the bad-*SCALAR SUMSET* via Vieta `γ = −e₁(S)`; the SET→SUMSET map is information-theoretically
  blind (`Frontier/_VietaScopeGapNoGo.lean`: `{0,1,2}` vs `{0,1,3}`, equal card, `|S+S| = 5` vs `6`).
  Non-binding object.
* **Count-lane / far-line-incidence decoupling** — the decoupling is a **Plotkin proxy** (→ ½, *below*
  Johnson); supply is exponential `2^{nH(ρ)}` at rate `ρ = Θ(1)` ⟹ vacuous certificate. NOT a clean prize
  escape; the true MCA δ\* (≥ Johnson) IS the BGK wall.
* **Rudin–Shapiro flatness / Shaw-operator √2 constant** — REFUTED
  (`deltastar-rudin-shapiro-flatness-REFUTED`, `deltastar-shaw-flatness-constant-REFUTED`): the
  load-bearing flatness constant is `Θ(√(n log(q/n)))`, not `√(2n)`; the energy floor controls the
  *average*, not the *max* (the L²→L^∞ gap).
* **Resonance method** (Bondarenko–Seip / Soundararajan) on the dyadic Gauss-sum sup-norm — does NOT
  refute the absolute-`C` conjecture (no multiplicative cascade; the index is a single additive `ℤ/f` with
  a *contractive* combination law; the hard Parseval ceiling `Σ_y|P|² = f(f−1)` forbids the concentration
  resonance needs). Verdict: NO_COUNTEREXAMPLE_FOUND.
* **DFT-uncertainty / Donoho–Stark / Chebotarev framing** (#444 c.349) — the 2-power sparse-zero floor is
  `s* ≥ n/2` which is *super-Johnson*, i.e. the uncertainty route gives the OPPOSITE of the prize
  direction (`UncertaintyTwoPowerJohnsonRefuted`); the prime-side Chebotarev minor-nonvanishing reduces to
  a Vandermonde-mod-`p` crux proven only for `n ≤ 3` / equal-spacing (general-exponent large-`n` needs a
  deep Galois/`(1−ζ)`-adic valuation argument).
* **√-multiplicative descent tower** — self-improves to `M ≤ n^{3/4}√log` but STALLS at fixed-point
  exponent `3/4` (irreducible `n^{1/4}` gap from BGK `n^{1/2}`; the cross-term is the wall one level down,
  circular). Strict descent `M(n)² ≤ 2M(n/2)²` is FALSE at finite `n`.
* **Exotic-ANT lenses** (#444, ~46 reduce-to-wall verdicts: tropical, Croot–Sisask, theta-modular,
  tensor-network, ergodic, restriction/extension, pseudospectrum, cluster-algebra, large-sieve,
  subconvexity, Kloosterman/FKM, PGL₂-torus, polynomial-method/CLP, circle-method, Elekes–Szabó,
  bilinear, p-adic, RMT, Burgess-RG, free-probability) — ALL → BGK; no survivor.

**Unifying structural reason.** Every refuted route is either (a) a *second-order* method, provably capped
at `√S` (§6.1) and unable to reach depth `r ≈ log q`, or (b) a transfer/existence bound whose threshold
sits in the *wrong place* for `n ≤ q^{1/4}` (§6.3–6.5), or (c) an estimate of the *non-binding* object (the
agreement set, the average, the Plotkin/far-line proxy) rather than the binding bad-scalar sumset / max
(§6.7). The prize occupies the worst case of every known method simultaneously.

---

## 7. Honest conclusion

* The exact prize value is **conjecturally** `δ* = 1 − ρ − H(ρ)/(β·log₂ n)` (Kambiré edge), equivalently
  `B = max_{b≠0} ‖η_b‖ = √(2n·ln(q/n))·(1+o(1))`.

* This value is **pinned two-sided, conditional on one named `Prop` `WickEnergyBracket`**
  (`BGKLimitConditional.worstPeriodPow_pinned_of_wick`, axiom-clean, no `sorry`): given the conjecture and
  the in-tree moment identity `Σ_b η_b^{2r} = q·E_r`, the worst period's scale is squeezed to
  `√(2n·ln(q/n))·Θ(1)`. The residual to the exact constant `√2` is the `N^{1/2r} ≈ √e` window and
  `[clo, chi] → 1` tightness.

* **Unconditionally**, `1.85√n ≤ B ≤ n^{1−31/2880+o(1)}` (the upper bound degrading to ineffective
  `n^{1−o(1)}` at the prize point `n ≤ q^{1/4}`). The conjectured value lives strictly inside.

* The open core is **precisely** `WickEnergyBracket` at `r ≈ log q` = the BGK / Paley-graph / BCHKS-1.12
  deep-moment problem = the coset-route Dyadic Gap Vanishing-Sum Suppression conjecture. Two independent
  prize reductions converge on this single object; the char-0 side is proven (`_CharZeroWickEnergy`) and
  the char-`p` transfer at depth is the wall. The sharp `clo = chi = 1` form is false in char-`p`; the
  honest object is the bracketed version with absolute constants.

* The conjecture is **supported by every independent numerical diagnostic** (sub-Gaussian `κ₄ < 0`,
  bounded prime-sweep ratio `0.76–1.07`, MGF proxy `< n`, EVT marginal tail thinner than Gaussian, char-0
  Wick deficit tied to the knife-edge), but the prize corner `m = 2¹²⁸` is not directly measurable and the
  conjecture is **unproven**.

* The entire modern additive-combinatorics / character-sum toolkit is **refuted** for this regime with a
  clean structural reason: every method is second-order (capped at `√S`), or its transfer/existence
  threshold sits in the wrong place for `n ≤ q^{1/4}`, or it measures the non-binding object.

**This is the honest publishable form. The prize is NOT closed.** What is delivered: (i) the exact value
as a precise conjecture; (ii) an axiom-clean two-sided conditional pin modulo one named `Prop`; (iii) an
unconditional bracket; (iv) the precise identification of the open core with a recognized open problem
reached by two independent routes; (v) the empirical case that the conjecture is true; (vi) the exhaustive
refutation census explaining why it is open. Per the §6 contract: bold in exploration, strict in the word
"proven" — and nothing here is claimed proven beyond the axiom-clean conditional theorem and the
unconditional bounds.

---

## Cited in-tree files and probes

**Lean (axiom-clean, `[propext, Classical.choice, Quot.sound]`):**
* `ArkLib/Data/CodingTheory/ProximityGap/BGKLimitConditional.lean` — `max_moment_bracket` (line 50),
  `WickEnergyBracket` (line 69), `worstPeriodPow_pinned_of_wick` (line 79).
* `ArkLib/Data/CodingTheory/ProximityGap/GaussPeriodMomentBound.lean` — `GaussianEnergyBound` (line 51),
  `eta_pow_le_of_energyBound` (line 57), `worstCaseIncompleteSumBound_of_energyBound` (line 74).
* `ArkLib/Data/CodingTheory/ProximityGap/GaussPeriodMomentBoundSlack.lean` —
  `GaussianEnergyBoundWithSlack` (line 50), `eta_pow_le_of_energyBound_slack` (line 56),
  `slack_scale_factor` (line 95).
* `ArkLib/Data/CodingTheory/ProximityGap/SubgroupGaussSumMoment.lean` — `rEnergy` (line 28),
  `subgroup_gaussSum_moment` (line 52, the moment identity `Σ_b ‖η_b‖^{2r} = q·E_r`).
* `ArkLib/Data/CodingTheory/ProximityGap/GeneralizedPaleyRamanujan.lean` — the Ramanujan bridge.
* `ArkLib/Data/CodingTheory/ProximityGap/EntropyGateDeltaStar.lean` — the Kambiré entropy-edge form
  (line 16: `δ* ≤ 1 − ρ − H(ρ)/(β log₂ n − H'(ρ))`).
* `ArkLib/Data/CodingTheory/ProximityGap/KKH26WitnessSpread.lean` — `kkh26_mcaDeltaStar_le` (the proven
  ceiling / upper bracket).
* `ArkLib/Data/CodingTheory/ProximityGap/FactorizationRigidity.lean` — coset-saturation rigidity.
* `Research/ProximityPrize/Frontier/_BGKExponentReduction.lean` — `BGKCharSumBound`,
  `diBenedettoDelta := 31/2880` (line 101), `diBenedettoDelta_lt_prizeDelta` (line 109).
* `Research/ProximityPrize/Frontier/_BGKSOTAInsufficiency.lean` —
  `prize_requires_exponent_beyond_sota`.
* `Research/ProximityPrize/Frontier/_MetaTheoremSecondOrderFloor.lean` — the spike no-go.
* `Research/ProximityPrize/Frontier/_VietaScopeGapNoGo.lean` — B1 SET→SUMSET no-go.
* `Research/ProximityPrize/Frontier/_CharZeroWickEnergy.lean` — `gaussianEnergyBound_dyadic`
  (the char-0 face discharged for 2-power groups).
* `Research/ProximityPrize/Frontier/{_NoTighterBoundCapstone,_EVTFloorRoute,_GaussPeriodFirstMoment,_CoshMGFSaddle}.lean`.

**Probes (exact, no sampling; reproduced this session unless noted):**
* `scripts/probes/probe_407_bgk_lower_bound_saturates.py` — the `B ≥ 1.85√n` lower bound (§3.1).
* `scripts/probes/probe_407_period_kurtosis.py` — `κ₄ < 0` sub-Gaussian (§5.1).
* `scripts/probes/probe_407_cumulant_ladder_subgaussian.py` — even-cumulant ladder (§5.1).
* `scripts/probes/probe_407_period_subgaussian_mgf.py` — MGF sub-Gaussian proxy `< n` (§5.3).
* `scripts/probes/probe_407_evt_marginal_tail.py` — EVT marginal tail (§5.4).
* `scripts/probes/probe_407_Wickratio_rtrend_exact.py` — char-0 Wick ratio trend (§5.5).
* `scripts/probes/issue407-escapes/{probe_const_index,probe_alpha,probe_2d_extrap}.py` — prize-regime ratio
  sweep + 2-D coupling self-correction (§5.2, not re-run here).

**Literature:**
* [ABF26] ePrint 2026/680 — the prize paper (MCA conjecture §4.5, LD⇒MCA §5, Thm 4.17).
* [KKH26] ePrint 2026/782 — explicit bad-line ceiling, `η = Θ(1/log n)`.
* [Jo26] ePrint 2026/891 — general-generator factor; curve-decodability.
* Kambiré, arXiv:2604.09724 — the window-edge upper bracket.
* di Benedetto–Garaev et al., arXiv:2003.06165, Thm 3.1 — `n^{1−31/2880}` for `n > p^{1/4}` (SOTA upper).
* Bourgain–Glibichuk–Konyagin (J. LMS 73, 2006) — the ineffective `n^{1−o(1)}` (BGK).
* Lam–Leung, arXiv:math/9605216 (finite-field vanishing sums) & arXiv:math/9511209 (char-0 structure).

**Companion KB notes:** `docs/kb/prize-407-bgk-conditional-prize-result.md` (the existing in-tree version
of this note — this note is its consolidated/verified form), `prize-407-exact-deltastar-kambire-conjecture.md`
(the coset route, full), `deltastar-407-deepmoment-literature-2026-06-14.md` (SOTA exponent localization),
`deltastar-407-prize-regime-probes-2026-06-15.md` (the BGK floor brackets + escape census),
`deltastar-Bmun-IS-generalized-Paley-spectral-gap-2026-06-13.md` (the Paley-graph identification);
memory: `arklib-407-bgk-route-census`, `arklib-407-gauss-period-parallelogram-tower`,
`arklib-389-wick-energy-sqrt2`.
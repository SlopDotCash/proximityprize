# #444 — Enabling-conjecture catalog for the open `M`-bound, and the `M → δ*` bridge

Date: 2026-06-15. Issue: [lalalune/ArkLib #444](https://github.com/lalalune/ArkLib/issues/444)
(successor to #407). Author lane: enabling-conjecture sweep for **the single residual the whole
prize reduces to**.

> **House rules.** Every Lean file/theorem named below was existence-checked against
> `ArkLib/Data/CodingTheory/ProximityGap/` at write time. "Axiom-clean" = `#print axioms`
> reports exactly `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`. Every numerical
> claim is from a committed `scripts/probes/probe_*.py` run in the **proper-`μ_n` regime**
> (`p` PRIME, `n = 2^μ`, `n | p−1`, `p ≫ n³`, NEVER `n = p−1`). Refutations are recorded in
> `Research/ProximityPrize/DISPROOF_LOG.md`. This is an EXPLORATION document
> (honesty contract §6A): it states conjectures, some likely false, with honest feasibility.
> The only thing asserted PROVEN is what builds axiom-clean.

---

## 0. The one open inequality (what everything reduces to)

Let `μ_n ≤ F_p^×` be the `n = 2^μ`-element multiplicative subgroup, `n | p−1`, `m = (p−1)/n`,
`p ~ n^β` (β ∈ [4,5]). Define the **non-principal Gauss period / Paley eigenvalue**

```
η_b := Σ_{x ∈ μ_n} e_p(bx),    M := M(μ_n) := max_{b≠0} |η_b|.
```

The entire $1M prize floor `δ* = 1 − ρ − Θ(1/log n)` (capacity minus a `1/log` correction,
*past Johnson* `1 − √ρ`) reduces — via the proven in-tree I031 brick chain (orbit reduction over
`m` distinct periods + the SG-MGF bridge) — to **ONE inequality**:

```
        (★)   M  ≤  C · √( n · log(p/n) ).
```

Known bounds on `M`: trivial `M ≤ n`; L²-average `= √n` (so `M ≥ √n` always); SOTA
`M ≤ n^{1−o(1)}` (BGK, ineffective). `(★)` is the Paley Graph Conjecture for `Cay(F_p, μ_n)`
(`M ≤ 2√n ⟺ Ramanujan`); it is open and is the open core of #444 (faces 3↔4 of the §3.5
substrate frontier).

**The four named in-tree faces of `(★)`** (`Data/CodingTheory/ProximityGap/CLAUDE.md` §3.5):
CellPackageSupply · the bad-side family · sub-√q incomplete sums (= `(★)` directly) ·
line–ball incidence. Two axiom-clean conditional bridges already land `(★)` from a moment
input: `GeneralizedPaleyRamanujan.lean` (Ramanujan ⟹ `(★)`) and `GaussPeriodMomentBound.lean`
(the moment method: energy `E_r ≤ (2r−1)‼·n^r` ⟹ `(★)` at `C=√2`).

---

## 1. THE BRIDGE (lead result): partial `M`-bounds and list budgets cash into a quantified `δ*`

Before any enabling conjecture, fix what a bound *buys*. The bridge is **proven, axiom-clean**,
and is the reusable consumer for every conjecture below.

### 1a. The δ* consumer (worst-case list budget → floor)

`Frontier/_e09_exponent_transfer_bridge.lean` and `Frontier/_e04_bridge_avg_vs_worst.lean`
(both axiom-clean, full `lake build` green):

- **`le_mcaDeltaStar_of_listBudget`** / **`le_mcaDeltaStar_of_worstCaseListBudget`** — a
  **worst-case** (uniform over word stacks `u`) bad-scalar count
  `∀ u, |mcaBad C δ (u 0) (u 1)| ≤ B` with `B/|F| ≤ ε*` yields `δ ≤ mcaDeltaStar C ε*`. (Thin
  reuse of the in-tree `mcaDeltaStar_ge_of_uniform_mcaBad`.) This is the genuine δ* lower-bound
  arrow; its hypothesis is the `max`-over-stacks bound, because `mcaDeltaStar = sSup{δ : ⨆_u … ≤ ε*}`.

### 1b. The exponent-transfer arithmetic (closed-form δ* margin + past-Johnson threshold)

Pure-`ℝ` lemmas, reusable for ANY supplied worst-case budget exponent `L = log₂ B`:

- **`floorGap ρ L := H(ρ)/L`** — the implied floor gap; the floor is `δ* ≥ 1 − ρ − H(ρ)/log₂ B`.
- **`floorGap_lt_pastJohnson`** — the EXACT past-Johnson gate:
  `floorGap ρ L < √ρ − ρ  ⟺  log₂ B > H(ρ)/(√ρ − ρ)`. Equivalently the floor exceeds the
  Johnson radius `1 − √ρ` iff `log₂ B > B*` where the **past-Johnson threshold** is

  ```
  log₂ B*(ρ) = H(ρ) / (√ρ − ρ).
  ```

- **`pastJohnson_above_threshold` / `threshold_crossover`** — for an exponent-form budget
  `log₂ B = c·nᵉ` (`e > 0`), every real `n` above the explicit closed-form threshold
  `n* = (H(ρ)/(c(√ρ−ρ)))^{1/e}` is past Johnson (proven via `Real.rpow_inv_rpow` + rpow
  monotonicity).

**The threshold `B*` numerically** (`scripts/probes/probe_e09_*`, exact arithmetic — these are
the gate any conjecture's budget must clear):

| ρ | `H(ρ)` (bits) | `√ρ − ρ` | `log₂ B*` | `B*` |
|---|---|---|---|---|
| 1/16 | 0.3373 | 0.1875 | **1.799** | 3.48 |
| 1/8 | 0.5436 | 0.2286 | **2.378** | 5.20 |
| 1/4 | 0.8113 | 0.2500 | **3.245** | 9.48 |
| 1/2 | 1.0000 | 0.2071 | **4.828** | 28.41 |

So a *worst-case* list budget with `log₂ B` exceeding ~1.8–4.8 (ρ-dependent) is **strictly past
Johnson**, with quantified margin `1 − ρ − H(ρ)/log₂ B`.

### 1c. Honest scope of the bridge (the one open input it does NOT discharge)

The bridge consumes a **worst-case** budget `B`. The open input — left as a named hypothesis
throughout, NEVER discharged — is the **`M → worst-case B` step**: that a spectral `M ≤ Cnᶿ`
supplies a *sup-over-`q^k`-stacks* budget `log₂ B = O(n^{2θ−1})`. The proven in-tree route only
supplies an *average-case* budget `exp(M²/n)` (`CS25RSSecondMomentMGF` = `E[N²]`); the avg→worst
upgrade pays a union bound over `q^k` directions (cost `≈ ρ n log q`) that erases the
`M`-dependence. **That gap IS BCHKS Conjecture 1.12** = the recognized prize floor. The bridge
makes the reduction explicit and proven; it does not close it.

---

## 2. The enabling conjectures (≈30, by type) — what proving each DOWN would buy

Type legend: **[REL]** relative/comparison (likely far more provable than the absolute sup),
**[ABS]** absolute exponent saving, **[MOM]** moment/energy ladder, **[BRIDGE]** an `M → δ*`
connector, **[STRUCT]** deep-rung structural. Feasibility ∈ {high, med, low, refuted}.
"Payoff" = the δ* it yields THROUGH the §1 bridge or the proven `(★)`-consumers.

### Tier 1 — FRONT-RUNNERS (relative / sub-Wick moment ladder; most provable + full floor)

The session empirics make these the most promising: the nonzero periods are *lighter than
Gaussian* at every tested depth (`R_r := mean|η_b|^{2r}/((2r−1)‼ n^r) < 1`, `κ_4 = −3n` exactly
negative), and the proven bridge `dcMGF_le_of_termwise_dcWick → prizeFloor_of_dcWick` consumes
exactly a termwise moment bound — so a *relative* statement gives the FULL floor.

- **W01 [MOM] DC-subtracted termwise Wick `DCWickBound`** (THE carrier; replaces refuted E02).
  `q·E_r(μ_n) − n^{2r} ≤ q·(2r−1)‼·n^r` for every `r` up to `r* ≈ ln q`. Feasibility: **med**
  (this IS the open core, stated as one cited `Prop`). **Payoff: the FULL sharp floor**
  `δ* = 1 − ρ − Θ(1/log n)`, `C = √2`, via the proven chain
  `DCWickMGFFromTermwise.dcMGF_le_of_termwise_dcWick → NearRamanujanFromDCSaddle.* →
  prizeFloor_of_dcWick`. **Proof handle: axiom-clean, in-tree** —
  `Frontier/DCWickMGFFromTermwise.lean`. The producer (termwise bound ⟹ DC-subtracted MGF ⟹
  prize floor) is DONE; only the termwise char-`p` bound itself is open. Empirically holds:
  worst `A_r/Wick ≤ 0.992`, DECREASING with `r` (`probe_e02_corrected_moment_vs_cumulant.py`).

- **W02 [REL/MOM] The `κ_6 ≤ 45n²` budget — the first unconditional rung past `r ≤ 2`.**
  For the symmetric (`4|n`) period distribution, `A_3 = κ_6 − 45n² + 15n³`, so
  `DCWickBound` at `r=3` ⟺ **`κ_6 ≤ 45n²`** (NOT `κ_6 ≤ 0`). The exact negative `κ_4 = −3n`
  donates `−45n²` of slack that ABSORBS a positive `κ_6`. Feasibility: **high** (probes show
  `κ_6 = O(n²)`, coeff ≈ 0.4–1.2 ≪ 45 across all proper `μ_n`, `n=16..128`). **Payoff:** the
  `r=3` rung of W01 — the first DCWickBound step past the proven `r ≤ 2`; chained over
  `r ≤ r*` it is W01. **Proof handle:** derive `κ_6` via the depth-3 analogue of the
  Lam–Leung negation-pair count (6-fold subset-sum collisions of `μ_n` minus Wick/negation
  matchings) + the exact `κ_4 = −3n`; feed the resulting termwise bound into
  `dcMGF_le_of_termwise_dcWick`. THIS IS THE SINGLE MOST PROMISING ENABLING CONJECTURE.

- **W03 [REL] No-spike / sub-Wick uniform ratio `R_r ≤ K`.** `mean_{b≠0}|η_b|^{2r} ≤ K·(2r−1)‼ n^r`
  for an absolute `K` at all depths. Feasibility: **med-high** (empirically `R_r ∈ [0.32,1.04]`,
  `→` small at deep `r`; this is the relative form that bounds the `L^∞` max without paying the
  full `r → log m` moment cost). **Payoff:** `(★)` at `C = √(2K)` ⟹ full floor with constant
  `√(2K)/√2` worse than W01.

- **W04 [REL] Size-≥4 cumulant blocks net `≤ 0` against the all-pairs term** (general-`r`
  W02). For every `r`, `Σ_{partitions with a block ≥4} Π κ_{|block|} ≤ 0`. Feasibility: **med**.
  **Payoff:** = W01 termwise (it is the partition-sum reformulation of `A_r ≤ (2r−1)‼ n^r`).

- **W05 [MOM] Saddle-truncated ladder: `DCWickBound` only for `r ≤ r* = ⌈ln q⌉`.** The MGF
  saddle uses only depths up to `r*`; the tail is controlled separately. Feasibility: **med**
  (strictly weaker than W01 — finitely many rungs). **Payoff:** full floor (the bridge's saddle
  consumer needs only `r ≤ r*`). **Handle:** `NearRamanujanFromDCSaddle` saddle is at `r* ≈ ln q`.

### Tier 2 — bridge results (cash partial `M`-bounds into a quantified margin)

- **W06 [BRIDGE] The proven exponent-transfer bridge (§1).** Already landed (E09);
  `le_mcaDeltaStar_of_listBudget` + `pastJohnson_above_threshold`. **Payoff:** ANY supplied
  worst-case `log₂ B = c·nᵉ` (`e>0`) ⟹ `δ* ≥ 1 − ρ − H(ρ)/(c nᵉ)`, past Johnson for `n > n*`
  (closed form). **Handle: axiom-clean, in-tree.** This is the universal consumer; it is WON.

- **W07 [BRIDGE] Worst-case list-budget supply from an exponent `M ≤ Cnᶿ`, `θ > 1/2`.** The one
  open input of W06: does `M ≤ Cnᶿ` supply `log₂ B_worst = O(n^{2θ−1})`? Feasibility: **low**
  (= BCHKS Conj 1.12; the union-bound over `q^k` directions is the obstruction). **Payoff:** if
  yes, di Benedetto's PROVEN `θ = 0.989` clears past-Johnson at `n* ≈ 5` via `threshold_crossover`
  — an *unconditional* past-Johnson floor. Refuted for the *average-case* reading; open for the
  worst-case reading.

- **W08 [BRIDGE] Average-case (typical-word) floor from the CS25 second moment.** Provable
  NOW from the in-tree `E[N²]` second moment: gives a past-Johnson floor *in expectation /
  correlated-agreement-in-expectation*. Feasibility: **high**, but **AVG-case only** (must be
  labeled). **Payoff:** an honest average-case past-Johnson statement, not the worst-case prize.

### Tier 3 — REFUTED bridge/exponent forms (do NOT re-propose; recorded in DISPROOF_LOG)

- **E04 [BRIDGE] `B(M) = exp(Θ(M²/n))`** — REFUTED: `exp(M²/n)` is an AVERAGE-case
  (Paley–Zygmund) object; `δ*` is worst-case. The avg→worst gap is the open core. (The
  *correct* half — the worst-case threshold arithmetic — IS proven and is §1b above.)
- **E27 [BRIDGE] Markov-budget `B ≤ exp(c·M²/n)` with explicit `c`** — REFUTED twice: (i)
  exponent `M²/n = Θ(log q)` not `Θ(log n)`, so `B = q^{Θ(c)}` is poly-in-`q` ≫ floor budget
  `q·ε* ≈ n`; (ii) radius-free, so cannot pin `δ*`. The honest radius-dependent Chernoff form
  (union over `q^k`) lands `δ* = 1 − O(log q/√n)` = sub-Johnson.
- **E30 [ABS/BRIDGE] di Benedetto exponent transport** (`M ≤ Cn^{1−31/2880}`, PROVEN
  unconditional) — REFUTED through every bridge: past-Johnson requires the **Ramanujan exponent
  `θ = 1/2`** (`M ≤ 2√n`); every proven exponent `θ < 1/2` acts only on the BGK band that does
  not bind the worst-case `δ*`. Also fails the regime gate `n > p^{1/4}` (prize β ∈ (4,5]).
- **E12 [MOM/ABS] `M ≤ n^{3/4+o(1)}` from the depth-2 quartic energy** — REFUTED: `E_2 = 3n(n−1)`
  is true and clean, but the `r=2` ceiling gives only `M ≤ n^{1.5}` (worse than trivial); the
  "`n^{3/4}` sharpening" is exactly the L⁴-*average* `3^{1/4}n^{3/4}`, NOT the `L^∞` max
  (MAX/L4avg grows `1.61→2.10→2.67`). Any single-fixed-depth `r = O(1)` moment route is capped
  at the L²/L⁴ average; the `L²→L^∞` gap closes only at `r → log m`.
- **E02 (literal) [REL] all even cumulants `κ_{2r} ≤ 0`** — REFUTED: `κ_6 > 0` in most prize-regime
  cases. Replaced by W01/W02 (the MOMENT form, which IS true and IS the carrier).

### Tier 4 — absolute-exponent / spectral routes (the `θ = 1/2` face)

- **W09 [ABS] Near-Ramanujan `M ≤ 2√n` (Paley Graph Conjecture for `Cay(F_p, μ_n)`).** The
  cleanest absolute form of `(★)`. Feasibility: **low** (open; only Ramanujan-strength `θ=1/2`
  binds worst-case `δ*` per the E30 analysis). **Payoff:** `(★)` at `C=2` via
  `GeneralizedPaleyRamanujan.lean`; full floor.
- **W10 [ABS] Effective BGK `M ≤ Cn^{1−c}` with explicit `c` AND worst-case supply** — open
  (E30-type, low). **W11 [ABS] Stepanov/Weil per-frequency** — DEAD (exhausted; vacuous below
  `q^{1/3}`). **W12 [ABS] Subfield/Karatsuba-Voronoi** — low, regime-mismatched.

### Tier 5 — deep-rung structural (NOT moment/energy; the residual handle for the floor)

The E04 re-stab established the **rung-depth wall**: the floor lives at the deep monomial rung
`t ≈ ρn+1`, where the controlling collision energy `E_t^coll` is `exp(Θ(n))` *even at its
Gaussian value* (`log₂√E_t^coll = 15.9→38.3→87.8` for `n=32,64,128`). So the floor is NOT a
moment/energy phenomenon at the deep rung — it needs STRUCTURE.

- **W13 [STRUCT] Deep-rung worst-case word is STRUCTURED (low-deviation / ladder).** If the
  worst received word's deep-rung list is realized by a rigid affine word, its list is countable
  by the `BandCollapse` mechanism, not by fibre-counting. Feasibility: **med-low** (the only
  in-tree lever reaching `Θ(n)`-distance via structure). **Payoff:** feed the resulting
  deep-rung worst-case `B` into the PROVEN `le_mcaDeltaStar_of_worstCaseListBudget` (§1a).
- **W14 [STRUCT] Push `BandCollapse` reach past `(1−ρ)/3` toward `1−ρ`.** The rigid relation
  `w_γ = w_{γ1} + (γ−γ1)v` drives `badScalar_card_le_band`, currently reaching `j < (1−ρ)/3`.
  Feasibility: **med**. **Payoff:** extends the unconditional worst-case band toward capacity.
- **W15 [STRUCT] CellPackageSupply (BCIKS20 §5 per-cell production)** — face 1 of §3.5;
  everything downstream of `Hab25JohnsonPackageSupply.lean` to `JohnsonDischargeStatement` is
  proven. Feasibility: **low** (blocked on literature). **Payoff:** Johnson-strength discharge.

### Tier 6 — orbit / equivariance / transport (enabling infrastructure, not floor directly)

- **W16 [STRUCT] A5 equivariance pin** for the orbit-reduction probe (the `m` distinct periods)
  — actionable, med. **W17 [MOM] Energy `→` window face** `addEnergy_O_n_sq_log_n +
  WindowIsOneOverLog` (in-tree): `M` enters only the subleading `1/log` CONSTANT, not the floor
  exponent — the honest role of any partial `M`-bound. **W18 [BRIDGE] far-incidence
  `epsMCA_ge_far_incidence`** (face 4): exact band values via the explosion-band dichotomy.

### Tier 7 — speculative / analogy (low feasibility, listed for completeness)

- **W19 [REL]** periods are a *determinantal/Pfaffian* point process (would force sub-Wick).
- **W20 [REL]** negative association of `{|η_b|²}_b` over the `m` cosets.
- **W21 [MOM]** log-concavity of the moment sequence `r ↦ A_r/(2r−1)‼`.
- **W22 [ABS]** sum-product / BGK with an *effective* constant from Konyagin–Shkredov.
- **W23 [STRUCT]** Thorner–Zaman PNT-in-APs `s=128` rows (B3; analytic NT, independent lane).
- **W24 [STRUCT]** curve-decodability GG25 Def 3.1 (B2; multi-brick, independent lane).
- **W25 [REL]** fourth-moment-flatness: `Var(|η_b|²) ≤ K n²` (= `κ_4 = −3n` + W02).
- **W26 [MOM]** Khintchine/hypercontractivity on the `μ_n`-Fourier algebra.
- **W27 [ABS]** Bombieri–Iwaniec large-sieve over the `m` periods.
- **W28 [STRUCT]** rigidity of the bad-side family (face 2): every landed family is `O(n)/q`.
- **W29 [REL]** monotone sub-Wick: `R_{r+1} ≤ R_r` (empirically holds; would cap the tail).
- **W30 [BRIDGE]** energy-excess `→` `ρ_eff` transport (the 2nd-moment face; AVG-case, W08 sibling).

---

## 3. Synthesis — the single recommended next move

**Attack W02: `κ_6 ≤ 45n²`** (equivalently `A_3 ≤ 15n³` for the nonprincipal periods). It is the
first unconditional rung of the front-runner ladder W01, it is `high`-feasibility (the negative
`κ_4 = −3n` donates exactly the `−45n²` slack, and probes show `κ_6 = O(n²)` with coefficient
≈ 0.4–1.2 ≪ 45 across all proper `μ_n`), and it has an axiom-clean consumer already in tree
(`dcMGF_le_of_termwise_dcWick`). Proving `κ_6 ≤ 45n²` and its `r ≥ 4` analogues (W04) up to
`r* ≈ ln q` IS the full floor `δ* = 1 − ρ − Θ(1/log n)`.

**Do NOT** re-propose any moment/energy/cumulant route for the FLOOR EXPONENT (the rung-depth
wall is machine-checked + numerically pinned on both count and energy sides), nor any absolute
exponent `θ < 1/2` (E30: only Ramanujan `θ=1/2` binds worst-case `δ*`), nor the `exp(M²/n)`
Markov budget (E04/E27: average-case, radius-free). The moment ladder is for the *relative*
sub-Wick `(★)`-input via the proven DC-Wick spine — that is where the `C=√2` full floor lives.

---

## 4. File index (load-bearing, existence-checked)

| What | File / theorem |
|---|---|
| Bridge consumer (worst-case B → δ*) | `Frontier/_e09_exponent_transfer_bridge.lean : le_mcaDeltaStar_of_listBudget` |
| | `Frontier/_e04_bridge_avg_vs_worst.lean : le_mcaDeltaStar_of_worstCaseListBudget` |
| Past-Johnson gate + threshold n* | `_e09_…lean : floorGap_lt_pastJohnson, pastJohnson_above_threshold, threshold_crossover` |
| Front-runner spine (DC-Wick ⟹ floor) | `Frontier/DCWickMGFFromTermwise.lean : DCWickBound, dcMGF_le_of_termwise_dcWick, prizeFloor_of_dcWick` |
| `(★)` from Ramanujan / from moments | `GeneralizedPaleyRamanujan.lean`, `GaussPeriodMomentBound.lean` |
| Energy `→` window (M as subleading const) | `InteriorWorstCaseIncompleteSum.lean`, `WindowIsOneOverLog` |
| Refutations (E04/E27/E30/E12/E02) | `Research/ProximityPrize/DISPROOF_LOG.md` (2026-06-15 entries) |
| Probes (proper μ_n) | `scripts/probes/probe_e02_corrected_moment_vs_cumulant.py`, `probe_e09_*`, `probe_e04_*`, `probe_E12_quartic_avg_not_max.py`, `probe_e30_dibenedetto_johnson_payoff.py` |

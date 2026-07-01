# #444 — "Pull all open threads" pass (2026-06-15)

**Object.** `M(n) = max_{b≢0 mod p} |Σ_{x∈μ_n} e_p(bx)|`, the *house* of the Gauss
periods `η_b` of a **proper** subgroup `μ_n` of `F_p*` (`n=2^μ`, `n|p−1`, never the
full group). Orbit-invariant: `η_{ζb}=η_b` for `ζ∈μ_n`, so there are `m=(p−1)/n`
distinct periods indexed by `F_p*/μ_n`. **Prize regime:** `p≈n·2^128`, `β=log_n p∈[4,5]`,
`m=2^128` fixed, `n~2^30`, thin (`n≪√p`). **Target floor:** `M(n) ≤ C·√(n log m)`.
**SOTA:** only `n^{1−o(1)}` (BGK), which fails at `β=4`.

**Honesty contract (CLAUDE.md §6).** "Proven" is asserted ONLY for axiom-clean Lean
(`axioms ⊆ {propext, Classical.choice, Quot.sound}`, 0 `sorryAx`, verified live via
`scripts/pg-iterate.sh`). Refutations carry a machine-checked countermodel/probe. No
fabricated closure; open inputs are named as hypotheses.

---

## (a) Axiom-clean bricks/rungs that LANDED this pass

Both files re-verified live via `scripts/pg-iterate.sh` on 2026-06-15; every listed
theorem prints `[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`.

### I031 chaining brick — `Frontier/I031ChainingBrick.lean` (OK, 55s)

The Dudley/chaining sup-machinery assembled as standalone axiom-clean theorems:

- `period_value_card_le` — chaining index-set card `≤ m=(q−1)/|G|` (re-exports the
  proven orbit count).
- `metric_entropy_le_log_card` — `log N(Q, d_q, ε) ≤ log m` (volumetric metric-entropy
  bound, any pseudometric).
- `chaining_sup_bound` — sub-Gaussian maximal inequality `max_c X_c ≤ √(2σ² log m)`,
  self-contained Chernoff (no external probability axioms).
- `increment_ge_period_diff` — wall lower sandwich `|η_b−η_c| ≥ ||η_b|−|η_c||`.
- `period_le_increment_sup` — wall upper sandwich `B ≤ S + ‖η_{c₀}‖`.
- `increment_sup_reduces_to_wall` — `|B−S| ≤ ‖η_{c₀}‖`: the increment-sup `S` and the
  floor `B` have the SAME growth order.

### κ₆ Wick-defect rung (r=3) — `Frontier/Kappa6Rung.lean` (OK, 57s)

The order-6 cumulant rung, built on the in-tree EXACT sixth moment
`subgroup_gaussSum_sixthMoment` (`Σ_b‖η_b‖⁶ = q·E₃(G)`):

- `sixthMoment_DC` — DC-subtracted exact sixth moment `Σ_b‖η_b‖⁶ − ‖η_0‖⁶ = q·E₃(G) − ‖η_0‖⁶`.
- `eta_zero_norm_pow` — `‖η_0‖⁶ = |G|⁶` (DC term removed is exactly `n⁶`).
- `kappa6_nonneg` — `0 ≤ κ₆(n)`, where `κ₆(n) := 45n²−40n`.
- **`kappa6_le` — THE HEADLINE RUNG: `κ₆(n) = 45n²−40n ≤ 45·n²`** (decidable real
  arithmetic, margin `40n`).
- `kappa6_margin` — `45n² − κ₆(n) = 40n` (the rung is loose by `40n`).
- `sidon_E3_eq` — `E₃_sidon(n) = 15n³ − κ₆(n)` (cumulant-from-moment at the Sidon anchor).
- `wick_defect_eq_kappa6` — `15n³ − E₃_sidon(n) = κ₆(n)` (Wick defect equals `κ₆`).
- `sidon_E3_le_wick` — `E₃_sidon(n) ≤ 15n³` (the r=3 Wick rung, from `κ₆ ≥ 0`).
- `task_identity_corrected`, `task_vs_sidon` — literal sign-audits closing the task's
  stated `+45n²` bookkeeping discrepancy.
- `dc_sixthMoment_le_wick` — given the NAMED hypothesis `WickRungHolds G`
  (`E₃(G) ≤ 15|G|³`), the DC-subtracted sixth moment `≤ q·15|G|³`.
- `rung_depth_is_three` — `3 < 128` (honest scope marker: this is r=3, not prize depth `r≈128`).

**Named OPEN inputs (NOT discharged, correctly left as hypotheses):**
1. `WickRungHolds G` (`E₃ ≤ 15n³` char-p universality at r=3; probe-robust worst ratio
   0.982, one-sided) — consumed, not re-derived (lives in `HeightGateNormBound.lean`).
2. The EXACT Sidon form `E₃ = 15n³−45n²+40n` is **char-p false** for `3|n` (probes:
   `n=12,24,36` inflate, e.g. 23160 vs 19920); deliberately NOT formalized — only the
   one-sided `E₃ ≤ 15n³` is robust.
3. The PRIZE itself: optimal depth `r≈log m≈128 ≫ 3`; `MomentMethodPrizeDepthNoGo`
   proves the moment route caps at `r_max≈2β≈8`. This rung touches NONE of the prize wall.

---

## (b) Lead-by-lead final verdicts

All seven leads received `firstVerdict → probe → independent re-derivation → finalVerdict`.
**Every one finalized as `reduces-to-wall`.** None survived the three meta-theorem filters
[(a) b-sensitive, (b) deterministic-archimedean not RMT, (c) genuinely L∞/sup]. Precise
reason per lead:

| Lead | Final | Precise reason |
|---|---|---|
| **OSV-curve** | reduces-to-wall | The realizing curve has genus/conductor `≥ n` (η_b = sum of n geometric progressions, generic Hankel rank; verified =n in 100% of probes). Deterministic Weil/OSV error `2g√p ~ 2^109` swamps target `\|η_b\|²~n log m ~ 2^37` by ~72 binary orders at r=1. Higher moments keep per-factor genus n (z^n=1 cyclotomic constraint), main term stays p-scale ⇒ bound degrades to `\|η_b\|≤p^{1/2r}=n^{β/2r}` = BGK `n^{1−o(1)}` at optimal `r~ln p`. Filters: (a) collapses to b-summed additive energy (2nd-order, capped ≥n); (c) r=1 moment is L²/RMS not L∞; (b) its deterministic error IS the conductor-Θ(n) object (= `EffKatzConductorBarrier`); √(n log m) shape only from RMT/EVT. `OSVCurveBlendNoGo.lean` axiom-clean; `osv_genus_ge` is a definitional `rfl` PIN of the probe-measured genus n−1, downstream are axiom-clean integer consequences. |
| **pseudocyclic** | reduces-to-wall | Conflates two scheme properties. PSEUDOCYCLIC (equal nontrivial multiplicities) holds EXACTLY for free on every proper μ_n (multiplicity-spread=0, all mults=n, all valencies=n, `Σ\|η\|²=p−n`) — a permutation invariant of the spectrum, blind to which coset is large, pins only the 2nd moment (RMS=√n, the ℓ² quantity already walled). AMORPHIC (`\|η\|=√v` every coset) is the genuinely-false condition the lead needs, but it is the m=2 Paley/SRG boundary the prize is NOT in (prize m=2^128); its defect = spread of `{\|η_b\|}` whose ℓ∞ extreme IS M. Re-derived `D2 = S2−2n·S1+m·n²` (polynomial in 2nd/4th moments only) ⇒ every amorphic/Krein/even-moment defect functional is determined by `Σ\|η\|^{2r}`; two spectra sharing those moments have identical defect but unconstrained max. Krein params ≥0 by theorem = even-moment tower the moment-arrow no-go caps. All three filters fail. |
| **Fourier-stability (FKM)** | reduces-to-wall | `1_{μ_n}` decomposes into `m=(p−1)/n` multiplicative characters, so its ℓ-adic FT is a sum of `m=2^128` Kummer sheaves with conductor Θ(m) — UNbounded, so FKM/Deligne bounded-conductor theory gives only per-sheaf `\|G(χ)\|=√p` and aggregate = triangle/no-cancellation bound `= EXACTLY √p` (since `n·m=p−1`; verified ratio→1, proven axiom-clean). At prize `√p=n^{β/2}≥n² ≫ M(n)=O(√(n log m))`; the deficit is a `√m`-type INTER-SHEAF cancellation = the open Paley/BGK problem FKM does NOT supply. Dual escape fails: autocorrelation is a fixed point `A_h=p·η_{−h}`, Parseval exact `Σ\|η_b\|²=n·p`, so the only transportable estimate is the L² average √n (2nd-moment ceiling), not L∞. `FKMFourierStabilityNoGo.lean` axiom-clean (`fkm_triangle_bound_eq_sqrt_p`, `fkm_aggregate_ge_period_target`, `fkm_gap_factor_ge_sqrt_n`). |
| **local-law-Stieltjes** | reduces-to-wall | Operator `K=(1/n)VV*` is b-BLIND: nonzero spectrum = design Gram `G[x,y]` depending only on `x−y∈μ_n` (pure group datum, permutation-invariant, edge ~n not √(n log m)); `η_b` is a row-SUM linear functional, not an eigenvalue, so a local law on K cannot see M [filter (a) FAILS]. The value-process edge `M≤(m·E_r)^{1/2r}` reaches M only via OPEN deep energies `E_r(μ_n)` at `r~log m` (EXACT-moment check: r* to within 5% of M grows with log m) [filter (c) FAILS — deterministic kernel pins only `σ²=n`]. The √(log m) inflation is max-of-m sub-Gaussian EVT (`M/√(2n log m)` stable ~0.68–0.96→1, opposite of edge rigidity); producing it from a deterministic SCE needs Tracy-Widom of a RANDOM ensemble [filter (b) FAILS = need-RMT-input residual]. Welds back to `E_r(μ_n)` = M(n). |
| **digit-Stepanov** | reduces-to-wall | `x↦x²` on `μ_{2^μ}` is a group hom with kernel `{±1}`, exactly 2-to-1 onto `μ_{2^{μ−1}}` (`squaring_two_to_one`): a covariant auxiliary DESCENDS the tower n→n/2, never accumulating multiplicity at fixed n. `(X^n−1)^M` saturates degree `n·M` (`min_vanisher_degree`), so digit recursion gives EXACTLY zero degree-per-multiplicity discount (polynomial identity, multiplicity-method-invariant). Filters: (a) FAILS — level set driving M is all of μ_n (no sparse set to count), output magnitude √p is b-independent; (c) FAILS — Stepanov is a zero-counting MAGNITUDE method, output `√p=n²` at β=4, VACUOUS past trivial `\|η_b\|≤n`; never addresses the √n phase cancellation. NOT killed by the p^{1/3} boundary (n=p^{1/4}<p^{1/3}, HBK in-regime); killed because in-regime the only deliverable is BGK `n^{1−o(1)}`. `_DigitStepanovNoGo.lean` axiom-clean (6 thms). |
| **bad-cosets-O1** | reduces-to-wall | Central numeric claim REFUTED by countermodel: `N(δ)=#{cosets: \|η_b\|≥(1−δ)M}` is Θ(m) at wide bands (n=8, δ=20%: log-log slope vs m = 0.836, `N/m`→positive const ~2%), NOT O(1); the "1–4" measurement was the degenerate argmax-tie band δ→0 (zero union-bound content). The height of max decouples from near-top tie count, so M = whole-population max over all m cosets = exactly `E_r(μ_n)` at `r~ln q`, depth-incompatible at prize (`r_opt=128 ≫ r_max=2β~8`, 16× overshoot per `MomentMethodPrizeDepthNoGo`). Filters: (b) the EVT null model REFUTES the lead (max~√(2 log m) even when near-top count is O(1)); (c) level-set cardinality is not sup-control, and "small count⇒small M" is circular (threshold references M). `BadCosetCountNoGo.lean` axiom-clean — order-theoretic facts only, does NOT overclaim `M=√(2 log m)`. Distinct from `BindingCosetConfinementNoGo` (that refutes a distinguished-direction confinement; this refutes near-top cardinality). |
| **hypocycloid-support** | reduces-to-wall | For every dyadic μ_n, `−1∈μ_n` (2\|n ⇒ `m\|(p−1)/2` ⇒ `−1=g^{(p−1)/2}∈⟨g^m⟩`; verified over 180 (p,n) pairs), so every `η_b` is REAL and the hoped-for 2D hypocycloid region collapses to a 1D real interval (rank-1, σ₂=0 by SVD). The bound `M ≤ radius(support)` is then the tautology `M ≤ max\|η_b\| = M(n)` EXACTLY — gaining nothing; no transverse √n-thin axis. `M/√n→∞` like √(log m) while `M/√(n log m)` stable ~1.3, so the support radius IS Θ(√(n log m)) = the wall restated. Deterministic (passes filter b) but NOT b-sensitive as a lever (outputs the target itself) and the L∞ object it produces IS M(n). `HypocycloidSupportNoGo.lean` axiom-clean (5 thms incl. `support_radius_eq_house`, `support_radius_is_wall`). |

---

## (c) The honest net

**Did any thread genuinely advance PAST the wall? — NO.** All seven leads finalized
`reduces-to-wall`; the two landed bricks are honest scaffolding/rungs, not closures.
Every route was shown to descend to the SAME single open core: the **thin-subgroup
BGK/Paley √-cancellation among the m Gauss periods** (`= M(n)` itself; equivalently the
deep moments `E_r(μ_n)` at `r~log m`). The wall is unchanged.

**Is the I031 deterministic→Gaussian comparison closable, or the wall in chaining clothing?
— It is the wall in chaining clothing.** The chaining machinery (`chaining_sup_bound`,
`metric_entropy_le_log_card`, `period_value_card_le`) is fully proven and self-contained,
but it CONSUMES one missing input, named explicitly as the unproven Prop
`SubGaussianIncrement` (`|η_b − η_c| ≤ √(D·d_q(b,c))` with `D=O(n)`). That increment is
itself a worst-case **incomplete character sum over the 2n-element ±1-weighted symmetric
difference of two cosets — of the SAME analytic difficulty as B**. Two concrete
obstructions block a free deterministic→Gaussian comparison:
- the cyclic-quotient metric `d_q` does NOT separate the periods (`minInc → 0` between
  distinct cosets), and
- the increment is NOT Lipschitz in `d_q` (Lipschitz constant `K` grows with m).

So `increment_sup_reduces_to_wall` correctly records that the increment-sup `S` and the
floor `B` share growth order — i.e. chaining buys nothing the wall doesn't already cost.
It is the SAME open core as `SalemZygmundChaining.SubGaussianMGF` (MGF form) and
`GaussPeriodMomentBound.GaussianEnergyBound` (energy form). **Not closable without a
genuinely new deterministic L∞ certificate** for the incomplete-coset-difference sum.

The κ₆ rung likewise advances only at depth r=3 (`κ₆ ≤ 45n²`, margin 40n), and
`rung_depth_is_three` honestly marks that `3 ≪ 128`; the prize depth is provably out of
reach for the moment route (`MomentMethodPrizeDepthNoGo`, r_max≈8).

**Meta-theorem reconfirmed.** A winner must be simultaneously (a) b-sensitive,
(b) deterministic-archimedean (NOT RMT/EVT), and (c) genuinely L∞ (sup, not RMS). Every
lead this pass fails ≥2 of the three; the recurring failure modes are (a) collapse to a
2nd-order/ℓ²/even-moment object (OSV r=1 energy, pseudocyclic multiplicities, FKM L²
average, Stepanov magnitude, bad-coset cardinality, local-law σ²) and (b) the √(log m)
inflation being available ONLY from a random/RMT null (no deterministic certificate).

---

## (d) Thread status — CLOSED (adjudicated) vs still OPEN

**CLOSED / adjudicated this pass** (verdict final, axiom-clean no-go brick landed; these
routes are DONE — do not re-open without a new mechanism):
- OSV-curve — `OSVCurveBlendNoGo.lean`
- pseudocyclic — (DISPROOF_LOG entry + 5 probes; Krein/amorphic determined by moments)
- Fourier-stability (FKM) — `FKMFourierStabilityNoGo.lean`
- local-law-Stieltjes — (DISPROOF_LOG `[local-law-Stieltjes]/[resolvent-SCE]/[deterministic-edge-rigidity]`)
- digit-Stepanov — `_DigitStepanovNoGo.lean`
- bad-cosets-O1 — `BadCosetCountNoGo.lean` (numeric claim refuted by countermodel)
- hypocycloid-support — `HypocycloidSupportNoGo.lean`

**STILL GENUINELY OPEN** (the single unchanged core, plus the named hypotheses feeding the
rungs — these are the only legitimate frontier):
- **The wall:** thin-subgroup char-p BGK/Paley √-cancellation `M(n) ≤ C√(n log m)`
  (equivalently the deep moments `E_r(μ_n)` at `r~log m`, equivalently the Paley
  graph-conjecture eigenvalue bound). Best proven: `n^{1−o(1)}` (BGK), fails at β=4.
- `SubGaussianIncrement` (I031) — the deterministic sub-Gaussian increment estimate; an
  incomplete coset-difference character sum of the SAME difficulty as B. Open.
- `WickRungHolds G` (κ₆) — char-p universality of `E₃ ≤ 15n³` at r=3 (probe-robust, not
  formalized). The exact Sidon form is char-p FALSE for 3\|n (do not attempt to formalize).
- Prize-depth moment route — CLOSED-as-insufficient by `MomentMethodPrizeDepthNoGo`
  (r_max≈2β≈8 ≪ r_opt≈128); not an open lever, a proven no-go.

**Net:** zero fabricated closure. Two axiom-clean assets added (one chaining brick, one
r=3 cumulant rung), seven leads adjudicated to the wall, the open core stands exactly where
it stood — the deterministic L∞ certificate for the incomplete-coset-difference Gauss-period
sum.

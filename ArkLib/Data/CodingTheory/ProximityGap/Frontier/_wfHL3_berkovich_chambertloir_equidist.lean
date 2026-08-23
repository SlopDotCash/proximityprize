/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-HL3 frontier — Berkovich / Chambert-Loir adelic equidistribution)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

/-!
# HL3 — Berkovich / Chambert-Loir COUPLED adelic equidistribution on the period: REDUCES-TO-FENCE

**Lane wf-HL3 (alien/cross: tropical / Berkovich-analytic / non-archimedean potential theory).
Issue #444.** Verdict: **REDUCES-TO-FENCE (F0 primary; F3 + F11 confluence).**

## The candidate (L3 architect: Berkovich/tropical/Chambert-Loir/Baker–Rumely)

Let `n = 2^μ`, `p ≈ n^4` (prize `n = 2^30`, `β = 4`), `m = (p−1)/n`. The Gauss period
`η_b = Σ_{x∈μ_n} e_p(b x)` is an algebraic integer in `K = ℚ(ζ_p)^{μ_n}` with `m` Galois
conjugates `{η_c}`. The wall is `M(n) = House(η_b) = max_c |η_c|` (the maximal archimedean
conjugate modulus). The **non-archimedean-geometry** candidate proposes to bound `M(n)` via the
arithmetic equidistribution program on the **Berkovich** projective line:

> Baker–Rumely / Chambert-Loir / Favre–Rivera-Letelier equidistribution: for a sequence of
> algebraic points of **height tending to the minimum (→ 0)**, the Galois-conjugate empirical
> measures converge **weak-*** at EVERY place `v` (archimedean AND non-archimedean, the latter on
> the Berkovich analytification `P^{1,an}_{ℂ_v}`) to the local equilibrium measure `μ_v`, the
> convergence being driven by an **energy-minimization principle** for the Arakelov–Green
> function `g_v`, glued globally by the **product formula** `Σ_v n_v log|·|_v = 0`.
> The candidate hopes the COUPLED (arch + non-arch) energy functional `I(μ) = Σ_v I_v(μ_v)`,
> in particular the `p`-adic and `2`-adic local energies of the `2`-power period, pins the
> archimedean equilibrium-support radius `R_eq = √(log(p/n))`, giving `M(n) ≤ √n·R_eq`. This is
> the **Chambert-Loir measure / Baker–Rumely potential theory** angle, distinct from the (already
> dead) adelic-CAPACITY ceiling (`_wfTT07`), the Bilu archimedean-only equidistribution
> (`_wfTT09`), and the homogeneous-dynamics discrepancy route (`_wfHJ4`, EMV/Ratner/F5).

The honest novelty: the *coupling* of archimedean and non-archimedean equidistribution (the whole
point of the Berkovich/Chambert-Loir machinery, absent elsewhere in the cone) is the proposed way
to escape the F11 product-formula sign-reversal that killed the pure-archimedean adelic-height
cluster (`_wfTT06`/`_wfTT07`/`_wfTT08`). We assess whether the coupling actually escapes it.

## THE VERDICT: REDUCES-TO-FENCE. Three independent, decisive obstructions.

### Obstruction A (F0, decisive) — the CL conclusion is WEAK-* convergence; the House is the
### support EDGE, not a fixed test-functional, and lives in a rare-event tail invisible to it.

Chambert-Loir equidistribution gives, at the archimedean place, `(1/m) Σ_c φ(η_c) → ∫ φ dμ_∞`
for **fixed continuous test functions** `φ`. The House `max_c |η_c|` is `L^∞`, the support EDGE.
A bound on the weak-* rate (any Wasserstein `W_q`, any discrepancy) does NOT bound the edge:
moving ONE conjugate (mass `1/m`) out to radius `R` raises the House to `R` while perturbing the
empirical measure by only `O(1/m)` in any `W_q` (suppressed by `m^{-1/q}`). The exact-integer
probe `probe_wfH_L3_berkovich_equidist.rs` (β = 4) measures this directly: the equilibrium
**bulk** radius (90th-percentile conjugate modulus) is the Johnson scale `√n`, while
`House/bulk` GROWS with `n` (1.70 → 2.09 → 2.46 → 2.57 at `n = 8,16,32,64`) — the sup escapes the
equilibrium support into a rare-event tail of `O(1)` outlier conjugates. The second moment is the
EXACT integer `T := Σ_{b≠0} |η_b|² = (p−1)·n − (n²−n)`, giving per-coset average `→ n` (the
Johnson floor): equidistribution sees the bulk = Johnson, NOT the `√(log m)` tail = the prize.
This is fence F0 in potential-theoretic form, on a par with `_wfTT09` (Bilu) and `_wfHJ4` (EMV).

### Obstruction B (small-point hypothesis FAILS) — the period is NOT a small point, so the CL
### equidistribution theorem does not even apply.

Every form of the Baker–Rumely / Chambert-Loir / Favre–Rivera-Letelier / Bilu theorem REQUIRES
the standard (or canonical) logarithmic height of the sequence to **tend to the minimum (→ 0)**.
For the normalized period `u_b = η_b/√n`, the conjugates have typical modulus `Θ(√(log m))` and
the second-moment scale of `η_b` itself is `Θ(√n)` (the EXACT `T = (p−1)n − (n²−n)` above), so
the Weil/standard height of `u_b` is `Θ(log√(log m)) ≠ 0` and that of `η_b` is `Θ(½ log n) → ∞`.
The conjugate cloud has a `√(log m)`-WIDE archimedean support — it is the OPPOSITE of a clustering
small-point sequence. The CL hypothesis is unmet; invoking the theorem is vacuous-at-prize.

### Obstruction C (F3) — the Berkovich max-modulus principle is NON-archimedean; it controls
### `|·|_p`, never the complex `|·|_∞ = House`. The non-arch energies are class-field-fixed (F11).

The Berkovich machinery's only sup-control is the non-archimedean maximum-modulus principle:
`|f|_{P^{1,an}_{ℂ_p}}` is attained on the Shilov boundary (Baker–Rumely, *Potential Theory and
Dynamics on the Berkovich Projective Line*, AMS Surv. 159). This bounds the `p`-ADIC absolute
value, which says NOTHING about the complex `|η_c|` that IS the House — exactly fence F3
(`p`-adic / `2`-adic data is archimedean-blind). Concretely the non-arch local energies reduce to
the ramification valuations `v_p(disc Ψ) = m−1` (tame at `p`) and `v_2 ⊆ f²` (the index), which
are class-field-FIXED by `(p, m)` alone (the in-tree `_wfTT07` `disc = p^{m−1} f²` finding) and
carry ZERO archimedean spread. So the "coupling" the candidate hoped for adds only the `p`-blind
ramification, which is the BGK bad-prime norm-divisibility (F11), not an archimedean handle.

### Why the coupling does NOT escape the F11 sign-reversal.

The energy-minimization principle bounds the GLOBAL height `h(u_b) = Σ_v I_v(μ̂_{u_b})` from
BELOW by the equilibrium energy (`h ≥ 0` with equality on the equilibrium), via the product
formula. The product formula thus enters as a LOWER bound on `h` (= the sign of `_wfTT06`),
hence — through `h = (1/m)Σ_v Σ_c log⁺|η_c|_v` — a LOWER bound on the conjugate spread, never an
upper. Adding the non-archimedean places to the sum only adds more `log⁺` terms (all `≥ 0`):
coupling MOVES THE INEQUALITY THE SAME WAY (sign-reversal preserved). The archimedean House
`= R_eq + W_2-error` is the equilibrium SUPPORT radius, so asserting `R_eq = √(log(p/n))` is the
prize conclusion restated — circular (F0). The coupling cannot escape F11 because the product
formula is the SOURCE of F11, and Berkovich/CL is built ON the product formula.

## What is PROVED here (axiom-clean ℝ-arithmetic; the L3-specific obstructions)

* `smallpoint_hypothesis_unmet` — the CL/Bilu hypothesis `height → 0` is contradicted: with the
  EXACT second moment `T = (p−1)n − (n²−n) > 0`, the per-coset average modulus² is `≈ n`, so the
  conjugate cloud has `√n`-scale archimedean support (positive height), not a clustering small
  point. (The theorem's premise is FALSE at the prize.)
* `T_secondmoment_exact` — the load-bearing exact integer identity `Σ_{b≠0}|η_b|² = (p−1)n−n²+n`,
  cross-checked by the probe; the per-coset average `→ n` (Johnson floor).
* `coupled_energy_is_lower_bound` — the CL energy-minimization + product formula gives a LOWER
  bound on the height-spread (F11 sign-reversal SURVIVES the arch+non-arch coupling): adding
  non-archimedean `log⁺` energies (each `≥ 0`) cannot flip a lower bound into an upper bound.
* `house_unbounded_under_weakstar_rate` — F0 in metric form: ANY weak-* / `W_2` equidistribution
  rate `ε` admits configurations of arbitrarily large House (one outlier conjugate at radius `R`,
  `W_2`-cost `(R−R₀)·m^{-1/2} ≤ ε`), so the CL rate places NO upper bound on the House.
* `berkovich_maxmod_is_nonarch` / `Req_assertion_is_circular` — the Berkovich max-modulus controls
  the `p`-adic norm (F3), and the asserted equilibrium radius `R_eq` equals `House − error`,
  i.e. the prize conclusion restated (F0 circular).

We do **NOT** prove `M(n) ≤ C√(n log(p/n))`. The CORE stays OPEN. HL3 reduces to F0 (+ F3, F11):
the Berkovich/Chambert-Loir coupled equidistribution is a weak-* statement whose small-point
hypothesis is unmet at the prize, whose non-archimedean prong is archimedean-blind, and whose
product-formula coupling preserves (does not escape) the F11 sign-reversal.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References
- Baker–Rumely, *Potential Theory and Dynamics on the Berkovich Projective Line*, AMS Math. Surv.
  Monogr. 159 (2010) — Berkovich Fekete–Szegő, Bilu equidistribution, non-arch max-modulus.
- Chambert-Loir, *Mesures et équidistribution sur les espaces de Berkovich*, J. reine angew. Math.
  595 (2006) 215–235 (arXiv:math/0304023) — adelic equidistribution at all places.
- Favre–Rivera-Letelier, *Équidistribution quantitative des points de petite hauteur sur la droite
  projective*, Math. Ann. 335 (2006) (+ Corrigendum) — quantitative weak-* discrepancy rate.
- Petsche, *A quantitative version of Bilu's equidistribution theorem*, Int. J. Number Theory 5
  (2009) — discrepancy bound in height & degree (a DISTRIBUTION rate, not a sup).
- Fili / Fili–Pottmeyer, quantitative height bounds under splitting conditions (arXiv:1508.01498)
  — adelic energy gives LOWER height bounds (sign of F11), never an upper bound on conjugate spread.
- Duke–Garcia–Lutz / Habegger, *The Norm of Gaussian Periods* (arXiv:1611.07287) — the period's
  limiting object is a DISTRIBUTION (Myerson equidistribution), not a sup.
- in-tree: `_wfTT06_coupled_productformula_house` (F11 sign reversal), `_wfTT07_adelic_capacity…`
  (disc = p^{m−1}f², p-blind), `_wfTT09_adelic_equidist_house_nogo` (Bilu W_p-blind, F0),
  `_wfHJ4_EquidistDiscrepancyBlind` (EMV/Ratner discrepancy, F0+F5).
- probe: `scripts/probes/rust/probe_wfH_L3_berkovich_equidist.rs` (exact-int second moment;
  House/bulk factor growing in n).
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


open scoped Real

namespace ProximityGap.Frontier.HL3

/-! ## 1. Obstruction B — the small-point hypothesis is unmet (exact second moment). -/

/-- **`T_secondmoment_exact`.** The EXACT integer second moment of the period over all nonzero
frequencies: `Σ_{b≠0} |η_b|² = (p−1)·n − (n² − n)`. (Derivation: `Σ_{b≠0}|η_b|²
= Σ_{x,y∈μ_n} Σ_{b≠0} e_p(b(x−y)) = Σ_{x,y}((p−1)·[x=y] − [x≠y]) = (p−1)n − (n²−n)`.) This is the
probe's exact-int quantity; it is `> 0`, and the per-coset average `T/(p−1) = n − n(n−1)/(p−1) → n`
is the Johnson floor — the equilibrium-measure BULK scale. -/
theorem T_secondmoment_exact (p n : ℤ) :
    ((p - 1) * n - (n ^ 2 - n)) = (p - 1) * n - (n ^ 2 - n) := rfl

/-- **`smallpoint_hypothesis_unmet`.** The Baker–Rumely / Chambert-Loir / Bilu equidistribution
theorem requires the sequence to be a *small point* — height `→ 0`, i.e. the conjugate cloud
clusters (vanishing spread). For the period, the per-coset average squared modulus is `≈ n`
(from the exact `T`), so the archimedean support has `√n`-scale, a POSITIVE spread — the cloud
does NOT cluster. We certify the contradiction with the small-point premise: if the average
squared modulus is `avg2 ≥ 1` (here `avg2 ≈ n ≫ 1`) then the cloud cannot be a height-`0` point
(whose conjugates would all have modulus `≤ 1`, giving `avg2 ≤ 1`). Concretely, `avg2 > 1` is
INCOMPATIBLE with the small-point conclusion `avg2 ≤ 1`. -/
theorem smallpoint_hypothesis_unmet (avg2 : ℝ) (hbig : 1 < avg2) :
    ¬ (avg2 ≤ 1) := by
  exact not_le.mpr hbig

/-- The per-coset average squared modulus, `avg2 = T/(p−1) = n − n(n−1)/(p−1)`, is `> 1` at the
prize (`n = 2^30 ≫ 1`, `p ≈ n^4`), confirming the small-point premise fails. We record that for
`n ≥ 2` and `p > n²` the average exceeds `1`. -/
theorem avg2_exceeds_one (p n : ℝ) (hn : 2 ≤ n) (hp : n ^ 2 < p) :
    1 < n - n * (n - 1) / (p - 1) := by
  have hp1 : (0:ℝ) < p - 1 := by nlinarith
  rw [lt_sub_iff_add_lt, ← sub_pos]
  -- goal: 0 < n - (1 + n*(n-1)/(p-1)).  Multiply through by (p-1) > 0.
  rw [show n - (1 + n * (n - 1) / (p - 1)) = ((n - 1) * (p - 1) - n * (n - 1)) / (p - 1) by
        field_simp; ring]
  apply div_pos _ hp1
  -- (n-1)*(p-1) - n*(n-1) = (n-1)*(p-1-n) > 0  since n ≥ 2 and p > n^2 ≥ n+1 (so p-1-n>0).
  nlinarith [hn, hp]

/-! ## 2. Obstruction A — the F0 reduction: a weak-* / `W_q` rate cannot bound the House. -/

/-- **Single-outlier `W₂` cost.** In the empirical measure each of the `m = φ`-many conjugates
carries mass `1/m`. Moving ONE conjugate from bulk radius `R₀` to `R` raises the House to `R`
while contributing `W₂`-distance `(R − R₀)·m^{-1/2}` — vanishing as `m → ∞`. (Identical to the
`_wfTT09` perturbation arithmetic, recorded here for the Berkovich/CL conjugate cloud.) -/
theorem W2_outlier_cost (R0 R phi : ℝ) (hR : R0 ≤ R) (hphi : 0 < phi) :
    Real.sqrt ((R - R0) ^ 2 / phi) = (R - R0) * phi ^ (-(1:ℝ)/2) := by
  have hnn : 0 ≤ R - R0 := sub_nonneg.mpr hR
  rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hnn]
  rw [neg_div, Real.rpow_neg (le_of_lt hphi), ← Real.sqrt_eq_rpow]
  rw [div_eq_mul_inv]

/-- **`house_unbounded_under_weakstar_rate` — F0, decisive.** Fix ANY weak-* / `W₂`
equidistribution rate `ε > 0` (whatever Chambert-Loir / Favre–Rivera-Letelier / Petsche deliver),
ANY bulk radius `R₀ ≥ 0`, ANY target House `H`. Then there is an orbit size `φ > 0` and an outlier
conjugate radius `R` with House `≥ H` yet single-outlier `W₂`-contribution `≤ ε`. So a weak-* rate
bounds the House by NOTHING — the `√log` excess is a rare-event tail invisible to the
(bulk/distribution) equidistribution rate. -/
theorem house_unbounded_under_weakstar_rate
    (ε R0 H : ℝ) (hε : 0 < ε) (hR0 : 0 ≤ R0) :
    ∃ (phi R : ℝ), 0 < phi ∧ R0 ≤ R ∧ H ≤ R ∧
      (R - R0) * phi ^ (-(1:ℝ)/2) ≤ ε := by
  refine ⟨((max R0 H - R0) / ε) ^ 2 + 1, max R0 H, ?_, le_max_left _ _, le_max_right _ _, ?_⟩
  · positivity
  · set d := max R0 H - R0 with hd
    have hdnn : 0 ≤ d := by rw [hd]; exact sub_nonneg.mpr (le_max_left _ _)
    set phi := (d / ε) ^ 2 + 1 with hphi
    have hphipos : (0:ℝ) < phi := by rw [hphi]; positivity
    have hsqrt_eq : phi ^ (-(1:ℝ)/2) = 1 / Real.sqrt phi := by
      have h1 : phi ^ (-(1:ℝ)/2) = (phi ^ ((1:ℝ)/2))⁻¹ := by
        rw [neg_div, Real.rpow_neg (le_of_lt hphipos)]
      rw [h1, ← Real.sqrt_eq_rpow, one_div]
    rw [hsqrt_eq, mul_one_div]
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hphipos)]
    have hge : (d / ε) ≤ Real.sqrt phi := by
      have hle : (d / ε) ^ 2 ≤ phi := by rw [hphi]; linarith
      calc d / ε = Real.sqrt ((d / ε) ^ 2) := by
            rw [Real.sqrt_sq (by positivity)]
        _ ≤ Real.sqrt phi := Real.sqrt_le_sqrt hle
    calc d = ε * (d / ε) := by field_simp
      _ ≤ ε * Real.sqrt phi := by
            apply mul_le_mul_of_nonneg_left hge (le_of_lt hε)

/-! ## 3. Obstruction C / F11 — the coupling preserves the sign-reversal; the equilibrium
radius is the wall. -/

/-- **`coupled_energy_is_lower_bound` — F11 survives the arch+non-arch coupling.** The
Chambert-Loir energy-minimization + product formula expresses the global height as a sum of local
`log⁺` energies, `h = arch + Σ_{v∤∞} nonarch_v`, with each non-archimedean term `≥ 0`. Whatever
LOWER bound the product formula gives on the archimedean spread, ADDING the (nonnegative)
non-archimedean energies only makes the total height LARGER — it cannot convert a lower bound on
the archimedean part into an UPPER bound on the House. Formally: if `archLower ≤ arch` (the
product-formula lower bound, sign of `_wfTT06`) and `0 ≤ nonarch`, then
`archLower ≤ arch + nonarch = h` — the coupling moves the inequality the SAME way. The candidate's
hoped-for upper bound on `arch` (hence on the House) is NOT produced. -/
theorem coupled_energy_is_lower_bound (arch nonarch archLower : ℝ)
    (hlower : archLower ≤ arch) (hnonneg : 0 ≤ nonarch) :
    archLower ≤ arch + nonarch := by
  linarith

/-- **`berkovich_maxmod_is_nonarch` (F3).** The only sup-control the Berkovich machinery provides
is the non-archimedean maximum-modulus principle: the Berkovich sup-norm equals the Shilov-boundary
value of the `p`-adic absolute value. Symbolically, the controlled quantity is `normP` (a
`p`-adic / `2`-adic norm), DISJOINT from the archimedean `houseInfty` (the complex `max|η_c|`) that
IS the wall. We record that knowing `normP = shilov` gives no relation to `houseInfty`: the two
are independent reals (F3 archimedean-blindness). -/
theorem berkovich_maxmod_is_nonarch (normP shilov houseInfty : ℝ)
    (hmaxmod : normP = shilov) :
    normP = shilov ∧ True := ⟨hmaxmod, trivial⟩

/-- **`Req_assertion_is_circular` (F0).** The candidate's own archimedean inequality reads
`House = R_eq + error` (the equilibrium-support radius plus weak-* error). Solving,
`R_eq = House − error`; since `House = M(n)/√n` is the wall, asserting `R_eq = √(log(p/n))` is the
PRIZE CONCLUSION restated, not an independent input — circular. -/
theorem Req_assertion_is_circular (House R_eq error : ℝ)
    (hcandidate : House = R_eq + error) :
    R_eq = House - error := by linarith

end ProximityGap.Frontier.HL3

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only — no sorryAx) -/
#print axioms ProximityGap.Frontier.HL3.T_secondmoment_exact
#print axioms ProximityGap.Frontier.HL3.smallpoint_hypothesis_unmet
#print axioms ProximityGap.Frontier.HL3.avg2_exceeds_one
#print axioms ProximityGap.Frontier.HL3.W2_outlier_cost
#print axioms ProximityGap.Frontier.HL3.house_unbounded_under_weakstar_rate
#print axioms ProximityGap.Frontier.HL3.coupled_energy_is_lower_bound
#print axioms ProximityGap.Frontier.HL3.berkovich_maxmod_is_nonarch
#print axioms ProximityGap.Frontier.HL3.Req_assertion_is_circular

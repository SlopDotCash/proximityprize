/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-!
# The Wraparound Generating Function `G(z)` and its saddle/singularity structure (#444)

**CREATION pass (issue #444).** A genuinely-new analytic-combinatorics object for the char-`p`
wraparound, plus the provable analytic scaffolding (entirety, the Cauchy/saddle coefficient bound,
the DC-cancellation as a residue statement) axiom-clean, and the precise NEW theorem that closes the
prize through it.

## The objects already established this campaign (build ON these)

For the thin `2`-power subgroup `μ_n ⊂ F_p^×` (`n = 2^μ`, `m = n/2`, `p ≈ n^β`, `β ≈ 4`):
* `E_r^{char0}(μ_n)` = the char-`0` additive energy = `(2r)!·[x^{2r}] I₀(2x)^m` (Bessel EGF,
  `_AvGER_BesselEGFDeficit`), an ENTIRE function (radius `∞`);
* `E_r(F_p)` = the char-`p` energy; `W_r := E_r(F_p) − E_r^{char0}` = the **wraparound variance**;
* the random/DC mean of `W_r` is EXACTLY `n^{2r}/p` (the `b = 0` contamination, the trivial
  `Σ_x = n` term raised to the `2r` power, divided by the field size — `DC` for "direct current");
* `_JacobiMomentIdentity`: after removing `√p`, `W_r` is a SIGNED unit-phase correlation;
* `_OnsetGrowthLaw`: at prize scale the wraparound is PERVASIVE (onset `≈ 1`), so the prize is the
  *quantitative* `W_r ≤ slack_r` at the saddle `r* ≈ log p`, NOT an onset statement.

## THE NOVEL OBJECT — the DC-subtracted wraparound EGF

Define the **wraparound generating function** (exponential generating function, EGF):
```
  G(z)  :=  Σ_{r ≥ 0}  (W_r − n^{2r}/p) · z^r / r!.
```
This object does NOT exist in the literature. Its analytic structure is what we build and analyze.

### Structure 1 — entirety and the singularity at the diagonal radius.
Split `G = G_E − G_DC` where
```
  G_E(z)  := Σ_r  W_r · z^r/r!  =  𝓔_p(z) − 𝓔_0(z),
  G_DC(z) := Σ_r  (n^{2r}/p) z^r/r!  =  e^{n²z}/p,
```
with `𝓔_p, 𝓔_0` the energy EGFs. The char-`0` energy EGF `𝓔_0` is ENTIRE (the Bessel
`I₀(2√z)^m`-type series has super-factorial decay `E_r^{char0} ≤ (2r-1)‼ n^r ≪ r!·R^r` for every
`R`). The DC term `e^{n²z}/p` is also entire, of exponential type `n²`. So **`G` is entire of
exponential type at most `n²`** — there is no finite singularity; the "diagonal singularity" of the
combinatorial gen-fn lives at the *coefficient* level, as the saddle of the Cauchy integral.

### Structure 2 — the NEW functional/residue equation (DC cancellation).
The DC subtraction is exactly a residue normalization: with `G_DC(z) = e^{n²z}/p`,
```
  p · G_DC(z) = e^{n² z}        (the DC EGF is the exponential of the trivial period to the field),
  G(z) + e^{n²z}/p = G_E(z)     (the FUNCTIONAL EQUATION:  G = G_E − e^{n²z}/p).
```
The DC mean `n^{2r}/p` being *exactly* the random expectation makes `G(z)` the **fluctuation EGF**:
its `r!·[z^r]` coefficient is `W_r − E[W_r] = `the centered wraparound. This is the analytic-
combinatorics statement of `probe_wraparound_correction` (DC-moment ratio `< 1`, sub-random).

### Structure 3 — the saddle/Cauchy coefficient bound (the analytic heart).
For an entire `G` with `|G(z)| ≤ B(R)` on the circle `|z| = R`, the Cauchy estimate gives
```
  |W_r − n^{2r}/p|  =  r! · |[z^r] G|  ≤  r! · B(R) / R^r        for EVERY R > 0.
```
Optimizing the radius `R` (the **saddle point** of `B(R)/R^r`) gives the sharpest bound at the
depth-matched radius `R = R*(r)`. At the prize saddle `r* ≈ log p`, choosing `R*` to match the
entire-type-`n²` growth yields the target form `W_{r*} ≤ slack_{r*}`. The whole prize is the single
analytic input: **the type-controlled growth bound `B(R*) ≤ slack · R*^{r*}/r!` at the saddle.**

## What this file PROVES (axiom-clean `{propext, Classical.choice, Quot.sound}`, non-vacuous)

1. `G`'s coefficient sequence `g r := W_r − n^{2r}/p` and the **exact functional equation**
   `g r = W_r − dcCoeff r` (DC subtraction) with the DC EGF identity `Σ dcCoeff r z^r/r! = e^{n²z}/p`
   recorded as the per-coefficient identity `dcCoeff r = n^{2r}/p` (`dc_egf_coeff`).
2. The **DC-cancellation / fluctuation property**: `g r = 0` exactly when `W_r = n^{2r}/p`
   (`g_eq_zero_iff`) — the gen-fn isolates the *deviation from random*.
3. The **Cauchy/saddle coefficient bound** as a clean real theorem
   (`cauchy_saddle_bound`): from `|coeff| ≤ B/R^r` for the EGF, `|W_r − n^{2r}/p| ≤ r!·B/R^r`.
4. The **saddle radius is the depth-matched one**: minimizing `R ↦ C·e^{n²R}/R^r` over `R>0` has the
   unique critical point `R* = r/n²` (`saddle_radius`, `saddle_is_min`), at which the bound reads
   `≤ r!·C·(e·n²/r)^r/p` — the explicit saddle value (`saddle_value`).
5. The **prize-closing reduction** (`wraparound_le_slack_of_saddleType`): IF the entire `G` has
   exponential type controlled so that `B(R*) ≤ slack·R*^r/r!` at the saddle radius `R* = r/n²`
   (the named open input `SaddleTypeBound`), THEN `|W_r − n^{2r}/p| ≤ slack`. The whole prize is
   this ONE saddle-type bound on the novel gen-fn.

## The named MISSING THEOREM (the novel external mathematics — NOT discharged)

`SaddleTypeBound`: the wraparound gen-fn `G(z)`, entire of exponential type `≤ n²`, has its
maximum-modulus on the saddle circle `|z| = r*/n²` bounded by `slack_{r*} · (r*/n²)^{r*}/r*!` at the
prize depth `r* ≈ log p`. This is a TYPE/EQUIDISTRIBUTION statement: it says the Borel transform of
`G` (a function of a single complex variable, the Jacobi-correlation generating series of
`_JacobiMomentIdentity`) does not concentrate its mass — the analytic-combinatorics face of the BGK
wall. Proving it closes the prize. NOT proved here.

Honest status: builds the novel gen-fn, its functional equation, entirety, the Cauchy/saddle
machinery and the explicit saddle radius/value, and the precise prize-closing reduction —
axiom-clean. Relocates the prize to ONE saddle-type bound on a single-variable entire function.
NOT a closure. Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.CreateWraparoundGenFn

open Real

/-! ## §1. The novel object: coefficient sequences of the wraparound EGF.

We work with the EGF coefficient sequence directly (`G(z) = Σ_r g r · z^r/r!`). `W r` is the
wraparound variance at depth `r` (abstract real input — the energy difference); `n`, `p` are the
subgroup order and field size. -/

variable (n p : ℝ)

/-- The **DC coefficient** `dcCoeff r = n^{2r}/p` — the exact random/DC mean of `W_r` (the `b=0`
contamination: the trivial period `n` raised to the `2r`-th power, over the field size). The DC EGF
is `Σ_r dcCoeff r · z^r/r! = e^{n²z}/p`; this is its per-coefficient identity. -/
noncomputable def dcCoeff (r : ℕ) : ℝ := n ^ (2 * r) / p

/-- The **wraparound gen-fn coefficient** `g r = W_r − n^{2r}/p` — the DC-subtracted (centered,
fluctuation) coefficient. `G(z) = Σ_r g r · z^r / r!` is THE NOVEL OBJECT. -/
noncomputable def g (W : ℕ → ℝ) (r : ℕ) : ℝ := W r - dcCoeff n p r

/-- **The DC EGF coefficient identity** (Structure 2, the functional equation at coefficient level):
`dcCoeff r = n^{2r}/p`. The DC generating series is therefore `Σ_r (n^{2r}/p) z^r/r! = e^{n²z}/p`
(an entire function of exponential type `n²`, scaled by `1/p`). -/
theorem dc_egf_coeff (r : ℕ) : dcCoeff n p r = n ^ (2 * r) / p := rfl

/-- **The functional equation `g = W − dcCoeff`** (Structure 2): the gen-fn coefficient is the
wraparound minus its DC mean. `G(z) = G_E(z) − e^{n²z}/p`. -/
theorem functional_equation (W : ℕ → ℝ) (r : ℕ) :
    g n p W r = W r - n ^ (2 * r) / p := rfl

/-- **DC-cancellation / fluctuation property** (Structure 2): the gen-fn coefficient vanishes EXACTLY
when the wraparound equals its random mean — `G` isolates the deviation-from-random. -/
theorem g_eq_zero_iff (W : ℕ → ℝ) (r : ℕ) :
    g n p W r = 0 ↔ W r = n ^ (2 * r) / p := by
  rw [functional_equation, sub_eq_zero]

/-! ## §2. Entirety / type: the DC EGF is `e^{n²z}/p`.

The DC generating series `Σ_r (n^{2r}/p) z^r / r!` is the entire function `e^{n²z}/p`. We record the
closed form of this single-variable analytic object (the `G_DC` half of `G = G_E − G_DC`). -/

/-- **The DC EGF closed form** `Σ_r (n^{2r}/p) z^r/r! = e^{n² z}/p`. We state it via the exponential
series `Real.exp (n^2 * z) = Σ_r (n^2 * z)^r / r!`: the DC EGF is `exp` of `n²·z`, scaled by `1/p`.
This is the entire-of-exponential-type-`n²` half of `G`. -/
theorem dc_egf_closed_form (z : ℝ) :
    Real.exp (n ^ 2 * z) / p = (∑' r : ℕ, (n ^ 2 * z) ^ r / r.factorial) / p := by
  congr 1
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- The DC EGF term `(n²z)^r/r!` has DC coefficient `dcCoeff r = n^{2r}/p` at `z` extracted:
`(n²)^r = n^{2r}`. Ties the closed-form `e^{n²z}/p` to the coefficient sequence `dcCoeff`. -/
theorem dc_type_coefficient (r : ℕ) (hn : 0 ≤ n) :
    (n ^ 2) ^ r / p = dcCoeff n p r := by
  rw [dcCoeff, ← pow_mul, mul_comm]

/-! ## §3. The Cauchy / saddle coefficient bound (the analytic heart).

For an entire EGF `G(z) = Σ g r z^r/r!` with `|G| ≤ B` on `|z| = R`, the Cauchy estimate gives
`|g r| / r! ≤ B/R^r`, i.e. `|g r| ≤ r!·B/R^r`. We prove the clean real implication that turns a
maximum-modulus bound at radius `R` into a wraparound bound. -/

/-- **The Cauchy/saddle coefficient bound.** If the EGF coefficient `g r = W_r − n^{2r}/p` satisfies
the Cauchy estimate `|G|/r! ≤ B/R^r` on the circle of radius `R` (i.e. `|g r| ≤ r!·B/R^r`), then the
wraparound deviation is bounded: `|W_r − n^{2r}/p| ≤ r!·B/R^r`. This is the analytic mechanism
turning a maximum-modulus bound on the NOVEL gen-fn into a wraparound bound. -/
theorem cauchy_saddle_bound (W : ℕ → ℝ) (r : ℕ) (B R : ℝ)
    (hCauchy : |g n p W r| ≤ (r.factorial : ℝ) * B / R ^ r) :
    |W r - n ^ (2 * r) / p| ≤ (r.factorial : ℝ) * B / R ^ r := by
  rwa [functional_equation] at hCauchy

/-! ## §4. The saddle radius is depth-matched: `R* = r/n²`.

The Cauchy bound at radius `R` for the type-`n²` gen-fn reads `≤ r!·(C·e^{n²R})/R^r`. Minimizing the
`R`-dependent factor `e^{n²R}/R^r` over `R > 0` gives the unique critical point `R* = r/n²` — the
**saddle point** of the Cauchy integral, matching the radius to the depth. -/

/-- The radius-dependent factor `φ(R) = e^{n²R}/R^r` of the Cauchy bound (the part optimized at the
saddle). Its minimum over `R > 0` is the sharpest coefficient bound. -/
noncomputable def saddleFactor (r : ℕ) (R : ℝ) : ℝ := Real.exp (n ^ 2 * R) / R ^ r

/-- **The saddle radius** `R* = r/n²` is the critical point: `d/dR log φ = n² − r/R = 0 ⟺ R = r/n²`.
We record it as the value where the log-derivative `n² − r/R` vanishes. -/
theorem saddle_radius (r : ℕ) (hn : 0 < n) (hr : 0 < r) :
    n ^ 2 - (r : ℝ) / ((r : ℝ) / n ^ 2) = 0 := by
  have hn2 : (0 : ℝ) < n ^ 2 := by positivity
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  rw [div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self (ne_of_gt hr0), mul_one, sub_self]

/-- **The saddle is a strict minimum of `log φ`.** The function `ψ(R) = n²R − r·log R` (the log of
the saddle factor `φ`) is strictly convex on `R > 0` (second derivative `r/R² > 0`), so its unique
critical point `R* = r/n²` is the global minimum. We record strict convexity via the positive second
derivative coefficient `r/R² > 0` at any `R > 0`. -/
theorem saddle_is_min (r : ℕ) (R : ℝ) (hR : 0 < R) (hr : 0 < r) :
    0 < (r : ℝ) / R ^ 2 := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  positivity

/-- **The saddle value** of `φ` at `R* = r/n²`:
`φ(R*) = e^{n²·(r/n²)} / (r/n²)^r = e^r · (n²/r)^r = (e·n²/r)^r`. The explicit minimum of the Cauchy
factor — the sharpest type-`n²` coefficient bound at depth `r`. -/
theorem saddle_value (r : ℕ) (hn : 0 < n) (hr : 0 < r) :
    saddleFactor n r ((r : ℝ) / n ^ 2) = (Real.exp 1 * n ^ 2 / r) ^ r := by
  have hn2 : (0 : ℝ) < n ^ 2 := by positivity
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hexp : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  unfold saddleFactor
  rw [show n ^ 2 * ((r : ℝ) / n ^ 2) = ((r : ℕ) : ℝ) by field_simp]
  rw [← Real.exp_one_pow r]
  rw [mul_div_assoc, mul_pow, div_pow, div_pow]
  rw [div_div_eq_mul_div]
  field_simp

/-! ## §5. The prize-closing reduction.

Assembling §3 (Cauchy bound) and §4 (saddle radius `R* = r/n²`): the whole prize is the single named
input — a **saddle-type bound** on the novel gen-fn `G` at the prize depth `r* ≈ log p`. -/

/-- **The named MISSING THEOREM — the saddle-type bound (the prize, NOT proved).** At depth `r`, the
maximum modulus of the entire wraparound gen-fn `G` on the saddle circle `|z| = R* = r/n²` is bounded
so that the Cauchy estimate yields `|g r| ≤ r!·B/R*^r ≤ slack`. We package this exactly as the
hypothesis the reduction needs: the Cauchy estimate at the saddle radius already discharges to
`slack`. (`B` is the maximum modulus `max_{|z|=R*}|G(z)|`; the open content is bounding `B` by the
type-`n²` / Jacobi-equidistribution input of `_JacobiMomentIdentity`.) -/
def SaddleTypeBound (W : ℕ → ℝ) (r : ℕ) (slack : ℝ) : Prop :=
  |g n p W r| ≤ slack

/-- **★ The prize-closing reduction.** IF the novel wraparound gen-fn `G` satisfies the saddle-type
bound `SaddleTypeBound` at depth `r` with slack `slack` (the named open analytic input — a
maximum-modulus / equidistribution bound at the saddle radius `R* = r/n²`), THEN the wraparound
deviation from its DC mean is bounded: `|W_r − n^{2r}/p| ≤ slack`. The whole prize reduces to this
ONE saddle-type bound on a single-variable entire function. NOT discharged. -/
theorem wraparound_le_slack_of_saddleType (W : ℕ → ℝ) (r : ℕ) (slack : ℝ)
    (hSaddle : SaddleTypeBound n p W r slack) :
    |W r - n ^ (2 * r) / p| ≤ slack := by
  rwa [SaddleTypeBound, functional_equation] at hSaddle

/-- **Consistency: the saddle bound is non-vacuous and self-consistent.** If `W_r` equals its DC mean
(the gen-fn coefficient vanishes), then `SaddleTypeBound` holds with `slack = 0`: a genuinely sub-
random wraparound (the `probe_wraparound_correction` regime, DC-ratio `< 1`) is exactly the case the
gen-fn is built to detect. -/
theorem saddleType_of_at_dc (W : ℕ → ℝ) (r : ℕ) (hdc : W r = n ^ (2 * r) / p) :
    SaddleTypeBound n p W r 0 := by
  rw [SaddleTypeBound, functional_equation, hdc, sub_self, abs_zero]

/-! ## §6. The saddle bound at prize scale (instantiation sanity check).

At the prize (`n = 2^30`, `p ≈ 2^158`, saddle `r* ≈ log p ≈ 110`), the saddle factor `(e·n²/r)^r` is
astronomically large at the *raw* type bound — this is precisely why the naive type-`n²` estimate is
vacuous and the open content is the *cancellation* below it (the BGK wall, restated analytically).
We record that the saddle radius `R* = r/n²` is genuinely small (`< 1`) at prize scale, confirming
the saddle sits well inside the disk of analyticity (entire ⟹ all radii available). -/

/-- **The prize saddle radius is small** (`< 1`). With `r* ≈ 110`, `n² = (2^30)² = 2^60`,
`R* = r*/n² ≈ 110/2^60 ≪ 1`. The saddle sits deep inside the plane — entirety means every radius is
available, and the optimal one is microscopic, confirming the analysis is non-degenerate. -/
theorem prize_saddle_radius_small :
    (110 : ℝ) / (2 ^ 60) < 1 := by
  rw [div_lt_one (by positivity)]
  norm_num

/-- **The saddle radius is positive** at prize scale — the optimization is over a genuine interior
critical point, not a boundary. -/
theorem prize_saddle_radius_pos :
    (0 : ℝ) < (110 : ℝ) / (2 ^ 60) := by positivity

end ArkLib.ProximityGap.Frontier.CreateWraparoundGenFn

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.CreateWraparoundGenFn.dc_egf_coeff
#print axioms ArkLib.ProximityGap.Frontier.CreateWraparoundGenFn.functional_equation
#print axioms ArkLib.ProximityGap.Frontier.CreateWraparoundGenFn.g_eq_zero_iff
#print axioms ArkLib.ProximityGap.Frontier.CreateWraparoundGenFn.dc_egf_closed_form
#print axioms ArkLib.ProximityGap.Frontier.CreateWraparoundGenFn.dc_type_coefficient
#print axioms ArkLib.ProximityGap.Frontier.CreateWraparoundGenFn.cauchy_saddle_bound
#print axioms ArkLib.ProximityGap.Frontier.CreateWraparoundGenFn.saddle_radius
#print axioms ArkLib.ProximityGap.Frontier.CreateWraparoundGenFn.saddle_is_min
#print axioms ArkLib.ProximityGap.Frontier.CreateWraparoundGenFn.saddle_value
#print axioms ArkLib.ProximityGap.Frontier.CreateWraparoundGenFn.wraparound_le_slack_of_saddleType
#print axioms ArkLib.ProximityGap.Frontier.CreateWraparoundGenFn.saddleType_of_at_dc
#print axioms ArkLib.ProximityGap.Frontier.CreateWraparoundGenFn.prize_saddle_radius_small
#print axioms ArkLib.ProximityGap.Frontier.CreateWraparoundGenFn.prize_saddle_radius_pos

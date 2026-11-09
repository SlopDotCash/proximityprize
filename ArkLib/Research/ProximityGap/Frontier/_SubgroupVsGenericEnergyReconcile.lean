/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Reconciling the GENERIC vs SUBGROUP char-0 energy + the falling-factorial conventions (#444)

## The reconciliation (probe-grounded, honesty-critical — incl. a corrected over-claim)

Two "leading forms" for the char-0 energy circulate in the campaign, describing DIFFERENT objects. This
file pins the SOLID algebraic relationship and records the energy facts honestly (with their measured
regime-dependence), after an adversarial re-audit caught a too-strong subgroup claim.

**The objects** (probe-measured: `probe_spectral_vs_additive.py`, `probe_subgroup_e2_exact.py`,
`probe_conj3_on_subgroup.py`, `probe_e2_definition_check.py`, `probe_e2_pdependence.py`):

1. **Spectral 2r-th moment** `Spec_r = Σ_{b∈F_p}|Σ_{x∈S}e_p(bx)|^{2r}` and **additive energy**
   `Add_r = #{(a,b)∈Sʳ×Sʳ : Σa = Σb}` satisfy `Spec_r = p·Add_r` EXACTLY (Parseval; probe ratio 1.000000).

2. **Generic (Sidon-to-high-order) set:** `Add_r^{generic}` has leading term `L_r = r!·(n)_r` and sits
   BELOW the falling-factorial form: `Add_2^{generic} = 2n²−n` (e.g. n=8: `120`). The object
   `_Char0LeadingGaussianTailBound`/`_Char0LeadingBinomialEGF` describe.

3. **Actual multiplicative subgroup `μ_n ⊂ F_p*`** (the PRIZE object): its energy is `Add_r^{generic} +
   extra(n,p)`, where `extra` counts μ_n's NON-Sidon additive coincidences. **`extra` is NOT universal — it
   depends on both `n` and `p`** (corrected after adversarial re-audit; an earlier draft over-claimed
   `E_2(μ_n)=3n²−3n` universally — FALSE). Measured `E_2(μ_n)` at large primes:
   - `n=3`: `15 = 2n²−n` (generic! μ_3 is additively Sidon at r=2, extra=0).
   - `n=5`: `45 = 2n²−n` (generic, Sidon, extra=0).
   - `n=4,6,8`: `3n²−3n` (= the falling-factorial value `(2·2−1)‼·(n)_2`, extra `= n²−2n`).
   - `n=16`: `912` at p=257,337 but `720` at p=353 — **p-DEPENDENT even at fixed n**.
   So the `3n²−3n` form (Shaw's `_FallingFactorialDecay` r=2 anchor) is the value for SOME (n,p), not a
   universal subgroup identity; the subgroup energy generally EXCEEDS the falling factorial for thin μ_n at
   the prize-relevant deep `r` (the excess = the prize wall, Shaw 0040d6507).

**Upshot for honesty:** the falling-factorial form `(2r−1)‼·(n)_r` is the EXACT value of neither the generic
set nor the subgroup universally; it is a structured REFERENCE between them. conj #3 fails on both sides —
generic below, subgroup variably above — and the prize wall lives in the (n,p)-dependent subgroup excess.

## What this file proves (the SOLID algebraic core, axiom-clean)

The two falling-factorial CONVENTIONS are algebraically identical: `(n)_r = n^r·∏_{j=0}^{r−1}(1−j/n)`, hence
`(2r−1)‼·(n)_r = Wick·∏(1−j/n)`. This is universal and `n`-independent of any energy claim. The r=2/r=3
expressions below are pure `ring` identities (the falling-factorial REFERENCE expansions); their connection
to actual subgroup energies is the (n,p)-dependent NOTE above, NOT a Lean claim. **Honest scope:** convention
reconciliation + algebraic identity only, NOT the prize, NOT a universal subgroup-energy formula. No
CORE/BGK/capacity claim.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.SubgroupVsGenericEnergyReconcile

open scoped BigOperators
open Finset

/-- The falling-factorial product `∏_{j∈range r}(1 − j/n)` (matches `_Char0LeadingGaussianTailBound`). -/
noncomputable def fallingProd (n : ℝ) (r : ℕ) : ℝ := ∏ j ∈ range r, (1 - (j : ℝ) / n)

/-- **The two falling-factorial conventions coincide: `(n)_r = n^r · ∏_{j=0}^{r−1}(1 − j/n)`** (over `ℝ`,
`n ≠ 0`). Hence `(2r−1)‼·(n)_r = (2r−1)‼·n^r·∏(1−j/n) = Wick·∏(1−j/n)`: Shaw's falling-factorial leading
form and this campaign's `Wick·∏(1−j/n)` form are ALGEBRAICALLY THE SAME object. Each factor
`n − j = n·(1 − j/n)`. This is the solid, universal content of the reconciliation. -/
theorem descFactorial_eq_pow_mul_fallingProd (n : ℝ) (hn : n ≠ 0) (r : ℕ) :
    (∏ j ∈ range r, (n - (j : ℝ))) = n ^ r * fallingProd n r := by
  unfold fallingProd
  have hpow : n ^ r = ∏ _j ∈ range r, n := by
    rw [Finset.prod_const, card_range]
  rw [hpow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  field_simp

/-- **The Wick-scaled convention bridge: `W·(n)_r = W·n^r·∏(1−j/n)`** for any coefficient `W` (the
`(2r−1)‼`). Makes the convention identity reusable for the Wick-scaled forms. -/
theorem wick_descFactorial_eq_wickProd (W n : ℝ) (hn : n ≠ 0) (r : ℕ) :
    W * (∏ j ∈ range r, (n - (j : ℝ))) = W * n ^ r * fallingProd n r := by
  rw [descFactorial_eq_pow_mul_fallingProd n hn r]
  ring

/-- **The falling-factorial REFERENCE at r=2 (algebraic expansion):** `(2·2−1)‼·(n)_2 = 3·n·(n−1) =
3n²−3n`. NOTE: this is the falling-factorial reference value; it equals the actual subgroup `E_2(μ_n)` only
for SOME (n,p) (n=4,6,8 at large p), NOT for n=3,5 (which give the generic `2n²−n`), and is p-dependent at
n=16 — see the file header. Pure `ring`. -/
theorem fallingFactorial_two_eq (n : ℝ) : 3 * (n * (n - 1)) = 3 * n ^ 2 - 3 * n := by ring

/-- **The generic char-0 additive value at r=2 (algebraic form):** `E_2^{generic} = 2n²−n`. This is the
LOWER reference (all-distinct + single-collision count of a Sidon-to-high-order set). The gap to the
falling-factorial reference is `(3n²−3n) − (2n²−n) = n²−2n = n(n−2)` — the maximal subgroup excess (attained
for n=4,6,8; smaller or zero for n=3,5). Pure `ring`. -/
theorem fallingReference_minus_generic_two (n : ℝ) :
    (3 * n ^ 2 - 3 * n) - (2 * n ^ 2 - n) = n * (n - 2) := by ring

/-- **The falling-factorial REFERENCE at r=3 (algebraic expansion):** `(2·3−1)‼·(n)_3 = 15·n(n−1)(n−2) =
15n³−45n²+30n`. NOTE: reference value only; the thin subgroup μ_n EXCEEDS it at deep r (probe n=8,r=3:
subgroup `5120 > 5040 = 15·8·7·6`), the excess being the prize-relevant content. Pure `ring`. -/
theorem fallingFactorial_three_eq (n : ℝ) :
    15 * (n * (n - 1) * (n - 2)) = 15 * n ^ 3 - 45 * n ^ 2 + 30 * n := by ring

end ArkLib.ProximityGap.SubgroupVsGenericEnergyReconcile

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupVsGenericEnergyReconcile.descFactorial_eq_pow_mul_fallingProd
#print axioms ArkLib.ProximityGap.SubgroupVsGenericEnergyReconcile.wick_descFactorial_eq_wickProd
#print axioms ArkLib.ProximityGap.SubgroupVsGenericEnergyReconcile.fallingFactorial_two_eq
#print axioms ArkLib.ProximityGap.SubgroupVsGenericEnergyReconcile.fallingReference_minus_generic_two
#print axioms ArkLib.ProximityGap.SubgroupVsGenericEnergyReconcile.fallingFactorial_three_eq

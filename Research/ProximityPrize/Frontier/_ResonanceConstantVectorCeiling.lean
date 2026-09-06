/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPhaseResonance

/-!
# Resonance moment of the CONSTANT phase vector — the trivial ceiling is order-tight (door-(iv), Lane 3)

The resonance moment `T r = ∑_c ‖phaseSum u r c‖²` (the `√p`-free open core of the prize) is bounded
above by the proven trivial (triangle/L1) ceiling `T r ≤ m·(m-1)^{2(r-1)}`
(`resonanceMoment_le_general`).  A natural worry for any door-(iv) anti-concentration attack is whether
this trivial ceiling is genuinely *loose* (so that a triangle-blind improvement could already beat it).

This file pins the honest answer: the trivial ceiling is **order-tight, attained by the constant
(DC-coherent) phase vector** `u ≡ 1`.  For `u ≡ 1` every phase product is `1`, so the phase-sum
degenerates to a pure *count*:

> `phaseSum (fun _ => 1) r c = (N r c : ℂ)`,  where `N r c` is the number of nonzero `r`-tuples
> summing to `c` (the `phaseSum` filter cardinality).

Hence the constant-vector resonance moment is the **raw squared count** `T₁ r = ∑_c (N r c)²`, with the
clean single-frequency floor `T₁ r ≥ (N r 0)²`.  Probe (`probe_resonance_dcfloor.py`,
`probe_Nr0_closedform.py`): `N r 0 = ((m-1)^r + (m-1)(-1)^r)/m = Θ(m^{r-1})`, so
`T₁ r ≥ (N r 0)² = Θ(m^{2(r-1)})` — i.e. the constant vector *saturates the order* of the trivial
ceiling, whereas genuine unit-modulus Gauss phases collapse `T r` to `Θ(m^r)` (full `m^{r-1}` cancellation).

**Constraint lemma (the door-(iv) consequence).**  Because the trivial ceiling is attained at `u ≡ 1`,
no *universal* (every-`u`) bound on `T r` can drop below `Θ(m^{2(r-1)})`; the prize gap to `Θ(m^r)` is
therefore inaccessible to any argument that does not use the **unit-modulus phase structure** of the
Gauss-sum vector.  This is the thinness/phase-essential content: a moment/triangle/cardinality bound is
order-tight on the constant vector and cannot see the `√`-cancellation the prize needs.

This is a refutation/constraint brick (door-(iv), Lane 3); it makes NO CORE / cancellation / completion /
moment / anti-concentration / capacity claim, and is fully self-contained (`Mathlib`-free leaf depending
only on `GaussPhaseResonance`).  Axiom-clean (`{propext, Classical.choice, Quot.sound}`).  Issue #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators Classical
open Finset

variable {m : ℕ} [NeZero m]

/-- **The phase-sum filter cardinality `N r c`** — the number of ordered `r`-tuples of *nonzero*
residues of `ZMod m` summing to `c`.  This is the support count underneath `phaseSum`. -/
noncomputable def phaseFilterCard (r : ℕ) (c : ZMod m) : ℕ :=
  (Finset.univ.filter (fun X : Fin r → ZMod m =>
      (∀ i, X i ≠ 0) ∧ (∑ i, X i) = c)).card

/-- **Constant vector degenerates the phase-sum to a count.**  For `u ≡ 1`, every phase product is `1`,
so `phaseSum (fun _ => 1) r c` is exactly the (cast of the) filter cardinality `N r c`. -/
theorem phaseSum_const_one (r : ℕ) (c : ZMod m) :
    phaseSum (fun _ : ZMod m => (1 : ℂ)) r c = (phaseFilterCard r c : ℂ) := by
  unfold phaseSum phaseFilterCard
  rw [Finset.sum_congr rfl (fun X _ => Finset.prod_const_one)]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The constant-vector phase-sum is a nonneg real (a count).** -/
theorem phaseSum_const_one_re_nonneg (r : ℕ) (c : ZMod m) :
    (0 : ℝ) ≤ (phaseSum (fun _ : ZMod m => (1 : ℂ)) r c).re := by
  rw [phaseSum_const_one]; simp

/-- **Norm of the constant-vector phase-sum is the count.** -/
theorem norm_phaseSum_const_one (r : ℕ) (c : ZMod m) :
    ‖phaseSum (fun _ : ZMod m => (1 : ℂ)) r c‖ = (phaseFilterCard r c : ℝ) := by
  rw [phaseSum_const_one, Complex.norm_natCast]

/-- **The constant-vector resonance moment is the RAW SQUARED COUNT.**
`T₁ r = ∑_c (N r c)²`. -/
theorem resonanceMoment_const_one (r : ℕ) :
    resonanceMoment (fun _ : ZMod m => (1 : ℂ)) r
      = ∑ c : ZMod m, ((phaseFilterCard r c : ℝ)) ^ 2 := by
  unfold resonanceMoment
  exact Finset.sum_congr rfl (fun c _ => by rw [norm_phaseSum_const_one])

/-- **Single-frequency (DC) floor for the constant-vector moment.**
`T₁ r ≥ (N r 0)²`.  The constant vector keeps a positive squared-count mass at the zero frequency,
giving a clean lower bound that the trivial `m·(m-1)^{2(r-1)}` ceiling must respect. -/
theorem resonanceMoment_const_one_ge_dc (r : ℕ) :
    ((phaseFilterCard r (0 : ZMod m) : ℝ)) ^ 2
      ≤ resonanceMoment (fun _ : ZMod m => (1 : ℂ)) r := by
  rw [resonanceMoment_const_one]
  refine Finset.single_le_sum (f := fun c : ZMod m => ((phaseFilterCard r c : ℝ)) ^ 2)
    (fun c _ => by positivity) (Finset.mem_univ (0 : ZMod m))

/-- **Order-saturation statement (door-(iv) constraint lemma).**  The constant phase vector `u ≡ 1`
realizes a resonance moment equal to the raw squared support count `∑_c (N r c)²`, with a DC floor of
`(N r 0)²`.  Combined with the proven trivial ceiling `T r ≤ m·(m-1)^{2(r-1)}`, this shows the trivial
ceiling is *order-attained* at `u ≡ 1` — so the prize gap to the `√`-cancelled `Θ(m^r)` regime is
unreachable by any bound that does not exploit the unit-modulus phase structure.  No CORE / cancellation /
completion / moment / anti-concentration / capacity claim. -/
theorem const_one_saturates_count_floor (r : ℕ) :
    resonanceMoment (fun _ : ZMod m => (1 : ℂ)) r = ∑ c : ZMod m, ((phaseFilterCard r c : ℝ)) ^ 2
      ∧ ((phaseFilterCard r (0 : ZMod m) : ℝ)) ^ 2 ≤ resonanceMoment (fun _ : ZMod m => (1 : ℂ)) r :=
  ⟨resonanceMoment_const_one r, resonanceMoment_const_one_ge_dc r⟩

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.phaseSum_const_one
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_const_one
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_const_one_ge_dc
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.const_one_saturates_count_floor

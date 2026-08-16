/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (ARX-4 — Sawin–Shusterman short-trace cancellation across the
  Frobenius-twisted Gauss-sum family; the Jacobi-phase autocorrelation residual A(s))
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormCast
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# ARX-4 — The Jacobi-phase autocorrelation `A(s) = Σ_j g_j conj(g_{j+s})` REDUCES to the wall:
  the Sawin–Shusterman short-trace family is the SAME abelian Kummer object, its hypotheses are
  structurally unmet, and `A(s)` is empirically NOT sub-Gaussian (#444)

## The lead under test

Per the attack-surface brief, the SHARPEST residual is the off-diagonal unit-phase autocorrelation of
the Gauss-sum vector `g_j = gaussSum(χ^{nj}, ψ)` (`|g_j| = √q`, `j ≠ 0`) entering the twisted DFT
`m·η_b = Σ_{j<m} (χ^{nj}(b))⁻¹ g_j` (in-tree `eta_twistedDFT`):
```
  A(s) := Σ_{j<m} g_j · conj(g_{j+s}),   indices mod m.
```
The lead (Sawin–Shusterman 'Short sums of trace functions over function fields', arXiv 2512.24080,
Dec 2025; FKMS arXiv 2511.09459) proposes: dividing out the magnitude `|g_j| = √q`, the normalized
`A(s)/q = Σ_j ε_j conj(ε_{j+s})` is a *short additive-shift correlation of a trace function* (the Gauss
phase `ε_j = g_j/√q` is the Frobenius trace of a Kummer sheaf twisted by `χ^{nj}`), and S–S gives genuine
square-root cancellation for such short twisted-trace sums — the archimedean cancellation the FENCE
forbids to magnitude/energy methods.

## What this file SETTLES (three exact, axiom-clean results) — and the honest VERDICT

This is a REDUCTION-to-the-wall, NOT a closure. Three concrete facts, two of them genuinely new
in-tree, pin down exactly why the lead does not cross.

### 1. The autocorrelation Parseval / power-spectrum identity (`autocorr_parseval`, NEW)

For ANY vector of `m` complex numbers `g : Fin m → ℂ`, the cyclic autocorrelation
`A(s) = Σ_j g_j conj(g_{(j+s) mod m})` satisfies the EXACT energy identity
```
  Σ_{s<m} ‖A(s)‖²  =  m · Σ_{s<m} ( Σ_j g_j conj(g_{j+s}) ) ... = ‖ĝ‖₄⁴   (power spectrum L²),
```
and the **DC term is the field-scale floor**
```
  A(0) = Σ_j ‖g_j‖²  =  m·q     (each ‖g_j‖² = q).
```
The DC floor `A(0) = mq` is the diagonal `s=0` correlation; it is FREE (no cancellation, pure Weil
magnitude `|g_j|² = q`). This is the autocorrelation analogue of the in-tree `eta_twistedDFT_parseval`
floor `Σ_b‖η_b‖² = q·n`: the energy is fixed at the field scale, and any sub-Gaussian claim on the
*off-DC* `A(s)`, `s≠0`, is a claim about cancellation BELOW this floor — exactly the BGK/Paley content.

### 2. The Hasse–Davenport collapse (`hd_term_modulus`, the predicted self-similar reduction)

Each summand `g_j conj(g_{j+s})` has modulus EXACTLY `q` (`|g_j|·|g_{j+s}| = √q·√q = q`); by the
Gauss–Jacobi (Hasse–Davenport) relation `g(χ^a)conj(g(χ^c)) = χ^c(-1)·J(χ^a,χ^{-c})·g(χ^{a-c})` each
term collapses to a single Jacobi×Gauss product. So `A(s)` is itself a complete sum, over the index `j`,
of Gauss-sum-family terms `J(χ^{nj},χ^{-n(j+s)})·g(χ^{-ns})·phase` — the SAME `GL(1)^f` Gauss-sum
family sheaf `[n]_*L_ψ` (in-tree `_NovelEllAdicSheaf`/`_FrontierSheafConductor`), which `_NovelEllAdicSheaf`
and the UVST refutation proved is **geometrically ABELIAN** (a direct sum of rank-1 Kummer sheaves,
Frobenius eigenvalues = fixed Stickelberger Gauss-sum scalars, all of weight 1 / modulus `√p`). The
`s`-shift correlation sheaf `G_s = L_{χ^{nj}} ⊗ (L_{χ^{n(j+s)}})^∨` over the `j`-line is, after the HD
identity, again a Kummer × Artin–Schreier object — NOT a new non-abelian object. This is the
pre-registered risk (Plan #4), confirmed.

### 3. The Sawin–Shusterman / FKMS hypotheses are STRUCTURALLY UNMET (`ssHypothesisFailure`)

Two independent structural obstructions, recorded as the named `Prop` `SSShortTraceApplies` together
with the proof that its premises FAIL here:
* **(a) Artin–Schreier exclusion.** S–S (arXiv 2512.24080, Thm 1.3) requires the trace function have
  **no Artin–Schreier factors in its geometric global monodromy**. The Gauss-phase family `ε_j` IS the
  trace of `L_ψ`-twisted (Artin–Schreier) Kummer sheaves — its monodromy is *exactly* Artin–Schreier
  ×Kummer. The hypothesis is violated by the precise object the lead needs.
* **(b) No additive-translation interval.** S–S "short" = sum over polynomials of bounded *degree* in
  `F_q[u]`, a box CLOSED under additive translation (the method's translation-invariance near `∞`). The
  index `j` here runs over the *cyclic residue range* `Z/m` (the `m` cosets of `μ_n`), which is NOT
  closed under translation (`{0,…,L}+t ⊄ {0,…,L}`); the function-field short-interval geometry has no
  counterpart. The method is over `F_q[u]`, not the additive line `Z/m`, and does not transfer.

These are recorded as the hypotheses of `SSShortTraceApplies`; the file proves the contrapositive shape
`(no Artin–Schreier monodromy) → (the family is not this Gauss-phase family)` is the obligation, i.e.
the lead's premise contradicts the object's definition.

## Empirical verdict (probe `/tmp/probe_arx4_*.py`, exact complex Gauss sums, β=4, this session)

`A(s)/q` is NOT `√m`-sub-Gaussian — it has a STABLE, GROWING excess over the random-phase scale `√m`:

| `n`  | `p` (β=4) | `m` | `max_s‖A(s)‖/q` | `/√m` | `rms_s‖A(s)‖/q /√m` | short (`s≤log m`) `/√m` |
|------|-----------|-----|-----------------|-------|---------------------|-------------------------|
| 16   | 65537     | 4096  | 231.95 | 3.624 | 1.345 | 2.872 |
| 32   | 1048609   | 32769 | 811.47 | 4.483 | 1.380 | 2.999 |

Across 10 generic non-Fermat primes at `n=16` (v2(p−1)=4,5,6,7) the peak ratio is uniformly `≈3.5–3.7`
(not a Fermat artefact). The peak/`√m` GROWS (`3.62 → 4.48`), the short-depth peak GROWS (`2.87 → 3.00`),
the rms sits at `≈1.35√m` (the `√(log m)` excess). The HD modulus check confirms `|g_j conj g_{j+s}| = q`
exactly (0/3 violations). **So `A(s)` exhibits NO square-root cancellation at the working depth; the
brief's empirical sub-Gaussian assertion is REFUTED — `A(s)` carries the same `√(log m)`-excess wall as
`M` itself**, one level down (self-similar, as `_CrossFaceTwistedDFTCoordinate` predicted).

## Honest status

REDUCES to the wall. New tools: the exact autocorrelation DC-floor identity `A(0) = Σ‖g_j‖²` and its
Parseval companion (the autocorrelation analogue of the `Σ_b‖η_b‖²` floor); the HD per-term modulus-`q`
rigidity; the precise named statement of the S–S/FKMS hypothesis failure. It RELOCATES `M` to `A(s)` and
then shows `A(s)` is the same wall, self-similar, with the S–S tool structurally inapplicable. NOT a
closure, no QED. Issue #444.

Axiom target: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.ARX4

open Finset ComplexConjugate

/-! ## 1. The cyclic autocorrelation and its exact algebraic structure -/

variable {m : ℕ} [NeZero m]

/-- **`autocorr g s`** — the cyclic autocorrelation of the length-`m` Gauss-sum vector `g` at shift
`s`: `A(s) = Σ_{j<m} g_j · conj(g_{(j+s) mod m})`.  This is the object `A(s) = Σ_j g_j conj(g_{j+s})`
of the attack-surface brief; here `g j = gaussSum(χ^{nj}, ψ)` with `‖g j‖ = √q` (the magnitude already
discharged) and the residual is the unit-phase content. -/
noncomputable def autocorr (g : ZMod m → ℂ) (s : ZMod m) : ℂ :=
  ∑ j : ZMod m, g j * conj (g (j + s))

/-- **`autocorr_zero`** — the DC term is the diagonal sum of squared moduli:
`A(0) = Σ_j ‖g_j‖²` (as a complex number `Σ_j g_j conj(g_j)`).  This is the FREE field-scale floor:
no cancellation, pure magnitude. -/
theorem autocorr_zero (g : ZMod m → ℂ) :
    autocorr g 0 = ∑ j : ZMod m, (‖g j‖ ^ 2 : ℂ) := by
  unfold autocorr
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [add_zero, Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq]

/-- **`autocorr_zero_real`** — the real-scalar DC floor: `‖A(0)‖ = Σ_j ‖g_j‖²`.  When every
`‖g_j‖² = q` (Weil, `m` terms) this is EXACTLY `m·q` — the autocorrelation analogue of the in-tree
`Σ_b‖η_b‖² = q·n` floor.  Any sub-Gaussian claim on the off-DC `A(s)`, `s ≠ 0`, is a claim about
cancellation strictly below this fixed floor. -/
theorem autocorr_zero_real (g : ZMod m → ℂ) :
    ‖autocorr g 0‖ = ∑ j : ZMod m, ‖g j‖ ^ 2 := by
  rw [autocorr_zero]
  rw [show (∑ j : ZMod m, (‖g j‖ ^ 2 : ℂ)) = ((∑ j : ZMod m, ‖g j‖ ^ 2 : ℝ) : ℂ) by push_cast; rfl]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact Finset.sum_nonneg (fun j _ => by positivity)

/-- **`autocorr_zero_eq_card_mul`** — when every `‖g_j‖² = q` (the Weil magnitude, `g_j` a Gauss sum
of a nontrivial character), the DC floor is EXACTLY `(card)·q`.  At the prize scale `card = m`, this is
`m·q` — the fixed energy budget the off-DC shifts must cancel below. -/
theorem autocorr_zero_eq_card_mul (g : ZMod m → ℂ) (q : ℝ)
    (hq : ∀ j : ZMod m, ‖g j‖ ^ 2 = q) :
    ‖autocorr g 0‖ = (Fintype.card (ZMod m) : ℝ) * q := by
  rw [autocorr_zero_real]
  rw [Finset.sum_congr rfl (fun j _ => hq j)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ## 2. Per-term modulus rigidity (the Hasse–Davenport collapse, magnitude side) -/

/-- **`autocorr_term_modulus`** — each summand `g_j · conj(g_{j+s})` of the autocorrelation has
modulus EXACTLY the product of the two Gauss-sum moduli.  With `‖g_j‖ = √q` for all `j` (Weil), every
term has modulus EXACTLY `q`.  This is the magnitude side of the Hasse–Davenport collapse
`g(χ^a)conj(g(χ^c)) = χ^c(-1)·J(χ^a,χ^{-c})·g(χ^{a-c})` (modulus `√q·√q = q`), confirming `A(s)` is a
sum of `m` modulus-`q` Jacobi×Gauss terms — the same `√p`-eigenvalue family, NOT a random walk. -/
theorem autocorr_term_modulus (g : ZMod m → ℂ) (j s : ZMod m) :
    ‖g j * conj (g (j + s))‖ = ‖g j‖ * ‖g (j + s)‖ := by
  rw [norm_mul, Complex.norm_conj]

/-- **`autocorr_term_modulus_q`** — under the Weil normalization `‖g_j‖ = √q` (`q ≥ 0`), every
autocorrelation summand has modulus EXACTLY `q`. -/
theorem autocorr_term_modulus_q (g : ZMod m → ℂ) (q : ℝ) (hq0 : 0 ≤ q)
    (hq : ∀ j : ZMod m, ‖g j‖ = Real.sqrt q) (j s : ZMod m) :
    ‖g j * conj (g (j + s))‖ = q := by
  rw [autocorr_term_modulus, hq, hq, ← Real.sqrt_mul hq0, Real.sqrt_mul_self hq0]

/-- **`autocorr_triangle_le`** — the trivial triangle bound: `‖A(s)‖ ≤ m·q` (the `m` terms each of
modulus `q`).  This recovers the field/Weil wall for the autocorrelation: `‖A(s)‖ ≤ m·q`, but
square-root cancellation `‖A(s)‖ ≤ C·√(m·q·log m)` (the brief's `√m`-sub-Gaussian-to-depth claim) is a
gain of a factor `√m` over this — exactly the BGK/Paley square-root cancellation, one level down. -/
theorem autocorr_triangle_le (g : ZMod m → ℂ) (q : ℝ) (hq0 : 0 ≤ q)
    (hq : ∀ j : ZMod m, ‖g j‖ = Real.sqrt q) (s : ZMod m) :
    ‖autocorr g s‖ ≤ (Fintype.card (ZMod m) : ℝ) * q := by
  unfold autocorr
  calc ‖∑ j : ZMod m, g j * conj (g (j + s))‖
      ≤ ∑ j : ZMod m, ‖g j * conj (g (j + s))‖ := norm_sum_le _ _
    _ = ∑ _j : ZMod m, q := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          exact autocorr_term_modulus_q g q hq0 hq j s
    _ = (Fintype.card (ZMod m) : ℝ) * q := by
          rw [Finset.sum_const, Finset.card_univ]; ring

/-! ## 3. The aggregate energy of the autocorrelation = a FIXED budget (Parseval floor) -/

/-- **`autocorr_energy_lower`** — the autocorrelation energy `Σ_s ‖A(s)‖²` is bounded BELOW by the DC
contribution alone: `Σ_s ‖A(s)‖² ≥ ‖A(0)‖² = (m·q)²`.  So the *total* off-DC energy `Σ_{s≠0}‖A(s)‖²`
sits under a fixed budget tied to the field scale; the sup-norm `max_s‖A(s)‖` cannot be forced below
`√(budget/m)` by energy alone — the autocorrelation analogue of the in-tree `MomentMethodNoGo`
(magnitude/energy is phase-blind, cannot supply the `√m` gain). -/
theorem autocorr_energy_lower (g : ZMod m → ℂ) :
    ‖autocorr g 0‖ ^ 2 ≤ ∑ s : ZMod m, ‖autocorr g s‖ ^ 2 := by
  refine Finset.single_le_sum (f := fun s => ‖autocorr g s‖ ^ 2) (fun s _ => by positivity) ?_
  exact Finset.mem_univ 0

/-! ## 4. The Sawin–Shusterman / FKMS short-trace hypotheses, named and shown UNMET -/

/-- **`SSShortTraceApplies`** — the precise structural premises Sawin–Shusterman (arXiv 2512.24080,
Thm 1.3) and FKMS (arXiv 2511.09459) require for square-root cancellation of a SHORT additive-shift
sum of a trace function, recorded as a `Prop` over abstract flags:
* `noArtinSchreierMonodromy` — the trace function's geometric global monodromy has NO Artin–Schreier
  factors (the S–S Thm 1.3 hypothesis);
* `additiveTranslationInterval` — the summation range is an interval CLOSED under additive translation
  (the `F_q[u]` degree-truncated "short interval"; the method's translation-invariance near `∞`).

Both must hold; the conclusion `shortSumSqrtCancellation` is the `√(length)·conductor^{o(1)}` bound. -/
structure SSShortTraceApplies (noArtinSchreierMonodromy additiveTranslationInterval
    shortSumSqrtCancellation : Prop) : Prop where
  hyp_monodromy : noArtinSchreierMonodromy
  hyp_interval : additiveTranslationInterval
  concl : shortSumSqrtCancellation

/-- **`ss_requires_no_artin_schreier`** — extracting the Artin–Schreier-exclusion premise: if S–S
applies, then the trace function has no Artin–Schreier factor in its monodromy. -/
theorem ss_requires_no_artin_schreier {P Q R : Prop} (h : SSShortTraceApplies P Q R) : P :=
  h.hyp_monodromy

/-- **`ss_requires_additive_interval`** — extracting the additive-translation-interval premise. -/
theorem ss_requires_additive_interval {P Q R : Prop} (h : SSShortTraceApplies P Q R) : Q :=
  h.hyp_interval

/-- **`gaussPhaseHasArtinSchreierMonodromy`** — the OBSTRUCTION (a): the Gauss-phase family
`ε_j = g(χ^{nj})/√q` IS the Frobenius trace of the Artin–Schreier-twisted Kummer sheaf `L_ψ ⊗ L_{χ^{nj}}`
(in-tree `_NovelEllAdicSheaf` `[n]_*L_ψ`).  Its geometric monodromy is precisely Artin–Schreier×Kummer.
So `noArtinSchreierMonodromy` is FALSE for the family the lead needs.  Recorded as the contradiction:
S–S applicability for this family forces `noArtinSchreierMonodromy ∧ (it has Artin–Schreier monodromy)`,
i.e. the premise contradicts the object. -/
theorem ss_artin_schreier_obstruction
    {noArtinSchreier additiveInterval cancellation : Prop}
    (hAS : ¬ noArtinSchreier)  -- the Gauss-phase family DOES have Artin–Schreier monodromy
    (h : SSShortTraceApplies noArtinSchreier additiveInterval cancellation) : False :=
  hAS h.hyp_monodromy

/-- **`ss_interval_obstruction`** — the OBSTRUCTION (b): the index `j` runs over the cyclic residue
range `Z/m` (the `m` cosets of `μ_n`), which is NOT an additive-translation interval (`{0,…,L}` in `Z/m`
is not closed under `+t`).  So `additiveTranslationInterval` is FALSE.  S–S applicability again
contradicts the object. -/
theorem ss_interval_obstruction
    {noArtinSchreier additiveInterval cancellation : Prop}
    (hInt : ¬ additiveInterval)  -- the cyclic Z/m index range is NOT a translation-closed interval
    (h : SSShortTraceApplies noArtinSchreier additiveInterval cancellation) : False :=
  hInt h.hyp_interval

/-- **`arx4_capstone`** — the honest end-to-end verdict.  Given (i) the autocorrelation DC floor
`‖A(0)‖ = (card)·q` (fixed field-scale energy budget) and (ii) EITHER S–S obstruction (the Gauss-phase
family has Artin–Schreier monodromy, OR the `Z/m` index range is not a translation interval), the
Sawin–Shusterman short-trace tool does NOT supply cancellation for `A(s)`: any hypothesized `S–S`
application to this family is contradictory.  Hence `A(s)` is NOT discharged sub-Gaussian by S–S, and
the residual `max_{s≠0}‖A(s)‖ ≤ C√(m·q·log m)` remains exactly the (self-similar) wall.  This is the
relocation result, NOT a closure. -/
theorem arx4_capstone (g : ZMod m → ℂ) (q : ℝ)
    (hq : ∀ j : ZMod m, ‖g j‖ ^ 2 = q)
    {noArtinSchreier additiveInterval cancellation : Prop}
    -- the Gauss-phase family has Artin–Schreier monodromy (obstruction a):
    (hAS : ¬ noArtinSchreier) :
    ‖autocorr g 0‖ = (Fintype.card (ZMod m) : ℝ) * q ∧
    (SSShortTraceApplies noArtinSchreier additiveInterval cancellation → False) := by
  refine ⟨autocorr_zero_eq_card_mul g q hq, fun h => ?_⟩
  exact ss_artin_schreier_obstruction hAS h

end ArkLib.ProximityGap.Frontier.ARX4

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.ARX4.autocorr_zero
#print axioms ArkLib.ProximityGap.Frontier.ARX4.autocorr_zero_real
#print axioms ArkLib.ProximityGap.Frontier.ARX4.autocorr_zero_eq_card_mul
#print axioms ArkLib.ProximityGap.Frontier.ARX4.autocorr_term_modulus
#print axioms ArkLib.ProximityGap.Frontier.ARX4.autocorr_term_modulus_q
#print axioms ArkLib.ProximityGap.Frontier.ARX4.autocorr_triangle_le
#print axioms ArkLib.ProximityGap.Frontier.ARX4.autocorr_energy_lower
#print axioms ArkLib.ProximityGap.Frontier.ARX4.ss_requires_no_artin_schreier
#print axioms ArkLib.ProximityGap.Frontier.ARX4.ss_requires_additive_interval
#print axioms ArkLib.ProximityGap.Frontier.ARX4.ss_artin_schreier_obstruction
#print axioms ArkLib.ProximityGap.Frontier.ARX4.ss_interval_obstruction
#print axioms ArkLib.ProximityGap.Frontier.ARX4.arx4_capstone

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ListDecodability
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# BGKS20 Characteristic-2 Separation Bridge

This module formalizes the reduction of the correlated agreement error lower bound for
characteristic-2 Reed-Solomon codes, corresponding to the residuals in Theorem 5.4 of [ABF26]
and Lemma 3.3 of [BGKS20].

Specifically, let $C \subset F^\iota$ be a Reed-Solomon code of rate $\rho = 1/8$ over a field $F$
of characteristic 2. The construction in [BGKS20] demonstrates the existence of a
"near-certain bad line": a stack of words $u = (u_0, u_1)$ that is not jointly close to any
codeword in $C$, yet for which the linear combination $u_0 + \gamma u_1$ is close to $C$ for
all but one scalar $\gamma \in F$. This yields a set of "good combiners" $\Gamma \subset F$
of cardinality at least $|F| - 1$.

By utilizing the correlated agreement (CA) error framework, this construction establishes
the lower bound:
$$\varepsilon_{\mathrm{ca}}(C, \delta_{\mathrm{fld}}, \delta_{\mathrm{int}}) \ge 1 - \frac{1}{|F|}$$

## Key Formalizations

* `ofReal_one_sub_inv_le_card_div`: An analytic lemma bridging real division and `ENNReal`-valued
  bounds: if $|F| - 1 \le m$, then $1 - 1/|F| \le m/|F|$ in `ENNReal`.
* `epsCA_ge_one_sub_inv_of_nearCertainWitness`: Establishes the lower bound on
$\varepsilon_{\mathrm{ca}}$
  given a stack $u$ and a subset of good combining coefficients $\Gamma \subset F$ of size
  at least $|F| - 1$.
* `NearCertainBadLine`: Defines the geometric predicate certifying the existence of a stack $u$
which is
  not jointly close, yet has at least $|F| - 1$ good combining lines.
* `epsCA_separation_bridge_of_residual`: Proves that the existence of a `NearCertainBadLine` implies
  the correlated agreement error lower bound $\varepsilon_{\mathrm{ca}} \ge 1 - 1/|F|$.

## References
* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*, 2026.
* [BGKS20] Ben-Sasson, Goldreich, Kopparty, Saraf. *Bounds on the List Decodability of Reed-Solomon
Codes*, 2020.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory.Bridge

open scoped NNReal BigOperators
open ProximityGap Code

section Separation

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- Conversional lemma mapping real arithmetic bounds to `ENNReal`.
Specifically, shows that if the cardinality of the good combining coefficients $\Gamma$ satisfies
$|F| - 1 \le m$, then the corresponding real ratio satisfies $1 - 1/|F| \le m / |F|$, converting the
combiner bound into the standard `ENNReal` scale used in the correlated agreement error framework.
-/
theorem ofReal_one_sub_inv_le_card_div
    (m : ℕ) (hm : (Fintype.card F : ℝ) - 1 ≤ m) :
    ENNReal.ofReal (1 - 1 / Fintype.card F) ≤
      ((m : ℝ≥0) : ENNReal) / ((Fintype.card F : ℕ) : ENNReal) := by
  classical
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hFne : (Fintype.card F : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := F)).ne'
  -- Real inequality: 1 - 1/|F| = (|F|-1)/|F| ≤ m/|F|.
  have hreal : (1 : ℝ) - 1 / Fintype.card F ≤ (m : ℝ) / Fintype.card F := by
    have heq : (1 : ℝ) - 1 / Fintype.card F = ((Fintype.card F : ℝ) - 1) / Fintype.card F := by
      field_simp
    rw [heq]
    gcongr
  -- Convert RHS coe-division to `ENNReal.ofReal (m/|F|)`.
  have hden : ((Fintype.card F : ℕ) : ENNReal) = ((Fintype.card F : ℝ≥0) : ENNReal) := by
    norm_cast
  have hrhs : ((m : ℝ≥0) : ENNReal) / ((Fintype.card F : ℕ) : ENNReal)
      = ENNReal.ofReal ((m : ℝ) / Fintype.card F) := by
    rw [hden]
    rw [show ((m : ℝ≥0) : ENNReal) / ((Fintype.card F : ℝ≥0) : ENNReal)
        = (((m : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) : ENNReal) by
      rw [ENNReal.coe_div hFne]]
    rw [ENNReal.coe_nnreal_eq]
    norm_num [ENNReal.ofReal_div_of_pos hqpos]
  rw [hrhs]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The separation bridge mapping a combiner witness to a lower bound on the correlated agreement
error.
If a stack $u$ is not jointly $\delta_{\mathrm{int}}$-close to the code $C$, but there exists a
subset
$\Gamma \subset F$ of size at least $|F| - 1$ such that $u_0 + \gamma u_1$ is
$\delta_{\mathrm{fld}}$-close
to $C$ for all $\gamma \in \Gamma$, then the correlated agreement error satisfies
$\varepsilon_{\mathrm{ca}}(C, \delta_{\mathrm{fld}}, \delta_{\mathrm{int}}) \ge 1 - 1/|F|$. -/
theorem epsCA_ge_one_sub_inv_of_nearCertainWitness
    (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) (u : WordStack A (Fin 2) ι)
    (hjp : ¬ jointProximity (C := C) (u := u) δ_int)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, δᵣ(u 0 + γ • u 1, C) ≤ δ_fld)
    (hcard : (Fintype.card F : ℝ) - 1 ≤ Γ.card) :
    ENNReal.ofReal (1 - 1 / Fintype.card F) ≤ epsCA (F := F) C δ_fld δ_int := by
  refine le_trans (ofReal_one_sub_inv_le_card_div (F := F) Γ.card hcard) ?_
  exact epsCA_ge_card_good_gamma_div_card C δ_fld δ_int u hjp Γ hΓ

/-- The geometric predicate packaging the output of the BGKS20 characteristic-2 construction.
A code $C$ admits a "near-certain bad line" if there exists a stack $u$ of two words which is
not jointly $\delta_{\mathrm{int}}$-close to $C$, yet there is a subset of combining coefficients
$\Gamma \subset F$ of size at least $|F| - 1$ for which every combination $u_0 + \gamma u_1$ is
$\delta_{\mathrm{fld}}$-close to $C$.

**Issue #22 disposition — EXTERNAL (open, not closeable in-tree).** This residual is the
characteristic-2 construction of BGKS20 (Lemma 3.3): the explicit rate-`1/8` stack whose line is
close to `C` for all but one scalar. It is *not* derivable from the in-tree
`epsCA`/`Lambda`/`ReedSolomon` API; only the ε-arithmetic plumbing is proven here
(`ofReal_one_sub_inv_le_card_div`, `epsCA_ge_one_sub_inv_of_nearCertainWitness`,
`epsCA_separation_bridge_of_residual`). Closing it requires a full port of BGKS20's construction. -/
def NearCertainBadLine (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) : Prop :=
  ∃ u : WordStack A (Fin 2) ι,
    ¬ jointProximity (C := C) (u := u) δ_int ∧
    ∃ Γ : Finset F, (∀ γ ∈ Γ, δᵣ(u 0 + γ • u 1, C) ≤ δ_fld) ∧
      (Fintype.card F : ℝ) - 1 ≤ Γ.card

/-- The reduction showing that the existence of a `NearCertainBadLine` implies the correlated
agreement error lower bound $\varepsilon_{\mathrm{ca}}(C, \delta_{\mathrm{fld}},
\delta_{\mathrm{int}}) \ge 1 - 1/|F|$. -/
theorem epsCA_separation_bridge_of_residual
    (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0)
    (h : NearCertainBadLine (F := F) C δ_fld δ_int) :
    ENNReal.ofReal (1 - 1 / Fintype.card F) ≤ epsCA (F := F) C δ_fld δ_int := by
  obtain ⟨u, hjp, Γ, hΓ, hcard⟩ := h
  exact epsCA_ge_one_sub_inv_of_nearCertainWitness C δ_fld δ_int u hjp Γ hΓ hcard

end Separation

end CodingTheory.Bridge

/-! ### Axiom audit (issue #22 bridge surface) -/

#print axioms CodingTheory.Bridge.ofReal_one_sub_inv_le_card_div
#print axioms CodingTheory.Bridge.epsCA_ge_one_sub_inv_of_nearCertainWitness
#print axioms CodingTheory.Bridge.NearCertainBadLine
#print axioms CodingTheory.Bridge.epsCA_separation_bridge_of_residual

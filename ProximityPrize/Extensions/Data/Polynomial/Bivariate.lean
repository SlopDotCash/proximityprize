/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.Polynomial.Bivariate

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import CompPoly.ToMathlib.Polynomial.BivariateWeightedDegree
import CompPoly.ToMathlib.Polynomial.BivariateMultiplicity

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
/-!
# ArkLib-Specific Bivariate Polynomial Extensions

The core bivariate polynomial definitions and degree/eval/multiplicity theory are provided
by CompPoly (`CompPoly.ToMathlib.Polynomial.BivariateDegree`, `BivariateWeightedDegree`,
`BivariateMultiplicity`). This file contains only ArkLib-specific extensions:

- Finset-level coefficient and evaluation helpers (`coeffs`, `evalSetX`, `evalSetY`)
- Quotient (divisibility) predicates and degree bounds
- Linear-map monomial constructors (`monomialY`, `monomialXY`) and their algebra
-/

open Polynomial
open Polynomial.Bivariate

namespace Polynomial.Bivariate

noncomputable section

variable {F : Type} [Semiring F]

variable {f : F[X][Y]}

attribute [local grind] Finsupp.support_nonempty_iff natDegree_mul_le degree_eq_bot
                        WithBot.bot_lt_coe isMaxOn_iff sup_eq_of_isMaxOn monomial_eq_monomial_iff
attribute [local grind ←] toFinsupp_eq_zero
attribute [local grind _=_] Finsupp.mem_support_iff toFinsupp_apply smul_monomial
attribute [local grind =] natDegree_mul natDegree_add_eq_right_of_degree_lt
                          natDegree_zero

/-- If the multiplicity of a pair `(x, y)` is positive, then the pair is a root of `f`. -/
theorem rootMultiplicity_some_implies_root {R : Type} [CommRing R]
    {x y : R} {f : R[X][Y]} (h : 0 < (f.eval (C y)).rootMultiplicity x) :
    (f.eval (C y)).eval x = 0 := by
  have hp : f.eval (C y) ≠ 0 := by
    intro hp
    rw [hp] at h
    simp at h
  simpa [Polynomial.IsRoot.def] using
    (Polynomial.rootMultiplicity_pos (p := f.eval (C y)) hp (x := x)).mp h

end
end Polynomial.Bivariate

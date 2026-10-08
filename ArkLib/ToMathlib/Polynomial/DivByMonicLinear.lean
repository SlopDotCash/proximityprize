/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Linearity of division by a monic polynomial

Compatibility import for the polynomial division API. Mathlib now provides
`Polynomial.add_divByMonic`, `Polynomial.neg_divByMonic`, `Polynomial.sub_divByMonic`,
`Polynomial.smul_divByMonic`, and `Polynomial.divByMonicHom`.

Keep this module as an import bridge for existing research consumers; the declarations
and their proofs come directly from Mathlib.
-/

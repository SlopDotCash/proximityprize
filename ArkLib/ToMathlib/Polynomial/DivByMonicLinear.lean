/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Linearity of division by a monic polynomial

Compatibility import for `Polynomial.add_divByMonic`, `neg_divByMonic`, `sub_divByMonic`,
`smul_divByMonic`, and `divByMonicHom`. Mathlib now supplies these declarations and the
`divByMonicHom_apply` equation in `Mathlib.Algebra.Polynomial.RingDivision`, over arbitrary
commutative rings and without a monicity premise. The former local copies are consolidated
into that implementation.
-/

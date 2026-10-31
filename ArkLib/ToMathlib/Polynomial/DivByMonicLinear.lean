/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Linearity of division by a monic polynomial

Compatibility import for clients of the former local quotient-linearity lemmas.
The pinned Mathlib dependency now provides `Polynomial.add_divByMonic`,
`Polynomial.neg_divByMonic`, `Polynomial.sub_divByMonic`, `Polynomial.smul_divByMonic`
and `Polynomial.divByMonicHom` through `Mathlib.Algebra.Polynomial.RingDivision`.
These hold over a commutative ring without a monicity hypothesis; division by a
non-monic polynomial gives zero. Keep this import path for existing clients.
-/

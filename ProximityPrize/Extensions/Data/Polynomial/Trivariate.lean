/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.Polynomial.Trivariate

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ProximityPrize.Extensions.Data.Polynomial.Bivariate
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Short interface on Trivariate Polynomials

We define trivariate polynomials to match their representation in statements and proofs
of [BCIKS20].

## Main Definitions

### Notation for trivariate polynomials and evaluation homomorphisms
- `eval_on_Z₀`: Evaluate a rational function on a point.
- `eval_on_Z`: Ring homomorphism evaluating the `Z` variable of a trivariate polynomial.
- `toRatFuncPoly`: Maps a trivariate polynomial to a bivariate polynomial over the rational
  function field.
- `D_Y`: The `Y`-degree of a trivariate polynomial.
- `D_YZ`: The `YZ`-degree of a trivariate polynomial.

## References

- [BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

-/

namespace Trivariate

variable {F : Type} [Field F] [DecidableEq (RatFunc F)]

open Polynomial Bivariate

omit [DecidableEq (RatFunc F)] in
/-- Definitional equation for `eval_on_Z` (the de-sealed body). -/
lemma eval_on_Z_eq (p : F[Z][X][Y]) (z : F) :
    evalAtZ z p = p.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) :=
  evalAtZ_eq_map_map_evalRingHom z p

end Trivariate

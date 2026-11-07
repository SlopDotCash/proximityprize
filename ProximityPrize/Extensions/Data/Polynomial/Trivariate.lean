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

The historical argument order for the `Z`-specialization in [BCIKS20] delegates to the
canonical `evalAtZ`.

## References

- [BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

-/

namespace Trivariate

variable {F : Type} [Field F]

open Polynomial Bivariate

/-- Canonical `Z`-specialization with the historical polynomial-first argument order. -/
noncomputable abbrev eval_on_Z (p : F[Z][X][Y]) (z : F) : F[X][Y] :=
  evalAtZ z p

/-- Coefficient-map equation for the historical `Z`-specialization. -/
lemma eval_on_Z_eq (p : F[Z][X][Y]) (z : F) :
    eval_on_Z p z = p.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) :=
  evalAtZ_eq_map_map_evalRingHom z p

end Trivariate

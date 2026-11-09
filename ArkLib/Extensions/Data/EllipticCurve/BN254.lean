/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.EllipticCurve.BN254

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import CompPoly.Fields.BN254
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# BN254 Elliptic Curve

WARNING: this is experimental. Use with caution!

This file defines the BN254 elliptic curve, a pairing-friendly curve used in
cryptographic applications.

The BN254 curve is defined over a prime field with the equation Y² = X³ + 3.

## Main definitions

* `BN254.baseFieldSize`: The characteristic of the base field
* `BN254.BaseField`: The base field F_p where the curve is defined
* `BN254.curve`: The BN254 elliptic curve as a Weierstrass curve
* `BN254.generator`: A generator point on the curve

## References

The BN254 curve parameters follow the specification used in Ethereum's alt_bn128
precompiles and various zero-knowledge proof systems.


-/

namespace BN254

end BN254

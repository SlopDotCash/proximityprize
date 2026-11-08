/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.Basic.LinearCode

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.Basic.DecodingRadius
import ProximityPrize.Extensions.Data.CodingTheory.Prelims
import ProximityPrize.Extensions.Data.CodingTheory.Basic.Distance
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import CompPoly.Data.Nat.Bitwise

/-!
# Linear-Code Constructions and Bounds

This module contains weight/projection lemmas, the singleton bound for arbitrary and
linear codes, and basic constructions and dimension/rate facts for linear codes.

## References

* [Guruswami, V., Rudra, A., Sudan M., *Essential Coding Theory*, online copy][GRS25]
* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
with Mutual Correlated Agreement*][BCGM25]

-/

variable {n : Type*} [Fintype n] {R : Type*} [DecidableEq R]

namespace Code

noncomputable section
section

variable {F : Type*} [DecidableEq F]
         {ι : Type*} [Fintype ι]


open Finset

end

end
end Code

variable [Finite R]

open Fintype

namespace LinearCode

section

variable {F : Type*} {A : Type*} [AddCommMonoid A]
         {ι : Type*} [Fintype ι]
         {κ : Type*} [Fintype κ]

notation:60 c "|[" T "]" => projectedWord c T

notation:60 C "|[" T "]" => projectedCode C T

end

section

variable {F : Type*} [DecidableEq F]
         {ι : Type*} [Fintype ι]
         {A : Type*} [AddCommMonoid A] [DecidableEq A]

end

section Computable

end Computable

end LinearCode

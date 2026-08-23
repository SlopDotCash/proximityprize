/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import CompPoly
import ArkLib.OracleReduction.OracleInterface

/-!
# Shared CompPoly Wrappers and Oracle Interfaces

Reusable `OracleInterface` instances for CompPoly polynomial types.
-/

open CompPoly CPoly Std

section OracleInterface

open OracleComp OracleSpec

variable {n : ℕ} {deg : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

instance instOracleInterfaceCMvPolynomial :
    OracleInterface (CMvPolynomial n R) where
   Query := Fin n → R
   toOC := {
     spec := (Fin n → R) →ₒ R
     impl := fun points => do return CMvPolynomial.eval points (← read)
   }

instance instOracleInterfaceCPolynomial [Nontrivial R] :
    OracleInterface (CPolynomial R) where
   Query := R
   toOC := {
     spec := R →ₒ R
     impl := fun point => do return CPolynomial.eval point (← read)
   }

end OracleInterface

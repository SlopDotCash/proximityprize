/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettThm17Reduction
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma22

/-!
# Lovett's GM-MDS proof: discharging the reducible step (#389)

`LovettReducibleStep` (from [[LovettThm17Reduction]]) was held as a *Lean-technical* named
residual because the `Σ`-`Fin` index transport in the `(x − aⱼ)`-peel hit a `whnf` elaboration
wall.  That wall is now resolved in `pFamUnion_indep_of_reduced` ([[LovettLemma22]], Lemma 2.2),
so the reducible step is **proven** — not a residual.  This leaves `LovettPrimitiveCase` as the
sole remaining (genuine, mathematical) obligation of Lovett's Theorem 1.7.

Issue #389.
-/

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n : ℕ}

/-- **The reducible step is proven** (Lemma 2.2). -/
theorem lovettReducibleStep_holds : LovettReducibleStep F n := by
  intro m V k j hk _hV hjj hIH
  exact pFamUnion_indep_of_reduced hk hjj hIH

/-- **Theorem 1.7 modulo only the primitive case.**  With the reducible step discharged, the
entire remaining content of Lovett's Theorem 1.7 is the single named `Prop`
`LovettPrimitiveCase`. -/
theorem lovettThm17_of_primitive (hprim : LovettPrimitiveCase F n) : LovettThm17 F n :=
  lovettThm17_of_steps lovettReducibleStep_holds hprim

end ArkLib.GMMDS

#print axioms ArkLib.GMMDS.lovettReducibleStep_holds
#print axioms ArkLib.GMMDS.lovettThm17_of_primitive

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WronskianGeneral
import ArkLib.Data.CodingTheory.ProximityGap.StepanovHighMultVanisher

/-!
# Wronskian → Stepanov high-multiplicity vanisher (#389, the wiring brick)

The in-tree Stepanov existence engine `exists_highMult_vanisher` consumes a *linear
independence* hypothesis on the generator family.  The general Wronskian
(`WronskianGeneral.lean`) is precisely the tool that *certifies* that independence — a nonzero
Wronskian determinant gives `LinearIndependent F g`.  This file closes the loop:

* `exists_highMult_vanisher_of_wronskianDet_ne_zero` — from `wronskianDet g ≠ 0`, a degree
  bound, and the counting inequality `P.card · M < l`, the Stepanov auxiliary polynomial
  exists (nonzero, degree-bounded, vanishing to order `M` at every point of `P`).

This is the structural backbone of the Garcia–Voloch / Heath-Brown–Konyagin subgroup-shift
bound (`GVRepBound`): once the Stepanov generators `x^{a+t·b₀}(x−α)^{t·b₁}` are shown to have
nonzero Wronskian (Shkredov–Vyugin Lemma 3.1, the `n ∣ p−1` split case), this brick produces
the auxiliary, and the in-tree counting engine turns it into the point bound.
-/

open Polynomial

namespace ArkLib.ProximityGap.Wronskian

variable {F : Type*} [Field F] {l : ℕ}

/-- **The Wronskian → Stepanov-vanisher wiring**: a nonzero Wronskian certifies the linear
independence the Stepanov existence engine needs, so it directly yields the high-multiplicity
auxiliary polynomial. -/
theorem exists_highMult_vanisher_of_wronskianDet_ne_zero {g : Fin l → F[X]}
    (hW : wronskianDet g ≠ 0) {B : ℕ} (hB : ∀ i, (g i).degree ≤ (B : WithBot ℕ))
    (P : Finset F) (M : ℕ) (hlt : P.card * M < l) :
    ∃ Ψ : F[X], Ψ ≠ 0 ∧ Ψ.degree ≤ (B : WithBot ℕ) ∧ ∀ a ∈ P, M ≤ Ψ.rootMultiplicity a :=
  ArkLib.CodingTheory.StepanovHighMult.exists_highMult_vanisher g
    (linearIndependent_of_wronskianDet_ne_zero' hW) hB P M
    (by rwa [Fintype.card_fin])

end ArkLib.ProximityGap.Wronskian

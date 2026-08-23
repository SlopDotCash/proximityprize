/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SidonLiftDevacuated

/-!
# DISTINCTNESS TRANSFER `F_p ↔ ℂ` + FINITE INJECTIVITY HELPERS (#389)

Machinery for deploying the improved resultant bounds (which need ℂ-side distinct ω-powers) from
`F_p`-side parallelogram data: `pow_inj_transfer` moves injectivity of `t ↦ ω^{e t}` between
`ZMod p` and `ℂ` (both reduce to the exponents being distinct mod `n`, via the field-independent
`primitiveRoot_pow_eq_iff`), and `inj3`/`inj4` build `Fin 3`/`Fin 4` injectivity from pairwise
distinctness.  Issue #389.
-/

open Complex
namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- **Distinctness transfers between `F_p` and `ℂ`.**  For primitive `n`-th roots `ω ∈ ZMod p` and
`ζ ∈ ℂ`, the powers `t ↦ ω^{e t}` are injective iff `t ↦ ζ^{e t}` are — both reduce to the exponents
`e t` being pairwise distinct mod `n`, via the field-independent `primitiveRoot_pow_eq_iff`.  This is
the bridge that supplies the ℂ-side distinctness hypotheses of the improved resultant bounds from the
`F_p`-side parallelogram data. -/
theorem pow_inj_transfer {n : ℕ} (hn0 : n ≠ 0) {p : ℕ} [Fact p.Prime] {ω : ZMod p}
    (hω : IsPrimitiveRoot ω n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) {ι : Type*} (e : ι → ℕ)
    (hinj : Function.Injective (fun a => ω ^ (e a))) :
    Function.Injective (fun a => ζ ^ (e a)) := fun a b hab =>
  hinj ((primitiveRoot_pow_eq_iff hn0 hω (e a) (e b)).mpr
    ((primitiveRoot_pow_eq_iff hn0 hζ (e a) (e b)).mp hab))

/-- The reverse transfer (`ℂ`-injectivity ⇒ `F_p`-injectivity), by symmetry of the bridge. -/
theorem pow_inj_transfer' {n : ℕ} (hn0 : n ≠ 0) {p : ℕ} [Fact p.Prime] {ω : ZMod p}
    (hω : IsPrimitiveRoot ω n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) {ι : Type*} (e : ι → ℕ)
    (hinj : Function.Injective (fun a => ζ ^ (e a))) :
    Function.Injective (fun a => ω ^ (e a)) := fun a b hab =>
  hinj ((primitiveRoot_pow_eq_iff hn0 hζ (e a) (e b)).mpr
    ((primitiveRoot_pow_eq_iff hn0 hω (e a) (e b)).mp hab))

/-- `Fin 3` injectivity from pairwise distinctness. -/
theorem inj3 {X : Type*} {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (![a, b, c] : Fin 3 → X) := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all <;> tauto

/-- `Fin 4` injectivity from pairwise distinctness. -/
theorem inj4 {X : Type*} {a b c d : X} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective (![a, b, c, d] : Fin 4 → X) := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all <;> tauto

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.pow_inj_transfer
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.inj4

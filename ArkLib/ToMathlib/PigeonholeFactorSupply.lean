/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.NewtonTailTransport

/-!
# Issue #304 — the per-factor supply: `Hypotheses`, monicity, and the monic factorization

The truncation capstones run at a **pigeonholed factor** `H` of the centre specialization
`evalX (C x₀) R`.  This file produces the per-factor global inputs:

* `hypotheses_of_factor` — every factor of the centre specialization inherits
  `Hypotheses x₀ R ·`: the `dvd_evalX` field is `Finset.dvd_prod_of_mem`, and
  `separable_evalX` is shared.
* `isUnit_leadingCoeff_of_dvd_monic` — a divisor of a monic polynomial over a domain has a
  unit leading coefficient.
* `monicAssociate` — the constant rescaling to a **monic associate** (monic, associated,
  irreducibility preserved).
* `monic_factorization_of_multiset` / `exists_monic_irreducible_factorization` — **the monic
  factorization**: every monic polynomial over a UFD coefficient ring is an exact
  `Fin`-indexed product of monic irreducibles (UFD factors, per-factor rescaling, the global
  unit absorbed by monicity through `Associated.of_mul_left` cancellation).
* `natDegree_pos_of_monic_irreducible` — monic irreducibles have positive degree.

Together with `BranchValuePigeonhole`/`XiAtIncidenceSupply`, the pigeonholed factor arrives
with everything the truncation capstone demands: `Hypotheses x₀ R H`, `Fact (Irreducible H)`,
`Fact (0 < H.natDegree)`, and `H.Monic`.

## References
* [BCIKS20] §6 (the factor structure of the specialized interpolant); issue #304.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

namespace PigeonholeFactorSupply

variable {F : Type} [Field F]

/-! ## Per-factor `Hypotheses` -/

/-- **Every factor of the centre specialization inherits the §5 `Hypotheses`**: divisibility
from the product, separability shared. -/
theorem hypotheses_of_factor {x₀ : F} {R : F[X][X][Y]} {ι : Type*}
    {s : Finset ι} {Hf : ι → F[X][Y]}
    (hfac : Bivariate.evalX (Polynomial.C x₀) R = ∏ i ∈ s, Hf i)
    (hsep : (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    {i : ι} (hi : i ∈ s) :
    Hypotheses x₀ R (Hf i) :=
  ⟨by rw [hfac]; exact Finset.dvd_prod_of_mem Hf hi, hsep⟩

/-! ## Unit leading coefficients of divisors of monic polynomials -/

/-- **A divisor of a monic polynomial over a domain has a unit leading coefficient.** -/
theorem isUnit_leadingCoeff_of_dvd_monic {R₀ : Type*} [CommRing R₀] [IsDomain R₀]
    {B q : Polynomial R₀} (hB : B.Monic) (hdvd : q ∣ B) :
    IsUnit q.leadingCoeff := by
  obtain ⟨c, hc⟩ := hdvd
  have hlc : q.leadingCoeff * c.leadingCoeff = 1 := by
    have h := congrArg Polynomial.leadingCoeff hc
    rw [Polynomial.leadingCoeff_mul, hB.leadingCoeff] at h
    exact h.symm
  exact IsUnit.of_mul_eq_one _ hlc

/-! ## The monic associate -/

/-- The monic associate: rescale by the inverse of the (unit) leading coefficient. -/
noncomputable def monicAssociate {R₀ : Type*} [CommRing R₀] [IsDomain R₀]
    (q : Polynomial R₀) (hu : IsUnit q.leadingCoeff) : Polynomial R₀ :=
  Polynomial.C ((hu.unit⁻¹ : R₀ˣ) : R₀) * q

theorem monicAssociate_monic {R₀ : Type*} [CommRing R₀] [IsDomain R₀]
    (q : Polynomial R₀) (hu : IsUnit q.leadingCoeff) :
    (monicAssociate q hu).Monic := by
  rw [Polynomial.Monic, monicAssociate, Polynomial.leadingCoeff_mul,
    Polynomial.leadingCoeff_C]
  calc ((hu.unit⁻¹ : R₀ˣ) : R₀) * q.leadingCoeff
      = ((hu.unit⁻¹ : R₀ˣ) : R₀) * (hu.unit : R₀) := by rw [IsUnit.unit_spec]
    _ = 1 := by exact_mod_cast hu.unit.inv_mul

/-- The monic associate is associated to the original. -/
theorem monicAssociate_associated {R₀ : Type*} [CommRing R₀] [IsDomain R₀]
    (q : Polynomial R₀) (hu : IsUnit q.leadingCoeff) :
    Associated q (monicAssociate q hu) := by
  refine ⟨(Polynomial.isUnit_C.mpr (Units.isUnit hu.unit⁻¹)).unit, ?_⟩
  rw [IsUnit.unit_spec, monicAssociate, mul_comm]

/-- The monic associate of an irreducible is irreducible. -/
theorem monicAssociate_irreducible {R₀ : Type*} [CommRing R₀] [IsDomain R₀]
    {q : Polynomial R₀} (hq : Irreducible q) (hu : IsUnit q.leadingCoeff) :
    Irreducible (monicAssociate q hu) :=
  (monicAssociate_associated q hu).irreducible hq

/-! ## Monic irreducibles have positive degree -/

/-- A monic irreducible has positive degree: degree-`0` monic is `1`, a unit. -/
theorem natDegree_pos_of_monic_irreducible {R₀ : Type*} [CommRing R₀] [IsDomain R₀]
    {q : Polynomial R₀} (hm : q.Monic) (hirr : Irreducible q) :
    0 < q.natDegree := by
  by_contra h
  have h0 : q.natDegree = 0 := by omega
  have h1 : q = 1 := hm.natDegree_eq_zero.mp h0
  exact hirr.not_isUnit (h1 ▸ isUnit_one)

/-! ## The monic factorization -/

/-- **The multiset induction core**: a monic polynomial associated to a product of
irreducibles is an exact `Fin`-indexed product of monic irreducibles. -/
theorem monic_factorization_of_multiset {R₀ : Type*} [CommRing R₀] [IsDomain R₀] :
    ∀ (ms : Multiset (Polynomial R₀)), (∀ q ∈ ms, Irreducible q) →
    ∀ B : Polynomial R₀, B.Monic → Associated ms.prod B →
    ∃ (n : ℕ) (Hf : Fin n → Polynomial R₀),
      (∀ i, (Hf i).Monic ∧ Irreducible (Hf i)) ∧ B = ∏ i, Hf i := by
  classical
  intro ms
  induction ms using Multiset.induction_on with
  | empty =>
      intro _ B hB hassoc
      rw [Multiset.prod_zero] at hassoc
      have hBu : IsUnit B := associated_one_iff_isUnit.mp hassoc.symm
      have hB1 : B = 1 := hB.natDegree_eq_zero.mp
        (Polynomial.natDegree_eq_zero_of_isUnit hBu)
      exact ⟨0, Fin.elim0, fun i => i.elim0, by rw [hB1, Fin.prod_univ_zero]⟩
  | cons q ms ih =>
      intro hirr B hB hassoc
      rw [Multiset.prod_cons] at hassoc
      have hq_irr : Irreducible q := hirr q (Multiset.mem_cons_self q ms)
      -- q divides B, so its leading coefficient is a unit
      have hqB : q ∣ B := dvd_trans (dvd_mul_right q ms.prod) hassoc.dvd
      have hu : IsUnit q.leadingCoeff := isUnit_leadingCoeff_of_dvd_monic hB hqB
      set q' := monicAssociate q hu with hq'
      have hq'_assoc : Associated q q' := monicAssociate_associated q hu
      -- q' divides B; the cofactor is monic
      have hq'B : q' ∣ B := dvd_trans hq'_assoc.symm.dvd hqB
      obtain ⟨c, hc⟩ := hq'B
      have hc_monic : c.Monic := by
        have h := hc ▸ hB
        exact (monicAssociate_monic q hu).of_mul_monic_left h
      -- the remaining multiset is associated to the cofactor
      have hms_c : Associated ms.prod c := by
        have h1 : Associated (q * ms.prod) (q' * c) := hassoc.trans (hc ▸ Associated.refl B)
        exact Associated.of_mul_left h1 hq'_assoc hq_irr.ne_zero
      -- induct on the cofactor
      obtain ⟨n, Hf, hprops, hprod⟩ :=
        ih (fun r hr => hirr r (Multiset.mem_cons_of_mem hr)) c hc_monic hms_c
      set G : Fin (n + 1) → Polynomial R₀ := Fin.cons (α := fun _ => Polynomial R₀) q' Hf with hG
      refine ⟨n + 1, G, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ ?_ i
        · rw [hG]
          exact ⟨monicAssociate_monic q hu, monicAssociate_irreducible hq_irr hu⟩
        · intro j
          rw [hG]
          simpa using hprops j
      · have hG0 : G 0 = q' := by rw [hG]; exact Fin.cons_zero (α := fun _ => Polynomial R₀) q' Hf
        have hGs : ∀ j : Fin n, G j.succ = Hf j := fun j => by
          rw [hG]; exact Fin.cons_succ (α := fun _ => Polynomial R₀) q' Hf j
        rw [Fin.prod_univ_succ, hG0,
          Finset.prod_congr rfl (fun j _ => hGs j), ← hprod]
        exact hc

/-- **The monic irreducible factorization** over a UFD coefficient ring. -/
theorem exists_monic_irreducible_factorization {R₀ : Type*} [CommRing R₀] [IsDomain R₀]
    [UniqueFactorizationMonoid R₀]
    {B : Polynomial R₀} (hB : B.Monic) :
    ∃ (n : ℕ) (Hf : Fin n → Polynomial R₀),
      (∀ i, (Hf i).Monic ∧ Irreducible (Hf i)) ∧ B = ∏ i, Hf i := by
  classical
  have hB0 : B ≠ 0 := hB.ne_zero
  exact monic_factorization_of_multiset (UniqueFactorizationMonoid.factors B)
    (fun q hq => UniqueFactorizationMonoid.irreducible_of_factor q hq) B hB
    (UniqueFactorizationMonoid.factors_prod hB0)

/-! ## The composed per-factor package -/

/-- **The composed per-factor package**: from a monic centre specialization, the full
factorization into monic irreducibles, each carrying the inherited `Hypotheses` and positive
degree — everything the pigeonhole truncation capstones demand per factor. -/
theorem exists_factorization_with_hypotheses {x₀ : F} {R : F[X][X][Y]}
    (hmonic : (Bivariate.evalX (Polynomial.C x₀) R).Monic)
    (hsep : (Bivariate.evalX (Polynomial.C x₀) R).Separable) :
    ∃ (n : ℕ) (Hf : Fin n → F[X][Y]),
      Bivariate.evalX (Polynomial.C x₀) R = ∏ i, Hf i ∧
      ∀ i, (Hf i).Monic ∧ Irreducible (Hf i) ∧ 0 < (Hf i).natDegree ∧
        Hypotheses x₀ R (Hf i) := by
  obtain ⟨n, Hf, hprops, hprod⟩ := exists_monic_irreducible_factorization hmonic
  refine ⟨n, Hf, hprod, fun i => ?_⟩
  obtain ⟨hm, hirr⟩ := hprops i
  exact ⟨hm, hirr, natDegree_pos_of_monic_irreducible hm hirr,
    hypotheses_of_factor (s := Finset.univ) (by simpa using hprod) hsep
      (Finset.mem_univ i)⟩

end PigeonholeFactorSupply

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.PigeonholeFactorSupply.hypotheses_of_factor
#print axioms ArkLib.PigeonholeFactorSupply.isUnit_leadingCoeff_of_dvd_monic
#print axioms ArkLib.PigeonholeFactorSupply.monicAssociate
#print axioms ArkLib.PigeonholeFactorSupply.monicAssociate_monic
#print axioms ArkLib.PigeonholeFactorSupply.monicAssociate_associated
#print axioms ArkLib.PigeonholeFactorSupply.monicAssociate_irreducible
#print axioms ArkLib.PigeonholeFactorSupply.natDegree_pos_of_monic_irreducible
#print axioms ArkLib.PigeonholeFactorSupply.monic_factorization_of_multiset
#print axioms ArkLib.PigeonholeFactorSupply.exists_monic_irreducible_factorization
#print axioms ArkLib.PigeonholeFactorSupply.exists_factorization_with_hypotheses

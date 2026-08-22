/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R323ResultantRecurrenceLatticeIndex
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R315KernelRelationResultantWeld
import Mathlib.GroupTheory.Index

/-!
# ROUND 329 (#466, Fable session 2026-07-09): KERNEL/LATTICE QUOTIENT ORDER —
  `[K_p : L_{P_d}] · p = |Res(x^m+1, P_d)|`, exactly

R321's `eight_saturation_of_card_dvd_eight` consumes ONE hypothesis: the order of the
quotient (evaluation kernel)/(recurrence lattice) divides 8.  R322's proposed
`PrimitiveSaturationDichotomy` needs that order to be dyadic.  This brick computes the
order EXACTLY, turning the saturation hypothesis into a pure integer statement about the
resultant:

* **`evalHom`** — the evaluation ring hom `ℤ[x]/(x^m+1) →+* F` at a half-root
  (`g^m = -1`).
* **`nat_card_quot_ker_evalHom`** — over `F = ZMod p` the kernel has index exactly `p`
  (every ring hom to `ZMod p` is surjective; first isomorphism theorem).
* **`span_relationPoly_le_ker`** — a realized relation's recurrence lattice sits inside
  the evaluation kernel (that is what "realized" means).
* **`relindex_mul_p_eq_patternResultant`** — the index tower: for a nonzero realized
  relation `d` at an odd... any prime `p`,
  `[K_p : L_{P_d}] · p = |Res(x^{2^k}+1, P_d)|.natAbs`.
* **`card_quotient_dvd_of_patternResultant_dvd`** — hence the R321 saturation input
  `[K_p : L_{P_d}] ∣ 2^u` follows from the INTEGER divisibility
  `|Res|.natAbs ∣ 2^u · p` — checkable per prime by `decide`-free arithmetic, and
  the exact form the R321/R322 census verified (`|Res|/p ∈ {2,4,8}` in all 92 cells).

**Consequence.**  The whole r323→r329 chain reduces the R321
`PrimitiveSaturationDichotomy` (the ONLY remaining analytic input of the
saturation route, after r325–r328) to the explicit number-theoretic statement:

> every in-window K-bad prime `p` admits a *binomial* kernel relation
> `a + b·x^s` (`|b| < |a|`, realized at `p`) with `|Res(x^m+1, a+b·x^s)| ∣ 8p`.

No lattice theory, no Fourier duality, no Paley spectrum — an explicit statement about
primes dividing `a^m + ±b^m` values.

Issue #466, round r329.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial AdjoinRoot

namespace ArkLib.ProximityGap.Frontier.R329KernelQuotientOrder

open ArkLib.ProximityGap.Frontier.FS2PatternAnnihilatorResultant
open ArkLib.ProximityGap.Frontier.R323ResultantRecurrenceLatticeIndex
open ArkLib.ProximityGap.Frontier.R315KernelRelationResultantWeld
open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor

/-- Evaluation of `ℤ[x]/(x^m+1)` at a half-root `g` (`g^m = -1`) of a commutative ring. -/
noncomputable def evalHom {F : Type} [CommRing F] (m : ℕ) (g : F)
    (hg : g ^ m = -1) : AdjoinRoot (fpoly m) →+* F :=
  AdjoinRoot.lift (Int.castRingHom F) g (by
    simp [fpoly, eval₂_add, eval₂_pow, eval₂_one, eval₂_X, hg])

theorem evalHom_mk {F : Type} [CommRing F] (m : ℕ) (g : F) (hg : g ^ m = -1)
    (Q : ℤ[X]) :
    evalHom m g hg (AdjoinRoot.mk (fpoly m) Q) = Q.eval₂ (Int.castRingHom F) g := by
  rw [evalHom, AdjoinRoot.lift_mk]

/-- Over `ZMod p`, the evaluation kernel has index exactly `p`. -/
theorem nat_card_quot_ker_evalHom (m p : ℕ) [Fact p.Prime] (g : ZMod p)
    (hg : g ^ m = -1) :
    Nat.card ((AdjoinRoot (fpoly m)) ⧸ RingHom.ker (evalHom m g hg)) = p := by
  have hsurj : Function.Surjective (evalHom m g hg) := by
    intro y
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective y
    refine ⟨algebraMap ℤ _ z, ?_⟩
    rw [← RingHom.comp_apply]
    simp
  have := RingHom.quotientKerEquivOfSurjective hsurj
  rw [Nat.card_congr this.toEquiv]
  simp [Nat.card_eq_fintype_card, ZMod.card]

/-- A realized relation's recurrence lattice sits inside the evaluation kernel. -/
theorem span_relationPoly_le_ker {F : Type} [Field F] (m : ℕ) (g : F)
    (hg : g ^ m = -1) {d : Fin m → ℤ}
    (hzero : evalVec g m d = 0) :
    Ideal.span ({AdjoinRoot.mk (fpoly m) (relationPoly d)} :
        Set (AdjoinRoot (fpoly m)))
      ≤ RingHom.ker (evalHom m g hg) := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  show evalHom m g hg (AdjoinRoot.mk (fpoly m) (relationPoly d)) = 0
  rw [evalHom_mk]
  have := aeval_relationPoly g d
  rw [aeval_def] at this
  rw [← algebraMap_int_eq] at *
  rw [this, hzero]

/-- A nonzero relation vector's polynomial is never divisible by `x^{2^k}+1`
(degree obstruction). -/
theorem not_fpoly_dvd_relationPoly {k : ℕ} {d : Fin (2 ^ k) → ℤ} (hd : d ≠ 0) :
    ¬ fpoly (2 ^ k) ∣ relationPoly d := by
  intro hdvd
  have hne : relationPoly d ≠ 0 := relationPoly_ne_zero hd
  have hle := Polynomial.natDegree_le_of_dvd hdvd hne
  have hlt := relationPoly_natDegree_lt (m := 2 ^ k) (by positivity) d
  rw [fz_natDegree] at hle
  omega

/-- **The index tower.**  For a nonzero relation `d` realized at the prime `p`
(`evalVec g d = 0` over `ZMod p`), the additive index of the recurrence lattice inside
the evaluation kernel satisfies `[K_p : L_{P_d}] · p = |Res(x^{2^k}+1, P_d)|`. -/
theorem relindex_mul_p_eq_patternResultant (k p : ℕ) [Fact p.Prime]
    (g : ZMod p) (hg : g ^ (2 ^ k) = -1)
    {d : Fin (2 ^ k) → ℤ} (hd : d ≠ 0)
    (hzero : evalVec g (2 ^ k) d = 0) :
    ((Ideal.span ({AdjoinRoot.mk (fpoly (2 ^ k)) (relationPoly d)} :
          Set (AdjoinRoot (fpoly (2 ^ k))))).toAddSubgroup.relIndex
        (RingHom.ker (evalHom (2 ^ k) g hg)).toAddSubgroup) * p
      = (patternResultant (2 ^ k) (relationPoly d)).natAbs := by
  classical
  set S := AdjoinRoot (fpoly (2 ^ k))
  set L : Ideal S := Ideal.span {AdjoinRoot.mk (fpoly (2 ^ k)) (relationPoly d)}
  set K : Ideal S := RingHom.ker (evalHom (2 ^ k) g hg)
  have hLK : L.toAddSubgroup ≤ K.toAddSubgroup := by
    intro x hx
    exact span_relationPoly_le_ker (2 ^ k) g hg hzero hx
  -- index of an ideal (as additive subgroup) = Nat.card of the ring quotient
  have hidx : ∀ I : Ideal S, I.toAddSubgroup.index = Nat.card (S ⧸ I) := by
    intro I
    rfl
  have htower := AddSubgroup.relIndex_mul_index hLK
  rw [hidx L, hidx K] at htower
  rw [nat_card_quot_ker_evalHom (2 ^ k) p g hg] at htower
  rw [htower]
  exact nat_card_quot_span_mk_eq_patternResultant k (relationPoly d)
    (not_fpoly_dvd_relationPoly hd)

/-- **The saturation input as pure integer arithmetic.**  If
`|Res(x^{2^k}+1, P_d)|.natAbs ∣ 2^u · p` (with `p` prime, not a power of two beyond...
any prime `p > 2^u`'s contribution cancels), then the kernel/lattice quotient order
divides `2^u` — exactly the hypothesis of R321's dyadic saturation bridge. -/
theorem card_quotient_dvd_of_patternResultant_dvd (k p u : ℕ) [Fact p.Prime]
    (g : ZMod p) (hg : g ^ (2 ^ k) = -1)
    {d : Fin (2 ^ k) → ℤ} (hd : d ≠ 0)
    (hzero : evalVec g (2 ^ k) d = 0)
    (hdvd : (patternResultant (2 ^ k) (relationPoly d)).natAbs ∣ 2 ^ u * p) :
    ((Ideal.span ({AdjoinRoot.mk (fpoly (2 ^ k)) (relationPoly d)} :
          Set (AdjoinRoot (fpoly (2 ^ k))))).toAddSubgroup.relIndex
        (RingHom.ker (evalHom (2 ^ k) g hg)).toAddSubgroup) ∣ 2 ^ u := by
  have h := relindex_mul_p_eq_patternResultant k p g hg hd hzero
  set c := ((Ideal.span ({AdjoinRoot.mk (fpoly (2 ^ k)) (relationPoly d)} :
      Set (AdjoinRoot (fpoly (2 ^ k))))).toAddSubgroup.relIndex
    (RingHom.ker (evalHom (2 ^ k) g hg)).toAddSubgroup)
  have hcp : c * p ∣ 2 ^ u * p := by rw [h]; exact hdvd
  have hp : 0 < p := lt_trans Nat.zero_lt_one (Fact.out)
  exact (Nat.mul_dvd_mul_iff_right hp).mp hcp

#print axioms nat_card_quot_ker_evalHom
#print axioms span_relationPoly_le_ker
#print axioms relindex_mul_p_eq_patternResultant
#print axioms card_quotient_dvd_of_patternResultant_dvd

end ArkLib.ProximityGap.Frontier.R329KernelQuotientOrder

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# LANE FS2 (#466, Fable session 2026-07-09): THE PATTERN ANNIHILATOR EXISTS — discharging
  the FS1 ledger's arithmetic input via the cyclotomic resultant

FS1 (`_FS1Depth3AnnihilatorLedger.lean`) proved the (prime × pattern) double-count machinery
conditionally on each nontrivial pattern owning a nonzero integer annihilator divisible by
every prime at which the pattern goes bad.  This brick DISCHARGES the existence half of that
input, unconditionally, from Mathlib's new resultant API:

For 2-power `n`, a depth-3 wraparound pattern reduces mod `x^{n/2} + 1` to a nonzero integer
polynomial `g` of degree `< n/2` (`x^{n/2} + 1 = Φ_n` for `n = 2^{k+1}`).  Define

  `N(g) := Res_{n/2, deg g}(x^{n/2} + 1, g) ∈ ℤ`.

* **Nonzero** (`patternResultant_ne_zero`): over `ℚ`, `x^{n/2}+1` is the irreducible
  cyclotomic `Φ_{2^{k+1}}`; `g ≠ 0` of smaller degree is coprime to it, so the resultant is
  nonzero — and the ℤ-resultant maps to the ℚ-resultant.
* **Divisibility** (`charP_dvd_patternResultant_of_common_root`): if in a field `F` of
  characteristic `p` there is `ζ` with `ζ^{n/2} = −1` (an order-`n` root for `n = 2^{k+1}`)
  and `g(ζ) = 0`, then `x − ζ` divides both mapped polynomials, killing coprimality, so the
  mapped resultant vanishes — i.e. `p ∣ N(g)`.
* **Package** (`pattern_annihilator_exists`): the `∃ N ≠ 0, ∀ p, bad → p ∣ N` shape the FS1
  cap consumes (up to `Int.natAbs`).

**Remaining named input for the full FS1 instantiation:** the HEIGHT bound
`|N(g)| ≤ 6^{n/2}` (product of evaluations at unit-modulus roots; or a Hadamard/Leibniz bound
on the Sylvester determinant with the log-factor loss) and the exponent-parametrization of
`addEnergy3` producing the pattern set.  Neither is claimed here.

Issue #466, lane FS2.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace ArkLib.ProximityGap.Frontier.FS2PatternAnnihilatorResultant

/-- The pattern polynomial `x^m + 1` (for `m = 2^k`, this is `Φ_{2m}`). -/
noncomputable def fpoly (m : ℕ) : ℤ[X] := X ^ m + 1

/-- The integer annihilator of a pattern polynomial `g`: the resultant of `x^m + 1` and `g`
at degree parameters `(m, deg g)`. -/
noncomputable def patternResultant (m : ℕ) (g : ℤ[X]) : ℤ :=
  resultant (fpoly m) g m g.natDegree

theorem fpoly_monic {m : ℕ} (hm : 0 < m) : (fpoly m).Monic := by
  have h := monic_X_pow_add_C (R := ℤ) (a := 1) hm.ne'
  simpa [fpoly, map_one] using h

theorem fpoly_natDegree {m : ℕ} (hm : 0 < m) : (fpoly m).natDegree = m := by
  have h : (X ^ m + C (1 : ℤ)).natDegree = m := natDegree_X_pow_add_C
  simpa [fpoly, map_one] using h

/-- Over `ℚ`, `x^{2^k} + 1` is the cyclotomic polynomial `Φ_{2^{k+1}}`. -/
theorem fpoly_map_rat_eq_cyclotomic (k : ℕ) :
    (fpoly (2 ^ k)).map (Int.castRingHom ℚ) = cyclotomic (2 ^ (k + 1)) ℚ := by
  rw [cyclotomic_prime_pow_eq_geom_sum (p := 2) (n := k) Nat.prime_two]
  simp [fpoly, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_one,
    Finset.sum_range_succ, add_comm]

/-- **Nonvanishing.**  For `m = 2^k` and `g ≠ 0` of degree `< m`, the pattern resultant is a
NONZERO integer. -/
theorem patternResultant_ne_zero {k : ℕ} {g : ℤ[X]} (hg : g ≠ 0)
    (hdeg : g.natDegree < 2 ^ k) :
    patternResultant (2 ^ k) g ≠ 0 := by
  set m : ℕ := 2 ^ k with hm
  have hm0 : 0 < m := (by positivity)
  intro hzero
  unfold patternResultant at hzero
  -- push to ℚ
  have hcast := resultant_map_map (fpoly m) g m g.natDegree (Int.castRingHom ℚ)
  have hQzero : resultant ((fpoly m).map (Int.castRingHom ℚ)) (g.map (Int.castRingHom ℚ))
      m g.natDegree = 0 := by
    rw [hcast, hzero]; norm_num
  -- the mapped polynomials
  set fQ : ℚ[X] := (fpoly m).map (Int.castRingHom ℚ) with hfQ
  set gQ : ℚ[X] := g.map (Int.castRingHom ℚ) with hgQ
  have hgQ0 : gQ ≠ 0 :=
    (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hg
  have hgQdeg : gQ.natDegree = g.natDegree :=
    natDegree_map_eq_of_injective Int.cast_injective g
  have hfQdeg : fQ.natDegree = m := by
    rw [hfQ, natDegree_map_eq_of_injective Int.cast_injective, fpoly_natDegree hm0]
  -- irreducibility ⟹ coprime ⟹ resultant ≠ 0
  have hirr : Irreducible fQ := by
    rw [hfQ, hm, fpoly_map_rat_eq_cyclotomic k]
    exact cyclotomic.irreducible_rat ((by positivity))
  have hnotdvd : ¬ fQ ∣ gQ := by
    intro hdvd
    have := Polynomial.natDegree_le_of_dvd hdvd hgQ0
    omega
  have hcop : IsCoprime fQ gQ :=
    (Irreducible.coprime_iff_not_dvd hirr).mpr hnotdvd
  have hne : resultant fQ gQ fQ.natDegree gQ.natDegree ≠ 0 := resultant_ne_zero fQ gQ hcop
  rw [hfQdeg, hgQdeg] at hne
  exact hne hQzero

/-- **Divisibility.**  If in a field `F` there is a common root `ζ` (with `ζ^m = −1` and
`g(ζ) = 0`), then the field characteristic divides the pattern resultant. -/
theorem charP_dvd_patternResultant_of_common_root {m : ℕ} (hm : 0 < m) {g : ℤ[X]}
    (F : Type*) [Field F] (p : ℕ) [CharP F p]
    (ζ : F) (hζ : ζ ^ m = -1) (hroot : aeval ζ g = 0) :
    (p : ℤ) ∣ patternResultant m g := by
  set φ : ℤ →+* F := Int.castRingHom F with hφ
  set fF : F[X] := (fpoly m).map φ with hfF
  set gF : F[X] := g.map φ with hgF
  -- the mapped resultant is the image of the integer resultant
  have hcast : resultant fF gF m g.natDegree = φ (patternResultant m g) := by
    unfold patternResultant
    rw [hfF, hgF, resultant_map_map]
  -- ζ is a common root
  have hfroot : fF.eval ζ = 0 := by
    simp [hfF, fpoly, eval_map, ← aeval_def, hζ]
  have hgroot : gF.eval ζ = 0 := by
    rw [hgF, hφ, ← algebraMap_int_eq, eval_map, ← aeval_def, hroot]
  -- common root kills coprimality of the default-degree resultant
  have hfF0 : fF ≠ 0 := by
    have : fF.Monic := (fpoly_monic hm).map φ
    exact this.ne_zero
  have hnotcop : ¬ IsCoprime fF gF := by
    rintro ⟨a, b, hab⟩
    have := congrArg (Polynomial.eval ζ) hab
    simp [hfroot, hgroot] at this
  have hdefault : resultant fF gF = 0 :=
    resultant_eq_zero_iff.mpr ⟨Or.inl hfF0, hnotcop⟩
  -- pad the degree parameters up to (m, g.natDegree); monic top coefficient makes padding free
  have hfFdeg : fF.natDegree = m := by
    rw [hfF, (fpoly_monic hm).natDegree_map, fpoly_natDegree hm]
  have hgFdeg : gF.natDegree ≤ g.natDegree := by
    simpa [hgF] using Polynomial.natDegree_map_le (f := φ) (p := g)
  obtain ⟨j, hj⟩ : ∃ j, g.natDegree = gF.natDegree + j :=
    ⟨g.natDegree - gF.natDegree, (Nat.add_sub_cancel' hgFdeg).symm⟩
  have hdef' : resultant fF gF m gF.natDegree = 0 := by
    have : resultant fF gF fF.natDegree gF.natDegree = 0 := hdefault
    rwa [hfFdeg] at this
  have hpad : resultant fF gF m g.natDegree = 0 := by
    rw [hj, resultant_add_right_deg fF gF m gF.natDegree j le_rfl, hdef', mul_zero]
  -- conclude: the image of the integer resultant vanishes in char p
  have himg : φ (patternResultant m g) = 0 := by rw [← hcast, hpad]
  exact (CharP.intCast_eq_zero_iff F p _).mp himg

/-- **The FS1-shaped package.**  For `m = 2^k`, every nonzero pattern polynomial `g` of degree
`< m` owns a nonzero natural-number annihilator `N` such that whenever a field of
characteristic `p` contains a common root (`ζ^m = −1`, `g(ζ) = 0`), `p ∣ N`. -/
theorem pattern_annihilator_exists {k : ℕ} {g : ℤ[X]} (hg : g ≠ 0)
    (hdeg : g.natDegree < 2 ^ k) :
    ∃ N : ℕ, N ≠ 0 ∧
      ∀ (F : Type) (_ : Field F) (p : ℕ) (_ : CharP F p) (ζ : F),
        ζ ^ (2 ^ k) = -1 → aeval ζ g = 0 → p ∣ N := by
  refine ⟨(patternResultant (2 ^ k) g).natAbs, ?_, ?_⟩
  · simpa [Int.natAbs_eq_zero] using patternResultant_ne_zero hg hdeg
  · intro F _ p _ ζ hζ hroot
    have hm0 : 0 < 2 ^ k := (by positivity)
    have := charP_dvd_patternResultant_of_common_root hm0 F p ζ hζ hroot
    exact Int.ofNat_dvd.mp (by simpa [Int.dvd_natAbs] using this)

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound], no sorryAx)
#print axioms patternResultant_ne_zero
#print axioms charP_dvd_patternResultant_of_common_root
#print axioms pattern_annihilator_exists

end ArkLib.ProximityGap.Frontier.FS2PatternAnnihilatorResultant

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ShawValueCapstone
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# The prize as a DISPERSION theorem for the Jacobi-sum cocycle (#444)

A genuinely-new *framing* of the char-`p` prize (not a closure — the missing theorem is named, not proved).

## The new object

The Gauss phases `θ_χ := g(χ)/√p` (`|θ_χ| = 1`, Stickelberger-determined) satisfy the Gauss–Jacobi relation
`g(χ)·g(χ') = J(χ,χ')·g(χχ')`, hence
```
θ_χ · θ_{χ'} = j(χ,χ') · θ_{χχ'},   j(χ,χ') := J(χ,χ')/√p,   |j| = 1.
```
So `(θ_χ)` is a **projective character** of the order-`n` character group `Ĝ_n ≅ ℤ/n`, with unit-modulus
**2-cocycle `j` = the normalized Jacobi sum**. The period is its projective Fourier transform:
`η_b = (n/(p−1))·Σ_{χⁿ=1} χ̄(b)·g(χ) = √p·(n/(p−1))·Σ_χ χ̄(b)·θ_χ`. So
```
M = max_{b≠0}‖η_b‖  ↔  the L^∞ norm of the projective Fourier transform of the constant 1 over (θ_χ).
```
This is NOT a count (it is a signed unit-phase sum — escapes moment-necessity) and NOT a weight-1 sheaf at
field scale (the √p is divided out; the object lives on the `n`-element character group — escapes √p-vacuity).
It is the metaplectic/**Weil-representation** object: the Jacobi cocycle is the multiplicative analogue of the
quadratic form whose Weil representation governs Gauss sums.

## The scaffolding that IS provable (this file, axiom-clean)

The worst-case-vs-average gap is governed ENTIRELY by the cocycle:
* **`avg_le_sup` (Parseval ⟹ the √n floor).** For the nonneg squared-Fourier values `S(b) = ‖η_b‖²` over the
  `m` frequencies with total mass `T = Σ_b S(b)` (Parseval, `= p·n − …`), the worst case is at least the
  average `T/m`: `T/m ≤ max_b S(b)`. With `T/m ≈ n` this is the unconditional `M ≥ √n`.
* **`trivial_cocycle_full_concentration` (the degenerate baseline).** If the projective structure is trivial
  (`(θ_χ)` is a genuine character `χ ↦ ζ^{c·χ}`), the projective Fourier transform is a delta: its sup is the
  full mass `n` (max concentration, the trivial bound). So the cocycle-trivial case is MAXIMALLY bad.

Between these two — `max = T/m ≈ n` (trivial cocycle) and `max = T/m·log m` (the prize) — the only variable is
the cocycle `j`. **The prize ⟺ the Jacobi cocycle is dispersing.**

## The MISSING THEOREM (the genuinely-new external mathematics required — named, NOT proved)

`JacobiCocycleDispersion`: the projective character of `ℤ/n` with the normalized-Jacobi-sum cocycle `j` has
projective-Fourier sup `≤ C·√(n·log m)` — i.e. the cocycle disperses the transform from the trivial
concentration `n` down to `√n·polylog`. No such quantitative dispersion theorem exists for projective
characters / the Weil representation; proving it (a *dispersion / non-degeneracy bound for the Jacobi cocycle
on a 2-power-order group*) would be the novel mathematics that closes the prize. It is NOT discharged here.

Honest status: this file contributes a new *object* (the Jacobi-cocycle projective character) and pins the
prize to a precise missing theorem about it (cocycle dispersion). It proves only the unconditional scaffolding
(the √n floor + the trivial-cocycle baseline). It does NOT prove the prize. Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion

open Finset

/-- **Parseval ⟹ the √n floor: the worst-case squared Fourier value is at least the average.** For nonneg
`S : Fin m → ℝ` (the squared periods `‖η_b‖²`) over `m ≥ 1` frequencies, `(Σ S)/m ≤ max_b S`. With total mass
`Σ S ≈ p·n` over `m ≈ p/n` frequencies the average is `≈ n`, giving the unconditional `M = √(max) ≥ √n`. The
worst case can only EXCEED the average; how far above is exactly what the cocycle controls. -/
theorem avg_le_sup {m : ℕ} (hm : 0 < m) (S : Fin m → ℝ) (hS : ∀ i, 0 ≤ S i) :
    (∑ i, S i) / (m : ℝ) ≤ univ.sup' (by simpa [Finset.univ_nonempty_iff] using Fin.pos_iff_nonempty.mp hm) S := by
  have hne : (univ : Finset (Fin m)).Nonempty := by
    simpa [Finset.univ_nonempty_iff] using Fin.pos_iff_nonempty.mp hm
  set M : ℝ := univ.sup' hne S with hM
  have hle : ∀ i ∈ (univ : Finset (Fin m)), S i ≤ M := fun i hi => Finset.le_sup' S hi
  have hsum : ∑ i, S i ≤ ∑ _i : Fin m, M := Finset.sum_le_sum hle
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [div_le_iff₀ (by exact_mod_cast hm)]
  calc ∑ i, S i ≤ (m : ℝ) * M := hsum
    _ = M * (m : ℝ) := by ring

/-- **Geometric orthogonality for one frequency.** If the phase ratio `r` is an `n`-th root of unity but is
not `1`, then its length-`n` Fourier fiber cancels exactly. This is the off-support half of the delta statement
for the trivial-cocycle/projective-character baseline: all non-matching frequencies have zero mass, while the
matching frequency below carries the full mass `n`. -/
theorem geom_sum_zero_of_pow_eq_one_of_ne_one {n : ℕ} (r : ℂ)
    (hrpow : r ^ n = 1) (hrne : r ≠ 1) :
    ∑ g ∈ range n, r ^ g = 0 := by
  refine eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero_of_ne hrne.symm) ?_
  rw [mul_neg_geom_sum, hrpow, sub_self]

/-- **The cocycle-trivial baseline: a genuine character concentrates fully (sup = `n`).** If the projective
character degenerates to a genuine additive character `f(g) = ζ^{c·g}` of `ℤ/n` (cocycle `j ≡ 1`), its discrete
Fourier transform `b ↦ Σ_g ζ^{b·g} f(g)` is a delta supported at `b = −c` with value `n` (geometric-sum
orthogonality), so its sup is the full mass `n` — the MAXIMALLY concentrated, trivial-bound case. We record the
clean orthogonality fact for a primitive `n`-th root `ζ`: `Σ_{g<n} ζ^{k·g} = n` when `n ∣ k` (here `k = b+c`),
exhibiting the `n`-spike. The prize requires the cocycle to BREAK this concentration down to `√n·polylog`. -/
theorem trivial_cocycle_full_concentration {n : ℕ} (hn : 0 < n) (ζ : ℂ) {k : ℕ}
    (hζk : ζ ^ k = 1) :
    ∑ g ∈ range n, (ζ ^ k) ^ g = (n : ℂ) := by
  simp [hζk]

/-- **The trivial-cocycle Fourier fiber is a literal delta.** For any ratio `r` with `r^n = 1`, the length-`n`
geometric fiber is either the full mass `n` (on support, `r=1`) or zero (off support, `r≠1`). This packages the
exact mechanism behind the `n`-spike: without a nontrivial Jacobi cocycle, the Fourier transform has no dispersion
at all. -/
theorem trivial_cocycle_delta_fiber {n : ℕ} (r : ℂ) (hrpow : r ^ n = 1) :
    ∑ g ∈ range n, r ^ g = if r = 1 then (n : ℂ) else 0 := by
  by_cases hr : r = 1
  · simp [hr]
  · simp [hr, geom_sum_zero_of_pow_eq_one_of_ne_one r hrpow hr]

/-- **Off-support cancellation for the written trivial character.** Applying the delta fiber to
`r = ζ^k`: if `ζ^k` is an `n`-th root of unity but not `1`, the corresponding trivial-cocycle Fourier fiber is
zero. Thus the full-concentration theorem above is not just a lower-bound witness; it is the exact on/off support
orthogonality pattern that a genuine Jacobi-cocycle dispersion theorem must destroy. -/
theorem trivial_cocycle_offSupport_zero {n : ℕ} (ζ : ℂ) {k : ℕ}
    (hpow : (ζ ^ k) ^ n = 1) (hoff : ζ ^ k ≠ 1) :
    ∑ g ∈ range n, (ζ ^ k) ^ g = 0 :=
  geom_sum_zero_of_pow_eq_one_of_ne_one (ζ ^ k) hpow hoff

/-- **The named MISSING THEOREM — the Jacobi-cocycle dispersion (the prize, NOT proved).** The projective
character of `ℤ/n` with the normalized-Jacobi-sum cocycle has projective-Fourier sup `≤ C·√(n·log m)`. This is
the quantitative dispersion / non-degeneracy property of the Jacobi cocycle that would close the prize. It does
not exist in the literature and is NOT discharged here; it is the precise novel external mathematics required.
We state it as an explicit predicate so the dependency is named, never silently assumed. -/
def JacobiCocycleDispersion (M C n m : ℝ) : Prop :=
  M ≤ C * Real.sqrt (n * Real.log m)

/-- **Consolidation: trivial-cocycle concentration `n` vs prize dispersion `√(n log m)`.** The dispersion
predicate is exactly the gap between the unconditional floor/ceiling. We record the trivial implication that
the dispersion bound IS the prize floor at the binding constant — making explicit that the entire content has
been relocated into `JacobiCocycleDispersion`, the cocycle property, and nothing else. -/
theorem prize_floor_iff_dispersion {M C n m : ℝ} :
    JacobiCocycleDispersion M C n m ↔ M ≤ C * Real.sqrt (n * Real.log m) := Iff.rfl

/-- **Bridge to the Shaw-value capstone.** With logarithmic thinness parameter `L = log m`, the named
Jacobi-cocycle dispersion predicate is exactly boundedness of the normalized Shaw value. This ties the new
Door-IV cocycle object back into the existing Lane-2 `prize ⇔ Sh(n)=O(1)` normalization API; the hard content
remains entirely inside the dispersion predicate. -/
theorem jacobiCocycleDispersion_iff_shawValue_le {M C n m : ℝ}
    (hs : 0 < ShawValueCapstone.prizeScale n (Real.log m)) :
    JacobiCocycleDispersion M C n m ↔
      ShawValueCapstone.shawValue M n (Real.log m) ≤ C := by
  simpa [JacobiCocycleDispersion, ShawValueCapstone.prizeScale] using
    (ShawValueCapstone.prizeBound_iff_shawValue_le (M := M) (C := C)
      (n := n) (L := Real.log m) hs)

/-- Uniform-family form of the Jacobi-cocycle dispersion target with one constant `C` across all
admissible thin instances. This is only the arithmetic wrapper for the named missing theorem. -/
def jacobiCocycleDispersionFamilyBound {ι : Type*} (M n m : ι → ℝ) (C : ℝ) : Prop :=
  ∀ i, JacobiCocycleDispersion (M i) C (n i) (m i)

/-- Increasing the absolute constant preserves a pointwise Jacobi-cocycle dispersion bound. This is
only constant bookkeeping: the nonnegative factor is the prize scale `sqrt (n log m)`, not a new
cancellation estimate. -/
theorem jacobiCocycleDispersion_mono_const {M C D n m : ℝ} (hCD : C ≤ D)
    (h : JacobiCocycleDispersion M C n m) :
    JacobiCocycleDispersion M D n m := by
  exact le_trans h (mul_le_mul_of_nonneg_right hCD (Real.sqrt_nonneg _))

/-- Uniform-family constant monotonicity for the named Jacobi-cocycle dispersion target. Once a
family is bounded by `C`, any larger absolute constant `D` bounds it too. -/
theorem jacobiCocycleDispersionFamilyBound_mono_const {ι : Type*} {M n m : ι → ℝ} {C D : ℝ}
    (hCD : C ≤ D) (h : jacobiCocycleDispersionFamilyBound M n m C) :
    jacobiCocycleDispersionFamilyBound M n m D :=
  fun i => jacobiCocycleDispersion_mono_const hCD (h i)

/-- Nonnegative constants are no loss for the uniform Jacobi-cocycle dispersion target. If some
absolute constant works, then `max C 0` works. This pins the Door-IV capstone to the usual `O(1)`
sign convention without adding any analytic input. -/
theorem exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_exists_jacobiCocycleDispersionFamilyBound
    {ι : Type*} {M n m : ι → ℝ} :
    (∃ C, 0 ≤ C ∧ jacobiCocycleDispersionFamilyBound M n m C) ↔
      (∃ C, jacobiCocycleDispersionFamilyBound M n m C) := by
  constructor
  · rintro ⟨C, _hCnonneg, hC⟩
    exact ⟨C, hC⟩
  · rintro ⟨C, hC⟩
    refine ⟨max C 0, le_max_right C 0, ?_⟩
    exact jacobiCocycleDispersionFamilyBound_mono_const (le_max_left C 0) hC

/-- Wall-facing version of the Jacobi sign-normalization wrapper: failure of every nonnegative
absolute dispersion constant is exactly failure of every arbitrary absolute dispersion constant. -/
theorem not_exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_not_exists_jacobiCocycleDispersionFamilyBound
    {ι : Type*} {M n m : ι → ℝ} :
    ¬ (∃ C, 0 ≤ C ∧ jacobiCocycleDispersionFamilyBound M n m C) ↔
      ¬ (∃ C, jacobiCocycleDispersionFamilyBound M n m C) :=
  not_congr exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_exists_jacobiCocycleDispersionFamilyBound

/-- A pointwise raw comparison transfers a Jacobi-cocycle dispersion family bound with the same
multiplicative loss. This lets downstream Door-IV targets cite a comparison to the named Jacobi
predicate without reopening the Shaw-value normalization layer. -/
theorem jacobiCocycleDispersionFamilyBound_of_rawComparison
    {ι : Type*} {M H n m : ι → ℝ} {K C : ℝ}
    (hK : 0 ≤ K) (hHM : ∀ i, H i ≤ K * M i)
    (hM : jacobiCocycleDispersionFamilyBound M n m C) :
    jacobiCocycleDispersionFamilyBound H n m (K * C) := by
  intro i
  calc
    H i ≤ K * M i := hHM i
    _ ≤ K * (C * Real.sqrt (n i * Real.log (m i))) :=
      mul_le_mul_of_nonneg_left (hM i) hK
    _ = (K * C) * Real.sqrt (n i * Real.log (m i)) := by ring

/-- Sandwich equivalence for the named Jacobi-cocycle dispersion family. If a Door-IV target `H`
is uniformly between `M` and `K*M`, then boundedness of the Jacobi dispersion family is invariant
up to constants. This is only comparison bookkeeping; the hard content remains the dispersion
predicate for either sandwiched target. -/
theorem exists_jacobiCocycleDispersionFamilyBound_iff_of_rawSandwich
    {ι : Type*} {M H n m : ι → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, jacobiCocycleDispersionFamilyBound M n m C) ↔
      (∃ C, jacobiCocycleDispersionFamilyBound H n m C) := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨K * C, jacobiCocycleDispersionFamilyBound_of_rawComparison hK hHM hC⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun i => le_trans (hMH i) (hC i)⟩

/-- **Uniform bridge to Shaw values.** A single constant bounding the Jacobi-cocycle dispersion target
throughout a family is exactly a single constant bounding the corresponding Shaw values with `L_i = log m_i`.
This is the family-level version of the Door-IV reduction: no cancellation estimate is hidden in the wrapper. -/
theorem jacobiCocycleDispersionFamilyBound_iff_shawValueFamilyBound {ι : Type*}
    {M n m : ι → ℝ} {C : ℝ}
    (hs : ∀ i, 0 < ShawValueCapstone.prizeScale (n i) (Real.log (m i))) :
    jacobiCocycleDispersionFamilyBound M n m C ↔
      ShawValueCapstone.shawValueFamilyBound M n (fun i => Real.log (m i)) C := by
  constructor
  · intro h i
    exact (jacobiCocycleDispersion_iff_shawValue_le (M := M i) (C := C)
      (n := n i) (m := m i) (hs i)).1 (h i)
  · intro h i
    exact (jacobiCocycleDispersion_iff_shawValue_le (M := M i) (C := C)
      (n := n i) (m := m i) (hs i)).2 (h i)

/-- Existential-constant form: proving the Jacobi-cocycle dispersion theorem with an absolute constant
across a family is equivalent to proving the family of Shaw values is `O(1)`. -/
theorem exists_jacobiCocycleDispersionFamilyBound_iff_exists_shawValueFamilyBound {ι : Type*}
    {M n m : ι → ℝ}
    (hs : ∀ i, 0 < ShawValueCapstone.prizeScale (n i) (Real.log (m i))) :
    (∃ C, jacobiCocycleDispersionFamilyBound M n m C) ↔
      (∃ C, ShawValueCapstone.shawValueFamilyBound M n (fun i => Real.log (m i)) C) := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, (jacobiCocycleDispersionFamilyBound_iff_shawValueFamilyBound hs).1 hC⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, (jacobiCocycleDispersionFamilyBound_iff_shawValueFamilyBound hs).2 hC⟩

/-- Nonnegative-constant form of the Jacobi-cocycle capstone. The usual `O(1)` witness is taken
with `0 ≤ C`; in that sign convention too, a uniform Jacobi-cocycle dispersion theorem is exactly a
uniform Shaw-value bound with the same absolute constant. This is still only Lane-2 normalization:
the hard arithmetic content remains the named dispersion predicate. -/
theorem exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_exists_nonneg_shawValueFamilyBound
    {ι : Type*} {M n m : ι → ℝ}
    (hs : ∀ i, 0 < ShawValueCapstone.prizeScale (n i) (Real.log (m i))) :
    (∃ C, 0 ≤ C ∧ jacobiCocycleDispersionFamilyBound M n m C) ↔
      (∃ C, 0 ≤ C ∧ ShawValueCapstone.shawValueFamilyBound M n (fun i => Real.log (m i)) C) := by
  constructor
  · rintro ⟨C, hCnonneg, hC⟩
    exact ⟨C, hCnonneg, (jacobiCocycleDispersionFamilyBound_iff_shawValueFamilyBound hs).1 hC⟩
  · rintro ⟨C, hCnonneg, hC⟩
    exact ⟨C, hCnonneg, (jacobiCocycleDispersionFamilyBound_iff_shawValueFamilyBound hs).2 hC⟩

/-- Wall-facing nonnegative form: failing to prove any nonnegative absolute Jacobi-dispersion
constant is exactly failing to prove any nonnegative absolute Shaw-value constant. This gives a
citable contrapositive interface for Door-IV probes without smuggling in cancellation. -/
theorem not_exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound
    {ι : Type*} {M n m : ι → ℝ}
    (hs : ∀ i, 0 < ShawValueCapstone.prizeScale (n i) (Real.log (m i))) :
    ¬ (∃ C, 0 ≤ C ∧ jacobiCocycleDispersionFamilyBound M n m C) ↔
      ¬ (∃ C, 0 ≤ C ∧ ShawValueCapstone.shawValueFamilyBound M n (fun i => Real.log (m i)) C) :=
  not_congr (exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_exists_nonneg_shawValueFamilyBound hs)

/-- Pointwise-positive parameter form of the nonnegative Jacobi-cocycle capstone. In prize-regime
applications one normally proves `0 < n_i` and `0 < log m_i`; this wrapper builds the positive scale
hypothesis and exposes the same nonnegative absolute-constant equivalence directly. -/
theorem exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_exists_nonneg_shawValueFamilyBound_of_pos
    {ι : Type*} {M n m : ι → ℝ} (hn : ∀ i, 0 < n i) (hlog : ∀ i, 0 < Real.log (m i)) :
    (∃ C, 0 ≤ C ∧ jacobiCocycleDispersionFamilyBound M n m C) ↔
      (∃ C, 0 ≤ C ∧ ShawValueCapstone.shawValueFamilyBound M n (fun i => Real.log (m i)) C) :=
  exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_exists_nonneg_shawValueFamilyBound
    (fun i => ShawValueCapstone.prizeScale_pos (hn i) (hlog i))

/-- Pointwise-positive wall-facing form. Under the standard prize-regime positivity hypotheses,
absence of a nonnegative Jacobi-dispersion absolute constant is exactly absence of a nonnegative
Shaw-value absolute constant. -/
theorem not_exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound_of_pos
    {ι : Type*} {M n m : ι → ℝ} (hn : ∀ i, 0 < n i) (hlog : ∀ i, 0 < Real.log (m i)) :
    ¬ (∃ C, 0 ≤ C ∧ jacobiCocycleDispersionFamilyBound M n m C) ↔
      ¬ (∃ C, 0 ≤ C ∧ ShawValueCapstone.shawValueFamilyBound M n (fun i => Real.log (m i)) C) :=
  not_exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound
    (fun i => ShawValueCapstone.prizeScale_pos (hn i) (hlog i))

end ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.avg_le_sup
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.geom_sum_zero_of_pow_eq_one_of_ne_one
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.trivial_cocycle_full_concentration
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.trivial_cocycle_delta_fiber
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.trivial_cocycle_offSupport_zero
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.prize_floor_iff_dispersion
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.jacobiCocycleDispersion_mono_const
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.jacobiCocycleDispersionFamilyBound_mono_const
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_exists_jacobiCocycleDispersionFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.not_exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_not_exists_jacobiCocycleDispersionFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.jacobiCocycleDispersionFamilyBound_of_rawComparison
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.exists_jacobiCocycleDispersionFamilyBound_iff_of_rawSandwich
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.jacobiCocycleDispersion_iff_shawValue_le
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.jacobiCocycleDispersionFamilyBound_iff_shawValueFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.exists_jacobiCocycleDispersionFamilyBound_iff_exists_shawValueFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_exists_nonneg_shawValueFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.not_exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_exists_nonneg_shawValueFamilyBound_of_pos
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.not_exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound_of_pos

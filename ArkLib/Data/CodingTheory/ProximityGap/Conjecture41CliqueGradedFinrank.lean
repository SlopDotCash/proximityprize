/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Conjecture41CliqueConstraintFinrank

/-!
# Conjecture 41 clique GRADED (`c ≥ 2`) relation-module dimension: `w(c−1)` / `(w−1)(c−1)`

`Conjecture41CliqueConstraintFinrank` (the `c = 1` slice) and `Conjecture41CliqueInfFinrank` (its
twisted companion) pinned the constraint-space dimension at the SINGLE coefficient slot: `w` (single
block) and `w−1` (double block). But the clique relation module at codimension `c` is in bijection
(Round 21/22, `relation_factor_sum_iff` / `..._twisted_iff`) with the **graded** constrained
space whose coordinates `v_α` are polynomials of degree `< c−1` — i.e. vectors in `F^{c−1}`:

  `V_single = { (v_α)_{α∈W} : deg v_α < c−1,  ∑_α v_α = 0 }`,
  `V_double = { (v_α)         : deg v_α < c−1,  ∑_α v_α = 0,  ∑_α γ_α v_α = 0 }`   (distinct `γ`).

The `∑ v_α = 0` condition is **coefficientwise** — it imposes `c−1` scalar equations, one per
coefficient slot, NOT one. The `Conjecture41CliqueRelationModule` docstring records the resulting
numerals as routine prose, never as a theorem:

  `dim V_single = (w+1)(c−1) − (c−1) = w(c−1)`,
  `dim V_double = (w+1)(c−1) − 2(c−1) = (w−1)(c−1)`   (distinct `γ`).

This file discharges **both graded numerals at every codimension `c = m + 1`** (`m = c−1`),
a degree-`<m` coefficient tuple as an element of `Fin m → F`. The graded sum map
`v ↦ ∑_α v_α : (↥W → (Fin m → F)) →ₗ[F] (Fin m → F)` is surjective (an indicator tuple hits any
target), and the graded twisted pair map is surjective when `γ` is non-constant (the same Cramer
witness, now per-slot). Rank–nullity over the `(W.card·m)`-dimensional ambient gives

  `finrank (ker gradedSumMap)       = (W.card − 1)·m = w·(c−1)`     (`finrank_cliqueGradedSumKer`),
  `finrank (ker gradedSum ⊓ ker tw) = (W.card − 2)·m = (w−1)·(c−1)` (the twisted headline below).

The `m = 1` (i.e. `c = 2`) instance recovers `w` / `w−1`, matching the `c = 1`-file numerals one
graded slot up; `m = 0` (`c = 1`) gives the degenerate `0` (no free coefficients). So this is the
genuine **`c ≥ 2` graded extension** the constant-`v` files left to "routine dimension bookkeeping".

PROBE: `scripts/probes/probe_clique_graded_finrank.py` — exact-ℚ / F_p Gaussian-elimination nullity
of the graded constraint matrix over `w = 2..6`, `c = 1..5`: single-block `dim = w(c−1)` (25/25),
double-block distinct-`γ` `dim = (w−1)(c−1)` (500/500 over ℚ and F_p). Field-universal (the clique
algebra carries no thinness — char-independent rank backbone of the §6.1 escape clause,
NOT a CORE/BGK input).

HONEST SCOPE (rules 1,3,6): this lands the full graded `c ≥ 2` dimension bookkeeping (the prose
numerals as theorems). The degeneracy escape clause's exceptional-prime **height** bound (the
open §6.1 residual) is UNTOUCHED. NOT a CORE closure; no capacity / beyond-Johnson / cliff-at-n/2
claim. Pure char-independent linear algebra on the proven Round-21/22 bijection.
-/

open Finset Module

namespace Round22GradedFinrank

variable {F : Type*} [Field F]

/-- The **graded sum map** on `W`-indexed degree-`<m` coefficient tuples: `v ↦ ∑_{α∈W} v α`, as an
`F`-linear map `(↥W → (Fin m → F)) →ₗ[F] (Fin m → F)`. Its kernel is the graded single-block
constraint space `{v : ∑ v = 0}` (coefficientwise) that `relation_factor_sum_iff` identifies with
degree-`<m` clique relations (`m = c−1`). -/
def gradedSumMap (W : Finset F) (m : ℕ) : (↥W → (Fin m → F)) →ₗ[F] (Fin m → F) :=
  ∑ i : ↥W, LinearMap.proj i

@[simp]
theorem gradedSumMap_apply (W : Finset F) (m : ℕ) (v : ↥W → (Fin m → F)) :
    gradedSumMap W m v = ∑ i : ↥W, v i := by
  simp only [gradedSumMap, LinearMap.coe_sum, Finset.sum_apply, LinearMap.proj_apply]

/-- The graded sum map is **surjective** when `W` is nonempty: the indicator tuple `Pi.single a s`
(target `s` at one node, `0` elsewhere) sums to `s`, hitting every target. -/
theorem gradedSumMap_surjective {W : Finset F} (hW : W.Nonempty) (m : ℕ) :
    Function.Surjective (gradedSumMap W m) := by
  classical
  obtain ⟨a, ha⟩ := hW
  intro s
  refine ⟨Pi.single (⟨a, ha⟩ : ↥W) s, ?_⟩
  rw [gradedSumMap_apply, Finset.sum_pi_single', if_pos (Finset.mem_univ _)]

/-- **HEADLINE — the graded single-block constraint-space finrank numeral.**
`finrank F (ker (gradedSumMap W m)) = (W.card − 1)·m`. With `m = c−1` and `W.card = w+1` this is
`w·(c−1)` — the degree-`<c−1` (codimension-`c`) single-block clique relation-space dimension. Proof:
rank–nullity `LinearMap.finrank_range_add_finrank_ker` for the surjective graded sum map, with
`finrank (↥W → (Fin m → F)) = W.card·m` (`Module.finrank_pi` twice + `Fintype.card_coe`) and
`finrank (range) = finrank (Fin m → F) = m` (surjective ⟹ `range = ⊤`). -/
theorem finrank_cliqueGradedSumKer {W : Finset F} (hW : W.Nonempty) (m : ℕ) :
    finrank F (LinearMap.ker (gradedSumMap W m)) = (W.card - 1) * m := by
  have hambient : finrank F (↥W → (Fin m → F)) = W.card * m := by
    rw [Module.finrank_pi_fintype]
    simp
  have hrange : finrank F (LinearMap.range (gradedSumMap W m)) = m := by
    rw [LinearMap.range_eq_top.mpr (gradedSumMap_surjective hW m), finrank_top,
      Module.finrank_pi, Fintype.card_fin]
  have hrk := (gradedSumMap W m).finrank_range_add_finrank_ker
  rw [hrange, hambient] at hrk
  have hcard : 1 ≤ W.card := Finset.Nonempty.card_pos hW
  -- hrk : m + finrank (ker) = W.card * m  ⟹  finrank (ker) = (W.card − 1) * m
  have hsub : (W.card - 1) * m = W.card * m - m := by
    rw [Nat.sub_mul, one_mul]
  rw [hsub]
  omega

/-- **Membership in the graded constraint kernel is the coefficientwise `∑ v = 0` condition.** A
graded tuple `v` lies in `ker (gradedSumMap W m)` iff `∑_α v_α = 0` (in `Fin m → F`, i.e. in every
coefficient slot) — the object the Round-22 IFF `relation_factor_sum_iff` consumes, graded. -/
theorem mem_cliqueGradedSumKer_iff_sum_eq_zero {W : Finset F} {m : ℕ} (v : ↥W → (Fin m → F)) :
    v ∈ LinearMap.ker (gradedSumMap W m) ↔ (∑ i : ↥W, v i) = 0 := by
  rw [LinearMap.mem_ker, gradedSumMap_apply]

/-! ## Double block (twisted): the `(w−1)(c−1)` graded numeral -/

/-- The **graded twisted sum map**: `v ↦ ∑_{α∈W} γ_α • v α`, an `F`-linear map
`(↥W → (Fin m → F)) →ₗ[F] (Fin m → F)`. Together with `gradedSumMap` it cuts out the graded twisted
constraint space `{v : ∑ v = 0 ∧ ∑ γ v = 0}` (`m = c−1`). -/
def gradedTwistMap (W : Finset F) (γ : ↥W → F) (m : ℕ) :
    (↥W → (Fin m → F)) →ₗ[F] (Fin m → F) :=
  ∑ i : ↥W, (γ i) • LinearMap.proj i

@[simp]
theorem gradedTwistMap_apply (W : Finset F) (γ : ↥W → F) (m : ℕ) (v : ↥W → (Fin m → F)) :
    gradedTwistMap W γ m v = ∑ i : ↥W, γ i • v i := by
  simp only [gradedTwistMap, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply]

/-- The **graded pair map** `P := gradedSumMap.prod gradedTwistMap`, `v ↦ (∑ v, ∑ γ v)`. Its kernel
is the graded twisted constraint space `ker (gradedSumMap) ⊓ ker (gradedTwistMap)`. -/
def gradedPairMap (W : Finset F) (γ : ↥W → F) (m : ℕ) :
    (↥W → (Fin m → F)) →ₗ[F] (Fin m → F) × (Fin m → F) :=
  (gradedSumMap W m).prod (gradedTwistMap W γ m)

theorem ker_gradedPairMap (W : Finset F) (γ : ↥W → F) (m : ℕ) :
    LinearMap.ker (gradedPairMap W γ m) =
      LinearMap.ker (gradedSumMap W m) ⊓ LinearMap.ker (gradedTwistMap W γ m) := by
  rw [gradedPairMap, LinearMap.ker_prod]

@[simp]
theorem gradedPairMap_apply (W : Finset F) (γ : ↥W → F) (m : ℕ) (v : ↥W → (Fin m → F)) :
    gradedPairMap W γ m v = (∑ i : ↥W, v i, ∑ i : ↥W, γ i • v i) := by
  simp only [gradedPairMap, LinearMap.prod_apply, Pi.prod, gradedSumMap_apply, gradedTwistMap_apply]

/-- **The graded pair map is surjective when `γ` is non-constant on `W`.** Given `a ≠ b ∈ W` with
`γ a ≠ γ b`, the per-slot `2 × 2` system `(v_a + v_b, γ_a v_a + γ_b v_b) = (s, t)` (all other
`v = 0`) has invertible coefficient matrix `[[1,1],[γ_a,γ_b]]` (det `γ_b − γ_a ≠ 0`), solved
slot-uniformly by the vector Cramer witness `v_a = (γ_b·s − t)/(γ_b − γ_a)`,
`v_b = (t − γ_a·s)/(γ_b − γ_a)`. Every target `(s, t) ∈ (Fin m → F)²` is hit. -/
theorem gradedPairMap_surjective_of_exists_ne {W : Finset F} {γ : ↥W → F} {m : ℕ}
    (h : ∃ a b : ↥W, a ≠ b ∧ γ a ≠ γ b) :
    Function.Surjective (gradedPairMap W γ m) := by
  classical
  obtain ⟨a, b, hab, hγab⟩ := h
  have hden : γ b - γ a ≠ 0 := sub_ne_zero.mpr (fun h => hγab h.symm)
  rintro ⟨s, t⟩
  -- per-slot vector witnesses (scalar coefficient applied to the whole Fin m → F target)
  set va : Fin m → F := (γ b - γ a)⁻¹ • (γ b • s - t) with hva
  set vb : Fin m → F := (γ b - γ a)⁻¹ • (t - γ a • s) with hvb
  set vec : ↥W → (Fin m → F) := Pi.single a va + Pi.single b vb with hvec
  refine ⟨vec, ?_⟩
  have hsum : ∑ i : ↥W, vec i = va + vb := by
    simp only [hvec, Pi.add_apply]
    rw [Finset.sum_add_distrib, Finset.sum_pi_single', Finset.sum_pi_single',
      if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  have htw : ∑ i : ↥W, γ i • vec i = γ a • va + γ b • vb := by
    simp only [hvec, Pi.add_apply, smul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single a]
      · rw [Pi.single_eq_same]
      · intro i _ hi; rw [Pi.single_eq_of_ne hi, smul_zero]
      · intro hni; exact absurd (Finset.mem_univ _) hni
    · rw [Finset.sum_eq_single b]
      · rw [Pi.single_eq_same]
      · intro i _ hi; rw [Pi.single_eq_of_ne hi, smul_zero]
      · intro hni; exact absurd (Finset.mem_univ _) hni
  rw [gradedPairMap_apply, hsum, htw]
  -- verify va + vb = s and γ_a va + γ_b vb = t, slotwise (Fin m → F equalities)
  have hs : va + vb = s := by
    rw [hva, hvb, ← smul_add]
    have : γ b • s - t + (t - γ a • s) = (γ b - γ a) • s := by
      rw [sub_smul]; abel
    rw [this, smul_smul, inv_mul_cancel₀ hden, one_smul]
  have ht : γ a • va + γ b • vb = t := by
    rw [hva, hvb, smul_smul, smul_smul, mul_comm (γ a), mul_comm (γ b), ← smul_smul, ← smul_smul,
      ← smul_add]
    have : γ a • (γ b • s - t) + γ b • (t - γ a • s)
        = (γ b - γ a) • t := by
      rw [smul_sub, smul_sub, sub_smul]
      rw [smul_comm (γ a) (γ b) s]
      abel
    rw [this, smul_smul, inv_mul_cancel₀ hden, one_smul]
  rw [hs, ht]

/-- **HEADLINE — the graded double-block (twisted) constraint-space finrank numeral.**
Under surjectivity of the graded pair map (non-constant `γ`), the graded twisted clique relation
space `ker (gradedSumMap W m) ⊓ ker (gradedTwistMap W γ m)` has dimension exactly `(W.card − 2)·m`.
With `m = c−1`, `W.card = w+1` this is `(w−1)·(c−1)` — the degree-`<c−1` double-block count. Proof:
rank–nullity for `P = gradedPairMap`, `finrank (range P) = finrank ((Fin m→F)²) = 2m` (surjective),
`finrank (↥W → (Fin m → F)) = W.card·m`, `ker P = ker gradedSum ⊓ ker gradedTwist`. -/
theorem finrank_cliqueGradedTwistInf {W : Finset F} {γ : ↥W → F} {m : ℕ}
    (hsurj : Function.Surjective (gradedPairMap W γ m)) :
    finrank F (LinearMap.ker (gradedSumMap W m) ⊓ LinearMap.ker (gradedTwistMap W γ m) :
      Submodule F (↥W → (Fin m → F))) = (W.card - 2) * m := by
  have hambient : finrank F (↥W → (Fin m → F)) = W.card * m := by
    rw [Module.finrank_pi_fintype]
    simp
  have hrange : finrank F (LinearMap.range (gradedPairMap W γ m)) = 2 * m := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_prod,
      Module.finrank_pi]
    simp [Fintype.card_fin]; ring
  have hrk := (gradedPairMap W γ m).finrank_range_add_finrank_ker
  rw [hrange, hambient, ker_gradedPairMap] at hrk
  -- hrk : 2*m + finrank (ker sum ⊓ ker twist) = W.card * m  ⟹  finrank = (W.card − 2) * m
  have hsub : (W.card - 2) * m = W.card * m - 2 * m := by
    rw [Nat.sub_mul]
  rw [hsub]
  omega

/-- The graded twisted numeral from the **natural non-constant-`γ` data** (`∃ a≠b, γa≠γb`): composes
the Cramer surjectivity (`gradedPairMap_surjective_of_exists_ne`) with the headline
`finrank_cliqueGradedTwistInf`. -/
theorem finrank_cliqueGradedTwistInf_of_exists_ne {W : Finset F} {γ : ↥W → F} {m : ℕ}
    (h : ∃ a b : ↥W, a ≠ b ∧ γ a ≠ γ b) :
    finrank F (LinearMap.ker (gradedSumMap W m) ⊓ LinearMap.ker (gradedTwistMap W γ m) :
      Submodule F (↥W → (Fin m → F))) = (W.card - 2) * m :=
  finrank_cliqueGradedTwistInf (gradedPairMap_surjective_of_exists_ne h)

end Round22GradedFinrank

#print axioms Round22GradedFinrank.gradedSumMap_apply
#print axioms Round22GradedFinrank.gradedSumMap_surjective
#print axioms Round22GradedFinrank.finrank_cliqueGradedSumKer
#print axioms Round22GradedFinrank.mem_cliqueGradedSumKer_iff_sum_eq_zero
#print axioms Round22GradedFinrank.gradedPairMap_surjective_of_exists_ne
#print axioms Round22GradedFinrank.finrank_cliqueGradedTwistInf
#print axioms Round22GradedFinrank.finrank_cliqueGradedTwistInf_of_exists_ne

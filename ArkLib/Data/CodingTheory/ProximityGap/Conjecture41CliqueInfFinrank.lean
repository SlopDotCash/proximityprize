/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Conjecture41CliqueConstraintFinrank

/-!
# Conjecture 41 clique constraint-space dimension: the `c = 1` DOUBLE-BLOCK (twisted) finrank

`Conjecture41CliqueConstraintFinrank` (Round 22) landed the **single-block** `c = 1` numeral:
`finrank F (ker (sumFunctional W)) = W.card − 1 = w`, the dimension of the constant-`v` clique
relation space `{v : ∑ v = 0}`.

This file lands the **double-block** companion -- the `c = 1` instance of the *twisted*
characterization `relation_factor_sum_twisted_iff` (`Conjecture41CliqueRelationReconstruct`), whose
relations satisfy BOTH `∑ v = 0` and `∑ γ_α v_α = 0`. That constraint space is the intersection of
two hyperplanes,

  `ker (sumFunctional W)  ⊓  ker (twistFunctional γ W)
     = { v : ∑_α v_α = 0  ∧  ∑_α γ_α v_α = 0 }`,

and we prove its dimension is **`w − 1 = W.card − 2`** -- *under the honest hypothesis that the two
functionals are linearly independent* (equivalently: `γ` is non-constant on `W`). The hypothesis is
ESSENTIAL: if `γ` is constant then `twistFunctional = γ_0 • sumFunctional`, the two hyperplanes
coincide, and the intersection is just the single `w`-dimensional hyperplane (NOT `w − 1`). This is
exactly the probe's two branches (see below).

We package the rank fact through the **pair map**
`P := (sumFunctional W).prod (twistFunctional γ W)`:
`LinearMap.ker_prod` gives `ker P = ker sum ⊓ ker twist`, and rank-nullity
(`LinearMap.finrank_range_add_finrank_ker`) gives
`finrank (ker P) = W.card − finrank (range P)`. The
headline `finrank_cliqueTwistInf` assumes `Function.Surjective P` (`finrank (range P) = 2`); the
companion `prod_surjective_of_exists_ne` discharges that hypothesis CONSTRUCTIVELY from a witness
pair `a ≠ b ∈ W` with `γ a ≠ γ b` (a `2×2` Cramer solve), so the final
`finrank_cliqueTwistInf_of_exists_ne` needs only the natural "γ non-constant" data.

PROBE: `scripts/probes/probe_clique_inf_finrank.py` -- exact-ℚ / F_p Gaussian-elimination nullity of
the `2 × |W|` matrix `[ones; γ]` over `w = 2..7`, 40 trials each:
  * `γ` with ≥2 distinct values (independent): nullity `= w−1` EXACTLY (240/240).
  * `γ` constant (proportional): nullity `= w`     EXACTLY (240/240, collapses).
Field-universal (ℚ and `F_101` agree). This is the char-independent rank backbone of the §6.1
Conjecture-41 escape clause, NOT a CORE / BGK input.

HONEST SCOPE (rules 1,3,6 + ASYMPTOTIC GUARD): the `c = 1` TWISTED numeral ONLY, and ONLY under the
linear-independence (non-constant-`γ`) hypothesis (FALSE without it -- the constant-`γ` collapse is
proved separately as `twistFunctional_eq_smul_of_const`). The full graded `c ≥ 2` dimension
bookkeeping and the degeneracy escape clause's exceptional-prime HEIGHT bound (the genuine open §6.1
residual) are UNTOUCHED. NOT a CORE closure; no capacity / beyond-Johnson / cliff-at-n/2 claim. Pure
char-independent linear algebra on the proven Round-22 twisted bijection.
-/

open Polynomial Finset Module

namespace Round22ConstraintFinrank

variable {F : Type*} [Field F]

/-- The **twisted (double-block) functional** on `W`-indexed tuples: `v ↦ ∑_{α∈W} γ α · v α`, as an
`F`-linear map `(↥W → F) →ₗ[F] F`. Together with `sumFunctional` it cuts out the `c = 1` twisted
clique relation space `{v : ∑ v = 0 ∧ ∑ γ v = 0}` (the object `relation_factor_sum_twisted_iff`
consumes). -/
def twistFunctional (W : Finset F) (γ : ↥W → F) : (↥W → F) →ₗ[F] F :=
  ∑ i : ↥W, (γ i) • LinearMap.proj i

@[simp]
theorem twistFunctional_apply (W : Finset F) (γ : ↥W → F) (v : ↥W → F) :
    twistFunctional W γ v = ∑ i : ↥W, γ i * v i := by
  simp only [twistFunctional, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]

/-- When `γ` is **constant** (`γ i = c` for all `i`), the twisted functional is `c • sumFunctional`.
Hence the two hyperplanes coincide and the twisted constraint space is just the single
`w`-dimensional `ker (sumFunctional W)` -- the probe's "collapse" branch, and the reason
non-constant `γ` (linear independence) is ESSENTIAL for the `w − 1` numeral. -/
theorem twistFunctional_eq_smul_of_const {W : Finset F} {γ : ↥W → F} {c : F}
    (hγ : ∀ i, γ i = c) : twistFunctional W γ = c • sumFunctional W := by
  ext v
  simp only [twistFunctional_apply, LinearMap.smul_apply, sumFunctional_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [hγ i])

/-- The **pair map** `P := sumFunctional.prod twistFunctional : (↥W → F) →ₗ[F] F × F`,
`v ↦ (∑ v, ∑ γ v)`. Its kernel is exactly the twisted constraint space
`ker (sumFunctional W) ⊓ ker (twistFunctional γ W)`. -/
def cliquePairMap (W : Finset F) (γ : ↥W → F) : (↥W → F) →ₗ[F] F × F :=
  (sumFunctional W).prod (twistFunctional W γ)

theorem ker_cliquePairMap (W : Finset F) (γ : ↥W → F) :
    LinearMap.ker (cliquePairMap W γ) =
      LinearMap.ker (sumFunctional W) ⊓ LinearMap.ker (twistFunctional W γ) := by
  rw [cliquePairMap, LinearMap.ker_prod]

@[simp]
theorem cliquePairMap_apply (W : Finset F) (γ : ↥W → F) (v : ↥W → F) :
    cliquePairMap W γ v = (∑ i : ↥W, v i, ∑ i : ↥W, γ i * v i) := by
  simp only [cliquePairMap, LinearMap.prod_apply, Pi.prod, sumFunctional_apply,
    twistFunctional_apply]

/-- **The pair map is surjective when `γ` is non-constant on `W`** -- given two nodes `a ≠ b ∈ W`
with `γ a ≠ γ b`, the `2 × 2` system `(v_a + v_b, γ_a v_a + γ_b v_b) = (s, t)` (with all other
`v = 0`) has the invertible coefficient matrix `[[1,1],[γ_a,γ_b]]` (determinant `γ_b − γ_a ≠ 0`), so
every target `(s, t)` is hit. This is the constructive Cramer solve discharging the
independence/surjectivity hypothesis. -/
theorem cliquePairMap_surjective_of_exists_ne {W : Finset F} {γ : ↥W → F}
    (h : ∃ a b : ↥W, a ≠ b ∧ γ a ≠ γ b) :
    Function.Surjective (cliquePairMap W γ) := by
  classical
  obtain ⟨a, b, hab, hγab⟩ := h
  have hden : γ b - γ a ≠ 0 := sub_ne_zero.mpr (fun h => hγab h.symm)
  rintro ⟨s, t⟩
  -- v_a = (γ_b·s − t)/(γ_b − γ_a),  v_b = (t − γ_a·s)/(γ_b − γ_a), all other coords 0.
  set va : F := (γ b * s - t) / (γ b - γ a) with hva
  set vb : F := (t - γ a * s) / (γ b - γ a) with hvb
  set vec : ↥W → F := Pi.single a va + Pi.single b vb with hvec
  refine ⟨vec, ?_⟩
  have hsum : ∑ i : ↥W, vec i = va + vb := by
    simp only [hvec]
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, Finset.sum_pi_single', Finset.sum_pi_single',
      if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  have htw : ∑ i : ↥W, γ i * vec i = γ a * va + γ b * vb := by
    simp only [hvec, Pi.add_apply, mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single a]
      · rw [Pi.single_eq_same]
      · intro i _ hi; rw [Pi.single_eq_of_ne hi, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_single b]
      · rw [Pi.single_eq_same]
      · intro i _ hi; rw [Pi.single_eq_of_ne hi, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  rw [cliquePairMap_apply, hsum, htw]
  have hs : va + vb = s := by
    rw [hva, hvb]
    field_simp
    ring
  have ht : γ a * va + γ b * vb = t := by
    rw [hva, hvb]
    field_simp
    ring
  rw [hs, ht]

/-- **HEADLINE -- the `c = 1` TWISTED constraint-space finrank numeral.**
Under surjectivity of the pair map (i.e. `sumFunctional` and `twistFunctional` linearly
independent), the twisted clique relation space
`ker (sumFunctional W) ⊓ ker (twistFunctional γ W)` has dimension exactly `W.card − 2 = w − 1`.
Proof: `LinearMap.finrank_range_add_finrank_ker` for `P = cliquePairMap`, with
`finrank (range P) = finrank (F × F) = 2` (surjective ⟹ `range = ⊤`), `finrank (↥W → F) = W.card`,
and `ker P = ker sum ⊓ ker twist` (`ker_cliquePairMap`). -/
theorem finrank_cliqueTwistInf {W : Finset F} {γ : ↥W → F}
    (hsurj : Function.Surjective (cliquePairMap W γ)) :
    finrank F (LinearMap.ker (sumFunctional W) ⊓ LinearMap.ker (twistFunctional W γ) :
      Submodule F (↥W → F)) = W.card - 2 := by
  have hambient : finrank F (↥W → F) = W.card := by
    rw [Module.finrank_pi, Fintype.card_coe]
  have hrange : finrank F (LinearMap.range (cliquePairMap W γ)) = 2 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_prod, Module.finrank_self]
  have hrk := (cliquePairMap W γ).finrank_range_add_finrank_ker
  rw [ker_cliquePairMap] at hrk
  rw [hambient, hrange] at hrk
  omega

/-- **The `c = 1` twisted numeral from the natural non-constant-`γ` data.** Combines
`finrank_cliqueTwistInf` with the constructive surjectivity witness
`cliquePairMap_surjective_of_exists_ne`: if `γ` takes two distinct values on `W` (`∃ a ≠ b`,
`γ a ≠ γ b`), the twisted constraint space has dimension exactly `W.card − 2 = w − 1`. The
hypothesis is sharp (`twistFunctional_eq_smul_of_const` shows it fails for constant `γ`). -/
theorem finrank_cliqueTwistInf_of_exists_ne {W : Finset F} {γ : ↥W → F}
    (h : ∃ a b : ↥W, a ≠ b ∧ γ a ≠ γ b) :
    finrank F (LinearMap.ker (sumFunctional W) ⊓ LinearMap.ker (twistFunctional W γ) :
      Submodule F (↥W → F)) = W.card - 2 :=
  finrank_cliqueTwistInf (cliquePairMap_surjective_of_exists_ne h)

/-- **Membership in the twisted constraint kernel is the conjunction `∑ v = 0 ∧ ∑ γ v = 0`** (the
object the Round-22 twisted IFF `relation_factor_sum_twisted_iff` consumes). So the
`(w − 1)`-dimensional intersection of `finrank_cliqueTwistInf` IS the constant-`v` twisted
(double-block) clique relation space, dimension now pinned. -/
theorem mem_cliqueTwistInf_iff {W : Finset F} {γ : ↥W → F} (v : ↥W → F) :
    v ∈ (LinearMap.ker (sumFunctional W) ⊓ LinearMap.ker (twistFunctional W γ) :
      Submodule F (↥W → F)) ↔ (∑ i : ↥W, v i) = 0 ∧ (∑ i : ↥W, γ i * v i) = 0 := by
  rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, sumFunctional_apply,
    twistFunctional_apply]

end Round22ConstraintFinrank

#print axioms Round22ConstraintFinrank.twistFunctional_apply
#print axioms Round22ConstraintFinrank.twistFunctional_eq_smul_of_const
#print axioms Round22ConstraintFinrank.ker_cliquePairMap
#print axioms Round22ConstraintFinrank.cliquePairMap_surjective_of_exists_ne
#print axioms Round22ConstraintFinrank.finrank_cliqueTwistInf
#print axioms Round22ConstraintFinrank.finrank_cliqueTwistInf_of_exists_ne
#print axioms Round22ConstraintFinrank.mem_cliqueTwistInf_iff

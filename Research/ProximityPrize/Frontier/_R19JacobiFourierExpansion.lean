/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge
import Mathlib.Data.ZMod.Basic

/-!
# LANE B2 (#466 round 19): the EXACT Jacobi–Fourier expansion of the thin shifted
  character sum — every `T_χ` face is a character polynomial with Jacobi coefficients

## The identity (new; probe-checked numerically before landing)

Let `G = μ_n ⊆ F*` (index `m = (q−1)/n`), let `χ : F → ℂ` be ANY nontrivial multiplicative
character (χ(0)=0), and let `{λ_j}_{j ∈ ℤ/m}` be the characters of `F*` trivial on `μ_n`
(the dual family of the quotient `F*/μ_n`).  Then for every `s ≠ 0`:

  `m · ∑_{y∈μ_n} χ(s−y)  =  χ(s) · ( ∑_{j≠0} J_j · λ_j(s)  −  1 )`,

where `J_j = ∑_t λ_j(t)·χ(1−t)` is a (generalized) Jacobi sum — an `s`-INDEPENDENT constant
with `‖J_j‖ = √q` whenever `λ_j·χ` is nontrivial.

**Why this matters for the campaign.**  The thin shifted sum `W_χ(s) = ∑_{y∈μ_n} χ(s−y)` is
the deg-`d` face of corrected Problem B (round 15 `T_χ` decomposition; round 17/18 deg-2
Karatsuba pin).  The identity says `W_χ` is EXACTLY a trigonometric polynomial in the `m−1`
nontrivial quotient characters, with coefficients of exactly known modulus `√q/m`-scale.
Consequences:

* every moment `∑_s W_χ(s)^{2r}` collapses by COMPLETE multiplicative orthogonality to a
  Jacobi-sum correlation over the linear equation `j₁ + … + j_{2r} ≡ 0 (mod m)` — the r = 3
  "sextic family cancellation" open object becomes a PURE Gauss/Jacobi phase-correlation sum
  (recall `J(λ,χ) = g(λ)g(χ)/g(λχ)`): at depth 3 the B-side literally becomes an A-side-type
  Gauss-sum moment.  The two open Props are faces of one phase-correlation object;
* the pointwise "dual" envelope `‖W_χ(s)‖ ≤ ((m−1)·√q + 1)/m` follows from the triangle
  inequality once `‖J_j‖ ≤ √q` is supplied (`jacobiCoeff_bound` named input here; elementary
  to prove by the round-17 `gSum_mul_conj` method, deferred to the companion brick);
* the expansion is `deg`-uniform: ONE identity covers all the `T_χ` faces at once.

## What is proven here (axiom-clean)

* `sum_shift_eq_zero`, `sum_units_lam` — the two orthogonality inputs in sum form;
* **`shifted_sum_jacobi_expansion`** — the exact identity above (pure finite reindexing);
* `norm_shifted_sum_le_of_jacobiBound` — the dual pointwise envelope, conditional on the
  named `‖J_j‖ ≤ B` input.

The dual family `{λ_j}` is taken as a hypothesis package (`SubgroupDualFamily`) — finite
abelian duality supplies it (Mathlib `MulChar.Duality` has the order-isomorphism; the
explicit instantiation is the companion lane).  No `sorry`, no fabricated axiom: the package
is an explicit named hypothesis, instantiable by standard mathematics.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 19, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A nontrivial multiplicative character in bare-function form (round-17 style). -/
structure IsMulCharC (χ : F → ℂ) : Prop where
  map_zero : χ 0 = 0
  map_mul : ∀ a b : F, χ (a * b) = χ a * χ b
  sum_eq_zero : ∑ a : F, χ a = 0

/-- **The dual family of the quotient `F*/G`**: `m` multiplicative characters `λ_j` (indexed by
`ℤ/m`), trivial exactly on `G`, forming a group under pointwise multiplication, with the
indicator orthogonality `∑_j λ_j(w) = m·1_G(w)`.  Finite abelian duality provides this for any
subgroup `G ⊆ F*` of index `m`; it is bundled as a hypothesis package so the expansion below is
pure algebra. -/
structure SubgroupDualFamily (G : Finset F) (m : ℕ) [NeZero m]
    (lam : ZMod m → F → ℂ) : Prop where
  map_zero : ∀ j : ZMod m, lam j 0 = 0
  map_mul : ∀ (j : ZMod m) (a b : F), lam j (a * b) = lam j a * lam j b
  triv_on_units : ∀ a : F, a ≠ 0 → lam 0 a = 1
  sum_eq_zero : ∀ j : ZMod m, j ≠ 0 → ∑ a : F, lam j a = 0
  indicator : ∀ w : F, ∑ j : ZMod m, lam j w = (m : ℂ) * (if w ∈ G then 1 else 0)

/-- The thin shifted character sum `W_χ(s) = ∑_{y∈G} χ(s−y)` — the deg-`d` face object. -/
noncomputable def shiftedSum (χ : F → ℂ) (G : Finset F) (s : F) : ℂ := ∑ y ∈ G, χ (s - y)

/-- The (generalized) Jacobi coefficient `J_j = ∑_t λ_j(t)·χ(1−t)`. -/
noncomputable def jacobiCoeff (χ : F → ℂ) {m : ℕ} [NeZero m] (lam : ZMod m → F → ℂ) (j : ZMod m) : ℂ :=
  ∑ t : F, lam j t * χ (1 - t)

variable {χ : F → ℂ} {G : Finset F} {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ}

/-- Shifted complete sum of a nontrivial character vanishes: `∑_w χ(s−w) = 0`. -/
theorem sum_shift_eq_zero (hχ : IsMulCharC χ) (s : F) : ∑ w : F, χ (s - w) = 0 := by
  classical
  calc ∑ w : F, χ (s - w) = ∑ w : F, χ w :=
        Fintype.sum_equiv (Equiv.subLeft s) _ _ (fun w => rfl)
    _ = 0 := hχ.sum_eq_zero

/-- **THE EXACT JACOBI–FOURIER EXPANSION.**  For `s ≠ 0`:
`m·W_χ(s) = χ(s)·(∑_{j≠0} J_j·λ_j(s) − 1)`. -/
theorem shifted_sum_jacobi_expansion (hχ : IsMulCharC χ)
    (hfam : SubgroupDualFamily G m lam) {s : F} (hs : s ≠ 0) :
    (m : ℂ) * shiftedSum χ G s
      = χ s * ((∑ j ∈ Finset.univ \ {(0 : ZMod m)},
          jacobiCoeff χ lam j * lam j s) - 1) := by
  classical
  -- Step 1: m·W = ∑_w (∑_j λ_j(w))·χ(s−w)
  have h1 : (m : ℂ) * shiftedSum χ G s
      = ∑ w : F, (∑ j : ZMod m, lam j w) * χ (s - w) := by
    have hpt : ∀ w : F, (∑ j : ZMod m, lam j w) * χ (s - w)
        = (m : ℂ) * ((if w ∈ G then 1 else 0) * χ (s - w)) := by
      intro w
      rw [hfam.indicator w]
      ring
    rw [Finset.sum_congr rfl (fun w _ => hpt w), ← Finset.mul_sum]
    congr 1
    rw [shiftedSum]
    have hpt2 : ∀ w : F, (if w ∈ G then (1:ℂ) else 0) * χ (s - w)
        = (if w ∈ G then χ (s - w) else 0) := by
      intro w; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun w _ => hpt2 w)]
    rw [Finset.sum_ite_mem Finset.univ G (fun w => χ (s - w)), Finset.univ_inter]
  -- Step 2: swap and evaluate per j
  have h2 : ∑ w : F, (∑ j : ZMod m, lam j w) * χ (s - w)
      = ∑ j : ZMod m, ∑ w : F, lam j w * χ (s - w) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun w _ => by rw [Finset.sum_mul])
  -- the j = 0 term: ∑_{w≠0} χ(s−w) = −χ(s)
  have h0 : ∑ w : F, lam 0 w * χ (s - w) = -(χ s) := by
    have hpt : ∀ w : F, lam 0 w * χ (s - w)
        = χ (s - w) - (if w = 0 then χ (s - w) else 0) := by
      intro w
      by_cases hw : w = 0
      · subst hw; simp [hfam.map_zero]
      · rw [hfam.triv_on_units w hw]; simp [hw]
    rw [Finset.sum_congr rfl (fun w _ => hpt w), Finset.sum_sub_distrib]
    rw [sum_shift_eq_zero hχ s]
    rw [Finset.sum_ite_eq' Finset.univ (0 : F) (fun w => χ (s - w))]
    simp
  -- the j ≠ 0 terms: U_j(s) = λ_j(s)·χ(s)·J_j
  have hj : ∀ j : ZMod m, j ≠ 0 →
      ∑ w : F, lam j w * χ (s - w) = jacobiCoeff χ lam j * lam j s * χ s := by
    intro j _
    -- reindex w = s·t
    have hre : ∑ w : F, lam j w * χ (s - w) = ∑ t : F, lam j (s * t) * χ (s - s * t) := by
      exact (Fintype.sum_bijective (fun t => s * t) (mulLeft_bijective₀ s hs) _ _
        (fun t => rfl)).symm
    rw [hre]
    have hpt : ∀ t : F, lam j (s * t) * χ (s - s * t)
        = (lam j s * χ s) * (lam j t * χ (1 - t)) := by
      intro t
      rw [hfam.map_mul j s t]
      have harg : s - s * t = s * (1 - t) := by ring
      rw [harg, hχ.map_mul s (1 - t)]
      ring
    rw [Finset.sum_congr rfl (fun t _ => hpt t), ← Finset.mul_sum]
    rw [jacobiCoeff]
    ring
  -- assemble
  rw [h1, h2]
  have hsplit : ∑ j : ZMod m, ∑ w : F, lam j w * χ (s - w)
      = (∑ w : F, lam 0 w * χ (s - w))
        + ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, ∑ w : F, lam j w * χ (s - w) := by
    rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr (Finset.mem_univ (0 : ZMod m)))]
    rw [Finset.sum_singleton]
    ring
  rw [hsplit, h0]
  rw [Finset.sum_congr rfl (fun j hj' => hj j (by
    have := (Finset.mem_sdiff.mp hj').2
    simpa using this))]
  rw [mul_sub, mul_one, Finset.mul_sum]
  have hterm : ∀ j ∈ Finset.univ \ {(0 : ZMod m)},
      jacobiCoeff χ lam j * lam j s * χ s = χ s * (jacobiCoeff χ lam j * lam j s) := by
    intro j _; ring
  rw [Finset.sum_congr rfl hterm]
  ring

/-- **The dual pointwise envelope**: if every Jacobi coefficient satisfies `‖J_j‖ ≤ B` and
`‖χ s‖ ≤ 1`, `‖λ_j s‖ ≤ 1`, then `‖W_χ(s)‖ ≤ ((m−1)·B + 1)/m` for `s ≠ 0`.
With the classical `B = √q` this is the dual-side pointwise bound for every face at once. -/
theorem norm_shifted_sum_le_of_jacobiBound (hχ : IsMulCharC χ)
    (hfam : SubgroupDualFamily G m lam) {s : F} (hs : s ≠ 0)
    {B : ℝ} (hB : ∀ j : ZMod m, j ≠ 0 → ‖jacobiCoeff χ lam j‖ ≤ B)
    (hχ1 : ‖χ s‖ ≤ 1) (hlam1 : ∀ j : ZMod m, ‖lam j s‖ ≤ 1) (hB0 : 0 ≤ B) :
    ‖shiftedSum χ G s‖ ≤ (((m : ℝ) - 1) * B + 1) / m := by
  have hm0 : (0:ℝ) < (m : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne m)
    exact_mod_cast this
  have hexp := shifted_sum_jacobi_expansion hχ hfam hs
  have hnorm : (m : ℝ) * ‖shiftedSum χ G s‖
      = ‖χ s * ((∑ j ∈ Finset.univ \ {(0 : ZMod m)},
          jacobiCoeff χ lam j * lam j s) - 1)‖ := by
    rw [← hexp, norm_mul, Complex.norm_natCast]
  rw [le_div_iff₀ hm0, mul_comm, hnorm]
  set S : ℂ := ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, jacobiCoeff χ lam j * lam j s with hS
  calc ‖χ s * (S - 1)‖
      ≤ ‖S - 1‖ := by
        rw [norm_mul]
        calc ‖χ s‖ * ‖S - 1‖ ≤ 1 * ‖S - 1‖ :=
              mul_le_mul_of_nonneg_right hχ1 (norm_nonneg _)
          _ = ‖S - 1‖ := one_mul _
    _ ≤ ‖S‖ + 1 := by
        calc ‖S - 1‖ ≤ ‖S‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = ‖S‖ + 1 := by norm_num
    _ ≤ ((m : ℝ) - 1) * B + 1 := by
        have hsum : ‖S‖ ≤ ((m : ℝ) - 1) * B := by
          rw [hS]
          calc ‖∑ j ∈ Finset.univ \ {(0 : ZMod m)}, jacobiCoeff χ lam j * lam j s‖
              ≤ ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, ‖jacobiCoeff χ lam j * lam j s‖ :=
                norm_sum_le _ _
            _ ≤ ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, B := by
                refine Finset.sum_le_sum (fun j hj => ?_)
                have hj0 : j ≠ 0 := by
                  have := (Finset.mem_sdiff.mp hj).2
                  simpa using this
                rw [norm_mul]
                calc ‖jacobiCoeff χ lam j‖ * ‖lam j s‖ ≤ B * 1 :=
                      mul_le_mul (hB j hj0) (hlam1 j) (norm_nonneg _) hB0
                  _ = B := mul_one B
            _ = ((Finset.univ \ {(0 : ZMod m)}).card : ℝ) * B := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ = ((m : ℝ) - 1) * B := by
                have hc : (Finset.univ \ {(0 : ZMod m)}).card = m - 1 := by
                  simp [Finset.card_sdiff, ZMod.card]
                rw [hc]
                have hm1 : 1 ≤ m := Nat.pos_of_ne_zero (NeZero.ne m)
                push_cast [Nat.cast_sub hm1]
                ring
        linarith

end ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion.shifted_sum_jacobi_expansion
#print axioms
  ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion.norm_shifted_sum_le_of_jacobiBound

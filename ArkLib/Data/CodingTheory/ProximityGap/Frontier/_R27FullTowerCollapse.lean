/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R26DiscreteLogExists
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R23TripleConvEnergyInput
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R26PointwiseTripleConvTarget

/-!
# LANE B2 (#466 round 27): the FULL-TOWER collapse — every rung, including the deep-depth
  wall, in final exact form

Rounds 21–22 collapsed rungs r = 2, 3.  This brick does every depth at once:

  `T(s)^r = ∑_c (J^{∗r})(c)·λ_c(s)`   (induction; `J^{∗r}` = r-fold self-convolution on `ℤ/m`
  with nonzero indices), hence

  **`fullTower_collapse`** :  `∑_{s≠0} ‖T(s)‖^{2r} = (q−1)·∑_c ‖(J^{∗r})(c)‖²`  for ALL `r`.

With rounds 25–26 the identity is UNCONDITIONAL for every finite field.  Consequences:

* the ENTIRE corrected Problem B — including the deep-depth demand `r ≈ ln q`, i.e. the
  remaining content of `HyperplaneCancellation` — is now exactly the ℓ²-growth profile of
  repeated self-convolution of the Jacobi sequence: `IterConvEnergyWick` below names the rung-`r`
  bound at the Wick scale `C^r·r!·(mq)^r`, and `sup_pureFace_of_iterConvEnergyWick` is the
  machine-checked consumer that turns the deep rung into the sup-norm cancellation the prize
  chain consumes;
* the ladder in this normal form: `r = 1` closed (Parseval, r20); `r = 2` closed mod textbook
  Weil (r17/18/21); `r = 3` the calibrated open core (r23); `r ≈ ln q` the wall — ONE family of
  inequalities, one open parameter range, zero scaffolding.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 27, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R27FullTowerCollapse

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R22SexticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- The `r`-fold self-convolution of the coefficient sequence, all indices nonzero:
`J^{∗0} = δ₀`, `J^{∗(r+1)}(c) = ∑_{j≠0} J^{∗r}(c−j)·J_j`. -/
noncomputable def iterConv (J : ZMod m → ℂ) : ℕ → ZMod m → ℂ
  | 0 => fun c => if c = 0 then 1 else 0
  | r + 1 => fun c => ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, iterConv J r (c - j) * J j

/-- **The power of the face is the λ-expansion of the iterated convolution** (all `r`,
`s ≠ 0`). -/
theorem pureFace_pow (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {s : F} (hs : s ≠ 0) :
    ∀ r : ℕ, (pureFace J lam s) ^ r = ∑ c : ZMod m, iterConv J r c * lam c s := by
  intro r
  induction r with
  | zero =>
    rw [pow_zero]
    have hpt : ∀ c : ZMod m, iterConv J 0 c * lam c s
        = if c = 0 then lam 0 s else 0 := by
      intro c
      simp only [iterConv]
      split_ifs with h
      · rw [h, one_mul]
      · rw [zero_mul]
    rw [Finset.sum_congr rfl (fun c _ => hpt c)]
    rw [Finset.sum_ite_eq' Finset.univ (0 : ZMod m) (fun _ => lam 0 s)]
    rw [if_pos (Finset.mem_univ _), hfam.triv_on_units s hs]
  | succ r ih =>
    rw [pow_succ, ih, pureFace, Finset.sum_mul_sum]
    have hpt : ∀ c : ZMod m, ∀ j ∈ Finset.univ \ {(0 : ZMod m)},
        (iterConv J r c * lam c s) * (J j * lam j s)
          = iterConv J r c * J j * lam (c + j) s := by
      intro c j _
      rw [hgrp.add_eq_mul c j s]
      ring
    rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun j hj => hpt c j hj))]
    rw [Finset.sum_comm]
    symm
    calc ∑ d : ZMod m, iterConv J (r + 1) d * lam d s
        = ∑ d : ZMod m, ∑ j ∈ Finset.univ \ {(0 : ZMod m)},
            iterConv J r (d - j) * J j * lam d s := by
          refine Finset.sum_congr rfl (fun d _ => ?_)
          simp only [iterConv]
          rw [Finset.sum_mul]
      _ = ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, ∑ d : ZMod m,
            iterConv J r (d - j) * J j * lam d s := Finset.sum_comm
      _ = ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, ∑ c : ZMod m,
            iterConv J r c * J j * lam (c + j) s := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          refine Finset.sum_nbij' (fun d => d - j) (fun c => c + j) ?_ ?_ ?_ ?_ ?_
          · intro d _; exact Finset.mem_univ _
          · intro c _; exact Finset.mem_univ _
          · intro d _; dsimp only; ring
          · intro c _; dsimp only; ring
          · intro d _
            dsimp only
            congr 2
            ring

/-- **THE FULL-TOWER COLLAPSE (round-27 main theorem).**  For every depth `r`:
`∑_{s≠0} ‖T(s)‖^{2r} = (q−1)·∑_c ‖(J^{∗r})(c)‖²`.  Together with rounds 25–26 this is
unconditional for every finite field: the whole corrected tower, including the deep-depth
wall, is the ℓ²-growth of repeated self-convolution. -/
theorem fullTower_collapse (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) (J : ZMod m → ℂ) (r : ℕ) :
    ∑ s ∈ Finset.univ.erase (0 : F), ‖pureFace J lam s‖ ^ (2 * r)
      = ((Fintype.card F - 1 : ℕ) : ℝ) * ∑ c : ZMod m, ‖iterConv J r c‖ ^ 2 := by
  classical
  have hpt : ∀ s ∈ Finset.univ.erase (0 : F),
      ‖pureFace J lam s‖ ^ (2 * r) = ‖∑ c : ZMod m, iterConv J r c * lam c s‖ ^ 2 := by
    intro s hs
    have hs0 : s ≠ 0 := (Finset.mem_erase.mp hs).1
    rw [← pureFace_pow hfam hgrp J hs0 r]
    rw [norm_pow]
    ring
  rw [Finset.sum_congr rfl hpt]
  exact lamExpansion_parseval hfam hgrp (iterConv J r)

/-- **The named deep-depth ladder** (rung `r`, constant `C`): the iterated-convolution energy
at Wick scale.  `r = 1` is closed (r20 Parseval); `r = 2` closed mod textbook Weil; `r = 3`
is the calibrated open core (r23); `r ≈ ln q` is the wall — the remaining content of
`HyperplaneCancellation` in final normal form. -/
def IterConvEnergyWick (J : ZMod m → ℂ) (q r : ℕ) (C : ℝ) : Prop :=
  ∑ c : ZMod m, ‖iterConv J r c‖ ^ 2
    ≤ C ^ r * (r.factorial : ℝ) * ((m : ℝ) * (q : ℝ)) ^ r

/-- At depth `3`, the full-tower `iterConv` energy is the same energy as the R22/R23
triple-convolution normal form.  This routes the calibrated r = 3 input into the uniform
ladder notation used by the deeper tower. -/
theorem iterConv_three_energy_eq_tripleConv_energy
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) :
    ∑ c : ZMod m, ‖iterConv J 3 c‖ ^ 2
      = ∑ d : ZMod m, ‖tripleConv J d‖ ^ 2 := by
  have hfull := fullTower_collapse (F := F) (G := G) (lam := lam) hfam hgrp J 3
  have hsext := sextic_convolution_collapse (F := F) (G := G) (lam := lam) hfam hgrp J
  have hpow : (2 : ℕ) * 3 = 6 := by norm_num
  rw [hpow] at hfull
  rw [hsext] at hfull
  have hcard : 0 < ((Fintype.card F - 1 : ℕ) : ℝ) := by
    have hnat : 0 < Fintype.card F - 1 := Nat.sub_pos_of_lt (Fintype.one_lt_card (α := F))
    exact_mod_cast hnat
  nlinarith

/-- The calibrated R23 triple-convolution input supplies the depth-3 full-tower Wick rung
for any ladder constant `K` with `C ≤ 6 K³`. -/
theorem iterConvEnergyWick_three_of_tripleConvEnergyBound
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {C K : ℝ}
    (hCK : C ≤ 6 * K ^ 3)
    (h : TripleConvEnergyBound J (Fintype.card F) C) :
    IterConvEnergyWick J (Fintype.card F) 3 K := by
  unfold IterConvEnergyWick
  unfold TripleConvEnergyBound at h
  rw [iterConv_three_energy_eq_tripleConv_energy (F := F) (G := G) (lam := lam) hfam hgrp J]
  have hscale : C * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3
      ≤ K ^ 3 * (Nat.factorial 3 : ℝ) * ((m : ℝ) * (Fintype.card F : ℝ)) ^ 3 := by
    have hnon : 0 ≤ (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3 := by positivity
    calc C * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3
        = C * ((m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) := by ring
      _ ≤ (6 * K ^ 3) * ((m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_right hCK hnon
      _ = K ^ 3 * (Nat.factorial 3 : ℝ) * ((m : ℝ) * (Fintype.card F : ℝ)) ^ 3 := by
          norm_num
          ring
  exact h.trans hscale

/-- The energy-level expanded Jacobi Hermitian target supplies the depth-3 full-tower Wick
rung for the Jacobi coefficient sequence. -/
theorem iterConvEnergyWick_three_of_jacobiAdditiveTripleHermitianExpandedEnergyBound
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C K : ℝ} (hCK : C ≤ 6 * K ^ 3)
    (h : JacobiAdditiveTripleHermitianExpandedEnergyBound χ lam C) :
    IterConvEnergyWick
      (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i)
      (Fintype.card F) 3 K :=
  iterConvEnergyWick_three_of_tripleConvEnergyBound hfam hgrp
    (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i) hCK
    (tripleConvEnergyBound_of_jacobiAdditiveTripleHermitianExpandedEnergyBound h)

/-- The pointwise expanded Jacobi Hermitian target supplies the depth-3 full-tower Wick
rung for the Jacobi coefficient sequence. -/
theorem iterConvEnergyWick_three_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C K : ℝ} (hCK : C ≤ 6 * K ^ 3)
    (h : JacobiAdditiveTripleHermitianExpandedPointwiseBound χ lam C) :
    IterConvEnergyWick
      (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i)
      (Fintype.card F) 3 K :=
  iterConvEnergyWick_three_of_jacobiAdditiveTripleHermitianExpandedEnergyBound hfam hgrp
    hCK (jacobiAdditiveTripleHermitianExpandedEnergyBound_of_pointwise h)

/-- The named B-side six-variable input supplies the depth-3 full-tower Wick rung for the
Jacobi coefficient sequence. -/
theorem iterConvEnergyWick_three_of_jacobiHermitianSixInput
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C K : ℝ} (hCK : C ≤ 6 * K ^ 3)
    (h : JacobiHermitianSixInput χ lam C) :
    IterConvEnergyWick
      (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i)
      (Fintype.card F) 3 K :=
  iterConvEnergyWick_three_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound hfam hgrp
    hCK h

/-- Consumer: the rung-`r` ladder bound yields the `2r`-th moment of the face, hence the
pointwise sup bound at depth `r` — the moment-method input the prize chain consumes at
`r ≈ ln q`. -/
theorem sup_pureFace_of_iterConvEnergyWick (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) (J : ZMod m → ℂ) {r : ℕ} {C : ℝ}
    (h : IterConvEnergyWick J (Fintype.card F) r C) {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ (2 * r)
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C ^ r * (r.factorial : ℝ) * ((m : ℝ) * (Fintype.card F : ℝ)) ^ r) := by
  have hmem : s ∈ Finset.univ.erase (0 : F) :=
    Finset.mem_erase.mpr ⟨hs, Finset.mem_univ _⟩
  have hsingle : ‖pureFace J lam s‖ ^ (2 * r)
      ≤ ∑ s' ∈ Finset.univ.erase (0 : F), ‖pureFace J lam s'‖ ^ (2 * r) :=
    Finset.single_le_sum (f := fun s' => ‖pureFace J lam s'‖ ^ (2 * r))
      (fun s' _ => by positivity) hmem
  refine le_trans hsingle ?_
  rw [fullTower_collapse hfam hgrp J r]
  have hq : (0:ℝ) ≤ ((Fintype.card F - 1 : ℕ) : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left h hq

end ArkLib.ProximityGap.Frontier.R27FullTowerCollapse

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R27FullTowerCollapse.pureFace_pow
#print axioms ArkLib.ProximityGap.Frontier.R27FullTowerCollapse.fullTower_collapse
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse in
#print axioms iterConv_three_energy_eq_tripleConv_energy
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse in
#print axioms iterConvEnergyWick_three_of_tripleConvEnergyBound
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse in
#print axioms iterConvEnergyWick_three_of_jacobiAdditiveTripleHermitianExpandedEnergyBound
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse in
#print axioms iterConvEnergyWick_three_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse in
#print axioms iterConvEnergyWick_three_of_jacobiHermitianSixInput
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse in
#print axioms sup_pureFace_of_iterConvEnergyWick

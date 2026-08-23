/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPhaseResonance

/-!
# The EXACT convolution recursion of the resonance phase-sum (#407 / #444)

Extends `GaussPhaseResonance` (the named `sqrt p`-free free variable of the prize). The base
file `_ResonanceMomentBaseCase` pins the `r = 1` rung `phaseSum u 1 c = u c` (for `c != 0`) and
`_ResonanceMomentRTwo` gives the `r = 2` off-diagonal convolution collapse. What was MISSING
(grep-confirmed: no `phaseSum_succ`, no `phaseSum u (r+1) = ∑ u · phaseSum u r`, no exact
equality recursion anywhere in `ProximityGap/`) is the SINGLE structural identity that ties the
whole tower together for EVERY depth at once:

> **`phaseSum u (r+1) c = ∑_{a ≠ 0} u(a) · phaseSum u r (c − a)`.**

This is the EXACT one-step convolution recursion: the depth-`(r+1)` phase-sum is the (nonzero-
support) convolution of the single-step kernel `a ↦ u(a)·[a≠0]` against the depth-`r` phase-sum.
Equivalently, on the group algebra `ℂ[ZMod m]`, `P_{r+1} = K ∗ P_r` where `K = ∑_{a≠0} u(a)·δ_a`
and `P_r = ∑_c phaseSum u r c · δ_c`. Every higher rung is therefore `K^{∗(r)}` convolved with the
base, so the ENTIRE tower is the iterated convolution power of ONE kernel `K`.

## Why this is the right structural lever (probe-verified, then formalized)

Probe `scripts/probes/probe_phaseSum_recursion.py` (random unit phases, `m ∈ {3,5,7,9}`,
`r ∈ {1,2,3}`): `max|lhs − rhs|` at machine epsilon (`≤ 1.4e-13`) for every case — the recursion
is EXACT, not approximate. The lever it unlocks: on the Fourier side this is `ξ̂_{r+1}(b) =
K̂(b) · ξ̂_r(b)`, i.e. `ξ̂_r(b) = K̂(b)^r` — the resonance moment `T r = (1/m) ∑_b |K̂(b)|^{2r}`
is the `2r`-th power-mean of the SINGLE step-kernel transform `K̂(b) = ∑_{a≠0} u(a) e_m(ab)`.
This LOCALIZES the whole `r`-tower to the spectral profile of ONE function (the open BGK object),
making explicit that no per-`r` argument adds information beyond the `r = 1` kernel spectrum.

## Honest scope

This is a CERTAIN exact algebraic identity (a Finset reindexing), not a bound. It does NOT bound
`K̂(b)` — that spectral profile IS the open Gauss-period/BGK content. It is the Lane-2/3 citable
structural capstone that the tower is iterated convolution of one kernel; CORE
`M(μ_n) ≤ C·√(n log m)` UNCHANGED / OPEN. No CORE / cancellation / completion / moment /
anti-concentration / capacity claim.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators Classical
open Finset

variable {m : ℕ} [NeZero m]

/-- **Membership in the depth-`(r+1)` phase-sum filter via the last/init split.**
A tuple `X : Fin (r+1) → ZMod m` lies in the depth-`(r+1)` filter at `c` iff its last coordinate
`a := X (Fin.last r)` is nonzero, its init `Fin.init X` lies in the depth-`r` filter at `c − a`,
and the two reassemble. This is the combinatorial heart of the recursion. -/
theorem phaseSum_succ_mem_iff (r : ℕ) (c : ZMod m) (X : Fin (r + 1) → ZMod m) :
    (X ∈ (Finset.univ.filter (fun X : Fin (r + 1) → ZMod m =>
        (∀ i, X i ≠ 0) ∧ (∑ i, X i) = c))) ↔
      (X (Fin.last r) ≠ 0 ∧
        (Fin.init X ∈ (Finset.univ.filter (fun Y : Fin r → ZMod m =>
          (∀ i, Y i ≠ 0) ∧ (∑ i, Y i) = c - X (Fin.last r))))) := by
  classical
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, hsum⟩
    refine ⟨hne (Fin.last r), fun i => ?_, ?_⟩
    · exact hne i.castSucc
    · -- ∑ init X = c - X last
      have hsplit : (∑ i, X i) = (∑ i : Fin r, Fin.init X i) + X (Fin.last r) :=
        Fin.sum_univ_castSucc X
      rw [hsplit] at hsum
      -- (∑ init) + last = c  ⟹  ∑ init = c - last
      rw [eq_sub_iff_add_eq]
      exact hsum
  · rintro ⟨hlast, hinit_ne, hinit_sum⟩
    refine ⟨fun i => ?_, ?_⟩
    · -- every coordinate nonzero: split via lastCases
      induction i using Fin.lastCases with
      | last => exact hlast
      | cast j =>
        have := hinit_ne j
        simpa [Fin.init] using this
    · have hsplit : (∑ i, X i) = (∑ i : Fin r, Fin.init X i) + X (Fin.last r) :=
        Fin.sum_univ_castSucc X
      rw [hsplit, hinit_sum, sub_add_cancel]

/-- **The EXACT one-step convolution recursion of the phase-sum (the structural capstone).**
`phaseSum u (r+1) c = ∑_{a ≠ 0} u(a) · phaseSum u r (c − a)`. The depth-`(r+1)` phase-sum is the
nonzero-support convolution of the single-step kernel `a ↦ u(a)` against the depth-`r` phase-sum;
hence the whole resonance tower is the iterated convolution power of ONE kernel. Pure Finset
reindexing — no hypothesis on `u`, exact for every `r` and every `c`. -/
theorem phaseSum_succ (u : ZMod m → ℂ) (r : ℕ) (c : ZMod m) :
    phaseSum u (r + 1) c =
      ∑ a ∈ Finset.univ.filter (fun a : ZMod m => a ≠ 0),
        u a * phaseSum u r (c - a) := by
  classical
  -- Rewrite the RHS phaseSum and pull the coefficient inside, then biject to the LHS.
  -- RHS becomes: ∑_{a≠0} ∑_{Y ∈ filter_r(c-a)} u a * ∏_i u (Y i).
  simp_rw [phaseSum, Finset.mul_sum]
  -- Re-collect as a sum over the sigma {(a, Y)} and biject with the (r+1)-filter via snoc.
  rw [Finset.sum_sigma']
  -- LHS = (r+1)-filter sum, RHS = sigma sum; biject (r+1)-filter → sigma via (last, init).
  refine Finset.sum_nbij'
    (i := fun X => Sigma.mk (X (Fin.last r)) (Fin.init X))
    (j := fun p => Fin.snoc p.2 p.1)
    ?_ ?_ ?_ ?_ ?_
  · -- X ∈ (r+1)-filter at c  ⟹  (X last, init X) ∈ sigma
    intro X hX
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX
    obtain ⟨hne, hsum⟩ := hX
    rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter]
    have hsplit : (∑ i, X i) = (∑ i : Fin r, Fin.init X i) + X (Fin.last r) :=
      Fin.sum_univ_castSucc X
    refine ⟨⟨Finset.mem_univ _, hne (Fin.last r)⟩, ⟨Finset.mem_univ _, fun i => hne i.castSucc, ?_⟩⟩
    rw [hsplit] at hsum
    rw [eq_sub_iff_add_eq]; exact hsum
  · -- (a, Y) ∈ sigma  ⟹  snoc Y a ∈ (r+1)-filter at c
    intro p hp
    rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter] at hp
    obtain ⟨⟨_, ha0⟩, _, hYne, hYsum⟩ := hp
    rw [Finset.mem_filter]
    simp only
    refine ⟨Finset.mem_univ _, fun i => ?_, ?_⟩
    · induction i using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact ha0
      | cast j => rw [Fin.snoc_castSucc]; exact hYne j
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [hYsum, sub_add_cancel]
  · -- left inverse: snoc (init X) (X last) = X
    intro X _
    exact Fin.snoc_init_self X
  · -- right inverse: (snoc Y a last, init (snoc Y a)) = (a, Y)
    intro p _
    simp only [Fin.snoc_last, Fin.init_snoc]
  · -- summand match: ∏_{i<r+1} u (X i) = u (X last) * ∏_i u (init X i)
    intro X _
    rw [Fin.prod_univ_castSucc, mul_comm]
    rfl

/-- **Total-mass (L¹) form of the recursion: `∑_c phaseSum u (r+1) c = S · ∑_c phaseSum u r c`**
where `S = ∑_{a≠0} u a`. Summing the convolution recursion over `c` and using that `c ↦ c - a`
is a bijection of `ZMod m`, the depth-`(r+1)` total mass is `S` times the depth-`r` total mass —
so `∑_c phaseSum u r c = S^r` (the phase-mass tower, here in clean recursive form). -/
theorem sum_phaseSum_succ (u : ZMod m → ℂ) (r : ℕ) :
    (∑ c : ZMod m, phaseSum u (r + 1) c)
      = (∑ a ∈ Finset.univ.filter (fun a : ZMod m => a ≠ 0), u a)
        * (∑ c : ZMod m, phaseSum u r c) := by
  classical
  simp_rw [phaseSum_succ]
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro a _
  -- ∑_c u a * phaseSum u r (c - a) = u a * ∑_c phaseSum u r (c - a) = u a * ∑_c phaseSum u r c
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.subRight a) _ _ (fun c => rfl)

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.phaseSum_succ_mem_iff
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.phaseSum_succ
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.sum_phaseSum_succ

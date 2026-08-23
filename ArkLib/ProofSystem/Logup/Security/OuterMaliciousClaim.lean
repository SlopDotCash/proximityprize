/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SoundnessConverse
import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckBridge
import ArkLib.Data.MvPolynomial.SchwartzZippelCounting

/-!
# The malicious-prover outer claim: per-`m` bad challenges + `(z, λ)` Schwartz–Zippel (issue #13)

The mathematics of the outer-phase soundness obligation `hOuter` against an **arbitrary**
(malicious) prover.  The prover commits a multiplicity oracle `m` (round 0), receives the
uniform challenge `x` (round 1), commits helper oracles `h₁ … h_K` (round 2, adversarially,
possibly depending on `x`), and receives the batching challenge `(z, λ)` (round 3).  The
after-outer mid-claim is

  `claim(m, x, h, z, λ) = S(h) + ∑ₖ λₖ · D̂ₖ(z)`        (`sum_qOnHypercube_eq`)

with `S(h) = ∑ᵤ ∑ₖ hₖ(u)` the helper mass and `D̂ₖ` the multilinear extension of the round-`u`
domain-identity violation `Dₖ(u)`.  This file proves the complete challenge-level analysis:

* **Stage 1 (the `x`-stage bad set).**  `outerBadChallenges params oStmt m` — the roots of the
  per-`m` cleared grand-sum numerator (`clearedNumerator`, denominators cleared over the *set* of
  pole values) together with the `m`-independent *degenerate* challenges (those producing ≥ 2
  vanishing denominators inside a single group/row, where the domain identity stops pinning the
  helper value).  For a bad lookup its cardinality is uniformly `≤ (M+1)·2ⁿ − 1`
  (`outerBadChallenges_card_le`) — the paper budget numerator: `deg ≤ |poleValues| − 1` for the
  root part and the multiplicity-excess `(M+1)·2ⁿ − |poleValues|` for the degenerate part.
* **Stage 2 (the `(z, λ)`-stage).**  At any guard-passing `x ∉ outerBadChallenges`, *no* helper
  message makes the claim identically zero in `(z, λ)` (`claim_not_identicallyZero`): away from
  all poles the domain identities force the honest helpers, whose mass is the grand sum — nonzero
  exactly because `x` is not a root of the cleared numerator; at a column pole the single-zero
  denominator (degenerate `x` excluded) forces a violation `Dₖ(u) ≠ 0` outright.  A non-identically
  zero claim then survives the uniform `(z, λ)` draw with probability at most `(n+1)/|F|`
  (`card_filter_claimZero_le`, in counting form): for each `z` the claim is affine in `λ` with
  coefficient vector `D̂(z)` — one root hyperplane when `D̂(z) ≠ 0` — and `D̂(z)` vanishes on at
  most `n·|F|ⁿ⁻¹` points by Schwartz–Zippel for the kernel MLE (`kernelMLEPoly`).

Everything is counting/algebra: no probability monads.  The run-level wiring (the opaque-prover
two-challenge decomposition) consumes these in `OuterMaliciousSoundness.lean`.

No `sorry`; axiom audit at the bottom.
-/

open Polynomial Finset

namespace Logup

section StageTwo

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n M K : ℕ}

/-! ### The claim decomposition `claim = S(h) + ∑ₖ λₖ · D̂ₖ(z)` -/

/-- The total helper mass `S(h) = ∑ᵤ ∑ₖ hₖ(u)` — the `(z, λ)`-independent part of the
after-outer mid-claim. -/
noncomputable def helperMass (helpers : HelperMessages F n K) : F :=
  ∑ u : Hypercube n, ∑ k : Fin K, evalOnHypercube (helpers k) u

/-- The multilinear extension of the group-`k` domain-identity violation, evaluated at the
Lagrange point `z`: `D̂ₖ(z) = ∑ᵤ Dₖ(u) · L_H(u, z)`. -/
noncomputable def violationMLE (groups : PartialSumGroups M K)
    (oStmt : ∀ i, OStmtIn F n M i) (mult : MultilinearOracle F n)
    (helpers : HelperMessages F n K) (x : F) (k : Fin K) (z : Fin n → F) : F :=
  ∑ u : Hypercube n,
    domainIdentityTerm groups oStmt mult helpers x k u * lagrangeKernel F u z

/-- **The mid-claim decomposition.**  The after-outer sum-check claim splits as the helper mass
plus the `λ`-batched violation MLEs at `z`. -/
theorem sum_qOnHypercube_eq (groups : PartialSumGroups M K)
    (oStmt : ∀ i, OStmtIn F n M i) (mult : MultilinearOracle F n)
    (helpers : HelperMessages F n K) (x : F) (z : Fin n → F) (lams : Fin K → F) :
    (∑ u : Hypercube n, qOnHypercube groups oStmt mult helpers x z lams u) =
      helperMass helpers +
        ∑ k : Fin K, lams k * violationMLE groups oStmt mult helpers x k z := by
  unfold qOnHypercube helperMass violationMLE
  rw [show (∑ u : Hypercube n, ∑ k : Fin K,
      (evalOnHypercube (helpers k) u +
        lagrangeKernel F u z * lams k * domainIdentityTerm groups oStmt mult helpers x k u)) =
      (∑ u : Hypercube n, ∑ k : Fin K, evalOnHypercube (helpers k) u) +
        ∑ u : Hypercube n, ∑ k : Fin K,
          lagrangeKernel F u z * lams k * domainIdentityTerm groups oStmt mult helpers x k u from by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  ring

/-! ### The kernel MLE polynomial and its Schwartz–Zippel count -/

/-- The Lagrange-kernel multilinear extension of a cube function, as a genuine `MvPolynomial`:
`∑ᵤ values(u)·2⁻ⁿ·∏ⱼ (1 + sign(uⱼ)·Xⱼ)`. -/
noncomputable def kernelMLEPoly (values : Hypercube n → F) : MvPolynomial (Fin n) F :=
  ∑ u : Hypercube n,
    MvPolynomial.C (values u * ((2 : F) ^ n)⁻¹) *
      ∏ j : Fin n, (1 + MvPolynomial.C (bitToSign F (u j)) * MvPolynomial.X j)

theorem kernelMLEPoly_eval (values : Hypercube n → F) (z : Fin n → F) :
    MvPolynomial.eval z (kernelMLEPoly values) =
      ∑ u : Hypercube n, values u * lagrangeKernel F u z := by
  unfold kernelMLEPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_mul, MvPolynomial.eval_C, map_prod]
  simp only [map_add, map_one, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  unfold lagrangeKernel lagrangeKernelAtPoint signPoint
  ring

/-- At a hypercube sign point the kernel MLE reads back the cube value (delta property of the
Lagrange kernel; needs `-1 ≠ 1`). -/
theorem kernelMLEPoly_eval_signPoint (hSigns : (-1 : F) ≠ 1)
    (values : Hypercube n → F) (u₀ : Hypercube n) :
    MvPolynomial.eval (signPoint F u₀) (kernelMLEPoly values) = values u₀ := by
  rw [kernelMLEPoly_eval]
  rw [Finset.sum_eq_single u₀]
  · rw [lagrangeKernel_signPoint F n hSigns u₀ u₀, if_pos rfl, mul_one]
  · intro v _ hv
    rw [lagrangeKernel_signPoint F n hSigns u₀ v, if_neg hv, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ u₀) h

theorem kernelMLEPoly_ne_zero (hSigns : (-1 : F) ≠ 1)
    {values : Hypercube n → F} {u₀ : Hypercube n} (hu : values u₀ ≠ 0) :
    kernelMLEPoly values ≠ 0 := by
  intro h0
  apply hu
  have := kernelMLEPoly_eval_signPoint hSigns values u₀
  rw [h0, map_zero] at this
  exact this.symm

theorem kernelMLEPoly_totalDegree_le (values : Hypercube n → F) :
    (kernelMLEPoly values).totalDegree ≤ n := by
  classical
  unfold kernelMLEPoly
  refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) (Finset.sup_le fun u _ => ?_)
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine le_trans (MvPolynomial.totalDegree_finset_prod _ _) ?_
  calc (∑ j : Fin n,
        (1 + MvPolynomial.C (bitToSign F (u j)) * MvPolynomial.X j).totalDegree)
      ≤ ∑ _j : Fin n, 1 := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
        · rw [MvPolynomial.totalDegree_one]
          exact Nat.zero_le 1
        · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
          rw [MvPolynomial.totalDegree_C, zero_add]
          exact le_of_eq (MvPolynomial.totalDegree_X j)
    _ = n := by rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin]

/-- **Kernel-MLE root count (Schwartz–Zippel).**  A cube function that is nonzero somewhere has a
multilinear extension vanishing on at most `n·|F|ⁿ⁻¹` Lagrange points (stated multiplied through
by `|F|`). -/
theorem card_filter_mleZero_mul_card_le (hSigns : (-1 : F) ≠ 1)
    {values : Hypercube n → F} {u₀ : Hypercube n} (hu : values u₀ ≠ 0) :
    (Finset.univ.filter fun z : Fin n → F =>
        (∑ u : Hypercube n, values u * lagrangeKernel F u z) = 0).card * Fintype.card F
      ≤ n * Fintype.card F ^ n := by
  classical
  have hcount := schwartz_zippel_counting (kernelMLEPoly values)
    (kernelMLEPoly_ne_zero hSigns hu) (fun _ => (Finset.univ : Finset F)) n (Fintype.card F)
    (kernelMLEPoly_totalDegree_le values) Fintype.card_pos
    (fun _ => le_of_eq (Finset.card_univ).symm)
  rw [Fintype.piFinset_univ] at hcount
  have hfilter : (Finset.univ.filter fun z : Fin n → F =>
        (∑ u : Hypercube n, values u * lagrangeKernel F u z) = 0) =
      (Finset.univ.filter fun z : Fin n → F =>
        MvPolynomial.eval z (kernelMLEPoly values) = 0) := by
    refine Finset.filter_congr fun z _ => ?_
    rw [kernelMLEPoly_eval]
  rw [hfilter]
  calc (Finset.univ.filter fun z : Fin n → F =>
        MvPolynomial.eval z (kernelMLEPoly values) = 0).card * Fintype.card F
      ≤ n * ∏ _i : Fin n, (Finset.univ : Finset F).card := hcount
    _ = n * Fintype.card F ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Finset.card_univ, Fintype.card_fin]

/-! ### The affine `λ`-stage count -/

/-- **Affine batching count.**  If some batching coefficient is nonzero, the affine equation
`S₀ + ∑ₖ λₖ·cₖ = 0` has at most `|F|^(K-1)` solutions (stated multiplied through by `|F|`). -/
theorem card_filter_affineZero_mul_card_le (S₀ : F) (c : Fin K → F)
    (k₀ : Fin K) (hc : c k₀ ≠ 0) :
    (Finset.univ.filter fun lams : Fin K → F => S₀ + ∑ k : Fin K, lams k * c k = 0).card *
        Fintype.card F
      ≤ Fintype.card F ^ K := by
  classical
  set P : MvPolynomial (Fin K) F :=
    MvPolynomial.C S₀ + ∑ k : Fin K, MvPolynomial.C (c k) * MvPolynomial.X k with hP
  have hPeval : ∀ lams : Fin K → F,
      MvPolynomial.eval lams P = S₀ + ∑ k : Fin K, lams k * c k := by
    intro lams
    rw [hP]
    rw [map_add, MvPolynomial.eval_C, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    ring
  have hPne : P ≠ 0 := by
    intro h0
    have h0' : ∀ lams : Fin K → F, S₀ + ∑ k : Fin K, lams k * c k = 0 := by
      intro lams
      rw [← hPeval lams, h0, map_zero]
    have hS : S₀ = 0 := by
      have := h0' (fun _ => 0)
      simpa using this
    have := h0' (fun k => if k = k₀ then 1 else 0)
    rw [hS, zero_add] at this
    apply hc
    rw [← this]
    rw [Finset.sum_eq_single k₀]
    · rw [if_pos rfl, one_mul]
    · intro k _ hk
      rw [if_neg hk, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ k₀) h
  have hPdeg : P.totalDegree ≤ 1 := by
    rw [hP]
    refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
    · rw [MvPolynomial.totalDegree_C]
      exact Nat.zero_le 1
    · refine le_trans (MvPolynomial.totalDegree_finset_sum _ _)
        (Finset.sup_le fun k _ => ?_)
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      exact le_of_eq (MvPolynomial.totalDegree_X k)
  have hcount := schwartz_zippel_counting P hPne
    (fun _ => (Finset.univ : Finset F)) 1 (Fintype.card F) hPdeg Fintype.card_pos
    (fun _ => le_of_eq (Finset.card_univ).symm)
  rw [Fintype.piFinset_univ] at hcount
  have hfilter : (Finset.univ.filter fun lams : Fin K → F =>
        S₀ + ∑ k : Fin K, lams k * c k = 0) =
      (Finset.univ.filter fun lams : Fin K → F => MvPolynomial.eval lams P = 0) := by
    refine Finset.filter_congr fun lams _ => ?_
    rw [hPeval]
  rw [hfilter]
  calc (Finset.univ.filter fun lams : Fin K → F =>
        MvPolynomial.eval lams P = 0).card * Fintype.card F
      ≤ 1 * ∏ _i : Fin K, (Finset.univ : Finset F).card := hcount
    _ = Fintype.card F ^ K := by
        rw [one_mul, Finset.prod_const, Finset.card_univ, Finset.card_univ, Fintype.card_fin]

/-! ### The `(z, λ)`-stage master count -/

private theorem card_filter_prod_fst {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    (Φ : A × B → Prop) [DecidablePred Φ] :
    (Finset.univ.filter Φ).card =
      ∑ a : A, (Finset.univ.filter fun b : B => Φ (a, b)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := Prod.fst) (s := Finset.univ.filter Φ) (t := Finset.univ)
    (fun x _ => Finset.mem_univ x.1)]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨hp1, hp2⟩ := hp
    rw [Finset.mem_filter] at hp1
    refine ⟨Finset.mem_univ _, ?_⟩
    have : p = (a, p.2) := by
      rw [← hp2]
    rw [← this]
    exact hp1.2
  · intro p hp p' hp' hpp
    rw [Finset.mem_filter] at hp hp'
    obtain ⟨_, hp2⟩ := hp
    obtain ⟨_, hp2'⟩ := hp'
    exact Prod.ext (hp2.trans hp2'.symm) hpp
  · intro b hb
    rw [Finset.mem_filter] at hb
    refine ⟨(a, b), ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_filter]
    exact ⟨⟨Finset.mem_univ _, hb.2⟩, rfl⟩

/-- **The `(z, λ)`-stage Schwartz–Zippel master count.**  If the after-outer claim is not
identically zero as a function of `(z, λ)` — i.e. NOT (zero helper mass AND all domain identities
satisfied) — then the uniform `(z, λ)` draw zeroes the claim on at most `(n+1)·|F|^(n+K-1)`
points (stated multiplied through by `|F|`). -/
theorem card_filter_claimZero_mul_card_le (hSigns : (-1 : F) ≠ 1)
    (groups : PartialSumGroups M K) (oStmt : ∀ i, OStmtIn F n M i)
    (mult : MultilinearOracle F n) (helpers : HelperMessages F n K) (x : F)
    (hNot : ¬ (helperMass helpers = 0 ∧
      ∀ (k : Fin K) (u : Hypercube n),
        domainIdentityTerm groups oStmt mult helpers x k u = 0)) :
    (Finset.univ.filter fun p : (Fin n → F) × (Fin K → F) =>
        (∑ u : Hypercube n, qOnHypercube groups oStmt mult helpers x p.1 p.2 u) = 0).card *
        Fintype.card F
      ≤ (n + 1) * Fintype.card F ^ (n + K) := by
  classical
  set q := Fintype.card F with hq
  -- Rewrite the claim through the decomposition.
  have hfilter : (Finset.univ.filter fun p : (Fin n → F) × (Fin K → F) =>
        (∑ u : Hypercube n, qOnHypercube groups oStmt mult helpers x p.1 p.2 u) = 0) =
      (Finset.univ.filter fun p : (Fin n → F) × (Fin K → F) =>
        helperMass helpers +
          ∑ k : Fin K, p.2 k * violationMLE groups oStmt mult helpers x k p.1 = 0) := by
    refine Finset.filter_congr fun p _ => ?_
    rw [sum_qOnHypercube_eq]
  rw [hfilter]
  -- Slice the product over `z`.
  rw [card_filter_prod_fst]
  rw [Finset.sum_mul]
  by_cases hS : helperMass helpers = 0
  · -- Helper mass zero: some violation is nonzero on the cube.
    have hD : ∃ (k : Fin K) (u : Hypercube n),
        domainIdentityTerm groups oStmt mult helpers x k u ≠ 0 := by
      by_contra hno
      push_neg at hno
      exact hNot ⟨hS, hno⟩
    obtain ⟨k₀, u₀, hD₀⟩ := hD
    -- Per-`z` bound: affine hyperplane when `D̂_{k₀}(z) ≠ 0`, trivial otherwise.
    have hper : ∀ z : Fin n → F,
        (Finset.univ.filter fun lams : Fin K → F =>
          helperMass helpers +
            ∑ k : Fin K, lams k * violationMLE groups oStmt mult helpers x k z = 0).card * q
        ≤ q ^ K + (if violationMLE groups oStmt mult helpers x k₀ z = 0
            then q ^ (K + 1) else 0) := by
      intro z
      by_cases hV : violationMLE groups oStmt mult helpers x k₀ z = 0
      · rw [if_pos hV]
        refine le_trans ?_ (Nat.le_add_left _ _)
        calc (Finset.univ.filter fun lams : Fin K → F =>
              helperMass helpers +
                ∑ k : Fin K, lams k * violationMLE groups oStmt mult helpers x k z = 0).card * q
            ≤ Fintype.card (Fin K → F) * q :=
              Nat.mul_le_mul_right q (le_trans (Finset.card_filter_le _ _)
                (le_of_eq Finset.card_univ))
          _ = q ^ (K + 1) := by
              rw [Fintype.card_fun, Fintype.card_fin, ← hq, pow_succ]
      · rw [if_neg hV, Nat.add_zero]
        exact card_filter_affineZero_mul_card_le (helperMass helpers)
          (fun k => violationMLE groups oStmt mult helpers x k z) k₀ hV
    refine le_trans (Finset.sum_le_sum fun z _ => hper z) ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, ← hq]
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    -- The kernel-SZ bound on the `z`-degenerate slice.
    have hZ : (Finset.univ.filter fun z : Fin n → F =>
        violationMLE groups oStmt mult helpers x k₀ z = 0).card * q ≤ n * q ^ n := by
      have h := card_filter_mleZero_mul_card_le (n := n) hSigns
        (values := fun u => domainIdentityTerm groups oStmt mult helpers x k₀ u)
        (u₀ := u₀) hD₀
      rw [← hq] at h
      exact h
    calc q ^ n * q ^ K +
          (Finset.univ.filter fun z : Fin n → F =>
            violationMLE groups oStmt mult helpers x k₀ z = 0).card * q ^ (K + 1)
        = q ^ (n + K) +
            ((Finset.univ.filter fun z : Fin n → F =>
              violationMLE groups oStmt mult helpers x k₀ z = 0).card * q) * q ^ K := by
          rw [← pow_add]
          ring
      _ ≤ q ^ (n + K) + (n * q ^ n) * q ^ K := by
          exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hZ) _
      _ = (n + 1) * q ^ (n + K) := by
          ring
  · -- Nonzero helper mass: every `z`-slice is an affine hyperplane (or empty).
    have hper : ∀ z : Fin n → F,
        (Finset.univ.filter fun lams : Fin K → F =>
          helperMass helpers +
            ∑ k : Fin K, lams k * violationMLE groups oStmt mult helpers x k z = 0).card * q
        ≤ q ^ K := by
      intro z
      by_cases hV : ∃ k : Fin K, violationMLE groups oStmt mult helpers x k z ≠ 0
      · obtain ⟨k₀, hk₀⟩ := hV
        exact card_filter_affineZero_mul_card_le (helperMass helpers)
          (fun k => violationMLE groups oStmt mult helpers x k z) k₀ hk₀
      · push_neg at hV
        have hempty : (Finset.univ.filter fun lams : Fin K → F =>
            helperMass helpers +
              ∑ k : Fin K, lams k * violationMLE groups oStmt mult helpers x k z = 0) = ∅ := by
          refine Finset.filter_eq_empty_iff.mpr fun lams _ => ?_
          rw [show (∑ k : Fin K, lams k * violationMLE groups oStmt mult helpers x k z) = 0 from
            Finset.sum_eq_zero fun k _ => by rw [hV k, mul_zero]]
          rw [add_zero]
          exact hS
        rw [hempty, Finset.card_empty, Nat.zero_mul]
        exact Nat.zero_le _
    refine le_trans (Finset.sum_le_sum fun z _ => hper z) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ← hq,
      smul_eq_mul, ← pow_add]
    exact Nat.le_mul_of_pos_left _ (Nat.succ_pos n)

end StageTwo

section StageOne

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n M : ℕ}

/-! ### Pole values and the per-`m` cleared grand-sum numerator -/

/-- The value carried by term `i` on row `u` (`t(u)` for the table term, `f_c(u)` for column
terms): the term denominator is `x + termValue`. -/
noncomputable def termValue (oStmt : ∀ i, OStmtIn F n M i) (i : TermIdx M)
    (u : Hypercube n) : F :=
  match termToInput i with
  | .table => evalOnHypercube (tableOracle oStmt) u
  | .column c => evalOnHypercube (columnOracle oStmt c) u

theorem termPhi_eq_add_termValue (oStmt : ∀ i, OStmtIn F n M i) (x : F)
    (i : TermIdx M) (u : Hypercube n) :
    termPhi oStmt x i u = x + termValue oStmt i u := by
  unfold termPhi termValue
  cases termToInput i <;> rfl

/-- The finset of all pole values: every value carried by some term on some row. -/
noncomputable def poleValues (oStmt : ∀ i, OStmtIn F n M i) : Finset F :=
  Finset.univ.image fun p : TermIdx M × Hypercube n => termValue oStmt p.1 p.2

theorem termValue_mem_poleValues (oStmt : ∀ i, OStmtIn F n M i)
    (i : TermIdx M) (u : Hypercube n) : termValue oStmt i u ∈ poleValues oStmt :=
  Finset.mem_image.mpr ⟨(i, u), Finset.mem_univ _, rfl⟩

theorem tableValue_mem_poleValues (oStmt : ∀ i, OStmtIn F n M i) (u : Hypercube n) :
    evalOnHypercube (tableOracle oStmt) u ∈ poleValues oStmt := by
  have := termValue_mem_poleValues oStmt 0 u
  rw [show termValue oStmt 0 u = evalOnHypercube (tableOracle oStmt) u from rfl] at this
  exact this

theorem columnValue_mem_poleValues (oStmt : ∀ i, OStmtIn F n M i)
    (c : Fin M) (u : Hypercube n) :
    evalOnHypercube (columnOracle oStmt c) u ∈ poleValues oStmt := by
  have := termValue_mem_poleValues oStmt ⟨c.val + 1, Nat.succ_lt_succ c.isLt⟩ u
  rw [show termValue oStmt ⟨c.val + 1, Nat.succ_lt_succ c.isLt⟩ u =
      evalOnHypercube (columnOracle oStmt c) u from by
    unfold termValue
    rw [show termToInput (⟨c.val + 1, Nat.succ_lt_succ c.isLt⟩ : TermIdx M) = .column c from by
      unfold termToInput
      simp]] at this
  exact this

theorem poleValues_card_le (oStmt : ∀ i, OStmtIn F n M i) :
    (poleValues oStmt).card ≤ (M + 1) * 2 ^ n := by
  refine le_trans (Finset.card_image_le) ?_
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, card_hypercube]

theorem poleValues_nonempty (oStmt : ∀ i, OStmtIn F n M i) :
    (poleValues oStmt).Nonempty :=
  ⟨_, tableValue_mem_poleValues oStmt (fun _ => 0)⟩

/-- **The per-`m` cleared grand-sum numerator.**  The numerator of the malicious grand sum
`∑ᵤ m(u)/(x + t(u)) − ∑_{(c,u)} 1/(x + f_c(u))` with denominators cleared over the *set* of
pole values (one linear factor per distinct value). -/
noncomputable def clearedNumerator (oStmt : ∀ i, OStmtIn F n M i)
    (mult : MultilinearOracle F n) : Polynomial F :=
  (∑ u : Hypercube n, Polynomial.C (evalOnHypercube mult u) *
      ∏ v ∈ (poleValues oStmt).erase (evalOnHypercube (tableOracle oStmt) u),
        (Polynomial.X + Polynomial.C v)) -
    ∑ p : Fin M × Hypercube n,
      ∏ v ∈ (poleValues oStmt).erase (evalOnHypercube (columnOracle oStmt p.1) p.2),
        (Polynomial.X + Polynomial.C v)

/-- Degree bound: clearing over the pole-value *set* gives the paper degree
`≤ |poleValues| − 1 ≤ (M+1)·2ⁿ − 1`. -/
theorem clearedNumerator_natDegree_le (oStmt : ∀ i, OStmtIn F n M i)
    (mult : MultilinearOracle F n) :
    (clearedNumerator oStmt mult).natDegree ≤ (poleValues oStmt).card - 1 := by
  classical
  have hprod : ∀ (w : F), w ∈ poleValues oStmt →
      (∏ v ∈ (poleValues oStmt).erase w, (Polynomial.X + Polynomial.C v)).natDegree ≤
        (poleValues oStmt).card - 1 := by
    intro w hw
    refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    calc (∑ v ∈ (poleValues oStmt).erase w, (Polynomial.X + Polynomial.C v).natDegree)
        ≤ ∑ _v ∈ (poleValues oStmt).erase w, 1 := by
          refine Finset.sum_le_sum fun v _ => ?_
          refine le_trans (Polynomial.natDegree_add_le _ _) ?_
          simp [Polynomial.natDegree_X, Polynomial.natDegree_C]
      _ = ((poleValues oStmt).erase w).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ = (poleValues oStmt).card - 1 := Finset.card_erase_of_mem hw
  unfold clearedNumerator
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun u _ => ?_
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    exact hprod _ (tableValue_mem_poleValues oStmt u)
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun p _ => ?_
    exact hprod _ (columnValue_mem_poleValues oStmt p.1 p.2)

/-- **Nonvanishing for a bad lookup, for *every* prover multiplicity.**  The residue test at a
column-only value `a₀`: the multiplicity terms all carry the factor `(X + a₀)` (the table never
takes the value `a₀`), while the surviving column terms contribute
`−(lookup count of a₀)·∏_{v ≠ a₀}(−a₀ + v) ≠ 0` (the count is nonzero in `F` by the
characteristic bound). -/
theorem clearedNumerator_ne_zero (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M))
    (mult : MultilinearOracle F n) :
    clearedNumerator oStmt mult ≠ 0 := by
  classical
  obtain ⟨a₀, hlook, htab⟩ := bad_lookup_exists_column_only_value stmt oStmt hBad
  -- `a₀` is a column value, hence a pole value.
  have ha₀mem : a₀ ∈ poleValues oStmt := by
    have hpos : 0 < ((Finset.univ : Finset (Fin M × Hypercube n)).filter fun ix =>
        evalOnHypercube (columnOracle oStmt ix.1) ix.2 = a₀).card := hlook
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hp
    rw [← hp.2]
    exact columnValue_mem_poleValues oStmt p.1 p.2
  -- The table never takes the value `a₀`.
  have htabne : ∀ u : Hypercube n, evalOnHypercube (tableOracle oStmt) u ≠ a₀ := by
    intro u hu
    have := tableMultiplicityCount_pos_of_eval oStmt u
    rw [hu, htab] at this
    exact absurd this (lt_irrefl 0)
  intro h0
  have heval : (clearedNumerator oStmt mult).eval (-a₀) = 0 := by
    rw [h0, Polynomial.eval_zero]
  unfold clearedNumerator at heval
  rw [Polynomial.eval_sub, Polynomial.eval_finset_sum, Polynomial.eval_finset_sum] at heval
  -- The multiplicity terms all vanish at `-a₀`.
  have hm0 : (∑ u : Hypercube n, (Polynomial.C (evalOnHypercube mult u) *
      ∏ v ∈ (poleValues oStmt).erase (evalOnHypercube (tableOracle oStmt) u),
        (Polynomial.X + Polynomial.C v)).eval (-a₀)) = 0 := by
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_prod]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero
      (Finset.mem_erase.mpr ⟨fun h => htabne u h.symm, ha₀mem⟩) ?_)
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, neg_add_cancel]
  rw [hm0, zero_sub, neg_eq_zero] at heval
  -- The column terms collapse to `(lookup count of a₀) · ∏_{v ≠ a₀}(−a₀ + v)`.
  have hcol : ∀ p : Fin M × Hypercube n,
      ((∏ v ∈ (poleValues oStmt).erase (evalOnHypercube (columnOracle oStmt p.1) p.2),
        (Polynomial.X + Polynomial.C v)).eval (-a₀)) =
      (if evalOnHypercube (columnOracle oStmt p.1) p.2 = a₀
        then ∏ v ∈ (poleValues oStmt).erase a₀, (-a₀ + v) else 0) := by
    intro p
    rw [Polynomial.eval_prod]
    by_cases hp : evalOnHypercube (columnOracle oStmt p.1) p.2 = a₀
    · rw [if_pos hp, hp]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    · rw [if_neg hp]
      refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun h => hp h.symm, ha₀mem⟩) ?_
      rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, neg_add_cancel]
  rw [Finset.sum_congr rfl fun p _ => hcol p] at heval
  rw [← Finset.sum_filter, Finset.sum_const] at heval
  have hcount : ((Finset.univ : Finset (Fin M × Hypercube n)).filter fun p =>
      evalOnHypercube (columnOracle oStmt p.1) p.2 = a₀).card =
      lookupMultiplicityCount oStmt a₀ := rfl
  rw [hcount, nsmul_eq_mul] at heval
  rcases mul_eq_zero.mp heval with hc | hprod
  · exact lookupMultiplicityCount_natCast_ne_zero stmt oStmt a₀ hlook hc
  · rw [Finset.prod_eq_zero_iff] at hprod
    obtain ⟨v, hv, hv0⟩ := hprod
    rw [Finset.mem_erase] at hv
    exact hv.1 (by linear_combination hv0)

/-- Away from every pole, the cleared numerator factors as the full pole product times the
malicious grand sum. -/
theorem clearedNumerator_eval_nonpole (oStmt : ∀ i, OStmtIn F n M i)
    (mult : MultilinearOracle F n) (x : F)
    (hx : ∀ v ∈ poleValues oStmt, x + v ≠ 0) :
    (clearedNumerator oStmt mult).eval x =
      (∏ v ∈ poleValues oStmt, (x + v)) *
        ((∑ u : Hypercube n,
            evalOnHypercube mult u / (x + evalOnHypercube (tableOracle oStmt) u)) -
          ∑ p : Fin M × Hypercube n,
            1 / (x + evalOnHypercube (columnOracle oStmt p.1) p.2)) := by
  classical
  have herase : ∀ (w : F), w ∈ poleValues oStmt →
      (∏ v ∈ (poleValues oStmt).erase w, (x + v)) =
        (∏ v ∈ poleValues oStmt, (x + v)) / (x + w) := by
    intro w hw
    rw [← Finset.mul_prod_erase (poleValues oStmt) (fun v => x + v) hw]
    rw [mul_comm, mul_div_assoc, div_self (hx w hw), mul_one]
  unfold clearedNumerator
  rw [Polynomial.eval_sub, Polynomial.eval_finset_sum, Polynomial.eval_finset_sum]
  rw [mul_sub]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    rw [herase _ (tableValue_mem_poleValues oStmt u)]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Polynomial.eval_prod]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    rw [herase _ (columnValue_mem_poleValues oStmt p.1 p.2)]
    rw [one_div, div_eq_mul_inv]

/-! ### Degenerate challenges (≥ 2 vanishing denominators in one group/row) -/

/-- The degenerate challenges: those `x` for which some group has at least two vanishing term
denominators on a single row.  There the domain identity stops pinning the helper value (the
identity holds for *every* `hₖ(u)`), so these must be charged to the `x`-stage bad set.  They are
`m`-independent. -/
noncomputable def degenerateChallenges (params : ProtocolParams M)
    (oStmt : ∀ i, OStmtIn F n M i) : Finset F := by
  classical
  exact Finset.univ.filter fun x : F =>
    ∃ (u : Hypercube n) (k : Fin params.numGroups),
      1 < ((canonicalGroups params k).filter fun i => termPhi oStmt x i u = 0).card

theorem mem_degenerateChallenges_iff (params : ProtocolParams M)
    (oStmt : ∀ i, OStmtIn F n M i) (x : F) :
    x ∈ degenerateChallenges params oStmt ↔
      ∃ (u : Hypercube n) (k : Fin params.numGroups),
        1 < ((canonicalGroups params k).filter fun i => termPhi oStmt x i u = 0).card := by
  classical
  unfold degenerateChallenges
  simp

/-- **Degenerate challenges are bounded by the value-multiplicity excess**
`(M+1)·2ⁿ − |poleValues|`: each degenerate `x` makes `−x` a pole value carried by at least two
term/row pairs. -/
theorem degenerateChallenges_card_le (params : ProtocolParams M)
    (oStmt : ∀ i, OStmtIn F n M i) :
    (degenerateChallenges params oStmt).card ≤ (M + 1) * 2 ^ n - (poleValues oStmt).card := by
  classical
  set count : F → ℕ := fun v =>
    ((Finset.univ : Finset (TermIdx M × Hypercube n)).filter fun p =>
      termValue oStmt p.1 p.2 = v).card with hcount
  -- The multi-carried pole values.
  set multi : Finset F := (poleValues oStmt).filter (fun v => 2 ≤ count v) with hmulti
  -- Step 1: `x ↦ -x` maps degenerate challenges into `multi`, injectively.
  have hmap : ∀ x ∈ degenerateChallenges params oStmt, -x ∈ multi := by
    intro x hx
    rw [mem_degenerateChallenges_iff] at hx
    obtain ⟨u, k, hk⟩ := hx
    -- two distinct group members with vanishing denominators on row `u`
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hk
    rw [Finset.mem_filter] at hi hj
    have hival : termValue oStmt i u = -x := by
      have h := hi.2
      rw [termPhi_eq_add_termValue] at h
      linear_combination h
    have hjval : termValue oStmt j u = -x := by
      have h := hj.2
      rw [termPhi_eq_add_termValue] at h
      linear_combination h
    rw [hmulti, Finset.mem_filter]
    constructor
    · rw [← hival]
      exact termValue_mem_poleValues oStmt i u
    · -- both `(i, u)` and `(j, u)` carry the value `-x`
      rw [hcount]
      have hsub : ({(i, u), (j, u)} : Finset (TermIdx M × Hypercube n)) ⊆
          (Finset.univ.filter fun p => termValue oStmt p.1 p.2 = -x) := by
        intro p hp
        rw [Finset.mem_insert, Finset.mem_singleton] at hp
        rw [Finset.mem_filter]
        rcases hp with rfl | rfl
        · exact ⟨Finset.mem_univ _, hival⟩
        · exact ⟨Finset.mem_univ _, hjval⟩
      refine le_trans (le_of_eq ?_) (Finset.card_le_card hsub)
      rw [Finset.card_insert_of_notMem (by
        rw [Finset.mem_singleton]
        intro h
        exact hij (congrArg Prod.fst h)), Finset.card_singleton]
  have hinj : (degenerateChallenges params oStmt).card ≤ multi.card := by
    refine Finset.card_le_card_of_injOn (fun x => -x) hmap ?_
    intro a _ b _ hab
    exact neg_injective hab
  -- Step 2: `|multi| ≤ total − |poleValues|` by the multiplicity-excess argument.
  have htotal : (∑ v ∈ poleValues oStmt, count v) = (M + 1) * 2 ^ n := by
    rw [hcount]
    rw [← Finset.card_eq_sum_card_fiberwise
      (f := fun p : TermIdx M × Hypercube n => termValue oStmt p.1 p.2)
      (s := Finset.univ) (t := poleValues oStmt)
      (fun p _ => termValue_mem_poleValues oStmt p.1 p.2)]
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, card_hypercube]
  have hone : ∀ v ∈ poleValues oStmt, 1 + (if v ∈ multi then 1 else 0) ≤ count v := by
    intro v hv
    have h1 : 1 ≤ count v := by
      rw [hcount]
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hv
      refine Finset.card_pos.mpr ⟨p, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hp⟩
    by_cases hvm : v ∈ multi
    · rw [if_pos hvm]
      rw [hmulti, Finset.mem_filter] at hvm
      have h2 := hvm.2
      omega
    · rw [if_neg hvm, Nat.add_zero]
      exact h1
  have hfm : (poleValues oStmt).filter (fun v => v ∈ multi) = multi := by
    rw [hmulti]
    ext v
    simp only [Finset.mem_filter]
    tauto
  have hexcess : (poleValues oStmt).card + multi.card ≤ ∑ v ∈ poleValues oStmt, count v := by
    calc (poleValues oStmt).card + multi.card
        = ∑ v ∈ poleValues oStmt, (1 + if v ∈ multi then 1 else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
          congr 1
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one, hfm]
      _ ≤ ∑ v ∈ poleValues oStmt, count v := Finset.sum_le_sum hone
  rw [htotal] at hexcess
  omega

/-! ### The per-`m` `x`-stage bad set and its uniform cardinality bound -/

/-- **The `x`-stage bad challenge set for prover multiplicity `m`**: the roots of the per-`m`
cleared grand-sum numerator together with the (`m`-independent) degenerate challenges.  Outside
this set (and the guard-rejected table poles), no helper message can zero the mid-claim
identically in `(z, λ)` (`claim_not_identicallyZero`). -/
noncomputable def outerBadChallenges (params : ProtocolParams M)
    (oStmt : ∀ i, OStmtIn F n M i) (mult : MultilinearOracle F n) : Finset F :=
  (clearedNumerator oStmt mult).roots.toFinset ∪ degenerateChallenges params oStmt

/-- **The uniform (paper-budget) cardinality bound** `|BadX(m)| ≤ (M+1)·2ⁿ − 1`, valid for every
prover multiplicity `m`: `≤ |poleValues| − 1` roots plus `≤ (M+1)·2ⁿ − |poleValues|` degenerate
challenges. -/
theorem outerBadChallenges_card_le (params : ProtocolParams M)
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M))
    (mult : MultilinearOracle F n) :
    (outerBadChallenges params oStmt mult).card ≤ (M + 1) * 2 ^ n - 1 := by
  classical
  have hroots : (clearedNumerator oStmt mult).roots.toFinset.card ≤
      (poleValues oStmt).card - 1 := by
    calc (clearedNumerator oStmt mult).roots.toFinset.card
        ≤ Multiset.card (clearedNumerator oStmt mult).roots :=
          (clearedNumerator oStmt mult).roots.toFinset_card_le
      _ ≤ (clearedNumerator oStmt mult).natDegree :=
          Polynomial.card_roots' (clearedNumerator oStmt mult)
      _ ≤ (poleValues oStmt).card - 1 := clearedNumerator_natDegree_le oStmt mult
  have hdeg := degenerateChallenges_card_le params oStmt
  have hD1 : 1 ≤ (poleValues oStmt).card := Finset.card_pos.mpr (poleValues_nonempty oStmt)
  have hDT : (poleValues oStmt).card ≤ (M + 1) * 2 ^ n := poleValues_card_le oStmt
  calc (outerBadChallenges params oStmt mult).card
      ≤ (clearedNumerator oStmt mult).roots.toFinset.card +
          (degenerateChallenges params oStmt).card := Finset.card_union_le _ _
    _ ≤ ((poleValues oStmt).card - 1) + ((M + 1) * 2 ^ n - (poleValues oStmt).card) :=
        Nat.add_le_add hroots hdeg
    _ ≤ (M + 1) * 2 ^ n - 1 := by omega

/-! ### The per-challenge master lemma: good `x` forces a non-identically-zero claim -/

/-- **The stage-2 master input.**  For a bad lookup, at any challenge `x` passing the table-pole
guard and outside `outerBadChallenges params oStmt m`, **no** helper message makes the after-outer
mid-claim identically zero in `(z, λ)`:

* if `x` avoids every pole, the satisfied domain identities force the honest helper values, whose
  total mass is the malicious grand sum — nonzero because `x` is not a root of the cleared
  numerator;
* if `x` hits a column pole, the (non-degenerate, hence unique) vanishing denominator in its
  group forces the domain-identity violation `Dₖ(u) = ∏_{j ≠ i₀} φⱼ(u) ≠ 0` outright. -/
theorem claim_not_identicallyZero (params : ProtocolParams M)
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M))
    (mult : MultilinearOracle F n) (x : F)
    (hGuard : ∀ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u ≠ 0)
    (hx : x ∉ outerBadChallenges params oStmt mult)
    (helpers : HelperMessages F n params.numGroups) :
    ¬ (helperMass helpers = 0 ∧
        ∀ (k : Fin params.numGroups) (u : Hypercube n),
          domainIdentityTerm (canonicalGroups params) oStmt mult helpers x k u = 0) := by
  classical
  rintro ⟨hS, hD⟩
  have hxroots : x ∉ (clearedNumerator oStmt mult).roots.toFinset := fun hmem =>
    hx (Finset.mem_union_left _ hmem)
  have hxdeg : x ∉ degenerateChallenges params oStmt := fun hmem =>
    hx (Finset.mem_union_right _ hmem)
  by_cases hpole : ∀ p : Fin M × Hypercube n,
      x + evalOnHypercube (columnOracle oStmt p.1) p.2 ≠ 0
  · -- `x` avoids every pole: helpers are forced honest, so `S = grand sum ≠ 0`.
    have hphi : ∀ (i : TermIdx M) (u : Hypercube n), termPhi oStmt x i u ≠ 0 := by
      intro i u
      unfold termPhi
      cases hidx : termToInput i with
      | table => simpa [phi] using hGuard u
      | column c => simpa [phi] using hpole (c, u)
    -- The domain identities pin every helper value.
    have hval : ∀ (k : Fin params.numGroups) (u : Hypercube n),
        evalOnHypercube (helpers k) u =
          helperValue (canonicalGroups params) oStmt mult x k u := by
      intro k u
      have h0 := hD k u
      unfold domainIdentityTerm at h0
      have h2 := helperValue_mul_denominatorProduct (canonicalGroups params) oStmt mult x k u
        (fun i _ => hphi i u)
      have hprod_ne : denominatorProduct (canonicalGroups params) oStmt x k u ≠ 0 := by
        unfold denominatorProduct
        exact Finset.prod_ne_zero_iff.mpr fun i _ => hphi i u
      have hsub : (evalOnHypercube (helpers k) u -
          helperValue (canonicalGroups params) oStmt mult x k u) *
            denominatorProduct (canonicalGroups params) oStmt x k u = 0 := by
        rw [sub_mul, h2]
        rw [sub_eq_zero] at h0 ⊢
        exact h0
      rcases mul_eq_zero.mp hsub with hzero | habs
      · rw [sub_eq_zero] at hzero
        exact hzero
      · exact absurd habs hprod_ne
    -- The forced helper mass is the malicious grand sum.
    have hmass : helperMass helpers =
        (∑ u : Hypercube n,
            evalOnHypercube mult u / (x + evalOnHypercube (tableOracle oStmt) u)) -
          ∑ p : Fin M × Hypercube n,
            1 / (x + evalOnHypercube (columnOracle oStmt p.1) p.2) := by
      unfold helperMass
      rw [Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun k _ => hval k u]
      have hgroup : ∀ u : Hypercube n,
          (∑ k : Fin params.numGroups,
            helperValue (canonicalGroups params) oStmt mult x k u) =
          ∑ i : TermIdx M, termNumerator mult i u / termPhi oStmt x i u := by
        intro u
        unfold helperValue
        exact canonicalGroups_sum_partition F M params
          (fun i => termNumerator mult i u / termPhi oStmt x i u)
      rw [Finset.sum_congr rfl fun u _ => hgroup u]
      have hterm : ∀ u : Hypercube n,
          (∑ i : TermIdx M, termNumerator mult i u / termPhi oStmt x i u) =
            evalOnHypercube mult u / (x + evalOnHypercube (tableOracle oStmt) u) +
              ∑ c : Fin M, (-1 : F) / (x + evalOnHypercube (columnOracle oStmt c) u) := by
        intro u
        rw [show (∑ i : TermIdx M, termNumerator mult i u / termPhi oStmt x i u) =
            ∑ i : Fin (M + 1), termNumerator mult i u / termPhi oStmt x i u from rfl]
        rw [Fin.sum_univ_succ]
        congr 1
      rw [Finset.sum_congr rfl fun u _ => hterm u]
      rw [Finset.sum_add_distrib, sub_eq_add_neg]
      congr 1
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [neg_div]
    -- Nonzero by the cleared-numerator root exclusion.
    have hnonpole : ∀ v ∈ poleValues oStmt, x + v ≠ 0 := by
      intro v hv
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hv
      rw [← hp]
      rw [show termValue oStmt p.1 p.2 = termPhi oStmt 0 p.1 p.2 from by
        rw [termPhi_eq_add_termValue, zero_add]]
      rw [termPhi_eq_add_termValue, zero_add, ← termPhi_eq_add_termValue]
      unfold termPhi
      cases hidx : termToInput p.1 with
      | table => simpa [phi] using hGuard p.2
      | column c => simpa [phi] using hpole (c, p.2)
    have hne := clearedNumerator_ne_zero stmt oStmt hBad mult
    have hevalne : (clearedNumerator oStmt mult).eval x ≠ 0 := by
      intro h0
      exact hxroots (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne).mpr h0))
    rw [clearedNumerator_eval_nonpole oStmt mult x hnonpole] at hevalne
    rcases mul_ne_zero_iff.mp hevalne with ⟨_, hsum_ne⟩
    rw [← hmass] at hsum_ne
    exact hsum_ne hS
  · -- `x` hits a column pole: the unique vanishing denominator forces a violation.
    push_neg at hpole
    obtain ⟨p₀, hp₀⟩ := hpole
    set j₀ : TermIdx M := ⟨p₀.1.val + 1, Nat.succ_lt_succ p₀.1.isLt⟩ with hj₀
    have hphij₀ : termPhi oStmt x j₀ p₀.2 = 0 := by
      rw [hj₀, termPhi_succ]
      exact hp₀
    obtain ⟨k₀, hk₀⟩ := params.exists_mem_group j₀
    -- Non-degeneracy: `j₀` is the only vanishing denominator in its group on this row.
    have hunique : ∀ i ∈ canonicalGroups params k₀, i ≠ j₀ → termPhi oStmt x i p₀.2 ≠ 0 := by
      intro i hi hij hzero
      apply hxdeg
      rw [mem_degenerateChallenges_iff]
      refine ⟨p₀.2, k₀, ?_⟩
      refine Finset.one_lt_card.mpr ⟨i, ?_, j₀, ?_, hij⟩
      · rw [Finset.mem_filter]
        exact ⟨hi, hzero⟩
      · rw [Finset.mem_filter]
        exact ⟨hk₀, hphij₀⟩
    -- The group-`k₀` violation at row `p₀.2` is forced nonzero.
    have hDk₀ : domainIdentityTerm (canonicalGroups params) oStmt mult helpers x k₀ p₀.2 ≠ 0 := by
      unfold domainIdentityTerm
      have hdenprod : denominatorProduct (canonicalGroups params) oStmt x k₀ p₀.2 = 0 := by
        unfold denominatorProduct
        exact Finset.prod_eq_zero hk₀ hphij₀
      rw [hdenprod, mul_zero, zero_sub, neg_ne_zero]
      rw [Finset.sum_eq_single j₀]
      · rw [hj₀, termNumerator_succ]
        rw [neg_one_mul, neg_ne_zero]
        exact Finset.prod_ne_zero_iff.mpr fun i hi =>
          hunique i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
      · intro i hi hij
        exact mul_eq_zero_of_right _
          (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun h => hij h.symm, hk₀⟩) hphij₀)
      · intro habs
        exact absurd hk₀ habs
    exact hDk₀ (hD k₀ p₀.2)

end StageOne

end Logup

/-! ### Axiom audit (issue #13 malicious outer-claim mathematics) -/

#print axioms Logup.sum_qOnHypercube_eq
#print axioms Logup.card_filter_mleZero_mul_card_le
#print axioms Logup.card_filter_affineZero_mul_card_le
#print axioms Logup.card_filter_claimZero_mul_card_le
#print axioms Logup.clearedNumerator_natDegree_le
#print axioms Logup.clearedNumerator_ne_zero
#print axioms Logup.clearedNumerator_eval_nonpole
#print axioms Logup.degenerateChallenges_card_le
#print axioms Logup.outerBadChallenges_card_le
#print axioms Logup.claim_not_identicallyZero

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckBridge
import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckPolynomial
import ArkLib.ProofSystem.Logup.Security.ConsistentClaimCore

/-!
# Batching-binding, step 1: a vanishing batched claim binds the helpers (issue #13)

Obligation 2 (first half) of the `hOuter@midLanguage` closing blueprint: if the batched LogUp
hypercube sum vanishes for **all** `(z, batchingScalars)` values, then the batching genuinely
binds the prover's helper oracles —

* `qsum_affine_in_batch` — the raw decomposition `∑_u q = A + ∑_k b_k · C_k(z)` (helper mass plus
  batch-weighted Lagrange-mixed domain-identity coefficients);
* `qsum_vanishing_forall` — evaluation at `b = 0` extracts `A = 0`; at `b = eₖ`,
  `z = signPoint u₀` the Lagrange delta (`lagrangeKernel_signPoint`) extracts
  `domainIdentityTerm k u₀ = 0` for every group `k` and row `u₀`.

The remaining half of the obligation is the partial-fraction clearing chain: `DIT ≡ 0` and
helper mass `0` force the grand-sum identity at `x` (inputs:
`helperValue_mul_denominatorProduct`, the `SoundnessConverse` count algebra), placing `x` in the
sharp Schwartz–Zippel locus — the round-2 monotonicity of the claim-based RBR state function.
Axiom-clean.
-/

open scoped BigOperators

namespace Logup

variable {F : Type} [Field F]
variable {n M K : ℕ}

/-- Raw affine-in-batch decomposition of the batched hypercube sum. -/
theorem qsum_affine_in_batch (groups : PartialSumGroups M K)
    (oStmt : ∀ i, OStmtIn F n M i) (multiplicity : MultilinearOracle F n)
    (helpers : HelperMessages F n K) (x : F) (z : Fin n → F) (b : Fin K → F) :
    ∑ u : Hypercube n, qOnHypercube groups oStmt multiplicity helpers x z b u
      = (∑ k : Fin K, ∑ u : Hypercube n, evalOnHypercube (helpers k) u)
        + ∑ k : Fin K, b k * (∑ u : Hypercube n,
            lagrangeKernel F u z * domainIdentityTerm groups oStmt multiplicity helpers x k u) := by
  unfold qOnHypercube
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  ring

/-- **Batching-binding, step 1 (coefficient extraction).** If the batched hypercube sum vanishes
for ALL `(z, batch)` values, then the helper mass vanishes and EVERY domain-identity term
vanishes at every row: the batching genuinely binds the helpers to the partial-fraction
identities. Evaluation at `batch = 0` extracts the helper mass; at `batch = eₖ`,
`z = signPoint u₀` the Lagrange delta extracts each `DIT k u₀`. -/
theorem qsum_vanishing_forall (hSigns : (-1 : F) ≠ 1)
    (groups : PartialSumGroups M K)
    (oStmt : ∀ i, OStmtIn F n M i) (multiplicity : MultilinearOracle F n)
    (helpers : HelperMessages F n K) (x : F)
    (h : ∀ (z : Fin n → F) (b : Fin K → F),
      ∑ u : Hypercube n, qOnHypercube groups oStmt multiplicity helpers x z b u = 0) :
    (∑ k : Fin K, ∑ u : Hypercube n, evalOnHypercube (helpers k) u) = 0 ∧
      ∀ (k : Fin K) (u₀ : Hypercube n),
        domainIdentityTerm groups oStmt multiplicity helpers x k u₀ = 0 := by
  classical
  -- helper mass: evaluate at batch = 0
  have hA : (∑ k : Fin K, ∑ u : Hypercube n, evalOnHypercube (helpers k) u) = 0 := by
    have h0 := h (fun _ => 0) 0
    rw [qsum_affine_in_batch] at h0
    simpa using h0
  refine ⟨hA, fun k u₀ => ?_⟩
  -- DIT k u₀: evaluate at z = signPoint u₀, batch = single k 1
  have hk := h (signPoint F u₀) (Pi.single k 1)
  rw [qsum_affine_in_batch, hA, zero_add] at hk
  rw [Finset.sum_eq_single k] at hk
  · rw [Pi.single_eq_same, one_mul] at hk
    have hdelta : (∑ u : Hypercube n,
        lagrangeKernel F u (signPoint F u₀) *
          domainIdentityTerm groups oStmt multiplicity helpers x k u)
        = domainIdentityTerm groups oStmt multiplicity helpers x k u₀ := by
      rw [Finset.sum_congr rfl (fun u _ => by
        rw [lagrangeKernel_signPoint (F := F) (n := n) hSigns u₀ u])]
      simp [Finset.sum_ite_eq']
    rwa [hdelta] at hk
  · intro b _ hbk
    rw [Pi.single_eq_of_ne hbk, zero_mul]
  · intro habs
    exact absurd (Finset.mem_univ k) habs

/-- **Batching-binding, step 2a (pointwise helper unbinding).** A vanishing domain-identity term
at a pole-free row forces the prover's helper value to equal the honest partial-fraction value:
`helpers k u = helperValue k u`. Cancellation of the nonzero denominator product against
`helperValue_mul_denominatorProduct`. -/
theorem helpers_eq_helperValue_of_DIT_zero
    (groups : PartialSumGroups M K)
    (oStmt : ∀ i, OStmtIn F n M i) (multiplicity : MultilinearOracle F n)
    (helpers : HelperMessages F n K) (x : F) (k : Fin K) (u : Hypercube n)
    (hden : ∀ i ∈ groups k, termPhi oStmt x i u ≠ 0)
    (hDIT : domainIdentityTerm groups oStmt multiplicity helpers x k u = 0) :
    evalOnHypercube (helpers k) u = helperValue groups oStmt multiplicity x k u := by
  have hprod : denominatorProduct groups oStmt x k u ≠ 0 := by
    unfold denominatorProduct
    exact Finset.prod_ne_zero_iff.mpr hden
  have hclear := helperValue_mul_denominatorProduct groups oStmt multiplicity x k u hden
  unfold domainIdentityTerm at hDIT
  rw [sub_eq_zero] at hDIT
  rw [← hclear] at hDIT
  exact mul_right_cancel₀ hprod hDIT

/-- **Batching-binding, step 2b (mass transfer).** If every domain-identity term vanishes at a
pole-free challenge, the helper mass equals the total honest partial-fraction mass: the prover's
claimed helpers carry exactly the grand rational sum. -/
theorem helper_mass_eq_grand_sum_of_DIT_zero
    (groups : PartialSumGroups M K)
    (oStmt : ∀ i, OStmtIn F n M i) (multiplicity : MultilinearOracle F n)
    (helpers : HelperMessages F n K) (x : F)
    (hden : ∀ (k : Fin K) (u : Hypercube n), ∀ i ∈ groups k, termPhi oStmt x i u ≠ 0)
    (hDIT : ∀ (k : Fin K) (u : Hypercube n),
      domainIdentityTerm groups oStmt multiplicity helpers x k u = 0) :
    (∑ k : Fin K, ∑ u : Hypercube n, evalOnHypercube (helpers k) u)
      = ∑ k : Fin K, ∑ u : Hypercube n, helperValue groups oStmt multiplicity x k u := by
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun u _ => ?_))
  exact helpers_eq_helperValue_of_DIT_zero groups oStmt multiplicity helpers x k u
    (hden k u) (hDIT k u)

/-- **Batching-binding, step 2c (ungrouping).** Under full domain-identity consistency at a
pole-free challenge, the prover's helper mass is the ungrouped LogUp partial-fraction total over
all terms. This bridges the row/group helper identities to the cleared numerator root count. -/
theorem consistentClaim_eq_termSum (params : ProtocolParams M)
    (oStmt : ∀ i, OStmtIn F n M i)
    (multiplicity : MultilinearOracle F n) (helpers : HelperMessages F n params.numGroups)
    (xChallenge : F)
    (hden : ∀ (i : TermIdx M) (u : Hypercube n), termPhi oStmt xChallenge i u ≠ 0)
    (hcons : ∀ (k : Fin params.numGroups) (u : Hypercube n),
      domainIdentityTerm (canonicalGroups params) oStmt multiplicity helpers xChallenge k u = 0) :
    (∑ u : Hypercube n, ∑ k : Fin params.numGroups, evalOnHypercube (helpers k) u)
      = ∑ u : Hypercube n, ∑ i : TermIdx M,
          termNumerator multiplicity i u / termPhi oStmt xChallenge i u := by
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have hpin : ∑ k : Fin params.numGroups, evalOnHypercube (helpers k) u
      = ∑ k : Fin params.numGroups,
          helperValue (canonicalGroups params) oStmt multiplicity xChallenge k u := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact helpers_eq_helperValue_of_DIT_zero (canonicalGroups params) oStmt multiplicity
      helpers xChallenge k u (fun i _ => hden i u) (hcons k u)
  rw [hpin]
  have hpart := canonicalGroups_sum_partition (params := params)
    (f := fun i => termNumerator multiplicity i u / termPhi oStmt xChallenge i u)
  rw [← hpart]
  exact Finset.sum_congr rfl (fun _ _ => rfl)

/-- **Orientation of one row's term total.** The ungrouped term sum at row `u` is the table
fraction `m(u) / (x + t(u))` minus the column-pole sum. -/
theorem termSum_orient (oStmt : ∀ i, OStmtIn F n M i)
    (multiplicity : MultilinearOracle F n) (xChallenge : F) (u : Hypercube n) :
    (∑ i : TermIdx M, termNumerator multiplicity i u / termPhi oStmt xChallenge i u)
      = evalOnHypercube multiplicity u *
          (xChallenge + evalOnHypercube (tableOracle oStmt) u)⁻¹
        - ∑ i : Fin M, (xChallenge + evalOnHypercube (columnOracle oStmt i) u)⁻¹ := by
  change (∑ i : Fin (M + 1),
      termNumerator multiplicity i u / termPhi oStmt xChallenge i u) = _
  rw [Fin.sum_univ_succ]
  have h0 : termNumerator multiplicity (0 : TermIdx M) u /
        termPhi oStmt xChallenge (0 : TermIdx M) u
      = evalOnHypercube multiplicity u *
          (xChallenge + evalOnHypercube (tableOracle oStmt) u)⁻¹ := by
    rw [termNumerator_zero, termPhi_zero, div_eq_mul_inv]
  have hcols : ∀ i : Fin M,
      termNumerator multiplicity i.succ u / termPhi oStmt xChallenge i.succ u
        = -(xChallenge + evalOnHypercube (columnOracle oStmt i) u)⁻¹ := by
    intro i
    have hnum : termNumerator multiplicity i.succ u = -1 :=
      termNumerator_succ multiplicity i u
    have hphi : termPhi oStmt xChallenge i.succ u
        = xChallenge + evalOnHypercube (columnOracle oStmt i) u :=
      termPhi_succ oStmt xChallenge i u
    rw [hnum, hphi, neg_div, one_div]
  have hsum : (∑ i : Fin M,
        termNumerator multiplicity i.succ u / termPhi oStmt xChallenge i.succ u)
      = ∑ i : Fin M, -(xChallenge + evalOnHypercube (columnOracle oStmt i) u)⁻¹ :=
    Finset.sum_congr rfl (fun i _ => hcols i)
  rw [h0, hsum, Finset.sum_neg_distrib, ← sub_eq_add_neg]

/-- **The consistent claim as a `perMNumerator` value.** Under full consistency at a challenge
avoiding every pole value in `A`, the helper claim equals the negative of the adversarial
multiplicity numerator over the common denominator. -/
theorem consistentClaim_eq_neg_perMNumerator_div (params : ProtocolParams M)
    [DecidableEq F]
    (oStmt : ∀ i, OStmtIn F n M i)
    (multiplicity : MultilinearOracle F n) (helpers : HelperMessages F n params.numGroups)
    (xChallenge : F) (A : Finset F)
    (hx : ∀ a ∈ A, xChallenge + a ≠ 0)
    (hcv : ∀ p : Fin M × Hypercube n, evalOnHypercube (columnOracle oStmt p.1) p.2 ∈ A)
    (htv : ∀ u : Hypercube n, evalOnHypercube (tableOracle oStmt) u ∈ A)
    (hcons : ∀ (k : Fin params.numGroups) (u : Hypercube n),
      domainIdentityTerm (canonicalGroups params) oStmt multiplicity helpers xChallenge k u = 0) :
    (∑ u : Hypercube n, ∑ k : Fin params.numGroups, evalOnHypercube (helpers k) u)
      = -((perMNumerator A
            (fun p : Fin M × Hypercube n => evalOnHypercube (columnOracle oStmt p.1) p.2)
            (fun u : Hypercube n => evalOnHypercube (tableOracle oStmt) u)
            (fun u : Hypercube n => evalOnHypercube multiplicity u)).eval xChallenge
          / ∏ a ∈ A, (xChallenge + a)) := by
  have hden : ∀ (i : TermIdx M) (u : Hypercube n), termPhi oStmt xChallenge i u ≠ 0 := by
    intro i u
    refine Fin.cases ?_ ?_ i
    · rw [termPhi_zero]
      exact hx _ (htv u)
    · intro j
      have hphi : termPhi oStmt xChallenge j.succ u
          = xChallenge + evalOnHypercube (columnOracle oStmt j) u :=
        termPhi_succ oStmt xChallenge j u
      rw [hphi]
      exact hx _ (hcv (j, u))
  rw [consistentClaim_eq_termSum params oStmt multiplicity helpers xChallenge hden hcons]
  have horient : (∑ u : Hypercube n, ∑ i : TermIdx M,
        termNumerator multiplicity i u / termPhi oStmt xChallenge i u)
      = (∑ u : Hypercube n, evalOnHypercube multiplicity u *
            (xChallenge + evalOnHypercube (tableOracle oStmt) u)⁻¹)
        - ∑ u : Hypercube n, ∑ i : Fin M,
            (xChallenge + evalOnHypercube (columnOracle oStmt i) u)⁻¹ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun u _ => termSum_orient oStmt multiplicity xChallenge u)
  rw [horient]
  have hcol : (∑ u : Hypercube n, ∑ i : Fin M,
        (xChallenge + evalOnHypercube (columnOracle oStmt i) u)⁻¹)
      = ∑ p : Fin M × Hypercube n,
          (xChallenge + evalOnHypercube (columnOracle oStmt p.1) p.2)⁻¹ := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_comm
  have hfrac := fracSum_eq_perMNumerator_div
    (ColIdx := Fin M × Hypercube n) (Row := Hypercube n) A
    (fun p : Fin M × Hypercube n => evalOnHypercube (columnOracle oStmt p.1) p.2)
    (fun u : Hypercube n => evalOnHypercube (tableOracle oStmt) u)
    (fun u : Hypercube n => evalOnHypercube multiplicity u)
    xChallenge hx hcv htv
  rw [hcol, ← hfrac, neg_sub]

end Logup

#print axioms Logup.qsum_affine_in_batch
#print axioms Logup.qsum_vanishing_forall
#print axioms Logup.helpers_eq_helperValue_of_DIT_zero
#print axioms Logup.helper_mass_eq_grand_sum_of_DIT_zero
#print axioms Logup.consistentClaim_eq_termSum
#print axioms Logup.termSum_orient
#print axioms Logup.consistentClaim_eq_neg_perMNumerator_div

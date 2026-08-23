/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das (Least Authority), Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.Data.Probability.Notation
import ArkLib.ToMathlib.CountingAgreementBricks

/-!
# Out-of-domain sampling (WHIR Lemma 4.24)

This file formalizes the out-of-domain sampling equivalence underlying WHIR.

* `OutOfDomSmpl.crs_equiv_rs_random_point_agreement` (Lemma 4.24) — for a word `f`, the existence
  of two distinct codewords `δ`-close to `f` whose decoded multilinear polynomials agree at the
  out-of-domain sample points `r₁, …, rₛ` is equivalent to the multi-constrained Reed-Solomon
  list (with weights `wᵢ = Z · eqPolynomial rᵢ`) having more than one codeword.
-/

namespace OutOfDomSmpl

open ListDecodable MvPolynomial NNReal ProbabilityTheory ReedSolomon

variable {F : Type} [Field F] [DecidableEq F]
         {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Lemma 4.24
  Let `f : ι → F`, `m` be the number of variables, `s` be a repetition parameter
  and `δ ∈ [0,1]` be a distance parameter, then for every `r₁,...,rₛ ∈ Fᵐ`
  the following statements are equivalent:
    - ∃ distinct u, u' ∈ Λ(C,f,δ) such that ∀ i < s, uPoly(rᵢ) = uPoly'(rᵢ)
      where, Λ(C,f,δ) denotes the list of codewords of C δ-close to f
             uPoly, uPoly' denotes the decoded multivariate polynomials of u and u'
    - ∃ σ₁,..,σₛ : F, such that |Λ(C',f,δ)| > 1
      where, C' is a multiconstrained RS = MCRS[F, ι, φ, m, s, w, σ]
             σ = {σ₁,..,σₛ}, w = {w₁,..,wₛ}, wᵢ = Z * eqPolynomial(rᵢ)

  Note on the weight encoding: `toWeightAssignment` (underlying `weightConstraint`) assigns
  the codeword value `p(b)` to variable index `0` and the point `b` to indices `1..m`, matching
  the paper's `ŵ(Z, X₁, …, X_m)`. The weights here are accordingly
  `X 0 * rename Fin.succ (eqPolynomial (r i))` (the original statement read the value variable
  at `Fin.last m` while the assignment provides it at `0`). -/
lemma crs_equiv_rs_random_point_agreement
    {f : ι → F} {m s : ℕ} {φ : ι ↪ F} [Smooth φ] :
  ∀ (r : Fin s → Fin m → F) (δ : ℝ≥0) (_hδLe : δ ≤ 1),
    (∃ u u' : smoothCode φ m,
      u.val ≠ u'.val ∧
      u.val ∈ closeCodewordsRel (smoothCode φ m) f δ ∧
      u'.val ∈ closeCodewordsRel (smoothCode φ m) f δ ∧
      ∀ i : Fin s, (mVdecode u).eval (r i) = (mVdecode u').eval (r i))
    ↔
    (∃ σ : Fin s → F,
      let w : Fin s → MvPolynomial (Fin (m + 1)) F :=
        fun i => MvPolynomial.X 0 * rename Fin.succ (eqPolynomial (r i))
      let multiCRSCode := multiConstrainedCode φ m s w σ
      ∃ u u' : ι → F, u ≠ u' ∧
        u ∈ closeCodewordsRel multiCRSCode f δ ∧
        u' ∈ closeCodewordsRel multiCRSCode f δ)
  := by
  intro r δ _hδLe
  constructor
  · rintro ⟨u, u', huu, hu, hu', hagree⟩
    refine ⟨fun i => MvPolynomial.eval (r i) (mVdecode u), u.val, u'.val, huu, ?_, ?_⟩
    · refine ⟨⟨u.2, fun i => ?_⟩, hu.2⟩
      rw [weightConstraint_eqPolynomial_iff _ (mVdecode_mem_restrictDegree _)]
    · refine ⟨⟨u'.2, fun i => ?_⟩, hu'.2⟩
      rw [weightConstraint_eqPolynomial_iff _ (mVdecode_mem_restrictDegree _)]
      exact (hagree i).symm
  · rintro ⟨σv, u, u', huu, hu, hu'⟩
    obtain ⟨⟨hmu, hcu⟩, hbu⟩ := hu
    obtain ⟨⟨hmu', hcu'⟩, hbu'⟩ := hu'
    refine ⟨⟨u, hmu⟩, ⟨u', hmu'⟩, huu, ⟨hmu, hbu⟩, ⟨hmu', hbu'⟩, fun i => ?_⟩
    have h1 := (weightConstraint_eqPolynomial_iff _
      (mVdecode_mem_restrictDegree _) (r i) (σv i)).mp (hcu i)
    have h2 := (weightConstraint_eqPolynomial_iff _
      (mVdecode_mem_restrictDegree _) (r i) (σv i)).mp (hcu' i)
    rw [h1, h2]

/-- Lemma 4.25 part 1
  Let `f : ι → F`, `m` be the number of variables, `s` be a repetition parameter
  and `δ ∈ [0,1]` be a distance parameter,
  if `C = RS [F, ι, m]` is `(δ,l)`-list decodable then
  `Pr_{r ← F} [ ∃ σ₁,..,σₛ : F, |Λ(C',f,δ)| > 1 ] =`
  `Pr_{r ← F} [ ∃ distinct u, u' ∈ RS[F, ι, φ, m] s.t. uPoly(pow(r)) = uPoly'(pow(r))]`
    where, pow(x,m) = {x^2⁰,x^2¹,....,x^2^{m-1}}
           C' = CRS [F, ι, φ, m, s, w, σ]
           σ = {σ₁,..,σₛ}, w = {w₁,..,wₛ}, wᵢ = Z * eqPolynomial(pow(r,m)) -/
lemma oodSampling_crs_eq_rs
    [Fintype F] {f : ι → F} {m s : ℕ} {φ : ι ↪ F} [Smooth φ]
    (l δ : ℝ≥0) (hδLe : δ ≤ 1)
    {C : Set (ι → F)} (hcode : C = smoothCode φ m ∧ listDecodable C δ l) :
    Pr_{ let rs ←$ᵖ (Fin s → F) }[ (∃ σ : Fin s → F,
                        let w : Fin s → MvPolynomial (Fin (m + 1)) F :=
                          fun i =>
                            let ri := rs i
                            let rVec := fun j : Fin m => ri ^ (2^(j : ℕ))
                            MvPolynomial.X 0 * rename Fin.succ (eqPolynomial rVec)
                        let multiCRSCode := multiConstrainedCode φ m s w σ
                        ∃ u u' : ι → F, u ≠ u' ∧
                          u ∈ closeCodewordsRel multiCRSCode f δ ∧
                          u' ∈ closeCodewordsRel multiCRSCode f δ)]
    =
    Pr_{ let rs ←$ᵖ (Fin s → F) }[ (∃ u u' : smoothCode φ m,
                        u.val ≠ u'.val ∧
                        u.val ∈ closeCodewordsRel C f δ ∧
                        u'.val ∈ closeCodewordsRel C f δ ∧
                        ∀ i : Fin s,
                          let ri := rs i
                          let rVec := fun j : Fin m => ri ^ (2^(j : ℕ))
                          (mVdecode u).eval (rVec) = (mVdecode u').eval (rVec))]
  := by
  have h1 := hcode.1
  subst h1
  have hequiv : ∀ rs : Fin s → F,
    (∃ σ : Fin s → F,
      let w : Fin s → MvPolynomial (Fin (m + 1)) F :=
        fun i =>
          let ri := rs i
          let rVec := fun j : Fin m => ri ^ (2^(j : ℕ))
          MvPolynomial.X 0 * rename Fin.succ (eqPolynomial rVec)
      let multiCRSCode := multiConstrainedCode φ m s w σ
      ∃ u u' : ι → F, u ≠ u' ∧
        u ∈ closeCodewordsRel multiCRSCode f ↑δ ∧
        u' ∈ closeCodewordsRel multiCRSCode f ↑δ)
    ↔
    (∃ u u' : smoothCode φ m,
      u.val ≠ u'.val ∧
      u.val ∈ closeCodewordsRel (↑(smoothCode φ m)) f ↑δ ∧
      u'.val ∈ closeCodewordsRel (↑(smoothCode φ m)) f ↑δ ∧
      ∀ i : Fin s,
        let ri := rs i
        let rVec := fun j : Fin m => ri ^ (2^(j : ℕ))
        (mVdecode u).eval rVec = (mVdecode u').eval rVec) :=
    fun rs => (crs_equiv_rs_random_point_agreement
      (fun i j => (rs i) ^ (2 ^ (j : ℕ))) δ hδLe).symm
  have hfun : (fun rs => PMF.pure (∃ σ : Fin s → F,
      let w := fun i =>
        let ri := rs i
        let rVec := fun j : Fin m => ri ^ (2^(j : ℕ))
        MvPolynomial.X 0 * rename Fin.succ (eqPolynomial rVec)
      let multiCRSCode := multiConstrainedCode φ m s w σ
      ∃ u u' : ι → F, u ≠ u' ∧
        u ∈ closeCodewordsRel multiCRSCode f ↑δ ∧
        u' ∈ closeCodewordsRel multiCRSCode f ↑δ) : (Fin s → F) → PMF Prop) =
    fun rs => PMF.pure (∃ u u' : smoothCode φ m,
      u.val ≠ u'.val ∧
      u.val ∈ closeCodewordsRel (↑(smoothCode φ m)) f ↑δ ∧
      u'.val ∈ closeCodewordsRel (↑(smoothCode φ m)) f ↑δ ∧
      ∀ i : Fin s,
        let ri := rs i
        let rVec := fun j : Fin m => ri ^ (2^(j : ℕ))
        (mVdecode u).eval rVec = (mVdecode u').eval rVec) :=
    funext fun rs => congr_arg PMF.pure (propext (hequiv rs))
  exact congr_arg (· True) (congr_arg (PMF.bind ($ᵖ (Fin s → F))) hfun)

section CountingBridge

open LinearMvExtension Polynomial

/-- The mass that the `Pr_{...}[...]` PMF encoding assigns to an event under uniform sampling
is exactly `#event / #domain`. -/
private lemma uniform_event_mass {α : Type} [Fintype α] [Nonempty α]
    (P : α → Prop) [DecidablePred P] :
    PMF.bind (PMF.uniformOfFintype α) (fun r => PMF.pure (P r)) True
      = ((Finset.univ.filter P).card : ENNReal) * ((Fintype.card α : ENNReal))⁻¹ := by
  classical
  rw [PMF.bind_apply, tsum_fintype]
  trans (∑ a ∈ Finset.univ.filter P, ((Fintype.card α : ENNReal))⁻¹)
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : P a <;>
      simp [PMF.uniformOfFintype_apply, PMF.pure_apply, h, eq_iff_iff]
  · rw [Finset.sum_const, nsmul_eq_mul]

/-- Distinct smooth codewords decode to distinct univariate polynomials (the decoded
polynomial interpolates the codeword on the domain). -/
private lemma decodeLT_ne_of_val_ne {φ : ι ↪ F} [Smooth φ] {m : ℕ} (u u' : smoothCode φ m)
    (hne : u.val ≠ u'.val) :
    ((decodeLT u : Polynomial F)) ≠ ((decodeLT u' : Polynomial F)) := by
  intro h
  apply hne
  funext x
  have hu : ((decodeLT u : Polynomial F)).eval (φ x) = u.val x :=
    Lagrange.eval_interpolate_at_node u.val (φ.injective.injOn) (Finset.mem_univ x)
  have hu' : ((decodeLT u' : Polynomial F)).eval (φ x) = u'.val x :=
    Lagrange.eval_interpolate_at_node u'.val (φ.injective.injOn) (Finset.mem_univ x)
  rw [← hu, ← hu', h]

/-- Evaluating the decoded multilinear polynomial at the power vector `(r^(2^j))_j` recovers
the decoded univariate polynomial's value at `r` (the smooth-code power substitution
round-trip). -/
private lemma mVdecode_eval_pow {φ : ι ↪ F} [Smooth φ] {m : ℕ} (u : smoothCode φ m) (r : F) :
    (mVdecode u).eval (fun j : Fin m => r ^ (2 ^ (j : ℕ)))
      = ((decodeLT u : Polynomial F)).eval r := by
  have h1 : Polynomial.eval r (powAlgHom (mVdecode u))
      = MvPolynomial.eval (fun j : Fin m => r ^ (2 ^ (j : ℕ))) (mVdecode u) := by
    unfold powAlgHom
    rw [MvPolynomial.aeval_def, ← Polynomial.coe_evalRingHom,
      MvPolynomial.eval₂_comp_left (Polynomial.evalRingHom r)]
    have hhom : (Polynomial.evalRingHom r).comp (algebraMap F (Polynomial F))
        = RingHom.id F := RingHom.ext fun a => by simp
    have hg : (⇑(Polynomial.evalRingHom r)
          ∘ fun j : Fin m => (Polynomial.X : Polynomial F) ^ 2 ^ (j : ℕ))
        = fun j : Fin m => r ^ 2 ^ (j : ℕ) := by
      funext j
      simp
    rw [hhom, hg, MvPolynomial.eval₂_id]
  have h2 : powAlgHom (mVdecode u) = ((decodeLT u : Polynomial F)) := by
    have := powContraction_is_right_inverse_to_linearMvExtension (decodeLT u)
    simpa [powContraction, mVdecode] using this
  rw [← h1, h2]

end CountingBridge

/-- Lemma 4.25 part 2
  Let `f : ι → F`, `m` be the number of variables, `s` be a repetition parameter
  and `δ ∈ [0,1]` be a distance parameter,
  if `C = RS [F, ι, m]` is `(δ,l)`-list decodable then
  the above equation is bounded as `≤ l²/2 * (2ᵐ/|F|)ˢ` -/
lemma oodSampling_rs_le_bound
    [Fintype F] {f : ι → F} {m s : ℕ} {φ : ι ↪ F} [Smooth φ]
    (δ l : ℝ≥0) (_hδLe : δ ≤ 1)
    (C : Set (ι → F)) (hcode : C = smoothCode φ m ∧ listDecodable C δ l) :
    Pr_{ let rs ←$ᵖ (Fin s → F) }[ ∃ u u' : smoothCode φ m,
                        u.val ≠ u'.val ∧
                        u.val ∈ closeCodewordsRel C f δ ∧
                        u'.val ∈ closeCodewordsRel C f δ ∧
                        ∀ i : Fin s,
                          let ri := rs i
                          let rVec := fun j : Fin m => ri ^ (2^(j : ℕ))
                          (mVdecode u).eval (rVec) = (mVdecode u').eval (rVec)
                      ] ≤ ENNReal.ofReal (((l : ℝ)^2 / 2) * (((2^m : ℝ) / Fintype.card F)^s))
:= by
  classical
  obtain ⟨hc, h_decodable⟩ := hcode
  subst hc
  -- The close-codeword list is finite with at most `l` elements.
  have hSfin : (closeCodewordsRel (↑(smoothCode φ m) : Set (ι → F)) f (↑δ : ℝ)).Finite :=
    Set.toFinite _
  set Sf : Finset (ι → F) := hSfin.toFinset with hSf
  set M : ℕ := Sf.card with hM
  have hml : (M : ENNReal) ≤ (l : ENNReal) := by
    have h0 := h_decodable f
    rw [Set.ncard_eq_toFinset_card _ hSfin, ← hSf, ← hM] at h0
    have h1 : (M : ℝ≥0) ≤ l := by exact_mod_cast h0
    exact_mod_cast h1
  -- Ordered pairs of distinct close codewords (halving via a pulled-back linear order).
  set e : (ι → F) ≃ Fin (Fintype.card (ι → F)) := Fintype.equivFin (ι → F) with he
  set P : Finset ((ι → F) × (ι → F)) := Sf.offDiag.filter (fun p => e p.1 < e p.2) with hP
  set T : (ι → F) × (ι → F) → Finset (Fin s → F) := fun p =>
    Finset.univ.filter (fun rs => ∀ i : Fin s,
      (Lagrange.interpolate Finset.univ ⇑φ p.1).eval (rs i)
        = (Lagrange.interpolate Finset.univ ⇑φ p.2).eval (rs i)) with hT
  have hpair : ∀ p ∈ P, (T p).card ≤ (2 ^ m - 1) ^ s := by
    intro p hp
    simp only [hP, Finset.mem_filter, Finset.mem_offDiag] at hp
    obtain ⟨⟨h1, h2, hpne⟩, -⟩ := hp
    rw [hSf, Set.Finite.mem_toFinset] at h1 h2
    simp only [hT]
    have hne :
        ((decodeLT (⟨p.1, h1.1⟩ : smoothCode φ m) : Polynomial F)) ≠
          ((decodeLT (⟨p.2, h2.1⟩ : smoothCode φ m) : Polynomial F)) :=
      decodeLT_ne_of_val_ne _ _ hpne
    have hdeg_left :
        ((decodeLT (⟨p.1, h1.1⟩ : smoothCode φ m) : Polynomial F)).natDegree < 2 ^ m := by
      have hmem := (decodeLT (⟨p.1, h1.1⟩ : smoothCode φ m)).2
      rw [Polynomial.mem_degreeLT] at hmem
      by_cases hzero :
          ((decodeLT (⟨p.1, h1.1⟩ : smoothCode φ m) : Polynomial F)) = 0
      · rw [hzero, Polynomial.natDegree_zero]
        positivity
      · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr hmem
    have hdeg_right :
        ((decodeLT (⟨p.2, h2.1⟩ : smoothCode φ m) : Polynomial F)).natDegree < 2 ^ m := by
      have hmem := (decodeLT (⟨p.2, h2.1⟩ : smoothCode φ m)).2
      rw [Polynomial.mem_degreeLT] at hmem
      by_cases hzero :
          ((decodeLT (⟨p.2, h2.1⟩ : smoothCode φ m) : Polynomial F)) = 0
      · rw [hzero, Polynomial.natDegree_zero]
        positivity
      · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr hmem
    simpa using Polynomial.card_filter_forall_eval_eq_le_of_natDegree_lt
      (F := F) (N := 2 ^ m) (s := s)
      (p := (decodeLT (⟨p.1, h1.1⟩ : smoothCode φ m) : Polynomial F))
      (q := (decodeLT (⟨p.2, h2.1⟩ : smoothCode φ m) : Polynomial F))
      hne hdeg_left hdeg_right
  have hPm : P.card ≤ M * (M - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have hswap : P.card = (Sf.offDiag.filter (fun p => e p.2 < e p.1)).card := by
      rw [hP]
      refine Finset.card_bij' (fun p _ => p.swap) (fun p _ => p.swap) ?_ ?_ ?_ ?_
      · intro a ha
        rw [Finset.mem_filter, Finset.mem_offDiag] at ha ⊢
        obtain ⟨⟨ha1, ha2, hane⟩, halt⟩ := ha
        exact ⟨⟨ha2, ha1, fun h => hane h.symm⟩, halt⟩
      · intro a ha
        rw [Finset.mem_filter, Finset.mem_offDiag] at ha ⊢
        obtain ⟨⟨ha1, ha2, hane⟩, halt⟩ := ha
        exact ⟨⟨ha2, ha1, fun h => hane h.symm⟩, halt⟩
      · intro a _; exact Prod.swap_swap a
      · intro a _; exact Prod.swap_swap a
    have hneg : Sf.offDiag.filter (fun p => ¬ e p.1 < e p.2)
        = Sf.offDiag.filter (fun p => e p.2 < e p.1) := by
      refine Finset.filter_congr ?_
      intro p hp
      rw [Finset.mem_offDiag] at hp
      have hne1 : e p.1 ≠ e p.2 := fun h => hp.2.2 (e.injective h)
      simp only [not_lt]
      exact ⟨fun h => lt_of_le_of_ne h hne1.symm, le_of_lt⟩
    have hsplit := Finset.card_filter_add_card_filter_not (s := Sf.offDiag)
      (fun p => e p.1 < e p.2)
    rw [hneg, ← hP, ← hswap] at hsplit
    have hoff : Sf.offDiag.card = M * (M - 1) := by
      rw [Finset.offDiag_card, ← hM, ← Nat.pred_eq_sub_one, Nat.mul_pred]
    omega
  -- The collision event is covered by the union of per-pair agreement events.
  have hcount : (Finset.univ.filter (fun rs : Fin s → F =>
      ∃ u u' : smoothCode φ m, u.val ≠ u'.val ∧
        u.val ∈ closeCodewordsRel (↑(smoothCode φ m) : Set (ι → F)) f (↑δ : ℝ) ∧
        u'.val ∈ closeCodewordsRel (↑(smoothCode φ m) : Set (ι → F)) f (↑δ : ℝ) ∧
        ∀ i : Fin s,
          let ri := rs i
          let rVec := fun j : Fin m => ri ^ (2^(j : ℕ))
          (mVdecode u).eval (rVec) = (mVdecode u').eval (rVec))).card
      ≤ M * (M - 1) / 2 * ((2 ^ m - 1) ^ s) := by
    refine le_trans (Finset.card_le_card (t := P.biUnion T) ?_)
      (le_trans Finset.card_biUnion_le ?_)
    · intro rs hrs
      rw [Finset.mem_filter] at hrs
      obtain ⟨-, u, u', huu, hu, hu', hagree⟩ := hrs
      have hvalne : e u.val ≠ e u'.val := fun h => huu (e.injective h)
      have hagree' : ∀ i : Fin s,
          ((decodeLT u : Polynomial F)).eval (rs i)
            = ((decodeLT u' : Polynomial F)).eval (rs i) := by
        intro i
        have h := hagree i
        simp only at h
        rwa [mVdecode_eval_pow u (rs i), mVdecode_eval_pow u' (rs i)] at h
      rcases lt_or_gt_of_ne hvalne with hlt | hgt
      · refine Finset.mem_biUnion.mpr ⟨(u.val, u'.val), ?_, ?_⟩
        · rw [hP, Finset.mem_filter, Finset.mem_offDiag]
          refine ⟨⟨?_, ?_, huu⟩, hlt⟩ <;> rw [hSf, Set.Finite.mem_toFinset] <;> assumption
        · simp only [hT]
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ rs, fun i => hagree' i⟩
      · refine Finset.mem_biUnion.mpr ⟨(u'.val, u.val), ?_, ?_⟩
        · rw [hP, Finset.mem_filter, Finset.mem_offDiag]
          refine ⟨⟨?_, ?_, fun h => huu h.symm⟩, hgt⟩ <;>
            rw [hSf, Set.Finite.mem_toFinset] <;> assumption
        · simp only [hT]
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ rs, fun i => (hagree' i).symm⟩
    · refine le_trans (Finset.sum_le_card_nsmul P _ _ hpair) ?_
      rw [smul_eq_mul]
      exact Nat.mul_le_mul_right _ hPm
  -- Sample-space size and ENNReal assembly.
  haveI : Nonempty F := ⟨0⟩
  have hcardX : Fintype.card (Fin s → F) = (Fintype.card F) ^ s := by
    rw [Fintype.card_fun, Fintype.card_fin]
  have hFpos : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  -- Rewrite the RHS into ENNReal division form.
  have hRHS : ENNReal.ofReal (((l : ℝ)^2 / 2) * (((2^m : ℝ) / Fintype.card F)^s))
      = ((l : ENNReal)^2 / 2) * (((2^m : ENNReal) / (Fintype.card F : ENNReal))^s) := by
    rw [ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_div_of_pos (by norm_num),
      ENNReal.ofReal_pow (by exact_mod_cast (l : ℝ≥0).coe_nonneg),
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_ofNat,
      ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_div_of_pos hFpos,
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_natCast]
  rw [hRHS]
  refine le_trans (le_of_eq (uniform_event_mass _)) ?_
  refine le_trans (mul_le_mul_left (Nat.cast_le.mpr hcount) _) ?_
  rw [hcardX, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, ENNReal.inv_pow, mul_assoc,
    ← mul_pow, ← div_eq_mul_inv]
  refine mul_le_mul' ?_ ?_
  · rw [ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
    calc (↑(M * (M - 1) / 2) : ENNReal) * 2
        = ↑(M * (M - 1) / 2 * 2) := by rw [Nat.cast_mul, Nat.cast_ofNat]
      _ ≤ (↑(M * (M - 1)) : ENNReal) := Nat.cast_le.mpr (Nat.div_mul_le_self _ 2)
      _ ≤ (M : ENNReal) * (M : ENNReal) := by
          rw [Nat.cast_mul]
          exact mul_le_mul' le_rfl (Nat.cast_le.mpr (Nat.sub_le _ _))
      _ ≤ (l : ENNReal) * (l : ENNReal) := mul_le_mul' hml hml
      _ = (l : ENNReal) ^ 2 := (pow_two _).symm
  · refine ENNReal.pow_le_pow_left (ENNReal.div_le_div_right ?_ _)
    calc ((2 ^ m - 1 : ℕ) : ENNReal)
        ≤ ((2 ^ m : ℕ) : ENNReal) := Nat.cast_le.mpr (Nat.sub_le _ _)
      _ = (2 : ENNReal) ^ m := by rw [Nat.cast_pow, Nat.cast_ofNat]

end OutOfDomSmpl

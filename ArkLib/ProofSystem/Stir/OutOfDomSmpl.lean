/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das (Least Authority)
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.Probability.Instances
import ArkLib.Data.Probability.Notation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Vector

/-! Section 4.3 [ACFY24stir]

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *STIR: Reed-Solomon proximity testing with
    fewer queries*][ACFY24stir]
-/

set_option maxHeartbeats 2000000

open Finset ListDecodable NNReal Polynomial ProbabilityTheory ReedSolomon
namespace OutOfDomSmpl

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Returns the domain complement `F \ φ(ι)` of an injective map `φ : ι ↪ F` -/
def domainComplement (φ : ι ↪ F) : Finset F :=
  Finset.univ \ Finset.image φ.toFun Finset.univ

/-- Pr_{r₀, …, r_{s-1} ← (𝔽 \ φ(ι)) }
      [ ∃ distinct u, u′ ∈ List(C, f, δ) :
        ∀ i < s, u(r_i) = u′(r_i) ]
    here, List (C, f, δ) denotes the list of codewords of C δ-close to f,
    wrt the Relative Hamming distance. -/
noncomputable def listDecodingCollisionProbability
  (φ : ι ↪ F) (f : ι → F) (δ : ℝ) (s degree : ℕ)
  (h_nonempty : Nonempty (domainComplement φ)) : ENNReal :=
  Pr_{let r ←$ᵖ (Fin s → domainComplement φ)}[
    ∃ (u u' : code φ degree),
      u.val ≠ u'.val ∧
      u.val ∈ closeCodewordsRel (code φ degree) f δ ∧
      u'.val ∈ closeCodewordsRel (code φ degree) f δ ∧
      ∀ i : Fin s,
        let uPoly := decodeLT u
        let uPoly' := decodeLT u'
        (uPoly : F[X]).eval (r i).1 = (uPoly' : F[X]).eval (r i).1
  ]

/-- The mass that the `Pr_{...}[...]` PMF encoding assigns to an event under uniform sampling
is exactly `#event / #domain` — the counting bridge used to estimate collision probabilities. -/
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

/-- Counting a coordinatewise event: the tuples satisfying `Q` in every coordinate form the
`piFinset` of the per-coordinate solution set, so their count is `(#Q)^s`. Together with
`uniform_event_mass` this replaces any independence machinery by pure counting. -/
private lemma card_filter_forall_pi {β : Type} [Fintype β] [DecidableEq β] {s : ℕ}
    (Q : β → Prop) [DecidablePred Q] :
    (Finset.univ.filter (fun r : Fin s → β => ∀ i, Q (r i))).card
      = ((Finset.univ.filter Q).card) ^ s := by
  classical
  have h : (Finset.univ.filter (fun r : Fin s → β => ∀ i, Q (r i)))
      = Fintype.piFinset (fun _ : Fin s => Finset.univ.filter Q) := by
    ext r
    simp [Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset]
  simp

omit [Fintype F] [DecidableEq F] in
/-- Distinct codewords decode to distinct polynomials: the decoded polynomial interpolates the
codeword on the domain (`Lagrange.eval_interpolate_at_node`), so equal polynomials force equal
codewords. -/
private lemma decodeLT_ne_of_val_ne {φ : ι ↪ F} {degree : ℕ} (u u' : code φ degree)
    (hne : u.val ≠ u'.val) :
    ((decodeLT u : F[X])) ≠ ((decodeLT u' : F[X])) := by
  intro h
  apply hne
  funext x
  have hu : ((decodeLT u : F[X])).eval (φ x) = u.val x :=
    Lagrange.eval_interpolate_at_node u.val (φ.injective.injOn) (Finset.mem_univ x)
  have hu' : ((decodeLT u' : F[X])).eval (φ x) = u'.val x :=
    Lagrange.eval_interpolate_at_node u'.val (φ.injective.injOn) (Finset.mem_univ x)
  rw [← hu, ← hu', h]

/-- The agreement set of two distinct codewords' polynomials (inside any subtype of `F`) has at
most `degree − 1` elements: agreement points are roots of the nonzero difference, whose degree is
below `degree`. -/
private lemma card_agreement_le {φ : ι ↪ F} {degree : ℕ} (u u' : code φ degree)
    (hne : u.val ≠ u'.val) :
    (Finset.univ.filter (fun x : ↥(domainComplement φ) =>
      ((decodeLT u : F[X])).eval x.1 = ((decodeLT u' : F[X])).eval x.1)).card
      ≤ degree - 1 := by
  classical
  set q : F[X] := (decodeLT u : F[X]) - (decodeLT u' : F[X]) with hq
  have hq0 : q ≠ 0 := sub_ne_zero_of_ne (decodeLT_ne_of_val_ne u u' hne)
  have hqdeg : q.natDegree < degree := by
    have hp := (decodeLT u).2
    have hp' := (decodeLT u').2
    rw [Polynomial.mem_degreeLT] at hp hp'
    have hlt : q.degree < (degree : WithBot ℕ) :=
      lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hp hp')
    exact (Polynomial.natDegree_lt_iff_degree_lt hq0).mpr hlt
  have hsub : (Finset.univ.filter (fun x : ↥(domainComplement φ) =>
        ((decodeLT u : F[X])).eval x.1 = ((decodeLT u' : F[X])).eval x.1)).image Subtype.val
      ⊆ q.roots.toFinset := by
    intro y hy
    simp only [Finset.mem_image, Finset.mem_filter] at hy
    obtain ⟨x, ⟨_, hx⟩, rfl⟩ := hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hq0]
    simp [hq, Polynomial.IsRoot, hx]
  calc (Finset.univ.filter _).card
      = ((Finset.univ.filter (fun x : ↥(domainComplement φ) =>
          ((decodeLT u : F[X])).eval x.1 = ((decodeLT u' : F[X])).eval x.1)).image
            Subtype.val).card := (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ q.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card q.roots := q.roots.toFinset_card_le
    _ ≤ q.natDegree := Polynomial.card_roots' q
    _ ≤ degree - 1 := by omega

/-- Lemma 4.5.1 -/
lemma out_of_dom_smpl_1
    {δ l : ℝ≥0} {s : ℕ} {f : ι → F} {degree : ℕ} {φ : ι ↪ F}
  (C : Set (ι → F)) (hC : C = code φ degree)
  (h_decodable : listDecodable C δ l)
  (h_nonempty : Nonempty (domainComplement φ)) :
  listDecodingCollisionProbability φ f δ s degree h_nonempty ≤
    ((l * (l-1) / 2)) * ((degree - 1) / (Fintype.card F - Fintype.card ι))^s
  := by
  classical
  subst hC
  haveI hne0 : Nonempty (domainComplement φ) := h_nonempty
  -- Setup: the close-codeword finset, an order on pairs, and per-pair agreement events.
  have hSfin : (closeCodewordsRel (↑(code φ degree) : Set (ι → F)) f (↑δ : ℝ)).Finite :=
    Set.toFinite _
  set Sf : Finset (ι → F) := hSfin.toFinset with hSf
  set m : ℕ := Sf.card with hm
  set e : (ι → F) ≃ Fin (Fintype.card (ι → F)) := Fintype.equivFin (ι → F) with he
  set P : Finset ((ι → F) × (ι → F)) := Sf.offDiag.filter (fun p => e p.1 < e p.2) with hP
  set T : (ι → F) × (ι → F) → Finset (Fin s → ↥(domainComplement φ)) := fun p =>
    Finset.univ.filter (fun r => ∀ i : Fin s,
      (Lagrange.interpolate Finset.univ ⇑φ p.1).eval (r i).1
        = (Lagrange.interpolate Finset.univ ⇑φ p.2).eval (r i).1) with hT
  -- List-decodability: at most `l` close codewords.
  have hml : (m : ENNReal) ≤ (l : ENNReal) := by
    have h0 := h_decodable f
    rw [Set.ncard_eq_toFinset_card _ hSfin, ← hSf, ← hm] at h0
    have h1 : (m : ℝ≥0) ≤ l := by exact_mod_cast h0
    exact_mod_cast h1
  -- Each ordered pair of distinct close codewords agrees on at most `degree - 1`
  -- out-of-domain points, so the s-fold agreement event has at most `(degree-1)^s` samples.
  have hpair : ∀ p ∈ P, (T p).card ≤ (degree - 1) ^ s := by
    intro p hp
    simp only [hP, Finset.mem_filter, Finset.mem_offDiag] at hp
    obtain ⟨⟨h1, h2, hpne⟩, -⟩ := hp
    rw [hSf, Set.Finite.mem_toFinset] at h1 h2
    simp only [hT]
    refine le_trans (le_of_eq (card_filter_forall_pi
      (fun x : ↥(domainComplement φ) =>
        (Lagrange.interpolate Finset.univ ⇑φ p.1).eval x.1
          = (Lagrange.interpolate Finset.univ ⇑φ p.2).eval x.1))) ?_
    exact Nat.pow_le_pow_left
      (card_agreement_le (⟨p.1, h1.1⟩ : code φ degree) ⟨p.2, h2.1⟩ hpne) s
  -- The ordered pair set has at most m(m-1)/2 elements (swap-bijection halving).
  have hPm : P.card ≤ m * (m - 1) / 2 := by
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
    rw [hneg, ← hP] at hsplit
    have hswap' := hswap
    rw [← hswap'] at hsplit
    have hoff : Sf.offDiag.card = m * (m - 1) := by
      rw [Finset.offDiag_card, ← hm, ← Nat.pred_eq_sub_one, Nat.mul_pred]
    omega
  -- Counting bound: the collision event is covered by the per-pair agreement events.
  have hcount : (Finset.univ.filter (fun r : Fin s → ↥(domainComplement φ) =>
      ∃ u u' : code φ degree, u.val ≠ u'.val ∧
        u.val ∈ closeCodewordsRel (↑(code φ degree) : Set (ι → F)) f (↑δ : ℝ) ∧
        u'.val ∈ closeCodewordsRel (↑(code φ degree) : Set (ι → F)) f (↑δ : ℝ) ∧
        ∀ i : Fin s,
          let uPoly := decodeLT u
          let uPoly' := decodeLT u'
          (uPoly : F[X]).eval (r i).1 = (uPoly' : F[X]).eval (r i).1)).card
      ≤ m * (m - 1) / 2 * ((degree - 1) ^ s) := by
    refine le_trans (Finset.card_le_card (t := P.biUnion T) ?_)
      (le_trans Finset.card_biUnion_le ?_)
    · intro r hr
      rw [Finset.mem_filter] at hr
      obtain ⟨-, u, u', huu, hu, hu', hagree⟩ := hr
      have hvalne : e u.val ≠ e u'.val := fun h => huu (e.injective h)
      rcases lt_or_gt_of_ne hvalne with hlt | hgt
      · refine Finset.mem_biUnion.mpr ⟨(u.val, u'.val), ?_, ?_⟩
        · rw [hP, Finset.mem_filter, Finset.mem_offDiag]
          refine ⟨⟨?_, ?_, huu⟩, hlt⟩ <;> rw [hSf, Set.Finite.mem_toFinset] <;> assumption
        · simp only [hT]
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ r, fun i => hagree i⟩
      · refine Finset.mem_biUnion.mpr ⟨(u'.val, u.val), ?_, ?_⟩
        · rw [hP, Finset.mem_filter, Finset.mem_offDiag]
          refine ⟨⟨?_, ?_, fun h => huu h.symm⟩, hgt⟩ <;>
            rw [hSf, Set.Finite.mem_toFinset] <;> assumption
        · simp only [hT]
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ r, fun i => (hagree i).symm⟩
    · refine le_trans (Finset.sum_le_card_nsmul P _ _ hpair) ?_
      rw [smul_eq_mul]
      exact Nat.mul_le_mul_right _ hPm
  -- The sample-space size: |F \ φ(ι)|^s.
  have hcardX : Fintype.card (Fin s → ↥(domainComplement φ))
      = (Fintype.card F - Fintype.card ι) ^ s := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    congr 1
    unfold domainComplement
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      show Finset.image φ.toFun Finset.univ = Finset.image ⇑φ Finset.univ from rfl,
      Finset.card_image_of_injective _ φ.injective, Finset.card_univ]
  -- Assemble in ENNReal.
  unfold listDecodingCollisionProbability
  refine le_trans (le_of_eq (uniform_event_mass _)) ?_
  refine le_trans (mul_le_mul_left (Nat.cast_le.mpr hcount) _) ?_
  rw [hcardX, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, ENNReal.inv_pow, mul_assoc,
    ← mul_pow, ← div_eq_mul_inv]
  refine mul_le_mul' ?_ (le_of_eq ?_)
  · rw [ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
    calc (↑(m * (m - 1) / 2) : ENNReal) * 2
        = ↑(m * (m - 1) / 2 * 2) := by rw [Nat.cast_mul, Nat.cast_ofNat]
      _ ≤ (↑(m * (m - 1)) : ENNReal) := Nat.cast_le.mpr (Nat.div_mul_le_self _ 2)
      _ = ↑m * (↑m - 1) := by rw [Nat.cast_mul, ENNReal.natCast_sub, Nat.cast_one]
      _ ≤ ↑l * (↑l - 1) := mul_le_mul' hml (tsub_le_tsub_right hml 1)
  · rw [ENNReal.natCast_sub, Nat.cast_one, ENNReal.natCast_sub]

/-- Lemma 4.5.2 -/
lemma out_of_dom_smpl_2
    {δ l : ℝ≥0} {s : ℕ} {f : ι → F} {degree : ℕ} {φ : ι ↪ F}
  (C : Set (ι → F)) (hC : C = code φ degree)
  (h_decodable : listDecodable C δ l)
  (h_nonempty : Nonempty (domainComplement φ)) :
  listDecodingCollisionProbability φ f δ s degree h_nonempty ≤
    ((l^2 / 2)) * (degree / (Fintype.card F - Fintype.card ι))^s
  := by
    transitivity
    · exact out_of_dom_smpl_1 C hC h_decodable h_nonempty
    · apply mul_le_mul'
      · apply ENNReal.div_le_div_right
        rw [pow_two]
        apply mul_le_mul' (by rfl)
        exact tsub_le_self
      · apply pow_le_pow_left'
        apply ENNReal.div_le_div_right
        exact tsub_le_self

end OutOfDomSmpl

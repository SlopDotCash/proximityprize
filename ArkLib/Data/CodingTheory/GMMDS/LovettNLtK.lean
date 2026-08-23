/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettRaise
import ArkLib.Data.CodingTheory.GMMDS.LovettPrimitiveDischarge

/-!
# Lovett's GM-MDS proof: the `n < k` primitive closure (Lemma 2.6, direct) (#389)

The genuine algebraic heart of Lovett's primitive case when `n < k` (arXiv:1803.02523, Lemma 2.6
+ final contradiction), proven *directly* as an independence statement (not by minimal-
counterexample contradiction).

Given a primitive `V*(k)` system with witness `vᵢ₀ = (1,…,1,0)` (Lemma 2.5) and `n < k`:

* `V' := raiseVec V i₀` has `|P(k,V')| = |P(k,V)| − 1`, so the `d`-induction hypothesis gives
  `P(k,V')` independent.
* `P(k,V') ∪ {p}` with `p = pVanish (V i₀)` is independent: every member of `P(k,V')` is divisible
  by `(x − a_last)` (the raised witness carries a `1` there, every other vector by Lemma 2.1),
  while `p` is not (`linearIndependent_separate_one`).
* `P(k,V)` and `P(k,V') ∪ {p}` span the same space (the block-span identity, lifted across the
  union: only the `i₀`-block changes, and there it is exactly
  `span {p·xᵉ : e ≤ k−n} = span ({p·(x−a_last)·xᵉ : e < k−n} ∪ {p})`) and have equal cardinality
  `d`, so by counting `P(k,V)` is independent.

Issue #389.
-/

open Finset Polynomial

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n m : ℕ}

/-- `pFam v e` is the plain block generator `pblk (pVanish v) e`. -/
theorem pFam_eq_pblk (v : Fin n → ℕ) (e : ℕ) :
    pFam (F := F) v e = pblk (pVanish (F := F) v) e := rfl

/-- For the raised witness, `pFam (raiseVec) e` is the raised block generator `rblk` of
`pVanish (V i₀)` at `c = a_last = X (lastCoord)`. -/
theorem pFam_raiseVec_eq_rblk {V : Fin m → (Fin n → ℕ)} (hn : 1 ≤ n) (i₀ : Fin m)
    (h0 : V i₀ (lastCoord n hn) = 0) (e : ℕ) :
    pFam (F := F) (raiseVec V hn i₀ i₀) e
      = rblk (pVanish (F := F) (V i₀)) (MvPolynomial.X (lastCoord n hn)) e := by
  rw [pFam, pVanish_raiseVec_self hn i₀ h0, rblk, xSubA]
  ring

/-- The induction measure drops by exactly `1` under the witness raise. -/
theorem lovettD_raiseVec {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n)
    {i₀ : Fin m} (hone : V i₀ = oneVec n hn) (hnk : n < k) :
    lovettD (raiseVec V hn i₀) k + 1 = lovettD V k := by
  classical
  have h0 : V i₀ (lastCoord n hn) = 0 := by rw [hone]; exact oneVec_last hn
  unfold lovettD
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
      ← Finset.add_sum_erase _ (fun i => k - vAbs (V i)) (Finset.mem_univ i₀)]
  have hother : ∑ i ∈ Finset.univ.erase i₀, (k - vAbs (raiseVec V hn i₀ i))
      = ∑ i ∈ Finset.univ.erase i₀, (k - vAbs (V i)) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [raiseVec_of_ne hn (Finset.ne_of_mem_erase hi)]
  rw [hother]
  have hwt0 : vAbs (raiseVec V hn i₀ i₀) = n := by
    rw [vAbs_raiseVec_self hn i₀ h0, hone, vAbs_oneVec hn]; omega
  have hwtV : vAbs (V i₀) = n - 1 := by rw [hone, vAbs_oneVec hn]
  rw [hwt0, hwtV]
  omega

/-- A ring map of polynomials carries `pblk` to `pblk` of the image. -/
theorem map_pblk {R S : Type*} [CommRing R] [CommRing S] (ψ : R →+* S) (a : R[X]) (e : ℕ) :
    (pblk a e).map ψ = pblk (a.map ψ) e := by
  rw [pblk, pblk, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]

/-- A ring map of polynomials carries `rblk` to `rblk` of the images. -/
theorem map_rblk {R S : Type*} [CommRing R] [CommRing S] (ψ : R →+* S) (a : R[X]) (c : R) (e : ℕ) :
    (rblk a c e).map ψ = rblk (a.map ψ) (ψ c) e := by
  rw [rblk, rblk, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

/-! ## The `n < k` independence -/

open scoped Classical in
/-- **Lovett's `n < k` primitive closure** (Lemma 2.6 + final contradiction, direct form).
A primitive `V*(k)` system with witness `vᵢ₀ = (1,…,1,0)` and `n < k` is independent. -/
theorem lovettHolds_nLtK {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hk : 1 ≤ k)
    (hV : IsVStar V k) (hn : 1 ≤ n) {i₀ : Fin m} (hone : V i₀ = oneVec n hn) (hnk : n < k)
    (IHd : ∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k < lovettD V k → IsVStar V' k → LovettHolds F V' k) :
    LovettHolds F V k := by
  classical
  set R := MvPolynomial (Fin n) F
  set j := lastCoord n hn with hj
  have h0 : V i₀ (lastCoord n hn) = 0 := by rw [hone]; exact oneVec_last hn
  -- the raised system
  set V' := raiseVec V hn i₀ with hV'
  have hV'star : IsVStar V' k := raiseVec_isVStar hk hV hn hone hnk
  -- d-IH ⟹ P(k,V') independent
  have hDlt : lovettD V' k < lovettD V k := by
    have h : lovettD V' k + 1 = lovettD V k := lovettD_raiseVec hk hn hone hnk
    omega
  have hindep' : LovettHolds F V' k := IHd V' hDlt hV'star
  -- every V' i has a 1 in the last coordinate
  have hall : ∀ i, 1 ≤ V' i j := by
    intro i
    by_cases hi : i = i₀
    · rw [hi, hV']; rw [raiseVec_self_last]
    · rw [hV', raiseVec_of_ne hn hi]
      exact witness_others_last_pos hk hV hn hone hi
  -- the separated family P(k,V') ∪ {p}, p = pFam (V i₀) 0 = pVanish (V i₀)
  have hsep := linearIndependent_separate_one (F := F) (V := V') (k := k) (j := j)
    hindep' hall (vlast := V i₀) h0
  -- name the two families over R[X]
  set g : (Σ i : Fin m, Fin (k - vAbs (V i))) → R[X] := pFamUnion (F := F) V k with hg
  set hfam : Option (Σ i : Fin m, Fin (k - vAbs (V' i))) → R[X] :=
    fun o => o.elim (pFam (F := F) (V i₀) 0) (pFamUnion (F := F) V' k) with hhfam
  -- `hsep : LinearIndependent R hfam`
  -- card equality: |g-index| = d = d' + 1 = |hfam-index|
  have hcardEq : Fintype.card (Σ i : Fin m, Fin (k - vAbs (V i)))
      = Fintype.card (Option (Σ i : Fin m, Fin (k - vAbs (V' i)))) := by
    rw [card_pFamUnion_index, Fintype.card_option, card_pFamUnion_index]
    have h : (∑ i, (k - vAbs (V' i))) + 1 = ∑ i, (k - vAbs (V i)) :=
      lovettD_raiseVec hk hn hone hnk
    omega
  -- pass to the fraction field K = Frac(R)
  set K := FractionRing R with hK
  set φ : R[X] → K[X] := fun p => p.map (algebraMap R K) with hφ
  -- φ is the linear map of the bridge; record its ring-hom behaviour
  have hφmul : ∀ a b : R[X], φ (a * b) = φ a * φ b := fun a b => Polynomial.map_mul _
  -- the two field-level families
  set gK : (Σ i : Fin m, Fin (k - vAbs (V i))) → K[X] := φ ∘ g with hgK
  set hK' : Option (Σ i : Fin m, Fin (k - vAbs (V' i))) → K[X] := φ ∘ hfam with hhK'
  -- bridge: hfam independent over R ⟹ hK' independent over K
  have hindepK : LinearIndependent K hK' :=
    (linearIndependent_fractionField_iff hfam).mp hsep
  -- the witness vanishing polynomial, mapped, and the separation point
  set w : K[X] := φ (pVanish (F := F) (V i₀)) with hw
  set c : K := algebraMap R K (MvPolynomial.X j) with hc
  -- block degree bound: k - |V i₀| = (k - n) + 1
  have hVi0 : vAbs (V i₀) = n - 1 := by rw [hone, vAbs_oneVec hn]
  -- abbreviation for d = k - n
  set d : ℕ := k - n with hd
  -- the span equality span(range gK) = span(range hK')
  have hspan : Submodule.span K (Set.range gK) = Submodule.span K (Set.range hK') := by
    apply le_antisymm
    · -- range gK ⊆ span (range hK')
      rw [Submodule.span_le]
      rintro _ ⟨⟨i, e⟩, rfl⟩
      by_cases hi : i = i₀
      · -- i = i₀: plain block; use pblk_mem_span_rblk
        subst hi
        -- gK ⟨i,e⟩ = pblk w (e:ℕ)
        have hval : gK ⟨i, e⟩ = pblk w (e : ℕ) := by
          show φ (pFam (F := F) (V i) (e : ℕ)) = pblk w (e : ℕ)
          rw [pFam_eq_pblk]; exact map_pblk _ _ _
        rw [SetLike.mem_coe, hval]
        -- membership in span (insert w (range rblk)) ⊆ span (range hK')
        have hebound : (e : ℕ) ≤ d := by
          have he : (e : ℕ) < k - vAbs (V i) := e.isLt
          have hkv : k - vAbs (V i) = d + 1 := by rw [hVi0]; omega
          omega
        have hmem := pblk_mem_span_rblk w c d (e : ℕ) hebound
        refine Submodule.span_mono ?_ hmem
        -- insert w (range (rblk w c)) ⊆ range hK'
        rintro x (rfl | ⟨e', rfl⟩)
        · -- x = w = hK' none
          exact ⟨none, by
            show φ (pFam (F := F) (V i) 0) = w
            rw [pFam_eq_pblk, pblk, pow_zero, mul_one]⟩
        · -- x = rblk w c e' = hK' (some ⟨i, e'⟩)
          refine ⟨some ⟨i, ⟨(e' : ℕ), by
            have := e'.isLt
            have : vAbs (V' i) = n := by
              rw [hV']; exact (vAbs_raiseVec_self hn i h0).trans (by rw [hVi0]; omega)
            simp only [this]; omega⟩⟩, ?_⟩
          show φ (pFam (F := F) (V' i) (e' : ℕ)) = rblk w c (e' : ℕ)
          rw [hV', pFam_raiseVec_eq_rblk hn i h0]
          show φ (rblk (pVanish (F := F) (V i)) (MvPolynomial.X j) (e' : ℕ))
              = rblk w c (e' : ℕ)
          exact map_rblk _ _ _ _
      · -- i ≠ i₀: identical block, member of range hK'
        have hVeq : V' i = V i := by rw [hV', raiseVec_of_ne hn hi]
        have hwt : vAbs (V' i) = vAbs (V i) := by rw [hVeq]
        refine Submodule.subset_span ⟨some ⟨i, ⟨(e : ℕ), by rw [hwt]; exact e.isLt⟩⟩, ?_⟩
        show φ (pFam (F := F) (V' i) (e : ℕ)) = gK ⟨i, e⟩
        rw [hVeq]; rfl
    · -- range hK' ⊆ span (range gK)
      rw [Submodule.span_le]
      rintro _ ⟨o, rfl⟩
      cases o with
      | none =>
        -- hK' none = w = pblk w 0 ∈ plain block, e=0
        have hval : hK' none = pblk w 0 := by
          show φ (pFam (F := F) (V i₀) 0) = pblk w 0
          rw [pFam_eq_pblk]; exact map_pblk _ _ _
        rw [SetLike.mem_coe, hval]
        refine Submodule.subset_span ⟨⟨i₀, ⟨0, by rw [hVi0]; omega⟩⟩, ?_⟩
        show gK ⟨i₀, ⟨0, _⟩⟩ = pblk w 0
        show φ (pFam (F := F) (V i₀) 0) = pblk w 0
        rw [pFam_eq_pblk]; exact map_pblk _ _ _
      | some p =>
        obtain ⟨i, e⟩ := p
        by_cases hi : i = i₀
        · -- i = i₀: rblk member; in span of plain block (rblk_mem_span_pblk)
          have hV'i : V' i = raiseVec V hn i₀ i₀ := by rw [hV', hi]
          have hh0i : V i₀ (lastCoord n hn) = 0 := h0
          have key : ∀ E : ℕ, φ (pFam (F := F) (V' i) E) = rblk w c E := by
            intro E
            rw [hV'i, pFam_raiseVec_eq_rblk hn i₀ hh0i]
            show φ (rblk (pVanish (F := F) (V i₀)) (MvPolynomial.X j) E)
                = rblk w c E
            exact map_rblk _ _ _ _
          have hval : hK' (some ⟨i, e⟩) = rblk w c (e : ℕ) := key (e : ℕ)
          rw [SetLike.mem_coe, hval]
          have he : (e : ℕ) + 1 ≤ d := by
            have hlt := e.isLt
            have hwt' : k - vAbs (V' i) = d := by
              rw [hV'i, vAbs_raiseVec_self hn i₀ hh0i, hVi0]; omega
            omega
          have hmem := rblk_mem_span_pblk w c (d := d) he
          refine Submodule.span_mono ?_ hmem
          rintro x ⟨e', rfl⟩
          refine ⟨⟨i, ⟨(e' : ℕ), by
            have hlt := e'.isLt
            have : k - vAbs (V i) = d + 1 := by rw [hi, hVi0]; omega
            omega⟩⟩, ?_⟩
          show φ (pFam (F := F) (V i) (e' : ℕ)) = pblk w (e' : ℕ)
          rw [hi, pFam_eq_pblk]; exact map_pblk (algebraMap R K) _ _
        · -- i ≠ i₀: identical block, member of range gK
          have hVeq : V' i = V i := by rw [hV', raiseVec_of_ne hn hi]
          have hwt : vAbs (V' i) = vAbs (V i) := by rw [hVeq]
          have key : ∀ E : ℕ, φ (pFam (F := F) (V i) E) = φ (pFam (F := F) (V' i) E) := by
            intro E; rw [hVeq]
          refine Submodule.subset_span ⟨⟨i, ⟨(e : ℕ), by rw [← hwt]; exact e.isLt⟩⟩, ?_⟩
          show φ (pFam (F := F) (V i) (e : ℕ)) = φ (pFam (F := F) (V' i) (e : ℕ))
          exact key (e : ℕ)
  -- counting transfer: gK independent over K
  have hgKindep : LinearIndependent K gK :=
    linearIndependent_of_span_eq_card hspan hcardEq hindepK
  -- bridge back to R
  show LinearIndependent R g
  rw [linearIndependent_fractionField_iff]
  exact hgKindep

/-! ## The unified primitive-case assembly (`n = k` ∨ `n < k`) -/

/-- **The primitive-case assembly** (Lovett §2 final step).  From the structured witness
`vᵢ₀ = (1,…,1,0)` (Lemma 2.5) and the `d`-induction hypothesis, the primitive system `V` is
independent.  We always have `n ≤ k` (`witness_n_le_k`), and split:

* `n = k`: the witness block has size `k − |vᵢ₀| = k − (n − 1) = 1`; close by one-vector
  separation (`lovettHolds_of_witness_nEqK`).
* `n < k`: the genuine Lovett Lemma 2.6 / final contradiction, proven directly
  (`lovettHolds_nLtK`): raise the witness and transfer independence via the block-span identity. -/
theorem lovettHolds_of_witness {m : ℕ} {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hk : 1 ≤ k)
    (hV : IsVStar V k) (hw : LovettWitness F V k)
    (IHd : ∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k < lovettD V k → IsVStar V' k → LovettHolds F V' k) :
    LovettHolds F V k := by
  obtain ⟨hn, i₀, hone⟩ := hw
  have hle : n ≤ k := witness_n_le_k hk hV hn hone
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact lovettHolds_nLtK hk hV hn hone hlt IHd
  · exact lovettHolds_of_witness_nEqK hk hV hn hone heq IHd

/-- **The primitive step reduces to the witness residual** (Lemma 2.5 existence). -/
theorem lovettPrimitiveStep_of_witnessExists (hw : LovettWitnessExists F) :
    LovettPrimitiveStep F := by
  intro n m V k hk hV hprim IHn IHd IHm
  exact lovettHolds_of_witness hk hV (hw V k hk hV hprim IHn IHd IHm) IHd

/-- **`LovettPrimitiveCase` (and full Theorem 1.7) reduce to the witness residual.** -/
theorem lovettPrimitiveCase_of_witnessExists (hw : LovettWitnessExists F) {n : ℕ} :
    LovettPrimitiveCase F n :=
  lovettPrimitiveCase_of_primitiveStep (lovettPrimitiveStep_of_witnessExists hw)

theorem lovettThm17_of_witnessExists (hw : LovettWitnessExists F) {n : ℕ} : LovettThm17 F n :=
  lovettThm17_of_primitiveStep (lovettPrimitiveStep_of_witnessExists hw)

end ArkLib.GMMDS

-- Axiom audit
#print axioms ArkLib.GMMDS.lovettHolds_nLtK
#print axioms ArkLib.GMMDS.lovettHolds_of_witness
#print axioms ArkLib.GMMDS.lovettPrimitiveStep_of_witnessExists
#print axioms ArkLib.GMMDS.lovettThm17_of_witnessExists

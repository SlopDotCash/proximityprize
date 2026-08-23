/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubJohnsonListSupply
import ArkLib.Data.CodingTheory.ProximityGap.EsymmFiber

/-!
# The `μ_n` list carries a cyclic symmetry (#389 / #357)

The Reed–Solomon code on the roots-of-unity domain `μ_n` is *cyclic*: the index
shift `i ↦ i+1` (mod `n`) corresponds on the domain to multiplication by `ζ`
(`domRU_succ`: `domRU(i+1) = ζ·domRU(i)`, clean because `ζⁿ = 1`).  The core fact
`rsCode_eval_scale_mem` (`i ↦ P(α·domRU i)` is a codeword for any `α ≠ 0`, via
`P(X) ↦ P(αX)`, degree-preserving) makes `rsCode (domRU)` invariant under both the
shift `shiftWord f = f ∘ (·+1)` and its inverse.

Consequently the shift acts as a **bijection between the list of `w` and the list of
`shiftWord w`**, so the sub-Johnson list size is *invariant under the cyclic shift of
the word* (`bigAgreeCodewords_card_shift`).  This is the structural symmetry the
threshold (`δ*`) argument exploits: the list-size function on words is constant on
cyclic orbits, reducing it to orbit representatives / a character-sum analysis — the
genuine open route below Johnson.  Here we land the symmetry itself, axiom-clean.
-/

open Polynomial

namespace ProximityGap.RUCyclic

open ProximityGap.Ownership ProximityGap.EsymmFiber ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The cyclic shift on words: `shiftWord f i = f (i+1)`. -/
def shiftWord (f : Fin n → F) : Fin n → F := fun i => f (i + 1)

/-- Its inverse: `unShiftWord f i = f (i-1)`. -/
def unShiftWord (f : Fin n → F) : Fin n → F := fun i => f (i - 1)

@[simp] theorem unShift_shift (f : Fin n → F) : unShiftWord (shiftWord f) = f := by
  funext i; simp [unShiftWord, shiftWord, sub_add_cancel]

@[simp] theorem shift_unShift (f : Fin n → F) : shiftWord (unShiftWord f) = f := by
  funext i; simp [unShiftWord, shiftWord, sub_add_cancel]

theorem shiftWord_injective : Function.Injective (shiftWord (F := F) (n := n)) :=
  Function.LeftInverse.injective unShift_shift

/-- **Domain equivariance.**  On `μ_n`, the index shift is multiplication by `ζ`:
`domRU(i+1) = ζ · domRU(i)` — using `ζⁿ = 1` to absorb the wraparound. -/
theorem domRU_succ {ζ : F} (hζ : IsPrimitiveRoot ζ n) (i : Fin n) :
    domRU hζ (i + 1) = ζ * domRU hζ i := by
  simp only [domRU_apply]
  have hmod : ((i + 1 : Fin n) : ℕ) ≡ (i : ℕ) + 1 [MOD n] := by
    rw [Fin.val_add]
    refine (Nat.mod_modEq _ _).trans (Nat.ModEq.add_left _ ?_)
    rw [Fin.val_one']
    exact Nat.mod_modEq 1 n
  conv_rhs => rw [mul_comm, ← pow_succ]
  rw [← pow_mod_orderOf ζ ((i + 1 : Fin n) : ℕ), ← pow_mod_orderOf ζ ((i : ℕ) + 1),
    ← hζ.eq_orderOf]
  exact congrArg (ζ ^ ·) hmod

/-- `domRU(i-1) = ζ⁻¹ · domRU(i)`. -/
theorem domRU_pred {ζ : F} (hζ : IsPrimitiveRoot ζ n) (i : Fin n) :
    domRU hζ (i - 1) = ζ⁻¹ * domRU hζ i := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
  have h := domRU_succ hζ (i - 1)
  rw [sub_add_cancel] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ hζ0, one_mul]

/-- **Core: `rsCode` contains every domain-scaling of a codeword.**  For `α ≠ 0`, the
word `i ↦ P(α·domRU i)` is a degree-`<k` codeword (`P(X) ↦ P(αX)` preserves degree). -/
theorem rsCode_eval_scale_mem {ζ : F} (hζ : IsPrimitiveRoot ζ n) {k : ℕ}
    {P : F[X]} (hP : P.degree < (k : WithBot ℕ)) (α : F) (hα : α ≠ 0) :
    (fun i => P.eval (α * domRU hζ i)) ∈ (rsCode (domRU hζ) k : Submodule F (Fin n → F)) := by
  refine ⟨P.comp (C α * X), ?_, ?_⟩
  · rcases eq_or_ne P 0 with rfl | hP0
    · simpa using hP
    · have hqne : C α * X ≠ C ((C α * X).coeff 0) := by
        have hcoeff : (C α * X).coeff 0 = 0 := by simp
        rw [hcoeff, map_zero]
        intro h
        have : (C α * X).natDegree = 1 := Polynomial.natDegree_C_mul_X α hα
        rw [h] at this; simp at this
      have hcomp0 : P.comp (C α * X) ≠ 0 := by
        intro h
        rw [Polynomial.comp_eq_zero_iff] at h
        rcases h with hPz | ⟨_, hq⟩
        · exact hP0 hPz
        · exact hqne hq
      have hdeg : (P.comp (C α * X)).natDegree = P.natDegree := by
        rw [Polynomial.natDegree_comp, Polynomial.natDegree_C_mul_X α hα, mul_one]
      have hndlt : P.natDegree < k := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hP
      exact (Polynomial.natDegree_lt_iff_degree_lt hcomp0).mp (by rw [hdeg]; exact hndlt)
  · funext i
    rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

/-- The shift preserves codewords. -/
theorem rsCode_shiftWord_mem {ζ : F} (hζ : IsPrimitiveRoot ζ n) {k : ℕ}
    {c : Fin n → F} (hc : c ∈ (rsCode (domRU hζ) k : Submodule F (Fin n → F))) :
    shiftWord c ∈ (rsCode (domRU hζ) k : Submodule F (Fin n → F)) := by
  obtain ⟨P, hP, rfl⟩ := hc
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
  have heq : shiftWord (fun j => P.eval (domRU hζ j))
      = (fun i => P.eval (ζ * domRU hζ i)) := by
    funext i; rw [shiftWord, domRU_succ hζ i]
  rw [heq]; exact rsCode_eval_scale_mem hζ hP ζ hζ0

/-- The inverse shift preserves codewords. -/
theorem rsCode_unShiftWord_mem {ζ : F} (hζ : IsPrimitiveRoot ζ n) {k : ℕ}
    {c : Fin n → F} (hc : c ∈ (rsCode (domRU hζ) k : Submodule F (Fin n → F))) :
    unShiftWord c ∈ (rsCode (domRU hζ) k : Submodule F (Fin n → F)) := by
  obtain ⟨P, hP, rfl⟩ := hc
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
  have heq : unShiftWord (fun j => P.eval (domRU hζ j))
      = (fun i => P.eval (ζ⁻¹ * domRU hζ i)) := by
    funext i; rw [unShiftWord, domRU_pred hζ i]
  rw [heq]; exact rsCode_eval_scale_mem hζ hP ζ⁻¹ (inv_ne_zero hζ0)

open Classical in
/-- Agreement counts are shift-invariant: `i ↦ i+1` bijects the agreement set of the
shifted pair onto that of the original. -/
theorem listAgreeSet_shift_card (c w : Fin n → F) :
    (listAgreeSet (shiftWord c) (shiftWord w)).card = (listAgreeSet c w).card := by
  refine Finset.card_bij (fun i _ => i + 1) ?_ ?_ ?_
  · intro i hi
    rw [listAgreeSet, Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_univ _, hi.2⟩
  · intro i _ j _ h; exact add_right_cancel h
  · intro j hj
    rw [listAgreeSet, Finset.mem_filter] at hj
    refine ⟨j - 1, ?_, by simp⟩
    rw [listAgreeSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show shiftWord c (j - 1) = shiftWord w (j - 1)
    rw [shiftWord, shiftWord, sub_add_cancel]
    exact hj.2

open Classical in
/-- **The list size is invariant under the cyclic shift of the word.**  The shift maps
`bigAgreeCodewords w` bijectively onto `bigAgreeCodewords (shiftWord w)` (it permutes
`rsCode` and preserves agreement counts), so the two have equal cardinality.  The
sub-Johnson list-size function is therefore constant on cyclic orbits of words. -/
theorem bigAgreeCodewords_card_shift {ζ : F} (hζ : IsPrimitiveRoot ζ n) {k m : ℕ}
    (w : Fin n → F) :
    (bigAgreeCodewords (domRU hζ) k m (shiftWord w)).card
      = (bigAgreeCodewords (domRU hζ) k m w).card := by
  symm
  -- shiftWord is a bijection bigAgree(w) → bigAgree(shiftWord w)
  refine Finset.card_bij' (fun c _ => shiftWord c) (fun c _ => unShiftWord c) ?_ ?_ ?_ ?_
  · intro c hc
    rw [bigAgreeCodewords, Finset.mem_filter] at hc ⊢
    obtain ⟨-, hcC, hcard⟩ := hc
    exact ⟨Finset.mem_univ _, rsCode_shiftWord_mem hζ hcC,
      by rw [listAgreeSet_shift_card]; exact hcard⟩
  · intro c hc
    rw [bigAgreeCodewords, Finset.mem_filter] at hc ⊢
    obtain ⟨-, hcC, hcard⟩ := hc
    refine ⟨Finset.mem_univ _, rsCode_unShiftWord_mem hζ hcC, ?_⟩
    have hsc := listAgreeSet_shift_card (unShiftWord c) w
    rw [shift_unShift] at hsc
    rw [← hsc]; exact hcard
  · intro c _; exact unShift_shift c
  · intro c _; exact shift_unShift c

/-- **Full `ℤ/n` action: the list size is invariant under every iterated shift.**  By
induction on the single-shift invariance, the sub-Johnson list size is a genuine class
function on the cyclic orbits of words. -/
theorem bigAgreeCodewords_card_iterate {ζ : F} (hζ : IsPrimitiveRoot ζ n) {k m : ℕ}
    (w : Fin n → F) (j : ℕ) :
    (bigAgreeCodewords (domRU hζ) k m (shiftWord^[j] w)).card
      = (bigAgreeCodewords (domRU hζ) k m w).card := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ', Function.comp_apply, bigAgreeCodewords_card_shift, ih]

/-- The core-shift embedding `i ↦ i+1` on index sets. -/
def coreShift : Fin n ↪ Fin n := (Equiv.addRight (1 : Fin n)).toEmbedding

/-- Its inverse embedding `i ↦ i-1`. -/
def coreUnShift : Fin n ↪ Fin n := (Equiv.addRight (1 : Fin n)).symm.toEmbedding

@[simp] theorem coreShift_apply (i : Fin n) : coreShift i = i + 1 := rfl
@[simp] theorem coreUnShift_apply (i : Fin n) : coreUnShift i = i - 1 := by
  show (Equiv.addRight (1 : Fin n)).symm i = i - 1
  rw [Equiv.addRight_symm]; exact (sub_eq_add_neg i 1).symm

theorem map_coreShift_unShift (T : Finset (Fin n)) :
    (T.map coreShift).map coreUnShift = T := by
  have hcomp : coreShift.trans coreUnShift = Function.Embedding.refl (Fin n) := by
    ext i
    simp only [Function.Embedding.trans_apply, coreShift_apply, coreUnShift_apply,
      Function.Embedding.refl_apply, add_sub_cancel_right]
  rw [Finset.map_map, hcomp, Finset.map_refl]

theorem map_coreUnShift_shift (T : Finset (Fin n)) :
    (T.map coreUnShift).map coreShift = T := by
  have hcomp : coreUnShift.trans coreShift = Function.Embedding.refl (Fin n) := by
    ext i
    simp only [Function.Embedding.trans_apply, coreShift_apply, coreUnShift_apply,
      Function.Embedding.refl_apply, sub_add_cancel]
  rw [Finset.map_map, hcomp, Finset.map_refl]

open Classical in
/-- **Explainability is shift-equivariant.**  `w` is explainable on the shifted core
`T.map coreShift` iff `shiftWord w` is explainable on `T` (transport the explaining
codeword by the shift). -/
theorem explainableOn_shift_iff {ζ : F} (hζ : IsPrimitiveRoot ζ n) {k : ℕ}
    (w : Fin n → F) (T : Finset (Fin n)) :
    ExplainableOn (domRU hζ) k w (T.map coreShift)
      ↔ ExplainableOn (domRU hζ) k (shiftWord w) T := by
  constructor
  · rintro ⟨c, hcC, hcag⟩
    refine ⟨shiftWord c, rsCode_shiftWord_mem hζ hcC, fun i hi => ?_⟩
    have : (i + 1) ∈ T.map coreShift := by
      rw [Finset.mem_map]; exact ⟨i, hi, by simp⟩
    have hc := hcag _ this
    simpa [shiftWord] using hc
  · rintro ⟨c, hcC, hcag⟩
    refine ⟨unShiftWord c, rsCode_unShiftWord_mem hζ hcC, fun j hj => ?_⟩
    rw [Finset.mem_map] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    have hc := hcag i hi
    simpa [unShiftWord, shiftWord, coreShift_apply, add_sub_cancel_right] using hc

open Classical in
/-- **The explainable-core count (`ExplainableCoreSupply`'s quantity) is shift-invariant.**
The core-shift `T ↦ T.map coreShift` bijects the explainable `(k+m+1)`-cores of `w`
onto those of `shiftWord w`.  Hence `ExplainableCoreSupply` is a *cyclic-orbit
invariant* on `μ_n`: if it fails for one word it fails for every shift, and the
exponential deep-band lower bound `not_explainableCoreSupply_exponential` propagates
across the whole orbit. -/
theorem explainableCoreCount_shift {ζ : F} (hζ : IsPrimitiveRoot ζ n) {k m : ℕ}
    (w : Fin n → F) :
    (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ExplainableOn (domRU hζ) k (shiftWord w) T)).card
      = (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ExplainableOn (domRU hζ) k w T)).card := by
  refine Finset.card_bij' (fun T _ => T.map coreShift) (fun T _ => T.map coreUnShift) ?_ ?_ ?_ ?_
  · -- s = explainable for shiftWord w → t = explainable for w
    intro T hT
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hT ⊢
    obtain ⟨⟨-, hcard⟩, hexpl⟩ := hT
    exact ⟨⟨Finset.subset_univ _, by rw [Finset.card_map]; exact hcard⟩,
      (explainableOn_shift_iff hζ w T).mpr hexpl⟩
  · intro T hT
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hT ⊢
    obtain ⟨⟨-, hcard⟩, hexpl⟩ := hT
    refine ⟨⟨Finset.subset_univ _, by rw [Finset.card_map]; exact hcard⟩, ?_⟩
    exact (explainableOn_shift_iff hζ w (T.map coreUnShift)).mp (by rwa [map_coreUnShift_shift])
  · intro T _; exact map_coreShift_unShift T
  · intro T _; exact map_coreUnShift_shift T

end ProximityGap.RUCyclic

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.RUCyclic.domRU_succ
#print axioms ProximityGap.RUCyclic.rsCode_shiftWord_mem
#print axioms ProximityGap.RUCyclic.bigAgreeCodewords_card_shift
#print axioms ProximityGap.RUCyclic.explainableCoreCount_shift

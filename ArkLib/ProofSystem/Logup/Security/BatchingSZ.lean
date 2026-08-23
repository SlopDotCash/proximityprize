/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckPolynomial
import ArkLib.Data.MvPolynomial.MultilinearSchwartzZippel

/-!
# The batching Schwartz–Zippel step of the LogUp outer soundness (issue #13, piece α2)

For the inconsistent-helpers branch of the outer mid-claim soundness: if some domain-identity
value is nonzero (`g k₀ u₀ ≠ 0`), then the batched claim

  `claim (z, s) = C + ∑ k, s k * L k z`,  with  `L k z = ∑ u, lagrangeKernel F u z * g k u`

vanishes at a uniformly random `(z, s)` only with probability `≤ (n + 1) / |F|` — counted here in
card form: `card · |F| ≤ (n + 1) · |F|^{n + K}` over the `|F|^{n+K}` points `(z, s)`.

Proof: `L k₀` is the signed multilinear extension of `g k₀`, hence a *nonzero* multilinear
polynomial (its value at the cube point `signPoint u₀` is `g k₀ u₀` by the Kronecker-delta property
of the Lagrange kernel); by the multilinear Schwartz–Zippel bound its zero set in `F^n` has at most
`n · |F|^{n-1}` points. For `z` outside that set the claim is a nonconstant affine function of
`s k₀`, pinning `s k₀` to a single value. The union of the two contributions gives the bound.

No `sorry`; axiom audit at the bottom.
-/

open Finset MvPolynomial
open scoped BigOperators

namespace Logup

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

section SignedMLE

/-- The signed basis polynomial `(2^n)⁻¹ ∏ⱼ (1 + uⱼ Xⱼ)` whose evaluation at `r` is
`lagrangeKernel F u r`. (Public rebuild of the `private` one in `SumcheckPolynomial.lean`.) -/
noncomputable def signedBasisPoly (u : Hypercube n) : MvPolynomial (Fin n) F :=
  MvPolynomial.C (((2 : F) ^ n)⁻¹) *
    ∏ j : Fin n, (1 + MvPolynomial.C (bitToSign F (u j)) * MvPolynomial.X j)

theorem signedBasisPoly_eval (u : Hypercube n) (r : Fin n → F) :
    MvPolynomial.eval r (signedBasisPoly u) = lagrangeKernel F u r := by
  simp [signedBasisPoly, lagrangeKernel, lagrangeKernelAtPoint, signPoint]

/-- The signed multilinear extension `z ↦ ∑ᵤ g u · L_H(u, z)` as a polynomial. -/
noncomputable def signedMLE (g : Hypercube n → F) : MvPolynomial (Fin n) F :=
  ∑ u : Hypercube n, MvPolynomial.C (g u) * signedBasisPoly u

theorem signedMLE_eval (g : Hypercube n → F) (r : Fin n → F) :
    MvPolynomial.eval r (signedMLE g) = ∑ u : Hypercube n, lagrangeKernel F u r * g u := by
  simp [signedMLE, signedBasisPoly_eval, mul_comm]

/-- Per-variable degree of one signed factor: `degreeOf i (1 + C a · X j) ≤ [i = j]`. -/
theorem signedFactor_degreeOf (a : F) (j i : Fin n) :
    degreeOf i ((1 : MvPolynomial (Fin n) F) + MvPolynomial.C a * MvPolynomial.X j)
      ≤ if i = j then 1 else 0 := by
  classical
  calc degreeOf i ((1 : MvPolynomial (Fin n) F) + MvPolynomial.C a * MvPolynomial.X j)
      ≤ max (degreeOf i (1 : MvPolynomial (Fin n) F))
          (degreeOf i (MvPolynomial.C a * MvPolynomial.X j)) := degreeOf_add_le _ _ _
    _ ≤ max 0 (degreeOf i (MvPolynomial.C a) + degreeOf i (MvPolynomial.X j)) := by
        gcongr
        · simpa using le_of_eq (degreeOf_C (R := F) 1 i)
        · exact degreeOf_mul_le _ _ _
    _ ≤ max 0 (0 + (if i = j then 1 else 0)) := by
        gcongr
        · exact le_of_eq (degreeOf_C (R := F) a i)
        · by_cases h : i = j
          · simpa only [h, if_pos rfl] using degreeOf_X_le (R := F) j i
          · simpa only [h, if_neg h] using
              le_of_eq (degreeOf_X_of_ne (R := F) (i := i) (j := j) h)
    _ = if i = j then 1 else 0 := by norm_num

/-- The signed basis polynomial is multilinear. -/
theorem signedBasisPoly_mem (u : Hypercube n) :
    (signedBasisPoly (F := F) u) ∈ F⦃≤ 1⦄[X (Fin n)] := by
  classical
  rw [mem_restrictDegree_iff_degreeOf_le]
  intro i
  unfold signedBasisPoly
  calc degreeOf i (MvPolynomial.C (((2 : F) ^ n)⁻¹) *
        ∏ j : Fin n, (1 + MvPolynomial.C (bitToSign F (u j)) * MvPolynomial.X j))
      ≤ degreeOf i (MvPolynomial.C (((2 : F) ^ n)⁻¹)) +
          degreeOf i (∏ j : Fin n, (1 + MvPolynomial.C (bitToSign F (u j)) * MvPolynomial.X j)) :=
        degreeOf_mul_le _ _ _
    _ ≤ 0 + ∑ j : Fin n, degreeOf i (1 + MvPolynomial.C (bitToSign F (u j)) * MvPolynomial.X j) := by
        gcongr
        · exact le_of_eq (degreeOf_C _ i)
        · exact degreeOf_prod_le i _ _
    _ ≤ 0 + ∑ j : Fin n, (if i = j then 1 else 0) := by
        gcongr
        exact signedFactor_degreeOf _ _ _
    _ = 1 := by norm_num

/-- The signed MLE is multilinear. -/
theorem signedMLE_mem (g : Hypercube n → F) :
    (signedMLE g) ∈ F⦃≤ 1⦄[X (Fin n)] := by
  classical
  rw [mem_restrictDegree_iff_degreeOf_le]
  intro i
  unfold signedMLE
  calc degreeOf i (∑ u : Hypercube n, MvPolynomial.C (g u) * signedBasisPoly u)
      ≤ (Finset.univ : Finset (Hypercube n)).sup
          (fun u => degreeOf i (MvPolynomial.C (g u) * signedBasisPoly u)) :=
        degreeOf_sum_le i _ _
    _ ≤ (Finset.univ : Finset (Hypercube n)).sup
          (fun u => degreeOf i (MvPolynomial.C (g u)) + degreeOf i (signedBasisPoly u)) := by
        gcongr
        exact degreeOf_mul_le _ _ _
    _ ≤ (Finset.univ : Finset (Hypercube n)).sup (fun _ => 0 + 1) := by
        gcongr with u
        · exact le_of_eq (degreeOf_C _ i)
        · exact (mem_restrictDegree_iff_degreeOf_le _ _).mp (signedBasisPoly_mem u) i
    _ ≤ 1 := by simp

/-- The signed MLE is nonzero whenever the underlying function is (Kronecker-delta evaluation at
the witnessing cube point). -/
theorem signedMLE_ne_zero (hSigns : (-1 : F) ≠ 1) (g : Hypercube n → F)
    (u₀ : Hypercube n) (hg : g u₀ ≠ 0) : signedMLE g ≠ 0 := by
  intro hzero
  apply hg
  have heval := signedMLE_eval g (signPoint F u₀)
  rw [hzero] at heval
  simp only [map_zero] at heval
  -- `∑ u, lagrangeKernel F u (signPoint u₀) * g u = g u₀` by the delta property.
  have hdelta : ∑ u : Hypercube n, lagrangeKernel F u (signPoint F u₀) * g u = g u₀ := by
    rw [Finset.sum_eq_single u₀]
    · rw [lagrangeKernel_signPoint (F := F) (n := n) hSigns u₀ u₀, if_pos rfl, one_mul]
    · intro v _ hvu
      rw [lagrangeKernel_signPoint (F := F) (n := n) hSigns u₀ v, if_neg hvu, zero_mul]
    · intro h; exact absurd (Finset.mem_univ u₀) h
  rw [← hdelta, ← heval]

end SignedMLE

section BatchingCount

variable {K : ℕ}

/-- **z-stage:** the zero set of the `k₀`-th batched coefficient (the signed MLE of a function
nonzero somewhere) satisfies the multilinear Schwartz–Zippel count. -/
theorem mleCoeff_zeros_card_mul_le (hSigns : (-1 : F) ≠ 1)
    (g : Hypercube n → F) (u₀ : Hypercube n) (hg : g u₀ ≠ 0) :
    (Finset.univ.filter (fun z : Fin n → F =>
        ∑ u : Hypercube n, lagrangeKernel F u z * g u = 0)).card * Fintype.card F
      ≤ n * Fintype.card F ^ n := by
  classical
  have hcount := MvPolynomial.multilinear_zeros_card_mul_le
    (signedMLE_mem g) (signedMLE_ne_zero hSigns g u₀ hg)
  have hset : (Finset.univ.filter (fun z : Fin n → F =>
      ∑ u : Hypercube n, lagrangeKernel F u z * g u = 0))
      = (Finset.univ.filter (fun z : Fin n → F =>
        MvPolynomial.eval z (signedMLE g) = 0)) := by
    apply Finset.filter_congr
    intro z _
    rw [signedMLE_eval]
  rw [hset]
  exact hcount

/-- **The batching zero-count.** If some coefficient function is nonzero somewhere, the batched
claim `C + ∑ k, s k · Lₖ(z)` vanishes on at most `(n+1) · |F|^{n+K-1}` of the `|F|^{n+K}` points
`(z, s)` — in product form, `card · |F| ≤ (n+1) · |F|^{n+K}`. -/
theorem batching_zero_card_mul_le (hSigns : (-1 : F) ≠ 1)
    (Cc : F) (g : Fin K → Hypercube n → F) (k₀ : Fin K) (u₀ : Hypercube n)
    (hg : g k₀ u₀ ≠ 0) :
    (Finset.univ.filter (fun zs : (Fin n → F) × (Fin K → F) =>
        Cc + ∑ k : Fin K, zs.2 k * (∑ u : Hypercube n, lagrangeKernel F u zs.1 * g k u)
          = 0)).card * Fintype.card F
      ≤ (n + 1) * Fintype.card F ^ (n + K) := by
  classical
  set L : (Fin n → F) → Fin K → F :=
    fun z k => ∑ u : Hypercube n, lagrangeKernel F u z * g k u with hL
  set Z₀ : Finset (Fin n → F) := Finset.univ.filter (fun z => L z k₀ = 0) with hZ₀
  -- Split the zero set by whether `z ∈ Z₀`.
  have hsubset : (Finset.univ.filter (fun zs : (Fin n → F) × (Fin K → F) =>
      Cc + ∑ k : Fin K, zs.2 k * L zs.1 k = 0))
      ⊆ (Finset.univ.filter (fun zs : (Fin n → F) × (Fin K → F) => zs.1 ∈ Z₀))
        ∪ (Finset.univ.filter (fun zs : (Fin n → F) × (Fin K → F) =>
            zs.1 ∉ Z₀ ∧ Cc + ∑ k : Fin K, zs.2 k * L zs.1 k = 0)) := by
    intro zs hzs
    rw [Finset.mem_filter] at hzs
    by_cases hz : zs.1 ∈ Z₀
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz, hzs.2⟩)
  -- First piece: `|Z₀| · |F|^K`.
  have hcard₁ : (Finset.univ.filter (fun zs : (Fin n → F) × (Fin K → F) => zs.1 ∈ Z₀)).card
      = Z₀.card * Fintype.card F ^ K := by
    rw [show (Finset.univ.filter (fun zs : (Fin n → F) × (Fin K → F) => zs.1 ∈ Z₀))
        = Z₀ ×ˢ (Finset.univ : Finset (Fin K → F)) from by
      ext zs; simp [Finset.mem_product]]
    rw [Finset.card_product]
    simp [Finset.card_univ]
  -- Second piece: the affine pinning — inject by forgetting the (pinned) `k₀`-coordinate.
  have hcard₂ : (Finset.univ.filter (fun zs : (Fin n → F) × (Fin K → F) =>
      zs.1 ∉ Z₀ ∧ Cc + ∑ k : Fin K, zs.2 k * L zs.1 k = 0)).card
      ≤ Fintype.card F ^ n * Fintype.card F ^ (K - 1) := by
    have hinj := Finset.card_le_card_of_injOn
      (f := fun zs : (Fin n → F) × (Fin K → F) =>
        ((zs.1, fun j : {j : Fin K // j ≠ k₀} => zs.2 j.val) :
          (Fin n → F) × ({j : Fin K // j ≠ k₀} → F)))
      (s := Finset.univ.filter (fun zs : (Fin n → F) × (Fin K → F) =>
        zs.1 ∉ Z₀ ∧ Cc + ∑ k : Fin K, zs.2 k * L zs.1 k = 0))
      (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
      (by
        rintro ⟨z, sc⟩ hzs ⟨z', sc'⟩ hzs' heq
        rw [Finset.mem_coe, Finset.mem_filter] at hzs hzs'
        obtain ⟨-, hz, hclaim⟩ := hzs
        obtain ⟨-, hz', hclaim'⟩ := hzs'
        have hzeq : z = z' := congrArg Prod.fst heq
        subst hzeq
        have hrest : (fun j : {j : Fin K // j ≠ k₀} => sc j.val)
            = (fun j : {j : Fin K // j ≠ k₀} => sc' j.val) := congrArg Prod.snd heq
        -- The non-`k₀` coordinates agree.
        have hrest' : ∀ j : Fin K, j ≠ k₀ → sc j = sc' j := fun j hj =>
          congrFun hrest ⟨j, hj⟩
        -- The `k₀` coordinate is pinned by the claim equation (nonzero coefficient).
        have hLk₀ : L z k₀ ≠ 0 := by
          intro h0
          exact hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩)
        have hsplit : ∀ sc'' : Fin K → F,
            ∑ k : Fin K, sc'' k * L z k
              = sc'' k₀ * L z k₀ + ∑ k ∈ Finset.univ.erase k₀, sc'' k * L z k := by
          intro sc''
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k₀)]
        have hsum_eq : ∑ k ∈ Finset.univ.erase k₀, sc k * L z k
            = ∑ k ∈ Finset.univ.erase k₀, sc' k * L z k := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [hrest' j (Finset.ne_of_mem_erase hj)]
        have hpin : sc k₀ * L z k₀ = sc' k₀ * L z k₀ := by
          have h1 := hclaim
          have h2 := hclaim'
          rw [hsplit sc] at h1
          rw [hsplit sc'] at h2
          have h12 := h1.trans h2.symm
          have h3 : sc k₀ * L z k₀ + ∑ k ∈ Finset.univ.erase k₀, sc k * L z k
              = sc' k₀ * L z k₀ + ∑ k ∈ Finset.univ.erase k₀, sc' k * L z k :=
            add_left_cancel h12
          rw [hsum_eq] at h3
          exact add_right_cancel h3
        have hk₀ : sc k₀ = sc' k₀ := mul_right_cancel₀ hLk₀ hpin
        refine Prod.ext rfl ?_
        funext j
        by_cases hj : j = k₀
        · rw [hj]; exact hk₀
        · exact hrest' j hj)
    refine le_trans hinj ?_
    rw [Finset.card_univ, Fintype.card_prod]
    have hsub : Fintype.card {j : Fin K // j ≠ k₀} = K - 1 := by
      rw [Fintype.card_subtype_compl]
      simp
    rw [show Fintype.card ((Fin n → F)) = Fintype.card F ^ n by
      simp [Fintype.card_fun]]
    rw [show Fintype.card ({j : Fin K // j ≠ k₀} → F) = Fintype.card F ^ (K - 1) by
      rw [Fintype.card_fun, hsub]]
  -- Assemble: `card ≤ card₁ + card₂`, then multiply through by `|F|`.
  have hzcount := mleCoeff_zeros_card_mul_le hSigns (g k₀) u₀ hg
  calc (Finset.univ.filter (fun zs : (Fin n → F) × (Fin K → F) =>
        Cc + ∑ k : Fin K, zs.2 k * L zs.1 k = 0)).card * Fintype.card F
      ≤ ((Finset.univ.filter (fun zs : (Fin n → F) × (Fin K → F) => zs.1 ∈ Z₀)).card
          + (Finset.univ.filter (fun zs : (Fin n → F) × (Fin K → F) =>
              zs.1 ∉ Z₀ ∧ Cc + ∑ k : Fin K, zs.2 k * L zs.1 k = 0)).card) * Fintype.card F := by
        gcongr
        exact le_trans (Finset.card_le_card hsubset) (Finset.card_union_le _ _)
    _ ≤ (Z₀.card * Fintype.card F ^ K
          + Fintype.card F ^ n * Fintype.card F ^ (K - 1)) * Fintype.card F :=
        Nat.mul_le_mul_right _ (add_le_add (le_of_eq hcard₁) hcard₂)
    _ = (Z₀.card * Fintype.card F) * Fintype.card F ^ K
          + Fintype.card F ^ n * (Fintype.card F ^ (K - 1) * Fintype.card F) := by ring
    _ ≤ (n * Fintype.card F ^ n) * Fintype.card F ^ K
          + Fintype.card F ^ n * (Fintype.card F ^ (K - 1) * Fintype.card F) := by
        gcongr
    _ = (n + 1) * Fintype.card F ^ (n + K) := by
        have hpow : Fintype.card F ^ (K - 1) * Fintype.card F = Fintype.card F ^ K := by
          rw [← pow_succ]
          congr 1
          have hK : 0 < K := k₀.pos
          omega
        rw [hpow, pow_add]
        ring

end BatchingCount

end Logup

/- Axiom audit. -/
#print axioms Logup.mleCoeff_zeros_card_mul_le
#print axioms Logup.batching_zero_card_mul_le

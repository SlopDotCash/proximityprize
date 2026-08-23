/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAJumpValueExact
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Stage B (#357): the smooth-domain jump value, UNCONDITIONAL

`MCAJumpValueExact.lean` pinned `ε_mca(RS[F,D,n−2], 1/n) = n/q` conditional on the
per-point nondegeneracy `Z_j(b₂) ≠ Z_j(b₁)`. This file discharges that condition for
subgroup evaluation domains via the `X^n − 1` derivative identity:

* `prod_erase_eq_deriv` — for `b ∈ μ_n`:  `∏_{t ∈ μ_n ∖ {b}} (b − t) = n·b^{n−1}`
  (differentiate `X^n − 1 = ∏ (X − t)` at the root `b`);
* `vanishWord_split` — the index-level factorization
  `Z_j(b)·(x_b − x_j)·(x_b − x_{b'}) = n·x_b^{n−1}` for a domain enumerating `μ_n`;
* `nondegeneracy_of_key` — the closed form: `Z_j(b₂) = Z_j(b₁)` forces
  `x_j·(x_{b₁} + x_{b₂}) = x_{b₁}² + x_{b₂}²`; so the **key inequality**
  `x_j·(x_{b₁}+x_{b₂}) ≠ x_{b₁}²+x_{b₂}²` yields nondegeneracy;
* `nondegeneracy_antipodal` — with the antipodal choice `x_{b₂} = −x_{b₁}` the key
  inequality is vacuous in odd characteristic: `0 = x_j·0 ≠ 2x_{b₁}²`;
* **`epsMCA_rs_smooth_jump_eq`** — for every subgroup domain (enumerating `μ_n`, `n = |ι|`,
  primitive root supplied, `(n : F) ≠ 0`, `(2 : F) ≠ 0`) containing an antipodal pair:

    `ε_mca(RS[F, μ_n, n−2], 1/n) = n/q`  **unconditionally**.

Every even-order multiplicative subgroup contains antipodal pairs (`−1 ∈ μ_n` and
`−x = (−1)·x`), so this covers all smooth (2-power) evaluation domains in odd
characteristic — the production setting. Combined with the family theorem, the threshold
function of high-rate smooth RS is now fully determined on the whole band:
`δ*(RS[F, μ_n, n−2], ε*) = 1/n` for every `ε* ∈ [1/q, n/q)`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- Issue #357 (Stage B registration); `MCAJumpValueExact.lean`.
-/

set_option linter.unusedSectionVars false

open Polynomial
open scoped NNReal ENNReal
open ProximityGap.MCAJumpValueExact

namespace ProximityGap.MCASmoothJumpUnconditional

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The derivative identity -/

/-- For a root of unity `b ∈ μ_n`:  `∏_{t ∈ μ_n ∖ {b}} (b − t) = n·b^{n−1}`. -/
theorem prod_erase_eq_deriv {n : ℕ} (hpos : 0 < n) {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    {b : F} (hb : b ∈ nthRootsFinset n (1 : F)) :
    ∏ t ∈ (nthRootsFinset n (1 : F)).erase b, (b - t) = (n : F) * b ^ (n - 1) := by
  have hfac : (X ^ n - 1 : F[X])
      = (X - C b) * ∏ t ∈ (nthRootsFinset n (1 : F)).erase b, (X - C t) := by
    rw [X_pow_sub_one_eq_prod hpos hζ, ← Finset.mul_prod_erase _ _ hb]
  have hder := congrArg Polynomial.derivative hfac
  rw [Polynomial.derivative_sub, Polynomial.derivative_one, Polynomial.derivative_X_pow,
    Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
    Polynomial.derivative_C] at hder
  have hev := congrArg (Polynomial.eval b) hder
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
    Polynomial.eval_natCast, sub_zero, sub_self, zero_mul, one_mul, zero_add,
    Polynomial.eval_prod] at hev
  rw [add_zero] at hev
  exact hev.symm

/-! ## The index-level factorization -/

section Smooth

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable (domain : ι ↪ F)

/-- Domain values are roots of unity (under the enumeration hypothesis). -/
theorem domain_mem_roots
    (himg : Finset.univ.image domain = nthRootsFinset (Fintype.card ι) (1 : F)) (i : ι) :
    domain i ∈ nthRootsFinset (Fintype.card ι) (1 : F) := by
  rw [← himg]
  exact Finset.mem_image_of_mem domain (Finset.mem_univ i)

/-- Domain values are nonzero. -/
theorem domain_ne_zero
    (himg : Finset.univ.image domain = nthRootsFinset (Fintype.card ι) (1 : F)) (i : ι) :
    domain i ≠ 0 := by
  intro h0
  have hmem := domain_mem_roots domain himg i
  rw [mem_nthRootsFinset Fintype.card_pos (1 : F), h0,
    zero_pow Fintype.card_pos.ne'] at hmem
  exact zero_ne_one hmem

/-- The full-erasure product at the index level equals the derivative value. -/
theorem index_prod_erase
    (himg : Finset.univ.image domain = nthRootsFinset (Fintype.card ι) (1 : F))
    {ζ : F} (hζ : IsPrimitiveRoot ζ (Fintype.card ι)) (b : ι) :
    ∏ t ∈ Finset.univ.erase b, (domain b - domain t)
      = ((Fintype.card ι : ℕ) : F) * domain b ^ (Fintype.card ι - 1) := by
  have himage : (Finset.univ.erase b).image domain
      = (nthRootsFinset (Fintype.card ι) (1 : F)).erase (domain b) := by
    rw [← himg, Finset.image_erase domain.injective]
  have hprod : ∏ t ∈ Finset.univ.erase b, (domain b - domain t)
      = ∏ y ∈ (nthRootsFinset (Fintype.card ι) (1 : F)).erase (domain b),
          (domain b - y) := by
    rw [← himage, Finset.prod_image (fun x _ y _ h => domain.injective h)]
  rw [hprod]
  exact prod_erase_eq_deriv Fintype.card_pos hζ (domain_mem_roots domain himg b)

/-- The three-factor split: `Z_j(b)·(x_b − x_j)·(x_b − x_{b'}) = n·x_b^{n−1}` whenever
`b, b', j` are pairwise distinct. -/
theorem vanishWord_split
    (himg : Finset.univ.image domain = nthRootsFinset (Fintype.card ι) (1 : F))
    {ζ : F} (hζ : IsPrimitiveRoot ζ (Fintype.card ι))
    {b b' j : ι} (hbb : b ≠ b') (hjb : j ≠ b) (hjb' : j ≠ b') :
    vanishWord domain (Tset j b b') b * (domain b - domain j) * (domain b - domain b')
      = ((Fintype.card ι : ℕ) : F) * domain b ^ (Fintype.card ι - 1) := by
  have hj_mem : j ∈ Finset.univ.erase b :=
    Finset.mem_erase.mpr ⟨hjb, Finset.mem_univ j⟩
  have hb'_mem : b' ∈ (Finset.univ.erase b).erase j :=
    Finset.mem_erase.mpr ⟨(fun h => hjb' h.symm),
      Finset.mem_erase.mpr ⟨hbb.symm, Finset.mem_univ b'⟩⟩
  have hsetEq : ((Finset.univ.erase b).erase j).erase b' = Tset j b b' := by
    ext i
    rw [mem_Tset]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    tauto
  have h1 := Finset.mul_prod_erase (Finset.univ.erase b)
    (fun t => domain b - domain t) hj_mem
  have h2 := Finset.mul_prod_erase ((Finset.univ.erase b).erase j)
    (fun t => domain b - domain t) hb'_mem
  rw [← index_prod_erase domain himg hζ b, ← h1, ← h2, hsetEq]
  show vanishWord domain (Tset j b b') b * (domain b - domain j) * (domain b - domain b')
    = (domain b - domain j) * ((domain b - domain b')
        * ∏ t ∈ Tset j b b', (domain b - domain t))
  rw [show vanishWord domain (Tset j b b') b
      = ∏ t ∈ Tset j b b', (domain b - domain t) from rfl]
  ring

/-! ## Nondegeneracy from the closed form -/

/-- **The closed form.** If `x_j·(x_{b₁}+x_{b₂}) ≠ x_{b₁}² + x_{b₂}²` then the per-point
nondegeneracy `Z_j(b₂) ≠ Z_j(b₁)` holds. -/
theorem nondegeneracy_of_key
    (himg : Finset.univ.image domain = nthRootsFinset (Fintype.card ι) (1 : F))
    {ζ : F} (hζ : IsPrimitiveRoot ζ (Fintype.card ι))
    (hnF : ((Fintype.card ι : ℕ) : F) ≠ 0)
    {b₁ b₂ j : ι} (hb : b₁ ≠ b₂) (hj1 : j ≠ b₁) (hj2 : j ≠ b₂)
    (hkey : domain j * (domain b₁ + domain b₂) ≠ domain b₁ ^ 2 + domain b₂ ^ 2) :
    vanishWord domain (Tset j b₁ b₂) b₂ ≠ vanishWord domain (Tset j b₁ b₂) b₁ := by
  intro hcon
  set A := domain b₁ with hA
  set B := domain b₂ with hB
  set J := domain j with hJ
  set Z := vanishWord domain (Tset j b₁ b₂) b₁ with hZ
  set n := Fintype.card ι with hn
  -- the two split identities (note `Tset j b₂ b₁` versus `Tset j b₁ b₂`: same set)
  have hsame : Tset j b₂ b₁ = Tset j b₁ b₂ := by
    ext i
    rw [mem_Tset, mem_Tset]
    tauto
  have hs1 : Z * (A - J) * (A - B)
      = ((n : ℕ) : F) * A ^ (n - 1) :=
    vanishWord_split domain himg hζ hb hj1 hj2
  have hs2 : Z * (B - J) * (B - A)
      = ((n : ℕ) : F) * B ^ (n - 1) := by
    have h := vanishWord_split domain himg hζ hb.symm hj2 hj1
    rw [hsame, hcon] at h
    exact h
  have hnpos : 0 < n := Fintype.card_pos
  -- multiply by the base points: A^n = B^n = 1
  have hApow : A ^ n = 1 := by
    have := domain_mem_roots domain himg b₁
    rwa [mem_nthRootsFinset Fintype.card_pos (1 : F)] at this
  have hBpow : B ^ n = 1 := by
    have := domain_mem_roots domain himg b₂
    rwa [mem_nthRootsFinset Fintype.card_pos (1 : F)] at this
  have hA1 : A * A ^ (n - 1) = 1 := by
    rw [← pow_succ']
    rw [show n - 1 + 1 = n by omega]
    exact hApow
  have hB1 : B * B ^ (n - 1) = 1 := by
    rw [← pow_succ']
    rw [show n - 1 + 1 = n by omega]
    exact hBpow
  -- the two scaled identities
  have ht1 : Z * A * (A - J) * (A - B) = ((n : ℕ) : F) := by
    calc Z * A * (A - J) * (A - B) = A * (Z * (A - J) * (A - B)) := by ring
      _ = A * (((n : ℕ) : F) * A ^ (n - 1)) := by rw [hs1]
      _ = ((n : ℕ) : F) * (A * A ^ (n - 1)) := by ring
      _ = ((n : ℕ) : F) := by rw [hA1, mul_one]
  have ht2 : Z * B * (B - J) * (B - A) = ((n : ℕ) : F) := by
    calc Z * B * (B - J) * (B - A) = B * (Z * (B - J) * (B - A)) := by ring
      _ = B * (((n : ℕ) : F) * B ^ (n - 1)) := by rw [hs2]
      _ = ((n : ℕ) : F) * (B * B ^ (n - 1)) := by ring
      _ = ((n : ℕ) : F) := by rw [hB1, mul_one]
  -- subtract and factor
  have hZ0 : Z ≠ 0 := vanishWord_ne_zero domain (fun h => (mem_Tset.mp h).2.1 rfl)
  have hAB : A - B ≠ 0 := sub_ne_zero.mpr (fun h => hb (domain.injective h))
  have hdiff : Z * (A - B) * (A * (A - J) + B * (B - J)) = 0 := by
    linear_combination ht1 - ht2
  rcases mul_eq_zero.mp hdiff with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hZ0 h'
    · exact hAB h'
  · apply hkey
    rw [hJ, hA, hB]
    linear_combination -h

/-- **The antipodal discharge.** With `x_{b₂} = −x_{b₁}` and `(2 : F) ≠ 0`, the key
inequality holds vacuously at every third point. -/
theorem nondegeneracy_antipodal
    (himg : Finset.univ.image domain = nthRootsFinset (Fintype.card ι) (1 : F))
    {ζ : F} (hζ : IsPrimitiveRoot ζ (Fintype.card ι))
    (hnF : ((Fintype.card ι : ℕ) : F) ≠ 0) (h2 : (2 : F) ≠ 0)
    {b₁ b₂ : ι} (hb : b₁ ≠ b₂) (hanti : domain b₂ = -domain b₁)
    {j : ι} (hj1 : j ≠ b₁) (hj2 : j ≠ b₂) :
    vanishWord domain (Tset j b₁ b₂) b₂ ≠ vanishWord domain (Tset j b₁ b₂) b₁ := by
  apply nondegeneracy_of_key domain himg hζ hnF hb hj1 hj2
  rw [hanti]
  intro hcon
  have hA0 : domain b₁ ≠ 0 := domain_ne_zero domain himg b₁
  have h2A : (2 : F) * domain b₁ ^ 2 = 0 := by linear_combination -hcon
  rcases mul_eq_zero.mp h2A with h | h
  · exact h2 h
  · exact hA0 (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h)

/-! ## The unconditional smooth jump value -/

open ProximityGap.MCAAntichainEngine in
/-- **THE UNCONDITIONAL SMOOTH JUMP VALUE.** For every subgroup evaluation domain
(enumerating `μ_n`, primitive root supplied, `(n : F) ≠ 0`, odd characteristic) with an
antipodal marked pair:

  `ε_mca(RS[F, μ_n, n−2], 1/n) = n/q`  **exactly, unconditionally**.

With the family theorem, `δ*(RS[F, μ_n, n−2], ε*) = 1/n` for every `ε* ∈ [1/q, n/q)`. -/
theorem epsMCA_rs_smooth_jump_eq
    (himg : Finset.univ.image domain = nthRootsFinset (Fintype.card ι) (1 : F))
    {ζ : F} (hζ : IsPrimitiveRoot ζ (Fintype.card ι))
    (hn : 4 ≤ Fintype.card ι)
    (hnF : ((Fintype.card ι : ℕ) : F) ≠ 0) (h2 : (2 : F) ≠ 0)
    {b₁ b₂ : ι} (hb : b₁ ≠ b₂) (hanti : domain b₂ = -domain b₁) :
    epsMCA (F := F) (A := F)
        (ReedSolomon.code domain (Fintype.card ι - 2) : Set (ι → F))
        (1 / (Fintype.card ι : ℝ≥0))
      = ((Fintype.card ι : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_rs_jump_eq domain hn hb
    (fun j hj1 hj2 => nondegeneracy_antipodal domain himg hζ hnF h2 hb hanti hj1 hj2)

end Smooth

/-! ## Source audit -/

#print axioms prod_erase_eq_deriv
#print axioms vanishWord_split
#print axioms nondegeneracy_of_key
#print axioms nondegeneracy_antipodal
#print axioms epsMCA_rs_smooth_jump_eq

end ProximityGap.MCASmoothJumpUnconditional

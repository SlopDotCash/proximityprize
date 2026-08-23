/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma24Finish
import ArkLib.Data.CodingTheory.GMMDS.LovettBlockSpan
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Lovett's GM-MDS proof: the meet-block span / degree-window facts for Lemma 2.4 (#389)

This file supplies the algebraic "block-dimension" facts behind Lovett's Lemma 2.4
(arXiv:1803.02523, p.8–9), working over the polynomial ring `R = F[a] = MvPolynomial (Fin n) F`.

For a vector `v` of weight `|v| ≤ k`, the **meet block**
`{ pFam v s = pVanish v · xˢ : s < k − |v| }` spans, inside `R[X]`, **all** multiples of
`pVanish v` of `x`-degree `< k`:

> `span_R { pFam v s : s < k − |v| } = pVanish v · degreeLT R (k − |v|)`,

because `pVanish v` is monic of degree `|v|` and `{xˢ : s < k − |v|}` spans `degreeLT R (k−|v|)`
(`degreeLT_eq_span_X_pow`).  The two load-bearing consequences used in Lemma 2.4 are:

* `pFam_mem_span_meetBlock` — any `pVanish v`-multiple `pVanish v · q` with
  `natDegree (pVanish v · q) < k` lies in `span_R { pFam v s : s < k − |v| }`;
* `pFamUnion_I_mem_span_meetBlock` — hence (using `pVanish (v_I) ∣ pVanish vᵢ`,
  `pVanish_vMeet_dvd_mem`, and the tight degree bound `|vᵢ| + e < k`) **every** `I`-block element
  `pFam vᵢ e` (`i ∈ I`, `e < k − |vᵢ|`) lies in the span of the single **meet block**
  `{ pFam (v_I) s : s < k − |v_I| }`.

This is the *forward* span inclusion `span (I-block) ⊆ span (meet block)` of Lemma 2.4 — the easy
half of the equal-span transfer (`Lemma24SpanTransfer`).  It is proven unconditionally over the
ring; the reverse inclusion (meet block ⊆ span of the `I`-block) is the dimension-counting half
that additionally needs the `I`-subsystem independence.

Issue #389.
-/

open Polynomial Finset

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n : ℕ}

/-- The **meet block** family for a vector `v`: `{ pFam v s : s < k − |v| }`, indexed by
`Fin (k − |v|)`.  (For `v = v_I` this is the single block that replaces the whole `I`-block in
Lovett's meet-replacement system.) -/
noncomputable def meetBlock (v : Fin n → ℕ) (k : ℕ) : Fin (k - vAbs v) → (MvPolynomial (Fin n) F)[X] :=
  fun s => pFam (F := F) v (s : ℕ)

/-- **The meet block spans every degree-`< k` multiple of `pVanish v`.**  If `q : R[X]` and the
product `pVanish v · q` has `x`-degree `< k`, then `pVanish v · q` lies in the span of
`{ pFam v s : s < k − |v| }`.  (Write `q` in the monomial basis of `degreeLT R (k − |v|)`; each
`pVanish v · xˢ` is `pFam v s`.) -/
theorem pFam_mem_span_meetBlock {v : Fin n → ℕ} {k : ℕ} (q : (MvPolynomial (Fin n) F)[X])
    (hdeg : (pVanish (F := F) v * q).natDegree < k) (hq0 : q ≠ 0) :
    pVanish (F := F) v * q ∈ Submodule.span (MvPolynomial (Fin n) F) (Set.range (meetBlock (F := F) v k)) := by
  classical
  -- bound deg q < k - |v|
  have hpv : pVanish (F := F) v ≠ 0 := (pVanish_monic v).ne_zero
  have hdegmul : (pVanish (F := F) v * q).natDegree = vAbs v + q.natDegree := by
    rw [natDegree_mul hpv hq0, pVanish_natDegree]
  have hqdeg : q.natDegree < k - vAbs v := by omega
  -- q ∈ degreeLT R (k - |v|) = span {x^s : s < k - |v|}
  have hqmem : q ∈ Polynomial.degreeLT (MvPolynomial (Fin n) F) (k - vAbs v) := by
    rw [Polynomial.mem_degreeLT, ← Polynomial.natDegree_lt_iff_degree_lt hq0]
    exact hqdeg
  rw [Polynomial.degreeLT_eq_span_X_pow] at hqmem
  -- now push through multiplication by pVanish v
  -- write q as a span-combination of monomials, multiply, identify with meetBlock entries
  refine Submodule.span_induction
    (p := fun x _ => pVanish (F := F) v * x ∈
      Submodule.span (MvPolynomial (Fin n) F) (Set.range (meetBlock (F := F) v k)))
    ?_ ?_ ?_ ?_ hqmem
  · -- generators: x^s with s < k - |v|
    rintro x hx
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    -- pVanish v * x^s = pFam v s = meetBlock v k ⟨s, _⟩
    have heq : pVanish (F := F) v * X ^ s = meetBlock (F := F) v k ⟨s, hs⟩ := by
      simp only [meetBlock, pFam]
    rw [heq]
    exact Submodule.subset_span ⟨⟨s, hs⟩, rfl⟩
  · -- zero
    simp
  · -- add
    intro x y _ _ hx hy
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  · -- smul
    intro a x _ hx
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ a hx

/-- **Every `I`-block element lies in the span of the meet block.**  For a tight meet over `I`
(`v_I = ⋀_{i∈I} vᵢ`), any member `i ∈ I` and exponent `e < k − |vᵢ|`: the family element
`pFam vᵢ e` is a `pVanish v_I`-multiple (`pVanish_vMeet_dvd_mem`) of `x`-degree
`|vᵢ| + e < k`, hence lies in `span { pFam v_I s : s < k − |v_I| }`. -/
theorem pFamUnion_I_mem_span_meetBlock {m : ℕ} {V : Fin m → (Fin n → ℕ)} {k : ℕ}
    {I : Finset (Fin m)} (hI : I.Nonempty) {i : Fin m} (hi : i ∈ I)
    (hk : vAbs (V i) ≤ k) (e : ℕ) (he : e < k - vAbs (V i)) :
    pFam (F := F) (V i) e ∈
      Submodule.span (MvPolynomial (Fin n) F)
        (Set.range (meetBlock (F := F) (vMeet V I hI) k)) := by
  classical
  set vI := vMeet V I hI with hvI
  -- pVanish vI ∣ pVanish (V i)
  obtain ⟨g, hg⟩ := pVanish_vMeet_dvd_mem (F := F) hI hi
  -- pFam (V i) e = pVanish (V i) * x^e = pVanish vI * (g * x^e)
  have hpFam : pFam (F := F) (V i) e = pVanish (F := F) vI * (g * X ^ e) := by
    rw [pFam, hg]; ring
  -- g * x^e ≠ 0:  g ≠ 0 since pVanish (V i) ≠ 0
  have hpvi : pVanish (F := F) (V i) ≠ 0 := (pVanish_monic (V i)).ne_zero
  have hg0 : g ≠ 0 := by
    rintro rfl; rw [mul_zero] at hg; exact hpvi hg
  have hge0 : g * X ^ e ≠ 0 := mul_ne_zero hg0 (pow_ne_zero e X_ne_zero)
  -- degree bound
  have hdeg : (pVanish (F := F) vI * (g * X ^ e)).natDegree < k := by
    rw [← hpFam, pFam_natDegree]
    omega
  rw [hpFam]
  exact pFam_mem_span_meetBlock (g * X ^ e) hdeg hge0

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.pFam_mem_span_meetBlock
#print axioms ArkLib.GMMDS.pFamUnion_I_mem_span_meetBlock

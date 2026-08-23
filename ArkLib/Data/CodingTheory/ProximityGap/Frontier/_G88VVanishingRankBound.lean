/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# G88V: the vanishing rank bound — coverage costs dimension, provably

Companion to G87V (`_G87CoverageDivisibility.lean`). The census-rank probe
(`scripts/probes/probe_466_g87v_census_rank.py`, results
`scripts/probes/_out_466_g87v_census_rank_n16.txt`) measured, at every accessible cell
(n = 16; p ∈ {97, 193, 257}; every root t of x^n − 1 mod p):

* common coverage of the full support-six census at an embedding of multiplicative order
  `m` is exactly `m/2` (primitive `m = n` ⟹ coverage 1);
* the census rank mod `p` is EXACTLY `n − coverage` in every cell;
* the rank over ℚ equals the mod-`p` rank, +1 exactly at primitive-order embeddings
  (where it reaches full rank `n`).

So full-rank census families exist exactly where coverage is trivial, and coverage grows
only at low-order (non-prize-shaped) embeddings by shedding rank in exact lockstep. This
file proves the PROVABLE half of that law — saturated with equality by the data:

* `rank_le_of_rows_vanishing` — **the rank fence**: over any field, if every row of an
  `m × d` matrix is annihilated by the `s` Vandermonde functionals of pairwise-distinct
  nodes `t : Fin s → K` (with `s ≤ d`), then `M.rank + s ≤ d`. Proof: the rows lie in the
  kernel of the node-evaluation map, which is surjective onto `K^s` because its
  restriction to the first `s` power-coordinates is the invertible square Vandermonde;
  rank–nullity does the rest.
* `rank_zmod_le_of_int_rows_vanishing` — the census form: an integer matrix whose rows
  all vanish mod `p` at `s` roots pairwise distinct mod `p` has mod-`p` rank ≤ `d − s`.

**Reading for the G82 seam.** Combined with G87V/G86H: a family with common coverage `s`
is confined mod `p` to a codimension-`s` subspace (this file); any full-rank `d × d`
subfamily has determinant divisible by `p^s` (G87V) and squared-bounded by `6^d` (G86H),
hence `s·log p ≤ (d/2)·log 6`. The measured saturation `rank_p = n − coverage` means the
census realizes this fence EXACTLY; coverage at accessible cells is bought only by
periodicity (low-order embeddings), which is unavailable at the prize cell (the embedding
has exact order `n` by construction).

**Honest scope.** The equality `rank_p = n − coverage` and the `coverage = ord/2` law are
measured, not proven (properties of the support-six census data); only the `≤` fence is a
theorem here. No bound on `M(μ_n)`; CORE remains OPEN / ON-BGK. Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G88VVanishingRankBound

open Finset Matrix

variable {K : Type} [Field K]

/-- **The rank fence.** If every row of `M : Matrix (Fin m) (Fin d) K` is annihilated by
the Vandermonde functionals `w ↦ Σ_j w_j · t_k^j` of `s ≤ d` pairwise-distinct nodes,
then `M.rank + s ≤ d`: common coverage costs dimension, one for one. -/
theorem rank_le_of_rows_vanishing {m d s : ℕ} (hs : s ≤ d)
    (M : Matrix (Fin m) (Fin d) K) (t : Fin s → K)
    (hdist : Function.Injective t)
    (hvan : ∀ i k, ∑ j : Fin d, M i j * t k ^ (j : ℕ) = 0) :
    M.rank + s ≤ d := by
  classical
  set V : Matrix (Fin s) (Fin d) K := Matrix.of (fun k j => t k ^ (j : ℕ)) with hV
  -- rows of M are killed by V: V * Mᵀ = 0
  have hVM : V * Mᵀ = 0 := by
    ext k i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, hV,
      Matrix.of_apply]
    calc ∑ j : Fin d, t k ^ (j : ℕ) * M i j = ∑ j : Fin d, M i j * t k ^ (j : ℕ) :=
          Finset.sum_congr rfl fun j _ => mul_comm _ _
      _ = 0 := hvan i k
  -- hence the row space of M sits inside ker (V.mulVecLin)
  have hspan : LinearMap.range Mᵀ.mulVecLin ≤ LinearMap.ker V.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hVM,
      Matrix.zero_mulVec]
  -- V.mulVecLin is surjective: its restriction to the first s power-coordinates is the
  -- invertible square Vandermonde
  have hsurj : Function.Surjective V.mulVecLin := by
    intro y
    have hdet : (Matrix.vandermonde t).det ≠ 0 :=
      Matrix.det_vandermonde_ne_zero_iff.mpr hdist
    have hunit : IsUnit (Matrix.vandermonde t) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hdet)
    obtain ⟨x, hx⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hunit) y
    refine ⟨fun j => if h : (j : ℕ) < s then x ⟨(j : ℕ), h⟩ else 0, ?_⟩
    funext k
    have hWx : ∑ a : Fin s, t k ^ (a : ℕ) * x a = y k := by
      have h1 := congrFun hx k
      simpa [Matrix.mulVec, Matrix.vandermonde, dotProduct] using h1
    -- reindex the padded sum through ℕ
    set f : ℕ → K := fun jn => if h : jn < s then t k ^ jn * x ⟨jn, h⟩ else 0 with hf
    have hstep1 : (V.mulVecLin fun j : Fin d =>
        if h : (j : ℕ) < s then x ⟨(j : ℕ), h⟩ else 0) k = ∑ j : Fin d, f (j : ℕ) := by
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hV, Matrix.of_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : (j : ℕ) < s <;> simp [hf, h]
    have hstep2 : ∑ j : Fin d, f (j : ℕ) = ∑ jn ∈ Finset.range d, f jn :=
      Fin.sum_univ_eq_sum_range f d
    have hstep3 : ∑ jn ∈ Finset.range d, f jn = ∑ jn ∈ Finset.range s, f jn := by
      refine (Finset.sum_subset (fun x hx => ?_) (fun jn _ hjn => ?_)).symm
      · rw [Finset.mem_range] at hx ⊢
        omega
      have : ¬ jn < s := by simpa using hjn
      simp [hf, this]
    have hstep4 : ∑ jn ∈ Finset.range s, f jn = ∑ a : Fin s, t k ^ (a : ℕ) * x a := by
      rw [← Fin.sum_univ_eq_sum_range f s]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [hf, a.isLt]
    rw [hstep1, hstep2, hstep3, hstep4, hWx]
  -- rank–nullity converts surjectivity into the kernel dimension
  have hrn := LinearMap.finrank_range_add_finrank_ker V.mulVecLin
  have hrange : Module.finrank K (LinearMap.range V.mulVecLin) = s := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp
  have hdom : Module.finrank K (Fin d → K) = d := by simp
  have hker : Module.finrank K (LinearMap.ker V.mulVecLin) + s = d := by omega
  -- the row space is inside the kernel; transpose rank equals rank over a field
  have hle : Mᵀ.rank ≤ Module.finrank K (LinearMap.ker V.mulVecLin) :=
    Submodule.finrank_mono hspan
  have htr : Mᵀ.rank = M.rank := Matrix.rank_transpose M
  omega

/-- **The census form**: an integer matrix whose rows all vanish mod `p` at `s` roots
pairwise distinct mod `p` has mod-`p` rank at most `d − s` (stated addition-free). With
G87V (`p^s ∣ det` for square full-rank families) and G86H (Hadamard), this is the third
kernel-checked face of the coverage fence, and the one the census-rank probe measures to
be EXACTLY saturated (`rank_p = n − coverage` at every accessible cell). -/
theorem rank_zmod_le_of_int_rows_vanishing {p : ℕ} (hp : p.Prime) {m d s : ℕ} (hs : s ≤ d)
    (M : Matrix (Fin m) (Fin d) ℤ) (t : Fin s → ℤ)
    (hdist : ∀ k l, k ≠ l → ¬ (p : ℤ) ∣ (t k - t l))
    (hvan : ∀ i k, (p : ℤ) ∣ ∑ j : Fin d, M i j * t k ^ (j : ℕ)) :
    (M.map (Int.cast : ℤ → ZMod p)).rank + s ≤ d := by
  haveI := Fact.mk hp
  refine rank_le_of_rows_vanishing hs _ (fun k => ((t k : ℤ) : ZMod p)) ?_ ?_
  · intro k l hkl
    by_contra hne
    have hd := hdist k l (by rintro rfl; exact hne rfl)
    apply hd
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [sub_eq_zero]
    exact hkl
  · intro i k
    have hv := hvan i k
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hv
    push_cast at hv
    simpa [Matrix.map_apply] using hv

end ArkLib.ProximityGap.Frontier.G88VVanishingRankBound

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G88VVanishingRankBound.rank_le_of_rows_vanishing
#print axioms
  ArkLib.ProximityGap.Frontier.G88VVanishingRankBound.rank_zmod_le_of_int_rows_vanishing

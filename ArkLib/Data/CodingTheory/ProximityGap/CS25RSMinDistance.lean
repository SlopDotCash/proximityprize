/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSCoveredFraction
import ArkLib.Data.CodingTheory.CodeGeometry
import ArkLib.Data.CodingTheory.ProximityGap.CS25CoveredFractionUniqueDecoding

/-!
# Reed–Solomon minimum distance (Singleton/MDS) and unique-decoding covered fraction (#82)

`rsCodeFinset_hammingDist_ge`: distinct degree-`<k` Reed–Solomon codewords differ in at least
`n − (k−1)` positions (the Singleton/MDS bound) — proved from the roots-in-domain bound
`card_domain_roots_le` (a nonzero degree-`<k` polynomial vanishes at `≤ k−1` of the distinct
evaluation points) via `CodeGeometry.agree_add_hammingDist`.

`rs_covered_count_ge_unique_decoding`: instantiating the unique-decoding covered fraction
(`covered_count_ge_of_minDist`) at the RS code gives, for `2r < n−(k−1)`, `|RS|·V ≤ |close|`.
All `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem card_domain_roots_le (domain : ι ↪ F) (q : Polynomial F) (hq : q ≠ 0) :
    (univ.filter (fun i => q.eval (domain i) = 0)).card ≤ q.natDegree := by
  calc (univ.filter (fun i => q.eval (domain i) = 0)).card
      = ((univ.filter (fun i => q.eval (domain i) = 0)).image (fun i => domain i)).card :=
        (Finset.card_image_of_injective _ domain.injective).symm
    _ ≤ q.roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        simp only [Multiset.mem_toFinset, Polynomial.mem_roots', Polynomial.IsRoot.def]
        exact ⟨hq, hi⟩
    _ ≤ Multiset.card q.roots := q.roots.toFinset_card_le
    _ ≤ q.natDegree := q.card_roots'

/-- **Reed–Solomon minimum distance (Singleton/MDS).** Distinct degree-`<k` RS codewords differ in
at least `n − (k−1)` positions. -/
theorem rsCodeFinset_hammingDist_ge (domain : ι ↪ F) (k : ℕ) [NeZero k] (c c' : ι → F)
    (hc : c ∈ rsCodeFinset domain k) (hc' : c' ∈ rsCodeFinset domain k) (hne : c ≠ c') :
    Fintype.card ι - (k - 1) ≤ hammingDist c c' := by
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  rw [mem_rsCodeFinset, ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero] at hc hc'
  obtain ⟨p, hp, rfl⟩ := hc
  obtain ⟨p', hp', rfl⟩ := hc'
  have hq_ne : p - p' ≠ 0 := by
    rw [sub_ne_zero]; intro h; exact hne (by rw [h])
  have hqdeg : (p - p').natDegree < k :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le p p') (max_lt hp hp')
  have hagree : CodeGeometry.agree (ReedSolomon.evalOnPoints domain p)
      (ReedSolomon.evalOnPoints domain p') ≤ k - 1 := by
    rw [CodeGeometry.agree]
    have heq : (univ.filter (fun i => ReedSolomon.evalOnPoints domain p i
        = ReedSolomon.evalOnPoints domain p' i))
        = (univ.filter (fun i => (p - p').eval (domain i) = 0)) := by
      apply Finset.filter_congr
      intro i _
      simp only [ReedSolomon.evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk,
        Polynomial.eval_sub, sub_eq_zero]
    rw [heq]
    exact le_trans (card_domain_roots_le domain (p - p') hq_ne) (by omega)
  have hsum := CodeGeometry.agree_add_hammingDist (ReedSolomon.evalOnPoints domain p)
    (ReedSolomon.evalOnPoints domain p')
  omega

/-- **RS unique-decoding covered fraction.** For `2r < n−(k−1)` (the RS unique-decoding radius), the
covered set satisfies `|RS|·V ≤ |close|`. -/
theorem rs_covered_count_ge_unique_decoding (domain : ι ↪ F) (k : ℕ) [NeZero k] (r : ℕ)
    (hr : 2 * r < Fintype.card ι - (k - 1))
    (hpos : 0 < (rsCodeFinset domain k).card
        * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    (rsCodeFinset domain k).card * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card
      ≤ (univ.filter (fun w : ι → F => closeCount (rsCodeFinset domain k) r w ≠ 0)).card :=
  covered_count_ge_of_minDist (rsCodeFinset domain k) r (Fintype.card ι - (k - 1))
    (fun c hc c' hc' hne => rsCodeFinset_hammingDist_ge domain k c c' hc hc' hne) hr hpos

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.rsCodeFinset_hammingDist_ge
#print axioms ArkLib.CS25.rs_covered_count_ge_unique_decoding

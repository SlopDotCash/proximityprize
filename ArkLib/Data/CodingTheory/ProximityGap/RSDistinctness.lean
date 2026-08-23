/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineSpaces

/-! # Reed–Solomon distinctness (consumable for GS list-decoding counting)

Distinct degree-`<k` polynomials agree on fewer than `k` domain points — the
Reed–Solomon minimum-distance fact underlying every list-decoding distinctness
count: two candidate codewords cannot match on `≥ k` evaluation points without
being identical. Consumable by the GS list-size / Sbeta agreement-counting. -/

namespace RSDistinct

open Polynomial

variable {F : Type} [Field F] {ι : Type} (domain : ι ↪ F)

/-- **RS distinctness.** Distinct `p, q ∈ degreeLT F k` agree on `< k` of the
domain points: `|{x ∈ S : p(ωₓ) = q(ωₓ)}| < k`. -/
theorem degreeLT_agree_card_lt_of_ne [DecidableEq F] {k : ℕ}
    {p q : F[X]} (hp : p ∈ Polynomial.degreeLT F k) (hq : q ∈ Polynomial.degreeLT F k)
    (hpq : p ≠ q) (S : Finset ι) :
    (S.filter (fun x => p.eval (domain x) = q.eval (domain x))).card < k := by
  classical
  have hd0 : p - q ≠ 0 := sub_ne_zero.mpr hpq
  have hdmem : p - q ∈ Polynomial.degreeLT F k := Submodule.sub_mem _ hp hq
  have hdeg : (p - q).natDegree < k := by
    rw [Polynomial.natDegree_lt_iff_degree_lt hd0]
    exact Polynomial.mem_degreeLT.mp hdmem
  set T : Finset ι := S.filter (fun x => p.eval (domain x) = q.eval (domain x)) with hT
  have hroots : ∀ a ∈ T.image domain, (p - q).IsRoot a := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    have hxe := (Finset.mem_filter.mp hx).2
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, hxe, sub_self]
  have hcard := ProximityGap.card_roots_finset_le_natDegree hd0 hroots
  rw [Finset.card_image_of_injective _ domain.injective] at hcard
  omega

/-- Contrapositive form: agreement on `≥ k` domain points forces equality. -/
theorem degreeLT_eq_of_agree_card_ge [DecidableEq F] {k : ℕ}
    {p q : F[X]} (hp : p ∈ Polynomial.degreeLT F k) (hq : q ∈ Polynomial.degreeLT F k)
    {S : Finset ι} (h : k ≤ (S.filter (fun x => p.eval (domain x) = q.eval (domain x))).card) :
    p = q := by
  by_contra hpq
  exact absurd h (not_le.mpr (degreeLT_agree_card_lt_of_ne domain hp hq hpq S))

/-- Pointwise agreement on at least `k` domain points forces equality for
degree-`< k` polynomials. -/
theorem degreeLT_eq_of_agree_on_finset {k : ℕ}
    {p q : F[X]} (hp : p ∈ Polynomial.degreeLT F k) (hq : q ∈ Polynomial.degreeLT F k)
    {S : Finset ι} (hcard : k ≤ S.card)
    (hagree : ∀ x ∈ S, p.eval (domain x) = q.eval (domain x)) :
    p = q := by
  classical
  have hfilter : S.filter (fun x => p.eval (domain x) = q.eval (domain x)) = S := by
    apply Finset.ext
    intro x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp hx).1
    · intro hx
      exact Finset.mem_filter.mpr ⟨hx, hagree x hx⟩
  exact degreeLT_eq_of_agree_card_ge domain hp hq (S := S) (by rwa [hfilter])

/-- **Reed–Solomon unique decoding.** If `p, q ∈ degreeLT F k` each agree with a
word `w` on at least `a` domain points and `2a ≥ n + k` (the unique-decoding
radius), then `p = q`: their agreement sets overlap in `≥ k` points on which `p`
and `q` coincide, forcing equality by RS distinctness. -/
theorem degreeLT_unique_decode [DecidableEq F] [Fintype ι] {k : ℕ} {p q : F[X]} {w : ι → F}
    (hp : p ∈ Polynomial.degreeLT F k) (hq : q ∈ Polynomial.degreeLT F k) {a : ℕ}
    (hpa : a ≤ (Finset.univ.filter (fun x => p.eval (domain x) = w x)).card)
    (hqa : a ≤ (Finset.univ.filter (fun x => q.eval (domain x) = w x)).card)
    (hrad : Fintype.card ι + k ≤ 2 * a) :
    p = q := by
  classical
  set Ap : Finset ι := Finset.univ.filter (fun x => p.eval (domain x) = w x) with hAp
  set Aq : Finset ι := Finset.univ.filter (fun x => q.eval (domain x) = w x) with hAq
  have hsub : Ap ∩ Aq ⊆ Finset.univ.filter (fun x => p.eval (domain x) = q.eval (domain x)) := by
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hxp, hxq⟩
    have h1 := (Finset.mem_filter.mp hxp).2
    have h2 := (Finset.mem_filter.mp hxq).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, by rw [h1, h2]⟩
  have hunion : (Ap ∪ Aq).card ≤ Fintype.card ι := by
    rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
  have hie : (Ap ∩ Aq).card + (Ap ∪ Aq).card = Ap.card + Aq.card :=
    Finset.card_inter_add_card_union _ _
  have hinter_ge : k ≤ (Ap ∩ Aq).card := by omega
  have hagree_ge : k ≤ (Finset.univ.filter
      (fun x => p.eval (domain x) = q.eval (domain x))).card :=
    le_trans hinter_ge (Finset.card_le_card hsub)
  exact degreeLT_eq_of_agree_card_ge domain hp hq hagree_ge

end RSDistinct

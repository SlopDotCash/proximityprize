/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.AffineListIncidences
import ArkLib.Data.Polynomial.FiniteDomainQuotient

/-! # Shortening a Reed–Solomon list on common agreement sites to an affine list -/
noncomputable section
open Finset Code Polynomial
namespace ProximityGap.SharedLocatorListIncidences
open AffineListIncidences

variable {F I : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I]

omit [Fintype F] [Fintype I] [Nonempty I] in
/-- Prescribed agreement sites consume one polynomial degree apiece. After removing
their common locator, each word has uniquely determined affine evaluations. -/
private theorem line_at (dom : I ↪ F) (A : Finset I) (s : ℕ) (ha : A.card = s)
    (v w : I → F) (hv : v ∈ ReedSolomon.code dom (s + 2))
    (hw : w ∈ ReedSolomon.code dom (s + 2)) (same : ∀ i ∈ A, w i = v i) :
    ∃ l : F × F, ∀ i, w i = v i +
      (Lagrange.nodal (A.image dom) id).eval (dom i) * (l.1 * dom i + l.2) := by
  classical
  let : NeZero (s + 2) := ⟨by omega⟩
  obtain ⟨f, df, ef⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hw
  obtain ⟨g, dg, eg⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hv
  have dz : (f - g).natDegree ≤ s + 1 := (natDegree_sub_le ..).trans (by omega)
  have zeros : ZeroOn (A.image dom) (f - g) := by
    rintro _ hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    rw [eval_sub, ef, eg, same i hi, sub_self]
  obtain ⟨q, ⟨hq, dq⟩, _⟩ := (zeroOn_iff_existsUnique_quotient_natDegree_le dz).mp zeros
  rw [card_image_of_injective _ dom.injective, ha] at dq
  refine ⟨(q.coeff 1, q.coeff 0), fun i => ?_⟩
  have eq := congrArg (fun h : F[X] => h.eval (dom i)) hq
  simp only [eval_sub, eval_mul, ef, eg] at eq
  have affine : q.eval (dom i) = q.coeff 1 * dom i + q.coeff 0 := by
    nth_rw 1 [q.eq_X_add_C_of_natDegree_le_one (by omega)]
    simp
  rw [affine] at eq
  linear_combination eq

omit [Fintype F] in
/-- Count common agreement subsets and retain exactly the required number of
distinct affine graphs on the shortened domain. -/
theorem scalar_bound (dom : I ↪ F) (n t B l s : ℕ) (hn : Fintype.card I = n)
    (ht : t ≤ n) (hl : 0 < l) (havg : n.choose s * (l - 1) < (B + 1) * t.choose s)
    (estimate : ∀ P L : Finset (F × F), P.card = n - s → L.card = l →
      incidences P L < l * (t - s)) :
    Lambda (ReedSolomon.code dom (s + 2) : Set (I → F)) (((n - t : ℕ) : ℝ) / n) ≤ B := by
  classical
  apply Lambda_le_of_forall_finset_card_le
  intro y T hall
  by_contra! hto
  obtain ⟨S, sub, hs⟩ := exists_subset_card_eq (show B + 1 ≤ T.card by omega)
  let hit (w : I → F) := univ.filter (fun i => y i = w i)
  have large (w : I → F) (hw : w ∈ S) : t ≤ (hit w).card := by
    have close := (mem_closeCodewordsRel_iff.mp (hall w (sub hw))).2
    rw [relHammingDist_coe, hn] at close
    have pos : (0 : ℝ) < n := by exact_mod_cast hn ▸ Fintype.card_pos (α := I)
    have dist : hammingDist y w ≤ n - t := by
      exact_mod_cast (div_le_div_iff_of_pos_right pos).mp close
    have both := card_filter_add_card_filter_not (s := (univ : Finset I)) (p := fun i => y i = w i)
    change (hit w).card + hammingDist y w = _ at both
    rw [card_univ, hn] at both
    omega
  let sets := (univ : Finset I).powersetCard s
  let slice (A : Finset I) := S.filter fun w => A ⊆ hit w
  have per (w : I → F) (hw : w ∈ S) : t.choose s ≤ (sets.filter (fun A => A ⊆ hit w)).card := by
    have eq : sets.filter (fun A => A ⊆ hit w) = (hit w).powersetCard s := by
      ext A; simp [sets, mem_powersetCard, and_comm]
    rw [eq, card_powersetCard]
    exact Nat.choose_le_choose s (large w hw)
  obtain ⟨A, hAs, ha⟩ : ∃ A ∈ sets, l ≤ (slice A).card := by
    by_contra! h
    have low : S.card * t.choose s ≤ ∑ w ∈ S, (sets.filter (fun A => A ⊆ hit w)).card := by
      simpa using sum_le_sum per
    have high : ∑ A ∈ sets, (slice A).card ≤ n.choose s * (l - 1) := by
      simpa [sets, hn] using sum_le_sum (s := sets)
        (fun A hA => show (slice A).card ≤ l - 1 by have := h A hA; omega)
    have eq : ∑ w ∈ S, (sets.filter (fun A => A ⊆ hit w)).card = ∑ A ∈ sets, (slice A).card := by
      simp only [slice, card_eq_sum_ones, sum_filter]
      rw [sum_comm]
    rw [hs, eq] at low
    exact havg.not_ge (low.trans high)
  have acard := (mem_powersetCard.mp hAs).2
  obtain ⟨V, vsub, vcard⟩ := exists_subset_card_eq ha
  have member (w : V) := (mem_filter.mp (vsub w.property)).1
  have code (w : V) := (mem_closeCodewordsRel_iff.mp (hall w.val (sub (member w)))).1
  have anchor (w : V) {i : I} (hi : i ∈ A) : y i = w.val i :=
    (mem_filter.mp ((mem_filter.mp (vsub w.property)).2 hi)).2
  obtain ⟨v, hv⟩ := card_pos.mp (show 0 < V.card by omega)
  choose line rep using fun w : V => line_at dom A s acard v w.val (code ⟨v,hv⟩) (code w)
    (fun _ hi => (anchor w hi).symm.trans (anchor ⟨v,hv⟩ hi))
  have inj : Function.Injective line := by
    intro u w eq
    apply Subtype.ext
    funext i
    rw [rep u i, rep w i, eq]
  let loc (i : I) := (Lagrange.nodal (A.image dom) id).eval (dom i)
  let point (i : I) := (dom i, (y i - v i) / loc i)
  have pinj : Function.Injective point := fun _ _ h => dom.injective (congrArg Prod.fst h)
  let points := Aᶜ.image point
  let lines := (univ : Finset V).image line
  have mcount : points.card = n - s := by
    simp only [points, card_image_of_injective _ pinj, card_compl, hn, acard]
  have lcount : lines.card = l := by simp [lines, card_image_of_injective _ inj, vcard]
  have mass (w : V) : t - s ≤ (points.filter (fun p => p.2 = (line w).1 * p.1 + (line w).2)).card := by
    have le : t - s ≤ (hit w.val \ A).card := by
      rw [← acard]
      exact (Nat.sub_le_sub_right (large w.val (member w)) _).trans (le_card_sdiff _ _)
    apply le.trans
    rw [← card_image_of_injective (hit w.val \ A) pinj]
    apply card_le_card
    intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    obtain ⟨hi, ia⟩ := mem_sdiff.mp hi
    refine mem_filter.mpr ⟨mem_image_of_mem _ (mem_compl.mpr ia), ?_⟩
    have nz : loc i ≠ 0 := Lagrange.eval_nodal_not_at_node
      (s := A.image dom) (v := id) (x := dom i) (by
        intro b hb he
        obtain ⟨j, hj, hbj⟩ := mem_image.mp hb
        have eq : i = j := dom.injective (he.trans hbj.symm)
        exact ia (by rwa [eq]))
    change (y i - v i) / loc i = _
    rw [div_eq_iff nz, (mem_filter.mp hi).2, rep w i]
    dsimp [loc]; ring
  have lower : l * (t - s) ≤ incidences points lines := by
    simp only [incidences, lines, sum_image inj.injOn]
    simpa [vcard] using sum_le_sum (s := (univ : Finset V)) (fun w _ => mass w)
  exact (estimate points lines mcount lcount).not_ge lower

/-- At each dimension, a sufficiently large 128-bit field budget ensures the closed
list bound at 3071 agreements above the dimension. The support-based width transfer
works when the budget is larger than the square root of the field cardinality. -/
theorem production (dom : I ↪ F) (s : ℕ) (hn : Fintype.card I = 1073741824)
    (ht : s + 3073 ≤ 1073741824) (graph : GraphEstimate F 1048575)
    (budget : 1073741824 * (1073741824 : ℕ).choose s ≤
      (Nat.card F / 2 ^ 128) * (s + 3073).choose s)
    (width : ℕ) [NeZero width] :
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code dom (s + 2) : Set (I → F)))
      (((1073741824 - (s + 3073) : ℕ) : ℝ) / 1073741824) ≤ (Nat.card F / 2 ^ 128 : ℕ) := by
  apply (InterleavedListProjection.list_budget_iff_of_length_le _ _ (by decide : 1 < 2 ^ 128)
    (by rw [hn]; decide)).mpr
  apply scalar_bound dom 1073741824 (s + 3073) _ 1073741825 s hn ht (by decide)
  · have pos : 0 < (s + 3073).choose s := Nat.choose_pos (by omega)
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · intro P L m l
    have h := graph P L
    rw [m, l] at h
    have mono : cost (1073741824 - s) 1073741825 1048575 ≤ cost 1073741824 1073741825 1048575 := by
      unfold cost; gcongr; omega
    have final : cost 1073741824 1073741825 1048575 < 1073741825 * 3073 := by decide
    simpa using (h.trans mono).trans_lt final

#print axioms production
end ProximityGap.SharedLocatorListIncidences

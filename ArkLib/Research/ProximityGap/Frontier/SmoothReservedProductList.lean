/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothDomainMcaEquivalence
import ArkLib.Research.ProximityGap.Frontier.SmoothPowerListDescent

/-! # Lifting a list while reserving one power fiber

Al Kindi's common-root construction (ePrint 2026/2245, Theorem 1.1) multiplies the
lifted polynomials by a locator on all but one site of a reserved fiber. We formulate
the comparison for arbitrary punctured base lists and then apply the product count on
the remaining smooth coset sites.
-/

namespace ProximityGap.SmoothReservedProductList

open Finset Code Polynomial
open scoped ENNReal

variable {I J F : Type} [Fintype I] [Fintype J] [Field F]

/-- A regular projection on all but one fiber sends every base list at `e` errors
to a list at `e*m+1` errors, with the Reed–Solomon dimension multiplied by `m`. -/
theorem punctured_lift [DecidableEq J] (D : I ↪ F) (E : J ↪ F) (π : I → Option J) (P : F[X])
    {m j : ℕ} (hm : 0 < m) (hj : 0 < j) (degree : P.natDegree = m)
    (fib : ∀ v, (Finset.univ.filter (fun i => π i = v)).card = m)
    (coordinates : ∀ i v, π i = some v → P.eval (D i) = E v) (e : ℕ) :
    Lambda (ReedSolomon.code E j : Set (J → F)) ((e : ℝ) / Fintype.card J) ≤
      Lambda (ReedSolomon.code D (j * m) : Set (I → F))
        (((e * m + 1 : ℕ) : ℝ) / Fintype.card I) := by
  classical
  let T := univ.filter fun i => π i = none
  obtain ⟨i₀, hi₀⟩ := card_pos.mp (hm.trans_eq (fib none).symm)
  let G : F[X] := ∏ i ∈ T.erase i₀, (X - C (D i))
  have degreeG : G.natDegree < m := by
    simp [G, card_erase_of_mem (show i₀ ∈ T from hi₀), T, fib, hm]
  have zero (i : I) : G.eval (D i) = 0 ↔ i ≠ i₀ ∧ π i = none := by
    simp [G, T, eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero, D.injective.eq_iff]
  let : NeZero j := ⟨hj.ne'⟩
  let C₀ := (ReedSolomon.code E j : Set (J → F))
  have reps (w : C₀) := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp w.property
  choose f degf evalf using reps
  let lift (w : C₀) := fun i : I => G.eval (D i) * (f w).eval (P.eval (D i))
  have iscode (w : C₀) : lift w ∈ ReedSolomon.code D (j * m) := by
    apply ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval (G * (f w).comp P)
    · have h := (natDegree_mul_le (p := G) (q := (f w).comp P)).trans_eq (by
        rw [natDegree_comp, degree])
      have mult := Nat.mul_le_mul_right m (degf w)
      rw [Nat.succ_mul] at mult
      omega
    · intro i
      simp [lift]
  have outside (w : C₀) (i : I) (v : J) (hπ : π i = some v) :
      lift w i = G.eval (D i) * w.val v := by
    simp [lift, coordinates _ _ hπ, evalf]
  have inj : Function.Injective lift := by
    intro u w eq
    apply Subtype.ext
    funext v
    obtain ⟨i, hi⟩ := card_pos.mp (hm.trans_eq (fib (some v)).symm)
    have hv := (mem_filter.mp hi).2
    have h := congrFun eq i
    rw [outside _ _ _ hv, outside _ _ _ hv] at h
    exact mul_left_cancel₀ (fun z => by simpa [hv] using ((zero i).mp z).2) h
  apply Lambda_le_iff_forall_encard_le.mpr
  intro y
  rw [← closeCodewords_eq_closeCodewordsRel]
  let receive (i : I) : F := (π i).elim 0 (fun v => G.eval (D i) * y v)
  let M := closeCodewords C₀ y e
  let M' := (fun w : C₀ => w.val) ⁻¹' M
  have hM : (fun w : C₀ => w.val) '' M' = M := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hw
      exact ⟨⟨w, hw.1⟩, hw, rfl⟩
  change M.encard ≤ _
  rw [← hM, Subtype.val_injective.injOn.encard_image, ← inj.injOn.encard_image (s := M')]
  apply encard_le_Lambda_of_subset_closeCodewordsRel (f := receive)
  rw [← closeCodewords_eq_closeCodewordsRel]
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨iscode w, (mem_hammingBall_iff _ _ _).mpr ?_⟩
  let bad := univ.filter fun v => y v ≠ w.val v
  have badsize : bad.card ≤ e :=
    (mem_hammingBall_iff _ _ _).mp (show w.val ∈ hammingBall y e from hw.2)
  let pulled := bad.biUnion fun v => univ.filter fun i => π i = some v
  have sum : pulled.card = bad.card * m := by
    apply (card_biUnion ?_).trans (sum_const_nat (fun v _ => fib (some v)))
    intro v _ u _ ne
    exact disjoint_left.mpr fun i hv hu => ne (Option.some.inj
      ((mem_filter.mp hv).2.symm.trans (mem_filter.mp hu).2))
  have sub : (univ.filter fun i => receive i ≠ lift w i) ⊆ insert i₀ pulled := by
    intro i hi
    by_cases h : i = i₀
    · simp [h]
    apply mem_insert_of_mem
    have diff := (mem_filter.mp hi).2
    cases hv : π i with
    | none => simp [receive, lift, hv, (zero i).mpr ⟨h, hv⟩] at diff
    | some v =>
      apply mem_biUnion.mpr
      refine ⟨v, mem_filter.mpr ⟨mem_univ _, ?_⟩, mem_filter.mpr ⟨mem_univ _, hv⟩⟩
      intro same
      exact diff (by simp [receive, hv, outside _ _ _ hv, same])
  exact ((card_le_card sub).trans (card_insert_le _ _)).trans
    (by rw [sum]; exact Nat.add_le_add_right (Nat.mul_le_mul_right m badsize) 1)

/-- The original coset product key also bounds lists on a punctured smooth domain.
Removing a site changes the number of subsets but preserves the size of the key space. -/
theorem punctured_product_lower [DecidableEq F] (V : Finset F)
    [ReedSolomon.Smooth (Function.Embedding.subtype (· ∈ V))] {v₀ : F} (hv : v₀ ∈ V)
    {j B : ℕ} (hj : 0 < j) (hB : V.card * B < (V.card - 1).choose (j + 1)) :
    (B : ℕ∞) < Lambda (ReedSolomon.code (Function.Embedding.subtype (· ∈ V.erase v₀)) j :
      Set (V.erase v₀ → F)) (((V.card - 1 - (j + 1) : ℕ) : ℝ) / (V.card - 1 : ℕ)) := by
  classical
  let E := Function.Embedding.subtype (· ∈ V)
  let H := ReedSolomon.Smooth.H E
  let c := ReedSolomon.Smooth.a E
  obtain ⟨z, hz⟩ := SmoothDomainMcaEquivalence.coset_equiv E
  let := Fintype.ofEquiv V z
  let W := V.erase v₀
  let z' (v : W) := z ⟨v.val, mem_of_mem_erase v.property⟩
  have coord (v : W) : v.val = (c : F) * ((z' v : Fˣ) : F) :=
    hz ⟨v.val, mem_of_mem_erase v.property⟩
  let D' : W ↪ F := ⟨fun v => ((z' v : Fˣ) : F), fun v w h =>
    Subtype.ext ((coord v).trans ((congrArg (fun a : F => (c : F) * a) h).trans (coord w).symm))⟩
  have cardH := (Fintype.card_congr z).ge
  rw [Fintype.card_coe] at cardH
  have low := PrescribedProductList.exceeds_budget D' H z' (fun _ => rfl) hj
    (B := B) (by
      rw [Fintype.card_coe, show W.card = V.card - 1 from card_erase_of_mem hv]
      exact (Nat.mul_le_mul_right B cardH).trans_lt hB)
  rw [Fintype.card_coe, show W.card = V.card - 1 from card_erase_of_mem hv] at low
  apply low.trans_le (Lambda_mono_code ?_ _)
  let : NeZero j := ⟨hj.ne'⟩
  intro w hw
  obtain ⟨p, hp, he⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hw
  apply ReedSolomon.mem_code_iff_eval_of_ne_zero.mpr
  refine ⟨p.comp (C (↑c⁻¹ : F) * X), ?_, ?_⟩
  · simpa [natDegree_comp, c⁻¹.ne_zero] using hp
  · intro v
    change (p.comp (C (↑c⁻¹ : F) * X)).eval v.val = w v
    rw [eval_comp, eval_mul, eval_C, eval_X, coord v, ← mul_assoc, Units.inv_mul, one_mul]
    exact he v

/-- At length `m*h`, the all-width list budget already fails at `(h-j-2)*m+1`
errors whenever fixing the product on the `h-1` available power values exceeds the budget. -/
theorem smooth_list_exceeds (κ : Type) [Nonempty κ] [Nonempty I] [Finite F] [DecidableEq F]
    (D : I ↪ F) [ReedSolomon.Smooth D] {m h j B : ℕ} (hm : 0 < m)
    (hn : Fintype.card I = m * h) (hp : ∃ b : ℕ, h = 2 ^ b) (hj : 0 < j)
    (hB : h * B < (h - 1).choose (j + 1)) :
    (B : ℕ∞) < Lambda (interleavedCodeSet (κ := κ)
      (ReedSolomon.code D (j * m) : Set (I → F)))
      ((((h - j - 2) * m + 1 : ℕ) : ℝ) / Fintype.card I) := by
  classical
  let := Fintype.ofFinite F
  obtain ⟨V, size, mem, fib, ⟨smooth⟩, _⟩ :=
    SmoothPowerMcaDescent.exists_smooth_base D hm hn hp
  let := smooth
  have pos : 0 < h := by obtain ⟨_, rfl⟩ := hp; positivity
  obtain ⟨v₀, hv⟩ := card_pos.mp (size.trans_gt pos)
  let W := V.erase v₀
  let π (i : I) : Option W := if eq : D i ^ m = v₀ then none
    else some ⟨D i ^ m, mem_erase.mpr ⟨eq, mem i⟩⟩
  have none_iff (i : I) : π i = none ↔ D i ^ m = v₀ := by
    by_cases eq : D i ^ m = v₀ <;> simp [π, eq]
  have some_iff (i : I) (v : W) : π i = some v ↔ D i ^ m = v.val := by
    have ne := (mem_erase.mp v.property).1
    by_cases eq : D i ^ m = v₀
    · simp [π, eq, Ne.symm ne]
    · simp [π, eq, Subtype.ext_iff]
  have sizes (v : Option W) : (univ.filter (fun i => π i = v)).card = m := by
    cases v with
    | none => simpa only [none_iff] using fib v₀ hv
    | some v => simpa only [some_iff] using fib v.val (mem_of_mem_erase v.property)
  let E := Function.Embedding.subtype (· ∈ W)
  have upper := punctured_lift D E π (X ^ m) hm hj (by simp) sizes
    (fun i v eq => by simpa [E] using (some_iff i v).mp eq) (h - j - 2)
  have lower := punctured_product_lower V hv hj (size ▸ hB)
  have cardW : Fintype.card W = h - 1 := (Fintype.card_coe _).trans ((card_erase_of_mem hv).trans
    (congrArg (fun z : ℕ => z - 1) size))
  rw [cardW] at upper
  rw [size, show h - 1 - (j + 1) = h - j - 2 by omega] at lower
  apply (lower.trans_le upper).trans_le
  let rep (x : F) := fun _ : κ => x
  apply Lambda_le_of_injective_comp (e := rep)
  · exact fun _ _ eq => congrFun eq (Classical.arbitrary κ)
  · exact fun _ hc _ => hc

end ProximityGap.SmoothReservedProductList

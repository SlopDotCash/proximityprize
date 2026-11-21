/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SignedReciprocalLists
import ArkLib.Research.ProximityGap.Frontier.ReservedFiberList
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved
import ArkLib.Data.CodingTheory.ListDecodability.SymbolMap
import Mathlib.Combinatorics.Pigeonhole

/-! # Lifting a quotient family to one Reed–Solomon list at two anchor fibers -/

namespace ProximityGap.TwoAnchorListWitness

open Finset Polynomial Code

variable {I J F : Type} [Fintype I] [Fintype J] [Nonempty J]
  [DecidableEq I] [DecidableEq J] [Field F]

/-- Some ordinary quotient fiber is avoided by at least the mean number of
candidates. Restricting to these candidates frees that fiber for the vanisher. -/
theorem exists_avoided_fiber (U : Finset I) (hu : U.Nonempty) (family : Finset (Finset I))
    (t : ℕ) (hsize : ∀ S ∈ family, S.card ≤ t) :
    ∃ z ∈ U, family.card*(U.card-t) ≤ U.card*(family.filter fun S => z ∉ S).card := by
  classical
  obtain ⟨z,hz,hmax⟩ := U.exists_max_image (fun x => (family.filter fun S => x ∉ S).card) hu
  refine ⟨z,hz,Finset.card_mul_le_card_mul (fun (S : Finset I) x => x ∉ S) ?_ hmax⟩
  intro S hS
  have he : U.bipartiteAbove (fun (T : Finset I) x => x ∉ T) S = U \ S := by
    ext x
    simp [Finset.bipartiteAbove]
  rw [he]
  exact (Nat.sub_le_sub_left (hsize S hS) _).trans (Finset.le_card_sdiff S U)

/-- The common vanishing sites may occupy any reserved fibers avoided by every candidate.
The two disjoint anchor allocations and the common sites fit inside their joint capacity. -/
theorem list_lower_reserved (D : I × J ↪ F) (a : I → F)
    (hpowers : ∀ x, D x ^ Fintype.card J = a x.1) (p m : I) (hpm : p ≠ m)
    (R : Finset I) (hpr : p∈R) (hmr : m∈R)
    (P M : Finset F) (family : Finset (Finset I)) (q : Finset I → F[X]) (y : I → F)
    (b t g : ℕ) (hq : ∀ S ∈ family, (q S).natDegree < b)
    (hS : ∀ S ∈ family, S.card = t ∧ Disjoint S R)
    (hag : ∀ S ∈ family, ∀ i, i ≠ p → i ≠ m → ((q S).eval (a i) = y i ↔ i ∈ S))
    (hanchor : ∀ S ∈ family, (q S).eval (a p) ∈ P ∨ (q S).eval (a m) ∈ M)
    (hp : P.card * g ≤ Fintype.card J) (hm : M.card * g ≤ Fintype.card J)
    (htotal : P.card*g+M.card*g+(Fintype.card J-1) ≤ R.card*Fintype.card J) :
    (family.card : ℕ∞) ≤ Lambda (ReedSolomon.code D (b*Fintype.card J) : Set (I × J → F))
      (((Fintype.card (I × J) - (t*Fintype.card J + (Fintype.card J-1) + g) : ℕ) : ℝ)
        / Fintype.card (I × J)) := by
  classical
  let h := Fintype.card J
  have hpos : 0 < h := Fintype.card_pos
  let fp := ({p} : Finset I) ×ˢ (univ : Finset J)
  let fm := ({m} : Finset I) ×ˢ (univ : Finset J)
  have memp (x : I × J) : x ∈ fp ↔ x.1 = p := by simp only [fp, mem_product, mem_singleton, mem_univ, and_true]
  have memm (x : I × J) : x ∈ fm ↔ x.1 = m := by simp only [fm, mem_product, mem_singleton, mem_univ, and_true]
  have dis : Disjoint fp fm := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact hpm (((memp x).mp hx).symm.trans ((memm x).mp hy))
  let region := R ×ˢ (univ : Finset J)
  have fpR : fp ⊆ region := fun x hx => mem_product.mpr ⟨(memp x).mp hx ▸ hpr,mem_univ _⟩
  have fmR : fm ⊆ region := fun x hx => mem_product.mpr ⟨(memm x).mp hx ▸ hmr,mem_univ _⟩
  obtain ⟨A,hA,cA⟩ := exists_subset_card_eq (s:=fp) (show P.card*g ≤ fp.card by simpa [fp] using hp)
  obtain ⟨B,hB,cB⟩ := exists_subset_card_eq (s:=fm) (show M.card*g ≤ fm.card by simpa [fm] using hm)
  have hdAB := dis.mono hA hB
  have cap : h-1 ≤ (region \ (A∪B)).card := by
    rw [card_sdiff_of_subset (union_subset (hA.trans fpR) (hB.trans fmR)),card_union_of_disjoint hdAB,cA,cB]
    simpa [region,h] using (Nat.le_sub_of_add_le (by omega : (h-1) + (P.card*g + M.card*g) ≤ R.card * Fintype.card J))
  obtain ⟨Z,hZ,cZ⟩ := exists_subset_card_eq cap
  let H : F[X] := ∏ x ∈ Z, (X - C (D x))
  let base (x : I × J) := H.eval (D x) * y x.1
  let pattern (v : F) (x : I × J) := H.eval (D x) * v
  obtain ⟨w₁, off₁, hit₁⟩ := ReciprocalFiberLists.split_fiber A P g base pattern cA.ge
  obtain ⟨w, off₂, hit₂⟩ := ReciprocalFiberLists.split_fiber B M g w₁ pattern cB.ge
  let f (S : Finset I) := H * (q S).comp (X ^ h)
  let word (S : Finset I) (x : I × J) := (f S).eval (D x)
  have value (S : Finset I) (x : I × J) : word S x = H.eval (D x) * (q S).eval (a x.1) := by
    simp [word, f, hpowers, h]
  have hz (x : I × J) : H.eval (D x) = 0 ↔ x ∈ Z := by
    simp [H, eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero, D.injective.eq_iff]
  have outside (x : I × J) (hx : x.1 ∉ R) : x ∉ A ∧ x ∉ B ∧ x ∉ Z := by
    have hr : x ∉ region := fun h => hx (mem_product.mp h).1
    exact ⟨fun h => hr (fpR (hA h)), fun h => hr (fmR (hB h)), fun h => hr (mem_sdiff.mp (hZ h)).1⟩
  have ordinary (S : Finset I) (hSf : S ∈ family) (x : I × J) (hx : x.1 ∉ R) :
      word S x = w x ↔ x.1 ∈ S := by
    obtain ⟨ha,hb,hz'⟩ := outside x hx
    rw [off₂ x hb, off₁ x ha, value]
    exact (mul_right_inj' (fun e => hz' ((hz x).mp e))).trans
      (hag S hSf _ (fun he => hx (he ▸ hpr)) (fun he => hx (he ▸ hmr)))
  have hinj : Set.InjOn word (family : Set (Finset I)) := by
    intro S hSf T hTf he
    ext i
    by_cases hi : i ∈ R
    · exact iff_of_false (fun h => Finset.disjoint_left.mp (hS S hSf).2 h hi)
          (fun h => Finset.disjoint_left.mp (hS T hTf).2 h hi)
    let x : I × J := (i, Classical.choice ‹Nonempty J›)
    exact (ordinary S hSf x hi).symm.trans ((congrFun he x) ▸ ordinary T hTf x hi)
  have hmemb : (↑(family.image word) : Set (I × J → F)) ⊆ closeCodewordsRel
      (ReedSolomon.code D (b*h) : Set (I × J → F)) w
      (((Fintype.card (I × J) - (t*h+(h-1)+g) : ℕ) : ℝ)/Fintype.card (I × J)) := by
    rw [← closeCodewords_eq_closeCodewordsRel]
    intro u hu
    obtain ⟨S,hSf,rfl⟩ := mem_image.mp hu
    refine ⟨ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval (f S) ?_ (fun _ => rfl), ?_⟩
    · have hd := hq S hSf
      have hd' := Nat.mul_le_mul_right h (show (q S).natDegree+1 ≤ b by omega)
      rw [Nat.add_mul, one_mul] at hd'
      apply natDegree_mul_le.trans_lt
      rw [show H.natDegree = h-1 by simpa [H] using cZ, natDegree_comp, natDegree_X_pow]
      omega
    let plain := S ×ˢ (univ : Finset J)
    let extra := (A ∪ B).filter fun x => word S x = w x
    have own (x : I × J) (hx : x ∈ plain) : x.1 ∉ R :=
      Finset.disjoint_left.mp (hS S hSf).2 (mem_product.mp hx).1
    have d₁ : Disjoint plain Z := Finset.disjoint_left.mpr (fun _ hx => (outside _ (own _ hx)).2.2)
    have d₂ : Disjoint (plain ∪ Z) extra := by
      apply Finset.disjoint_left.mpr
      intro x hx he
      have hab := (mem_filter.mp he).1
      rcases mem_union.mp hx with hor | hzr
      · have out := outside x (own x hor)
        exact (mem_union.mp hab).elim out.1 out.2.1
      · exact (mem_sdiff.mp (hZ hzr)).2 hab
    have eg : g ≤ extra.card := by
      rcases hanchor S hSf with hpv | hmv
      · apply (hit₁ _ hpv).trans (card_le_card _)
        intro x hx
        obtain ⟨ha,hw⟩ := mem_filter.mp hx
        have hbx : x ∉ B := fun hb => Finset.disjoint_left.mp dis (hA ha) (hB hb)
        have he : x.1 = p := (memp x).mp (hA ha)
        exact mem_filter.mpr ⟨mem_union_left _ ha, by simpa [value, off₂ x hbx, pattern, he] using hw.symm⟩
      · apply (hit₂ _ hmv).trans (card_le_card _)
        intro x hx
        obtain ⟨hb,hw⟩ := mem_filter.mp hx
        have he : x.1 = m := (memm x).mp (hB hb)
        exact mem_filter.mpr ⟨mem_union_right _ hb, by simpa [value, pattern, he] using hw.symm⟩
    have sub : (plain ∪ Z) ∪ extra ⊆ univ.filter (fun x => w x = word S x) := by
      intro x hx
      apply mem_filter.mpr ⟨mem_univ _, ?_⟩
      rcases mem_union.mp hx with hx | hx
      · rcases mem_union.mp hx with hor | hzr
        · exact ((ordinary S hSf x (own x hor)).mpr (mem_product.mp hor).1).symm
        · have hab := (mem_sdiff.mp (hZ hzr)).2
          rw [off₂ x (fun hb => hab (mem_union_right _ hb)), off₁ x (fun ha => hab (mem_union_left _ ha)),
            value, show base x = H.eval (D x) * y x.1 from rfl, (hz x).mpr hzr]
          simp
      · exact (mem_filter.mp hx).2.symm
    have hcard := card_le_card sub
    rw [card_union_of_disjoint d₂, card_union_of_disjoint d₁, card_product, card_univ,
      (hS S hSf).1, cZ] at hcard
    rw [mem_hammingBall_iff]
    change (univ.filter fun x => w x ≠ word S x).card ≤ _
    change t*h+(h-1)+extra.card ≤ _ at hcard
    let yes := univ.filter fun x => w x = word S x
    have he : (univ.filter fun x => w x ≠ word S x) = (univ : Finset (I × J)) \ yes := by
      ext x
      simp [yes]
    rw [he, card_sdiff_of_subset (subset_univ _), card_univ]
    apply Nat.sub_le_sub_left
    exact (Nat.add_le_add_left eg _).trans hcard
  have bound := encard_le_Lambda_of_subset_closeCodewordsRel hmemb
  rwa [Set.encard_coe_eq_coe_finsetCard,card_image_of_injOn hinj] at bound

/-- From prescribed quotient agreements and anchor values to the canonical worst-center
list size. Both anchors and all candidates use the same production received word. -/
theorem list_lower (D : I × J ↪ F) (a : I → F)
    (hpowers : ∀ x, D x ^ Fintype.card J = a x.1) (p m : I) (hpm : p ≠ m)
    (P M : Finset F) (family : Finset (Finset I)) (q : Finset I → F[X]) (y : I → F)
    (b t g : ℕ) (hq : ∀ S ∈ family, (q S).natDegree < b)
    (hS : ∀ S ∈ family, S.card = t ∧ p ∉ S ∧ m ∉ S)
    (hag : ∀ S ∈ family, ∀ i, i ≠ p → i ≠ m → ((q S).eval (a i) = y i ↔ i ∈ S))
    (hanchor : ∀ S ∈ family, (q S).eval (a p) ∈ P ∨ (q S).eval (a m) ∈ M)
    (hp : P.card * g ≤ Fintype.card J) (hm : M.card * g ≤ Fintype.card J)
    (htotal : P.card*g+M.card*g+(Fintype.card J-1) ≤ 2*Fintype.card J) :
    (family.card : ℕ∞) ≤ Lambda (ReedSolomon.code D (b*Fintype.card J) : Set (I × J → F))
      (((Fintype.card (I × J) - (t*Fintype.card J + (Fintype.card J-1) + g) : ℕ) : ℝ)
        / Fintype.card (I × J)) := by
  classical
  apply list_lower_reserved D a hpowers p m hpm {p,m} (by simp) (by simp) P M family q y b t g hq
  · intro S hs
    exact ⟨(hS S hs).1, by simpa [Finset.disjoint_insert_right,Finset.disjoint_singleton_right] using (hS S hs).2⟩
  · exact hag
  · exact hanchor
  · exact hp
  · exact hm
  · simpa [hpm] using htotal

omit [Fintype I] in
private theorem reserve_of_or (p m : I) (hpm : p≠m) (family : Finset (Finset I))
    (avoid : ∀ S ∈ family, p∉S ∧ m∉S) (u v h : ℕ) (hu : u≤h) (hv : v≤h)
    (hr : u+v+(h-1)≤2*h ∨ ∃ z : I, z≠p ∧ z≠m ∧ ∀ S ∈ family, z∉S) :
    ∃ R : Finset I, p∈R ∧ m∈R ∧ (∀ S∈family, Disjoint S R) ∧ u+v+(h-1)≤R.card*h := by
  classical
  rcases hr with cap | ⟨z,hzp,hzm,hz⟩
  · refine ⟨{p,m}, by simp, by simp, ?_, by simpa [hpm] using cap⟩
    intro S hs
    simpa [Finset.disjoint_insert_right, Finset.disjoint_singleton_right] using avoid S hs
  · refine ⟨{z,p,m}, by simp, by simp, ?_, ?_⟩
    · intro S hs
      simpa [Finset.disjoint_insert_right, Finset.disjoint_singleton_right] using And.intro (hz S hs) (avoid S hs)
    · simpa [hzp,hzm,hpm] using (show u+v+(h-1)≤3*h by omega)

/-- From prescribed quotient agreements and anchor values to the canonical worst-center
list size. Both anchors and all candidates use the same production received word. -/
theorem list_lower_with_reserve (D : I × J ↪ F) (a : I → F)
    (hpowers : ∀ x, D x ^ Fintype.card J = a x.1) (p m : I) (hpm : p ≠ m)
    (P M : Finset F) (family : Finset (Finset I)) (q : Finset I → F[X]) (y : I → F)
    (b t g : ℕ) (hq : ∀ S ∈ family, (q S).natDegree < b)
    (hS : ∀ S ∈ family, S.card = t ∧ p ∉ S ∧ m ∉ S)
    (hag : ∀ S ∈ family, ∀ i, i ≠ p → i ≠ m → ((q S).eval (a i) = y i ↔ i ∈ S))
    (hanchor : ∀ S ∈ family, (q S).eval (a p) ∈ P ∨ (q S).eval (a m) ∈ M)
    (hp : P.card * g ≤ Fintype.card J) (hm : M.card * g ≤ Fintype.card J)
    (hreserve : P.card*g+M.card*g+(Fintype.card J-1) ≤ 2*Fintype.card J ∨
      ∃ z : I, z ≠ p ∧ z ≠ m ∧ ∀ S ∈ family, z ∉ S) :
    (family.card : ℕ∞) ≤ Lambda (ReedSolomon.code D (b*Fintype.card J) : Set (I × J → F))
      (((Fintype.card (I × J) - (t*Fintype.card J + (Fintype.card J-1) + g) : ℕ) : ℝ)
        / Fintype.card (I × J)) := by
  obtain ⟨R,hpR,hmR,dis,total⟩ := reserve_of_or p m hpm family (fun S hs => (hS S hs).2)
    _ _ _ hp hm hreserve
  exact list_lower_reserved D a hpowers p m hpm R hpR hmR P M family q y b t g hq
    (fun S hs => ⟨(hS S hs).1,dis S hs⟩) hag hanchor hp hm total

/-- Monic locator of quotient roots indexed by a selected set. -/
noncomputable def locator (a : I → F) (S : Finset I) : F[X] := ∏ i ∈ S, (X - C (a i))

/-- A common locator constant and two anchor palettes produce a list when an arbitrary
set of reserved fibers avoids the entire quotient family. -/
theorem locator_list_lower_reserved (D : I × J ↪ F) (a : I ↪ F) (ha : ∀ i, a i ≠ 0)
    (hpowers : ∀ x, D x ^ Fintype.card J = a x.1) (p m : I) (hpm : p ≠ m)
    (reserve : Finset I) (hpr : p∈reserve) (hmr : m∈reserve)
    (P M : Finset F) (family : Finset (Finset I)) (c : F) (b g : ℕ) (hb : 0 < b)
    (hS : ∀ S ∈ family, S.card = b+1 ∧ Disjoint S reserve)
    (hconst : ∀ S ∈ family, (locator a S).eval 0 = c)
    (hanchor : ∀ S ∈ family, (locator a S).eval (a p) ∈ P ∨ (locator a S).eval (a m) ∈ M)
    (hp : P.card*g ≤ Fintype.card J) (hm : M.card*g ≤ Fintype.card J)
    (htotal : P.card*g+M.card*g+(Fintype.card J-1) ≤ reserve.card*Fintype.card J) :
    (family.card : ℕ∞) ≤ Lambda (ReedSolomon.code D (b*Fintype.card J) : Set (I × J → F))
      (((Fintype.card (I × J) - ((b+1)*Fintype.card J + (Fintype.card J-1) + g) : ℕ) : ℝ)
        / Fintype.card (I × J)) := by
  classical
  let R : F[X] := X^(b+1) + C c
  let q (S : Finset I) := (R-locator a S).divX
  let val (i : I) (v : F) := (R.eval (a i)-v)/a i
  have hR : R.IsMonicOfDegree (b+1) := ⟨natDegree_X_pow_add_C, monic_X_pow_add_C c (by omega)⟩
  have hd (S : Finset I) (hs : S ∈ family) : (q S).natDegree < b := by
    have hL : (locator a S).IsMonicOfDegree (b+1) :=
      ⟨by simpa [locator] using (hS S hs).1, monic_prod_X_sub_C _ _⟩
    have hdiff := IsMonicOfDegree.natDegree_sub_lt (by omega : b+1 ≠ 0) hR hL
    change (R-locator a S).divX.natDegree < b
    rw [natDegree_divX_eq_natDegree_tsub_one]
    omega
  have he (S : Finset I) (hs : S ∈ family) (i : I) : (q S).eval (a i) = val i ((locator a S).eval (a i)) := by
    have hzero : (R-locator a S).coeff 0 = 0 := by
      simp [coeff_zero_eq_eval_zero, R, hconst S hs]
    have h := congrArg (eval (a i)) (divX_mul_X_add (R-locator a S))
    rw [hzero, C_0, add_zero, eval_mul, eval_X, eval_sub] at h
    exact (eq_div_iff (ha i)).mpr h
  have hip := card_image_le (s := P) (f := val p)
  have him := card_image_le (s := M) (f := val m)
  apply list_lower_reserved D a hpowers p m hpm reserve hpr hmr (P.image (val p)) (M.image (val m)) family q
    (fun i => val i 0) b (b+1) g hd hS
  · intro S hs i _ _
    rw [he S hs i, show val i ((locator a S).eval (a i)) = val i 0 ↔ (locator a S).eval (a i) = 0 by
      simp [val, div_left_inj' (ha i)]]
    simp [locator, eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero, a.injective.eq_iff]
  · intro S hs
    rw [he S hs p, he S hs m]
    exact (hanchor S hs).imp (fun hx => mem_image_of_mem _ hx) (fun hx => mem_image_of_mem _ hx)
  · exact (Nat.mul_le_mul_right g hip).trans hp
  · exact (Nat.mul_le_mul_right g him).trans hm
  · exact (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_right g hip)
      (Nat.mul_le_mul_right g him)) _).trans htotal

/-- A common locator constant and the two filtered anchor-value sets suffice.
Every counted member is a different actual Reed–Solomon evaluation word. -/
theorem locator_list_lower (D : I × J ↪ F) (a : I ↪ F) (ha : ∀ i, a i ≠ 0)
    (hpowers : ∀ x, D x ^ Fintype.card J = a x.1) (p m : I) (hpm : p ≠ m)
    (P M : Finset F) (family : Finset (Finset I)) (c : F) (b g : ℕ) (hb : 0 < b)
    (hS : ∀ S ∈ family, S.card = b+1 ∧ p ∉ S ∧ m ∉ S)
    (hconst : ∀ S ∈ family, (locator a S).eval 0 = c)
    (hanchor : ∀ S ∈ family, (locator a S).eval (a p) ∈ P ∨ (locator a S).eval (a m) ∈ M)
    (hp : P.card*g ≤ Fintype.card J) (hm : M.card*g ≤ Fintype.card J)
    (htotal : P.card*g+M.card*g+(Fintype.card J-1) ≤ 2*Fintype.card J) :
    (family.card : ℕ∞) ≤ Lambda (ReedSolomon.code D (b*Fintype.card J) : Set (I × J → F))
      (((Fintype.card (I × J) - ((b+1)*Fintype.card J + (Fintype.card J-1) + g) : ℕ) : ℝ)
        / Fintype.card (I × J)) := by
  classical
  apply locator_list_lower_reserved D a ha hpowers p m hpm {p,m} (by simp) (by simp) P M family c b g hb
  · intro S hs
    exact ⟨(hS S hs).1, by simpa [Finset.disjoint_insert_right,Finset.disjoint_singleton_right] using (hS S hs).2⟩
  · exact hconst
  · exact hanchor
  · exact hp
  · exact hm
  · simpa [hpm] using htotal

/-- A common locator constant and the two filtered anchor-value sets suffice.
Every counted member is a different actual Reed–Solomon evaluation word. -/
theorem locator_list_lower_with_reserve (D : I × J ↪ F) (a : I ↪ F) (ha : ∀ i, a i ≠ 0)
    (hpowers : ∀ x, D x ^ Fintype.card J = a x.1) (p m : I) (hpm : p ≠ m)
    (P M : Finset F) (family : Finset (Finset I)) (c : F) (b g : ℕ) (hb : 0 < b)
    (hS : ∀ S ∈ family, S.card = b+1 ∧ p ∉ S ∧ m ∉ S)
    (hconst : ∀ S ∈ family, (locator a S).eval 0 = c)
    (hanchor : ∀ S ∈ family, (locator a S).eval (a p) ∈ P ∨ (locator a S).eval (a m) ∈ M)
    (hp : P.card*g ≤ Fintype.card J) (hm : M.card*g ≤ Fintype.card J)
    (hreserve : P.card*g+M.card*g+(Fintype.card J-1) ≤ 2*Fintype.card J ∨
      ∃ z : I, z ≠ p ∧ z ≠ m ∧ ∀ S ∈ family, z ∉ S) :
    (family.card : ℕ∞) ≤ Lambda (ReedSolomon.code D (b*Fintype.card J) : Set (I × J → F))
      (((Fintype.card (I × J) - ((b+1)*Fintype.card J + (Fintype.card J-1) + g) : ℕ) : ℝ)
        / Fintype.card (I × J)) := by
  obtain ⟨R,hpR,hmR,dis,total⟩ := reserve_of_or p m hpm family (fun S hs => (hS S hs).2)
    _ _ _ hp hm hreserve
  exact locator_list_lower_reserved D a ha hpowers p m hpm R hpR hmR P M family c b g hb
    (fun S hs => ⟨(hS S hs).1,dis S hs⟩) hconst hanchor hp hm total

/-- Reserving a commonly missed fiber leaves both anchors fully available. A count
before restriction suffices for a strict lower bound on the actual scalar list. -/
theorem locator_exceeds_by_avoidance (D : I × J ↪ F) (a : I ↪ F) (ha : ∀ i, a i ≠ 0)
    (hpowers : ∀ x, D x ^ Fintype.card J = a x.1) (p m : I) (hpm : p ≠ m)
    (P M : Finset F) (family : Finset (Finset I)) (c : F) (b g B : ℕ) (hb : 0 < b)
    (hS : ∀ S ∈ family, S.card = b+1 ∧ p ∉ S ∧ m ∉ S)
    (hconst : ∀ S ∈ family, (locator a S).eval 0 = c)
    (hanchor : ∀ S ∈ family, (locator a S).eval (a p) ∈ P ∨ (locator a S).eval (a m) ∈ M)
    (hp : P.card*g ≤ Fintype.card J) (hm : M.card*g ≤ Fintype.card J)
    (hcount : (Fintype.card I-2)*B < family.card*(Fintype.card I-2-(b+1))) :
    (B : ℕ∞) < Lambda (ReedSolomon.code D (b*Fintype.card J) : Set (I × J → F))
      (((Fintype.card (I × J) - ((b+1)*Fintype.card J + (Fintype.card J-1) + g) : ℕ) : ℝ)
        / Fintype.card (I × J)) := by
  classical
  let ordinary := ((univ : Finset I).erase p).erase m
  have hord : ordinary.card = Fintype.card I-2 := by
    simp [ordinary, card_erase_of_mem, hpm.symm]
    omega
  rw [← hord] at hcount
  have hnonempty : ordinary.Nonempty := by
    rw [← card_pos]
    by_contra! he
    simp [Nat.eq_zero_of_le_zero he] at hcount
  obtain ⟨z,hz,havg⟩ := exists_avoided_fiber ordinary hnonempty family (b+1)
    (fun S hs => (hS S hs).1.le)
  let kept := family.filter fun S => z ∉ S
  have hk : B < kept.card := by
    by_contra! he
    exact (not_lt_of_ge (havg.trans (Nat.mul_le_mul_left ordinary.card he))) hcount
  have hsub : kept ⊆ family := filter_subset _ _
  have hzmem := mem_erase.mp hz
  have lower := locator_list_lower_with_reserve D a ha hpowers p m hpm P M kept c b g hb
    (fun S hs => hS S (hsub hs)) (fun S hs => hconst S (hsub hs))
    (fun S hs => hanchor S (hsub hs)) hp hm
    (.inr ⟨z, (mem_erase.mp hzmem.2).1, hzmem.1, fun _ hs => (mem_filter.mp hs).2⟩)
  exact (show (B : ℕ∞) < kept.card by exact_mod_cast hk).trans_le lower

/-- Without restrictions on the anchor values, pigeonholing the quotient product
still yields a concrete bad ball at the baseline lifted radius. -/
theorem exceeds_of_product (D : I × J ↪ F) (a : I ↪ F)
    (H : Subgroup Fˣ) [Fintype H] (z : I → H) (hz : ∀ i, a i = ((z i : Fˣ) : F))
    (hpowers : ∀ x, D x ^ Fintype.card J = a x.1) (p m : I) (hpm : p ≠ m)
    (b B : ℕ) (hb : 0 < b)
    (hcount : Fintype.card H * B < (Fintype.card I - 2).choose (b+1)) :
    (B : ℕ∞) < Lambda (ReedSolomon.code D (b*Fintype.card J) : Set (I × J → F))
      (((Fintype.card (I × J) - ((b+1)*Fintype.card J + (Fintype.card J-1)) : ℕ) : ℝ)
        / Fintype.card (I × J)) := by
  classical
  let ordinary := ((univ : Finset I).erase p).erase m
  have hord : ordinary.card = Fintype.card I-2 := by
    simp [ordinary, card_erase_of_mem, hpm.symm]
    omega
  let sets := ordinary.powersetCard (b+1)
  let key (S : Finset I) : H := ∏ i ∈ S, z i
  obtain ⟨k,_,hpop⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := sets) (t := (univ : Finset H)) (f := key) (fun _ _ => mem_univ _)
    (show univ.card * B < sets.card by simpa [sets,hord] using hcount)
  let family := sets.filter fun S => key S = k
  let c := (-1:F)^(b+1) * ((k : Fˣ) : F)
  have hsize (S : Finset I) (hs : S ∈ family) := mem_powersetCard.mp (mem_filter.mp hs).1
  have hS (S : Finset I) (hs : S ∈ family) : S.card = b+1 ∧ p ∉ S ∧ m ∉ S := by
    have hsub := (hsize S hs).1
    refine ⟨(hsize S hs).2, fun he => ?_, fun he => ?_⟩
    · exact notMem_erase _ _ (mem_erase.mp (hsub he)).2
    · exact notMem_erase _ _ (hsub he)
  have hconst (S : Finset I) (hs : S ∈ family) : (locator a S).eval 0 = c := by
    have he := congrArg ((Units.coeHom F).comp H.subtype) (mem_filter.mp hs).2
    change ((Units.coeHom F).comp H.subtype) (∏ i ∈ S, z i) = _ at he
    rw [map_prod] at he
    simpa [locator, eval_prod, Finset.prod_neg, (hS S hs).1, hz, c] using
      congrArg (fun u : F => (-1)^(b+1)*u) he
  let plus := family.image fun S => (locator a S).eval (a p)
  have lower := locator_list_lower D a (fun i => hz i ▸ Units.ne_zero _) hpowers p m hpm plus ∅ family c b 0
    hb hS hconst (fun S hs => Or.inl (mem_image_of_mem _ hs)) (by simp) (by simp) (by simp; omega)
  exact (show (B : ℕ∞) < family.card by exact_mod_cast hpop).trans_le (by simpa using lower)

/-- The unconditioned fixed-product construction on a cyclic subgroup, for every
positive interleaving width and every budget below its quotient pigeonhole count. -/
theorem cyclic_exceeds [Fintype F] {r h b B : ℕ} (hr : 2 ≤ r) (hh : 0 < h) (hb : 0 < b)
    (g : Fˣ) (hg : orderOf g = h*r) (hcount : r*B < (r-2).choose (b+1))
    (width : ℕ) (hw : 0 < width) :
    (B : ℕ∞) < Lambda (interleavedCodeSet (κ := Fin width)
      (ReedSolomon.code (ReservedFiberList.cyclicDomain g hg) (b*h) : Set (Fin r × Fin h → F)))
        (((r*h-((b+1)*h+(h-1)) : ℕ) : ℝ)/(r*h : ℕ)) := by
  classical
  let : NeZero h := ⟨hh.ne'⟩
  let D := ReservedFiberList.cyclicDomain g hg
  let a := ReservedFiberList.cyclicLabels hh g hg
  let H := Subgroup.zpowers (g^h)
  let z (i : Fin r) : H := ⟨(g^h)^i.val, Subgroup.npow_mem_zpowers _ _⟩
  have hz (i : Fin r) : a i = ((z i : Fˣ) : F) := by
    change ((g^(h*i.val) : Fˣ) : F) = ↑((g^h)^i.val)
    rw [pow_mul]
  have hc : Fintype.card H = r := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (Subgroup.zpowers (g^h)) = r
    rw [Nat.card_zpowers, orderOf_pow, hg,
      Nat.gcd_eq_right (dvd_mul_right h r), Nat.mul_div_cancel_left _ hh]
  let p : Fin r := ⟨0, by omega⟩
  let m : Fin r := ⟨1, by omega⟩
  have hbase := exceeds_of_product D a H z hz (ReservedFiberList.cyclicDomain_pow hh g hg)
    p m (by intro he; have := congrArg Fin.val he; simp [p,m] at this) b B hb
    (by simpa [hc] using hcount)
  let rep (x : F) : Fin width → F := fun _ => x
  have hrp : Function.Injective rep := fun x y he => congrFun he ⟨0,hw⟩
  apply lt_of_lt_of_le _ (Lambda_le_of_injective_comp (e := rep) hrp
    (C := (ReedSolomon.code D (b*h) : Set (Fin r × Fin h → F)))
    (D := interleavedCodeSet (κ := Fin width) (ReedSolomon.code D (b*h) : Set (Fin r × Fin h → F)))
    (fun _ hc _ => hc) _)
  simpa [Fintype.card_prod] using hbase

#print axioms locator_exceeds_by_avoidance
#print axioms exists_avoided_fiber
#print axioms locator_list_lower_with_reserve
#print axioms cyclic_exceeds
#print axioms exceeds_of_product
#print axioms locator_list_lower_reserved
#print axioms locator_list_lower
#print axioms list_lower
end ProximityGap.TwoAnchorListWitness

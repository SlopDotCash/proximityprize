/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius
import ArkLib.Data.CodingTheory.ListDecodability
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.FieldTheory.Finiteness

/-! # A center-free rank test for interleaved lists

For an ordered list prescribe an agreement support for each member. At coordinates
shared by two supports the two scalar codewords must agree. Each row of an
interleaving lies in the same linear solution space. Inclusion–exclusion removes
tuples whose interleaved codewords coincide, imposing each additional collision
as homogeneous linear equations. The resulting count depends only on dimensions
of explicitly defined subspaces over the base field.
-/

namespace ProximityGap.ListSupportRank

open Code Finset

variable {K I : Type*} [Field K] [Fintype K] [Fintype I] {L : ℕ}

/-- The homogeneous overlap equations for an ordered family of scalar codewords. -/
def compatible (C : Submodule K (I → K)) (S : Fin L → Finset I) :
    Submodule K (Fin L → C) where
  carrier := {z | ∀ a b i, i ∈ S a → i ∈ S b → (z a : I → K) i = (z b : I → K) i}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy a b i ha hb
    exact congrArg₂ (· + ·) (hx a b i ha hb) (hy a b i ha hb)
  smul_mem' := by
    intro r x hx a b i ha hb
    exact congrArg (r • ·) (hx a b i ha hb)

/-- On top of the overlap equations, identify every pair of codewords indexed by an edge. -/
def collisions (C : Submodule K (I → K)) (S : Fin L → Finset I)
    (T : Finset (Fin L × Fin L)) : Submodule K (compatible C S) where
  carrier := {z | ∀ e ∈ T, z.val e.1 = z.val e.2}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy e he
    exact congrArg₂ (· + ·) (hx e he) (hy e he)
  smul_mem' := by
    intro r x hx e he
    exact congrArg (r • ·) (hx e he)

/-- Unordered pairs, oriented by the order on list indices. -/
def pairs (L : ℕ) : Finset (Fin L × Fin L) :=
  univ.filter fun p => p.1 < p.2

/-- Signed rank sum for distinct compatible ordered interleaved codewords. -/
noncomputable def rankCount (C : Submodule K (I → K)) (S : Fin L → Finset I) (m : ℕ) : ℤ :=
  ∑ T ∈ (pairs L).powerset, (-1 : ℤ) ^ T.card *
    (Fintype.card K : ℤ) ^ (Module.finrank K (collisions C S T) * m)

private noncomputable def bad (C : Submodule K (I → K)) (S : Fin L → Finset I)
    (m : ℕ) (e : Fin L × Fin L) : Finset (Fin m → compatible C S) := by
  classical
  exact univ.filter fun z => ∀ j, (z j).val e.1 = (z j).val e.2

open Classical in
private theorem intersection_card (C : Submodule K (I → K)) (S : Fin L → Finset I)
    (m : ℕ) (T : Finset (Fin L × Fin L)) :
    (T.inf (bad C S m)).card = Fintype.card K ^ (Module.finrank K (collisions C S T) * m) := by
  classical
  let equiv : ↥(T.inf (bad C S m)) ≃ (Fin m → collisions C S T) := {
    toFun z j := ⟨z.val j, fun e he => by
      have h := Finset.mem_inf.mp z.property e he
      exact (Finset.mem_filter.mp h).2 j⟩
    invFun v := ⟨fun j => (v j).val, Finset.mem_inf.mpr fun e he =>
      Finset.mem_filter.mpr ⟨mem_univ _, fun j => (v j).property e he⟩⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [← Fintype.card_coe, Fintype.card_congr equiv, Fintype.card_fun, Fintype.card_fin, pow_mul]
  have hc : Fintype.card (collisions C S T) =
      Fintype.card K ^ Module.finrank K (collisions C S T) := by
    let _ : AddCommGroup ↥(compatible C S) := (compatible C S).addCommGroup
    let _ : AddCommGroup ↥(collisions C S T) := (collisions C S T).addCommGroup
    exact Module.card_eq_pow_finrank (K := K) (V := ↥(collisions C S T))
  rw [hc]

omit [Fintype I] in
/-- Positivity precisely detects whether the overlap pattern supports a list of distinct words. -/
theorem rankCount_pos_iff [Finite I] (C : Submodule K (I → K)) (S : Fin L → Finset I) (m : ℕ) :
    0 < rankCount C S m ↔ ∃ z : Fin m → compatible C S,
      Function.Injective (fun a j => (z j).val a) := by
  classical
  let _ := Fintype.ofFinite I
  let good := (pairs L).inf fun e => (bad C S m e)ᶜ
  have hcount : (good.card : ℤ) = rankCount C S m := by
    rw [Finset.inclusion_exclusion_card_inf_compl (pairs L) (bad C S m)]
    unfold rankCount
    apply Finset.sum_congr rfl
    intro T _
    rw [intersection_card C S m T, Nat.cast_pow]
  rw [← hcount, Int.natCast_pos, Finset.card_pos]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, fun {a b} hab => ?_⟩
    by_contra h
    have hbad {a b : Fin L} (hlt : a < b) (hEq : ∀ j, (z j).val a = (z j).val b) : False := by
      have hn := Finset.mem_inf.mp hz (a,b) (Finset.mem_filter.mpr ⟨mem_univ _, hlt⟩)
      exact (Finset.mem_compl.mp hn) (Finset.mem_filter.mpr ⟨mem_univ _, hEq⟩)
    rcases lt_or_gt_of_ne h with hlt | hgt
    · exact hbad hlt (congrFun hab)
    · exact hbad hgt (fun j => (congrFun hab j).symm)
  · rintro ⟨z, hz⟩
    refine ⟨z, Finset.mem_inf.mpr fun e he => Finset.mem_compl.mpr fun hb => ?_⟩
    have hlt : e.1 < e.2 := (Finset.mem_filter.mp he).2
    exact hlt.ne (hz (funext (Finset.mem_filter.mp hb).2))

/-- An oversized list is equivalent to a positive rank sum on a family of supports of the
specified size. This holds for any finite linear code, including zero interleaving width. -/
theorem lambda_exceeds_iff (C : Submodule K (I → K)) (m B t : ℕ) (hn : 0 < Fintype.card I) :
    (B : ℕ∞) < Lambda (interleavedCodeSet (κ := Fin m) (C : Set (I → K)))
      (1 - (t : ℝ) / Fintype.card I) ↔
    ∃ S : Fin (B + 1) → Finset I, (∀ a, (S a).card = t) ∧ 0 < rankCount C S m := by
  classical
  let D : Set (I → Fin m → K) := interleavedCodeSet (κ := Fin m) (C : Set (I → K))
  let r := 1 - (t : ℝ) / Fintype.card I
  have overcrowded : (B : ℕ∞) < Lambda D r ↔
      ∃ y, Nonempty (Fin (B + 1) ↪ closeCodewordsRel D y r) := by
    rw [← not_le, Lambda_le_iff_forall_ncard_le]
    simp only [Set.toFinite, true_and, not_forall, not_le,
      Function.Embedding.nonempty_iff_card_le, Fintype.card_fin,
      Set.fintypeCard_eq_ncard, Nat.succ_le_iff]
  rw [overcrowded]
  constructor
  · rintro ⟨y, ⟨l⟩⟩
    let w := fun a => (l a).val
    have hw (a) := mem_closeCodewordsRel_iff.mp (l a).property
    have hsize (a) : t ≤ (univ.filter fun i => w a i = y i).card := by
      have h := (relHammingDist_le_one_sub_div_iff hn).mp (hw a).2
      exact_mod_cast h
    choose S hsub hcard using fun a => Finset.exists_subset_card_eq (hsize a)
    refine ⟨S, hcard, (rankCount_pos_iff C S m).mpr ?_⟩
    let z (j : Fin m) : compatible C S :=
      ⟨fun a => ⟨fun i => w a i j, (hw a).1 j⟩, fun a b i ha hb => by
        exact congrFun (((mem_filter.mp (hsub a ha)).2).trans
          ((mem_filter.mp (hsub b hb)).2).symm) j⟩
    refine ⟨z, fun {a b} heq => l.injective (Subtype.ext ?_)⟩
    funext i j
    exact congrFun (congrArg Subtype.val (congrFun heq j)) i
  · rintro ⟨S, hcard, hpos⟩
    obtain ⟨z, hinj⟩ := (rankCount_pos_iff C S m).mp hpos
    let w (a : Fin (B + 1)) (i : I) (j : Fin m) := ((z j).val a : I → K) i
    let y (i : I) : Fin m → K := if h : ∃ a, i ∈ S a then w h.choose i else 0
    have hag {a i} (ha : i ∈ S a) : w a i = y i := by
      have hex : ∃ b, i ∈ S b := ⟨a, ha⟩
      dsimp [y]
      rw [dite_eq_left hex]
      funext j
      exact (z j).property a hex.choose i ha hex.choose_spec
    have hmem (a) : w a ∈ closeCodewordsRel D y r := by
      apply mem_closeCodewordsRel_iff.mpr
      refine ⟨fun j => ((z j).val a).property, (relHammingDist_le_one_sub_div_iff hn).mpr ?_⟩
      have hle : t ≤ (univ.filter fun i => w a i = y i).card := by
        rw [← hcard a]
        exact Finset.card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, hag hi⟩
      exact_mod_cast hle
    refine ⟨y, ⟨⟨fun a => ⟨w a, hmem a⟩, fun {a b} heq => hinj ?_⟩⟩⟩
    funext j
    apply Subtype.ext
    funext i
    exact congrFun (congrFun (congrArg Subtype.val heq) i) j

/-- Exact interleaved RS safety at an integer agreement threshold, for every supplied
injection, in particular every multiplicative coset used by the prize. -/
theorem rs_safe_iff (α : I ↪ K) (k m B t : ℕ) (hn : 0 < Fintype.card I) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code α k : Set (I → K)))
      (1 - (t : ℝ) / Fintype.card I) ≤ (B : ℕ∞) ↔
    ∀ S : Fin (B + 1) → Finset I, (∀ a, (S a).card = t) →
      rankCount (ReedSolomon.code α k) S m ≤ 0 := by
  rw [← not_lt, lambda_exceeds_iff (ReedSolomon.code α k) m B t hn]
  push Not
  rfl

open scoped NNReal ENNReal in
/-- The sponsor's real product gives the natural budget in the rank test, for every finite
nonnegative tolerance. This comparison even covers an infinite worst-case list size. -/
theorem lambda_le_floor_iff {A : Type*} (C : Set (I → A)) (r : ℝ) (ε : ℝ≥0) :
    (Lambda C r : ℝ≥0∞) ≤ (ε : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞) ↔
      Lambda C r ≤ (⌊ε * (Fintype.card K : ℝ≥0)⌋₊ : ℕ∞) := by
  rw [← ENNReal.coe_natCast, ← ENNReal.coe_mul]
  generalize Lambda C r = L
  induction L using ENat.recTopCoe with
  | top => simp only [ENat.toENNReal_top, top_le_iff, ENNReal.coe_ne_top, ENat.natCast_ne_top]
  | coe n =>
    simpa only [ENat.toENNReal_coe, ← ENNReal.coe_natCast, ENNReal.coe_le_coe,
      ENat.natCast_le_natCast] using
        (Nat.le_floor_iff (a := ε * (Fintype.card K : ℝ≥0)) (n := n) (by positivity)).symm

/-- Evaluate coefficient vectors bijectively as RS words when the degree bound fits the domain. -/
private noncomputable def encoder (α : I ↪ K) (k : ℕ) (hk : k ≤ Fintype.card I) :
    (Fin k → K) ≃ₗ[K] ReedSolomon.code α k := by
  let _ : FiniteDimensional K (Polynomial.degreeLT K k) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv K k).symm
  let ev : Polynomial.degreeLT K k →ₗ[K] ReedSolomon.code α k :=
    (ReedSolomon.evalOnPoints α).submoduleMap _
  have hs : Function.Surjective ev := LinearMap.submoduleMap_surjective _ _
  have hd : Module.finrank K (Polynomial.degreeLT K k) = Module.finrank K (ReedSolomon.code α k) :=
    (Polynomial.finrank_degreeLT_n k).trans (ReedSolomon.dim_eq_deg_of_le (α := α) hk).symm
  exact (Polynomial.degreeLTEquiv K k).symm.trans (LinearEquiv.ofBijective ev
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hs, hs⟩)

omit [Fintype K] in
private theorem encoder_apply (α : I ↪ K) (k : ℕ) (hk : k ≤ Fintype.card I)
    (x : Fin k → K) (i : I) :
    ((encoder α k hk x : ReedSolomon.code α k) : I → K) i = ∑ j, x j * α i ^ (j : ℕ) := by
  let p := (Polynomial.degreeLTEquiv K k).symm x
  change p.val.eval (α i) = _
  simpa [p] using Polynomial.eval_eq_sum_degreeLTEquiv p.property (α i)

/-- Each row of the interpolation system subtracts two evaluations at the same domain point.
Overlap positions and the requested whole-word collisions select its nonzero rows. -/
noncomputable def vandermonde (α : I ↪ K) (k : ℕ) (S : Fin L → Finset I)
    (T : Finset (Fin L × Fin L)) :
    (Fin L → Fin k → K) →ₗ[K] ((Fin L × Fin L × I) → K) := by
  classical
  let evaluation (a : Fin L) (i : I) : (Fin L → Fin k → K) →ₗ[K] K :=
    ∑ j : Fin k, (α i ^ (j : ℕ)) •
      ((LinearMap.proj (R := K) (φ := fun _ : Fin k => K) j).comp
        (LinearMap.proj (R := K) (φ := fun _ : Fin L => Fin k → K) a))
  exact LinearMap.pi fun e =>
    if ((e.2.2 ∈ S e.1 ∧ e.2.2 ∈ S e.2.1) ∨ (e.1, e.2.1) ∈ T) then
      evaluation e.1 e.2.2 - evaluation e.2.1 e.2.2 else 0

omit [Fintype K] in
private theorem mem_vandermonde_ker (α : I ↪ K) (k : ℕ) (hk : k ≤ Fintype.card I)
    (S : Fin L → Finset I) (T : Finset (Fin L × Fin L)) (x : Fin L → Fin k → K) :
    x ∈ (vandermonde α k S T).ker ↔ ∀ a b i, (i ∈ S a ∧ i ∈ S b) ∨ (a,b) ∈ T →
      ((encoder α k hk (x a) : ReedSolomon.code α k) : I → K) i =
      ((encoder α k hk (x b) : ReedSolomon.code α k) : I → K) i := by
  classical
  rw [LinearMap.mem_ker, funext_iff]
  simp only [Prod.forall, encoder_apply, vandermonde, LinearMap.pi_apply, Pi.zero_apply]
  constructor
  · intro h a b i hi
    simpa [hi, LinearMap.sub_apply, sub_eq_zero, LinearMap.sum_apply, mul_comm] using h a b i
  · intro h a b i
    by_cases hi : (i ∈ S a ∧ i ∈ S b) ∨ (a,b) ∈ T
    · simpa [hi, LinearMap.sub_apply, sub_eq_zero, LinearMap.sum_apply, mul_comm] using h a b i hi
    · simp [hi]

omit [Fintype K] in
/-- The linear space in every term of the rank sum is the kernel of the displayed
block Vandermonde system on coefficient arrays. -/
theorem nullity_eq (α : I ↪ K) (k : ℕ) (hk : k ≤ Fintype.card I) (S : Fin L → Finset I)
    (T : Finset (Fin L × Fin L)) :
    Module.finrank K (collisions (ReedSolomon.code α k) S T) =
      Module.finrank K (vandermonde α k S T).ker := by
  let E := encoder α k hk
  let decode (v : (vandermonde α k S T).ker) : collisions (ReedSolomon.code α k) S T :=
    ⟨⟨fun a => E (v.val a), fun a b i ha hb =>
      (mem_vandermonde_ker α k hk S T v.val).mp v.property a b i (Or.inl ⟨ha,hb⟩)⟩,
      fun e he => Subtype.ext (funext fun i =>
        (mem_vandermonde_ker α k hk S T v.val).mp v.property e.1 e.2 i (Or.inr he))⟩
  let encode (u : collisions (ReedSolomon.code α k) S T) : (vandermonde α k S T).ker :=
    ⟨fun a => E.symm (u.val.val a), (mem_vandermonde_ker α k hk S T _).mpr (by
      intro a b i h
      change ((E (E.symm _)).val i) = ((E (E.symm _)).val i)
      rw [E.apply_symm_apply, E.apply_symm_apply]
      obtain ⟨ha,hb⟩ | he := h
      · exact u.val.property a b i ha hb
      · exact congrFun (congrArg Subtype.val (u.property (a,b) he)) i)⟩
  let e : (vandermonde α k S T).ker ≃ₗ[K] collisions (ReedSolomon.code α k) S T := {
    toFun := decode
    invFun := encode
    left_inv v := Subtype.ext (funext fun a => E.symm_apply_apply (v.val a))
    right_inv u := Subtype.ext (Subtype.ext (funext fun a => E.apply_symm_apply (u.val.val a)))
    map_add' x y := Subtype.ext (Subtype.ext (funext fun a => E.map_add _ _))
    map_smul' c x := Subtype.ext (Subtype.ext (funext fun a => E.map_smul _ _)) }
  exact e.finrank_eq.symm

/-- A received-word-free and codeword-free test on the supplied evaluation points.
The only indices in the test are supports, pairs of list members, and matrix entries. -/
theorem rs_vandermonde_safe_iff (α : I ↪ K) (k m B t : ℕ) (hn : 0 < Fintype.card I)
    (hk : k ≤ Fintype.card I) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code α k : Set (I → K)))
      (1 - (t : ℝ) / Fintype.card I) ≤ (B : ℕ∞) ↔
    ∀ S : Fin (B + 1) → Finset I, (∀ a, (S a).card = t) →
      (∑ T ∈ (pairs (B + 1)).powerset, (-1 : ℤ) ^ T.card *
        (Fintype.card K : ℤ) ^ (Module.finrank K (vandermonde α k S T).ker * m)) ≤ 0 := by
  simpa only [rankCount, nullity_eq α k hk] using rs_safe_iff α k m B t hn

end ProximityGap.ListSupportRank

#print axioms ProximityGap.ListSupportRank.rankCount_pos_iff
#print axioms ProximityGap.ListSupportRank.rs_safe_iff
#print axioms ProximityGap.ListSupportRank.lambda_le_floor_iff
#print axioms ProximityGap.ListSupportRank.nullity_eq
#print axioms ProximityGap.ListSupportRank.rs_vandermonde_safe_iff

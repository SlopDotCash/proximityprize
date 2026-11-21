/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FiniteGaussianNullity
import ArkLib.Research.ProximityGap.Frontier.SimultaneousSupportParity
import ArkLib.Research.ProximityGap.Frontier.ExactSizeMcaSupport

/-! # Executable simultaneous MCA support tests

Use an explicit ordering of the domain and an enumeration of the field labels.
Each support is tested by Lagrange interpolation on its first available anchors.
The matrix columns are the two received rows. Adding both separate-row equations
for a selected label tests the dimension lost by imposing joint agreement.
-/

namespace ProximityGap.SimultaneousSupportGaussian

open Finset FiniteGaussianNullity SimultaneousSupportParity
open scoped NNReal ENNReal

variable {F I : Type} [Field F] [DecidableEq F] [DecidableEq I] {n : ℕ}

/-- The supplied coordinates in their presentation order. -/
def sites (E : Fin n ≃ I) : List I := (List.finRange n).map E

omit [DecidableEq I] in
private theorem mem_sites (E : Fin n ≃ I) (i : I) : i ∈ sites E :=
  List.mem_map.mpr ⟨E.symm i, List.mem_finRange _, E.apply_symm_apply _⟩

/-- A list of the elements of a finite set, in the order of a covering enumeration. -/
def selected {A : Type*} [DecidableEq A] (l : List A) (s : Finset A) : List s :=
  l.filterMap fun a => if h : a ∈ s then some ⟨a,h⟩ else none

private theorem mem_selected {A : Type*} [DecidableEq A] (l : List A) (hl : ∀ a, a ∈ l)
    (s : Finset A) (a : s) : a ∈ selected l s := by
  apply List.mem_filterMap.mpr
  exact ⟨a.val, hl _, by simp [a.property]⟩

/-- The first at most k sites in the support are its deterministic interpolation anchors. -/
def anchors (E : Fin n ≃ I) (k : ℕ) (s : Finset I) : Finset I :=
  (((sites E).filter (· ∈ s)).take k).toFinset

private theorem anchors_valid (E : Fin n ≃ I) (k : ℕ) (s : Finset I) :
    Anchors k s (anchors E k s) := by
  let A := (sites E).filter (· ∈ s)
  have hn : A.Nodup := ((List.nodup_finRange n).map E.injective).filter _
  have hA : A.toFinset = s := by ext i; simp [A, mem_sites]
  have ht : (A.take k).toFinset.card = min k A.length := by
    rw [List.toFinset_card_of_nodup hn.take, List.length_take]
  refine ⟨fun i hi => ?_, ht.le.trans (min_le_left _ _), ?_⟩
  · exact hA ▸ List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hi))
  · by_cases h : k ≤ A.length
    · exact Or.inl (ht.trans (min_eq_left h))
    · right
      change (A.take k).toFinset = s
      rw [List.take_of_length_le (le_of_not_ge h), hA]

/-- Explicit Lagrange weights computed entirely in the supplied field. -/
def weight (D : I ↪ F) (T : Finset I) (i j : I) : F :=
  ∏ u ∈ T.erase j, (D j - D u)⁻¹ * (D i - D u)

omit [DecidableEq F] in
private theorem weight_eq (D : I ↪ F) (T : Finset I) (i j : I) :
    weight D T i j = (Lagrange.basis T D j).eval (D i) := by
  simp [weight, Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_prod]

/-- Coefficient of site j in the residual at site i. -/
def coefficient (D : I ↪ F) (T : Finset I) (i j : I) : F :=
  (if j = i then 1 else 0) - (if j ∈ T then weight D T i j else 0)

omit [DecidableEq F] in
private theorem parity_sum [Fintype I] (D : I ↪ F) (s T : Finset I) (i : s) (w : I → F) :
    ∑ j, coefficient D T i j * w j = parity D s T w i := by
  classical
  rw [parity_apply]
  simp only [coefficient, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  simp [weight_eq, mul_comm]

private def unpack (E : Fin n ≃ I) : (Fin (n + n) → F) ≃ ((I → F) × (I → F)) where
  toFun x := (fun i => x ((E.symm i).castAdd n), fun i => x (Fin.natAdd n (E.symm i)))
  invFun y := Fin.append (y.1 ∘ E) (y.2 ∘ E)
  left_inv x := by
    simp only [Function.comp_def, E.symm_apply_apply]
    exact Fin.append_castAdd_natAdd
  right_inv y := by
    ext <;> simp only [Fin.append_left, Fin.append_right, Function.comp_apply, E.apply_symm_apply]

/-- A folded parity row with row multipliers u and v. -/
def row (E : Fin n ≃ I) (D : I ↪ F) (T : Finset I) (i : I) (u v : F) : Fin (n + n) → F :=
  cache (Fin.append (fun j => u * coefficient D T i (E j))
    (fun j => v * coefficient D T i (E j)))

omit [DecidableEq F] in
private theorem row_dot (E : Fin n ≃ I) (D : I ↪ F) (s T : Finset I) (i : s)
    (u v : F) (x : Fin (n + n) → F) :
    dot (row E D T i u v) x =
      u * parity D s T (unpack E x).1 i + v * parity D s T (unpack E x).2 i := by
  let _ := Fintype.ofEquiv (Fin n) E
  rw [← parity_sum, ← parity_sum, ← E.sum_comp, ← E.sum_comp]
  have hcache (r : Fin (n + n) → F) : cache r = r := by funext j; simp [cache]
  simp only [dot, row, hcache, Fin.sum_univ_add, Fin.append_left,
    Fin.append_right, unpack, Equiv.coe_fn_mk, E.symm_apply_apply, Finset.mul_sum, mul_assoc]

/-- All residual rows for one support and one direction. -/
def block (E : Fin n ≃ I) (D : I ↪ F) (s T : Finset I) (u v : F) : List (Fin (n + n) → F) :=
  (selected (sites E) s).map fun i : s => row E D T i.val u v

omit [DecidableEq F] in
private theorem block_iff (E : Fin n ≃ I) (D : I ↪ F) (s T : Finset I)
    (u v : F) (x : Fin (n + n) → F) :
    (∀ r ∈ block E D s T u v, dot r x = 0) ↔
      ∀ i : s, u * parity D s T (unpack E x).1 i + v * parity D s T (unpack E x).2 i = 0 := by
  constructor
  · intro h i
    rw [← row_dot]
    exact h _ (List.mem_map.mpr ⟨i, mem_selected _ (mem_sites E) _ i, rfl⟩)
  · intro h r hr
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
    exact (row_dot E D s T i u v x).trans (h i)

/-- Matrix for the selected folds; optionally append both ordinary row blocks at a label. -/
def grid (E : Fin n ≃ I) (labels : List F) (D : I ↪ F) (G : Finset F) (S T : G → Finset I)
    (joint : Option G) : List (Fin (n + n) → F) :=
  (selected labels G).flatMap (fun g => block E D (S g) (T g) 1 g.val) ++
    match joint with
    | none => []
    | some g => block E D (S g) (T g) 1 0 ++ block E D (S g) (T g) 0 1

/-- Executable dimension of a folded system, with an optional joint support. -/
def dimension (E : Fin n ≃ I) (labels : List F) (D : I ↪ F) (G : Finset F)
    (S T : G → Finset I) (joint : Option G) : ℕ :=
  nullity (n + n) (grid E labels D G S T joint)

/-- The mathematical subspace certified for either matrix choice. -/
noncomputable def target (D : I ↪ F) (G : Finset F) (S T : G → Finset I) :
    Option G → Submodule F ((I → F) × (I → F))
  | none => (folded D G S T).ker
  | some g => (folded D G S T).ker ⊓
      (parity D (S g) (T g)).ker.prod (parity D (S g) (T g)).ker

private theorem grid_iff (E : Fin n ≃ I) (labels : List F) (hl : ∀ g, g ∈ labels)
    (D : I ↪ F) (G : Finset F) (S T : G → Finset I) (joint : Option G)
    (x : Fin (n + n) → F) :
    (∀ r ∈ grid E labels D G S T joint, dot r x = 0) ↔ unpack E x ∈ target D G S T joint := by
  let A := (selected labels G).flatMap fun g : G => block E D (S g) (T g) 1 g.val
  have hA : (∀ r ∈ A, dot r x = 0) ↔ ∀ g, ∀ r ∈ block E D (S g) (T g) 1 g.val,
      dot r x = 0 := by
    constructor
    · intro h g r hr
      exact h r (List.mem_flatMap.mpr ⟨g, mem_selected _ hl _ _, hr⟩)
    · intro h r hr
      obtain ⟨g, _, hg⟩ := List.mem_flatMap.mp hr
      exact h g r hg
  have hfold : (∀ r ∈ A, dot r x = 0) ↔ unpack E x ∈ (folded D G S T).ker := by
    rw [hA, LinearMap.mem_ker, funext_iff]
    apply forall_congr' fun g => ?_
    rw [block_iff, funext_iff]
    apply forall_congr' fun i => ?_
    change _ ↔ parity D (S g) (T g) ((unpack E x).1 + g.val • (unpack E x).2) i = 0
    rw [map_add, map_smul]
    simp
  cases joint with
  | none =>
    change (∀ r ∈ A ++ [], dot r x = 0) ↔ _
    simpa only [List.append_nil, target] using hfold
  | some g =>
    let P := parity D (S g) (T g)
    change (∀ r ∈ A ++ (_ ++ _), dot r x = 0) ↔
      unpack E x ∈ (folded D G S T).ker ⊓ P.ker.prod P.ker
    simp only [List.forall_mem_append, hfold, block_iff, one_mul, zero_mul, zero_add, add_zero,
      Submodule.mem_inf, Submodule.mem_prod, LinearMap.mem_ker, funext_iff, Pi.zero_apply, P]

/-- Every reported dimension equals the independently defined folded or augmented nullity. -/
theorem dimension_eq [Finite F] (E : Fin n ≃ I) (labels : List F)
    (hl : ∀ g, g ∈ labels) (D : I ↪ F) (G : Finset F) (S T : G → Finset I) (joint : Option G) :
    dimension E labels D G S T joint = Module.finrank F (target D G S T joint) := by
  classical
  let _ := Fintype.ofFinite F
  let _ := Fintype.ofEquiv (Fin n) E
  let rows := grid E labels D G S T joint
  let W := target D G S T joint
  let equiv : Solutions rows ≃ W := {
    toFun := fun x => ⟨unpack E x.val, (grid_iff E labels hl D G S T joint _).mp x.property⟩
    invFun := fun y => ⟨(unpack E).symm y.val, (grid_iff E labels hl D G S T joint _).mpr
      (by simp)⟩
    left_inv x := Subtype.ext ((unpack E).symm_apply_apply x.val)
    right_inv y := Subtype.ext ((unpack E).apply_symm_apply y.val) }
  have hcard := Nat.card_congr equiv
  rw [card_solutions, Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card] at hcard
  exact Nat.pow_right_injective Fintype.one_lt_card hcard

/-- All supports at or above the prescribed number of agreements. -/
def profiles (E : Fin n ≃ I) (G : Finset F) (t : ℕ) : Finset (G → Finset I) :=
  Fintype.piFinset fun _ => (sites E).toFinset.powerset.filter fun s => t ≤ s.card

omit [Field F] in
private theorem mem_profiles (E : Fin n ≃ I) (G : Finset F) (t : ℕ) (S : G → Finset I) :
    S ∈ profiles E G t ↔ ∀ g, t ≤ (S g).card := by
  simp only [profiles, Fintype.mem_piFinset, mem_filter, mem_powerset]
  exact forall_congr' fun g =>
    ⟨And.right, fun h => ⟨fun i _ => List.mem_toFinset.mpr (mem_sites E i), h⟩⟩

/-- Does each individual joint augmentation cut the common folded kernel? -/
def allDrop (E : Fin n ≃ I) (labels : List F) (D : I ↪ F) (k : ℕ) (G : Finset F)
    (S : G → Finset I) : Bool :=
  let T := fun g => anchors E k (S g)
  let d := dimension E labels D G S T none
  decide (∀ g : G, dimension E labels D G S T (some g) < d)

/-- Some support profile gives a bad pair for all of the selected labels. -/
def violates (E : Fin n ≃ I) (labels : List F) (D : I ↪ F) (k t : ℕ) (G : Finset F) : Bool :=
  decide ((profiles E G t).filter fun S => allDrop E labels D k G S = true).Nonempty

/-- Gaussian MCA safety test with the operational count budget and agreement threshold. -/
def mcaSafe (E : Fin n ≃ I) (labels : List F) (D : I ↪ F) (k B t : ℕ) : Bool :=
  !decide ((labels.toFinset.powersetCard (B + 1)).filter
    fun G => violates E labels D k t G = true).Nonempty

omit [Field F] in
private theorem label_mem (labels : List F) (hl : ∀ g, g ∈ labels) (B : ℕ) (G : Finset F) :
    G ∈ labels.toFinset.powersetCard (B + 1) ↔ G.card = B + 1 := by
  rw [mem_powersetCard]
  exact ⟨And.right, fun h => ⟨fun g _ => List.mem_toFinset.mpr (hl g), h⟩⟩

open SimultaneousSupportRank

private theorem allDrop_iff [Nonempty I] [Finite F] (E : Fin n ≃ I)
    (labels : List F) (hl : ∀ g, g ∈ labels) (D : I ↪ F) (k : ℕ) (G : Finset F)
    (S : G → Finset I) :
    allDrop E labels D k G S = true ↔ ∀ g,
      Module.finrank F ↥(space (ReedSolomon.code D k) G S ⊓
        jointSpace (ReedSolomon.code D k) (S g)) <
      Module.finrank F (space (ReedSolomon.code D k) G S) := by
  let _ := Fintype.ofEquiv (Fin n) E
  let T := fun g => anchors E k (S g)
  have hT (g) : Anchors k (S g) (T g) := anchors_valid E k (S g)
  change decide (∀ g, dimension E labels D G S T (some g) <
    dimension E labels D G S T none) = true ↔ _
  rw [decide_eq_true_eq]
  apply forall_congr' fun g => ?_
  rw [dimension_eq E labels hl, dimension_eq E labels hl]
  change Module.finrank F ↥((folded D G S T).ker ⊓
    (parity D (S g) (T g)).ker.prod (parity D (S g) (T g)).ker) <
      Module.finrank F (folded D G S T).ker ↔ _
  rw [ker_folded D G S T hT, ← joint_eq D (S g) (T g) (hT g)]

/-- Correctness at integer error radius e/n against canonical affine-line MCA error. -/
theorem mcaSafe_iff [Nonempty I] [Fintype I] [Fintype F] [SampleableType F] (E : Fin n ≃ I)
    (labels : List F) (hlabels : ∀ g, g ∈ labels) (D : I ↪ F) (k B e : ℕ) (_he : e ≤ n)
    (hn : 0 < n) :
    mcaSafe E labels D k B (n - e) = true ↔
      CoreDefinitions.mcaError (CoreDefinitions.AffineLineGenerator F) (ReedSolomon.code D k)
        ((e : ℝ) / n) ≤ (B : ℝ≥0∞) / Fintype.card F := by
  let δ : ℝ≥0 := (e : ℝ≥0) / n
  have hcard : Fintype.card I = n := (Fintype.card_congr E).symm.trans (Fintype.card_fin n)
  have hsize (s : Finset I) : (n - e ≤ s.card) ↔ (1 - δ) * Fintype.card I ≤ (s.card : ℝ≥0) := by
    have hn' : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
    rw [hcard, tsub_mul, one_mul, div_mul_cancel₀ _ hn']
    have hcast : ((n - e : ℕ) : ℝ≥0) = (n : ℝ≥0) - e := Nat.cast_tsub n e
    rw [← hcast, Nat.cast_le]
  change _ ↔ CoreDefinitions.mcaError _ _ (δ : ℝ) ≤ _
  rw [← not_lt, canonical_failure_iff (ReedSolomon.code D k) δ B]
  simp only [mcaSafe, Bool.not_eq_true', decide_eq_false_iff_not]
  apply not_congr
  simp only [Finset.Nonempty, mem_filter, violates, decide_eq_true_eq, label_mem labels hlabels,
    mem_profiles, allDrop_iff E labels hlabels, hsize, exists_prop]

/-- Enumerate the remaining labels directly after fixing the affine origin and scale. -/
def anchoredSets (labels : List F) : ℕ → Finset (Finset F)
  | 0 => {{0}}
  | B + 1 => (((labels.toFinset.erase 0).erase 1).powersetCard B).image
      fun U => insert 0 (insert 1 U)

private theorem mem_anchoredSets (labels : List F) (hl : ∀ g, g ∈ labels)
    (B : ℕ) (G : Finset F) :
    G ∈ anchoredSets labels B ↔ G.card = B + 1 ∧ 0 ∈ G ∧ (0 < B → 1 ∈ G) := by
  cases B with
  | zero =>
    simp only [anchoredSets, mem_singleton, Nat.zero_add, lt_self_iff_false, false_implies,
      and_true]
    constructor
    · rintro rfl
      simp
    · rintro ⟨h, hz⟩
      obtain ⟨a, rfl⟩ := card_eq_one.mp h
      have ha : (0 : F) = a := Finset.mem_singleton.mp hz
      rw [← ha]
  | succ B =>
    simp only [anchoredSets, mem_image, mem_powersetCard, Nat.succ_pos, true_implies]
    constructor
    · rintro ⟨U, ⟨hU, hc⟩, rfl⟩
      have h0 : (0 : F) ∉ U := fun h => notMem_erase _ _ ((mem_erase.mp (hU h)).2)
      have h1 : (1 : F) ∉ U := fun h => notMem_erase _ _ (hU h)
      simp [h0, h1, hc]
    · rintro ⟨hc, hz, ho⟩
      have ho' : (1 : F) ∈ G.erase 0 := mem_erase.mpr ⟨one_ne_zero, ho⟩
      refine ⟨(G.erase 0).erase 1, ⟨?_, ?_⟩, ?_⟩
      · intro x hx
        obtain ⟨h1, hx'⟩ := mem_erase.mp hx
        exact mem_erase.mpr ⟨h1, mem_erase.mpr ⟨(mem_erase.mp hx').1,
          List.mem_toFinset.mpr (hl x)⟩⟩
      · rw [card_erase_of_mem ho', card_erase_of_mem hz, hc]
        omega
      · rw [insert_erase ho', insert_erase hz]

/-- Search only fixed-size support assignments on normalized scalar sets. -/
def anchoredSafe (E : Fin n ≃ I) (labels : List F) (D : I ↪ F) (k B t : ℕ) : Bool :=
  let supports := (sites E).toFinset.powersetCard (max t (k + 1))
  decide (∀ G ∈ anchoredSets labels B,
    ∀ S ∈ (Fintype.piFinset fun _ : G => supports), allDrop E labels D k G S = false)

/-- The reduced search computes the canonical MCA budget predicate for the supplied domain. -/
theorem anchoredSafe_iff [Nonempty I] [Fintype I] [Fintype F] [SampleableType F]
    (E : Fin n ≃ I) (labels : List F) (hl : ∀ g, g ∈ labels) (D : I ↪ F)
    (k B e : ℕ) (hn : 0 < n) :
    anchoredSafe E labels D k B (n - e) = true ↔
      CoreDefinitions.mcaError (CoreDefinitions.AffineLineGenerator F) (ReedSolomon.code D k)
        ((e : ℝ) / n) ≤ (B : ℝ≥0∞) / Fintype.card F := by
  let δ : ℝ≥0 := (e : ℝ≥0) / n
  have hcard : Fintype.card I = n := (Fintype.card_congr E).symm.trans (Fintype.card_fin n)
  have hfloor : Fintype.card I - ⌊δ * Fintype.card I⌋₊ = n - e := by
    simp only [hcard, δ, div_mul_cancel₀ _ (by exact_mod_cast hn.ne' : (n : ℝ≥0) ≠ 0),
      Nat.floor_natCast]
  have hs (S : Finset I) : S ⊆ (sites E).toFinset :=
    fun i _ => List.mem_toFinset.mpr (mem_sites E i)
  change _ ↔ CoreDefinitions.mcaError _ _ (δ : ℝ) ≤ _
  rw [← not_lt, ExactSizeMcaSupport.anchored_failure_iff D k B δ]
  simp only [anchoredSafe, decide_eq_true_eq, mem_anchoredSets labels hl, Fintype.mem_piFinset,
    mem_powersetCard, hs, true_and, ← Bool.not_eq_true, allDrop_iff E labels hl, hfloor]
  constructor
  · intro hall ⟨G, hc, hz, ho, S, hS, hd⟩
    exact hall G ⟨hc, hz, ho⟩ S hS hd
  · intro h G ⟨hc, hz, ho⟩ S hS hd
    exact h ⟨G, hc, hz, ho, S, hS, hd⟩



end ProximityGap.SimultaneousSupportGaussian

#print axioms ProximityGap.SimultaneousSupportGaussian.dimension_eq
#print axioms ProximityGap.SimultaneousSupportGaussian.mcaSafe_iff

#print axioms ProximityGap.SimultaneousSupportGaussian.anchoredSafe_iff

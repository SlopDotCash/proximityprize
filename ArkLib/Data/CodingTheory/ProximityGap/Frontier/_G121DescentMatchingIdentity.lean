/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G95CardinalityDeepCapNoGo

/-!
# G121: the descent matching identity — exact cross-rung transfer

The recent counterexamples (`DCEnergyBound` false at `(n, p, r) = (64, 16778497, 5)`; positive
depth-five anomaly at an order-32 prime, G106) kill every *uniform* per-depth sign law.  What
survives an arbitrary counterexample is an exact identity.  This file proves one:

**Marking one matching position.**  For a rung-`(k+1)` equal-sum pair `(v, w)`, let
`matchCount (v, w) = #{(i, j) : v i = w j}`.  Removing a marked matching position from both
sides bijects onto (position pair) × (free common value) × (rung-`k` equal-sum pair):

```text
Σ_{(v,w) equal-sum, rung k+1} matchCount (v, w) = (k+1)² · #A · E_k(A)
Σ_{(v,w) all pairs,  rung k+1} matchCount (v, w) = (k+1)² · #A^(2k+1),
```

hence the **descent anomaly transfer** (in ℤ):

```text
q · Σ_eq matchCount − Σ_all matchCount = (k+1)² · #A · (q·E_k − #A^(2k)) ≥ 0,
```

nonnegative at EVERY prime and rung by the G95 pigeonhole floor — no sign law assumed.

**Full-depth invisibility.**  `matchCount (v, w) = 0` iff the two value bags are disjoint iff
the G83M cancellation depth is maximal (`= k+1`).  So the descent moment sees exactly the
non-maximal-depth sectors: all rung-`(k+1)` structure invisible to rung `k` lives in the
fully-disjoint sector.  This pins where genuinely new (non-descent) information sits at every
rung — the object the depth-five lanes (G111–G120) are attacking.

**Honest scope.**  Exact identities and an unconditional inequality; no bound on the
fully-disjoint sector itself (that is the wall).  CORE remains OPEN.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G121DescentMatchingIdentity

open Finset Fintype
open ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation
open ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo

variable {α : Type*} [DecidableEq α]

/-- The number of matching position pairs of an ordered pair of `r`-tuples. -/
def matchCount {r : ℕ} (y : (Fin r → α) × (Fin r → α)) : ℕ :=
  #{ij ∈ (univ : Finset (Fin r × Fin r)) | y.1 ij.1 = y.2 ij.2}

section Identities

variable [AddCancelCommMonoid α]

/-- The one-position slice of the equal-sum set at a fixed matching position pair `(i, j)`
bijects onto (free common value) × (rung-`k` equal-sum pairs). -/
theorem card_matchSlice (A : Finset α) (k : ℕ) (i j : Fin (k + 1)) :
    #{y ∈ energySet A (k + 1) | y.1 i = y.2 j} = A.card * Finset.addREnergy k A := by
  classical
  have key : #{y ∈ energySet A (k + 1) | y.1 i = y.2 j}
      = #(A ×ˢ energySet A k) := by
    refine Finset.card_bij'
      (fun y _ => (y.1 i, (Fin.removeNth i y.1, Fin.removeNth j y.2)))
      (fun z _ => (Fin.insertNth i z.1 z.2.1, Fin.insertNth j z.1 z.2.2))
      ?hi ?hj ?li ?ri
    case hi =>
      intro y hy
      have hy' := Finset.mem_filter.mp hy
      have hE := Finset.mem_filter.mp hy'.1
      have hprod := Finset.mem_product.mp hE.1
      have h1 : ∀ t, y.1 t ∈ A := fun t => Fintype.mem_piFinset.mp hprod.1 t
      have h2 : ∀ t, y.2 t ∈ A := fun t => Fintype.mem_piFinset.mp hprod.2 t
      have hsum : ∑ t, y.1 t = ∑ t, y.2 t := hE.2
      have hij : y.1 i = y.2 j := hy'.2
      refine Finset.mem_product.mpr ⟨h1 i, ?_⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Fintype.mem_piFinset.mpr (fun t => h1 _),
          Fintype.mem_piFinset.mpr (fun t => h2 _)⟩, ?_⟩
      have e1 : ∑ t, y.1 t = y.1 i + ∑ t, Fin.removeNth i y.1 t :=
        Fin.sum_univ_succAbove y.1 i
      have e2 : ∑ t, y.2 t = y.2 j + ∑ t, Fin.removeNth j y.2 t :=
        Fin.sum_univ_succAbove y.2 j
      apply add_left_cancel (a := y.1 i)
      calc
        y.1 i + ∑ t, Fin.removeNth i y.1 t = ∑ t, y.1 t := e1.symm
        _ = ∑ t, y.2 t := hsum
        _ = y.2 j + ∑ t, Fin.removeNth j y.2 t := e2
        _ = y.1 i + ∑ t, Fin.removeNth j y.2 t := by rw [hij]
    case hj =>
      intro z hz
      have hz' := Finset.mem_product.mp hz
      have hzA : z.1 ∈ A := hz'.1
      have hzE := Finset.mem_filter.mp hz'.2
      have hzprod := Finset.mem_product.mp hzE.1
      have hz1 : ∀ t, z.2.1 t ∈ A := fun t => Fintype.mem_piFinset.mp hzprod.1 t
      have hz2 : ∀ t, z.2.2 t ∈ A := fun t => Fintype.mem_piFinset.mp hzprod.2 t
      have hzsum : ∑ t, z.2.1 t = ∑ t, z.2.2 t := hzE.2
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
      · refine Fintype.mem_piFinset.mpr (fun t => ?_)
        rcases Fin.eq_self_or_eq_succAbove i t with h | ⟨u, rfl⟩
        · subst h; simpa using hzA
        · simpa [Fin.insertNth_apply_succAbove] using hz1 u
      · refine Fintype.mem_piFinset.mpr (fun t => ?_)
        rcases Fin.eq_self_or_eq_succAbove j t with h | ⟨u, rfl⟩
        · subst h; simpa using hzA
        · simpa [Fin.insertNth_apply_succAbove] using hz2 u
      · rw [Fin.sum_univ_succAbove _ i, Fin.sum_univ_succAbove _ j]
        simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
        rw [hzsum]
      · simp
    case li =>
      intro y hy
      have hy' := Finset.mem_filter.mp hy
      have hij : y.1 i = y.2 j := hy'.2
      have hfst : Fin.insertNth i (y.1 i) (Fin.removeNth i y.1) = y.1 :=
        Fin.insertNth_self_removeNth i y.1
      have hsnd : Fin.insertNth j (y.1 i) (Fin.removeNth j y.2) = y.2 := by
        rw [hij]
        exact Fin.insertNth_self_removeNth j y.2
      exact Prod.ext hfst hsnd
    case ri =>
      intro z hz
      simp [Fin.removeNth_insertNth, Fin.insertNth_apply_same]
  rw [key, Finset.card_product, card_energySet]

/-- **Descent matching identity (equal-sum side).**  The total matching moment over the
rung-`(k+1)` equal-sum set equals `(k+1)² · #A · E_k(A)`. -/
theorem sum_matchCount_energySet (A : Finset α) (k : ℕ) :
    ∑ y ∈ energySet A (k + 1), matchCount y
      = (k + 1) ^ 2 * (A.card * Finset.addREnergy k A) := by
  classical
  have hswap : ∑ y ∈ energySet A (k + 1), matchCount y
      = ∑ ij ∈ (univ : Finset (Fin (k + 1) × Fin (k + 1))),
          #{y ∈ energySet A (k + 1) | y.1 ij.1 = y.2 ij.2} := by
    unfold matchCount
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  rw [Finset.sum_congr rfl (fun ij _ => card_matchSlice A k ij.1 ij.2)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    smul_eq_mul, ← sq]

/-- The one-position slice of the full pair cube at a fixed position pair. -/
theorem card_matchSlice_cube (A : Finset α) (k : ℕ) (i j : Fin (k + 1)) :
    #{y ∈ (piFinset fun _ : Fin (k + 1) => A) ×ˢ (piFinset fun _ : Fin (k + 1) => A) |
        y.1 i = y.2 j}
      = A.card * A.card ^ (2 * k) := by
  classical
  have key : #{y ∈ (piFinset fun _ : Fin (k + 1) => A) ×ˢ
        (piFinset fun _ : Fin (k + 1) => A) | y.1 i = y.2 j}
      = #(A ×ˢ ((piFinset fun _ : Fin k => A) ×ˢ (piFinset fun _ : Fin k => A))) := by
    refine Finset.card_bij'
      (fun y _ => (y.1 i, (Fin.removeNth i y.1, Fin.removeNth j y.2)))
      (fun z _ => (Fin.insertNth i z.1 z.2.1, Fin.insertNth j z.1 z.2.2))
      ?hi ?hj ?li ?ri
    case hi =>
      intro y hy
      have hy' := Finset.mem_filter.mp hy
      have hprod := Finset.mem_product.mp hy'.1
      have h1 : ∀ t, y.1 t ∈ A := fun t => Fintype.mem_piFinset.mp hprod.1 t
      have h2 : ∀ t, y.2 t ∈ A := fun t => Fintype.mem_piFinset.mp hprod.2 t
      exact Finset.mem_product.mpr ⟨h1 i, Finset.mem_product.mpr
        ⟨Fintype.mem_piFinset.mpr (fun t => h1 _),
          Fintype.mem_piFinset.mpr (fun t => h2 _)⟩⟩
    case hj =>
      intro z hz
      have hz' := Finset.mem_product.mp hz
      have hzA : z.1 ∈ A := hz'.1
      have hz2' := Finset.mem_product.mp hz'.2
      have hz1 : ∀ t, z.2.1 t ∈ A := fun t => Fintype.mem_piFinset.mp hz2'.1 t
      have hz2 : ∀ t, z.2.2 t ∈ A := fun t => Fintype.mem_piFinset.mp hz2'.2 t
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, by simp⟩
      · refine Fintype.mem_piFinset.mpr (fun t => ?_)
        rcases Fin.eq_self_or_eq_succAbove i t with h | ⟨u, rfl⟩
        · subst h; simpa using hzA
        · simpa [Fin.insertNth_apply_succAbove] using hz1 u
      · refine Fintype.mem_piFinset.mpr (fun t => ?_)
        rcases Fin.eq_self_or_eq_succAbove j t with h | ⟨u, rfl⟩
        · subst h; simpa using hzA
        · simpa [Fin.insertNth_apply_succAbove] using hz2 u
    case li =>
      intro y hy
      have hy' := Finset.mem_filter.mp hy
      have hij : y.1 i = y.2 j := hy'.2
      have hfst : Fin.insertNth i (y.1 i) (Fin.removeNth i y.1) = y.1 :=
        Fin.insertNth_self_removeNth i y.1
      have hsnd : Fin.insertNth j (y.1 i) (Fin.removeNth j y.2) = y.2 := by
        rw [hij]
        exact Fin.insertNth_self_removeNth j y.2
      exact Prod.ext hfst hsnd
    case ri =>
      intro z hz
      simp [Fin.removeNth_insertNth, Fin.insertNth_apply_same]
  rw [key, Finset.card_product, Finset.card_product, card_piFinset_const, ← pow_add]
  congr 2
  omega

/-- **Descent matching identity (population side).** -/
theorem sum_matchCount_cube (A : Finset α) (k : ℕ) :
    ∑ y ∈ (piFinset fun _ : Fin (k + 1) => A) ×ˢ (piFinset fun _ : Fin (k + 1) => A),
        matchCount y
      = (k + 1) ^ 2 * (A.card * A.card ^ (2 * k)) := by
  classical
  have hswap : ∑ y ∈ (piFinset fun _ : Fin (k + 1) => A) ×ˢ
        (piFinset fun _ : Fin (k + 1) => A), matchCount y
      = ∑ ij ∈ (univ : Finset (Fin (k + 1) × Fin (k + 1))),
          #{y ∈ (piFinset fun _ : Fin (k + 1) => A) ×ˢ
              (piFinset fun _ : Fin (k + 1) => A) | y.1 ij.1 = y.2 ij.2} := by
    unfold matchCount
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  rw [Finset.sum_congr rfl (fun ij _ => card_matchSlice_cube A k ij.1 ij.2)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    smul_eq_mul, ← sq]

end Identities

/-! ## The unconditional descent anomaly transfer -/

section Transfer

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Descent anomaly transfer.**  The signed matching moment of the rung-`(k+1)` depth
measure equals `(k+1)² · #A` times the rung-`k` global DC anomaly — hence is nonnegative at
every prime, every subgroup, every rung, with no sign law assumed (G95 floor). -/
theorem descent_anomaly_transfer (A : Finset F) (k : ℕ) :
    (Fintype.card F : ℤ) * ∑ y ∈ energySet A (k + 1), (matchCount y : ℤ)
        - ∑ y ∈ (piFinset fun _ : Fin (k + 1) => A) ×ˢ
            (piFinset fun _ : Fin (k + 1) => A), (matchCount y : ℤ)
      = (k + 1) ^ 2 * A.card *
          ((Fintype.card F : ℤ) * Finset.addREnergy k A - (A.card : ℤ) ^ (2 * k)) := by
  have h1 := sum_matchCount_energySet A k
  have h2 := sum_matchCount_cube A k
  have h1' : ∑ y ∈ energySet A (k + 1), (matchCount y : ℤ)
      = ((k + 1) ^ 2 * (A.card * Finset.addREnergy k A) : ℕ) := by
    rw [← h1]; push_cast; rfl
  have h2' : ∑ y ∈ (piFinset fun _ : Fin (k + 1) => A) ×ˢ
        (piFinset fun _ : Fin (k + 1) => A), (matchCount y : ℤ)
      = ((k + 1) ^ 2 * (A.card * A.card ^ (2 * k)) : ℕ) := by
    rw [← h2]; push_cast; rfl
  rw [h1', h2']
  push_cast
  ring

/-- The descent moment of the signed measure is **nonnegative unconditionally** — the exact
cross-rung positivity that survives every uniform-law counterexample. -/
theorem descent_moment_nonneg (A : Finset F) (k : ℕ) :
    0 ≤ (Fintype.card F : ℤ) * ∑ y ∈ energySet A (k + 1), (matchCount y : ℤ)
        - ∑ y ∈ (piFinset fun _ : Fin (k + 1) => A) ×ˢ
            (piFinset fun _ : Fin (k + 1) => A), (matchCount y : ℤ) := by
  rw [descent_anomaly_transfer]
  apply mul_nonneg
  · positivity
  · have h := card_pow_le_card_mul_addREnergy (α := F) k A
    have : ((A.card : ℤ)) ^ (2 * k) ≤ (Fintype.card F : ℤ) * Finset.addREnergy k A := by
      exact_mod_cast h
    omega

end Transfer

/-! ## Full-depth invisibility -/

section Invisibility

variable [DecidableEq α]

/-- `matchCount` vanishes exactly on the fully-disjoint (maximal-cancellation-depth) pairs. -/
theorem matchCount_eq_zero_iff {r : ℕ} (y : (Fin r → α) × (Fin r → α)) :
    matchCount y = 0 ↔ cancelDepth y = r := by
  constructor
  · intro h
    have hdisj : ∀ i j, y.1 i ≠ y.2 j := by
      intro i j hij
      have : (i, j) ∈ {ij ∈ (univ : Finset (Fin r × Fin r)) | y.1 ij.1 = y.2 ij.2} :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
      rw [Finset.card_eq_zero.mp h] at this
      exact absurd this (Finset.notMem_empty _)
    -- disjoint bags: the common part is zero
    have hcommon : commonPart (valueBag y.1) (valueBag y.2) = 0 := by
      unfold commonPart
      rw [Multiset.inter_eq_zero_iff_disjoint]
      rw [Multiset.disjoint_left]
      intro a ha hb
      obtain ⟨i, hi⟩ : ∃ i, y.1 i = a := by
        have := Multiset.mem_coe.mp ha
        simpa [valueBag, List.mem_ofFn] using ha
      obtain ⟨j, hj⟩ : ∃ j, y.2 j = a := by
        simpa [valueBag, List.mem_ofFn] using hb
      exact hdisj i j (hi.trans hj.symm)
    unfold cancelDepth leftCore
    rw [hcommon, Multiset.sub_zero]
    simp [valueBag]
  · intro h
    unfold cancelDepth at h
    -- maximal depth forces zero common part, hence no matching positions
    have hcard : (commonPart (valueBag y.1) (valueBag y.2)).card = 0 := by
      have hrec := congrArg Multiset.card (left_reconstruct (valueBag y.1) (valueBag y.2))
      rw [Multiset.card_add] at hrec
      have hbag : (valueBag y.1).card = r := by simp [valueBag]
      omega
    have hcommon : commonPart (valueBag y.1) (valueBag y.2) = 0 :=
      Multiset.card_eq_zero.mp hcard
    unfold matchCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ⟨i, j⟩ _
    intro hij
    have hmem : y.1 i ∈ commonPart (valueBag y.1) (valueBag y.2) := by
      unfold commonPart
      rw [Multiset.mem_inter]
      constructor
      · simpa [valueBag, List.mem_ofFn] using ⟨i, rfl⟩
      · rw [hij]; simpa [valueBag, List.mem_ofFn] using ⟨j, rfl⟩
    rw [hcommon] at hmem
    exact absurd hmem (Multiset.notMem_zero _)

end Invisibility

end ArkLib.ProximityGap.Frontier.G121DescentMatchingIdentity

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G121DescentMatchingIdentity.card_matchSlice
#print axioms
  ArkLib.ProximityGap.Frontier.G121DescentMatchingIdentity.sum_matchCount_energySet
#print axioms
  ArkLib.ProximityGap.Frontier.G121DescentMatchingIdentity.card_matchSlice_cube
#print axioms ArkLib.ProximityGap.Frontier.G121DescentMatchingIdentity.sum_matchCount_cube
#print axioms
  ArkLib.ProximityGap.Frontier.G121DescentMatchingIdentity.descent_anomaly_transfer
#print axioms ArkLib.ProximityGap.Frontier.G121DescentMatchingIdentity.descent_moment_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.G121DescentMatchingIdentity.matchCount_eq_zero_iff

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._BSG_DRC1
import ArkLib.Research.ProximityGap.Frontier._BSG_DRC2
import ArkLib.Research.ProximityGap.Frontier._BSG_BareDRCExtract

/-!
# BSG — refutation of the energy-stripped DRC residuals (negative brick)

`BareDRCExtract C₁ C₂ c` is the post-averaging dependent-random-choice extraction residual
(`_BSG_DRC1.lean`). This file proves it **false for every choice of constants**
(`bareDRCExtract_false`), and with it the other energy-stripped residuals of the old BSG ladder:
`BareDRC` (`_BSG_Reduce`, `bareDRC_false`), `DRCKernel` (`_BSG_DRC2`, `drcKernel_false`) and
`DRCRefinedReps` (`_BSG_BareDRCExtract`, `drcRefinedReps_false`). None of these is a remaining
open input: each is unsatisfiable, so the conditional implications out of them
(`bareDRC_of_extract`, `bsgCore_of_bareDRC`, `bareDRC_of_kernel`, `bareDRCExtract_of_refinedReps`)
are vacuous. The standard BSG theorem is not affected: its proof uses additive-energy information
that these graph-only interfaces discard. The energy-coupled replacement interface is
`DRCKernelEnergy` in `_BSGC_attempt4.lean` (still open, and not certified satisfiable).

The first section keeps the original small brick: at the **trivial constants**
`C₁ = C₂ = c = 1` an explicit `ZMod 7` countermodel proves `¬ BareDRCExtract 1 1 1`. The
all-constants refutation follows at the end of the file.

## The countermodel

Carrier `α = ZMod 7`, `A = {0, 1, 3}` (a Sidon / `B₂` set: all `3·3 = 9` ordered differences
land on `7` *distinct* values, so `#(A - A) = 7`), `K = 1`, `G = A ×ˢ A` the complete bipartite
graph, `b₀ = 0`.

* All three hypotheses of `BareDRCExtract` hold at this instance:
  - edge-density `#A² ≤ 4K²·#G`: `9 ≤ 36` (since `#G = #(A ×ˢ A) = 9`);
  - cherry-richness `#A⁴ ≤ 16K⁴·(#A · ∑_b deg(b)²)`: each `deg(b) = #A = 3`, the diagonal term
    alone gives `∑_b deg(b)² ≥ 9`, so `16·(3·9) = 432 ≥ 81`;
  - apex `#A ≤ 4K²·deg(b₀)`: `3 ≤ 12`.
* The conclusion fails. With `C₁ = C₂ = c = K = 1` it demands
  `A' ⊆ A`, `#A' ≥ #A = 3`, and `#(A' - A') ≤ #A'`. From `A' ⊆ A` and `#A' ≥ 3 = #A` we get
  `A' = A`, hence `#(A' - A') = #(A - A) = 7 > 3 = #A'`. Contradiction.

This is a **negative result**: at the trivial constants the extraction step cannot hold; a Sidon
set is the canonical obstruction (a small-doubling refinement of constant density is impossible
when the whole set already has the maximal doubling `#(A-A) ≈ #A²`).

The countermodel is verified by `decide` (over the finite carrier `ZMod 7`), `Finset.single_le_sum`,
and `Finset.eq_of_subset_of_card_le`; no `sorry`, `native_decide`, or extra axioms.
-/

open Finset
open scoped BigOperators Pointwise

namespace Finset.BSG

/-- The witness set `A = {0, 1, 3} ⊆ ZMod 7`: a Sidon set with maximal doubling `#(A - A) = 7`. -/
def exA : Finset (ZMod 7) := {0, 1, 3}

/-- The complete bipartite graph `G = A ×ˢ A` on the witness set. -/
def exG : Finset (ZMod 7 × ZMod 7) := exA ×ˢ exA

@[simp] lemma card_exA : #exA = 3 := by decide

/-- `A - A` is everything in `ZMod 7`: the Sidon property gives the maximal doubling. -/
@[simp] lemma card_exA_sub : #(exA - exA) = 7 := by decide

@[simp] lemma card_exG : #exG = 9 := by decide

/-- Every right-vertex `b ∈ A` has full left-degree `#A = 3` in the complete graph `G = A ×ˢ A`. -/
lemma rDeg_exG (b : ZMod 7) (hb : b ∈ exA) : rDeg exA exG b = 3 := by
  revert hb
  revert b
  decide

/-- **Refutation brick.** `BareDRCExtract` is **false** at the trivial constants `(1, 1, 1)`. -/
theorem bareDRCExtract_false_1_1_1 : ¬ Finset.BSG.BareDRCExtract 1 1 1 := by
  intro h
  -- The three hypotheses, supplied as `#A`-cleared numeric facts at this instance.
  have hKpos : (0 : ℕ) < 1 := one_pos
  have hAne : exA.Nonempty := ⟨0, by decide⟩
  have hGsub : exG ⊆ exA ×ˢ exA := by rw [exG]
  have hb₀ : (0 : ZMod 7) ∈ exA := by decide
  -- h1 : edge-density `#A² ≤ 4·K²·#G`,  9 ≤ 36.
  have h1 : #exA ^ 2 ≤ 4 * (1 : ℕ) ^ 2 * #exG := by
    simp only [card_exA, card_exG]; norm_num
  -- h2 : cherry-richness.  Bound the cherry sum below by its `b₀ = 0` diagonal term `deg(0)² = 9`.
  have hsum_ge : (3 : ℕ) ^ 2 ≤ ∑ b ∈ exA, rDeg exA exG b ^ 2 := by
    have hterm : rDeg exA exG (0 : ZMod 7) ^ 2 ≤ ∑ b ∈ exA, rDeg exA exG b ^ 2 :=
      Finset.single_le_sum (f := fun b => rDeg exA exG b ^ 2)
        (fun i _ => Nat.zero_le _) hb₀
    rw [rDeg_exG 0 hb₀] at hterm
    exact hterm
  have h2 : #exA ^ 4 ≤ 16 * (1 : ℕ) ^ 4 * (#exA * (∑ b ∈ exA, rDeg exA exG b ^ 2)) := by
    rw [card_exA]
    calc (3 : ℕ) ^ 4 = 81 := by norm_num
      _ ≤ 16 * 1 ^ 4 * (3 * 3 ^ 2) := by norm_num
      _ ≤ 16 * 1 ^ 4 * (3 * (∑ b ∈ exA, rDeg exA exG b ^ 2)) := by
            have := hsum_ge
            exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this)
  -- h3 : apex `#A ≤ 4·K²·deg(b₀)`,  3 ≤ 12.
  have h3 : #exA ≤ 4 * (1 : ℕ) ^ 2 * rDeg exA exG (0 : ZMod 7) := by
    rw [card_exA, rDeg_exG 0 hb₀]; norm_num
  -- Apply the (assumed) extraction to obtain a small-doubling refinement `A'`.
  obtain ⟨A', hsub, _hne, hsize, hdoub⟩ :=
    h exA 1 exG 0 hKpos hAne hGsub hb₀ h1 h2 h3
  -- `hsize : 1 · 1 · #A' ≥ #A`, i.e. `#A' ≥ 3`; combined with `#A' ≤ #A = 3` forces `A' = A`.
  have hsubcard : #A' ≤ #exA := Finset.card_le_card hsub
  rw [card_exA] at hsubcard
  have hge3 : (3 : ℕ) ≤ #A' := by
    have : (1 : ℕ) * 1 * #A' ≥ #exA := hsize
    rw [card_exA] at this
    simpa using this
  have hAeq : A' = exA := Finset.eq_of_subset_of_card_le hsub (by rw [card_exA]; omega)
  subst hAeq
  -- `hdoub : #(A' - A') ≤ 1 · 1^1 · #A'`, i.e. `#(A - A) ≤ #A = 3`; but `#(A - A) = 7`.
  rw [card_exA_sub] at hdoub
  have : (7 : ℕ) ≤ 1 * 1 ^ 1 * #exA := hdoub
  rw [card_exA] at this
  omega

/-! ## Refutation for every choice of constants

The `ZMod 7` brick above only refutes `(1,1,1)`. The same obstruction works for **every**
`C₁, C₂, c`: take `K = 1`, the complete graph `G = A ×ˢ A`, and a Sidon set `A` of size
`N = C₁ * (C₂ + 1) + 1`. All graph hypotheses hold at `K = 1` for *every* nonempty `A` (edge count
`#A²`, cherry sum `#A³`, every right degree `#A`), while in a Sidon set every nonempty `B ⊆ A`
has `#(B - B) ≥ #B * #B - #B`. So `#(B - B) ≤ C₂ * #B` forces `#B ≤ C₂ + 1`, contradicting
`C₁ * #B ≥ #A = N`. (The exponent `c` is irrelevant at `K = 1`.)

The Sidon set used is the unit-vector set `{e_i}` in `Fin N → ℤ`, whose ordered off-diagonal
differences `e_i - e_j` are pairwise distinct. -/

/-- The unit-vector set `{e_i : i : Fin N}` in `Fin N → ℤ` (a Sidon set of size `N`). -/
noncomputable def sidonUnitVecs (N : ℕ) : Finset (Fin N → ℤ) :=
  Finset.univ.image (fun i : Fin N => (Pi.single i (1 : ℤ) : Fin N → ℤ))

lemma card_sidonUnitVecs (N : ℕ) : #(sidonUnitVecs N) = N := by
  classical
  rw [sidonUnitVecs, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro i j hij
  have h := congrFun hij i
  by_contra hne
  simp [Ne.symm hne] at h

/-- **Sidon property of the unit vectors.** An off-diagonal difference `x - y` of unit vectors
determines the ordered pair `(x, y)`. -/
lemma sidonUnitVecs_sub_eq {N : ℕ} {x y x' y' : Fin N → ℤ}
    (hx : x ∈ sidonUnitVecs N) (hy : y ∈ sidonUnitVecs N)
    (hx' : x' ∈ sidonUnitVecs N) (hy' : y' ∈ sidonUnitVecs N)
    (hxy : x ≠ y) (h : x - y = x' - y') : x = x' ∧ y = y' := by
  classical
  simp only [sidonUnitVecs, Finset.mem_image, Finset.mem_univ, true_and] at hx hy hx' hy'
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  obtain ⟨k, rfl⟩ := hx'
  obtain ⟨l, rfl⟩ := hy'
  have hij : i ≠ j := fun hij => hxy (by rw [hij])
  have hi := congrFun h i
  have hj := congrFun h j
  simp only [Pi.sub_apply, Pi.single_apply, if_neg hij, if_neg (Ne.symm hij)] at hi hj
  have hik : i = k := by
    by_contra hik
    rw [if_neg hik] at hi
    split_ifs at hi <;> omega
  have hjl : j = l := by
    by_contra hjl
    rw [if_neg hjl] at hj
    split_ifs at hj <;> omega
  exact ⟨by rw [hik], by rw [hjl]⟩

/-- In a subset of the Sidon unit-vector set, the difference set has at least `#B² - #B`
elements (the off-diagonal differences are pairwise distinct). -/
lemma card_sub_ge_of_subset_sidonUnitVecs {N : ℕ} {B : Finset (Fin N → ℤ)}
    (hB : B ⊆ sidonUnitVecs N) : #B * #B - #B ≤ #(B - B) := by
  classical
  rw [← Finset.offDiag_card]
  refine Finset.card_le_card_of_injOn (fun p => p.1 - p.2) ?_ ?_
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_offDiag] at hp
    exact Finset.sub_mem_sub hp.1 hp.2.1
  · intro p hp q hq hpq
    rw [Finset.mem_coe, Finset.mem_offDiag] at hp hq
    obtain ⟨h1, h2⟩ :=
      sidonUnitVecs_sub_eq (hB hp.1) (hB hp.2.1) (hB hq.1) (hB hq.2.1) hp.2.2 hpq
    exact Prod.ext h1 h2

/-- **`BareDRCExtract` is false for every choice of constants.** -/
theorem bareDRCExtract_false (C₁ C₂ c : ℕ) : ¬ BareDRCExtract C₁ C₂ c := by
  intro h
  classical
  set N : ℕ := C₁ * (C₂ + 1) + 1 with hN
  set A : Finset (Fin N → ℤ) := sidonUnitVecs N with hAdef
  have hAcard : #A = N := card_sidonUnitVecs N
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨b₀, hb₀⟩ := hAne
  have hdeg : ∀ b ∈ A, rDeg A (A ×ˢ A) b = #A := by
    intro b hb
    rw [rDeg, Finset.filter_true_of_mem]
    intro a ha
    exact Finset.mem_product.mpr ⟨ha, hb⟩
  have hsum : ∑ b ∈ A, rDeg A (A ×ˢ A) b ^ 2 = #A * #A ^ 2 := by
    rw [Finset.sum_congr rfl (fun b hb => by rw [hdeg b hb]), Finset.sum_const, smul_eq_mul]
  have h1 : #A ^ 2 ≤ 4 * 1 ^ 2 * #(A ×ˢ A) := by
    rw [Finset.card_product]; nlinarith
  have h2 : #A ^ 4 ≤ 16 * 1 ^ 4 * (#A * ∑ b ∈ A, rDeg A (A ×ˢ A) b ^ 2) := by
    rw [hsum]; nlinarith
  have h3 : #A ≤ 4 * 1 ^ 2 * rDeg A (A ×ˢ A) b₀ := by
    rw [hdeg b₀ hb₀]; omega
  obtain ⟨B, hBA, hBne, hsize, hdoub⟩ :=
    h A 1 (A ×ˢ A) b₀ one_pos ⟨b₀, hb₀⟩ subset_rfl hb₀ h1 h2 h3
  have hoff := card_sub_ge_of_subset_sidonUnitVecs hBA
  simp only [one_pow, mul_one] at hsize hdoub
  have hBpos : 0 < #B := hBne.card_pos
  have hBle : #B ≤ C₂ + 1 := by
    have hsq : #B * #B ≤ (C₂ + 1) * #B := by
      have h' : #B * #B - #B ≤ C₂ * #B := le_trans hoff hdoub
      have h'' : #B ≤ #B * #B := Nat.le_mul_of_pos_left _ hBpos
      rw [add_mul, one_mul]
      omega
    exact Nat.le_of_mul_le_mul_right hsq hBpos
  have hC : C₁ * #B ≤ C₁ * (C₂ + 1) := Nat.mul_le_mul_left _ hBle
  rw [hAcard] at hsize
  omega

/-- `BareDRC` (no distinguished vertex) implies `BareDRCExtract` (which has extra hypotheses). -/
theorem bareDRCExtract_of_bareDRC {C₁ C₂ c : ℕ} (h : BareDRC C₁ C₂ c) :
    BareDRCExtract C₁ C₂ c := by
  intro α _ _ A K G _b₀ hK hA hGsub _hb₀ hdense hcherry _hgood
  exact h A K G hK hA hGsub hdense hcherry

/-- **`BareDRC` is false for every choice of constants.** -/
theorem bareDRC_false (C₁ C₂ c : ℕ) : ¬ BareDRC C₁ C₂ c :=
  fun h => bareDRCExtract_false C₁ C₂ c (bareDRCExtract_of_bareDRC h)

/-- **`DRCKernel` (`_BSG_DRC2`) is false for every choice of constants**, since it implies
`BareDRC` (`bareDRC_of_kernel`). -/
theorem drcKernel_false (C₁ C₂ c : ℕ) : ¬ DRCKernel C₁ C₂ c :=
  fun h => bareDRC_false C₁ C₂ c (bareDRC_of_kernel h)

/-- **`DRCRefinedReps` (`_BSG_BareDRCExtract`) is false for every choice of constants**, since it
implies `BareDRCExtract` (`bareDRCExtract_of_refinedReps`). -/
theorem drcRefinedReps_false (C₁ C₂ c : ℕ) : ¬ DRCRefinedReps C₁ C₂ c :=
  fun h => bareDRCExtract_false C₁ C₂ c (bareDRCExtract_of_refinedReps h)

end Finset.BSG

-- Axiom audit (expected: propext, Classical.choice, Quot.sound — and NO sorryAx).
#print axioms Finset.BSG.bareDRCExtract_false_1_1_1
#print axioms Finset.BSG.bareDRCExtract_false
#print axioms Finset.BSG.bareDRC_false
#print axioms Finset.BSG.drcKernel_false
#print axioms Finset.BSG.drcRefinedReps_false

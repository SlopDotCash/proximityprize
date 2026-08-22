/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS

/-!
# THE TWO-BRANCH COUNTERMODEL (#389): the universal mean-degree law is FALSE

The #389 supply programme reduced the sub-Johnson wall to the conjectured
**mean-degree law** (probe census `717da6067`, issue thread 2026-06-13): for
every agreement-capped word, the total agreement mass of the
`≥ k+m+1`-agreement family is `≤ 2n`.  The law is a THEOREM for
`t² ≥ 2(k−1)n`-range bands (`mean_degree_law_deep`); this file refutes its
universal form in the open sub-Johnson range — and locates the true growth.

**The countermodel family (the two-branch parabola word).**  Split the domain
`D = A ⊔ B` and set `w = x²` on `A`, `w = x² + c` on `B`:

* every polynomial of degree `< k = 2` agrees with each branch on `≤ 2` points
  (the root budget of `g − P` with `g` the branch, `deg g = 2 > deg P`), so
  every codeword agreement is `≤ 4 ≤ 6 = 2k+m+1` — the word is
  agreement-capped UNCONDITIONALLY (`w101_agreement_le_four`);
* the line through `(x₁, x₁²)` and `(x₂, x₂²)` meets the `B`-branch at the
  roots of `z² − (x₁+x₂)z + (x₁x₂ + c)`; whenever its discriminant
  `(x₁−x₂)² − 4c` is a nonzero square with both roots in `B`, the line carries
  FOUR graph points — an explainable `(k+m+1)`-core of agreement exactly `4`.

At `q = 101`, `D = {0,…,79}`, `A = {0,…,39}`, `B = {40,…,79}`, `c = 29` this
yields `107` four-rich lines (probe-verified to be ALL the `≥ 4`-rich lines):
`Σ a_c = 428 > 160 = 2n` — the law fails by a factor `2.7`.  Asymptotically
the family carries `~ n²/64` four-rich lines once `n³ ≳ 64·q²` (probe
`probe_two_branch_subjohnson_supply.py`, exact ratio `1.00` at `n = 601`);
the previous censuses (`n ≤ 24` at `q = 31`) stopped exactly at the
crossover and could not see it.

**What survives, and the corrected target.**  The proven deep-band law
(`mean_degree_law_deep`) is hypothesis-guarded and now provably sharp.  The
corrected open surface is the two-regime growth law
`S_max(capped) = Θ(n + C(n,k+m+1)/q^{m+1})` (partition floor + random mean):
the two-branch family realizes the mean term constructively, and a
`B = O(n + C(n,t)/q^{m+1})` bound still delivers prize-grade bad-scalar
counts through `deep_band_badSet_card_of_residual`.  Named here as
`CappedSupplyTwoRegimeLaw`; wiring it to `SubJohnsonSupplyResidual` is the
registered follow-up.

Issue #389.  Probes: `probe_two_branch_subjohnson_supply.py`,
`probe_two_branch_witness_dump.py`.
-/

open Finset Polynomial

namespace ProximityGap.TwoBranch

open ProximityGap.SpikeFloor

/-- **The refuted statement** (the universal mean-degree law, as conjectured in
the #389 thread): for every agreement-capped word over every RS code, every
family of distinct `≥ k+m+1`-agreement sets has total mass `≤ 2n`. -/
def UniversalMeanDegreeLaw : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
    ∀ (n : ℕ) [NeZero n], ∀ (dom : Fin n ↪ F) (k m : ℕ) (w : Fin n → F),
    (∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
        (Finset.univ.filter fun i => c i = w i).card ≤ 2 * k + m + 1) →
    ∀ S : Finset (Finset (Fin n)),
      (∀ A ∈ S, (k + m + 1 ≤ A.card) ∧
        ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
          A = Finset.univ.filter fun i => c i = w i) →
      ∑ A ∈ S, A.card ≤ 2 * n

/-- **The branch root budget**: a polynomial `P` of degree below `deg g` agrees
with the `g`-branch of a word on at most `natDegree g` points of any subset of
the domain. -/
theorem branch_agreement_card_le {F : Type} [Field F] [DecidableEq F] {n : ℕ}
    (dom : Fin n ↪ F) {P g : F[X]} (hdeg : P.degree < g.degree)
    (s : Finset (Fin n)) :
    (s.filter fun i => P.eval (dom i) = g.eval (dom i)).card ≤ g.natDegree := by
  classical
  have hne : g - P ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h] at hdeg
    exact lt_irrefl _ hdeg
  have hdegeq : (g - P).degree = g.degree := by
    rw [sub_eq_add_neg]
    rw [Polynomial.degree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_neg])]
  calc (s.filter fun i => P.eval (dom i) = g.eval (dom i)).card
      = ((s.filter fun i => P.eval (dom i) = g.eval (dom i)).image dom).card :=
        (Finset.card_image_of_injective _ dom.injective).symm
    _ ≤ (g - P).roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        have hxv := (Finset.mem_filter.mp hi).2
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
        rw [Polynomial.IsRoot, Polynomial.eval_sub, hxv, sub_self]
    _ ≤ (g - P).roots.card := (g - P).roots.toFinset_card_le
    _ ≤ (g - P).natDegree := (g - P).card_roots'
    _ = g.natDegree := Polynomial.natDegree_eq_of_degree_eq hdegeq

/-! ## The concrete instance: `q = 101`, `n = 80`, `k = 2`, `m = 1` -/

instance primeFact_TwoBranchSupplyCountermodel_1 : Fact (Nat.Prime 101) := ⟨by decide⟩

/-- The field `F₁₀₁`. -/
abbrev F101 : Type := ZMod 101

/-- The interval domain `{0, …, 79} ⊂ F₁₀₁`. -/
def dom101 : Fin 80 ↪ F101 :=
  ⟨fun i => (i.val : F101), fun a b hab => by
    have hab' : ((a.val : ℕ) : F101) = ((b.val : ℕ) : F101) := hab
    have h2 := congrArg ZMod.val hab'
    rw [ZMod.val_natCast_of_lt (Nat.lt_trans a.isLt (by norm_num)),
        ZMod.val_natCast_of_lt (Nat.lt_trans b.isLt (by norm_num))] at h2
    exact Fin.ext h2⟩

/-- The two-branch parabola word: `x²` on `A = {0,…,39}`, `x² + 29` on
`B = {40,…,79}`. -/
def w101 : Fin 80 → F101 :=
  fun i => (i.val : F101) ^ 2 + (if 40 ≤ i.val then 29 else 0)

/-- **The agreement cap, by theorem (no enumeration)**: every polynomial of
degree `< 2` agrees with `w101` on at most `4` points — `≤ 2` per branch. -/
theorem w101_agreement_le_four {P : F101[X]} (hP : P.degree < (2 : ℕ)) :
    (Finset.univ.filter fun i => P.eval (dom101 i) = w101 i).card ≤ 4 := by
  classical
  have hdegX2 : (X ^ 2 : F101[X]).degree = 2 := Polynomial.degree_X_pow 2
  have hdegX2C : (X ^ 2 + Polynomial.C (29 : F101)).degree = 2 :=
    Polynomial.degree_X_pow_add_C Nat.zero_lt_two (29 : F101)
  have hsub : (Finset.univ.filter fun i => P.eval (dom101 i) = w101 i)
      ⊆ ((Finset.univ.filter fun i : Fin 80 => ¬ 40 ≤ i.val).filter
            fun i => P.eval (dom101 i) = (X ^ 2 : F101[X]).eval (dom101 i))
        ∪ ((Finset.univ.filter fun i : Fin 80 => 40 ≤ i.val).filter
            fun i => P.eval (dom101 i)
              = (X ^ 2 + Polynomial.C (29 : F101)).eval (dom101 i)) := by
    intro i hi
    have hiv := (Finset.mem_filter.mp hi).2
    by_cases hb : 40 ≤ i.val
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, ?_⟩)
      rw [hiv]
      simp [w101, dom101, hb]
    · refine Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, ?_⟩)
      rw [hiv]
      simp [w101, dom101, hb]
  refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _) ?_)
  have h1 := branch_agreement_card_le dom101
    (P := P) (g := (X ^ 2 : F101[X])) (by rw [hdegX2]; exact hP)
    (Finset.univ.filter fun i : Fin 80 => ¬ 40 ≤ i.val)
  have h2 := branch_agreement_card_le dom101
    (P := P) (g := (X ^ 2 + Polynomial.C (29 : F101))) (by rw [hdegX2C]; exact hP)
    (Finset.univ.filter fun i : Fin 80 => 40 ≤ i.val)
  rw [Polynomial.natDegree_X_pow] at h1
  rw [Polynomial.natDegree_X_pow_add_C] at h2
  omega

/-- Affine words are codewords of `rsCode dom101 2`. -/
theorem affine_mem_rsCode (s b : F101) :
    (fun i => s * dom101 i + b) ∈ (rsCode dom101 2 : Submodule F101 (Fin 80 → F101)) := by
  refine ⟨Polynomial.C s * Polynomial.X + Polynomial.C b, ?_, ?_⟩
  · refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le s)
        (by exact_mod_cast Nat.one_lt_two)
    · exact lt_of_le_of_lt Polynomial.degree_C_le
        (by exact_mod_cast Nat.zero_lt_two)
  · funext i
    simp

/-- The agreement set of an affine codeword is EXACTLY a given `4`-set, from
the four membership facts (decidable) plus the cap (theorem). -/
theorem line_agreeSet_eq {s b : F101} {T : Finset (Fin 80)}
    (hT : ∀ i ∈ T, s * dom101 i + b = w101 i) (hcard : T.card = 4) :
    T = Finset.univ.filter fun i => (fun i => s * dom101 i + b) i = w101 i := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT i hi⟩
  · rw [hcard]
    have hrw : (Finset.univ.filter fun i => (fun i => s * dom101 i + b) i = w101 i)
        = (Finset.univ.filter fun i =>
            (Polynomial.C s * Polynomial.X + Polynomial.C b).eval (dom101 i) = w101 i) := by
      apply Finset.filter_congr
      intro i _
      simp
    rw [hrw]
    refine w101_agreement_le_four ?_
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le s)
        (by exact_mod_cast Nat.one_lt_two)
    · exact lt_of_le_of_lt Polynomial.degree_C_le
        (by exact_mod_cast Nat.zero_lt_two)

/-- The witnessed family: the `107` four-rich lines of the two-branch word
(slope, intercept, and the four agreement points), generated and
census-verified by `probe_two_branch_witness_dump.py`. -/
def lineDataN : List ((ℕ × ℕ) × Finset (Fin 80)) := [
  ((3, 0), {0, 3, 45, 59}),
  ((4, 0), {0, 4, 52, 53}),
  ((8, 0), {0, 8, 51, 58}),
  ((18, 0), {0, 18, 40, 79}),
  ((19, 0), {0, 19, 54, 66}),
  ((25, 0), {0, 25, 62, 64}),
  ((33, 0), {0, 33, 63, 71}),
  ((5, 97), {1, 4, 46, 60}),
  ((6, 96), {1, 5, 53, 54}),
  ((10, 92), {1, 9, 52, 59}),
  ((21, 81), {1, 20, 55, 67}),
  ((27, 75), {1, 26, 63, 65}),
  ((35, 67), {1, 34, 64, 72}),
  ((7, 91), {2, 5, 47, 61}),
  ((8, 89), {2, 6, 54, 55}),
  ((12, 81), {2, 10, 53, 60}),
  ((23, 59), {2, 21, 56, 68}),
  ((29, 47), {2, 27, 64, 66}),
  ((37, 31), {2, 35, 65, 73}),
  ((9, 83), {3, 6, 48, 62}),
  ((10, 80), {3, 7, 55, 56}),
  ((14, 68), {3, 11, 54, 61}),
  ((25, 35), {3, 22, 57, 69}),
  ((31, 17), {3, 28, 65, 67}),
  ((39, 94), {3, 36, 66, 74}),
  ((11, 73), {4, 7, 49, 63}),
  ((12, 69), {4, 8, 56, 57}),
  ((16, 53), {4, 12, 55, 62}),
  ((27, 9), {4, 23, 58, 70}),
  ((33, 86), {4, 29, 66, 68}),
  ((41, 54), {4, 37, 67, 75}),
  ((13, 61), {5, 8, 50, 64}),
  ((14, 56), {5, 9, 57, 58}),
  ((18, 36), {5, 13, 56, 63}),
  ((29, 82), {5, 24, 59, 71}),
  ((35, 52), {5, 30, 67, 69}),
  ((43, 12), {5, 38, 68, 76}),
  ((15, 47), {6, 9, 51, 65}),
  ((16, 41), {6, 10, 58, 59}),
  ((20, 17), {6, 14, 57, 64}),
  ((31, 52), {6, 25, 60, 72}),
  ((37, 16), {6, 31, 68, 70}),
  ((45, 69), {6, 39, 69, 77}),
  ((17, 31), {7, 10, 52, 66}),
  ((18, 24), {7, 11, 59, 60}),
  ((22, 97), {7, 15, 58, 65}),
  ((33, 20), {7, 26, 61, 73}),
  ((39, 79), {7, 32, 69, 71}),
  ((19, 13), {8, 11, 53, 67}),
  ((20, 5), {8, 12, 60, 61}),
  ((24, 74), {8, 16, 59, 66}),
  ((35, 87), {8, 27, 62, 74}),
  ((41, 39), {8, 33, 70, 72}),
  ((21, 94), {9, 12, 54, 68}),
  ((22, 85), {9, 13, 61, 62}),
  ((26, 49), {9, 17, 60, 67}),
  ((37, 51), {9, 28, 63, 75}),
  ((43, 98), {9, 34, 71, 73}),
  ((23, 72), {10, 13, 55, 69}),
  ((24, 62), {10, 14, 62, 63}),
  ((28, 22), {10, 18, 61, 68}),
  ((39, 13), {10, 29, 64, 76}),
  ((45, 54), {10, 35, 72, 74}),
  ((25, 48), {11, 14, 56, 70}),
  ((26, 37), {11, 15, 63, 64}),
  ((30, 94), {11, 19, 62, 69}),
  ((41, 74), {11, 30, 65, 77}),
  ((47, 8), {11, 36, 73, 75}),
  ((27, 22), {12, 15, 57, 71}),
  ((28, 10), {12, 16, 64, 65}),
  ((32, 63), {12, 20, 63, 70}),
  ((43, 32), {12, 31, 66, 78}),
  ((49, 61), {12, 37, 74, 76}),
  ((29, 95), {13, 16, 58, 72}),
  ((30, 82), {13, 17, 65, 66}),
  ((34, 30), {13, 21, 64, 71}),
  ((45, 89), {13, 32, 67, 79}),
  ((51, 11), {13, 38, 75, 77}),
  ((31, 65), {14, 17, 59, 73}),
  ((32, 51), {14, 18, 66, 67}),
  ((36, 96), {14, 22, 65, 72}),
  ((53, 60), {14, 39, 76, 78}),
  ((33, 33), {15, 18, 60, 74}),
  ((34, 18), {15, 19, 67, 68}),
  ((38, 59), {15, 23, 66, 73}),
  ((35, 100), {16, 19, 61, 75}),
  ((36, 84), {16, 20, 68, 69}),
  ((40, 20), {16, 24, 67, 74}),
  ((37, 64), {17, 20, 62, 76}),
  ((38, 47), {17, 21, 69, 70}),
  ((42, 80), {17, 25, 68, 75}),
  ((39, 26), {18, 21, 63, 77}),
  ((40, 8), {18, 22, 70, 71}),
  ((44, 37), {18, 26, 69, 76}),
  ((41, 87), {19, 22, 64, 78}),
  ((42, 68), {19, 23, 71, 72}),
  ((46, 93), {19, 27, 70, 77}),
  ((43, 45), {20, 23, 65, 79}),
  ((44, 25), {20, 24, 72, 73}),
  ((48, 46), {20, 28, 71, 78}),
  ((46, 81), {21, 25, 73, 74}),
  ((50, 98), {21, 29, 72, 79}),
  ((48, 34), {22, 26, 74, 75}),
  ((50, 86), {23, 27, 75, 76}),
  ((52, 35), {24, 28, 76, 77}),
  ((54, 83), {25, 29, 77, 78}),
  ((56, 28), {26, 30, 78, 79})
]

set_option maxRecDepth 100000 in
/-- The decidable line facts, in pure `ℕ` arithmetic (kernel-fast): each
entry's `4`-set satisfies the line equation mod `101`. -/
theorem line_facts_nat : ∀ pair ∈ lineDataN,
    (∀ i ∈ pair.2, (pair.1.1 * i.val + pair.1.2) % 101
        = (i.val * i.val + (if 40 ≤ i.val then 29 else 0)) % 101) ∧
      pair.2.card = 4 := by
  decide +kernel

/-- The cast bridge: a mod-`101` identity in `ℕ` is the `F101` line
evaluation fact. -/
theorem line_eval_eq {s b : ℕ} {i : Fin 80}
    (h : (s * i.val + b) % 101
        = (i.val * i.val + (if 40 ≤ i.val then 29 else 0)) % 101) :
    (s : F101) * dom101 i + (b : F101) = w101 i := by
  have hcast : ((s * i.val + b : ℕ) : F101)
      = ((i.val * i.val + (if 40 ≤ i.val then 29 else 0) : ℕ) : F101) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  simp only [w101, dom101, Function.Embedding.coeFn_mk, pow_two]
  by_cases hb : 40 ≤ i.val
  · rw [if_pos hb] at hcast ⊢
    push_cast at hcast
    exact hcast
  · rw [if_neg hb] at hcast ⊢
    push_cast at hcast
    rw [add_zero] at hcast ⊢
    exact hcast

/-- The agreement-set family of the countermodel word. -/
def S101 : Finset (Finset (Fin 80)) := (lineDataN.map Prod.snd).toFinset

set_option maxRecDepth 100000 in
theorem S101_mass : 2 * 80 < ∑ A ∈ S101, A.card := by decide +kernel

theorem S101_family : ∀ A ∈ S101, (2 + 1 + 1 ≤ A.card) ∧
    ∃ c ∈ (rsCode dom101 2 : Submodule F101 (Fin 80 → F101)),
      A = Finset.univ.filter fun i => c i = w101 i := by
  intro A hA
  rw [S101, List.mem_toFinset, List.mem_map] at hA
  obtain ⟨pair, hmem, rfl⟩ := hA
  obtain ⟨hsub, hcard⟩ := line_facts_nat pair hmem
  exact ⟨by omega, fun i => (pair.1.1 : F101) * dom101 i + (pair.1.2 : F101),
    affine_mem_rsCode _ _,
    line_agreeSet_eq (fun i hi => line_eval_eq (hsub i hi)) hcard⟩

/-- **THE REFUTATION**: the universal mean-degree law is FALSE — the
two-branch parabola word at `(q, n) = (101, 80)` is agreement-capped and its
four-rich family carries mass `428 > 160 = 2n`. -/
theorem universalMeanDegreeLaw_REFUTED : ¬ UniversalMeanDegreeLaw := by
  intro h
  have hcap : ∀ c ∈ (rsCode dom101 2 : Submodule F101 (Fin 80 → F101)),
      (Finset.univ.filter fun i => c i = w101 i).card ≤ 2 * 2 + 1 + 1 := by
    rintro c ⟨P, hP, rfl⟩
    exact le_trans (w101_agreement_le_four hP) (by omega)
  have hlaw := h F101 80 dom101 2 1 w101 hcap S101 S101_family
  exact absurd hlaw (Nat.not_le.mpr S101_mass)

/-! ## The corrected open target

The refutation locates the true growth: the capped supply has TWO regimes,
the partition floor `Θ(n)` (dominant for `n³ ≲ q²` at this band) and the
random mean `Θ(C(n,k+m+1)/q^{m+1})` (which the two-branch family realizes
constructively once `n³ ≳ q²`).  The corrected conjecture — sufficient for
the deep-band consumer chain — is that nothing beats their sum by more than
a constant. -/

open Classical in
/-- **THE CORRECTED OPEN TARGET (the two-regime growth law, PRIME fields)**:
the capped per-word supply is bounded by `C₀·(n + C(n,k+m+1)/q^{m+1})` —
partition floor plus random mean.  The two-branch countermodel shows the
second term is REAL (not an artifact of uncapped words); the partition
censuses show the first is.

The prime-field restriction is NOT cosmetic: over `q = p²` with subfield
domain `D = F_p ⊂ F_{p²}`, the same two-branch construction runs entirely
inside the subfield plane and carries `~ n²/64` cores while the mean term
`C(n,4)/q²` collapses to `O(1)` — the general-field form of this law is
FALSE (self-refutation, recorded in `DISPROOF_LOG.md`; char-2/extension-field
production settings need a subfield-structure hypothesis).

**The Solymosi–Stojaković asymptotic red-team (free domains).**  [SS13]
(DCG 50(3):811–820; arXiv:1107.0327) Theorem 1: for `k ≥ 4` there are
`n`-point planar sets with NO `k+1` collinear and `> n^{2−c/√log n}` exact
collinear `k`-tuples, `c = 2·log₂(4k+9)` — integer-grid constructions whose
tuples are arithmetic progressions.  Sheared into a graph over `F_p`
(`p ≥ poly(coordinate bound)`), the `k = 4` case is a capped word (cap
`5 ≤ 6`) with `n^{2−o(1)}` explainable `4`-cores: this law is therefore
ASYMPTOTICALLY FALSE for free domains even over prime fields.  Quantitative
caveats that keep it the right probe-scale/production target: (i) the SS
exponent beats linear only once `√log n > c`, i.e. `n > 2^{87}` at `k = 4` —
beyond every production domain; (ii) the transport needs `q ≥ poly(n)` with
a large constant — at production `q = Θ(n)` (M31) the mod-`p` wraparound
destroys the cap; (iii) whether `t_k(n) = o(n²)` at fixed cap is Erdős's
open $100 problem (Brass–Moser–Pach, Conjecture 12) — the free-domain supply
wall IS that problem.  Production engine words moreover live on SMOOTH
MULTIPLICATIVE domains, where SS's arithmetic-progression mechanism (and the
subfield/Frobenius/GAP-grid mechanisms) have no room: the production-relevant
open target is `SmoothDomainTwoRegimeLaw` below.

Status: open at probe/production scales (adversarially calibrated
`C₀ ≤ 1.91`, `probe_two_regime_adversarial.py`); asymptotically false for
free domains by [SS13]-transport. -/
def CappedSupplyTwoRegimeLaw (C₀ : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    ∀ (n : ℕ) [NeZero n], ∀ (dom : Fin n ↪ ZMod p) (k m : ℕ) (w : Fin n → ZMod p),
    (∀ c ∈ (rsCode dom k : Submodule (ZMod p) (Fin n → ZMod p)),
        (Finset.univ.filter fun i => c i = w i).card ≤ 2 * k + m + 1) →
    (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ∃ c ∈ (rsCode dom k : Submodule (ZMod p) (Fin n → ZMod p)),
          ∀ i ∈ T, c i = w i)).card
      ≤ C₀ * (n + n.choose (k + m + 1) / p ^ (m + 1))

open Classical in
/-- **THE PRODUCTION-RELEVANT OPEN TARGET (the μ_n two-regime law)**: the
capped supply law on SMOOTH MULTIPLICATIVE domains over prime fields — the
domains the deep-band engine actually uses.  Every known superlinear
mechanism requires additive structure the multiplicative group `μ_n` lacks:
subfields (excluded: prime `q`), Frobenius `𝔽_p`-lines (excluded: prime `q`),
GAP/grid rows (additive), and the [SS13] tuples (arithmetic progressions —
`μ_n` carries only the mean count of long APs).  Status: open; this is the
sharpest production form of the sub-Johnson supply wall. -/
def SmoothDomainTwoRegimeLaw (C₀ : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    ∀ (n : ℕ) [NeZero n], ∀ (γ : ZMod p), orderOf γ = n →
    ∀ (dom : Fin n ↪ ZMod p), (∀ i, dom i = γ ^ (i : ℕ)) →
    ∀ (k m : ℕ) (w : Fin n → ZMod p),
    (∀ c ∈ (rsCode dom k : Submodule (ZMod p) (Fin n → ZMod p)),
        (Finset.univ.filter fun i => c i = w i).card ≤ 2 * k + m + 1) →
    (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ∃ c ∈ (rsCode dom k : Submodule (ZMod p) (Fin n → ZMod p)),
          ∀ i ∈ T, c i = w i)).card
      ≤ C₀ * (n + n.choose (k + m + 1) / p ^ (m + 1))

end ProximityGap.TwoBranch

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.TwoBranch.universalMeanDegreeLaw_REFUTED

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAHalfDistanceGeneralRefuted
import Mathlib.Tactic.ComputeDegree

/-!
# The MDS staircase conjecture is FALSE: the degenerate-pencil explosion (#357)

The directed-search record behind `MDSStaircaseConjecture` ("Reed–Solomon codes keep
the linear staircase down to `d ≥ 2b`") missed a degenerate-discriminant branch of the
Padé syzygy.  The **perfect-square pencil identity**

  `r·A² − h·A·B + p·B² = ρλ²·T^(f+2(b−1))`  for  `A = B + λT^(b−1)`, `p = r = ρT^f`,
  `h = 2ρT^f`

produces, for every family of disjoint `(b−1)`-point blocks of the evaluation domain
whose locators lie in one pencil `⟨B, T^(b−1)⟩`, an affine-in-γ family of weight-`(b−1)`
error words — i.e. one `mcaEvent`-bad scalar **per block** at band `b`, for every
distance `d = m + 1 ≤ 3b − 3` (`m = n − k = 2(b−1) + f`, `f ≤ b − 2`).  On smooth
domains the cosets of `μ_(b−1)` supply `n/(b−1)` such blocks (their locators are
`1 − x^(b−1)·T^(b−1)`), so RS explodes to `n/(b−1) > b` bad scalars throughout the strip
`2b − 1 ≤ d ≤ 3b − 3`: the `3b − 2` collapse threshold is sharp for MDS codes too, and
there is **no MDS/general separation at the staircase-threshold level**.

This file machine-checks the refuting instance `RS[F₁₉, μ₁₈ = F₁₉ˣ, k = 10]` (`n = 18`,
`d = 9 = 2·4 + 1`, `b = 4`, blocks = the six cosets of `μ₃`): the explicit stack below
carries the six bad scalars `{1, 3, 5, 15, 16, 17}` at `δ = 1/6` (band 4), of which five
are certified here — already contradicting the `≤ 4` claim of `MDSStaircaseConjecture`
at its in-hypothesis instance `k + 2b = 18 ≤ n`.

Probe: `scripts/probes/probe_mds_pencil_explosion.py` (exact end-to-end `mcaEvent`
verification at six instances, T1–T6).  Each certificate's joint-failure runs through
one root-counting engine (`joint_kill`): a would-be explanation of `u₁` on the witness
agrees with an explicit degree-9 interpolant at ten domain points, hence equals it,
and the interpolant conflicts with `u₁` at an eleventh witness point.

Issue #357.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCAMDSStaircaseRefuted

open ProximityGap.MCAHalfDistanceGeneralRefuted (MDSStaircaseConjecture)
open ProximityGap.MCAHalfDistanceStaircase (LinearStaircaseUpper)

abbrev F19 := ZMod 19

instance primeFact_MCAMDSStaircaseRefuted_1 : Fact (Nat.Prime 19) := ⟨by decide⟩

/-- The smooth domain `μ₁₈ = F₁₉ˣ`, enumerated as powers of the generator 2. -/
def dom : Fin 18 → F19 :=
  ![1, 2, 4, 8, 16, 13, 7, 14, 9, 18, 17, 15, 11, 3, 6, 12, 5, 10]

theorem dom_injective : Function.Injective dom := by decide

def domEmb : Fin 18 ↪ F19 := ⟨dom, dom_injective⟩

/-- The refuting code: `RS[F₁₉, μ₁₈, 10]` (the canonical `ReedSolomon.code`). -/
noncomputable abbrev rsC : Submodule F19 (Fin 18 → F19) := ReedSolomon.code domEmb 10

/-! ## Membership and extraction for the canonical RS code -/

/-- Degree-9 membership helper: explicit-coefficient codewords. -/
theorem deg9_mem (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ : F19) :
    (fun i => a₀ + a₁ * dom i + a₂ * dom i ^ 2 + a₃ * dom i ^ 3 + a₄ * dom i ^ 4 +
      a₅ * dom i ^ 5 + a₆ * dom i ^ 6 + a₇ * dom i ^ 7 + a₈ * dom i ^ 8 +
      a₉ * dom i ^ 9) ∈ rsC := by
  refine Submodule.mem_map.mpr
    ⟨C a₉ * X ^ 9 + C a₈ * X ^ 8 + C a₇ * X ^ 7 + C a₆ * X ^ 6 + C a₅ * X ^ 5 +
      C a₄ * X ^ 4 + C a₃ * X ^ 3 + C a₂ * X ^ 2 + C a₁ * X + C a₀, ?_, ?_⟩
  · rw [Polynomial.mem_degreeLT]
    compute_degree!
  · funext i
    show (_ : Polynomial F19).eval (dom i) = _
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    ring

/-- Extraction: every codeword is the evaluation of a degree-`< 10` polynomial. -/
theorem rsC_extract {w : Fin 18 → F19} (hw : w ∈ rsC) :
    ∃ P : Polynomial F19, P.degree < 10 ∧ ∀ i, w i = P.eval (dom i) := by
  obtain ⟨P, hP, hPw⟩ := Submodule.mem_map.mp hw
  exact ⟨P, Polynomial.mem_degreeLT.mp hP, fun i => (congrFun hPw i).symm⟩

/-! ## The stack -/

/-- First row of the pencil stack (twisted-syndrome series `T²/(1 + 6T³ + T³)`-type;
support on the first eight powers plus index 12). -/
def u₀ : Fin 18 → F19 := ![2, 12, 10, 12, 14, 0, 2, 11, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0]

/-- Second row (twisted-syndrome series `T²/(1 + 6T³)`-type). -/
def u₁ : Fin 18 → F19 := ![3, 9, 17, 9, 1, 0, 3, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-! ## The joint-failure engine -/

/-- **The root-counting kill.**  If a degree-9 interpolant (explicit coefficients
`q₀,…,q₉`) matches `u₁` on ten witness positions whose domain values are distinct, but
conflicts with `u₁` at an eleventh witness position, then no codeword pair jointly
explains `(u₀, u₁)` on the witness: the would-be explanation of `u₁` agrees with the
interpolant at ten points, so (both having degree `< 10`) equals it — contradicting the
conflict. -/
theorem joint_kill (T I : Finset (Fin 18)) (hIT : I ⊆ T)
    (q₀ q₁ q₂ q₃ q₄ q₅ q₆ q₇ q₈ q₉ : F19)
    (hcard : 10 ≤ (I.image dom).card)
    (hint : ∀ i ∈ I, q₀ + q₁ * dom i + q₂ * dom i ^ 2 + q₃ * dom i ^ 3 +
      q₄ * dom i ^ 4 + q₅ * dom i ^ 5 + q₆ * dom i ^ 6 + q₇ * dom i ^ 7 +
      q₈ * dom i ^ 8 + q₉ * dom i ^ 9 = u₁ i)
    (c : Fin 18) (hcT : c ∈ T)
    (hconf : q₀ + q₁ * dom c + q₂ * dom c ^ 2 + q₃ * dom c ^ 3 + q₄ * dom c ^ 4 +
      q₅ * dom c ^ 5 + q₆ * dom c ^ 6 + q₇ * dom c ^ 7 + q₈ * dom c ^ 8 +
      q₉ * dom c ^ 9 ≠ u₁ c) :
    ¬ pairJointAgreesOn (rsC : Set (Fin 18 → F19)) T u₀ u₁ := by
  rintro ⟨v₀, _, v₁, hv₁, hag⟩
  obtain ⟨P, hPdeg, hPv⟩ := rsC_extract hv₁
  set Q : Polynomial F19 :=
    C q₉ * X ^ 9 + C q₈ * X ^ 8 + C q₇ * X ^ 7 + C q₆ * X ^ 6 + C q₅ * X ^ 5 +
      C q₄ * X ^ 4 + C q₃ * X ^ 3 + C q₂ * X ^ 2 + C q₁ * X + C q₀ with hQ
  have hQeval : ∀ x : F19, Q.eval x =
      q₀ + q₁ * x + q₂ * x ^ 2 + q₃ * x ^ 3 + q₄ * x ^ 4 + q₅ * x ^ 5 + q₆ * x ^ 6 +
        q₇ * x ^ 7 + q₈ * x ^ 8 + q₉ * x ^ 9 := by
    intro x
    simp only [hQ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  have hQdeg : Q.degree < 10 := by
    rw [hQ]
    compute_degree!
  have hPQ : P - Q = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
      (f := P - Q) (s := I.image dom) ?_ ?_
    · refine lt_of_le_of_lt (Polynomial.degree_sub_le P Q) (max_lt ?_ ?_) <;>
        [exact lt_of_lt_of_le hPdeg (by exact_mod_cast hcard);
         exact lt_of_lt_of_le hQdeg (by exact_mod_cast hcard)]
    · intro x hx
      obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp hx
      have h1 : v₁ i = P.eval (dom i) := hPv i
      have h2 : v₁ i = u₁ i := (hag i (hIT hiI)).2
      have h3 : Q.eval (dom i) = u₁ i := by rw [hQeval]; exact hint i hiI
      rw [Polynomial.eval_sub, ← h1, h2, h3, sub_self]
  have hPeqQ : P = Q := sub_eq_zero.mp hPQ
  have hvc : v₁ c = u₁ c := (hag c hcT).2
  have hQc : v₁ c = Q.eval (dom c) := by rw [hPv c, hPeqQ]
  exact hconf (by rw [← hQeval (dom c), ← hQc, hvc])

/-! ## The certificates: five bad scalars at `δ = 1/6` (band 4) -/

/-- The size clause at `δ = 1/6`, `n = 18`: a 15-element witness suffices
(`(1 − 1/6)·18 = 15`). -/
theorem card_clause {T : Finset (Fin 18)} (hT : T.card = 15) :
    (T.card : ℝ≥0) ≥ (1 - (1/6 : ℝ≥0)) * (Fintype.card (Fin 18) : ℝ≥0) := by
  have h16 : (1/6 : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by norm_num : (0:ℝ≥0) < 6)]
    norm_num
  have h56 : (1 : ℝ≥0) - 1/6 = 5/6 := by
    rw [tsub_eq_iff_eq_add_of_le h16]
    rw [← NNReal.coe_inj]
    push_cast
    norm_num
  rw [hT, h56, Fintype.card_fin, ge_iff_le, ← NNReal.coe_le_coe]
  push_cast
  norm_num

/-- **Certificate γ = 5** (block = the coset `{1, 7, 11} = μ₃`): the line point *is*
the error word (explanation 0); the interpolant through ten witness points conflicts
with `u₁` at index 13. -/
theorem cert5 : mcaEvent (F := F19) (rsC : Set (Fin 18 → F19)) (1/6) u₀ u₁ 5 := by
  refine ⟨{1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17}, card_clause (by decide),
    ⟨0, Submodule.zero_mem _, ?_⟩, ?_⟩
  · intro i hi
    fin_cases hi <;> decide
  · exact joint_kill _ {1, 2, 3, 4, 5, 7, 8, 9, 10, 11} (by decide)
      14 5 15 2 11 10 12 14 13 15 (by decide) (by decide) 13 (by decide) (by decide)

/-- **Certificate γ = 16** (block `{2, 14, 3}`). -/
theorem cert16 : mcaEvent (F := F19) (rsC : Set (Fin 18 → F19)) (1/6) u₀ u₁ 16 := by
  refine ⟨{0, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 16, 17}, card_clause (by decide),
    ⟨_, deg9_mem 14 18 8 1 1 5 3 18 18 2, ?_⟩, ?_⟩
  · intro i hi
    fin_cases hi <;> decide
  · exact joint_kill _ {0, 2, 3, 4, 5, 6, 8, 9, 10, 11} (by decide)
      7 4 7 14 3 14 9 2 4 15 (by decide) (by decide) 12 (by decide) (by decide)

/-- **Certificate γ = 1** (block `{4, 9, 6}`). -/
theorem cert1 : mcaEvent (F := F19) (rsC : Set (Fin 18 → F19)) (1/6) u₀ u₁ 1 := by
  refine ⟨{0, 1, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17}, card_clause (by decide),
    ⟨_, deg9_mem 14 9 4 7 10 12 13 9 9 13, ?_⟩, ?_⟩
  · intro i hi
    fin_cases hi <;> decide
  · exact joint_kill _ {0, 1, 3, 4, 5, 6, 7, 9, 10, 11} (by decide)
      1 16 5 0 8 15 16 6 0 12 (by decide) (by decide) 12 (by decide) (by decide)

/-- **Certificate γ = 17** (block `{8, 18, 12}`). -/
theorem cert17 : mcaEvent (F := F19) (rsC : Set (Fin 18 → F19)) (1/6) u₀ u₁ 17 := by
  refine ⟨{0, 1, 2, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 16, 17}, card_clause (by decide),
    ⟨_, deg9_mem 10 11 7 0 8 2 16 11 11 15, ?_⟩, ?_⟩
  · intro i hi
    fin_cases hi <;> decide
  · exact joint_kill _ {0, 1, 2, 4, 5, 6, 7, 8, 10, 11} (by decide)
      14 2 5 5 13 8 7 9 3 13 (by decide) (by decide) 12 (by decide) (by decide)

/-- **Certificate γ = 3** (block `{13, 15, 10}`). -/
theorem cert3 : mcaEvent (F := F19) (rsC : Set (Fin 18 → F19)) (1/6) u₀ u₁ 3 := by
  refine ⟨{0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16}, card_clause (by decide),
    ⟨_, deg9_mem 8 14 2 14 5 6 5 14 14 5, ?_⟩, ?_⟩
  · intro i hi
    fin_cases hi <;> decide
  · exact joint_kill _ {0, 1, 2, 3, 4, 6, 7, 8, 9, 10} (by decide)
      7 17 6 10 14 14 1 2 2 6 (by decide) (by decide) 12 (by decide) (by decide)

/-! ## The refutation -/

open Classical in
/-- **`MDSStaircaseConjecture` is FALSE.**  At its in-hypothesis instance
`RS[F₁₉, F₁₉ˣ, k = 10]` (`n = 18`, `k + 2b = 18 ≤ 18`, `b = 4`, `d = 9 = 2b + 1`), the
degenerate-pencil stack carries five certified bad scalars `{1, 3, 5, 16, 17}` at
`δ = 1/6` (band 4, `δ·n = 3 < 4`) — exceeding the conjectured cap `b = 4`.  The
Reed–Solomon staircase does **not** collapse below the universal `3b − 2` threshold:
the strip `2b − 1 ≤ d ≤ 3b − 3` explodes for MDS codes exactly as for general linear
codes. -/
theorem mdsStaircaseConjecture_refuted : ¬ MDSStaircaseConjecture := by
  intro h
  have hLSU : LinearStaircaseUpper (ReedSolomon.code domEmb 10) 4 :=
    h (Fin 18) inferInstance inferInstance inferInstance F19 inferInstance inferInstance
      inferInstance domEmb 10 4 (by norm_num) (by rw [Fintype.card_fin])
  have hδ : ((1 : ℝ≥0)/6) * (Fintype.card (Fin 18) : ℝ≥0) < ((4 : ℕ) : ℝ≥0) := by
    rw [Fintype.card_fin, ← NNReal.coe_lt_coe]
    push_cast
    norm_num
  have hcap := hLSU (1/6) hδ ![u₀, u₁]
  have hsub : ({1, 3, 5, 16, 17} : Finset F19) ⊆ Finset.filter (fun γ : F19 =>
      mcaEvent (F := F19) ((ReedSolomon.code domEmb 10 :
        Submodule F19 (Fin 18 → F19)) : Set (Fin 18 → F19)) (1/6)
        ((![u₀, u₁] : WordStack F19 (Fin 2) (Fin 18)) 0)
        ((![u₀, u₁] : WordStack F19 (Fin 2) (Fin 18)) 1) γ) Finset.univ := by
    intro γ hγ
    fin_cases hγ
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, cert1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, cert3⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, cert5⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, cert16⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, cert17⟩
  have h5 : (5 : ℕ) ≤ (Finset.filter (fun γ : F19 =>
      mcaEvent (F := F19) ((ReedSolomon.code domEmb 10 :
        Submodule F19 (Fin 18 → F19)) : Set (Fin 18 → F19)) (1/6)
        ((![u₀, u₁] : WordStack F19 (Fin 2) (Fin 18)) 0)
        ((![u₀, u₁] : WordStack F19 (Fin 2) (Fin 18)) 1) γ) Finset.univ).card := by
    calc (5 : ℕ) = ({1, 3, 5, 16, 17} : Finset F19).card := by decide
      _ ≤ _ := Finset.card_le_card hsub
  omega

end ProximityGap.MCAMDSStaircaseRefuted

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.MCAMDSStaircaseRefuted.cert1
#print axioms ProximityGap.MCAMDSStaircaseRefuted.mdsStaircaseConjecture_refuted

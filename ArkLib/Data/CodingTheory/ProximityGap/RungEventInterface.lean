/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungFrameGeometry
import ArkLib.Data.CodingTheory.ProximityGap.MCAExactComputationKit
import Mathlib.LinearAlgebra.Lagrange

/-!
# The rung event interface (#371): mcaEvent ⟺ defect identity

The bridge between the probabilistic obligation (`epsMCA`/`mcaEventNat` over
`evalCode`-style codes) and the polynomial defect identities on which the
whole rung programme's structural laws operate
(`RungAgreementGeometry` … `RungFrameGeometry`).

* `domCode dom d` — words that are evaluations of degree-`≤ d` polynomials
  on an embedded domain (the domain-general form of `evalCode`);
* `vanishingPoly_dvd_of_eval_zero` — the vanishing ⟹ divisibility helper
  (factored out of four inline uses);
* `rowPoly` — the degree-`< n` interpolant of a word;
* `explainable_iff_defect` — the line is explainable on `S` iff the rows'
  interpolants satisfy a defect identity `R₀ + C γ·R₁ − P = g·m_S`;
* `pairJoint_iff_rows_explainable` — the joint clause in row form;
* `mcaEventNat_iff_defect` — the full event translation.

Downstream: `badScalarCount C t u₀ u₁ ≤ B` reduces to counting scalars
with defect identities — the assembly's native habitat.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section Interface

variable (dom : Fin n ↪ F)

/-- The domain-general evaluation code: evaluations of degree-`≤ d`
polynomials on the embedded domain. -/
def domCode (d : ℕ) : Set (Fin n → F) :=
  {w | ∃ q : F[X], q.natDegree ≤ d ∧ ∀ i : Fin n, w i = q.eval (dom i)}

/-- Vanishing on `T` gives divisibility by the vanishing polynomial. -/
theorem vanishingPoly_dvd_of_eval_zero {T : Finset (Fin n)} {f : F[X]}
    (h : ∀ i ∈ T, f.eval (dom i) = 0) :
    vanishingPoly dom T ∣ f := by
  rw [vanishingPoly]
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · intro i hi j hj hij
    exact isCoprime_X_sub_C_of_isUnit_sub
      (Ne.isUnit (sub_ne_zero.mpr (fun hc => hij (dom.injective hc))))
  · intro i hi
    rw [Polynomial.dvd_iff_isRoot]
    exact h i hi

/-- The degree-`< n` interpolant of a word on the embedded domain. -/
noncomputable def rowPoly (u : Fin n → F) : F[X] :=
  Lagrange.interpolate Finset.univ (fun i => dom i) u

theorem rowPoly_eval (u : Fin n → F) (i : Fin n) :
    (rowPoly dom u).eval (dom i) = u i :=
  Lagrange.eval_interpolate_at_node u dom.injective.injOn (Finset.mem_univ i)

/-- **Explainability ⟺ defect identity.**  The folded line agrees with a
degree-`≤ d` codeword on `S` iff the row interpolants satisfy an exact
division identity against `m_S`. -/
theorem explainable_iff_defect (d : ℕ) (u₀ u₁ : Fin n → F) (γ : F)
    (S : Finset (Fin n)) :
    (∃ w ∈ domCode dom d, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) ↔
    ∃ P : F[X], P.natDegree ≤ d ∧ ∃ q : F[X],
      rowPoly dom u₀ + C γ * rowPoly dom u₁ - P = q * vanishingPoly dom S := by
  constructor
  · rintro ⟨w, ⟨P, hPd, hPw⟩, hwS⟩
    refine ⟨P, hPd, ?_⟩
    have hvan : ∀ i ∈ S,
        (rowPoly dom u₀ + C γ * rowPoly dom u₁ - P).eval (dom i) = 0 := by
      intro i hi
      have h1 := hwS i hi
      rw [hPw i] at h1
      simp only [eval_sub, eval_add, eval_mul, eval_C, rowPoly_eval]
      rw [smul_eq_mul] at h1
      linear_combination -h1
    obtain ⟨q, hq⟩ := vanishingPoly_dvd_of_eval_zero dom hvan
    exact ⟨q, by rw [hq, mul_comm]⟩
  · rintro ⟨P, hPd, q, hid⟩
    refine ⟨fun i => P.eval (dom i), ⟨P, hPd, fun i => rfl⟩, ?_⟩
    intro i hi
    have hev := congrArg (Polynomial.eval (dom i)) hid
    rw [eval_mul, vanishingPoly_eval_eq_zero dom hi, mul_zero] at hev
    simp only [eval_sub, eval_add, eval_mul, eval_C, rowPoly_eval] at hev
    rw [smul_eq_mul]
    linear_combination -hev

/-- **The joint clause in row form**: a joint pair exists iff both rows are
individually `≤ d`-explainable on `S`. -/
theorem pairJoint_iff_rows_explainable (d : ℕ) (u₀ u₁ : Fin n → F)
    (S : Finset (Fin n)) :
    pairJointAgreesOn (domCode dom d) S u₀ u₁ ↔
    (∃ q₀ : F[X], q₀.natDegree ≤ d ∧ ∀ i ∈ S, q₀.eval (dom i) = u₀ i) ∧
    (∃ q₁ : F[X], q₁.natDegree ≤ d ∧ ∀ i ∈ S, q₁.eval (dom i) = u₁ i) := by
  constructor
  · rintro ⟨v₀, ⟨P₀, hP₀, hv₀⟩, v₁, ⟨P₁, hP₁, hv₁⟩, hag⟩
    exact ⟨⟨P₀, hP₀, fun i hi => by rw [← hv₀ i]; exact (hag i hi).1⟩,
           ⟨P₁, hP₁, fun i hi => by rw [← hv₁ i]; exact (hag i hi).2⟩⟩
  · rintro ⟨⟨q₀, hq₀d, hq₀⟩, ⟨q₁, hq₁d, hq₁⟩⟩
    exact ⟨fun i => q₀.eval (dom i), ⟨q₀, hq₀d, fun i => rfl⟩,
           fun i => q₁.eval (dom i), ⟨q₁, hq₁d, fun i => rfl⟩,
           fun i hi => ⟨hq₀ i hi, hq₁ i hi⟩⟩

/-- **The full event translation**: `mcaEventNat` on the domain code is the
defect-identity event on the row interpolants. -/
theorem mcaEventNat_iff_defect (d t : ℕ) (u₀ u₁ : Fin n → F) (γ : F) :
    ProximityGap.MCAExactKit.mcaEventNat (F := F) (domCode dom d) t u₀ u₁ γ ↔
    ∃ S : Finset (Fin n), t ≤ S.card ∧
      (∃ P : F[X], P.natDegree ≤ d ∧ ∃ q : F[X],
        rowPoly dom u₀ + C γ * rowPoly dom u₁ - P = q * vanishingPoly dom S) ∧
      ¬ ((∃ q₀ : F[X], q₀.natDegree ≤ d ∧ ∀ i ∈ S, q₀.eval (dom i) = u₀ i) ∧
         (∃ q₁ : F[X], q₁.natDegree ≤ d ∧ ∀ i ∈ S, q₁.eval (dom i) = u₁ i)) := by
  unfold ProximityGap.MCAExactKit.mcaEventNat
  refine exists_congr fun S => ?_
  rw [explainable_iff_defect dom d u₀ u₁ γ S,
    pairJoint_iff_rows_explainable dom d u₀ u₁ S]

end Interface

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.vanishingPoly_dvd_of_eval_zero
#print axioms ProximityGap.WBPencil.explainable_iff_defect
#print axioms ProximityGap.WBPencil.pairJoint_iff_rows_explainable
#print axioms ProximityGap.WBPencil.mcaEventNat_iff_defect

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section Router

variable (dom : Fin n ↪ F)

open Polynomial

/-- **The in-A joint kill**: a witness contained in an agreement set of the
direction row is automatically jointly explained — so the `¬ joint` clause
forces every bad witness to leave `A`. -/
theorem rows_explainable_of_witness_in_agreement (d : ℕ) (u₀ u₁ : Fin n → F)
    {γ : F} {P q g : F[X]} {S A : Finset (Fin n)}
    (hq : q.natDegree ≤ d) (hP : P.natDegree ≤ d)
    (hA : ∀ i ∈ A, (rowPoly dom u₁).eval (dom i) = q.eval (dom i))
    (hid : rowPoly dom u₀ + C γ * rowPoly dom u₁ - P
      = g * vanishingPoly dom S)
    (hSA : S ⊆ A) :
    (∃ q₀ : F[X], q₀.natDegree ≤ d ∧ ∀ i ∈ S, q₀.eval (dom i) = u₀ i) ∧
    (∃ q₁ : F[X], q₁.natDegree ≤ d ∧ ∀ i ∈ S, q₁.eval (dom i) = u₁ i) := by
  constructor
  · refine ⟨P - C γ * q, ?_, ?_⟩
    · have h1 : (C γ * q).natDegree ≤ d :=
        le_trans (natDegree_C_mul_le _ _) hq
      exact le_trans (natDegree_sub_le _ _) (max_le hP h1)
    · intro i hi
      have hev := congrArg (Polynomial.eval (dom i)) hid
      rw [eval_mul, vanishingPoly_eval_eq_zero dom hi, mul_zero] at hev
      have hAi := hA i (hSA hi)
      rw [rowPoly_eval] at hAi
      simp only [eval_sub, eval_add, eval_mul, eval_C, rowPoly_eval] at hev ⊢
      linear_combination -hev + γ * hAi
  · exact ⟨q, hq, fun i hi => by rw [← hA i (hSA hi), rowPoly_eval]⟩

open Classical in
/-- **The identity-level census bound** — the single named target of the
rung assembly: every stack carries at most `B` scalars with a
defect-identity witness of size ≥ `t` that is not jointly explained. -/
def IdentityCensusBound (d t B : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F,
    (Finset.univ.filter (fun γ : F =>
      ∃ S : Finset (Fin n), t ≤ S.card ∧
        (∃ P : F[X], P.natDegree ≤ d ∧ ∃ q : F[X],
          rowPoly dom u₀ + C γ * rowPoly dom u₁ - P
            = q * vanishingPoly dom S) ∧
        ¬ ((∃ q₀ : F[X], q₀.natDegree ≤ d ∧
              ∀ i ∈ S, q₀.eval (dom i) = u₀ i) ∧
           (∃ q₁ : F[X], q₁.natDegree ≤ d ∧
              ∀ i ∈ S, q₁.eval (dom i) = u₁ i)))).card ≤ B

open Classical in
/-- The census router: the identity-level bound caps `badScalarCount`. -/
theorem badScalarCount_le_of_identityCensusBound
    {d t B : ℕ} (h : IdentityCensusBound dom d t B) (u₀ u₁ : Fin n → F) :
    ProximityGap.MCAExactKit.badScalarCount (F := F) (domCode dom d) t u₀ u₁
      ≤ B := by
  refine le_trans (Finset.card_le_card ?_) (h u₀ u₁)
  intro γ hγ
  rw [Finset.mem_filter] at hγ ⊢
  exact ⟨hγ.1, (mcaEventNat_iff_defect dom d t u₀ u₁ γ).mp hγ.2⟩

open Classical in
/-- **The epsMCA router**: the identity-level census bound discharges the
probabilistic obligation — `ε_mca(domCode, δ) ≤ B/|F|` whenever the
threshold `t` matches the cardinality clause at `δ`. -/
theorem epsMCA_le_of_identityCensusBound
    {d t B : ℕ} {δ : ℝ≥0}
    (ht : ∀ S : Finset (Fin n),
      ((S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) ↔ t ≤ S.card)
    (h : IdentityCensusBound dom d t B) :
    epsMCA (F := F) (A := F) (domCode dom d) δ
      ≤ (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  rw [ProximityGap.MCAExactKit.epsMCA_eq_sup_badScalarCount (domCode dom d) ht]
  refine ENNReal.div_le_div_right ?_ _
  refine Nat.cast_le.mpr (Finset.sup_le fun u _ => ?_)
  exact badScalarCount_le_of_identityCensusBound dom h (u 0) (u 1)

end Router

end ProximityGap.WBPencil

#print axioms ProximityGap.WBPencil.rows_explainable_of_witness_in_agreement
#print axioms ProximityGap.WBPencil.badScalarCount_le_of_identityCensusBound
#print axioms ProximityGap.WBPencil.epsMCA_le_of_identityCensusBound

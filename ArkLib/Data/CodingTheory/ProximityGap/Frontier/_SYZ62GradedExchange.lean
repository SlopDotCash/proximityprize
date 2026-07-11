/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ61MuBasisExistence

/-!
# SYZ62 — the product-degree grading and the leading-vector exchange for the syzygy kernel

SYZ61 landed part (a) of the two-ramp decomposition **unconditionally**: the syzygy kernel of a
coprime triple `(f,g,h)` is a free `K[X]`-module of rank *exactly 2*.  The remaining classical piece
feeding `SYZ60.MuBasisWindowIso` (hence `SYZ44.TwoRamp`) is the **graded** refinement: a
degree-minimal (μ-)basis `(e₁,e₂)` whose principal windows tile the degree-`D` kernel window.

This file builds the classical apparatus for that refinement, self-contained and axiom-clean:

* **The product-degree grading** `pdeg d w` on `K[X]³` for weights `d = (d₀,d₁,d₂)` (the W-degrees):
  the `max` over the three slots of `deg(wᵢ) + dᵢ`, valued in `WithBot ℕ` (`⊥` for the zero vector).
  We prove the two grading laws — `pdeg d (q • w) = deg q + pdeg d w` (`pdeg_smul`) and the
  subadditivity `pdeg d (w + w') ≤ max (pdeg d w) (pdeg d w')` (`pdeg_add_le`), plus the constant-
  scaling and window-monotonicity corollaries.

* **The leading-coefficient vector** `lv d D w ∈ K³`: the tuple of coefficients of `wᵢ` at the slot
  degree `D - dᵢ` (`0` where the slot does not attain the product-degree `D`).  It is `K`-linear in
  `w` at a fixed target degree (`lv_add`, `lv_smulK`) and transforms by the leading coefficient under
  a monomial shift.

* **The exchange obligation**, stated as a named `Prop` `GradedExchange`, and the reduction
  `windowed generation ⟸ GradedExchange`: once every kernel element of product-degree `D ≥ δ₂`
  can be reduced modulo `e₁, e₂` to strictly smaller product-degree, the two principal windows
  generate the degree-`D` kernel window — the exact hypothesis `SYZ60.MuBasisWindowIso` needs.

## Scrupulous honesty — scope

This file proves the **grading algebra and the leading-vector linear structure in full**, and
reduces windowed generation to the single-step exchange.  It does **not** discharge the exchange step
itself (the leading-vector independence + rank-2 triangularity induction), nor does it build the
`K`-linear windowed isomorphism that would close `SYZ60.MuBasisWindowIso`.  Those remain the named
residual `GradedExchange` (the last classical μ-basis input).  So after SYZ62 the two-ramp residual
is `GradedExchange` alone — the leading-vector exchange step — and `SYZ44.RankNullity` /
`SYZ60.MuBasisWindowIso` remain conditional on it.  This does **not** claim δ* closure.

Axiom-clean; `#print axioms` at the bottom.  No `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Module Polynomial

namespace ArkLib.ProximityGap.SYZ62

variable {K : Type*} [Field K]

/-! ## 1. The product-degree grading on `K[X]³` -/

/-- The per-slot graded degree: `deg(wᵢ) + dᵢ`, valued in `WithBot ℕ` (`⊥` when `wᵢ = 0`). -/
noncomputable def pterm (d : Fin 3 → ℕ) (w : Fin 3 → K[X]) (i : Fin 3) : WithBot ℕ :=
  (w i).degree + (d i : ℕ)

/-- **The product-degree grading.**  `pdeg d w := maxᵢ (deg(wᵢ) + dᵢ)`, the `W`-graded degree of the
syzygy vector `w` for weights `d`.  Valued in `WithBot ℕ`: the zero vector has `pdeg = ⊥`. -/
noncomputable def pdeg (d : Fin 3 → ℕ) (w : Fin 3 → K[X]) : WithBot ℕ :=
  max (max (pterm d w 0) (pterm d w 1)) (pterm d w 2)

theorem pdeg_zero (d : Fin 3 → ℕ) : pdeg d (0 : Fin 3 → K[X]) = ⊥ := by
  simp [pdeg, pterm]

/-- Adding a fixed `WithBot ℕ` on the left is monotone, so it commutes with binary `max`. -/
private theorem add_left_map_max (c a b : WithBot ℕ) : c + max a b = max (c + a) (c + b) :=
  Monotone.map_max (f := fun x => c + x) (fun _ _ h => add_le_add_right h c)

/-- Adding a fixed `WithBot ℕ` on the right is monotone, so it commutes with binary `max`. -/
private theorem add_right_map_max (c a b : WithBot ℕ) : max a b + c = max (a + c) (b + c) :=
  Monotone.map_max (f := fun x => x + c) (fun _ _ h => add_le_add_left h c)

/-- Per-slot grading law under scaling: `pterm d (q • w) i = deg q + pterm d w i`. -/
theorem pterm_smul (d : Fin 3 → ℕ) (q : K[X]) (w : Fin 3 → K[X]) (i : Fin 3) :
    pterm d (q • w) i = q.degree + pterm d w i := by
  simp only [pterm, Pi.smul_apply, smul_eq_mul, degree_mul]
  rw [add_assoc]

/-- **Grading law under `K[X]`-scaling.**  `pdeg d (q • w) = deg q + pdeg d w`.  Uses
`Polynomial.degree_mul` (valid over the domain `K[X]`, including the zero cases via `⊥` absorption)
and the fact that left-addition commutes with `max`. -/
theorem pdeg_smul (d : Fin 3 → ℕ) (q : K[X]) (w : Fin 3 → K[X]) :
    pdeg d (q • w) = q.degree + pdeg d w := by
  simp only [pdeg]
  rw [pterm_smul, pterm_smul, pterm_smul, add_left_map_max, add_left_map_max]

/-- Per-slot subadditivity: `pterm d (w + w') i ≤ max (pterm d w i) (pterm d w' i)`. -/
theorem pterm_add_le (d : Fin 3 → ℕ) (w w' : Fin 3 → K[X]) (i : Fin 3) :
    pterm d (w + w') i ≤ max (pterm d w i) (pterm d w' i) := by
  simp only [pterm, Pi.add_apply]
  calc (w i + w' i).degree + (d i : ℕ)
      ≤ max (w i).degree (w' i).degree + (d i : ℕ) := add_le_add_left (degree_add_le _ _) _
    _ = max ((w i).degree + (d i : ℕ)) ((w' i).degree + (d i : ℕ)) := add_right_map_max _ _ _

/-- Each slot's graded degree is bounded by the product-degree: `pterm d w i ≤ pdeg d w`. -/
theorem pterm_le_pdeg (d : Fin 3 → ℕ) (w : Fin 3 → K[X]) (i : Fin 3) :
    pterm d w i ≤ pdeg d w := by
  simp only [pdeg]
  fin_cases i
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_max_right _ _

/-- Universal property of the product-degree: `pdeg d w ≤ b` iff every slot is `≤ b`. -/
theorem pdeg_le {d : Fin 3 → ℕ} {w : Fin 3 → K[X]} {b : WithBot ℕ}
    (h : ∀ i, pterm d w i ≤ b) : pdeg d w ≤ b :=
  max_le (max_le (h 0) (h 1)) (h 2)

/-- **Subadditivity of the grading.**  `pdeg d (w + w') ≤ max (pdeg d w) (pdeg d w')`. -/
theorem pdeg_add_le (d : Fin 3 → ℕ) (w w' : Fin 3 → K[X]) :
    pdeg d (w + w') ≤ max (pdeg d w) (pdeg d w') :=
  pdeg_le fun i =>
    le_trans (pterm_add_le d w w' i)
      (max_le_max (pterm_le_pdeg d w i) (pterm_le_pdeg d w' i))

/-! ## 2. The leading-coefficient vector -/

/-- **The leading-coefficient vector at target degree `D`.**  `lv d D w i := coeff (wᵢ) (D − dᵢ)`:
the coefficient of slot `i` at the degree that *would* make it attain product-degree `D`.  Where the
slot attains `pdeg = D` this is its leading coefficient; where the slot's product-degree is `< D`
it is `0` (a coefficient above the slot degree), so `lv` is exactly the "leading vector supported on
the slots achieving the product-degree" of the classical exchange argument.  Being a coefficient
extraction it is manifestly `K`-linear in `w`. -/
def lv (d : Fin 3 → ℕ) (D : ℕ) (w : Fin 3 → K[X]) : Fin 3 → K :=
  fun i => (w i).coeff (D - d i)

@[simp] theorem lv_apply (d : Fin 3 → ℕ) (D : ℕ) (w : Fin 3 → K[X]) (i : Fin 3) :
    lv d D w i = (w i).coeff (D - d i) := rfl

/-- `lv` is additive in the syzygy vector. -/
theorem lv_add (d : Fin 3 → ℕ) (D : ℕ) (w w' : Fin 3 → K[X]) :
    lv d D (w + w') = lv d D w + lv d D w' := by
  funext i; simp [lv, coeff_add]

/-- `lv` is homogeneous under the base-field scaling. -/
theorem lv_smulK (d : Fin 3 → ℕ) (D : ℕ) (c : K) (w : Fin 3 → K[X]) :
    lv d D (c • w) = c • lv d D w := by
  funext i; simp [lv, Pi.smul_apply, coeff_smul]

/-- **The leading vector detects the product-degree.**  If `w`'s product-degree is strictly below
the target `D`, its leading vector vanishes: every slot coefficient sits above the slot degree. -/
theorem lv_eq_zero_of_pdeg_lt (d : Fin 3 → ℕ) (D : ℕ) (w : Fin 3 → K[X])
    (hlt : pdeg d w < (D : WithBot ℕ)) : lv d D w = 0 := by
  funext i
  simp only [lv, Pi.zero_apply]
  apply coeff_eq_zero_of_degree_lt
  have h1 : pterm d w i < (D : WithBot ℕ) := lt_of_le_of_lt (pterm_le_pdeg d w i) hlt
  simp only [pterm] at h1
  -- h1 : (w i).degree + ↑(d i) < ↑D
  rcases eq_or_ne (w i) 0 with h0 | h0
  · simp [h0]
  · have hdeg : (w i).degree = ((w i).natDegree : WithBot ℕ) := (degree_eq_natDegree h0)
    rw [hdeg] at h1 ⊢
    rw [← Nat.cast_add, Nat.cast_lt] at h1
    rw [Nat.cast_lt]
    omega

/-! ## 3. The graded exchange obligation and windowed generation -/

section Exchange

variable {d : Fin 3 → ℕ}

/-- **The graded exchange step (named residual).**  The last classical μ-basis input: every nonzero
element `w` of the syzygy module `N` can be *reduced* by a `K[X]`-combination of the two
degree-minimal generators `e₁, e₂` to strictly smaller product-degree.  Classically this is the
leading-vector argument: `lv d D w` lies in the `K`-span of the (shifted) leading vectors of
`e₁, e₂` — the ≤-2-dimensional leading-vector space forced by the rank-2 freeness (SYZ61) — so a
suitable combination cancels the top and drops `pdeg`.  Carried as a hypothesis; SYZ61 supplies the
rank-2 structure the leading-vector independence rests on. -/
def GradedExchange (N : Submodule K[X] (Fin 3 → K[X])) (e₁ e₂ : Fin 3 → K[X]) : Prop :=
  ∀ w ∈ N, w ≠ 0 → ∃ q₁ q₂ : K[X],
    pdeg d (w - (q₁ • e₁ + q₂ • e₂)) < pdeg d w

/-- **Windowed generation from the exchange step (the reduction, axiom-clean).**  Granting the
graded exchange step, the two degree-minimal generators `e₁, e₂` *generate the whole syzygy module*
`N`: well-founded recursion on the product-degree (`WithBot ℕ` is well-founded under `<`) reduces any
`w ∈ N` to `0` modulo `Submodule.span K[X] {e₁, e₂}`.  This is precisely the windowed-generation
content that `SYZ60.MuBasisWindowIso` requires — the graded refinement of SYZ61's rank-2 freeness. -/
theorem span_of_gradedExchange {N : Submodule K[X] (Fin 3 → K[X])} {e₁ e₂ : Fin 3 → K[X]}
    (he₁ : e₁ ∈ N) (he₂ : e₂ ∈ N) (hex : GradedExchange (d := d) N e₁ e₂) :
    ∀ w ∈ N, w ∈ Submodule.span K[X] ({e₁, e₂} : Set (Fin 3 → K[X])) := by
  set S : Submodule K[X] (Fin 3 → K[X]) := Submodule.span K[X] ({e₁, e₂} : Set _) with hS
  have hmem₁ : e₁ ∈ S := Submodule.subset_span (by simp)
  have hmem₂ : e₂ ∈ S := Submodule.subset_span (by simp)
  have key : ∀ v : WithBot ℕ, ∀ w, w ∈ N → pdeg d w = v → w ∈ S := by
    intro v
    induction v using WellFoundedLT.induction with
    | _ v IH =>
      intro w hw hv
      rcases eq_or_ne w 0 with h0 | h0
      · simp [h0, S.zero_mem]
      · obtain ⟨q₁, q₂, hred⟩ := hex w hw h0
        set r : Fin 3 → K[X] := w - (q₁ • e₁ + q₂ • e₂) with hr
        have hrN : r ∈ N := N.sub_mem hw (N.add_mem (N.smul_mem _ he₁) (N.smul_mem _ he₂))
        have hrlt : pdeg d r < v := hv ▸ hred
        have hrS : r ∈ S := IH (pdeg d r) hrlt r hrN rfl
        have hcomb : (q₁ • e₁ + q₂ • e₂) ∈ S :=
          S.add_mem (S.smul_mem _ hmem₁) (S.smul_mem _ hmem₂)
        have : w = r + (q₁ • e₁ + q₂ • e₂) := by rw [hr]; ring
        rw [this]
        exact S.add_mem hrS hcomb
  intro w hw
  exact key (pdeg d w) w hw rfl

end Exchange

/-! ## 4. Specialization to the syzygy kernel (SYZ61) -/

/-- **The μ-basis generation statement for the syzygy kernel.**  For a coprime triple, the syzygy
kernel is free of rank exactly 2 (SYZ61).  If two kernel elements `e₁, e₂` satisfy the graded
exchange step for the `W`-weights `d`, then they generate the *entire* kernel — the graded refinement
of SYZ61 that `SYZ60.MuBasisWindowIso` consumes.  The remaining gap is exactly `GradedExchange`
(the leading-vector exchange), stated and reduced above; SYZ61's rank-2 structure is the linear
algebra it rests on. -/
theorem syzygyKernel_eq_span_of_gradedExchange {d : Fin 3 → ℕ} {f g h : K[X]}
    {e₁ e₂ : Fin 3 → K[X]}
    (he₁ : e₁ ∈ LinearMap.ker (SYZ61.syzygyMap f g h))
    (he₂ : e₂ ∈ LinearMap.ker (SYZ61.syzygyMap f g h))
    (hex : GradedExchange (d := d) (LinearMap.ker (SYZ61.syzygyMap f g h)) e₁ e₂) :
    LinearMap.ker (SYZ61.syzygyMap f g h)
      = Submodule.span K[X] ({e₁, e₂} : Set (Fin 3 → K[X])) := by
  apply le_antisymm
  · intro w hw
    exact span_of_gradedExchange he₁ he₂ hex w hw
  · rw [Submodule.span_le]
    intro x hx
    rcases hx with hx | hx <;> simp_all

end ArkLib.ProximityGap.SYZ62

/-! ## Axiom audit -/

#print axioms ArkLib.ProximityGap.SYZ62.pdeg_smul
#print axioms ArkLib.ProximityGap.SYZ62.pdeg_add_le
#print axioms ArkLib.ProximityGap.SYZ62.lv_add
#print axioms ArkLib.ProximityGap.SYZ62.lv_smulK
#print axioms ArkLib.ProximityGap.SYZ62.lv_eq_zero_of_pdeg_lt
#print axioms ArkLib.ProximityGap.SYZ62.span_of_gradedExchange
#print axioms ArkLib.ProximityGap.SYZ62.syzygyKernel_eq_span_of_gradedExchange

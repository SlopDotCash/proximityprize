/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StepanovCountingLemma
import ArkLib.Data.CodingTheory.ProximityGap.GVRepBoundFromEnergy

/-!
# The Stepanov auxiliary-polynomial framework (#389) — and an honest circularity finding

This file feeds the counting lemma `card_le_natDegree_of_vanishing` the representation
point set `{y ∈ G : c − y ∈ G}` and packages the result against the `GVRepBound`
interface.  In doing so it makes a **negative discovery, recorded honestly**:

> **`stepanovAux_iff`** — the natural "auxiliary-polynomial existence"
> `StepanovAux G c D m` (a nonzero degree-`<D` polynomial vanishing to order `m` at the
> rep points) is **equivalent** to the bound `m·r(c) < D` itself.

The reason is separability: the rep points are distinct simple roots, so vanishing to
order `m` there forces `∏(X−y)^m ∣ f`, hence `deg f ≥ m·r(c)`.  The forward direction
(`repCount_lt_of_stepanovAux`) and the converse (`stepanovAux_of_lt`) together give the
equivalence — so this `StepanovAux` is a **restatement, not a reduction**.

**What this teaches about the real open core.**  Genuine Stepanov/Heath-Brown–Konyagin
leverage does NOT come from vanishing at the (unknown, separable) rep points; it comes
from an auxiliary polynomial vanishing to order `m` on a *structurally fixed* set,
constructed from the relations `xⁿ=1` and `(c−x)ⁿ=1`, whose degree is bounded
*independently* of `r(c)` — with the crux being a Wronskian non-vanishing.  That object
is genuinely different from `StepanovAux` here, and remains the open kernel.

Recorded so the tree does not carry this as a false reduction; the counting lemma
(`StepanovCountingLemma`) remains the genuine reusable half.  Axiom-clean; no `sorry`.
-/

open Polynomial

namespace ArkLib.ProximityGap.Stepanov

open ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The Stepanov auxiliary-polynomial existence** (the open kernel of the rep bound):
a nonzero polynomial of degree `< D`, divisible by `(X − y)^m` at every representation
point `y ∈ {y ∈ G : c − y ∈ G}` of `c`. -/
def StepanovAux (G : Finset F) (c : F) (D m : ℕ) : Prop :=
  ∃ f : F[X], f ≠ 0 ∧ f.natDegree < D ∧
    ∀ y ∈ G.filter (fun y => c - y ∈ G), (X - C y) ^ m ∣ f

/-- **The auxiliary polynomial bounds the representation count.**  By the counting
lemma, `m · r(c) ≤ deg(f) < D`. -/
theorem repCount_lt_of_stepanovAux {G : Finset F} {c : F} {D m : ℕ}
    (h : StepanovAux G c D m) : m * repCount G c < D := by
  obtain ⟨f, hf, hdeg, hdvd⟩ := h
  have hcount : m * (G.filter (fun y => c - y ∈ G)).card ≤ f.natDegree :=
    card_le_natDegree_of_vanishing hf hdvd
  rw [repCount]
  omega

/-- **⚠ CIRCULARITY: the converse.**  Because the representation points are *separable*
(distinct simple roots), `∏ (X − y)^m` already vanishes to order `m` at all of them, so
`m · r(c) < D ⟹ StepanovAux G c D m`.  Combined with `repCount_lt_of_stepanovAux` this
gives the **equivalence `StepanovAux G c D m ↔ m·r(c) < D`** — i.e. `StepanovAux` as
stated is a *restatement* of the bound, not a genuine reduction of it.  The real
Stepanov leverage requires an auxiliary polynomial vanishing on a *structurally fixed*
set (built from the relations `xⁿ=1`, `(c−x)ⁿ=1`) whose degree is bounded *independently*
of `r(c)` — not the separable-vanishing condition here, which is degree-`≥ m·r(c)` by
force.  Recorded honestly: this framework does not advance past the rep bound. -/
theorem stepanovAux_of_lt {G : Finset F} {c : F} {D m : ℕ}
    (h : m * repCount G c < D) : StepanovAux G c D m := by
  classical
  refine ⟨∏ y ∈ G.filter (fun y => c - y ∈ G), (X - C y) ^ m, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun y _ => pow_ne_zero _ (X_sub_C_ne_zero y)
  · rw [Polynomial.natDegree_prod _ _ (fun y _ => pow_ne_zero _ (X_sub_C_ne_zero y))]
    have hsum : ∑ y ∈ G.filter (fun y => c - y ∈ G), ((X - C y) ^ m).natDegree
        = (G.filter (fun y => c - y ∈ G)).card * m := by
      rw [Finset.sum_congr rfl
        (fun y _ => by rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]),
        Finset.sum_const, smul_eq_mul]
    rw [hsum, Nat.mul_comm]
    exact h
  · intro y hy; exact Finset.dvd_prod_of_mem _ hy

/-- **The equivalence**: `StepanovAux` as stated is exactly the rep bound (circular). -/
theorem stepanovAux_iff {G : Finset F} {c : F} {D m : ℕ} :
    StepanovAux G c D m ↔ m * repCount G c < D :=
  ⟨repCount_lt_of_stepanovAux, stepanovAux_of_lt⟩

/-- **The whole Garcia–Voloch rep bound from the auxiliary-polynomial existence.**  If
`StepanovAux G c D m` holds for every `c ≠ 0`, with `D ≤ (M+1)·m` and `M³ ≤ 64|G|²`,
then `GVRepBound G M`.  ⚠ By `stepanovAux_iff` the hypothesis is *equivalent* to the
rep bound itself, so this is a packaging lemma, not a reduction — the genuine open
input remains an unconditional rep/energy bound (Stepanov/HBK), unchanged. -/
theorem gvRepBound_of_stepanovAux {G : Finset F} {D m M : ℕ} (hm : 1 ≤ m)
    (hMD : D ≤ (M + 1) * m) (hMcube : M ^ 3 ≤ 64 * G.card ^ 2)
    (h : ∀ c : F, c ≠ 0 → StepanovAux G c D m) :
    GVRepBound G M := by
  refine ⟨fun t ht => ?_, hMcube⟩
  have hlt : m * repCount G t < D := repCount_lt_of_stepanovAux (h t ht)
  have h2 : m * repCount G t < (M + 1) * m := lt_of_lt_of_le hlt hMD
  rw [mul_comm (M + 1) m] at h2
  have h3 : repCount G t < M + 1 := Nat.lt_of_mul_lt_mul_left h2
  omega

end ArkLib.ProximityGap.Stepanov

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.Stepanov.repCount_lt_of_stepanovAux
#print axioms ArkLib.ProximityGap.Stepanov.stepanovAux_of_lt
#print axioms ArkLib.ProximityGap.Stepanov.stepanovAux_iff
#print axioms ArkLib.ProximityGap.Stepanov.gvRepBound_of_stepanovAux

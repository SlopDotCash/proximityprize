/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Multiplicity
import ArkLib.Data.CodingTheory.SubspaceDesign
import ArkLib.Data.CodingTheory.ProximityGap.GK16RootCounting
import Mathlib.Algebra.Polynomial.FieldDivision

set_option linter.unusedSectionVars false

/-!
# The UM (univariate-multiplicity) subspace-design half (ABF26 T2.18 / DA.7)

Scratch file for issue #92. The folded RS (GK16) half of ABF26 Theorem 2.18 is
proven in `SubspaceDesign.lean` via the folded-Wronskian degree budget. This file
formalizes the **univariate multiplicity (UM)** half: the analogue for
`ReedSolomon.Multiplicity.umCode`, whose per-symbol packing is the first `s`
formal (`D_ux`) derivatives of a degree-`< k` polynomial at each domain point.

The mathematical key is that the UM per-coordinate vanishing subspace
`A_i = A ⊓ ker(eval_i)` consists of polynomials all of whose first `s` derivatives
vanish at `domain i`, which — over a field where `s! ≠ 0` (the ABF26 A.7
characteristic condition) — is equivalent to a **root of multiplicity `≥ s`** at
`domain i`. This is the genuine `D_ux`/multiplicity content (Mathlib's
`lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors`) that
replaces the folded-Wronskian machinery of the GK16 half.

## Bricks

* `Multiplicity.mem_ker_umProj_iff` — membership in `ker(proj i ∘ umEvalOnPoints)`:
  a polynomial lies in the kernel iff its first `s` formal derivatives all vanish
  at `domain i`.
* `Multiplicity.iterate_derivative_eval_eq_zero_iff_le_rootMultiplicity` — the
  `D_ux` ↔ root-multiplicity bridge (field + `s!` invertible).
* `Multiplicity.mem_ker_umProj_iff_le_rootMultiplicity` — the combined symbol-level
  characterization of `ker(eval_i)` in terms of `rootMultiplicity`.
-/

namespace ReedSolomon.Multiplicity

open Polynomial

variable {ι : Type*} [Fintype ι]
variable {F : Type*} [CommRing F]

/-- **Symbol-level kernel of the UM evaluation map.** A polynomial `p` evaluates to
the zero symbol at coordinate `i` under `umEvalOnPoints domain s` — i.e. lies in
`ker (proj i ∘ umEvalOnPoints domain s)` — iff each of its first `s` formal
derivatives `D_ux^j p` vanishes at `domain i`. This is the `D_ux` operation made
explicit: the `s` components of the UM symbol are exactly the `s` derivative
evaluations. -/
lemma umEvalOnPoints_apply (domain : ι ↪ F) (s : ℕ) (p : Polynomial F) (x : ι)
    (j : Fin s) :
    umEvalOnPoints domain s p x j = (derivative^[j.val] p).eval (domain x) := rfl

/-- A polynomial `p` lies in `ker (proj i ∘ umEvalOnPoints domain s)` iff all of its
first `s` formal derivatives vanish at `domain i`. -/
lemma mem_ker_umProj_iff (domain : ι ↪ F) (s : ℕ) (i : ι) (p : Polynomial F) :
    umEvalOnPoints domain s p ∈
        LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) ↔
      ∀ j : Fin s, (derivative^[j.val] p).eval (domain i) = 0 := by
  rw [LinearMap.mem_ker, LinearMap.proj_apply]
  constructor
  · intro h j
    have := congrFun h j
    simpa [umEvalOnPoints_apply] using this
  · intro h
    funext j
    simpa [umEvalOnPoints_apply] using h j

end ReedSolomon.Multiplicity

namespace ReedSolomon.Multiplicity

open Polynomial

variable {ι : Type*} [Fintype ι]
variable {F : Type*} [Field F]

/-- **The `D_ux` ↔ root-multiplicity bridge (ABF26 A.7 characteristic condition).**
Over a field, for a nonzero polynomial `p` and `s ≥ 1`, all of its first `s` formal
derivatives vanish at `t` iff `t` is a root of `p` of multiplicity at least `s`,
*provided* `(s-1)! ≠ 0` (the genuine characteristic side condition of ABF26
Definition A.7: `char F ≥ k ≥ s` keeps the factorial invertible). -/
lemma iterate_derivative_eval_eq_zero_iff_le_rootMultiplicity
    {p : Polynomial F} {t : F} {s : ℕ} (hp : p ≠ 0) (hs : 1 ≤ s)
    (hchar : ((s - 1).factorial : F) ∈ nonZeroDivisors F) :
    (∀ j : Fin s, (derivative^[j.val] p).eval t = 0) ↔
      s ≤ p.rootMultiplicity t := by
  rw [show s ≤ p.rootMultiplicity t ↔ s - 1 < p.rootMultiplicity t by omega]
  rw [lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors hp hchar]
  constructor
  · intro h m hm
    have hms : m < s := by omega
    exact h ⟨m, hms⟩
  · intro h j
    exact h j.val (by omega)

/-- **Symbol-level kernel ↔ multiplicity.** Combining `mem_ker_umProj_iff` with the
`D_ux`/root-multiplicity bridge: for a nonzero polynomial `p` (`s ≥ 1`, `(s-1)!`
invertible), `umEvalOnPoints domain s p` vanishes at coordinate `i` iff `domain i`
is a root of `p` of multiplicity at least `s`. -/
lemma mem_ker_umProj_iff_le_rootMultiplicity (domain : ι ↪ F) (s : ℕ) (i : ι)
    {p : Polynomial F} (hp : p ≠ 0) (hs : 1 ≤ s)
    (hchar : ((s - 1).factorial : F) ∈ nonZeroDivisors F) :
    umEvalOnPoints domain s p ∈
        LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) ↔
      s ≤ p.rootMultiplicity (domain i) := by
  rw [mem_ker_umProj_iff]
  exact iterate_derivative_eval_eq_zero_iff_le_rootMultiplicity hp hs hchar

/-- **UM multiplicity spine (the `D_ux` analogue of the GK16 §4 degree budget).**
For a nonzero polynomial `p` of degree `< k` over a field, the number of domain
points at which `p` has a root of multiplicity `≥ s`, times `s`, is at most `k - 1`.

This is the genuine UM degree budget: each such point contributes a factor
`(X - domain i)^s`, and the distinct points give disjoint factors whose total degree
`s · #{such points}` is bounded by `natDegree p ≤ k - 1`. It is the multiplicity-code
counterpart of `ArkLib.FRS.GK16.sum_rootMultiplicity_foldedWronskian_le`, but proved
directly from `Polynomial.sum_rootMultiplicity_le` rather than the folded Wronskian. -/
lemma um_card_mult_ge_mul_le {domain : ι ↪ F} {k s : ℕ} {p : Polynomial F}
    (hp : p ≠ 0) (hdeg : p.natDegree ≤ k - 1)
    (S : Finset ι) (hS : ∀ i ∈ S, s ≤ p.rootMultiplicity (domain i)) :
    s * S.card ≤ k - 1 := by
  classical
  -- Each domain point in `S` contributes ≥ s to the (distinct-point) multiplicity sum.
  have hmul : s * S.card ≤ ∑ i ∈ S, p.rootMultiplicity (domain i) := by
    calc s * S.card = ∑ _i ∈ S, s := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ i ∈ S, p.rootMultiplicity (domain i) := Finset.sum_le_sum hS
  -- The distinct-point multiplicity sum is bounded by the degree.
  have hdistinct : ∑ i ∈ S, p.rootMultiplicity (domain i)
      = ∑ a ∈ S.image domain, Polynomial.rootMultiplicity a p := by
    rw [Finset.sum_image (fun i _ j _ h => domain.injective h)]
  have hbound : ∑ a ∈ S.image domain, Polynomial.rootMultiplicity a p ≤ p.natDegree :=
    Polynomial.sum_rootMultiplicity_le_natDegree p hp (S.image domain)
  calc s * S.card ≤ ∑ i ∈ S, p.rootMultiplicity (domain i) := hmul
    _ = ∑ a ∈ S.image domain, Polynomial.rootMultiplicity a p := hdistinct
    _ ≤ p.natDegree := hbound
    _ ≤ k - 1 := hdeg

end ReedSolomon.Multiplicity

/-! ## The UM degree-budget residual and rate-arithmetic theorem

Mirroring the GK16 side (`CodingTheory.GK16DegreeBudget` /
`CodingTheory.frs_is_subspaceDesign_gk16`), we package the UM degree budget
`∑_i dim A_i ≤ (dim A)·(k-1)` as a named residual, and prove the rate-arithmetic
reduction to `IsSubspaceDesign` for `τ(r) = (k-1)/n` on `[s]` — fully and
unconditionally, exactly as in the FRS half (the budget is the only residual). -/

namespace CodingTheory

open scoped NNReal
open ReedSolomon.Multiplicity

variable {ι : Type} [Fintype ι]
variable {F : Type} [Field F]

/-- **The UM degree-budget residual.** For a subspace `A` of the univariate
multiplicity code, the per-coordinate vanishing dimensions
`dim A_i := dim (A ⊓ ker(eval_i))` sum to at most `(dim A)·(k-1)`. This is the UM
counterpart of `CodingTheory.GK16DegreeBudget`; its discharge follows the
multiplicity spine `ReedSolomon.Multiplicity.um_card_mult_ge_mul_le` under the
encoder-isomorphism transport. -/
def UMDegreeBudget (k s : ℕ) (C : Submodule F (ι → Fin s → F)) : Prop :=
  ∀ A : Submodule F (ι → Fin s → F), A ≤ C →
    (∑ i : ι, Module.finrank F (↥(A ⊓
        (LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
        Submodule F (ι → Fin s → F)))) ≤ Module.finrank F A * (k - 1)

/-- **ABF26 Theorem 2.18 [GW13/KSY14], UM half** (reduced to the UM degree-budget
residual `UMDegreeBudget`). Univariate multiplicity codes are τ-subspace-design for

  `τ(r) := (k-1)/n`   for `r ∈ [s] = {1, …, s}`,   and   `τ(r) := 1`   otherwise,

*given* the residual `UMDegreeBudget k s (umCode …)`. The rate-arithmetic reduction
is **fully proven, axiom-clean**, identical in shape to the FRS half
`CodingTheory.frs_is_subspaceDesign_gk16`: the `r ∈ [s]` branch divides the degree
budget by `n`; the `r ∉ [s]` branch (`τ = 1`) holds unconditionally from `A_i ≤ A`.

The repaired profile `τ(r) = (k-1)/n` on `[s]` matches the `s`-factor-corrected rate
of the GK16 half and already implies the L2.17 lower bound
`τ(r) ≥ k/(s·n) - 1/n` (`CodingTheory.subspaceDesign_tau_lower`). -/
theorem um_is_subspaceDesign_of_budget
    [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ)
    (h_residual : UMDegreeBudget k s (ReedSolomon.Multiplicity.umCode domain k s)) :
    let τ : ℕ → ℝ := fun r ↦
      if r ∈ Finset.Icc 1 s then (k - 1 : ℝ) / Fintype.card ι else 1
    IsSubspaceDesign s τ (ReedSolomon.Multiplicity.umCode domain k s) := by
  intro τ r A hA_le _hA_rank
  have hn_pos : 0 < Fintype.card ι := Fintype.card_pos
  have hn_posR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn_pos
  haveI : FiniteDimensional F (ι → Fin s → F) := inferInstance
  set Ai : ι → Submodule F (ι → Fin s → F) := fun i =>
    A ⊓ (LinearMap.ker
      (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) with hAi
  have hAi_rank_le : ∀ i, Module.finrank F (Ai i) ≤ Module.finrank F A := fun i =>
    Submodule.finrank_mono inf_le_left
  by_cases hr : r ∈ Finset.Icc 1 s
  · -- Range `r ∈ [s]`: divide the UM budget `∑_i dim A_i ≤ (dim A)·(k-1)` by `n`.
    simp only [τ, if_pos hr]
    have hbudget : (∑ i : ι, Module.finrank F (Ai i)) ≤ Module.finrank F A * (k - 1) :=
      h_residual A hA_le
    have hbudgetR :
        (∑ i : ι, (Module.finrank F (Ai i) : ℝ)) ≤
          (Module.finrank F A : ℝ) * ((k : ℝ) - 1) := by
      by_cases hk0 : k = 0
      · -- `k = 0`: the code is `⊥`, so `A = ⊥` and every `dim A_i = 0`.
        subst hk0
        have hC0 : ReedSolomon.Multiplicity.umCode domain 0 s = ⊥ := by
          have hdLT : Polynomial.degreeLT F 0 = ⊥ := by
            rw [eq_bot_iff]
            intro p hp
            rw [Polynomial.mem_degreeLT] at hp
            rw [Submodule.mem_bot, ← Polynomial.degree_eq_bot]
            exact Nat.WithBot.lt_zero_iff.mp (by simpa using hp)
          unfold ReedSolomon.Multiplicity.umCode
          rw [hdLT, Submodule.map_bot]
        have hAbot : A = ⊥ := le_bot_iff.mp (hA_le.trans hC0.le)
        have hzero : ∀ i, Module.finrank F (Ai i) = 0 := by
          intro i
          have : Ai i = ⊥ := by rw [hAi, hAbot]; simp
          rw [this]; simp
        have hAr : Module.finrank F A = 0 := by rw [hAbot]; simp
        simp [hzero, hAr]
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        calc (∑ i : ι, (Module.finrank F (Ai i) : ℝ))
            = ((∑ i : ι, Module.finrank F (Ai i) : ℕ) : ℝ) := by push_cast; rfl
          _ ≤ ((Module.finrank F A * (k - 1) : ℕ) : ℝ) := by exact_mod_cast hbudget
          _ = (Module.finrank F A : ℝ) * ((k : ℝ) - 1) := by
                push_cast [Nat.cast_sub hk1]; ring
    rw [div_le_iff₀ hn_posR]
    calc (∑ i : ι, (Module.finrank F (Ai i) : ℝ))
        ≤ (Module.finrank F A : ℝ) * ((k : ℝ) - 1) := hbudgetR
      _ = (Module.finrank F A : ℝ) * ((k - 1 : ℝ) / Fintype.card ι) * Fintype.card ι := by
            field_simp
  · -- Range `r ∉ [s]`: `τ(r) = 1`, proven unconditionally from `A_i ≤ A`.
    simp only [τ, if_neg hr, mul_one]
    rw [div_le_iff₀ hn_posR]
    calc (∑ i : ι, (Module.finrank F (Ai i) : ℝ))
        ≤ (∑ _i : ι, (Module.finrank F A : ℝ)) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          exact_mod_cast hAi_rank_le i
      _ = (Module.finrank F A : ℝ) * Fintype.card ι := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-! ### Rank-1 discharge of the UM degree budget

The general `UMDegreeBudget` discharge (arbitrary `dim A`) needs the encoder-isomorphism
transport plus a Wronskian-of-derivatives argument, mirroring the GK16 structural residual
`GK16Claim16StructuralData`. The **rank-1 case** — a single nonzero UM codeword — is
discharged here *unconditionally* (given the A.7 characteristic condition `s! ≠ 0`), and
is exactly the instance consumed by ABF26 Lemma 2.17 (`subspaceDesign_tau_lower`). -/

variable [DecidableEq ι]

/-- The 1-dimensional subspace `span{a}` meets `ker(proj i)` in itself when `a i = 0`. -/
private lemma um_span_inf_ker_proj_of_eq_zero {s : ℕ} {a : ι → Fin s → F} {i : ι}
    (hai : a i = 0) :
    (Submodule.span F {a}) ⊓
        LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) =
      Submodule.span F {a} :=
  inf_eq_left.mpr <| Submodule.span_le.mpr <| Set.singleton_subset_iff.mpr <| by
    simp [LinearMap.mem_ker, LinearMap.proj_apply, hai]

/-- The 1-dimensional subspace `span{a}` meets `ker(proj i)` trivially when `a i ≠ 0`. -/
private lemma um_span_inf_ker_proj_of_ne_zero {s : ℕ} {a : ι → Fin s → F} {i : ι}
    (hai : a i ≠ 0) :
    (Submodule.span F {a}) ⊓
        LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx_span, hx_ker⟩ := Submodule.mem_inf.mp hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx_span
  have h0 : c • a i = 0 := by
    simpa [LinearMap.mem_ker, LinearMap.proj_apply] using hx_ker
  rcases smul_eq_zero.mp h0 with hc | h
  · simp [hc]
  · exact absurd h hai

/-- **UM degree budget, rank-1 case (unconditional, given `s! ≠ 0`).** For a single
nonzero degree-`< k` polynomial `p`, the UM codeword `c := umEvalOnPoints domain s p`
satisfies the design budget at `A := span{c}`:

  `∑_i dim (span{c} ⊓ ker(eval_i)) ≤ k - 1 = dim(span{c}) · (k-1)`.

Each `dim A_i ∈ {0,1}`, equal to `1` exactly when the symbol `c i = 0`, i.e. (by the
`D_ux`/multiplicity bridge) when `domain i` is a root of `p` of multiplicity `≥ s`; the
spine `um_card_mult_ge_mul_le` bounds the count of such points by `(k-1)/s ≤ k-1`. -/
theorem um_degreeBudget_rank_one
    {domain : ι ↪ F} {k s : ℕ} {p : Polynomial F}
    (hp0 : p ≠ 0) (hpdeg : p ∈ Polynomial.degreeLT F k) (hs : 1 ≤ s)
    (hchar : ((s - 1).factorial : F) ∈ nonZeroDivisors F) :
    (∑ i : ι, Module.finrank F (↥((Submodule.span F {umEvalOnPoints domain s p}) ⊓
        (LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
        Submodule F (ι → Fin s → F))))
      ≤ k - 1 := by
  classical
  set c := umEvalOnPoints domain s p with hc
  have hpdeg' : p.natDegree ≤ k - 1 := by
    have hlt : p.degree < (k : ℕ) := Polynomial.mem_degreeLT.mp hpdeg
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0; rw [Nat.cast_zero] at hlt
        exact absurd (Polynomial.degree_eq_bot.mp (by
          simpa using hlt)) hp0
      · exact hk0
    have : p.natDegree < k := by
      rwa [Polynomial.degree_eq_natDegree hp0, Nat.cast_lt] at hlt
    omega
  by_cases hc0 : c = 0
  · -- `c = 0`: `span{c} = ⊥`, every `A_i = ⊥`, the sum is `0 ≤ k-1`.
    have hzero : (∑ i : ι, Module.finrank F (↥((Submodule.span F {c}) ⊓
        (LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
        Submodule F (ι → Fin s → F)))) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hbot : (Submodule.span F {c}) ⊓
          (LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) = ⊥ := by
        rw [hc0]; simp
      rw [hbot]; exact finrank_bot _ _
    rw [hzero]; exact Nat.zero_le _
  · -- `c ≠ 0`: per-coordinate rank `dim A_i = if c i = 0 then 1 else 0`.
    have hterm : ∀ i : ι,
        (Module.finrank F (↥((Submodule.span F {c}) ⊓
            (LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
            Submodule F (ι → Fin s → F))))
          = if c i = 0 then 1 else 0 := by
      intro i
      by_cases hci : c i = 0
      · rw [um_span_inf_ker_proj_of_eq_zero hci, if_pos hci, finrank_span_singleton hc0]
      · rw [um_span_inf_ker_proj_of_ne_zero hci, if_neg hci]; simp
    -- The sum equals the number of zero-symbol coordinates.
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_boole]
    -- A zero symbol `c i = 0` is a root of multiplicity `≥ s` of `p`.
    have hroot : ∀ i ∈ (Finset.univ.filter fun i => c i = 0),
        s ≤ p.rootMultiplicity (domain i) := by
      intro i hi
      have hci : c i = 0 := (Finset.mem_filter.mp hi).2
      have hmem : umEvalOnPoints domain s p ∈
          LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) := by
        rw [LinearMap.mem_ker, LinearMap.proj_apply]; exact hci
      exact (mem_ker_umProj_iff_le_rootMultiplicity domain s i hp0 hs hchar).mp hmem
    -- Apply the multiplicity spine: `s · #{zero coords} ≤ k-1`, hence `#{…} ≤ k-1`.
    have hcard := um_card_mult_ge_mul_le (domain := domain) (k := k) (s := s)
      hp0 hpdeg' (Finset.univ.filter fun i => c i = 0) hroot
    calc (Finset.univ.filter fun i => c i = 0).card
        ≤ s * (Finset.univ.filter fun i => c i = 0).card :=
          Nat.le_mul_of_pos_left _ hs
      _ ≤ k - 1 := hcard

end CodingTheory

namespace ReedSolomon.Multiplicity
#print axioms mem_ker_umProj_iff
#print axioms iterate_derivative_eval_eq_zero_iff_le_rootMultiplicity
#print axioms mem_ker_umProj_iff_le_rootMultiplicity
#print axioms um_card_mult_ge_mul_le
#print axioms CodingTheory.um_is_subspaceDesign_of_budget
#print axioms CodingTheory.um_degreeBudget_rank_one
end ReedSolomon.Multiplicity

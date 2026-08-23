/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.ResultantDegreeBound
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Bounded-degree polynomial kernel vectors via signed maximal minors (Cramer route)

If `M : Matrix κ ν F[X]` has all entries of `natDegree ≤ d` and a nonzero kernel vector over the
fraction field `Frac(F[X])` (e.g. `RatFunc F`), then `M` has a nonzero kernel vector over `F[X]`
itself whose entries have `natDegree ≤ card κ · d`.

The construction is the classical Cramer/maximal-minor argument, done directly over the base
ring (no rank theory needed):

* pick a *maximal* nonvanishing minor of `M`, say of size `r`, on rows `ri` and columns `ci`
  (`Nat.findGreatest`; the `0 × 0` minor is `1`, so a maximum exists);
* `r < card ν`, since an invertible window covering **all** columns would force the kernel to
  vanish (`adjugate · M = det • 1` over a domain);
* adjoin one extra column `j₀ ∉ range ci` and take the vector of **signed maximal minors** of
  the resulting `r × (r+1)` window (`Matrix.signedMinorVec`); its coordinate at `j₀` is the
  chosen nonvanishing `r × r` minor, and `(M *ᵥ y) i` is the `(r+1) × (r+1)` minor on rows
  `Fin.cons i ri` (Laplace expansion `Matrix.det_succ_row_zero`), which vanishes: by maximality
  of `r` when row `i` is new, and by row repetition otherwise.

Main results:

* `Matrix.signedMinorVec`, `Matrix.mulVec_signedMinorVec` — the Cramer kernel vector and the
  Laplace identity `(M *ᵥ signedMinorVec M ri cs) i = det (M.submatrix (Fin.cons i ri) cs)`;
* `Matrix.exists_signed_minor_kernel_vector` — over an integral domain, a nonzero kernel vector
  can be replaced by one whose entries are `0` or `±`(minors of `M` of size `≤ card κ`);
* `Matrix.exists_natDegree_le_kernel_vector` — the degree-bounded kernel vector over `F[X]`,
  via `Polynomial.natDegree_det_le`;
* `Matrix.exists_kernel_vector_of_fractionRing_kernel` — denominator clearing: a nonzero kernel
  vector over `Frac(R)` yields one over `R` (`IsLocalization.exist_integer_multiples`);
* `Matrix.exists_natDegree_le_kernel_vector_of_fractionRing` /
  `Matrix.exists_natDegree_le_kernel_vector_of_ratFunc` — the combination: nonzero kernel over
  `Frac(F[X])` (resp. `RatFunc F`) gives a polynomial kernel vector of `natDegree ≤ card κ · d`.

This is the degree-budget seam of **unit (2)** of the Hab25 Johnson MCA ledger (issue #302):
it bounds the `Z`-degree of the Guruswami–Sudan interpolant over `K = F(Z)` obtained from the
linear system `gs_existence`, complementing the `X`/`Y`-degree bounds already in
`ArkLib/Data/CodingTheory/GuruswamiSudan/` and the discriminant bound in
`ArkLib/ToMathlib/ResultantDegreeBound.lean`.

All statements are Mathlib-only.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audit anchors at end of file).
-/

open Polynomial

namespace Matrix

variable {R : Type*} [CommRing R] {κ ν : Type*}

/-- The **Cramer kernel vector** attached to a row window `ri : Fin r → κ` and a column window
`cs : Fin (r+1) → ν`: the vector supported on the columns `cs k`, whose value there is the
signed maximal minor `(-1)^k · det (M.submatrix ri (cs ∘ k.succAbove))` (delete column `k`). -/
def signedMinorVec [DecidableEq ν] (M : Matrix κ ν R) {r : ℕ}
    (ri : Fin r → κ) (cs : Fin (r + 1) → ν) : ν → R := fun j =>
  ∑ k : Fin (r + 1),
    if j = cs k then (-1) ^ (k : ℕ) * (M.submatrix ri (cs ∘ k.succAbove)).det else 0

theorem signedMinorVec_apply [DecidableEq ν] (M : Matrix κ ν R) {r : ℕ}
    (ri : Fin r → κ) {cs : Fin (r + 1) → ν} (hcs : Function.Injective cs) (k : Fin (r + 1)) :
    signedMinorVec M ri cs (cs k) =
      (-1) ^ (k : ℕ) * (M.submatrix ri (cs ∘ k.succAbove)).det := by
  unfold signedMinorVec
  rw [Finset.sum_eq_single k (fun b _ hbk => if_neg fun h => hbk (hcs h.symm))
    (fun h => absurd (Finset.mem_univ k) h), if_pos rfl]

theorem signedMinorVec_apply_of_notMem [DecidableEq ν] (M : Matrix κ ν R) {r : ℕ}
    (ri : Fin r → κ) (cs : Fin (r + 1) → ν) {j : ν} (hj : j ∉ Set.range cs) :
    signedMinorVec M ri cs j = 0 :=
  Finset.sum_eq_zero fun k _ => if_neg fun h => hj ⟨k, h.symm⟩

/-- **Laplace identity for the Cramer kernel vector**: the `i`-th coordinate of
`M *ᵥ signedMinorVec M ri cs` is the `(r+1) × (r+1)` minor of `M` on rows `Fin.cons i ri` and
columns `cs` (expansion along the row `i`). -/
theorem mulVec_signedMinorVec [Fintype ν] [DecidableEq ν] (M : Matrix κ ν R) {r : ℕ}
    (ri : Fin r → κ) (cs : Fin (r + 1) → ν) (i : κ) :
    M.mulVec (signedMinorVec M ri cs) i = (M.submatrix (Fin.cons i ri) cs).det := by
  rw [Matrix.det_succ_row_zero]
  have hrow : Fin.cons i ri ∘ Fin.succ = ri :=
    funext fun a => by simp only [Function.comp_apply, Fin.cons_succ]
  calc M.mulVec (signedMinorVec M ri cs) i
      = ∑ j, M i j * ∑ k : Fin (r + 1),
          if j = cs k then (-1) ^ (k : ℕ) * (M.submatrix ri (cs ∘ k.succAbove)).det else 0 := rfl
    _ = ∑ j, ∑ k : Fin (r + 1),
          if j = cs k then M i j * ((-1) ^ (k : ℕ) * (M.submatrix ri (cs ∘ k.succAbove)).det)
          else 0 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [mul_ite, mul_zero]
    _ = ∑ k : Fin (r + 1), ∑ j,
          if j = cs k then M i j * ((-1) ^ (k : ℕ) * (M.submatrix ri (cs ∘ k.succAbove)).det)
          else 0 := Finset.sum_comm
    _ = ∑ k : Fin (r + 1),
          M i (cs k) * ((-1) ^ (k : ℕ) * (M.submatrix ri (cs ∘ k.succAbove)).det) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        exact Fintype.sum_ite_eq' (cs k)
          (fun j => M i j * ((-1) ^ (k : ℕ) * (M.submatrix ri (cs ∘ k.succAbove)).det))
    _ = ∑ k : Fin (r + 1), (-1) ^ (k : ℕ) * (M.submatrix (Fin.cons i ri) cs) 0 k *
          ((M.submatrix (Fin.cons i ri) cs).submatrix Fin.succ k.succAbove).det := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.submatrix_submatrix, hrow]
        simp only [Matrix.submatrix_apply, Fin.cons_zero]
        ring

/-- Over an integral domain, a nonzero kernel vector can be replaced by one all of whose entries
are (up to sign) minors of `M` of size at most `card κ` — the vector of signed maximal minors of
a maximal-rank window. -/
theorem exists_signed_minor_kernel_vector {R : Type*} [CommRing R] [IsDomain R]
    {κ ν : Type*} [Fintype κ] [Fintype ν]
    (M : Matrix κ ν R) (x : ν → R) (hx : x ≠ 0) (hker : M.mulVec x = 0) :
    ∃ (s : ℕ) (y : ν → R), s ≤ Fintype.card κ ∧ y ≠ 0 ∧ M.mulVec y = 0 ∧
      ∀ j, y j = 0 ∨ ∃ (f : Fin s → κ) (g : Fin s → ν),
        y j = (M.submatrix f g).det ∨ y j = -(M.submatrix f g).det := by
  classical
  -- the maximal size of a nonvanishing minor of `M`
  let P : ℕ → Prop := fun t => ∃ f : Fin t → κ, ∃ g : Fin t → ν,
    Function.Injective f ∧ Function.Injective g ∧ (M.submatrix f g).det ≠ 0
  have hP0 : P 0 := ⟨Fin.elim0, Fin.elim0, Function.injective_of_subsingleton _,
    Function.injective_of_subsingleton _, by rw [Matrix.det_fin_zero]; exact one_ne_zero⟩
  set r := Nat.findGreatest P (Fintype.card ν) with hrdef
  obtain ⟨ri, ci, hri, hci, hdet⟩ : P r := Nat.findGreatest_spec (Nat.zero_le _) hP0
  -- `r < card ν`: otherwise the columns of `M` are linearly independent, killing `x`
  have hrlt : r < Fintype.card ν := by
    rcases Nat.lt_or_ge r (Fintype.card ν) with h | h
    · exact h
    exfalso
    have hreq : r = Fintype.card ν := le_antisymm (Nat.findGreatest_le _) h
    have hbij : Function.Bijective ci :=
      (Fintype.bijective_iff_injective_and_card ci).mpr ⟨hci, by simp [hreq]⟩
    have hBker : (M.submatrix ri ci).mulVec (x ∘ ci) = 0 := by
      funext a
      calc (M.submatrix ri ci).mulVec (x ∘ ci) a
          = ∑ b, M (ri a) (ci b) * x (ci b) := rfl
        _ = ∑ j, M (ri a) j * x j := hbij.sum_comp (fun j => M (ri a) j * x j)
        _ = M.mulVec x (ri a) := rfl
        _ = 0 := by rw [hker]; rfl
    have hsmul : (M.submatrix ri ci).det • (x ∘ ci) = 0 := by
      have h2 := congrArg ((M.submatrix ri ci).adjugate.mulVec) hBker
      rwa [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
        Matrix.mulVec_zero] at h2
    apply hx
    funext j
    obtain ⟨b, rfl⟩ := hbij.surjective j
    have h3 := congrFun hsmul b
    simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply, Pi.zero_apply] at h3
    exact (mul_eq_zero.mp h3).resolve_left hdet
  -- a column outside the window
  have hnsurj : ¬ Function.Surjective ci := fun hs =>
    absurd (Fintype.card_le_of_surjective ci hs) (by simpa using not_le.mpr hrlt)
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, ∀ b, ci b ≠ j₀ := by
    simp only [Function.Surjective, not_forall, not_exists] at hnsurj
    exact hnsurj
  have hj₀r : j₀ ∉ Set.range ci := fun h => by obtain ⟨b, hb⟩ := h; exact hj₀ b hb
  have hcons : Function.Injective (Fin.cons j₀ ci : Fin (r + 1) → ν) :=
    Fin.cons_injective_iff.mpr ⟨hj₀r, hci⟩
  refine ⟨r, signedMinorVec M ri (Fin.cons j₀ ci),
    by simpa using Fintype.card_le_of_injective ri hri, ?_, ?_, ?_⟩
  · -- nonzero: the value at `j₀` is the nonvanishing `r × r` minor
    have hyj : signedMinorVec M ri (Fin.cons j₀ ci) ((Fin.cons j₀ ci : Fin (r + 1) → ν) 0) =
        (M.submatrix ri ci).det := by
      rw [signedMinorVec_apply M ri hcons 0]
      have hcomp : (Fin.cons j₀ ci ∘ (0 : Fin (r + 1)).succAbove) = ci :=
        funext fun b => by simp [Fin.succAbove_zero]
      rw [hcomp]
      simp
    intro h0
    rw [h0] at hyj
    simp only [Pi.zero_apply] at hyj
    exact hdet hyj.symm
  · -- kernel: each coordinate of the image is an `(r+1) × (r+1)` minor, which vanishes
    funext i
    rw [Pi.zero_apply, mulVec_signedMinorVec M ri (Fin.cons j₀ ci) i]
    by_cases hmem : ∃ a, ri a = i
    · -- repeated row
      obtain ⟨a, ha⟩ := hmem
      refine Matrix.det_zero_of_row_eq (i := (0 : Fin (r + 1))) (j := a.succ)
        (Fin.succ_ne_zero a).symm ?_
      funext b
      simp [Matrix.submatrix_apply, ha]
    · -- genuine `(r+1)`-minor: vanishes by maximality of `r`
      by_contra hne
      have hP1 : P (r + 1) := ⟨Fin.cons i ri, Fin.cons j₀ ci,
        Fin.cons_injective_iff.mpr ⟨fun h => by obtain ⟨a, ha⟩ := h; exact hmem ⟨a, ha⟩, hri⟩,
        hcons, hne⟩
      exact Nat.findGreatest_is_greatest (hrdef ▸ Nat.lt_succ_self r) hrlt hP1
  · -- every entry is `0` or a signed `r × r` minor
    intro j
    by_cases hj : ∃ k, (Fin.cons j₀ ci : Fin (r + 1) → ν) k = j
    · obtain ⟨k, rfl⟩ := hj
      rw [signedMinorVec_apply M ri hcons k]
      rcases neg_one_pow_eq_or R (k : ℕ) with h | h
      · exact Or.inr ⟨ri, Fin.cons j₀ ci ∘ k.succAbove, Or.inl (by rw [h, one_mul])⟩
      · exact Or.inr ⟨ri, Fin.cons j₀ ci ∘ k.succAbove, Or.inr (by rw [h, neg_one_mul])⟩
    · exact Or.inl (signedMinorVec_apply_of_notMem M ri _ fun h => by
        obtain ⟨k, hk⟩ := h; exact hj ⟨k, hk⟩)

/-- **Bounded-degree kernel vectors for polynomial matrices.** If a matrix over `F[X]` with
entries of `natDegree ≤ d` has a nonzero kernel vector, it has one whose entries have
`natDegree ≤ card κ · d` (entries are signed minors of `M`). -/
theorem exists_natDegree_le_kernel_vector {F : Type*} [CommRing F] [IsDomain F]
    {κ ν : Type*} [Fintype κ] [Fintype ν]
    (M : Matrix κ ν F[X]) {d : ℕ} (hM : ∀ i j, (M i j).natDegree ≤ d)
    (x : ν → F[X]) (hx : x ≠ 0) (hker : M.mulVec x = 0) :
    ∃ y : ν → F[X], y ≠ 0 ∧ M.mulVec y = 0 ∧ ∀ j, (y j).natDegree ≤ Fintype.card κ * d := by
  obtain ⟨s, y, hs, hy0, hyker, hyform⟩ := exists_signed_minor_kernel_vector M x hx hker
  refine ⟨y, hy0, hyker, fun j => ?_⟩
  have hbound : ∀ (f : Fin s → κ) (g : Fin s → ν),
      ((M.submatrix f g).det).natDegree ≤ Fintype.card κ * d := by
    intro f g
    refine (Polynomial.natDegree_det_le (M.submatrix f g) fun a b => hM (f a) (g b)).trans ?_
    simpa using Nat.mul_le_mul_right d hs
  rcases hyform j with h | ⟨f, g, h | h⟩
  · simp [h]
  · rw [h]; exact hbound f g
  · rw [h, Polynomial.natDegree_neg]; exact hbound f g

/-- Clearing denominators: a nonzero kernel vector over the fraction field yields one over the
base ring. -/
theorem exists_kernel_vector_of_fractionRing_kernel {R : Type*} [CommRing R]
    {K : Type*} [CommRing K] [Algebra R K] [IsFractionRing R K]
    {κ ν : Type*} [Fintype κ] [Fintype ν]
    (M : Matrix κ ν R) (x : ν → K) (hx : x ≠ 0)
    (hker : (M.map (algebraMap R K)).mulVec x = 0) :
    ∃ p : ν → R, p ≠ 0 ∧ M.mulVec p = 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) Finset.univ x
  choose p hp using fun j => hb j (Finset.mem_univ j)
  refine ⟨p, ?_, ?_⟩
  · intro h0
    apply hx
    funext j
    show x j = 0
    have h1 := hp j
    rw [congrFun h0 j] at h1
    simp only [Pi.zero_apply, map_zero, Algebra.smul_def] at h1
    exact ((IsLocalization.map_units K b).mul_right_eq_zero.mp h1.symm)
  · funext i
    rw [Pi.zero_apply]
    have hcalc : algebraMap R K (M.mulVec p i) =
        algebraMap R K (b : R) * ((M.map (algebraMap R K)).mulVec x i) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hp j, Algebra.smul_def]
      ring
    rw [hker, Pi.zero_apply, mul_zero] at hcalc
    exact IsFractionRing.injective R K (hcalc.trans (map_zero _).symm)

/-- **The Cramer/bounded-degree-kernel lemma** (issue #302, unit (2)). A matrix over `F[X]` with
entries of `natDegree ≤ d` and a nonzero kernel vector over the fraction field of `F[X]` has a
nonzero *polynomial* kernel vector with entries of `natDegree ≤ card κ · d`. -/
theorem exists_natDegree_le_kernel_vector_of_fractionRing {F : Type*} [CommRing F] [IsDomain F]
    {K : Type*} [CommRing K] [Algebra F[X] K] [IsFractionRing F[X] K]
    {κ ν : Type*} [Fintype κ] [Fintype ν]
    (M : Matrix κ ν F[X]) {d : ℕ} (hM : ∀ i j, (M i j).natDegree ≤ d)
    (x : ν → K) (hx : x ≠ 0) (hker : (M.map (algebraMap F[X] K)).mulVec x = 0) :
    ∃ y : ν → F[X], y ≠ 0 ∧ M.mulVec y = 0 ∧ ∀ j, (y j).natDegree ≤ Fintype.card κ * d := by
  obtain ⟨p, hp0, hpker⟩ := exists_kernel_vector_of_fractionRing_kernel M x hx hker
  exact exists_natDegree_le_kernel_vector M hM p hp0 hpker

/-- `RatFunc` specialization of `exists_natDegree_le_kernel_vector_of_fractionRing`. -/
theorem exists_natDegree_le_kernel_vector_of_ratFunc {F : Type*} [Field F]
    {κ ν : Type*} [Fintype κ] [Fintype ν]
    (M : Matrix κ ν F[X]) {d : ℕ} (hM : ∀ i j, (M i j).natDegree ≤ d)
    (x : ν → RatFunc F) (hx : x ≠ 0)
    (hker : (M.map (algebraMap F[X] (RatFunc F))).mulVec x = 0) :
    ∃ y : ν → F[X], y ≠ 0 ∧ M.mulVec y = 0 ∧ ∀ j, (y j).natDegree ≤ Fintype.card κ * d :=
  exists_natDegree_le_kernel_vector_of_fractionRing M hM x hx hker

end Matrix

-- Axiom audit anchors: every result is axiom-clean `[propext, Classical.choice, Quot.sound]`.
#print axioms Matrix.signedMinorVec_apply
#print axioms Matrix.signedMinorVec_apply_of_notMem
#print axioms Matrix.mulVec_signedMinorVec
#print axioms Matrix.exists_signed_minor_kernel_vector
#print axioms Matrix.exists_natDegree_le_kernel_vector
#print axioms Matrix.exists_kernel_vector_of_fractionRing_kernel
#print axioms Matrix.exists_natDegree_le_kernel_vector_of_fractionRing
#print axioms Matrix.exists_natDegree_le_kernel_vector_of_ratFunc

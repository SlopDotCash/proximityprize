/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Jo26GeneratorMCA

/-!
# Curve decodability, the marked variant, and interleaving transfer ([GG25] / [Jo26] §5)

First formalization of **curve decodability** ([GG25] Definition 3.1, restated as [Jo26]
Definition 2.7) and of the [Jo26] §5 *marked* variant, together with the interleaving
transfer theorem ([Jo26] Theorem 5.7) — hypothesis K5 of issue #334.

An `F_q`-additive code `C ⊆ Σ^n` is `(ℓ, δ, a, b)`-**curve-decodable** if for every stack
`u = (u₀, …, u_ℓ)` of words and every codeword-valued function `f : F_q → C`, whenever the
degree-`ℓ` curve `α ↦ ∑ⱼ uⱼ αʲ` is `δ`-close (relative Hamming) to `f(α)` for at least `a`
points `α`, there is a single curve of codewords `c₀, …, c_ℓ ∈ C` with
`f(α) = ∑ⱼ cⱼ αʲ` on at least `b` of those close points.  The **marked** variant
([Jo26] Definition 5.1) instead quantifies over an arbitrary *marked set* `A₀ ⊆ F_q` of
size exactly `a` on which closeness holds pointwise, and demands `b` agreements inside
`A₀` — a stronger conclusion, since the adversary chooses which close points count.

## Main definitions

* `curveAt u α` — the curve point `∑ⱼ αʲ • uⱼ` ([GG25] Definition 3.1).
* `closeSet δ u f` — the set `A_δ(u, f) = {α : Δ(∑ⱼ uⱼ αʲ, f(α)) ≤ δ}`.
* `CurveDecodable F C ℓ δ a b` — [GG25] Definition 3.1 / [Jo26] Definition 2.7.
* `MarkedCurveDecodable F C ℓ δ a b` — [Jo26] Definition 5.1.
* `FarWordSupply C δ` — the far-word existence condition extracted from the counting
  argument of [Jo26] Lemma 5.4: every word has *some* codeword at relative distance `> δ`.
* `rowComb lam w` — the `λ`-combination `i ↦ ∑ₖ λₖ • w(i)ₖ` of the rows of an
  interleaved word.
* `combCurveSubmodule C f B` — the subspace `V_B ≤ F^s` of combination vectors whose
  row-combined `f` is *exactly* a codeword curve on `B` ([Jo26] proof of Theorem 5.7).

## Main results

* `curveDecodable_of_marked` — marked ⟹ original ([Jo26] Theorem 5.5, easy half;
  unconditional).
* `relHammingDist_rowComb_le` — row combination does not increase relative Hamming
  distance ([Jo26] Lemma 5.6; unconditional).
* `markedCurveDecodable_interleaved` — **[Jo26] Theorem 5.7**: if `C` is *marked*
  `(ℓ, δ, a, b)`-curve-decodable, `b ≤ a`, and `C(a, b) ≤ q`, then the `s`-fold
  interleaved code `C^⋈s` is marked `(ℓ, δ, a, b)`-curve-decodable (unconditional).
  The engine is the [Jo26] Lemma 3.2 covering lemma, reused from the wave-1 module
  `Jo26Gen.exists_nonzero_notMem_of_proper_family_of_card_le`: the `C(a, b) ≤ q`
  subspaces `V_B` (one per `b`-subset `B ⊆ A₀`) cover `F^s` by marked decodability of the
  base code, so one of them is everything; evaluating it on the standard basis assembles
  the interleaved codeword curve column by column.
* `curveDecodable_interleaved` — the plain curve-decodability of `C^⋈s` (corollary).
* `markedCurveDecodable_of_interpolation` — [Jo26] Lemma 5.2: for `b ≤ ℓ + 1` (and
  `b ≤ a`) every linear code is marked `(ℓ, δ, a, b)`-curve-decodable, by Lagrange
  interpolation of `b` points with codeword coefficients (unconditional).
* `farWordSupply_of_far_pair` — two codewords at relative distance `> 2δ` supply a far
  word for every center (a clean sufficient condition for `FarWordSupply`, by the
  triangle inequality).
* `markedCurveDecodable_of_curveDecodable` — original ⟹ marked, **conditional on
  `FarWordSupply C δ`** ([Jo26] Lemma 5.4 / Theorem 5.5, substantive half): redefining
  `f` outside `A₀` to be `δ`-far pins the close set to exactly `A₀`.  The far-word
  existence is the counting step of [Jo26] Lemma 5.4, isolated here as a named
  hypothesis rather than an axiom.
* `curveDecodable_iff_markedCurveDecodable` — [Jo26] Theorem 5.5 as an equivalence,
  conditional on `FarWordSupply C δ`.
* `markedCurveDecodable_interleaved_of_curveDecodable` — [Jo26] Theorem 5.7 from the
  *original* curve-decodability hypothesis, conditional on `FarWordSupply`.

## References

* [GG25] Z. Guo, V. Guruswami (attribution per [Jo26]), ePrint 2025/2054, Definition 3.1.
* [Jo26] S. Jo, *Interleaving Stability for Mutual Correlated Agreement and Curve
  Decodability*, ePrint 2026/891, §5. (Issue #334, hypothesis K5.)
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap.CurveDec

open Finset Code Polynomial
open scoped NNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {M : Type} [DecidableEq M] [AddCommMonoid M] [Module F M]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ### Curves, close sets, and the two decodability notions -/

/-- The point of the degree-`ℓ` curve through the stack `u = (u₀, …, u_ℓ)` at parameter
`α`: the word `i ↦ ∑ⱼ αʲ • uⱼ(i)` ([GG25] Definition 3.1). -/
def curveAt {ℓ : ℕ} (u : Fin (ℓ + 1) → ι → M) (α : F) : ι → M :=
  fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j i

/-- The close set `A_δ(u, f)`: parameters `α` at which the curve point is within relative
Hamming distance `δ` of `f α` ([GG25] Definition 3.1). -/
def closeSet {ℓ : ℕ} (δ : ℚ≥0) (u : Fin (ℓ + 1) → ι → M) (f : F → ι → M) : Finset F :=
  Finset.univ.filter fun α => δᵣ(curveAt u α, f α) ≤ δ

lemma mem_closeSet {ℓ : ℕ} {δ : ℚ≥0} {u : Fin (ℓ + 1) → ι → M} {f : F → ι → M} {α : F} :
    α ∈ closeSet δ u f ↔ δᵣ(curveAt u α, f α) ≤ δ := by
  simp [closeSet]

variable (F) in
/-- **[GG25] Definition 3.1 ([Jo26] Definition 2.7): curve decodability.**  `C` is
`(ℓ, δ, a, b)`-curve-decodable if for every stack `u` and codeword-valued `f`, whenever
the close set `A_δ(u, f)` has at least `a` elements, some codeword curve `c₀, …, c_ℓ ∈ C`
matches `f` on at least `b` elements of `A_δ(u, f)`. -/
def CurveDecodable (C : Set (ι → M)) (ℓ : ℕ) (δ : ℚ≥0) (a b : ℕ) : Prop :=
  ∀ (u : Fin (ℓ + 1) → ι → M) (f : F → ι → M), (∀ α, f α ∈ C) →
    a ≤ (closeSet δ u f).card →
    ∃ c : Fin (ℓ + 1) → ι → M, (∀ j, c j ∈ C) ∧
      b ≤ ((closeSet δ u f).filter fun α => f α = curveAt c α).card

variable (F) in
/-- **[Jo26] Definition 5.1: marked curve decodability.**  Same data, but quantified over
an arbitrary *marked set* `A₀` of size exactly `a` on which the curve is pointwise
`δ`-close to `f`; the codeword curve must match `f` on at least `b` elements of `A₀`
itself. -/
def MarkedCurveDecodable (C : Set (ι → M)) (ℓ : ℕ) (δ : ℚ≥0) (a b : ℕ) : Prop :=
  ∀ (u : Fin (ℓ + 1) → ι → M) (f : F → ι → M), (∀ α, f α ∈ C) →
    ∀ A₀ : Finset F, A₀.card = a → (∀ α ∈ A₀, δᵣ(curveAt u α, f α) ≤ δ) →
    ∃ c : Fin (ℓ + 1) → ι → M, (∀ j, c j ∈ C) ∧
      b ≤ (A₀.filter fun α => f α = curveAt c α).card

/-- **Marked ⟹ original ([Jo26] Theorem 5.5, easy half).**  Any `a`-subset of the close
set is a valid marked set, and agreements inside it are agreements inside the close
set. Unconditional. -/
theorem curveDecodable_of_marked {C : Set (ι → M)} {ℓ : ℕ} {δ : ℚ≥0} {a b : ℕ}
    (h : MarkedCurveDecodable F C ℓ δ a b) : CurveDecodable F C ℓ δ a b := by
  intro u f hf hcard
  obtain ⟨A₀, hA₀sub, hA₀card⟩ := Finset.exists_subset_card_eq hcard
  obtain ⟨c, hc, hb⟩ := h u f hf A₀ hA₀card fun α hα => mem_closeSet.mp (hA₀sub hα)
  exact ⟨c, hc, hb.trans (Finset.card_le_card (Finset.filter_subset_filter _ hA₀sub))⟩

/-! ### Row combinations and [Jo26] Lemma 5.6 -/

/-- The `λ`-combination of the rows of an interleaved word: `i ↦ ∑ₖ λₖ • w(i)ₖ`. -/
def rowComb {s : ℕ} (lam : Fin s → F) (w : ι → Fin s → A) : ι → A :=
  fun i => ∑ k, lam k • w i k

/-- Row-combining an interleaved codeword of `C^⋈s` lands in the (linear) base code. -/
lemma rowComb_mem {s : ℕ} (C : Submodule F (ι → A)) (lam : Fin s → F)
    {w : ι → Fin s → A} (hw : w ∈ ((C : Set (ι → A))^⋈ (Fin s))) :
    rowComb lam w ∈ C := by
  have hrow : ∀ k, (fun i => w i k) ∈ C := fun k => hw k
  have heq : rowComb lam w = ∑ k, lam k • (fun i => w i k) := by
    funext i
    simp [rowComb, Finset.sum_apply]
  rw [heq]
  exact Submodule.sum_mem C fun k _ => Submodule.smul_mem C _ (hrow k)

/-- Row combination commutes with curve evaluation. -/
lemma rowComb_curveAt {ℓ s : ℕ} (lam : Fin s → F) (U : Fin (ℓ + 1) → ι → Fin s → A)
    (α : F) : rowComb lam (curveAt U α) = curveAt (fun j => rowComb lam (U j)) α := by
  funext i
  simp only [rowComb, curveAt, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  exact smul_comm _ _ _

/-- Relative distances over the same index set compare like the underlying Hamming
distances (even across different alphabets). -/
lemma relHammingDist_le_of_hammingDist_le {M' : Type} [DecidableEq M']
    {u v : ι → M} {u' v' : ι → M'}
    (h : hammingDist u v ≤ hammingDist u' v') : δᵣ(u, v) ≤ δᵣ(u', v') := by
  simp only [Code.relHammingDist]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_right' (Nat.cast_le.mpr h) _

/-- **[Jo26] Lemma 5.6.**  Row combination does not increase relative Hamming distance:
if two interleaved words agree at a position, so do their `λ`-combinations. -/
theorem relHammingDist_rowComb_le {s : ℕ} (lam : Fin s → F) (v w : ι → Fin s → A) :
    δᵣ(rowComb lam v, rowComb lam w) ≤ δᵣ(v, w) := by
  refine relHammingDist_le_of_hammingDist_le ?_
  have h := hammingDist_comp_le_hammingDist
    (fun _ : ι => fun m : Fin s → A => ∑ k, lam k • m k) (x := v) (y := w)
  simpa [rowComb] using h

/-! ### The combination subspaces `V_B` and [Jo26] Theorem 5.7 -/

/-- The subspace `V_B ≤ F^s` of combination vectors `λ` whose row-combined `f` is
*exactly* a codeword curve on `B`: `λ ∈ V_B` iff there are `h₀, …, h_ℓ ∈ C` with
`λ ⋅ f(α) = ∑ⱼ hⱼ αʲ` for every `α ∈ B` ([Jo26] proof of Theorem 5.7).  Linearity of `C`
makes this a subspace: witnesses add, scale, and `0` is witnessed by the zero curve. -/
def combCurveSubmodule (C : Submodule F (ι → A)) {ℓ s : ℕ}
    (f : F → ι → Fin s → A) (B : Finset F) : Submodule F (Fin s → F) where
  carrier := {lam | ∃ h : Fin (ℓ + 1) → ι → A, (∀ j, h j ∈ C) ∧
    ∀ α ∈ B, rowComb lam (f α) = curveAt h α}
  zero_mem' := ⟨0, fun _ => C.zero_mem, fun α _ => by
    funext i
    simp [rowComb, curveAt]⟩
  add_mem' := by
    rintro lam lam' ⟨h, hh, hag⟩ ⟨h', hh', hag'⟩
    refine ⟨h + h', fun j => C.add_mem (hh j) (hh' j), fun α hα => ?_⟩
    funext i
    have h1 := congrFun (hag α hα) i
    have h2 := congrFun (hag' α hα) i
    simp only [rowComb, curveAt] at h1 h2 ⊢
    calc ∑ k, (lam + lam') k • f α i k
        = (∑ k, lam k • f α i k) + ∑ k, lam' k • f α i k := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun k _ => by rw [Pi.add_apply, add_smul]
      _ = (∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • h j i)
          + ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • h' j i := by rw [h1, h2]
      _ = ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • (h + h') j i := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => by
            rw [Pi.add_apply, Pi.add_apply, smul_add]
  smul_mem' := by
    rintro r lam ⟨h, hh, hag⟩
    refine ⟨r • h, fun j => C.smul_mem r (hh j), fun α hα => ?_⟩
    funext i
    have h1 := congrFun (hag α hα) i
    simp only [rowComb, curveAt] at h1 ⊢
    calc ∑ k, (r • lam) k • f α i k
        = r • ∑ k, lam k • f α i k := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun k _ => by
            rw [Pi.smul_apply, smul_eq_mul, mul_smul]
      _ = r • ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • h j i := by rw [h1]
      _ = ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • (r • h) j i := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [Pi.smul_apply]
          rw [smul_comm]

/-- **[Jo26] Theorem 5.7 (interleaving transfer for marked curve decodability).**
If the linear code `C` is marked `(ℓ, δ, a, b)`-curve-decodable, `b ≤ a`, and
`C(a, b) ≤ q = |F|`, then for every `s ≥ 1` the `s`-fold interleaved code `C^⋈s` is
marked `(ℓ, δ, a, b)`-curve-decodable.

Proof: for any marked instance `(U, f, A₀)` of the interleaved code, each `b`-subset
`B ⊆ A₀` carries a subspace `V_B ≤ F^s` (`combCurveSubmodule`).  Every `λ ∈ F^s` lies in
some `V_B`: the row-combined instance `(λ⋅U, λ⋅f)` is a marked instance of the base code
by Lemma 5.6 (`relHammingDist_rowComb_le`), so marked decodability produces `b`
agreements, i.e. a `b`-subset `B` witnessing `λ ∈ V_B`.  There are `C(a, b) ≤ q` of the
`V_B`, so by the covering lemma ([Jo26] Lemma 3.2, in-tree
`Jo26Gen.exists_nonzero_notMem_of_proper_family_of_card_le`) they cannot all be proper:
some `V_B = ⊤`.  Evaluating that `V_B` at the standard basis vectors and assembling the
per-row codeword curves column by column yields an interleaved codeword curve agreeing
with `f` on `B ⊆ A₀`, `|B| = b`. -/
theorem markedCurveDecodable_interleaved (C : Submodule F (ι → A)) (ℓ : ℕ) (δ : ℚ≥0)
    {a b : ℕ} (s : ℕ) [NeZero s] (hba : b ≤ a)
    (hchoose : a.choose b ≤ Fintype.card F)
    (hC : MarkedCurveDecodable F (C : Set (ι → A)) ℓ δ a b) :
    MarkedCurveDecodable F ((C : Set (ι → A))^⋈ (Fin s)) ℓ δ a b := by
  classical
  intro U f hf A₀ hA₀card hclose
  -- Step 1: the subspaces V_B cover F^s.
  have hcover : ∀ lam : Fin s → F, ∃ B ∈ A₀.powersetCard b,
      lam ∈ combCurveSubmodule C (ℓ := ℓ) f B := by
    intro lam
    have hclose' : ∀ α ∈ A₀,
        δᵣ(curveAt (fun j => rowComb lam (U j)) α, rowComb lam (f α)) ≤ δ := by
      intro α hα
      rw [← rowComb_curveAt]
      exact (relHammingDist_rowComb_le lam _ _).trans (hclose α hα)
    obtain ⟨c, hc, hbcard⟩ := hC (fun j => rowComb lam (U j))
      (fun α => rowComb lam (f α)) (fun α => rowComb_mem C lam (hf α))
      A₀ hA₀card hclose'
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hbcard
    refine ⟨B, Finset.mem_powersetCard.mpr
      ⟨hBsub.trans (Finset.filter_subset _ _), hBcard⟩,
      c, hc, fun α hα => (Finset.mem_filter.mp (hBsub hα)).2⟩
  -- Step 2: a.choose b ≤ q proper subspaces cannot cover, so some V_B is everything.
  have hex_top : ∃ B ∈ A₀.powersetCard b, combCurveSubmodule C (ℓ := ℓ) f B = ⊤ := by
    by_contra hnot
    push_neg at hnot
    have hne : (A₀.powersetCard b).Nonempty := by
      obtain ⟨B, hBsub, hBcard⟩ :=
        Finset.exists_subset_card_eq (show b ≤ A₀.card by omega)
      exact ⟨B, Finset.mem_powersetCard.mpr ⟨hBsub, hBcard⟩⟩
    haveI : Nonempty {B // B ∈ A₀.powersetCard b} :=
      ⟨⟨hne.choose, hne.choose_spec⟩⟩
    have hcardle : Fintype.card {B // B ∈ A₀.powersetCard b} ≤ Fintype.card F := by
      rw [Fintype.card_coe, Finset.card_powersetCard, hA₀card]
      exact hchoose
    obtain ⟨lam, -, hlam⟩ := Jo26Gen.exists_nonzero_notMem_of_proper_family_of_card_le
      (t := s) (Nat.one_le_iff_ne_zero.mpr (NeZero.ne s)) hcardle
      (fun B : {B // B ∈ A₀.powersetCard b} => combCurveSubmodule C (ℓ := ℓ) f B.val)
      (fun B => hnot B.val B.property)
    obtain ⟨B, hB, hmem⟩ := hcover lam
    exact hlam ⟨B, hB⟩ hmem
  obtain ⟨B, hB, htop⟩ := hex_top
  obtain ⟨hBsub, hBcard⟩ := Finset.mem_powersetCard.mp hB
  -- Step 3: standard-basis evaluation yields per-row codeword curves.
  have hrow : ∀ k : Fin s, ∃ h : Fin (ℓ + 1) → ι → A, (∀ j, h j ∈ C) ∧
      ∀ α ∈ B, (fun i => f α i k) = curveAt h α := by
    intro k
    have hmem : (Pi.single k 1 : Fin s → F) ∈ combCurveSubmodule C (ℓ := ℓ) f B := by
      rw [htop]; exact Submodule.mem_top
    obtain ⟨h, hh, hag⟩ := hmem
    refine ⟨h, hh, fun α hα => ?_⟩
    rw [← hag α hα]
    funext i
    simp [rowComb, Pi.single_apply, ite_smul]
  choose h hhC hhag using hrow
  -- Step 4: assemble the interleaved codeword curve column by column.
  refine ⟨fun j => fun i k => h k j i, fun j k => hhC k j, ?_⟩
  have hsub : B ⊆ A₀.filter fun α => f α = curveAt (fun j => fun i k => h k j i) α := by
    intro α hα
    refine Finset.mem_filter.mpr ⟨hBsub hα, ?_⟩
    funext i k
    have hk : f α i k = curveAt (h k) α i := congrFun (hhag k α hα) i
    rw [hk]
    simp [curveAt, Finset.sum_apply]
  calc b = B.card := hBcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- **[Jo26] Theorem 5.7, original-form conclusion.**  Under the same hypotheses, the
interleaved code is plainly `(ℓ, δ, a, b)`-curve-decodable. -/
theorem curveDecodable_interleaved (C : Submodule F (ι → A)) (ℓ : ℕ) (δ : ℚ≥0)
    {a b : ℕ} (s : ℕ) [NeZero s] (hba : b ≤ a)
    (hchoose : a.choose b ≤ Fintype.card F)
    (hC : MarkedCurveDecodable F (C : Set (ι → A)) ℓ δ a b) :
    CurveDecodable F ((C : Set (ι → A))^⋈ (Fin s)) ℓ δ a b :=
  curveDecodable_of_marked (markedCurveDecodable_interleaved C ℓ δ s hba hchoose hC)

/-! ### [Jo26] Lemma 5.2: interpolation for `b ≤ ℓ + 1` -/

/-- **[Jo26] Lemma 5.2.**  For `b ≤ ℓ + 1` (and `b ≤ a`) every linear code is marked
`(ℓ, δ, a, b)`-curve-decodable, for *any* `δ`: pick any `b` points of the marked set and
Lagrange-interpolate `f` through them.  Each interpolation coefficient is an `F`-linear
combination of the codewords `f(α)`, hence again a codeword. -/
theorem markedCurveDecodable_of_interpolation (C : Submodule F (ι → A)) (ℓ : ℕ)
    (δ : ℚ≥0) {a b : ℕ} (hba : b ≤ a) (hbl : b ≤ ℓ + 1) :
    MarkedCurveDecodable F (C : Set (ι → A)) ℓ δ a b := by
  classical
  intro u f hf A₀ hA₀card _hclose
  obtain ⟨t, htsub, htcard⟩ :=
    Finset.exists_subset_card_eq (show b ≤ A₀.card by omega)
  set P : F → F[X] := fun m => Lagrange.basis t id m with hP
  set c : Fin (ℓ + 1) → ι → A := fun j => ∑ m ∈ t, (P m).coeff (j : ℕ) • f m with hc
  have hinj : Set.InjOn id (t : Set F) := fun _ _ _ _ hxy => hxy
  have hdeg : ∀ m ∈ t, (P m).natDegree < ℓ + 1 := by
    intro m hm
    have h1 : 1 ≤ t.card := Finset.card_pos.mpr ⟨m, hm⟩
    have h2 : (P m).natDegree = t.card - 1 := Lagrange.natDegree_basis hinj hm
    omega
  have hagree : ∀ α ∈ t, f α = curveAt c α := by
    intro α₀ hα₀
    funext i
    have heval : ∀ m ∈ t,
        ∑ j : Fin (ℓ + 1), (P m).coeff (j : ℕ) * α₀ ^ (j : ℕ) = (P m).eval α₀ := by
      intro m hm
      rw [Polynomial.eval_eq_sum_range' (hdeg m hm) α₀]
      exact Fin.sum_univ_eq_sum_range (fun j => (P m).coeff j * α₀ ^ j) (ℓ + 1)
    calc f α₀ i
        = ∑ m ∈ t, (P m).eval α₀ • f m i := by
          rw [Finset.sum_eq_single α₀]
          · have hself : (P α₀).eval α₀ = 1 := by
              simpa [hP] using
                (Lagrange.eval_basis_self (s := t) (v := id) hinj hα₀)
            rw [hself, one_smul]
          · intro m _ hne
            have hzero : (P m).eval α₀ = 0 := by
              simpa [hP] using
                (Lagrange.eval_basis_of_ne (s := t) (v := id)
                  (i := m) (j := α₀) hne hα₀)
            rw [hzero, zero_smul]
          · intro hα
            exact absurd hα₀ hα
      _ = ∑ m ∈ t, (∑ j : Fin (ℓ + 1), (P m).coeff (j : ℕ) * α₀ ^ (j : ℕ)) • f m i := by
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [heval m hm]
      _ = ∑ m ∈ t, ∑ j : Fin (ℓ + 1), ((P m).coeff (j : ℕ) * α₀ ^ (j : ℕ)) • f m i := by
          exact Finset.sum_congr rfl fun m _ => Finset.sum_smul
      _ = ∑ j : Fin (ℓ + 1), ∑ m ∈ t, ((P m).coeff (j : ℕ) * α₀ ^ (j : ℕ)) • f m i :=
          Finset.sum_comm
      _ = curveAt c α₀ i := by
          simp only [curveAt, hc, Finset.sum_apply, Pi.smul_apply]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [smul_smul, mul_comm]
  refine ⟨c, fun j => Submodule.sum_mem C fun m _ => Submodule.smul_mem C _ (hf m), ?_⟩
  calc b = t.card := htcard.symm
    _ ≤ _ := Finset.card_le_card fun α hα =>
        Finset.mem_filter.mpr ⟨htsub hα, hagree α hα⟩

/-! ### [Jo26] Lemma 5.4 and Theorem 5.5: original ⟹ marked -/

/-- **Far-word supply** — the existence condition underlying the counting step of [Jo26]
Lemma 5.4: for every word `w` there is a codeword at relative distance `> δ` from `w`.
[Jo26] discharges this by counting (codewords near `w` are few when the code is large
enough); here it is a named hypothesis, with `farWordSupply_of_far_pair` as a clean
sufficient condition. -/
def FarWordSupply (C : Set (ι → M)) (δ : ℚ≥0) : Prop :=
  ∀ w : ι → M, ∃ v ∈ C, ¬ δᵣ(w, v) ≤ δ

/-- Two codewords at relative distance `> 2δ` supply a `δ`-far codeword for every
center, by the triangle inequality. -/
theorem farWordSupply_of_far_pair {C : Set (ι → M)} {δ : ℚ≥0}
    {c₁ c₂ : ι → M} (h₁ : c₁ ∈ C) (h₂ : c₂ ∈ C) (hfar : 2 * δ < δᵣ(c₁, c₂)) :
    FarWordSupply C δ := by
  intro w
  by_contra hcon
  push_neg at hcon
  have hd₁ := hcon c₁ h₁
  have hd₂ := hcon c₂ h₂
  have htri : δᵣ(c₁, c₂) ≤ δᵣ(w, c₁) + δᵣ(w, c₂) := by
    have hnat : hammingDist c₁ c₂ ≤ hammingDist w c₁ + hammingDist w c₂ := by
      rw [hammingDist_comm w c₁]
      exact hammingDist_triangle c₁ w c₂
    simp only [Code.relHammingDist]
    rw [← add_div]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    refine mul_le_mul_right' ?_ _
    exact_mod_cast hnat
  have hle : δᵣ(c₁, c₂) ≤ 2 * δ := by
    calc δᵣ(c₁, c₂) ≤ δᵣ(w, c₁) + δᵣ(w, c₂) := htri
      _ ≤ δ + δ := add_le_add hd₁ hd₂
      _ = 2 * δ := (two_mul δ).symm
  exact absurd hfar (not_lt.mpr hle)

/-- **Original ⟹ marked ([Jo26] Lemma 5.4 / Theorem 5.5, substantive half),
conditional on `FarWordSupply C δ`.**  Redefine `f` outside the marked set `A₀` to a
codeword that is `δ`-far from the curve point there; the close set of the modified
instance is then *exactly* `A₀`, so original curve decodability concludes inside `A₀`,
where the modified function agrees with `f`. -/
theorem markedCurveDecodable_of_curveDecodable {C : Set (ι → M)} {ℓ : ℕ} {δ : ℚ≥0}
    {a b : ℕ} (hfws : FarWordSupply C δ) (hC : CurveDecodable F C ℓ δ a b) :
    MarkedCurveDecodable F C ℓ δ a b := by
  classical
  intro u f hf A₀ hA₀card hclose
  choose far hfarC hfarFar using hfws
  set g : F → ι → M := fun α => if α ∈ A₀ then f α else far (curveAt u α) with hg
  have hgC : ∀ α, g α ∈ C := by
    intro α
    rw [hg]
    dsimp only
    split_ifs with hα
    · exact hf α
    · exact hfarC _
  have hgclose : closeSet δ u g = A₀ := by
    ext α
    rw [mem_closeSet]
    constructor
    · intro hd
      by_contra hα
      rw [hg] at hd
      dsimp only at hd
      rw [if_neg hα] at hd
      exact hfarFar (curveAt u α) hd
    · intro hα
      rw [hg]
      dsimp only
      rw [if_pos hα]
      exact hclose α hα
  obtain ⟨c, hc, hb⟩ := hC u g hgC (by rw [hgclose, hA₀card])
  refine ⟨c, hc, ?_⟩
  rw [hgclose] at hb
  have hfilter : (A₀.filter fun α => g α = curveAt c α)
      = A₀.filter fun α => f α = curveAt c α := by
    refine Finset.filter_congr fun α hα => ?_
    rw [hg]
    dsimp only
    rw [if_pos hα]
  rwa [hfilter] at hb

/-- **[Jo26] Theorem 5.5** (as an equivalence): under the far-word supply, curve
decodability and marked curve decodability coincide. -/
theorem curveDecodable_iff_markedCurveDecodable {C : Set (ι → M)} {ℓ : ℕ} {δ : ℚ≥0}
    {a b : ℕ} (hfws : FarWordSupply C δ) :
    CurveDecodable F C ℓ δ a b ↔ MarkedCurveDecodable F C ℓ δ a b :=
  ⟨markedCurveDecodable_of_curveDecodable hfws, curveDecodable_of_marked⟩

/-- **[Jo26] Theorem 5.7 from the original hypothesis**, conditional on the far-word
supply for the base code: curve decodability of `C` upgrades to marked curve
decodability ([Jo26] Theorem 5.5) and then transfers to every interleaving. -/
theorem markedCurveDecodable_interleaved_of_curveDecodable (C : Submodule F (ι → A))
    (ℓ : ℕ) (δ : ℚ≥0) {a b : ℕ} (s : ℕ) [NeZero s] (hba : b ≤ a)
    (hchoose : a.choose b ≤ Fintype.card F)
    (hfws : FarWordSupply (C : Set (ι → A)) δ)
    (hC : CurveDecodable F (C : Set (ι → A)) ℓ δ a b) :
    MarkedCurveDecodable F ((C : Set (ι → A))^⋈ (Fin s)) ℓ δ a b :=
  markedCurveDecodable_interleaved C ℓ δ s hba hchoose
    (markedCurveDecodable_of_curveDecodable hfws hC)

end ProximityGap.CurveDec

#print axioms ProximityGap.CurveDec.curveDecodable_of_marked
#print axioms ProximityGap.CurveDec.relHammingDist_rowComb_le
#print axioms ProximityGap.CurveDec.markedCurveDecodable_interleaved
#print axioms ProximityGap.CurveDec.curveDecodable_interleaved
#print axioms ProximityGap.CurveDec.markedCurveDecodable_of_interpolation
#print axioms ProximityGap.CurveDec.farWordSupply_of_far_pair
#print axioms ProximityGap.CurveDec.markedCurveDecodable_of_curveDecodable
#print axioms ProximityGap.CurveDec.curveDecodable_iff_markedCurveDecodable
#print axioms ProximityGap.CurveDec.markedCurveDecodable_interleaved_of_curveDecodable

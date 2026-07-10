/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Jo26CurveInterpolationRegime
import ArkLib.Data.CodingTheory.ProximityGap.GG25CurveDecodFromListSize
import ArkLib.Data.CodingTheory.ProximityGap.GG25MCAFromCurveDecodability
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSMinDistance
import ArkLib.Data.CodingTheory.ProximityGap.SubspaceDesignListSize

/-!
# B2 brick W17 — curve stitching: interpolation ⟹ ball-count curve list-size (#334 B2, #466)

**Where this sits.** The B2 lane ([GG25] ePrint 2025/2054 Def 3.1 / [Jo26] ePrint 2026/891
Def 2.7 curve decodability) has, in-tree and axiom-clean: the definition (`CurveDecodable`,
`curveCloseSet`), the pigeonhole engine `curveDecodable_of_curveListSize`
(`CurveListSizeLe C ℓ δ m` ∧ `m·b ≤ a` ⟹ `(ℓ,δ,a,b)`-curve-decodable), the universal `m = |F|`
anchor (`Frontier/_GG25CurveDecodabilityOpener`), the f-value refinement
(`Frontier/_GG25CurveDecodNextBrick`), the per-row product bound (`…B2Capstone`,
`m = L_row^(ℓ+1)`), and the small-witness Lagrange regime `b ≤ ℓ+1`
(`Jo26CurveInterpolationRegime`, [Jo26] Rem 5.3: the trivial regime).  The JLR26
(arXiv 2601.10047) chain toward the folded-RS capacity bound had two named in-tree gaps
(kb `jlr26-frs-subspace-design-formalization-map-2026-06-13.md` §2): **line stitching
(Lemma 5.7)** and **peeling (Lemma 5.10)**.

**What this file adds — the stitching mechanism, unconditional, for every `F`-linear code.**
The JLR26 5.7 stitching step, in the in-tree curve vocabulary and at every curve degree `ℓ`
(lines = `ℓ = 1`):

1. `sum_basis_eval_mul_pow` / `lagrangeCurve_comb_eq_of_agree` — **the stitching identity**:
   the degree-`≤ ℓ` Lagrange codeword-curve through the `ℓ+1` graph points
   `(α, f α)`, `α ∈ B`, coincides with the tested curve `∑ⱼ γʲ·uⱼ` **at every seed `γ`** on any
   coordinate where all `ℓ+1` interpolated codewords agree with the tested curve (two degree-`≤ ℓ`
   `A`-valued polynomials agreeing at `ℓ+1` points are equal; module-valued Lagrange uniqueness).
2. `hammingDist_comb_lagrangeCurve_le` — **the all-seeds spread**: if `B` consists of `ℓ+1`
   *close* seeds (`⊆ curveCloseSet δ u f`), the stitched curve is `(ℓ+1)·⌊δn⌋`-close to the
   tested stack at **every** seed `γ ∈ F` (union bound over the `ℓ+1` per-seed error sets).
3. `hammingDist_f_lagrangeCurve_le` — **the transfer**: every close seed `β` then has its
   codeword `f β` within `(ℓ+2)·⌊δn⌋` of the stitched curve value (triangle), i.e.
   `f β − comb cs β` is a **codeword of weight `≤ (ℓ+2)·⌊δn⌋`** — a ball-around-zero element.
4. `curveListSizeLe_of_ball_le` — **the ball-count curve list-size**: hence the close set is
   covered by the translates of ONE stitched curve by low-weight codewords, so
   `CurveListSizeLe C ℓ δ L` for any `L` bounding the number of codewords of weight
   `≤ (ℓ+2)·⌊δn⌋`.  This replaces the per-row product `L_row^(ℓ+1)` (B2Capstone) by a
   *single ball list count* — the [JLR26 §5.3] structure.  The one-level peeling of
   [JLR26 Lemma 5.10] (split the close set into explanation fibers, pigeonhole) is exactly the
   in-tree engine `curveDecodable_of_curveListSize` applied to this list-size; the *recursive*
   multi-line peeling of 5.10 is NOT formalized here.
5. `curveDecodable_of_ball_le` / `curveListSizeLe_one_of_min_norm` /
   `curveDecodable_full_of_min_norm` — the payoff: `L·b ≤ a` gives `(ℓ,δ,a,b)`-curve
   decodability; in the curve-UDR regime `(ℓ+2)·⌊δn⌋ < wt_min(C)` the ball is `{0}`, `L = 1`,
   and ONE curve explains the **entire** close set: `(ℓ, δ, a, a)`-curve-decodability for every
   `a` — the first in-tree unconditional instance with `b > ℓ+1` (indeed `b = a`, vs the
   `b ≤ ℓ+1` trivial regime of [Jo26] Lemma 5.2).
6. `rs_curveDecodable_udr` — **concrete family instance**: explicit plain Reed–Solomon
   (any embedded domain) is `(ℓ, δ, a, a)`-curve-decodable whenever
   `(ℓ+2)·⌊δn⌋ < n − (k−1)` (from the in-tree RS Singleton distance
   `ArkLib.CS25.rsCodeFinset_hammingDist_ge`).
7. `subspaceDesign_curveListSizeLe` / `subspaceDesign_curveDecodable` — **[JLR26] Lemma 5.7 in
   the in-tree subspace-design vocabulary**: for a `τ`-subspace-design code, the ball count is
   bounded by the in-tree confinement list bound `subspaceDesign_list_card_le` (Claim 5.8) at
   the received word `y = 0`, giving `CurveListSizeLe C ℓ δ (|F|^(r−1))` and hence
   `(ℓ, δ, a, b)`-curve-decodability under `|F|^(r−1)·b ≤ a`, whenever
   `τ(r)·n + r·n < (r+1)·(n − (ℓ+2)⌊δn⌋)`.  This composes stitching (this file) with
   confinement (`SubspaceDesignListDim/ListSize`) — the 5.4+5.8 ⟹ 5.7 assembly of the JLR26
   map, with the *crude* `|F|^(r−1)` count (the pruned `poly(1/η)` count via Lemma 5.5 pinning
   remains open, as does the recursive 5.10 peeling and the FRS τ-parameter instantiation).

**Honest scope.** Everything here is unconditional and axiom-clean.  It does NOT touch the
plain-RS prize core: the ball count above the unique-decoding radius for plain RS in the δ*
window is exactly the open list-size wall (`RSCurveListSizeResidual` / BCHKS Conj 1.12), and the
subspace-design instance is FRS-shaped (plain RS `s = 1` has a useless τ-profile — see the
workbench §R.2 boundary).  This brick feeds the FRS/list-decoding arm of the campaign, closing
the "line stitching (5.7)" gap of the JLR26 in-tree map at the crude-count level.

Numerically refutation-tested first: `scripts/probes/probe_w17_curve_stitching.py`
(494 adversarial trials over GF(11)/GF(13)/GF(17), claims 1–4 including the UDR full
explanation: 0 violations).

## References
* [GG25] Z. Guo, V. Guruswami, ePrint 2025/2054 (ECCC TR25-166), Def 3.1, Thm 3.3.
* [Jo26] S. Jo, ePrint 2026/891, Def 2.7, Lemma 5.2, Rem 5.3.
* [JLR26] Jeronimo–Liu–Rajpal, arXiv 2601.10047, §5.3–5.4 (Lemmas 5.4, 5.7, 5.10, Claim 5.8).
  Issue #334, class B2.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Finset Code Polynomial
open scoped NNReal

namespace ProximityGap.W17Stitching

open ProximityGap ProximityGap.GG25Lemma32 CodingTheory

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ### The scalar Lagrange reproduction identities -/

/-- **Monomial reproduction.** Lagrange interpolation at the nodes `B` reproduces the monomial
`γ^k` for every `k < |B|`: `∑_{α ∈ B} (basisₐ).eval γ · α^k = γ^k`.  (Uniqueness of degree-`<|B|`
interpolation, `Lagrange.eq_interpolate` at `f = X^k`.) -/
private lemma sum_basis_eval_mul_pow {B : Finset F} {k : ℕ} (hk : k < B.card) (γ : F) :
    ∑ α ∈ B, (Lagrange.basis B id α).eval γ * α ^ k = γ ^ k := by
  classical
  have hinj : Set.InjOn (id : F → F) B := fun _ _ _ _ h => h
  have hdeg : (Polynomial.X ^ k : Polynomial F).degree < B.card := by
    rw [Polynomial.degree_X_pow]
    exact_mod_cast hk
  have h := Lagrange.eq_interpolate (v := id) hinj hdeg
  have hev := congrArg (Polynomial.eval γ) h
  rw [Lagrange.interpolate_apply] at hev
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, id_eq] at hev
  -- hev : γ ^ k = ∑ α ∈ B, α ^ k * (basis B id α).eval γ
  calc ∑ α ∈ B, (Lagrange.basis B id α).eval γ * α ^ k
      = ∑ α ∈ B, α ^ k * (Lagrange.basis B id α).eval γ :=
        Finset.sum_congr rfl fun α _ => mul_comm _ _
    _ = γ ^ k := hev.symm

/-- The Lagrange basis evaluation as its `Fin (ℓ+1)`-truncated coefficient sum (the basis
polynomial has degree `|B| − 1 = ℓ`). -/
private lemma basis_eval_eq_fin_sum {B : Finset F} {ℓ : ℕ} (hB : B.card = ℓ + 1)
    {α : F} (hα : α ∈ B) (γ : F) :
    ∑ j : Fin (ℓ + 1), (Lagrange.basis B id α).coeff (j : ℕ) * γ ^ (j : ℕ)
      = (Lagrange.basis B id α).eval γ := by
  have hinj : Set.InjOn (id : F → F) B := fun _ _ _ _ h => h
  have hdeg : (Lagrange.basis B id α).natDegree < ℓ + 1 := by
    rw [Lagrange.natDegree_basis hinj hα, hB]
    omega
  rw [Polynomial.eval_eq_sum_range' hdeg γ]
  exact Fin.sum_univ_eq_sum_range (fun k => (Lagrange.basis B id α).coeff k * γ ^ k) (ℓ + 1)

/-! ### The stitching identity (module-valued Lagrange uniqueness) -/

/-- **The stitching identity ([JLR26] 5.7 mechanism, coordinate form).**  If the `ℓ+1`
interpolated values agree with the tested curve at coordinate `i` (`f α i = comb u α i` for all
`α ∈ B`), then the Lagrange codeword-curve through them coincides with the tested curve at `i`
**for every seed `γ`**: two degree-`≤ ℓ` `A`-valued polynomials agreeing at the `ℓ+1` points of
`B` are equal. -/
theorem lagrangeCurve_comb_eq_of_agree {B : Finset F} {ℓ : ℕ} (hB : B.card = ℓ + 1)
    {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A} {i : ι}
    (hagree : ∀ α ∈ B, f α i = comb u α i) (γ : F) :
    comb (fun j : Fin (ℓ + 1) => lagrangeCurve B f (j : ℕ)) γ i = comb u γ i := by
  classical
  have hstep1 : comb (fun j : Fin (ℓ + 1) => lagrangeCurve B f (j : ℕ)) γ i
      = ∑ α ∈ B, (Lagrange.basis B id α).eval γ • f α i := by
    rw [comb]
    calc ∑ j : Fin (ℓ + 1), γ ^ (j : ℕ) • lagrangeCurve B f (j : ℕ) i
        = ∑ j : Fin (ℓ + 1), ∑ α ∈ B,
            ((Lagrange.basis B id α).coeff (j : ℕ) * γ ^ (j : ℕ)) • f α i := by
          refine Finset.sum_congr rfl fun j _ => ?_
          unfold lagrangeCurve
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [smul_smul, mul_comm]
      _ = ∑ α ∈ B, ∑ j : Fin (ℓ + 1),
            ((Lagrange.basis B id α).coeff (j : ℕ) * γ ^ (j : ℕ)) • f α i := Finset.sum_comm
      _ = ∑ α ∈ B, (Lagrange.basis B id α).eval γ • f α i := by
          refine Finset.sum_congr rfl fun α hα => ?_
          rw [← Finset.sum_smul, basis_eval_eq_fin_sum hB hα]
  have hstep2 : ∑ α ∈ B, (Lagrange.basis B id α).eval γ • f α i
      = ∑ k : Fin (ℓ + 1), γ ^ (k : ℕ) • u k i := by
    calc ∑ α ∈ B, (Lagrange.basis B id α).eval γ • f α i
        = ∑ α ∈ B, ∑ k : Fin (ℓ + 1),
            ((Lagrange.basis B id α).eval γ * α ^ (k : ℕ)) • u k i := by
          refine Finset.sum_congr rfl fun α hα => ?_
          rw [hagree α hα, comb, Finset.smul_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [smul_smul]
      _ = ∑ k : Fin (ℓ + 1), ∑ α ∈ B,
            ((Lagrange.basis B id α).eval γ * α ^ (k : ℕ)) • u k i := Finset.sum_comm
      _ = ∑ k : Fin (ℓ + 1), γ ^ (k : ℕ) • u k i := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← Finset.sum_smul, sum_basis_eval_mul_pow (by rw [hB]; exact k.isLt) γ]
  rw [hstep1, hstep2, comb]

/-! ### The all-seeds spread and the transfer -/

/-- Every close seed has integer distance `≤ ⌊δn⌋` between its codeword and the tested curve. -/
theorem close_seed_dist_le {δ : ℝ≥0} {ℓ : ℕ}
    {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A} {α : F}
    (hα : α ∈ curveCloseSet δ u f) :
    hammingDist (f α) (comb u α) ≤ ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ := by
  simp only [curveCloseSet, Finset.mem_filter, Finset.mem_univ, true_and] at hα
  have h2 := hammingDist_le_floor_of_relHam_le hα
  calc hammingDist (f α) (comb u α)
      = hammingDist (comb u α) (f α) := hammingDist_comm _ _
    _ ≤ ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ := h2

/-- **The all-seeds spread ([JLR26] 5.7 stitching, distance form).**  The Lagrange codeword-curve
through `ℓ+1` **close** seeds is `(ℓ+1)·⌊δn⌋`-close to the tested stack at **every** seed
`γ ∈ F`: any coordinate where the two curves differ at some seed must be a per-seed error
coordinate for one of the `ℓ+1` interpolation seeds (union bound over the stitching identity). -/
theorem hammingDist_comb_lagrangeCurve_le {δ : ℝ≥0} {ℓ : ℕ}
    {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A} {B : Finset F}
    (hBsub : B ⊆ curveCloseSet δ u f) (hBcard : B.card = ℓ + 1) (γ : F) :
    hammingDist (comb u γ) (comb (fun j : Fin (ℓ + 1) => lagrangeCurve B f (j : ℕ)) γ)
      ≤ (ℓ + 1) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ := by
  classical
  -- the disagreement coordinates inject into the union of per-seed error sets
  have hsub : (Finset.univ.filter fun i => comb u γ i ≠
        comb (fun j : Fin (ℓ + 1) => lagrangeCurve B f (j : ℕ)) γ i)
      ⊆ B.biUnion (fun α => Finset.univ.filter fun i => f α i ≠ comb u α i) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    by_contra hnot
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      not_exists, not_and, not_not] at hnot
    exact hi.2 (lagrangeCurve_comb_eq_of_agree hBcard hnot γ).symm
  have hcard : hammingDist (comb u γ)
        (comb (fun j : Fin (ℓ + 1) => lagrangeCurve B f (j : ℕ)) γ)
      ≤ ∑ α ∈ B, (Finset.univ.filter fun i => f α i ≠ comb u α i).card := by
    refine le_trans ?_ Finset.card_biUnion_le
    exact Finset.card_le_card hsub
  have hsum : ∑ α ∈ B, (Finset.univ.filter fun i => f α i ≠ comb u α i).card
      ≤ ∑ _α ∈ B, ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ := by
    refine Finset.sum_le_sum fun α hα => ?_
    exact close_seed_dist_le (hBsub hα)
  have hconst : (∑ _α ∈ B, ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊)
      = (ℓ + 1) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ := by
    rw [Finset.sum_const, smul_eq_mul, hBcard]
  exact le_trans hcard (le_trans hsum (le_of_eq hconst))

/-- **The transfer.**  Every close seed's codeword is within `(ℓ+2)·⌊δn⌋` of the stitched
curve's value there (triangle through the tested curve), i.e. the difference
`f β − comb cs β` is a codeword of weight `≤ (ℓ+2)·⌊δn⌋`. -/
theorem hammingDist_f_lagrangeCurve_le {δ : ℝ≥0} {ℓ : ℕ}
    {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A} {B : Finset F}
    (hBsub : B ⊆ curveCloseSet δ u f) (hBcard : B.card = ℓ + 1)
    {β : F} (hβ : β ∈ curveCloseSet δ u f) :
    hammingDist (f β) (comb (fun j : Fin (ℓ + 1) => lagrangeCurve B f (j : ℕ)) β)
      ≤ (ℓ + 2) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ := by
  calc hammingDist (f β) (comb (fun j : Fin (ℓ + 1) => lagrangeCurve B f (j : ℕ)) β)
      ≤ hammingDist (f β) (comb u β)
        + hammingDist (comb u β)
            (comb (fun j : Fin (ℓ + 1) => lagrangeCurve B f (j : ℕ)) β) :=
        hammingDist_triangle _ _ _
    _ ≤ ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊
        + (ℓ + 1) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ :=
        add_le_add (close_seed_dist_le hβ) (hammingDist_comb_lagrangeCurve_le hBsub hBcard β)
    _ = (ℓ + 2) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ := by ring

/-! ### The ball-count curve list-size -/

/-- **The ball-count curve list-size ([JLR26] 5.7-shape input for the pigeonhole engine).**
If every finite set of codewords of weight `≤ (ℓ+2)·⌊δn⌋` has size `≤ L` (a ball-around-zero
list bound), then `M` has curve list-size `≤ L`:

* if the close set has `≤ ℓ+1` seeds, ONE Lagrange curve through all of them covers it;
* otherwise, stitch through any `ℓ+1` close seeds; every close seed's codeword is then a
  low-weight-codeword translate of the stitched curve's value (`hammingDist_f_lagrangeCurve_le`),
  so shifting the stitched curve's constant row by those `≤ L` translates covers the close set.

This replaces the per-row product bound `L_row^(ℓ+1)` (`GG25CurveDecodabilityB2Capstone`) by a
single ball list count — linear, not exponential, in the list input. -/
theorem curveListSizeLe_of_ball_le (M : Submodule F (ι → A)) (ℓ : ℕ) (δ : ℝ≥0) {L : ℕ}
    (hL : 1 ≤ L)
    (hball : ∀ S : Finset (ι → A),
      (∀ c ∈ S, c ∈ M ∧ hammingNorm c ≤ (ℓ + 2) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊) →
      S.card ≤ L) :
    CurveListSizeLe (F := F) (M : Set (ι → A)) ℓ δ L := by
  classical
  intro u f hf
  by_cases hsize : (curveCloseSet δ u f).card ≤ ℓ + 1
  · -- small close set: one Lagrange curve through ALL close seeds
    refine ⟨{ chooseCurve := fun _ => fun j => lagrangeCurve (curveCloseSet δ u f) f (j : ℕ)
              mem_code := fun _ _ => lagrangeCurve_mem M hf _
              passes_through := fun α hα => funext fun i =>
                (lagrangeCurve_eval hsize hα i).symm }, ?_⟩
    have himg : (curveCloseSet δ u f).image
          (fun _ : F => fun j : Fin (ℓ + 1) => lagrangeCurve (curveCloseSet δ u f) f (j : ℕ))
        ⊆ {fun j : Fin (ℓ + 1) => lagrangeCurve (curveCloseSet δ u f) f (j : ℕ)} := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨α, _, rfl⟩ := hx
      exact Finset.mem_singleton_self _
    calc ((curveCloseSet δ u f).image _).card
        ≤ ({fun j : Fin (ℓ + 1) => lagrangeCurve (curveCloseSet δ u f) f (j : ℕ)} :
            Finset (Fin (ℓ + 1) → ι → A)).card := Finset.card_le_card himg
      _ = 1 := Finset.card_singleton _
      _ ≤ L := hL
  · -- large close set: stitch through ℓ+1 close seeds, then translate by low-weight codewords
    push_neg at hsize
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hsize.le
    set cs : Fin (ℓ + 1) → ι → A := fun j => lagrangeCurve B f (j : ℕ) with hcs
    have hcs_mem : ∀ j, cs j ∈ M := fun _ => lagrangeCurve_mem M hf _
    have hcomb_mem : ∀ β : F, comb cs β ∈ M := by
      intro β
      have hrw : comb cs β = ∑ j : Fin (ℓ + 1), β ^ (j : ℕ) • cs j := by
        funext i
        rw [comb, Finset.sum_apply]
        exact Finset.sum_congr rfl fun j _ => rfl
      rw [hrw]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcs_mem j)
    set eMap : F → ι → A := fun β => f β - comb cs β with heMap
    have he_mem : ∀ β, eMap β ∈ M := fun β => M.sub_mem (hf β) (hcomb_mem β)
    set gMap : (ι → A) → Fin (ℓ + 1) → ι → A :=
      fun w => Fin.cons (cs 0 + w) (fun j : Fin ℓ => cs j.succ) with hgMap
    -- evaluating a constant-row-shifted stitched curve
    have hexp : ∀ (w : ι → A) (β : F) (i : ι),
        (∑ j : Fin (ℓ + 1), β ^ (j : ℕ) • gMap w j i) = w i + comb cs β i := by
      intro w β i
      rw [comb, Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [hgMap, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, one_smul,
        Pi.add_apply]
      abel
    refine ⟨{ chooseCurve := fun β => gMap (eMap β)
              mem_code := ?_
              passes_through := ?_ }, ?_⟩
    · intro β j
      refine Fin.cases ?_ ?_ j
      · simp only [hgMap, Fin.cons_zero]
        exact M.add_mem (hcs_mem 0) (he_mem β)
      · intro j'
        simp only [hgMap, Fin.cons_succ]
        exact hcs_mem j'.succ
    · intro α _
      funext i
      rw [hexp (eMap α) α i]
      simp only [heMap, Pi.sub_apply]
      abel
    · -- image card: the assignment factors through the error map into the weight-≤(ℓ+2)⌊δn⌋ ball
      have h1 : (curveCloseSet δ u f).image (fun β => gMap (eMap β))
          = ((curveCloseSet δ u f).image eMap).image gMap := by
        rw [Finset.image_image, Function.comp_def]
      rw [h1]
      refine le_trans Finset.card_image_le (hball _ ?_)
      intro c hc
      rw [Finset.mem_image] at hc
      obtain ⟨β, hβ, rfl⟩ := hc
      refine ⟨he_mem β, ?_⟩
      have hn : hammingNorm (eMap β) = hammingDist (f β) (comb cs β) := by
        show hammingNorm (f β - comb cs β) = hammingDist (f β) (comb cs β)
        rw [hammingDist_comm, hammingDist_eq_hammingNorm, ← sub_eq_neg_add]
      rw [hn]
      exact hammingDist_f_lagrangeCurve_le hBsub hBcard hβ

/-- **The payoff: curve decodability from a ball list bound.**  Feeding the ball-count curve
list-size into the in-tree pigeonhole engine (`curveDecodable_of_curveListSize` — the one-level
[JLR26] 5.10 peeling): `L·b ≤ a` gives `(ℓ, δ, a, b)`-curve-decodability. -/
theorem curveDecodable_of_ball_le (M : Submodule F (ι → A)) (ℓ : ℕ) (δ : ℝ≥0) {L a b : ℕ}
    (hL : 1 ≤ L) (hLb : L * b ≤ a)
    (hball : ∀ S : Finset (ι → A),
      (∀ c ∈ S, c ∈ M ∧ hammingNorm c ≤ (ℓ + 2) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊) →
      S.card ≤ L) :
    CurveDecodable (F := F) (M : Set (ι → A)) ℓ δ a b :=
  curveDecodable_of_curveListSize hL hLb (curveListSizeLe_of_ball_le M ℓ δ hL hball)

/-! ### The curve-UDR regime: ball = {0}, one curve explains the whole close set -/

/-- **Curve list-size ONE in the curve-UDR regime.**  If every nonzero codeword has weight
`> (ℓ+2)·⌊δn⌋`, the ball is `{0}` and a SINGLE stitched curve covers the whole close set. -/
theorem curveListSizeLe_one_of_min_norm (M : Submodule F (ι → A)) (ℓ : ℕ) (δ : ℝ≥0)
    (hudr : ∀ c ∈ M, c ≠ 0 →
      (ℓ + 2) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ < hammingNorm c) :
    CurveListSizeLe (F := F) (M : Set (ι → A)) ℓ δ 1 := by
  classical
  refine curveListSizeLe_of_ball_le M ℓ δ le_rfl (fun S hS => ?_)
  have hsub : S ⊆ {0} := by
    intro c hc
    obtain ⟨hcM, hcw⟩ := hS c hc
    rw [Finset.mem_singleton]
    by_contra hne
    exact absurd hcw (not_le.mpr (hudr c hcM hne))
  exact le_trans (Finset.card_le_card hsub) (le_of_eq (Finset.card_singleton _))

/-- **Full explanation in the curve-UDR regime: `(ℓ, δ, a, a)`-curve-decodability for EVERY
`a`.**  One codeword-curve explains the ENTIRE close set — the first in-tree unconditional
instance beyond the trivial `b ≤ ℓ+1` interpolation regime ([Jo26] Rem 5.3). -/
theorem curveDecodable_full_of_min_norm (M : Submodule F (ι → A)) (ℓ : ℕ) (δ : ℝ≥0)
    (hudr : ∀ c ∈ M, c ≠ 0 →
      (ℓ + 2) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ < hammingNorm c) (a : ℕ) :
    CurveDecodable (F := F) (M : Set (ι → A)) ℓ δ a a :=
  curveDecodable_of_curveListSize le_rfl (le_of_eq (one_mul a))
    (curveListSizeLe_one_of_min_norm M ℓ δ hudr)

end ProximityGap.W17Stitching

namespace ProximityGap.W17Stitching

open ProximityGap ProximityGap.GG25Lemma32 CodingTheory

/-! ### Concrete family instance 1: explicit plain Reed–Solomon in the curve-UDR window -/

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Explicit plain RS is `(ℓ, δ, a, a)`-curve-decodable in the curve-UDR window.**  For any
embedded evaluation domain and degree bound `k ≥ 1`: whenever
`(ℓ+2)·⌊δn⌋ < n − (k−1)` (the stitched-ball radius is below the RS Singleton distance), one
codeword-curve explains the entire close set, at every threshold `a`.  Instantiable: e.g.
`n = 8, k = 2, ℓ = 1, δ = 1/8` gives `3·1 = 3 < 7`.  (The prize window `δ > 1−√ρ` is NOT
reached: there the ball count is the open list-size wall — see the module docstring.) -/
theorem rs_curveDecodable_udr (domain : ι ↪ F) (k : ℕ) [NeZero k] (ℓ : ℕ) (δ : ℝ≥0)
    (h : (ℓ + 2) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ < Fintype.card ι - (k - 1)) (a : ℕ) :
    CurveDecodable (F := F)
      ((ReedSolomon.code domain k : Submodule F (ι → F)) : Set (ι → F)) ℓ δ a a := by
  refine curveDecodable_full_of_min_norm (ReedSolomon.code domain k) ℓ δ ?_ a
  intro c hc hne
  have hd := ArkLib.CS25.rsCodeFinset_hammingDist_ge domain k c 0
    ((ArkLib.CS25.mem_rsCodeFinset domain k c).mpr hc)
    ((ArkLib.CS25.mem_rsCodeFinset domain k 0).mpr (Submodule.zero_mem _)) hne
  rw [hammingDist_zero_right] at hd
  omega

/-! ### Concrete family instance 2: subspace-design codes ([JLR26] Lemma 5.7, crude count) -/

variable {s : ℕ}

/-- **[JLR26] Lemma 5.7 in the in-tree subspace-design vocabulary (crude count).**  For a
`τ`-subspace-design code `C` (block alphabet `F^s`), the stitched ball of radius `(ℓ+2)·⌊δn⌋`
is a list of codewords agreeing with the received word `y = 0` on `≥ n − (ℓ+2)·⌊δn⌋`
coordinates, so the in-tree confinement bound `subspaceDesign_list_card_le` (Claim 5.8 + basis
extraction) caps it at `|F|^(r−1)` whenever `τ(r)·n + r·n < (r+1)·(n − (ℓ+2)⌊δn⌋)`.  Composed
with the stitching list-size this gives `CurveListSizeLe C ℓ δ (|F|^(r−1))` — line stitching at
every curve degree (lines = `ℓ = 1`), with the crude confinement count (the pruned `poly(1/η)`
count via the Lemma 5.5 pinning remains open). -/
theorem subspaceDesign_curveListSizeLe {τ : ℕ → ℝ}
    {C : Submodule F (ι → Fin s → F)} (h : IsSubspaceDesign s τ C)
    {r : ℕ} (hr : 1 ≤ r) (ℓ : ℕ) (δ : ℝ≥0)
    (hbig : τ r * Fintype.card ι + r * Fintype.card ι
      < (r + 1) * ((Fintype.card ι - (ℓ + 2) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ : ℕ) : ℝ)) :
    CurveListSizeLe (F := F) (C : Set (ι → Fin s → F)) ℓ δ (Fintype.card F ^ (r - 1)) := by
  classical
  refine curveListSizeLe_of_ball_le C ℓ δ (Nat.one_le_pow _ _ Fintype.card_pos)
    (fun S hS => ?_)
  refine ProximityGap.subspaceDesign_list_card_le h hr (0 : ι → Fin s → F) S
    (fun c hc => (hS c hc).1) (fun c hc => ?_) hbig
  -- weight ≤ (ℓ+2)⌊δn⌋ ⟹ agreement with 0 on ≥ n − (ℓ+2)⌊δn⌋ coordinates
  obtain ⟨-, hcw⟩ := hS c hc
  have hpart : (Finset.univ.filter fun i => c i = (0 : ι → Fin s → F) i).card
      + hammingNorm c = Fintype.card ι := by
    have h0 := CodeGeometry.agree_add_hammingDist c (0 : ι → Fin s → F)
    rw [hammingDist_zero_right] at h0
    exact h0
  omega

/-- **The subspace-design curve-decodability payoff ([JLR26] Lemma 5.7 + one-level 5.10
peeling).**  A `τ`-subspace-design code is `(ℓ, δ, a, b)`-curve-decodable whenever
`|F|^(r−1)·b ≤ a` and `τ(r)·n + r·n < (r+1)·(n − (ℓ+2)⌊δn⌋)`. -/
theorem subspaceDesign_curveDecodable {τ : ℕ → ℝ}
    {C : Submodule F (ι → Fin s → F)} (h : IsSubspaceDesign s τ C)
    {r : ℕ} (hr : 1 ≤ r) (ℓ : ℕ) (δ : ℝ≥0) {a b : ℕ}
    (hab : Fintype.card F ^ (r - 1) * b ≤ a)
    (hbig : τ r * Fintype.card ι + r * Fintype.card ι
      < (r + 1) * ((Fintype.card ι - (ℓ + 2) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ : ℕ) : ℝ)) :
    CurveDecodable (F := F) (C : Set (ι → Fin s → F)) ℓ δ a b :=
  curveDecodable_of_curveListSize (Nat.one_le_pow _ _ Fintype.card_pos) hab
    (subspaceDesign_curveListSizeLe h hr ℓ δ hbig)

end ProximityGap.W17Stitching

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.W17Stitching.lagrangeCurve_comb_eq_of_agree
#print axioms ProximityGap.W17Stitching.hammingDist_comb_lagrangeCurve_le
#print axioms ProximityGap.W17Stitching.hammingDist_f_lagrangeCurve_le
#print axioms ProximityGap.W17Stitching.curveListSizeLe_of_ball_le
#print axioms ProximityGap.W17Stitching.curveDecodable_of_ball_le
#print axioms ProximityGap.W17Stitching.curveListSizeLe_one_of_min_norm
#print axioms ProximityGap.W17Stitching.curveDecodable_full_of_min_norm
#print axioms ProximityGap.W17Stitching.rs_curveDecodable_udr
#print axioms ProximityGap.W17Stitching.subspaceDesign_curveListSizeLe
#print axioms ProximityGap.W17Stitching.subspaceDesign_curveDecodable

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Jo26CurveInterpolationRegime
import ArkLib.Data.CodingTheory.ProximityGap.GG25CurveDecodFromListSize
import ArkLib.Data.CodingTheory.ProximityGap.GG25MCAFromCurveDecodability
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSMinDistance

/-!
# B2 brick ZW17 — the recursive multi-curve peeling of [JLR26] Lemma 5.10 (#334 B2, #466)

**The named gap this closes.**  The landed stitching brick
`Frontier/_W17CurveDecodStitching.lean` closed the [JLR26] (arXiv 2601.10047) Lemma 5.7
"line stitching" gap of the in-tree map
(kb `jlr26-frs-subspace-design-formalization-map-2026-06-13` §2) at the crude-count level,
and its docstring names the remaining gap: "the one-level peeling of [JLR26 Lemma 5.10] is
exactly the in-tree engine `curveDecodable_of_curveListSize` applied to this list-size; the
*recursive* multi-line peeling of 5.10 is NOT formalized here."  This file formalizes that
recursive multi-line peeling, generalized from lines (`ℓ = 1`) to every curve degree `ℓ`,
in the in-tree curve vocabulary.

**[JLR26] Lemma 5.10, faithfully (paper pp. 18–19).**  Fix `2 ≤ t₁ ≤ t₂`.  If `C` has
`(δ, a, t₁)`-line stitching (Def 5.6) and is `(δ/(1−1/t₁), L)`-list-decodable (Def 5.9)
with `q > (L+1)²`, then `C` has line `(δ, ε, 1/t₂)`-correlated agreement with
`ε = ((t₂−1)·L + a)/q`.  The proof peels: iteratively apply stitching to the unexplained
residue of the close set, each stage removing the `≥ t₁` seeds exactly matched by the stage
line; each stage line is globally `δ/(1−1/t₁)`-close to the tested line at EVERY seed
(Lemma 5.4 spread); the number of distinct globally-close lines is `≤ L` (pairwise
collisions occupy few seeds, so at a collision-free seed the values are distinct codewords
in one list-decoding ball); so if no line accumulates `t₂` exact matches the process
terminates with `|close| ≤ (t₂−1)·L + (a−1)`.

**What is proven here (all unconditional, axiom-clean).**  In the in-tree vocabulary the
stitching input is exactly `MarkedCurveDecodable` ([Jo26] Def 5.1 = the curve form of
[JLR26] Def 5.6), and the "many exact matches ⟹ correlated agreement" tail of 5.10 is the
in-tree Theorem 3.3 engine (`GG25MCAFromCurveDecodability`); the missing piece was the
peeling core, proven here:

1. `comb_mem` / `comb_eq_comb_of_agree` / `card_agree_le_of_ne` — curve values are
   codewords; **curve value rigidity** (two degree-`≤ ℓ` curves whose value functions agree
   at `ℓ+1` seeds agree at every seed, from the W17 stitching identity, copied verbatim
   below with provenance), and the collision cap (value-distinct curves collide at `≤ ℓ`
   seeds).
2. `spread_mul_le` — **the [JLR26] Lemma 5.4 spread, exact-match form**: a codeword-curve
   exactly matching `f` on a set `B` of `> ℓ` close seeds is close to the tested stack at
   EVERY seed: `(|B| − ℓ)·Δ(comb u γ, comb cs γ) ≤ |B|·⌊δn⌋`, i.e. relative radius
   `δ/(1 − ℓ/|B|)` — for lines (`ℓ = 1`, `|B| = t₁`) exactly the paper's `δ/(1 − 1/t₁)`.
3. `card_family_le` — **the globally-close-curve list bound** (5.10's middle step): a
   finset of distinct codeword-curve value functions, all globally `D`-close to the tested
   stack at every seed, has size `≤ L`, given the `(D, L)`-list bound and
   `q > (L+1)·L·ℓ` (pairwise collisions occupy `≤ ℓ·(L+1)·L` seeds; at a collision-free
   seed the `L+1` values would be distinct codewords in one radius-`D` ball).  For lines
   this is the paper's `q > (L+1)²` step, with the slightly finer ordered-pair count.
4. `curveDecodable_of_marked_listDecodable` — **the peeling theorem = the [JLR26]
   Lemma 5.10 core, curve form**: `MarkedCurveDecodable (a, t₁)` stitching (`t₁ > ℓ`)
   + list bound `L` at any radius `D` with `t₁·⌊δn⌋ ≤ (t₁−ℓ)·D` + `q > (L+1)·L·ℓ` give,
   for EVERY `t₂`, `(ℓ, δ, (t₂−1)·L + a, t₂)`-curve-decodability.  The proof replaces the
   paper's sequential stage-by-stage recursion by the equivalent one-shot accounting: the
   family `𝒢` of ALL curve value functions with `≥ t₁` exact matches on the close set
   (every stage curve of the paper's recursion lands in `𝒢`) has `|𝒢| ≤ L` by (2)+(3); the
   `𝒢`-unexplained residue has `< a` seeds (one more stitch would fire into `𝒢`); and if
   every codeword curve explains `≤ t₂−1` close seeds then
   `|close| ≤ L·(t₂−1) + (a−1)` — the exact bound the paper's recursion terminates with,
   without process bookkeeping.
5. `curveListSizeLe_of_marked_listDecodable` — **the cover form**: the same hypotheses give
   `CurveListSizeLe C ℓ δ (L + (a−1))` (each explained seed keeps its `𝒢`-curve, each of
   the `< a` residual seeds keeps its own constant curve), feeding the in-tree one-level
   engine `curveDecodable_of_curveListSize`.  The direct form (4) is strictly sharper:
   close-set threshold `(t₂−1)·L + a` versus the one-level engine's `(L+a−1)·t₂`.
6. `curveDecodable_of_listDecodable` — the free-stitching corollary: instantiating the
   stitching with the [Jo26] Lemma 5.2 interpolation regime (`a = t₁ = ℓ+1`, in-tree
   `markedCurveDecodable_interpolation`) leaves list-decodability at radius `(ℓ+1)·⌊δn⌋`
   as the ONLY hypothesis: `(ℓ, δ, (t₂−1)·L + ℓ + 1, t₂)`-curve-decodability for every
   `t₂`, whenever `q > (L+1)·L·ℓ`.
7. `rs_curveDecodable_peeling` — concrete family instance: explicit plain Reed–Solomon in
   the double-UDR window `2·(ℓ+1)·⌊δn⌋ < n − (k−1)` is `(ℓ, δ, t₂ + ℓ, t₂)`-curve-decodable
   for every `t₂ ≥ 1` (`L = 1`), for `q > 2ℓ`.

**Honest scope.**  Everything here is unconditional and axiom-clean; the list-decodability
input is an explicit hypothesis exactly as in [JLR26] Lemma 5.10 (their Definition 5.9),
not a socket.  This does NOT touch the plain-RS prize core: for plain RS in the δ* window
the required list bound at radius `≈ δ/(1−ℓ/t₁)` IS the open list-size wall
(`RSCurveListSizeResidual` / BCHKS Conj 1.12).  For folded RS the remaining open in-tree
steps toward [JLR26] Thm 5.12 are the capacity list-decodability input (PRUNE) and the
τ-subspace-design stitching instantiation with the pruned `poly(1/η)` count ([JLR26]
Lemma 5.7 + §5.6 parameter choices); this brick delivers the 5.10 peeling ENGINE those
inputs plug into, composable with the in-tree Theorem 3.3 engine down to MCA.

## References
* [JLR26] Jeronimo–Liu–Rajpal, arXiv 2601.10047, §5.3–5.4 (Def 5.6, Lemma 5.4, Def 5.9,
  Lemma 5.10; peeling proof pp. 18–19).  Issue #334, class B2.
* [GG25] Z. Guo, V. Guruswami, ePrint 2025/2054 (ECCC TR25-166), Def 3.1, Thm 3.3.
* [Jo26] S. Jo, ePrint 2026/891, Def 2.7, Def 5.1, Lemma 5.2.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Finset Code Polynomial
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.ZW17RecursivePeeling

open _root_.ProximityGap _root_.ProximityGap.GG25Lemma32

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ### Substrate copied from `Frontier/_W17CurveDecodStitching.lean`

The stitching brick `_W17CurveDecodStitching.lean` is a new file with no olean, so it cannot
be imported under lock-free verification.  The three lemmas below are copied VERBATIM from
it (namespace `ProximityGap.W17Stitching`), with provenance noted per lemma; they are
`private` here so that the eventual consolidation pass can dedupe against the W17 originals
without a public-name conflict. -/

-- PROVENANCE: verbatim copy of `ProximityGap.W17Stitching.sum_basis_eval_mul_pow`
-- (`Frontier/_W17CurveDecodStitching.lean`).
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

-- PROVENANCE: verbatim copy of `ProximityGap.W17Stitching.basis_eval_eq_fin_sum`
-- (`Frontier/_W17CurveDecodStitching.lean`).
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

-- PROVENANCE: verbatim copy of `ProximityGap.W17Stitching.lagrangeCurve_comb_eq_of_agree`
-- (`Frontier/_W17CurveDecodStitching.lean`), demoted to `private`.
/-- **The stitching identity ([JLR26] 5.7 mechanism, coordinate form).**  If the `ℓ+1`
interpolated values agree with the tested curve at coordinate `i` (`f α i = comb u α i` for all
`α ∈ B`), then the Lagrange codeword-curve through them coincides with the tested curve at `i`
**for every seed `γ`**: two degree-`≤ ℓ` `A`-valued polynomials agreeing at the `ℓ+1` points of
`B` are equal. -/
private theorem lagrangeCurve_comb_eq_of_agree {B : Finset F} {ℓ : ℕ} (hB : B.card = ℓ + 1)
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

-- PROVENANCE: verbatim copy of `ProximityGap.W17Stitching.close_seed_dist_le`
-- (`Frontier/_W17CurveDecodStitching.lean`), demoted to `private`.
/-- Every close seed has integer distance `≤ ⌊δn⌋` between its codeword and the tested curve. -/
private theorem close_seed_dist_le {δ : ℝ≥0} {ℓ : ℕ}
    {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A} {α : F}
    (hα : α ∈ curveCloseSet δ u f) :
    hammingDist (f α) (comb u α) ≤ ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ := by
  simp only [curveCloseSet, Finset.mem_filter, Finset.mem_univ, true_and] at hα
  have h2 := hammingDist_le_floor_of_relHam_le hα
  calc hammingDist (f α) (comb u α)
      = hammingDist (comb u α) (f α) := hammingDist_comm _ _
    _ ≤ ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ := h2

/-! ### Curve values, rigidity, and the collision cap -/

/-- Curve values of a codeword stack are codewords (`F`-linearity of the code). -/
theorem comb_mem (M : Submodule F (ι → A)) {ℓ : ℕ} {cs : Fin (ℓ + 1) → ι → A}
    (hcs : ∀ j, cs j ∈ M) (β : F) : comb cs β ∈ M := by
  have hrw : comb cs β = ∑ j : Fin (ℓ + 1), β ^ (j : ℕ) • cs j := by
    funext i
    rw [comb, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => rfl
  rw [hrw]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcs j)

/-- **Curve value rigidity.**  Two degree-`≤ ℓ` curve stacks whose value functions agree at
`ℓ + 1` distinct seeds agree at EVERY seed (module-valued Lagrange uniqueness, coordinate by
coordinate through the stitching identity). -/
theorem comb_eq_comb_of_agree {ℓ : ℕ} {cs cs' : Fin (ℓ + 1) → ι → A} {B : Finset F}
    (hB : B.card = ℓ + 1) (hagree : ∀ β ∈ B, comb cs β = comb cs' β) (γ : F) :
    comb cs γ = comb cs' γ := by
  funext i
  have h1 : comb (fun j : Fin (ℓ + 1) => lagrangeCurve B (comb cs) (j : ℕ)) γ i
      = comb cs' γ i :=
    lagrangeCurve_comb_eq_of_agree hB (fun α hα => by rw [hagree α hα]) γ
  have h2 : comb (fun j : Fin (ℓ + 1) => lagrangeCurve B (comb cs) (j : ℕ)) γ i
      = comb cs γ i :=
    lagrangeCurve_comb_eq_of_agree hB (fun α _ => rfl) γ
  rw [← h2, h1]

/-- **The collision cap.**  Value-distinct degree-`≤ ℓ` curves collide at `≤ ℓ` seeds
(the [JLR26] 5.10 "at most one collision parameter per pair of lines" step, at every curve
degree). -/
theorem card_agree_le_of_ne {ℓ : ℕ} {cs cs' : Fin (ℓ + 1) → ι → A}
    (hne : (comb cs : F → ι → A) ≠ comb cs') :
    (univ.filter fun β : F => comb cs β = comb cs' β).card ≤ ℓ := by
  by_contra hcard
  push_neg at hcard
  have hcard' : ℓ + 1 ≤ (univ.filter fun β : F => comb cs β = comb cs' β).card := hcard
  obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hcard'
  have hagree : ∀ β ∈ B, comb cs β = comb cs' β := fun β hβ =>
    (Finset.mem_filter.mp (hBsub hβ)).2
  exact hne (funext fun γ => comb_eq_comb_of_agree hBcard hagree γ)

/-! ### The spread ([JLR26] Lemma 5.4, exact-match form) -/

/-- **The spread.**  If a codeword-curve exactly matches `f` on a set `B` of more than `ℓ`
close seeds, then at EVERY seed `γ` it is close to the tested stack:
`(|B| − ℓ)·Δ(comb u γ, comb cs γ) ≤ |B|·⌊δn⌋`.  (At a disagreement coordinate `i` of seed
`γ`, the two curves' coordinate-`i` polynomials differ, so they agree at `≤ ℓ` of the seeds
of `B` (rigidity); at each of the other `≥ |B| − ℓ` seeds, coordinate `i` is a per-seed
error coordinate; double counting against the total error mass `≤ |B|·⌊δn⌋` bounds the
number of disagreement coordinates.) -/
theorem spread_mul_le {δ : ℝ≥0} {ℓ : ℕ}
    {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A} {cs : Fin (ℓ + 1) → ι → A} {B : Finset F}
    (hBsub : B ⊆ curveCloseSet δ u f) (hmatch : ∀ α ∈ B, f α = comb cs α)
    (hBcard : ℓ < B.card) (γ : F) :
    (B.card - ℓ) * hammingDist (comb u γ) (comb cs γ)
      ≤ B.card * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ := by
  classical
  -- at each disagreement coordinate, the two curves agree at ≤ ℓ seeds of B (rigidity)
  have hroot : ∀ i : ι, comb u γ i ≠ comb cs γ i →
      (B.filter (fun α => comb cs α i = comb u α i)).card ≤ ℓ := by
    intro i hi
    by_contra hgt
    push_neg at hgt
    have hgt' : ℓ + 1 ≤ (B.filter (fun α => comb cs α i = comb u α i)).card := hgt
    obtain ⟨B₀, hB₀sub, hB₀card⟩ := Finset.exists_subset_card_eq hgt'
    have hagree : ∀ α ∈ B₀, comb cs α i = comb u α i := fun α hα =>
      (Finset.mem_filter.mp (hB₀sub hα)).2
    have h1 : comb (fun j : Fin (ℓ + 1) => lagrangeCurve B₀ (comb cs) (j : ℕ)) γ i
        = comb u γ i := lagrangeCurve_comb_eq_of_agree hB₀card hagree γ
    have h2 : comb (fun j : Fin (ℓ + 1) => lagrangeCurve B₀ (comb cs) (j : ℕ)) γ i
        = comb cs γ i := lagrangeCurve_comb_eq_of_agree hB₀card (fun α _ => rfl) γ
    exact hi (by rw [← h1, h2])
  -- hence each disagreement coordinate is an error coordinate for ≥ |B| − ℓ seeds of B
  have hlow : ∀ i ∈ (univ.filter fun i : ι => comb u γ i ≠ comb cs γ i),
      B.card - ℓ ≤ (B.filter (fun α => comb cs α i ≠ comb u α i)).card := by
    intro i hi
    have hii : comb u γ i ≠ comb cs γ i := (Finset.mem_filter.mp hi).2
    have hroot_i := hroot i hii
    have hunion : B ⊆ B.filter (fun α => comb cs α i = comb u α i) ∪
        B.filter (fun α => comb cs α i ≠ comb u α i) := by
      intro α hα
      by_cases hcase : comb cs α i = comb u α i
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hα, hcase⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hα, hcase⟩)
    have hcards := le_trans (Finset.card_le_card hunion) (Finset.card_union_le _ _)
    omega
  -- the per-seed error mass over B is ≤ ⌊δn⌋ per seed (closeness + exact matching)
  have hmass : ∀ α ∈ B,
      ((univ.filter fun i : ι => comb u γ i ≠ comb cs γ i).filter
        (fun i => comb cs α i ≠ comb u α i)).card
      ≤ ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ := by
    intro α hα
    have hsub : (univ.filter fun i : ι => comb u γ i ≠ comb cs γ i).filter
        (fun i => comb cs α i ≠ comb u α i)
        ⊆ univ.filter (fun i : ι => f α i ≠ comb u α i) := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ i, ?_⟩
      rw [hmatch α hα]
      exact hi.2
    refine le_trans (Finset.card_le_card hsub) ?_
    exact close_seed_dist_le (hBsub hα)
  -- double count the incidences {(i, α) : i a disagreement coordinate, α an error seed}
  have hdc : hammingDist (comb u γ) (comb cs γ)
      = (univ.filter fun i : ι => comb u γ i ≠ comb cs γ i).card := rfl
  have hswap : ∑ i ∈ (univ.filter fun i : ι => comb u γ i ≠ comb cs γ i),
        (B.filter (fun α => comb cs α i ≠ comb u α i)).card
      = ∑ α ∈ B, ((univ.filter fun i : ι => comb u γ i ≠ comb cs γ i).filter
        (fun i => comb cs α i ≠ comb u α i)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  calc (B.card - ℓ) * hammingDist (comb u γ) (comb cs γ)
      = ∑ _i ∈ (univ.filter fun i : ι => comb u γ i ≠ comb cs γ i), (B.card - ℓ) := by
        rw [Finset.sum_const, smul_eq_mul, ← hdc]
        ring
    _ ≤ ∑ i ∈ (univ.filter fun i : ι => comb u γ i ≠ comb cs γ i),
          (B.filter (fun α => comb cs α i ≠ comb u α i)).card :=
        Finset.sum_le_sum hlow
    _ = ∑ α ∈ B, ((univ.filter fun i : ι => comb u γ i ≠ comb cs γ i).filter
          (fun i => comb cs α i ≠ comb u α i)).card := hswap
    _ ≤ ∑ _α ∈ B, ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ := Finset.sum_le_sum hmass
    _ = B.card * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ := by
        rw [Finset.sum_const, smul_eq_mul]

/-! ### The globally-close-curve list bound ([JLR26] 5.10, middle step) -/

/-- **The globally-close-curve list bound.**  A finset `𝒢` of (distinct) codeword-curve value
functions, all globally `D`-close to the tested stack at every seed, has `|𝒢| ≤ L`, given the
`(D, L)`-list bound and `q > (L+1)·L·ℓ`: pairwise collisions of value-distinct curves occupy
`≤ ℓ·(L+1)·L` seeds ([JLR26] 5.10 "at most one collision parameter per pair", at every curve
degree via `card_agree_le_of_ne`), so a collision-free seed `β` exists, and there the `L+1`
values of any `(L+1)`-subfamily would be distinct codewords in the radius-`D` ball around
`comb u β`. -/
theorem card_family_le (M : Submodule F (ι → A)) {ℓ L D : ℕ}
    {u : Fin (ℓ + 1) → ι → A} (𝒢 : Finset (F → ι → A))
    (hcurve : ∀ v ∈ 𝒢, ∃ cs : Fin (ℓ + 1) → ι → A, (∀ j, cs j ∈ M) ∧ v = comb cs)
    (hclose : ∀ v ∈ 𝒢, ∀ γ : F, hammingDist (comb u γ) (v γ) ≤ D)
    (hlist : ∀ y : ι → A, ∀ S : Finset (ι → A),
      (∀ c ∈ S, c ∈ M ∧ hammingDist y c ≤ D) → S.card ≤ L)
    (hq : (L + 1) * L * ℓ < Fintype.card F) :
    𝒢.card ≤ L := by
  classical
  by_contra hgt
  push_neg at hgt
  have hgt' : L + 1 ≤ 𝒢.card := hgt
  obtain ⟨𝒢', h𝒢'sub, h𝒢'card⟩ := Finset.exists_subset_card_eq hgt'
  -- the collision parameters
  set Bad : Finset F := univ.filter
    (fun β => ∃ v ∈ 𝒢', ∃ v' ∈ 𝒢', v ≠ v' ∧ v β = v' β) with hBad
  -- each ordered pair of distinct value functions collides at ≤ ℓ seeds
  have hpair : ∀ p ∈ 𝒢'.offDiag, (univ.filter fun β : F => p.1 β = p.2 β).card ≤ ℓ := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    obtain ⟨hp1, hp2, hpne⟩ := hp
    obtain ⟨cs, hcs, hcs_eq⟩ := hcurve p.1 (h𝒢'sub hp1)
    obtain ⟨cs', hcs', hcs'_eq⟩ := hcurve p.2 (h𝒢'sub hp2)
    rw [hcs_eq, hcs'_eq] at hpne ⊢
    exact card_agree_le_of_ne hpne
  have hBadcard : Bad.card ≤ (L + 1) * L * ℓ := by
    have hsub : Bad ⊆ 𝒢'.offDiag.biUnion
        (fun p => univ.filter fun β : F => p.1 β = p.2 β) := by
      intro β hβ
      rw [hBad, Finset.mem_filter] at hβ
      obtain ⟨-, v, hv, v', hv', hne, heq⟩ := hβ
      exact Finset.mem_biUnion.mpr ⟨(v, v'), Finset.mem_offDiag.mpr ⟨hv, hv', hne⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ β, heq⟩⟩
    calc Bad.card
        ≤ (𝒢'.offDiag.biUnion (fun p => univ.filter fun β : F => p.1 β = p.2 β)).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ p ∈ 𝒢'.offDiag, (univ.filter fun β : F => p.1 β = p.2 β).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ 𝒢'.offDiag, ℓ := Finset.sum_le_sum hpair
      _ = 𝒢'.offDiag.card * ℓ := by rw [Finset.sum_const, smul_eq_mul]
      _ = (L + 1) * L * ℓ := by
          rw [Finset.offDiag_card, h𝒢'card]
          congr 1
          have h2 : (L + 1) * (L + 1) = (L + 1) * L + (L + 1) := by ring
          omega
  -- a collision-free seed exists
  have hβex : ∃ β : F, β ∉ Bad := by
    by_contra hall
    push_neg at hall
    have hsub : (univ : Finset F) ⊆ Bad := fun β _ => hall β
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_univ] at hcard
    omega
  obtain ⟨β, hβ⟩ := hβex
  -- evaluation at β is injective on 𝒢'
  have hinj : Set.InjOn (fun v : F → ι → A => v β) ↑𝒢' := by
    intro v hv v' hv' heq
    by_contra hne
    refine hβ ?_
    rw [hBad, Finset.mem_filter]
    exact ⟨Finset.mem_univ β, v, Finset.mem_coe.mp hv, v', Finset.mem_coe.mp hv', hne, heq⟩
  have himg := Finset.card_image_of_injOn hinj
  -- the L+1 distinct values at β are codewords in the radius-D ball around comb u β
  have hmem : ∀ c ∈ 𝒢'.image (fun v => v β), c ∈ M ∧ hammingDist (comb u β) c ≤ D := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨v, hv, rfl⟩ := hc
    obtain ⟨cs, hcs, rfl⟩ := hcurve v (h𝒢'sub hv)
    exact ⟨comb_mem M hcs β, hclose (comb cs) (h𝒢'sub hv) β⟩
  have hfinal := hlist (comb u β) (𝒢'.image (fun v => v β)) hmem
  rw [himg, h𝒢'card] at hfinal
  omega

/-! ### The peeled cover: ≤ L exactly-explaining curves + a residue of < a seeds -/

/-- **The peeled cover (the one-shot form of the [JLR26] 5.10 recursion).**  Under stitching
(`MarkedCurveDecodable (a, t₁)`, `t₁ > ℓ`), a list bound `L` at radius `D` with
`t₁·⌊δn⌋ ≤ (t₁−ℓ)·D`, and `q > (L+1)·L·ℓ`: for every instance `(u, f)` the family `𝒢` of ALL
codeword-curve value functions with `≥ t₁` exact matches on the close set satisfies `|𝒢| ≤ L`
(each member spreads to a globally `D`-close curve through any `t₁` seeds of its fiber), and
the `𝒢`-unexplained residue of the close set has `< a` seeds (one more stitch would fire, and
its curve would land in `𝒢`).  Every stage curve of the paper's sequential peeling lies in
`𝒢`, so this is the recursion's full transcript, obtained without process bookkeeping. -/
private theorem exists_goodFamily (M : Submodule F (ι → A)) {ℓ : ℕ} {δ : ℝ≥0}
    {a t₁ L D : ℕ}
    (hstitch : MarkedCurveDecodable (F := F) (M : Set (ι → A)) ℓ δ a t₁)
    (ht₁ : ℓ < t₁)
    (hD : t₁ * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ ≤ (t₁ - ℓ) * D)
    (hlist : ∀ y : ι → A, ∀ S : Finset (ι → A),
      (∀ c ∈ S, c ∈ M ∧ hammingDist y c ≤ D) → S.card ≤ L)
    (hq : (L + 1) * L * ℓ < Fintype.card F)
    (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A) (hf : ∀ α, f α ∈ M) :
    ∃ 𝒢 : Finset (F → ι → A),
      𝒢.card ≤ L ∧
      (∀ v ∈ 𝒢, ∃ cs : Fin (ℓ + 1) → ι → A, (∀ j, cs j ∈ M) ∧ v = comb cs) ∧
      ((curveCloseSet δ u f).filter (fun α => ¬ ∃ v ∈ 𝒢, f α = v α)).card < a := by
  classical
  -- the family of ALL codeword-curve value functions with ≥ t₁ exact matches on the close set
  set 𝒢 : Finset (F → ι → A) := univ.filter
    (fun v => (∃ cs : Fin (ℓ + 1) → ι → A, (∀ j, cs j ∈ M) ∧ v = comb cs) ∧
      t₁ ≤ ((curveCloseSet δ u f).filter (fun α => f α = v α)).card) with h𝒢
  have h𝒢curve : ∀ v ∈ 𝒢, ∃ cs : Fin (ℓ + 1) → ι → A, (∀ j, cs j ∈ M) ∧ v = comb cs := by
    intro v hv
    rw [h𝒢, Finset.mem_filter] at hv
    exact hv.2.1
  have h𝒢fiber : ∀ v ∈ 𝒢,
      t₁ ≤ ((curveCloseSet δ u f).filter (fun α => f α = v α)).card := by
    intro v hv
    rw [h𝒢, Finset.mem_filter] at hv
    exact hv.2.2
  -- the spread: every family member is globally D-close to the tested stack
  have h𝒢close : ∀ v ∈ 𝒢, ∀ γ : F, hammingDist (comb u γ) (v γ) ≤ D := by
    intro v hv γ
    obtain ⟨cs, hcs, rfl⟩ := h𝒢curve v hv
    have hfib := h𝒢fiber (comb cs) hv
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hfib
    have hBclose : B ⊆ curveCloseSet δ u f := hBsub.trans (Finset.filter_subset _ _)
    have hmatch : ∀ α ∈ B, f α = comb cs α := fun α hα =>
      (Finset.mem_filter.mp (hBsub hα)).2
    have hspread := spread_mul_le hBclose hmatch (hBcard.symm ▸ ht₁) γ
    have hpos : 0 < t₁ - ℓ := by omega
    have hchain : (t₁ - ℓ) * hammingDist (comb u γ) (comb cs γ) ≤ (t₁ - ℓ) * D := by
      calc (t₁ - ℓ) * hammingDist (comb u γ) (comb cs γ)
          = (B.card - ℓ) * hammingDist (comb u γ) (comb cs γ) := by rw [hBcard]
        _ ≤ B.card * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ := hspread
        _ = t₁ * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ := by rw [hBcard]
        _ ≤ (t₁ - ℓ) * D := hD
    exact Nat.le_of_mul_le_mul_left hchain hpos
  have h𝒢card : 𝒢.card ≤ L := card_family_le M 𝒢 h𝒢curve h𝒢close hlist hq
  -- the unexplained residue is < a: otherwise one more stitch fires into 𝒢
  have hres : ((curveCloseSet δ u f).filter (fun α => ¬ ∃ v ∈ 𝒢, f α = v α)).card < a := by
    -- (`le_of_not_lt`, not `push_neg`: the latter would rewrite the `¬∃` inside the filter)
    by_contra hge
    have hge' : a ≤ ((curveCloseSet δ u f).filter
        (fun α => ¬ ∃ v ∈ 𝒢, f α = v α)).card := not_lt.mp hge
    obtain ⟨A₀, hA₀sub, hA₀card⟩ := Finset.exists_subset_card_eq hge'
    have hA₀close : ∀ α ∈ A₀,
        (δᵣ( (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j i), f α ) : ℝ≥0) ≤ δ := by
      intro α hα
      have hαS : α ∈ curveCloseSet δ u f := (Finset.filter_subset _ _) (hA₀sub hα)
      simpa [curveCloseSet] using hαS
    obtain ⟨cs, hcs, hcount⟩ := hstitch u f hf A₀ hA₀card hA₀close
    -- the stitched curve's value function lies in 𝒢
    have hcount' : t₁ ≤ (A₀.filter (fun α => f α = comb cs α)).card := hcount
    have hv𝒢 : comb cs ∈ 𝒢 := by
      rw [h𝒢, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ⟨cs, hcs, rfl⟩, le_trans hcount' (Finset.card_le_card ?_)⟩
      intro α hα
      rw [Finset.mem_filter] at hα
      rw [Finset.mem_filter]
      exact ⟨(Finset.filter_subset _ _) (hA₀sub hα.1), hα.2⟩
    -- but its ≥ t₁ ≥ 1 matched seeds of A₀ were unexplained — contradiction
    have hne : (A₀.filter (fun α => f α = comb cs α)).Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨α, hα⟩ := hne
    rw [Finset.mem_filter] at hα
    have hαres := hA₀sub hα.1
    rw [Finset.mem_filter] at hαres
    exact hαres.2 ⟨comb cs, hv𝒢, hα.2⟩
  exact ⟨𝒢, h𝒢card, h𝒢curve, hres⟩

/-! ### The peeling theorem ([JLR26] Lemma 5.10 core, curve form) -/

/-- **The recursive multi-curve peeling theorem ([JLR26] Lemma 5.10 core, at every curve
degree).**  If `M` is `(a, t₁)`-marked-curve-decodable at `(ℓ, δ)` ("curve stitching",
`t₁ > ℓ`), and every radius-`D` ball contains `≤ L` codewords where `t₁·⌊δn⌋ ≤ (t₁−ℓ)·D`
(for lines `ℓ = 1` this is the paper's list-decodability at `δ/(1−1/t₁)`), and
`q > (L+1)·L·ℓ`, then for EVERY `t₂`:

  `M` is `(ℓ, δ, (t₂−1)·L + a, t₂)`-curve-decodable —

a close set of `≥ (t₂−1)·L + a` seeds forces ONE codeword curve to exactly explain `≥ t₂` of
them.  This is the additive-threshold peeling bound `ε = ((t₂−1)L + a)/q` of [JLR26] 5.10;
compare the in-tree one-level pigeonhole (`curveDecodable_of_curveListSize`), which from a
list-size `m` needs the multiplicative threshold `m·t₂`. -/
theorem curveDecodable_of_marked_listDecodable (M : Submodule F (ι → A)) {ℓ : ℕ} {δ : ℝ≥0}
    {a t₁ L D : ℕ}
    (hstitch : MarkedCurveDecodable (F := F) (M : Set (ι → A)) ℓ δ a t₁)
    (ht₁ : ℓ < t₁)
    (hD : t₁ * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ ≤ (t₁ - ℓ) * D)
    (hlist : ∀ y : ι → A, ∀ S : Finset (ι → A),
      (∀ c ∈ S, c ∈ M ∧ hammingDist y c ≤ D) → S.card ≤ L)
    (hq : (L + 1) * L * ℓ < Fintype.card F) (t₂ : ℕ) :
    CurveDecodable (F := F) (M : Set (ι → A)) ℓ δ ((t₂ - 1) * L + a) t₂ := by
  classical
  intro u f hf hclose
  by_contra hno
  push_neg at hno
  obtain ⟨𝒢, h𝒢card, h𝒢curve, hres⟩ := exists_goodFamily M hstitch ht₁ hD hlist hq u f hf
  -- every 𝒢-fiber is ≤ t₂ − 1 (else the theorem's conclusion holds)
  have hfib_le : ∀ v ∈ 𝒢,
      ((curveCloseSet δ u f).filter (fun α => f α = v α)).card ≤ t₂ - 1 := by
    intro v hv
    obtain ⟨cs, hcs, rfl⟩ := h𝒢curve v hv
    have hlt : ((curveCloseSet δ u f).filter (fun α => f α = comb cs α)).card < t₂ :=
      hno cs hcs
    omega
  -- split the close set into the 𝒢-explained part and the residue
  have hsplit : curveCloseSet δ u f ⊆
      (curveCloseSet δ u f).filter (fun α => ∃ v ∈ 𝒢, f α = v α) ∪
      (curveCloseSet δ u f).filter (fun α => ¬ ∃ v ∈ 𝒢, f α = v α) := by
    intro α hα
    by_cases h : ∃ v ∈ 𝒢, f α = v α
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hα, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hα, h⟩)
  have hcard_le := le_trans (Finset.card_le_card hsplit) (Finset.card_union_le _ _)
  -- the explained part is covered by the ≤ L fibers, each ≤ t₂ − 1
  have hexp : ((curveCloseSet δ u f).filter (fun α => ∃ v ∈ 𝒢, f α = v α)).card
      ≤ ∑ v ∈ 𝒢, ((curveCloseSet δ u f).filter (fun α => f α = v α)).card := by
    refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
    intro α hα
    rw [Finset.mem_filter] at hα
    obtain ⟨hαS, v, hv, heq⟩ := hα
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_filter.mpr ⟨hαS, heq⟩⟩
  have hsum_le : ∑ v ∈ 𝒢, ((curveCloseSet δ u f).filter (fun α => f α = v α)).card
      ≤ L * (t₂ - 1) := by
    calc ∑ v ∈ 𝒢, ((curveCloseSet δ u f).filter (fun α => f α = v α)).card
        ≤ ∑ _v ∈ 𝒢, (t₂ - 1) := Finset.sum_le_sum hfib_le
      _ = 𝒢.card * (t₂ - 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ L * (t₂ - 1) := Nat.mul_le_mul h𝒢card le_rfl
  -- total: (t₂−1)L + a ≤ |close| ≤ L(t₂−1) + (a−1), contradiction
  have hcomm : (t₂ - 1) * L = L * (t₂ - 1) := Nat.mul_comm _ _
  omega

/-! ### The cover form: curve list-size L + (a − 1), feeding the in-tree engine -/

/-- The constant curve through a single value: `comb (Fin.cons w 0) α = w`. -/
private lemma comb_singleton {ℓ : ℕ} (w : ι → A) (α : F) :
    w = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) •
      (Fin.cons w (fun _ : Fin ℓ => (0 : ι → A)) : Fin (ℓ + 1) → ι → A) j i := by
  funext i
  rw [Fin.sum_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ]

/-- **The peeled cover as a curve list-size ([JLR26] 5.10, cover form).**  The peeling
hypotheses give `CurveListSizeLe M ℓ δ (L + (a − 1))`: each `𝒢`-explained close seed keeps
its exactly-explaining family curve (`≤ L` of them), and each of the `< a` residual seeds
keeps its own constant curve.  This feeds the in-tree one-level pigeonhole engine
(`curveDecodable_of_curveListSize`); the direct peeling theorem
`curveDecodable_of_marked_listDecodable` is strictly sharper (additive vs multiplicative
threshold). -/
theorem curveListSizeLe_of_marked_listDecodable (M : Submodule F (ι → A)) {ℓ : ℕ} {δ : ℝ≥0}
    {a t₁ L D : ℕ}
    (hstitch : MarkedCurveDecodable (F := F) (M : Set (ι → A)) ℓ δ a t₁)
    (ht₁ : ℓ < t₁)
    (hD : t₁ * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ ≤ (t₁ - ℓ) * D)
    (hlist : ∀ y : ι → A, ∀ S : Finset (ι → A),
      (∀ c ∈ S, c ∈ M ∧ hammingDist y c ≤ D) → S.card ≤ L)
    (hq : (L + 1) * L * ℓ < Fintype.card F) :
    CurveListSizeLe (F := F) (M : Set (ι → A)) ℓ δ (L + (a - 1)) := by
  classical
  intro u f hf
  obtain ⟨𝒢, h𝒢card, h𝒢curve, hres⟩ := exists_goodFamily M hstitch ht₁ hD hlist hq u f hf
  -- a concrete stack for each family member
  set stackOf : (F → ι → A) → Fin (ℓ + 1) → ι → A := fun v =>
    if hv : ∃ cs : Fin (ℓ + 1) → ι → A, (∀ j, cs j ∈ M) ∧ v = comb cs
    then Classical.choose hv else fun _ _ => 0
    with hstackOf
  have hstack_mem : ∀ v ∈ 𝒢, ∀ j, stackOf v j ∈ M := by
    intro v hv j
    have hex := h𝒢curve v hv
    simp only [hstackOf, dif_pos hex]
    exact (Classical.choose_spec hex).1 j
  have hstack_eq : ∀ v ∈ 𝒢, v = comb (stackOf v) := by
    intro v hv
    have hex := h𝒢curve v hv
    simp only [hstackOf, dif_pos hex]
    exact (Classical.choose_spec hex).2
  -- the per-seed assignment: the explaining family curve, else the constant curve
  set pick : F → Fin (ℓ + 1) → ι → A := fun α =>
    if h : ∃ v ∈ 𝒢, f α = v α then stackOf (Classical.choose h)
    else Fin.cons (f α) (fun _ : Fin ℓ => (0 : ι → A))
    with hpick
  refine ⟨{ chooseCurve := pick
            mem_code := ?_
            passes_through := ?_ }, ?_⟩
  · -- every chosen row is a codeword
    intro α j
    simp only [hpick]
    by_cases h : ∃ v ∈ 𝒢, f α = v α
    · simp only [dif_pos h]
      exact hstack_mem _ (Classical.choose_spec h).1 j
    · simp only [dif_neg h]
      refine Fin.cases ?_ ?_ j
      · simpa [Fin.cons_zero] using hf α
      · intro j'
        simp only [Fin.cons_succ]
        exact M.zero_mem
  · -- the chosen curve passes through f α at every close seed
    intro α hα
    simp only [hpick]
    by_cases h : ∃ v ∈ 𝒢, f α = v α
    · simp only [dif_pos h]
      have h1 : f α = (Classical.choose h) α := (Classical.choose_spec h).2
      have h2 : Classical.choose h = comb (stackOf (Classical.choose h)) :=
        hstack_eq _ (Classical.choose_spec h).1
      exact h1.trans (congrFun h2 α)
    · simp only [dif_neg h]
      exact comb_singleton (f α) α
  · -- image count: ≤ L family stacks + ≤ a − 1 residual constant curves
    show ((curveCloseSet δ u f).image pick).card ≤ L + (a - 1)
    have himgsub : (curveCloseSet δ u f).image pick ⊆
        ((curveCloseSet δ u f).filter (fun α => ∃ v ∈ 𝒢, f α = v α)).image pick ∪
        ((curveCloseSet δ u f).filter (fun α => ¬ ∃ v ∈ 𝒢, f α = v α)).image pick := by
      intro c hc
      rw [Finset.mem_image] at hc
      obtain ⟨α, hα, rfl⟩ := hc
      by_cases h : ∃ v ∈ 𝒢, f α = v α
      · exact Finset.mem_union_left _
          (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hα, h⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hα, h⟩))
    have h1 : (((curveCloseSet δ u f).filter (fun α => ∃ v ∈ 𝒢, f α = v α)).image pick).card
        ≤ L := by
      refine le_trans (Finset.card_le_card ?_)
        (le_trans (Finset.card_image_le (f := stackOf) (s := 𝒢)) h𝒢card)
      intro c hc
      rw [Finset.mem_image] at hc
      obtain ⟨α, hα, rfl⟩ := hc
      have hαexp := (Finset.mem_filter.mp hα).2
      rw [Finset.mem_image]
      refine ⟨Classical.choose hαexp, (Classical.choose_spec hαexp).1, ?_⟩
      simp only [hpick]
      rw [dif_pos hαexp]
    have h2 : (((curveCloseSet δ u f).filter
        (fun α => ¬ ∃ v ∈ 𝒢, f α = v α)).image pick).card ≤ a - 1 := by
      refine le_trans Finset.card_image_le ?_
      omega
    have hunion := le_trans (Finset.card_le_card himgsub) (Finset.card_union_le _ _)
    omega

/-! ### The free-stitching corollary: list-decodability alone -/

/-- **Peeling with interpolation stitching ([JLR26] 5.10 over the [Jo26] Lemma 5.2 trivial
regime).**  For an `F`-submodule code, the interpolation regime provides
`(a, t₁) = (ℓ+1, ℓ+1)` stitching for FREE, so the ONLY hypothesis left is the list bound at
radius `(ℓ+1)·⌊δn⌋`: any `F`-linear code whose radius-`(ℓ+1)⌊δn⌋` balls hold `≤ L` codewords
(with `q > (L+1)·L·ℓ`) is `(ℓ, δ, (t₂−1)·L + ℓ + 1, t₂)`-curve-decodable for every `t₂`. -/
theorem curveDecodable_of_listDecodable (M : Submodule F (ι → A)) (ℓ : ℕ) (δ : ℝ≥0) {L : ℕ}
    (hlist : ∀ y : ι → A, ∀ S : Finset (ι → A),
      (∀ c ∈ S, c ∈ M ∧ hammingDist y c ≤ (ℓ + 1) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊) →
      S.card ≤ L)
    (hq : (L + 1) * L * ℓ < Fintype.card F) (t₂ : ℕ) :
    CurveDecodable (F := F) (M : Set (ι → A)) ℓ δ ((t₂ - 1) * L + (ℓ + 1)) t₂ := by
  refine curveDecodable_of_marked_listDecodable M
    (markedCurveDecodable_interpolation M ℓ δ (le_refl (ℓ + 1)) (le_refl (ℓ + 1)))
    (by omega) ?_ hlist hq t₂
  have h1 : ℓ + 1 - ℓ = 1 := by omega
  rw [h1, one_mul]

/-! ### Concrete family instance: explicit plain RS in the double-UDR window -/

/-- **Explicit plain RS peeling instance.**  For any embedded evaluation domain and degree
bound `k ≥ 1`, in the double-UDR window `2·(ℓ+1)·⌊δn⌋ < n − (k−1)` the radius-`(ℓ+1)⌊δn⌋`
balls hold at most one codeword (`L = 1`), so plain RS is `(ℓ, δ, t₂ + ℓ, t₂)`-curve-decodable
for every `t₂ ≥ 1`, whenever `q > 2ℓ`: a close set of `t₂ + ℓ` seeds forces one curve to
explain all but `ℓ` of them.  (The prize window `δ > 1−√ρ` is NOT touched: there the needed
ball bound is the open list-size wall — see the module docstring.) -/
theorem rs_curveDecodable_peeling (domain : ι ↪ F) (k : ℕ) [NeZero k] (ℓ : ℕ) (δ : ℝ≥0)
    (h : 2 * ((ℓ + 1) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊) < Fintype.card ι - (k - 1))
    (hq : 2 * ℓ < Fintype.card F) {t₂ : ℕ} (ht₂ : 1 ≤ t₂) :
    CurveDecodable (F := F)
      ((ReedSolomon.code domain k : Submodule F (ι → F)) : Set (ι → F)) ℓ δ (t₂ + ℓ) t₂ := by
  have hlist : ∀ y : ι → F, ∀ S : Finset (ι → F),
      (∀ c ∈ S, c ∈ ReedSolomon.code domain k ∧
        hammingDist y c ≤ (ℓ + 1) * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊) → S.card ≤ 1 := by
    intro y S hS
    refine Finset.card_le_one.mpr (fun c hc c' hc' => ?_)
    obtain ⟨hcM, hcd⟩ := hS c hc
    obtain ⟨hcM', hcd'⟩ := hS c' hc'
    by_contra hne
    have hd := ArkLib.CS25.rsCodeFinset_hammingDist_ge domain k c c'
      ((ArkLib.CS25.mem_rsCodeFinset domain k c).mpr hcM)
      ((ArkLib.CS25.mem_rsCodeFinset domain k c').mpr hcM') hne
    have htri : hammingDist c c' ≤ hammingDist c y + hammingDist y c' :=
      hammingDist_triangle _ _ _
    have hcomm : hammingDist c y = hammingDist y c := hammingDist_comm _ _
    omega
  have hbase := curveDecodable_of_listDecodable (ReedSolomon.code domain k) ℓ δ
    (L := 1) hlist (by omega) t₂
  exact hbase.mono (by omega) le_rfl

end ArkLib.ProximityGap.Frontier.ZW17RecursivePeeling

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ArkLib.ProximityGap.Frontier.ZW17RecursivePeeling.comb_mem
#print axioms ArkLib.ProximityGap.Frontier.ZW17RecursivePeeling.comb_eq_comb_of_agree
#print axioms ArkLib.ProximityGap.Frontier.ZW17RecursivePeeling.card_agree_le_of_ne
#print axioms ArkLib.ProximityGap.Frontier.ZW17RecursivePeeling.spread_mul_le
#print axioms ArkLib.ProximityGap.Frontier.ZW17RecursivePeeling.card_family_le
#print axioms ArkLib.ProximityGap.Frontier.ZW17RecursivePeeling.curveDecodable_of_marked_listDecodable
#print axioms ArkLib.ProximityGap.Frontier.ZW17RecursivePeeling.curveListSizeLe_of_marked_listDecodable
#print axioms ArkLib.ProximityGap.Frontier.ZW17RecursivePeeling.curveDecodable_of_listDecodable
#print axioms ArkLib.ProximityGap.Frontier.ZW17RecursivePeeling.rs_curveDecodable_peeling

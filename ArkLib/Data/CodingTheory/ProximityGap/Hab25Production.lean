/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25BranchDichotomy
import Mathlib.LinearAlgebra.Lagrange

/-!
# Candidate production: the BCIKS20 Step-7 supply (Claims 5.9 + 5.11, consumer vocabulary)

The single remaining open statement of #302 is the production of a candidate global curve
`pHat ∈ F[Z][X]` beating the defect budget of `branch_capture_dichotomy`.  This file lands the
**entire elementary (Step-7) part** of that production in the decode vocabulary, and isolates
the one genuinely open input as a *per-coordinate scalar statement* — BCIKS20 Claim 5.10's
output shape — instead of a global algebraic one:

* `exists_rich_coordinates` — **Claim 5.11** (the double-counting supply): if every cell
  scalar's decode agrees with the curve fold on all but `e` coordinates, then `k` coordinates
  exist on which all but `M` cell scalars agree, whenever `e·|E| < (M+1)·(n−k+1)`;
* `lagrangeCurveTuple` / `curve_pin_of_node_agreement` — **the Claim 5.9 interpolation step**:
  a degree-`< k` decode agreeing with the fold at `k` fixed coordinates *is* the polynomial
  curve of the coordinatewise Lagrange tuple — pointwise curve values at `k` nodes pin the
  whole family;
* `capture_on_rich_subcell` — the unconditional composition: **every decoded cell is captured
  by one polynomial curve off an exceptional set of `≤ k·M` scalars**;
* `cell_card_le_of_rich_coordinates` — the unconditional count through the in-tree `L`-ary
  Claim-1 dichotomy: `|E| ≤ T + k·M`;
* `branchOfCurveTuple` (+ `map_eval`/degree lemmas) — the literal candidate builder: a curve
  tuple is a global `pHat ∈ F[Z][X]` with `deg_X < k`, `deg_Z < L` (the converse of
  `map_eval_eq_curve_sum`), and `eval_defect_coeff_natDegree_le` proves the **defect budget**
  `M_defect = B + deg_Y R·(L−1)` of `branch_capture_dichotomy` for any such candidate;
* `CoordinateUpgrade` — the **named open residual** (BCIKS20 Claim 5.10's output): every cell
  scalar's decode value at the `k` chosen coordinates equals the fold-curve value.  This is
  exactly what the Λ-weight machinery proves per coordinate (paper: `γ(x) = w(x, Z)` in `𝕃`,
  via Lemma A.1 — in-tree proven — plus the Claim A.2 weight growth — the open #138/#139
  kernel).  It is consumed here, never fabricated;
* `global_branch_of_coordinate_upgrade` — **the capstone**: upgrade + surface divisibility +
  `|E| > B + deg_Y R·(L−1)` produce the global branch `(Y − C pHat) ∣ R` outright — the exact
  input of `pinning_of_global_branch`/`cell_card_le_of_global_branch`;
* `global_branch_or_card_le` — the unconditional dichotomy: **global branch, or
  `|E| ≤ B + deg_Y R·(L−1) + k·M`** — candidate production with the honest `k·M` slack, which
  is precisely the term `CoordinateUpgrade` (Claim 5.10) removes.

Honesty note: the slack is genuine.  Algebra-only candidate production (no decode/fold data)
is FALSE — `Y² − Z` over a finite field has one irreducible separable fiber component, tiny
budgets, and arbitrarily many decoded scalars (`√γ` per quadratic residue `γ`), yet no global
`pHat` exists; the fold-agreement data consumed here is what excludes it.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset
open _root_.ProximityGap Code
open scoped NNReal

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀]

/-! ## Claim 5.11: the double-counting coordinate supply -/

/-- **BCIKS20 Claim 5.11 (double counting).** If every scalar of the cell `E` carries an
agreement set `A γ` missing at most `e` of the `n` coordinates, and the budget
`e·|E| < (M+1)·(n−k+1)` holds, then there are `k` coordinates on which all but at most `M`
of the cell scalars agree: at most `e·|E|/(M+1) < n−k+1` coordinates can have more than `M`
non-members, so at least `k` coordinates are `M`-rich. -/
theorem exists_rich_coordinates {α : Type} {n : ℕ} (E : Finset α) (A : α → Finset (Fin n))
    (e M k : ℕ) (hkn : k ≤ n)
    (hdef : ∀ γ ∈ E, n - e ≤ (A γ).card)
    (hM : e * E.card < (M + 1) * (n - k + 1)) :
    ∃ T : Finset (Fin n), T.card = k ∧
      ∀ t ∈ T, E.card - M ≤ (E.filter (fun γ => t ∈ A γ)).card := by
  classical
  set poor : Finset (Fin n) := Finset.univ.filter
    (fun t => (E.filter (fun γ => t ∈ A γ)).card < E.card - M) with hpoor
  -- the incidence double count: total disagreement pairs are bounded by `e·|E|`
  have hswap : ∑ t : Fin n, (E.filter (fun γ => t ∉ A γ)).card
      = ∑ γ ∈ E, (Finset.univ.filter (fun t : Fin n => t ∉ A γ)).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  have hcompl : ∀ γ : α, (Finset.univ.filter (fun t : Fin n => t ∉ A γ)).card
      = n - (A γ).card := by
    intro γ
    have h1 : Finset.univ.filter (fun t : Fin n => t ∉ A γ) = (A γ)ᶜ := by
      ext t
      simp [Finset.mem_compl]
    rw [h1, Finset.card_compl, Fintype.card_fin]
  have htotal : ∑ t : Fin n, (E.filter (fun γ => t ∉ A γ)).card ≤ e * E.card := by
    rw [hswap]
    calc ∑ γ ∈ E, (Finset.univ.filter (fun t : Fin n => t ∉ A γ)).card
        ≤ ∑ _γ ∈ E, e := by
          refine Finset.sum_le_sum fun γ hγ => ?_
          rw [hcompl]
          have h2 := hdef γ hγ
          have h3 : (A γ).card ≤ n := by
            have h4 := Finset.card_le_univ (A γ)
            simpa using h4
          omega
      _ = e * E.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  -- every poor coordinate contributes at least `M + 1` disagreement pairs
  have hpoorlb : ∀ t ∈ poor, M + 1 ≤ (E.filter (fun γ => t ∉ A γ)).card := by
    intro t ht
    rw [hpoor, Finset.mem_filter] at ht
    have hpart := Finset.card_filter_add_card_filter_not
      (s := E) (p := fun γ => t ∈ A γ)
    omega
  have hpoorcount : poor.card * (M + 1) ≤ e * E.card :=
    calc poor.card * (M + 1) = ∑ _t ∈ poor, (M + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ t ∈ poor, (E.filter (fun γ => t ∉ A γ)).card := Finset.sum_le_sum hpoorlb
      _ ≤ ∑ t : Fin n, (E.filter (fun γ => t ∉ A γ)).card :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ poor)
      _ ≤ e * E.card := htotal
  -- pigeonhole: fewer than `n − k + 1` poor coordinates, so at least `k` rich ones
  have hpoorlt : poor.card < n - k + 1 := by
    by_contra hcon
    push Not at hcon
    have hmul : (n - k + 1) * (M + 1) ≤ poor.card * (M + 1) :=
      Nat.mul_le_mul hcon (le_refl (M + 1))
    have hcomm : (M + 1) * (n - k + 1) = (n - k + 1) * (M + 1) := Nat.mul_comm _ _
    omega
  have hrichcard : k ≤ (Finset.univ \ poor).card := by
    have h1 : (Finset.univ \ poor).card = n - poor.card := by
      rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hrichcard
  refine ⟨T, hTcard, ?_⟩
  intro t ht
  have htpoor : t ∉ poor := (Finset.mem_sdiff.mp (hTsub ht)).2
  rw [hpoor, Finset.mem_filter] at htpoor
  push Not at htpoor
  exact htpoor (Finset.mem_univ t)

/-! ## The Claim 5.9 interpolation step: `k` node values pin the curve -/

/-- The coordinatewise Lagrange curve tuple: `a j` interpolates the `j`-th word row of the
stack at the nodes `T` of the evaluation domain. -/
noncomputable def lagrangeCurveTuple {n L : ℕ} (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) (T : Finset (Fin n)) (j : Fin L) : F₀[X] :=
  Lagrange.interpolate T (fun t => domain t) (fun t => u j t)

lemma lagrangeCurveTuple_degree_lt {n L : ℕ} (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) (T : Finset (Fin n)) (j : Fin L) :
    (lagrangeCurveTuple domain u T j).degree < (T.card : WithBot ℕ) :=
  Lagrange.degree_interpolate_lt _ (Function.Injective.injOn domain.injective)

lemma lagrangeCurveTuple_natDegree_lt {n L k : ℕ} (hk : 0 < k) (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) {T : Finset (Fin n)} (hT : T.card = k) (j : Fin L) :
    (lagrangeCurveTuple domain u T j).natDegree < k := by
  rcases eq_or_ne (lagrangeCurveTuple domain u T j) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero]
    exact hk
  · have hd := lagrangeCurveTuple_degree_lt domain u T j
    rw [hT] at hd
    exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hd

lemma lagrangeCurveTuple_eval_at_node {n L : ℕ} (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) {T : Finset (Fin n)} {t : Fin n} (ht : t ∈ T)
    (j : Fin L) :
    (lagrangeCurveTuple domain u T j).eval (domain t) = u j t :=
  Lagrange.eval_interpolate_at_node _ (Function.Injective.injOn domain.injective) ht

/-- **The Claim 5.9 interpolation step.** A degree-`< k` polynomial whose values at `k`
domain nodes are the curve-fold values `∑ⱼ γʲ·uⱼ` *is* the polynomial curve of the Lagrange
tuple: both sides are degree-`< k` interpolants of the same `k` values.  Pointwise curve
agreement at `k` coordinates pins the decode globally. -/
theorem curve_pin_of_node_agreement {n L k : ℕ} (hk : 0 < k) {domain : Fin n ↪ F₀}
    {u : WordStack F₀ (Fin L) (Fin n)} {T : Finset (Fin n)} (hT : T.card = k)
    {γ : F₀} {p : F₀[X]} (hpdeg : p.degree < (k : ℕ))
    (hagree : ∀ t ∈ T, p.eval (domain t) = ∑ j : Fin L, γ ^ (j : ℕ) • u j t) :
    p = ∑ j : Fin L, Polynomial.C (γ ^ (j : ℕ)) * lagrangeCurveTuple domain u T j := by
  have hvs : Set.InjOn (fun t : Fin n => (domain t : F₀)) ↑T :=
    Function.Injective.injOn domain.injective
  have hp : p = Lagrange.interpolate T (fun t => domain t)
      (fun t => ∑ j : Fin L, γ ^ (j : ℕ) • u j t) :=
    Lagrange.eq_interpolate_of_eval_eq _ hvs (by rw [hT]; exact hpdeg) hagree
  have hqdeg : (∑ j : Fin L, Polynomial.C (γ ^ (j : ℕ)) *
      lagrangeCurveTuple domain u T j).degree < (T.card : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro j _
    refine lt_of_le_of_lt ?_ (lagrangeCurveTuple_degree_lt domain u T j)
    have hCsmul : Polynomial.C (γ ^ (j : ℕ)) * lagrangeCurveTuple domain u T j =
        (γ ^ (j : ℕ)) • lagrangeCurveTuple domain u T j := by
      rw [Polynomial.smul_eq_C_mul]
    rw [hCsmul]
    exact Polynomial.degree_smul_le _ _
  have hq : ∑ j : Fin L, Polynomial.C (γ ^ (j : ℕ)) * lagrangeCurveTuple domain u T j
      = Lagrange.interpolate T (fun t => domain t)
        (fun t => ∑ j : Fin L, γ ^ (j : ℕ) • u j t) := by
    refine Lagrange.eq_interpolate_of_eval_eq _ hvs hqdeg ?_
    intro t ht
    rw [Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, smul_eq_mul]
    congr 1
    exact lagrangeCurveTuple_eval_at_node domain u ht j
  rw [hp, hq]

/-! ## The unconditional composition: capture off a small exceptional set -/

/-- A decode's witness set misses at most `e` coordinates, in `ℕ` form, whenever
`δ·n ≤ e`. -/
lemma decode_witness_card_ge {n : ℕ} {δ : ℝ≥0} {e : ℕ} {S : Finset (Fin n)}
    (hcard : ((S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)))
    (hδe : δ * (n : ℝ≥0) ≤ (e : ℝ≥0)) :
    n - e ≤ S.card := by
  have h1 : (n : ℝ≥0) - δ * n ≤ (S.card : ℝ≥0) := by
    rw [Fintype.card_fin] at hcard
    calc (n : ℝ≥0) - δ * n = (1 - δ) * n := by rw [tsub_mul, one_mul]
      _ ≤ (S.card : ℝ≥0) := hcard
  have h2 : (n : ℝ≥0) ≤ (S.card : ℝ≥0) + δ * n := tsub_le_iff_right.mp h1
  have h3 : (n : ℝ≥0) ≤ (S.card : ℝ≥0) + (e : ℝ≥0) :=
    le_trans h2 (add_le_add le_rfl hδe)
  have h4 : (n : ℝ≥0) ≤ ((S.card + e : ℕ) : ℝ≥0) := by
    push_cast
    exact h3
  have h5 : n ≤ S.card + e := by exact_mod_cast h4
  omega

variable [Fintype F₀] [DecidableEq F₀]

/-- **Unconditional Step-7 capture off a small exceptional set.** Every decoded cell `E`
carries `k` rich coordinates `T` and a sub-cell `E' ⊆ E` with `|E| ≤ |E'| + k·M` whose
members are ALL pinned to the single polynomial curve of the Lagrange tuple at `T` — the
elementary half of BCIKS20 Step 7.  The exceptional `≤ k·M` scalars are exactly what
Claim 5.10 (`CoordinateUpgrade` below) removes. -/
theorem capture_on_rich_subcell {n L k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    {domain : Fin n ↪ F₀} {δ : ℝ≥0} {u : WordStack F₀ (Fin L) (Fin n)}
    (E : Finset F₀) (P : F₀ → F₀[X]) (e M : ℕ)
    (hdec : ∀ γ ∈ E, ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ)
    (hδe : δ * (n : ℝ≥0) ≤ (e : ℝ≥0))
    (hM : e * E.card < (M + 1) * (n - k + 1)) :
    ∃ (T : Finset (Fin n)) (E' : Finset F₀), E' ⊆ E ∧ T.card = k ∧
      E.card ≤ E'.card + k * M ∧
      ∀ γ ∈ E', P γ =
        ∑ j : Fin L, Polynomial.C (γ ^ (j : ℕ)) * lagrangeCurveTuple domain u T j := by
  classical
  -- choose per-scalar witness sets (opaque `choose` fvars)
  have hex : ∀ γ : F₀, ∃ s : Finset (Fin n), γ ∈ E →
      n - e ≤ s.card ∧ (P γ).degree < (k : ℕ) ∧
        ∀ t ∈ s, (P γ).eval (domain t) = ∑ j : Fin L, γ ^ (j : ℕ) • u j t := by
    intro γ
    by_cases hγ : γ ∈ E
    · obtain ⟨d, hd⟩ := hdec γ hγ
      refine ⟨d.S, fun _ => ⟨decode_witness_card_ge d.hcard hδe, ?_, ?_⟩⟩
      · rw [← hd]
        exact d.hdeg
      · intro t ht
        rw [← hd]
        exact d.hagree t ht
    · exact ⟨∅, fun h => absurd h hγ⟩
  choose A hA using hex
  obtain ⟨T, hTcard, hrich⟩ := exists_rich_coordinates E A e M k hkn
    (fun γ hγ => (hA γ hγ).1) hM
  refine ⟨T, E.filter (fun γ => T ⊆ A γ), Finset.filter_subset _ _, hTcard, ?_, ?_⟩
  · -- counting: the non-rich scalars are covered by the per-coordinate misses
    have hsplit : E \ E.filter (fun γ => T ⊆ A γ) ⊆
        T.biUnion (fun t => E.filter (fun γ => t ∉ A γ)) := by
      intro γ hγ
      rw [Finset.mem_sdiff] at hγ
      obtain ⟨hγE, hγn⟩ := hγ
      have hns : ¬ T ⊆ A γ := fun hc => hγn (Finset.mem_filter.mpr ⟨hγE, hc⟩)
      obtain ⟨t, htT, htn⟩ := Finset.not_subset.mp hns
      exact Finset.mem_biUnion.mpr ⟨t, htT, Finset.mem_filter.mpr ⟨hγE, htn⟩⟩
    have hperT : ∀ t ∈ T, (E.filter (fun γ => t ∉ A γ)).card ≤ M := by
      intro t ht
      have hpart := Finset.card_filter_add_card_filter_not
        (s := E) (p := fun γ => t ∈ A γ)
      have hr := hrich t ht
      omega
    have hbadcard : (E \ E.filter (fun γ => T ⊆ A γ)).card ≤ k * M := by
      refine le_trans (Finset.card_le_card hsplit) (le_trans Finset.card_biUnion_le ?_)
      calc ∑ t ∈ T, (E.filter (fun γ => t ∉ A γ)).card
          ≤ ∑ _t ∈ T, M := Finset.sum_le_sum hperT
        _ = k * M := by rw [Finset.sum_const, hTcard, smul_eq_mul]
    have hcards := Finset.card_sdiff_add_card_eq_card
      (Finset.filter_subset (fun γ => T ⊆ A γ) E)
    omega
  · -- pinning on the rich sub-cell, via the `k`-node agreement
    intro γ hγ
    obtain ⟨hγE, hTA⟩ := Finset.mem_filter.mp hγ
    refine curve_pin_of_node_agreement hk hTcard (hA γ hγE).2.1 ?_
    intro t ht
    exact (hA γ hγE).2.2 t (hTA ht)

/-- **The unconditional count**: composing the rich-sub-cell capture with the in-tree
`L`-ary Claim-1 dichotomy — every decoded cell obeys `|E| ≤ T + k·M` for any threshold
`T ≥ n·(L−1)`, with the honest `k·M` slack. -/
theorem cell_card_le_of_rich_coordinates {n L k : ℕ} [NeZero n] (hk : 0 < k) (hkn : k ≤ n)
    {domain : Fin n ↪ F₀} {δ : ℝ≥0} {u : WordStack F₀ (Fin L) (Fin n)}
    (E : Finset F₀) (P : F₀ → F₀[X]) (e M Tthr : ℕ)
    (hn : Fintype.card (Fin n) * (L - 1) ≤ Tthr)
    (hdec : ∀ γ ∈ E, ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ)
    (hδe : δ * (n : ℝ≥0) ≤ (e : ℝ≥0))
    (hM : e * E.card < (M + 1) * (n - k + 1)) :
    E.card ≤ Tthr + k * M := by
  obtain ⟨T, E', hE'sub, hTcard, hcount, hpin⟩ :=
    capture_on_rich_subcell hk hkn E P e M hdec hδe hM
  have h1 : E'.card ≤ Tthr := by
    refine cell_card_le_of_curve_decode_family_pinning E' Tthr P hn
      (fun γ hγ => hdec γ (hE'sub hγ)) ?_
    intro _
    exact ⟨fun j => lagrangeCurveTuple domain u T j,
      fun j => lagrangeCurveTuple_natDegree_lt hk domain u hTcard j, hpin⟩
  omega

/-! ## The named open residual: the Claim 5.10 coordinate upgrade -/

/-- **The Claim 5.10 output shape — the single open input of candidate production.**
At every chosen coordinate, EVERY cell scalar's decode value equals the curve-fold value
(not merely the witness-set majority that the counting supplies).  In the paper this is
exactly `γ(x) = w(x, Z)` identically in `𝕃` at each rich coordinate `x` (BCIKS20 Claim
5.10), proven there from Lemma A.1 (in-tree: `Lemma_A_1`, proven) plus the Claim A.2 weight
growth of the Hensel numerators — the open #138/#139 Λ-weight kernel.  It is carried here as
a documented hypothesis, never fabricated. -/
def CoordinateUpgrade {n L : ℕ} (domain : Fin n ↪ F₀) (u : WordStack F₀ (Fin L) (Fin n))
    (E : Finset F₀) (P : F₀ → F₀[X]) (T : Finset (Fin n)) : Prop :=
  ∀ γ ∈ E, ∀ t ∈ T, (P γ).eval (domain t) = ∑ j : Fin L, γ ^ (j : ℕ) • u j t

/-- Full-cell pinning from the coordinate upgrade: with Claim 5.10's output at `k`
coordinates, the WHOLE cell is pinned to the Lagrange curve tuple. -/
theorem curve_pinning_of_coordinate_upgrade {n L k : ℕ} (hk : 0 < k)
    {domain : Fin n ↪ F₀} {u : WordStack F₀ (Fin L) (Fin n)}
    {E : Finset F₀} {P : F₀ → F₀[X]} {T : Finset (Fin n)} (hT : T.card = k)
    (hdeg : ∀ γ ∈ E, (P γ).degree < (k : ℕ))
    (hupg : CoordinateUpgrade domain u E P T) :
    ∀ γ ∈ E, P γ =
      ∑ j : Fin L, Polynomial.C (γ ^ (j : ℕ)) * lagrangeCurveTuple domain u T j :=
  fun γ hγ => curve_pin_of_node_agreement hk hT (hdeg γ hγ) (hupg γ hγ)

/-! ## The candidate builder and its defect budget -/

/-- The global candidate of a curve tuple: `pHat := ∑ⱼ C(Zʲ)·(map C aⱼ) ∈ F[Z][X]` — the
converse of `map_eval_eq_curve_sum`: its `Z`-specializations are the polynomial curve. -/
noncomputable def branchOfCurveTuple {L : ℕ} (a : Fin L → F₀[X]) : (F₀[X])[X] :=
  ∑ j : Fin L, Polynomial.C ((Polynomial.X : F₀[X]) ^ (j : ℕ)) * (a j).map Polynomial.C

/-- Specializing the candidate recovers the curve: `pHat|_{Z:=γ} = ∑ⱼ C(γʲ)·aⱼ`. -/
lemma branchOfCurveTuple_map_eval {L : ℕ} (a : Fin L → F₀[X]) (γ : F₀) :
    (branchOfCurveTuple a).map (Polynomial.evalRingHom γ) =
      ∑ j : Fin L, Polynomial.C (γ ^ (j : ℕ)) * a j := by
  rw [branchOfCurveTuple, ← Polynomial.coe_mapRingHom, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, Polynomial.coe_mapRingHom]
  congr 1
  · rw [Polynomial.map_C]
    congr 1
    rw [Polynomial.coe_evalRingHom, Polynomial.eval_pow, Polynomial.eval_X]
  · rw [Polynomial.map_map]
    have hcomp : (Polynomial.evalRingHom γ).comp (Polynomial.C : F₀ →+* F₀[X])
        = RingHom.id F₀ := RingHom.ext fun x => by simp
    rw [hcomp, Polynomial.map_id]

/-- The candidate inherits the tuple's `X`-degree bound. -/
lemma branchOfCurveTuple_natDegree_lt {L k : ℕ} (hk : 0 < k) {a : Fin L → F₀[X]}
    (ha : ∀ j, (a j).natDegree < k) :
    (branchOfCurveTuple a).natDegree < k := by
  have hle : (branchOfCurveTuple a).natDegree ≤ k - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    refine le_trans Polynomial.natDegree_mul_le ?_
    have h1 : (Polynomial.C ((Polynomial.X : F₀[X]) ^ (j : ℕ))).natDegree = 0 :=
      Polynomial.natDegree_C _
    have h2 : ((a j).map (Polynomial.C : F₀ →+* F₀[X])).natDegree ≤ (a j).natDegree :=
      Polynomial.natDegree_map_le
    have h3 := ha j
    omega
  omega

/-- The candidate's `F[Z]`-coefficients have `Z`-degree `< L` — the C5.8/C5.9 budget shape
of `pinning_of_global_branch`. -/
lemma branchOfCurveTuple_coeff_natDegree_lt {L : ℕ} (hL : 0 < L) (a : Fin L → F₀[X])
    (i : ℕ) :
    ((branchOfCurveTuple a).coeff i).natDegree < L := by
  have hle : ((branchOfCurveTuple a).coeff i).natDegree ≤ L - 1 := by
    rw [branchOfCurveTuple, Polynomial.finset_sum_coeff]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_map]
    refine le_trans Polynomial.natDegree_mul_le ?_
    have h1 : ((Polynomial.X : F₀[X]) ^ (j : ℕ)).natDegree ≤ (j : ℕ) :=
      Polynomial.natDegree_X_pow_le _
    have h2 : (Polynomial.C ((a j).coeff i)).natDegree = 0 := Polynomial.natDegree_C _
    have hj : (j : ℕ) ≤ L - 1 := by
      have h4 := j.isLt
      omega
    omega
  omega

/-- Coefficient `Z`-degree bound for powers: if every coefficient of `p ∈ F[Z][X]` has
`Z`-degree `≤ m`, every coefficient of `p^b` has `Z`-degree `≤ b·m`. -/
lemma coeff_pow_natDegree_le {p : (F₀[X])[X]} {m : ℕ}
    (hp : ∀ i, (p.coeff i).natDegree ≤ m) (b : ℕ) :
    ∀ i, ((p ^ b).coeff i).natDegree ≤ b * m := by
  induction b with
  | zero =>
      intro i
      rw [pow_zero, Polynomial.coeff_one]
      split_ifs <;> simp
  | succ b ih =>
      intro i
      rw [pow_succ, Polynomial.coeff_mul]
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x hx => ?_
      refine le_trans Polynomial.natDegree_mul_le ?_
      have h1 := ih x.1
      have h2 := hp x.2
      have h3 : (b + 1) * m = b * m + m := by ring
      omega

/-- **The defect budget of `branch_capture_dichotomy`, proven**: a candidate with
coefficient `Z`-degrees `≤ m` has evaluation defect `R.eval pHat` with coefficient
`Z`-degrees `≤ B + deg_Y R · m` — at `m = L−1` this is the issue's quantitative margin
`M_defect = B + D_Y·(L−1)`. -/
theorem eval_defect_coeff_natDegree_le {R : (F₀[X])[X][Y]} {pHat : (F₀[X])[X]} {B m : ℕ}
    (hRB : ∀ b a : ℕ, ((R.coeff b).coeff a).natDegree ≤ B)
    (hp : ∀ i, (pHat.coeff i).natDegree ≤ m) (i : ℕ) :
    ((Polynomial.eval pHat R).coeff i).natDegree ≤ B + R.natDegree * m := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.finset_sum_coeff]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun b hb => ?_
  rw [Polynomial.coeff_mul]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x hx => ?_
  refine le_trans Polynomial.natDegree_mul_le ?_
  have h1 := hRB b x.1
  have h2 := coeff_pow_natDegree_le hp b x.2
  have hble : b ≤ R.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  have hmul : b * m ≤ R.natDegree * m := Nat.mul_le_mul_right m hble
  omega

/-! ## The capstones -/

/-- **Candidate production from the coordinate upgrade (the capstone).** Given the cell
surface (`(Y − C (P γ)) ∣ R|_γ`), the interpolant coefficient budget `B`, and the Claim-5.10
coordinate upgrade at `k` coordinates, a cell larger than the defect budget
`B + deg_Y R·(L−1)` forces the **global branch**: `(Y − C pHat) ∣ R` for the explicit
Lagrange candidate — exactly the input of `pinning_of_global_branch` and
`cell_card_le_of_global_branch`, closing the chain the day Claim 5.10 lands. -/
theorem global_branch_of_coordinate_upgrade {n L k : ℕ} (hk : 0 < k) (hL : 0 < L)
    {domain : Fin n ↪ F₀} {u : WordStack F₀ (Fin L) (Fin n)}
    (R : (F₀[X])[X][Y]) {B : ℕ}
    (hRB : ∀ b a : ℕ, ((R.coeff b).coeff a).natDegree ≤ B)
    (E : Finset F₀) (P : F₀ → F₀[X]) (T : Finset (Fin n)) (hT : T.card = k)
    (hdeg : ∀ γ ∈ E, (P γ).degree < (k : ℕ))
    (hdvdP : ∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    (hupg : CoordinateUpgrade domain u E P T)
    (hbig : B + R.natDegree * (L - 1) < E.card) :
    (Polynomial.X - Polynomial.C
        (branchOfCurveTuple (fun j => lagrangeCurveTuple domain u T j))) ∣ R := by
  classical
  set pHat := branchOfCurveTuple (fun j => lagrangeCurveTuple domain u T j) with hpHat
  have hpin := curve_pinning_of_coordinate_upgrade hk hT hdeg hupg
  have hcoeff : ∀ i, (pHat.coeff i).natDegree ≤ L - 1 := by
    intro i
    have h1 := branchOfCurveTuple_coeff_natDegree_lt hL
      (fun j => lagrangeCurveTuple domain u T j) i
    rw [← hpHat] at h1
    omega
  have hdefect : ∀ i, ((Polynomial.eval pHat R).coeff i).natDegree
      ≤ B + R.natDegree * (L - 1) := eval_defect_coeff_natDegree_le hRB hcoeff
  rcases branch_capture_dichotomy R pHat hdefect with hgl | hbound
  · exact hgl
  · exfalso
    have hsub : E ⊆ Finset.univ.filter (fun γ : F₀ =>
        (Polynomial.X - Polynomial.C (pHat.map (Polynomial.evalRingHom γ))) ∣
          R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) := by
      intro γ hγ
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hpHat, branchOfCurveTuple_map_eval, ← hpin γ hγ]
      exact hdvdP γ hγ
    have hcard := Finset.card_le_card hsub
    omega

/-- **The unconditional candidate-production dichotomy.** With only the proven supplies —
decode data, the counting numerics, and the cell surface — every cell either produces a
**global branch** `pHat` with the full C5.8/C5.9 budgets (`deg_X < k`, `deg_Z < L`,
`(Y − C pHat) ∣ R`), or is bounded by the defect budget plus the honest slack:
`|E| ≤ B + deg_Y R·(L−1) + k·M`.  The `k·M` term is exactly what the Claim 5.10 upgrade
(the open Λ-weight kernel) removes. -/
theorem global_branch_or_card_le {n L k : ℕ} (hk : 0 < k) (hkn : k ≤ n) (hL : 0 < L)
    {domain : Fin n ↪ F₀} {δ : ℝ≥0} {u : WordStack F₀ (Fin L) (Fin n)}
    (R : (F₀[X])[X][Y]) {B : ℕ}
    (hRB : ∀ b a : ℕ, ((R.coeff b).coeff a).natDegree ≤ B)
    (E : Finset F₀) (P : F₀ → F₀[X]) (e M : ℕ)
    (hdec : ∀ γ ∈ E, ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ)
    (hδe : δ * (n : ℝ≥0) ≤ (e : ℝ≥0))
    (hM : e * E.card < (M + 1) * (n - k + 1))
    (hdvdP : ∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) :
    (∃ pHat : (F₀[X])[X], pHat.natDegree < k ∧ (∀ i, (pHat.coeff i).natDegree < L) ∧
        (Polynomial.X - Polynomial.C pHat) ∣ R) ∨
      E.card ≤ B + R.natDegree * (L - 1) + k * M := by
  classical
  obtain ⟨T, E', hE'sub, hTcard, hcount, hpin⟩ :=
    capture_on_rich_subcell hk hkn E P e M hdec hδe hM
  set a : Fin L → F₀[X] := fun j => lagrangeCurveTuple domain u T j with ha
  set pHat := branchOfCurveTuple a with hpHat
  by_cases hbig : B + R.natDegree * (L - 1) < E'.card
  · left
    have hadeg : ∀ j, (a j).natDegree < k := fun j =>
      lagrangeCurveTuple_natDegree_lt hk domain u hTcard j
    refine ⟨pHat, branchOfCurveTuple_natDegree_lt hk hadeg,
      fun i => branchOfCurveTuple_coeff_natDegree_lt hL a i, ?_⟩
    have hcoeff : ∀ i, (pHat.coeff i).natDegree ≤ L - 1 := by
      intro i
      have h1 := branchOfCurveTuple_coeff_natDegree_lt hL a i
      rw [← hpHat] at h1
      omega
    have hdefect : ∀ i, ((Polynomial.eval pHat R).coeff i).natDegree
        ≤ B + R.natDegree * (L - 1) := eval_defect_coeff_natDegree_le hRB hcoeff
    rcases branch_capture_dichotomy R pHat hdefect with hgl | hbound
    · exact hgl
    · exfalso
      have hsub : E' ⊆ Finset.univ.filter (fun γ : F₀ =>
          (Polynomial.X - Polynomial.C (pHat.map (Polynomial.evalRingHom γ))) ∣
            R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) := by
        intro γ hγ
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [hpHat, branchOfCurveTuple_map_eval, ← hpin γ hγ]
        exact hdvdP γ (hE'sub hγ)
      have hcard := Finset.card_le_card hsub
      omega
  · right
    omega

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_rich_coordinates
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms curve_pin_of_node_agreement
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms capture_on_rich_subcell
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms cell_card_le_of_rich_coordinates
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms curve_pinning_of_coordinate_upgrade
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms branchOfCurveTuple_map_eval
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms eval_defect_coeff_natDegree_le
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms global_branch_of_coordinate_upgrade
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms global_branch_or_card_le

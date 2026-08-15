/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ConstantWeightPlotkinBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorSecantLines
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# P1 rate-quarter predecessor: Ramsey clique extraction in the agreement-overlap graph

Thread `rq:turan-extraction` (#466).  The agreement-overlap graph at the P1
rate-quarter predecessor (`N = 2^30`, `K = 2^28`, `T = 592794966`) has
independence number at most five: among any six explanations two agreement
sets overlap on at least `K` coordinates (exact constant-weight Plotkin with
`lambda = K - 1`; the divided bound is exactly five).  This file turns that
local forcing into GLOBAL clique structure and connects cliques to source
pencils.

Main contents:

* **Two-color finite Ramsey** (`ramsey_clique_or_compl_clique`): for any
  graph and any vertex set `S` with `(s+t).choose s ≤ S.card`, `S` contains an
  `(s+1)`-clique of `G` or a `(t+1)`-clique of `Gᶜ`.  Erdős–Szekeres bound,
  proved from scratch (Mathlib has no Ramsey machinery as of this Mathlib
  pin).
* **Clique extraction** (`exists_overlap_clique`): with the six-point overlap
  forcing, every selected family with at least `(s+5).choose s` scalars
  contains an `(s+1)`-clique of the overlap graph — pairwise `K`-core
  secants.
* **Concrete over-budget pin** (`exists_164_clique_of_over_budget`): since
  `C(168,5) = 1050220248 ≤ 2^30 < 1082239158 = C(169,5)`, an over-budget
  family (`N < |G|`) contains a **164-clique**.  164 is the largest size this
  Ramsey bound yields at budget `N`.
* **Triangle dichotomy** (`triangle_secant_eq_or_triple_agreement_le`): three
  explanations either lie on one polynomial source pencil or their triple
  agreement has at most `K - 1` coordinates.  Hence triple agreement `≥ K`
  consolidates a triangle onto a single pencil
  (`secant_eq_of_triple_agreement_ge_K`).
* **Collinear saturation jump** (`line_core_saturated_of_five_collinear`):
  five collinear explanations force the pencil core above
  `472558252 ≈ 0.44·N`, strictly above the Plotkin saturation ceiling
  `327272222` where pairwise agreement counting is provably vacuous.
* **Named residual** (`CliqueFiveCollinear`): every 164-clique contains five
  collinear members.  Consumed by
  `over_budget_saturated_line_of_cliqueFiveCollinear`: over-budget families
  then contain a saturated-core pencil carrying five bad scalars.

Numerical support (`scripts/probes/probe_w4_clique_pencil_structure.py`,
exact over `F_10007` at the ratio-faithful toy point `n=32, k=8, t=18`):

* a 3-clique with THREE DISTINCT pencils and a 4-clique in general position
  (no collinear triple, near-pencil sunflower with common core `k-1`) are
  both explicitly realized — so cliques of size `≤ 4` do NOT consolidate,
  and the dichotomy's `K-1` triple bound is sharp in structure;
* for `m = 5, 6, 7, 8`, EVERY admissible concurrency design measured
  (including the minimal-constraint mixed design at `m = 5`) has solution
  space of dimension exactly `2k` — the single-pencil locus.  General
  position dies at `m = 5` at these ratios; large cliques are
  collinearity-dominated, supporting (not proving) the named residual.

Provenance: the six-set forcing statement and the overlap-graph construction
parallel the in-flight lane `_P1RateQuarterAgreementOverlapGraph.lean`
(restated locally; that file has no olean).  The `secantCore` shorthand
parallels the in-flight `_P1RateQuarterForcedSecantMatching.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

open Finset Polynomial
open _root_.ProximityGap Code

namespace ArkLib.ProximityGap.Frontier.W4TuranExtraction

open ConstantWeightPlotkinBound
open HalfPredecessorBadEventRichPointBridge
open HalfPredecessorLineCoreGeometry
open HalfPredecessorSecantLines

attribute [local instance] Classical.propDecidable

/-! ## Two-color finite Ramsey with the Erdős–Szekeres threshold -/

section AbstractRamsey

variable {V : Type} [DecidableEq V]

/-- Any nonempty vertex set carries a 1-clique. -/
private theorem exists_singleton_clique (G : SimpleGraph V) {S : Finset V}
    (hS : 1 ≤ S.card) :
    ∃ C : Finset V, C ⊆ S ∧ G.IsNClique 1 C := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hS
  exact ⟨{v}, Finset.singleton_subset_iff.mpr hv,
    SimpleGraph.isNClique_one.mpr ⟨v, rfl⟩⟩

/-- **Two-color finite Ramsey, Erdős–Szekeres form.**  Every vertex set of
size at least `(s+t).choose s` contains an `(s+1)`-clique of `G` or a
`(t+1)`-clique of the complement.  The bound is the classical Pascal
recursion `R(a,b) ≤ R(a-1,b) + R(a,b-1)`. -/
theorem ramsey_clique_or_compl_clique (G : SimpleGraph V) :
    ∀ n s t : ℕ, s + t ≤ n → ∀ S : Finset V, (s + t).choose s ≤ S.card →
      (∃ C : Finset V, C ⊆ S ∧ G.IsNClique (s + 1) C) ∨
      (∃ C : Finset V, C ⊆ S ∧ Gᶜ.IsNClique (t + 1) C) := by
  intro n
  induction n with
  | zero =>
    intro s t hst S hS
    have hs : s = 0 := by omega
    subst hs
    rw [Nat.choose_zero_right] at hS
    exact Or.inl (exists_singleton_clique G hS)
  | succ n ih =>
    intro s t hst S hS
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      rw [Nat.choose_zero_right] at hS
      exact Or.inl (exists_singleton_clique G hS)
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht
      rw [Nat.add_zero, Nat.choose_self] at hS
      exact Or.inr (exists_singleton_clique Gᶜ hS)
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have hpos : 0 < (s' + 1 + (t' + 1)).choose (s' + 1) :=
      Nat.choose_pos (by omega)
    have hone : 1 ≤ S.card := by omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hone
    set NB : Finset V := (S.erase v).filter (fun w => G.Adj v w) with hNBdef
    set NC : Finset V := (S.erase v).filter (fun w => ¬ G.Adj v w) with hNCdef
    have hNBsub : NB ⊆ S :=
      (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
    have hNCsub : NC ⊆ S :=
      (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
    have hsplit : NB.card + NC.card = (S.erase v).card := by
      simpa only [hNBdef, hNCdef] using
        Finset.card_filter_add_card_filter_not
          (s := S.erase v) (p := fun w => G.Adj v w)
    have herase : (S.erase v).card = S.card - 1 :=
      Finset.card_erase_of_mem hv
    have harg : s' + (t' + 1) = s' + 1 + t' := by omega
    have hkey : (s' + 1 + (t' + 1)).choose (s' + 1)
        = (s' + (t' + 1)).choose s' + (s' + 1 + t').choose (s' + 1) := by
      have h1 : s' + 1 + (t' + 1) = (s' + (t' + 1)) + 1 := by omega
      rw [h1, Nat.choose_succ_succ' (s' + (t' + 1)) s', harg]
    rw [hkey] at hS
    by_cases hbig : (s' + (t' + 1)).choose s' ≤ NB.card
    · rcases ih s' (t' + 1) (by omega) NB hbig with ⟨C, hCsub, hC⟩ | ⟨C, hCsub, hC⟩
      · left
        refine ⟨insert v C, Finset.insert_subset hv (hCsub.trans hNBsub), ?_⟩
        exact hC.insert fun b hb => (Finset.mem_filter.mp (hCsub hb)).2
      · exact Or.inr ⟨C, hCsub.trans hNBsub, hC⟩
    · have hNC : (s' + 1 + t').choose (s' + 1) ≤ NC.card := by omega
      rcases ih (s' + 1) t' (by omega) NC hNC with ⟨C, hCsub, hC⟩ | ⟨C, hCsub, hC⟩
      · exact Or.inl ⟨C, hCsub.trans hNCsub, hC⟩
      · right
        refine ⟨insert v C, Finset.insert_subset hv (hCsub.trans hNCsub), ?_⟩
        refine hC.insert fun b hb => ?_
        have hbmem := Finset.mem_filter.mp (hCsub hb)
        have hbne : v ≠ b := fun h =>
          Finset.ne_of_mem_erase hbmem.1 h.symm
        exact (SimpleGraph.compl_adj G v b).mpr ⟨hbne, hbmem.2⟩

/-- **Clique extraction from six-point forcing.**  If every six vertices of
`S` contain an edge (independence number at most five on `S`), then any
subset of size at least `(s+5).choose s` contains an `(s+1)`-clique. -/
theorem exists_nclique_of_six_forcing (G : SimpleGraph V) (S : Finset V)
    (hforce : ∀ X : Finset V, X ⊆ S → X.card = 6 →
      ∃ a ∈ X, ∃ b ∈ X, G.Adj a b)
    (s : ℕ) (hcard : (s + 5).choose s ≤ S.card) :
    ∃ C : Finset V, C ⊆ S ∧ G.IsNClique (s + 1) C := by
  rcases ramsey_clique_or_compl_clique G (s + 5) s 5 le_rfl S hcard with
    h | ⟨C, hCsub, hC⟩
  · exact h
  · exfalso
    have hCcard : C.card = 6 := by
      have := hC.card_eq
      omega
    obtain ⟨a, ha, b, hb, hadj⟩ := hforce C hCsub hCcard
    have hab : a ≠ b := hadj.ne
    have hcompl := hC.isClique ha hb hab
    exact ((SimpleGraph.compl_adj G a b).mp hcompl).2 hadj

end AbstractRamsey

/-! ## The P1 rate-quarter predecessor instantiation -/

/-- Prize length.  (Same value as in `_P1RateQuarterAgreementOverlapGraph`;
restated locally to keep this file's build independent.) -/
abbrev N : Nat := 2 ^ 30

/-- Rate-quarter Reed--Solomon dimension. -/
abbrev K : Nat := 2 ^ 28

/-- Agreement threshold at the lattice predecessor of the saturated
common-factor endpoint. -/
abbrev T : Nat := 592794966

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Six-set overlap forcing.**  Among any six subsets of the P1 coordinate
set, each of cardinality at least the predecessor agreement threshold, two
distinct sets overlap in at least the Reed--Solomon dimension `K`.
(Restatement of the pin in the in-flight `_P1RateQuarterAgreementOverlapGraph`
lane, kept local because that file has no olean.) -/
theorem exists_pair_inter_card_ge_K_of_six
    (A : Fin 6 → Finset (Fin N))
    (hsize : ∀ i, T ≤ (A i).card) :
    ∃ i j : Fin 6, i ≠ j ∧ K ≤ (A i ∩ A j).card := by
  classical
  by_contra hnot
  push Not at hnot
  let A' : Fin 6 → Finset (Fin N) := fun i =>
    Classical.choose (Finset.exists_subset_card_eq (hsize i))
  have hA'sub : ∀ i, A' i ⊆ A i := by
    intro i
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hsize i))).1
  have hA'card : ∀ i, (A' i).card = T := by
    intro i
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hsize i))).2
  have hpair : ∀ i j, i ≠ j → (A' i ∩ A' j).card ≤ K - 1 := by
    intro i j hij
    have hsmall : (A i ∩ A j).card < K := hnot i j hij
    have hsub : A' i ∩ A' j ⊆ A i ∩ A j :=
      Finset.inter_subset_inter (hA'sub i) (hA'sub j)
    have hle := Finset.card_le_card hsub
    omega
  have hplot := constantWeight_plotkin A' T (K - 1) hA'card hpair
  simp only [Fintype.card_fin] at hplot
  norm_num [N, K, T] at hplot

/-- The agreement-overlap graph on the scalar field: two scalars are adjacent
when both are selected and their full agreement sets overlap on at least the
interpolation dimension `K`.  Working on all of `F` (with membership folded
into adjacency) makes the abstract Ramsey theorem directly applicable to
`S = family.G`. -/
noncomputable def overlapGraph
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u) : SimpleGraph F where
  Adj x y := x ≠ y ∧ x ∈ family.G ∧ y ∈ family.G ∧
    K ≤ (fullAgreement dom (u 0) (u 1) x (family.q x) ∩
      fullAgreement dom (u 0) (u 1) y (family.q y)).card
  symm := by
    rintro x y ⟨hne, hx, hy, hcard⟩
    exact ⟨hne.symm, hy, hx, by
      simpa only [Finset.inter_comm] using hcard⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-- Six-point forcing holds inside the selected family: any six selected
scalars contain an overlap-graph edge. -/
theorem overlapGraph_six_forcing
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (hsize : ∀ gamma ∈ family.G, T ≤
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card) :
    ∀ X : Finset F, X ⊆ family.G → X.card = 6 →
      ∃ a ∈ X, ∃ b ∈ X, (overlapGraph family).Adj a b := by
  intro X hX hX6
  have he : X ≃ Fin 6 := by
    rw [← hX6]
    exact X.equivFin
  let label : Fin 6 → F := fun i => (he.symm i : F)
  have hinjective : Function.Injective label := by
    intro i j hij
    apply he.symm.injective
    exact Subtype.ext hij
  have hlabelX : ∀ i, label i ∈ X := fun i => (he.symm i).2
  have hlabelG : ∀ i, label i ∈ family.G := fun i => hX (hlabelX i)
  let A : Fin 6 → Finset (Fin N) := fun i =>
    fullAgreement dom (u 0) (u 1) (label i) (family.q (label i))
  obtain ⟨i, j, hij, hoverlap⟩ :=
    exists_pair_inter_card_ge_K_of_six A
      (fun i => hsize (label i) (hlabelG i))
  refine ⟨label i, hlabelX i, label j, hlabelX j, ?_⟩
  change label i ≠ label j ∧ label i ∈ family.G ∧ label j ∈ family.G ∧
    K ≤ (fullAgreement dom (u 0) (u 1) (label i) (family.q (label i)) ∩
      fullAgreement dom (u 0) (u 1) (label j) (family.q (label j))).card
  exact ⟨hinjective.ne hij, hlabelG i, hlabelG j, by simpa only [A] using hoverlap⟩

/-- **Ramsey clique extraction at the P1 predecessor.**  Every selected
family with at least `(s+5).choose s` scalars contains an `(s+1)`-clique of
the agreement-overlap graph. -/
theorem exists_overlap_clique
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (hsize : ∀ gamma ∈ family.G, T ≤
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card)
    (s : ℕ) (hcard : (s + 5).choose s ≤ family.G.card) :
    ∃ C : Finset F, C ⊆ family.G ∧
      (overlapGraph family).IsNClique (s + 1) C :=
  exists_nclique_of_six_forcing (overlapGraph family) family.G
    (overlapGraph_six_forcing family hsize) s hcard

/-! ## The concrete over-budget pin: a 164-clique -/

/-- `C(168,5) = 1050220248`, kernel-checked through the descending
factorial. -/
theorem choose_168_5_eq : (168 : ℕ).choose 5 = 1050220248 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- `C(169,5) = 1082239158`, kernel-checked through the descending
factorial. -/
theorem choose_169_5_eq : (169 : ℕ).choose 5 = 1082239158 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The Erdős–Szekeres thresholds bracket the bad-count budget exactly at
clique size 164: `C(168,5) ≤ 2^30 < C(169,5)`.  So 164 is the largest clique
size this Ramsey route certifies for an over-budget family. -/
theorem ramsey_pin_164 :
    (163 + 5).choose 163 ≤ N ∧ (N : ℕ) < (164 + 5).choose 164 := by
  have h168 : (168 : ℕ).choose 163 = (168 : ℕ).choose 5 := by
    have h := Nat.choose_symm (n := 168) (k := 5) (by norm_num)
    norm_num at h
    exact h
  have h169 : (169 : ℕ).choose 164 = (169 : ℕ).choose 5 := by
    have h := Nat.choose_symm (n := 169) (k := 5) (by norm_num)
    norm_num at h
    exact h
  constructor
  · show (168 : ℕ).choose 163 ≤ N
    rw [h168, choose_168_5_eq]
    norm_num [N]
  · show (N : ℕ) < (169 : ℕ).choose 164
    rw [h169, choose_169_5_eq]
    norm_num [N]

/-- **Over-budget 164-clique.**  A selected family exceeding the bad-count
budget `N` contains 164 scalars whose agreement sets pairwise overlap on at
least `K` coordinates. -/
theorem exists_164_clique_of_over_budget
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (hsize : ∀ gamma ∈ family.G, T ≤
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card)
    (hover : N < family.G.card) :
    ∃ C : Finset F, C ⊆ family.G ∧
      (overlapGraph family).IsNClique 164 C := by
  have hcard : (163 + 5).choose 163 ≤ family.G.card :=
    le_trans ramsey_pin_164.1 (le_of_lt hover)
  simpa using exists_overlap_clique family hsize 163 hcard

/-! ## Edges are `K`-core secants -/

/-- Shorthand for the joint core of the canonical secant through two selected
scalars.  (Parallels the in-flight `_P1RateQuarterForcedSecantMatching`
lane.) -/
noncomputable def secantCore
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (gamma beta : F) : Finset (Fin N) :=
  jointCore dom (u 0) (u 1)
    (secantParameter family gamma beta).1
    (secantParameter family gamma beta).2

/-- Every overlap-graph edge carries a `K`-coordinate secant core: the exact
line-core identity identifies the agreement overlap of the two endpoints with
the joint core of their unique secant. -/
theorem secantCore_card_ge_K_of_adj
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    {gamma beta : F}
    (hadj : (overlapGraph family).Adj gamma beta) :
    K ≤ (secantCore family gamma beta).card := by
  change gamma ≠ beta ∧ gamma ∈ family.G ∧ beta ∈ family.G ∧
    K ≤ (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
      fullAgreement dom (u 0) (u 1) beta (family.q beta)).card at hadj
  obtain ⟨hne, hg, hb, hoverlap⟩ := hadj
  let line := secantParameter family gamma beta
  have hgOn : gamma ∈ pointsOn family line :=
    first_point_mem_pointsOn_secant family (beta := beta) hg
  have hbOn : beta ∈ pointsOn family line :=
    second_point_mem_pointsOn_secant family (gamma := gamma) hb hne
  have hgLine := (mem_pointsOn_iff family line gamma).mp hgOn |>.2
  have hbLine := (mem_pointsOn_iff family line beta).mp hbOn |>.2
  show K ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card
  rw [← fullAgreement_inter_eq_jointCore
    dom (u 0) (u 1) line.1 line.2 hne]
  simpa only [line, hgLine, hbLine] using hoverlap

/-- Members of an overlap clique pairwise determine `K`-core secants. -/
theorem clique_pairwise_secantCore
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    {m : ℕ} {C : Finset F}
    (hC : (overlapGraph family).IsNClique m C)
    {gamma beta : F} (hg : gamma ∈ C) (hb : beta ∈ C)
    (hne : gamma ≠ beta) :
    K ≤ (secantCore family gamma beta).card :=
  secantCore_card_ge_K_of_adj family (hC.isClique hg hb hne)

/-! ## Triangle dichotomy: collinear or `K-1`-small triple agreement -/

/-- **Triangle dichotomy.**  Three distinct selected explanations either lie
on a single polynomial source pencil (their two secants from the first point
coincide) or their triple agreement has at most `K - 1` coordinates.

The probe realizes both branches at the ratio-faithful toy point: a triangle
of three distinct pencils exists at these thresholds, so the dichotomy cannot
be strengthened to unconditional collinearity. -/
theorem triangle_secant_eq_or_triple_agreement_le
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    {a b c : F} (ha : a ∈ family.G) (hb : b ∈ family.G)
    (hc : c ∈ family.G) (hab : a ≠ b) (hac : a ≠ c) :
    secantParameter family a b = secantParameter family a c ∨
      ((fullAgreement dom (u 0) (u 1) a (family.q a) ∩
          fullAgreement dom (u 0) (u 1) b (family.q b)) ∩
        fullAgreement dom (u 0) (u 1) c (family.q c)).card ≤ K - 1 := by
  by_cases hslope : slopePolynomial a b (family.q a) (family.q b)
      = slopePolynomial a c (family.q a) (family.q c)
  · left
    simp only [secantParameter]
    rw [hslope]
  · right
    exact triple_fullAgreement_card_le_pred_of_slope_ne dom (u 0) (u 1)
      (by norm_num [K]) hab hac (family.degree_lt a ha)
      (family.degree_lt b hb) (family.degree_lt c hc) hslope

/-- **Consolidation trigger.**  Triple agreement of at least `K` coordinates
forces a triangle onto one source pencil. -/
theorem secant_eq_of_triple_agreement_ge_K
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    {a b c : F} (ha : a ∈ family.G) (hb : b ∈ family.G)
    (hc : c ∈ family.G) (hab : a ≠ b) (hac : a ≠ c)
    (htriple : K ≤
      ((fullAgreement dom (u 0) (u 1) a (family.q a) ∩
          fullAgreement dom (u 0) (u 1) b (family.q b)) ∩
        fullAgreement dom (u 0) (u 1) c (family.q c)).card) :
    secantParameter family a b = secantParameter family a c := by
  rcases triangle_secant_eq_or_triple_agreement_le family ha hb hc hab hac with
    h | h
  · exact h
  · exfalso
    have hK : 1 ≤ K := by norm_num [K]
    omega

/-- Equal secants place the third point on the common line: collinearity in
the incidence structure of `_HalfPredecessorSecantLines`. -/
theorem third_mem_pointsOn_of_secant_eq
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    {a b c : F} (hc : c ∈ family.G) (hac : a ≠ c)
    (heq : secantParameter family a b = secantParameter family a c) :
    c ∈ pointsOn family (secantParameter family a b) := by
  rw [heq]
  exact second_point_mem_pointsOn_secant family hc hac

/-! ## The collinear saturation jump -/

/-- Core floor forced by five collinear explanations:
`ceil((5*T - N) / 4) = 472558252`. -/
abbrev saturatedCollinearCoreFloor : Nat := 472558252

/-- **Five collinear explanations force a saturated core.**  If a relevant
secant line carries at least five selected points, its joint core has at
least `472558252 ≈ 0.44·N` coordinates — obtained from the exact fresh-fibre
packing law `L * (T - z) + z ≤ N`. -/
theorem line_core_saturated_of_five_collinear
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (hsize : ∀ gamma ∈ family.G, T ≤
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (h5 : 5 ≤ (pointsOn family line).card) :
    saturatedCollinearCoreFloor ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card := by
  have hdeg := lineParameter_degree_lt family hline
  have hlarge : ∀ gamma ∈ pointsOn family line,
      T ≤ (fullAgreement dom (u 0) (u 1) gamma
        (line.1 + Polynomial.C gamma * line.2)).card := by
    intro gamma hgamma
    have hmem := (mem_pointsOn_iff family line gamma).mp hgamma
    rw [← hmem.2]
    exact hsize gamma hmem.1
  have hproper := family.line_hproper line.1 line.2 (pointsOn family line)
    hdeg.1 hdeg.2 (pointsOn_subset_G family line)
    (fun gamma hgamma => (mem_pointsOn_iff family line gamma).mp hgamma |>.2)
  have hpack := line_card_mul_max_add_core_le dom (u 0) (u 1)
    line.1 line.2 (pointsOn family line) T hlarge hproper
  rw [show Fintype.card (Fin N) = N from Fintype.card_fin N] at hpack
  set z := (jointCore dom (u 0) (u 1) line.1 line.2).card with hz
  set L := (pointsOn family line).card with hL
  have hTval : T = 592794966 := rfl
  have hNval : N = 1073741824 := by norm_num [N]
  have hFval : saturatedCollinearCoreFloor = 472558252 := rfl
  by_cases hzT : T ≤ z
  · omega
  · have h1 : 1 ≤ T - z := by omega
    rw [max_eq_right h1] at hpack
    have h5m : 5 * (T - z) ≤ L * (T - z) :=
      Nat.mul_le_mul_right _ h5
    omega

/-- The five-collinear core floor lies strictly above the Plotkin saturation
ceiling `327272222` (the least overlap threshold at which the constant-weight
Plotkin denominator `T^2 - N*lambda` goes nonpositive; see the in-flight
forced-secant-matching lane).  Pairwise agreement counting is provably
vacuous above that ceiling, so the conditional core jump lands in genuinely
new territory. -/
theorem saturated_floor_above_plotkin_ceiling :
    327272222 < saturatedCollinearCoreFloor := by
  norm_num [saturatedCollinearCoreFloor]

/-! ## The honest named residual and its consumer -/

/-- **Named open residual (clique collinearity).**  Every 164-clique of the
agreement-overlap graph contains five members lying on one relevant secant
line.

Status: OPEN.  Numerical support (probe, ratio-faithful toy point): general
position — no three collinear — is realizable at clique sizes 3 and 4 but
every admissible concurrency design at sizes 5–8 collapses to the
single-pencil locus (solution dimension exactly `2k`), so large cliques are
collinearity-dominated.  The single-line capacity at the prize point is
`N - T + 1 = 480946859 ≥ 164`, so the conclusion is not capacity-obstructed.
A proof must rule out sunflower-dominated 164-cliques with all lines thin;
a refutation must realize one. -/
def CliqueFiveCollinear (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Prop :=
  ∀ (dom : Fin N ↪ F) (delta : NNReal) (u : WordStack F (Fin 2) (Fin N))
    (family : BadScalarRichPointFamily dom K delta u),
    (∀ gamma ∈ family.G, T ≤
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card) →
    ∀ C : Finset F, C ⊆ family.G →
      (overlapGraph family).IsNClique 164 C →
      ∃ line ∈ lineParameters family,
        5 ≤ (C ∩ pointsOn family line).card

/-- **Conditional saturation.**  Under the clique-collinearity residual, an
over-budget family contains a relevant secant line carrying at least five
bad scalars whose joint core is saturated (at least `472558252 ≈ 0.44·N`
coordinates, strictly above the Plotkin ceiling).  This reduces the
consolidation step of the four-pencil programme to the graph-side residual:
the quantitative core jump is automatic once five clique members align. -/
theorem over_budget_saturated_line_of_cliqueFiveCollinear
    (hcc : CliqueFiveCollinear F)
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (hsize : ∀ gamma ∈ family.G, T ≤
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card)
    (hover : N < family.G.card) :
    ∃ line ∈ lineParameters family,
      5 ≤ (pointsOn family line).card ∧
        saturatedCollinearCoreFloor ≤
          (jointCore dom (u 0) (u 1) line.1 line.2).card := by
  obtain ⟨C, hCsub, hC⟩ :=
    exists_164_clique_of_over_budget family hsize hover
  obtain ⟨line, hline, hfive⟩ := hcc dom delta u family hsize C hCsub hC
  have hfive' : 5 ≤ (pointsOn family line).card :=
    le_trans hfive (Finset.card_le_card (Finset.inter_subset_right))
  exact ⟨line, hline, hfive',
    line_core_saturated_of_five_collinear family hsize hline hfive'⟩

/-- Sanity: the single-line capacity at the P1 predecessor,
`N - T + 1 = 480946859`, comfortably exceeds 164 — the residual's conclusion
is not capacity-obstructed. -/
theorem single_line_capacity_exceeds_164 : 164 ≤ N - T + 1 := by
  norm_num [N, T]

end ArkLib.ProximityGap.Frontier.W4TuranExtraction

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.W4TuranExtraction.ramsey_clique_or_compl_clique
#print axioms
  ArkLib.ProximityGap.Frontier.W4TuranExtraction.exists_nclique_of_six_forcing
#print axioms
  ArkLib.ProximityGap.Frontier.W4TuranExtraction.exists_pair_inter_card_ge_K_of_six
#print axioms
  ArkLib.ProximityGap.Frontier.W4TuranExtraction.overlapGraph_six_forcing
#print axioms
  ArkLib.ProximityGap.Frontier.W4TuranExtraction.exists_overlap_clique
#print axioms
  ArkLib.ProximityGap.Frontier.W4TuranExtraction.choose_168_5_eq
#print axioms
  ArkLib.ProximityGap.Frontier.W4TuranExtraction.ramsey_pin_164
#print axioms
  ArkLib.ProximityGap.Frontier.W4TuranExtraction.exists_164_clique_of_over_budget
#print axioms
  ArkLib.ProximityGap.Frontier.W4TuranExtraction.secantCore_card_ge_K_of_adj
#print axioms
  ArkLib.ProximityGap.Frontier.W4TuranExtraction.clique_pairwise_secantCore
#print axioms
  ArkLib.ProximityGap.Frontier.W4TuranExtraction.triangle_secant_eq_or_triple_agreement_le
#print axioms
  ArkLib.ProximityGap.Frontier.W4TuranExtraction.secant_eq_of_triple_agreement_ge_K
#print axioms
  ArkLib.ProximityGap.Frontier.W4TuranExtraction.third_mem_pointsOn_of_secant_eq
#print axioms
  ArkLib.ProximityGap.Frontier.W4TuranExtraction.line_core_saturated_of_five_collinear
#print axioms
  ArkLib.ProximityGap.Frontier.W4TuranExtraction.over_budget_saturated_line_of_cliqueFiveCollinear

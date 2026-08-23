/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.UniversalStaircaseCollapse
import ArkLib.Data.CodingTheory.ProximityGap.StripEdgeDeltaStar
import ArkLib.Data.CodingTheory.ProximityGap.CosetCliqueBoundary
import ArkLib.Data.CodingTheory.ProximityGap.MCAExactPin

/-!
# Strip sup-exactness: `ε_mca = (n/(b−1))/q` EXACTLY on the top strip row, every band (#357)

Closing-audit **item 4** (sub-Johnson sup-exactness), strip half: the in-tree strip
explosion (`MonomialStripExplosion.strip_eps_ge`, worth `(n/e)/q` at `g = e := b−1`) is
**extremal on the top strip row `d = 3e`** — no stack of any code of distance `≥ 3e`
carries more than `max(2e−1, ⌊n/e⌋)` bad scalars at band-`(e+1)` radii.  With the
certificate this pins the first **exact** strip values of the staircase, at every band
at once, and a new exact-`δ*` family whose *good* side is an explosion value.

**The per-stack theorem** (`topStrip_badScalars_card_le`).  For any linear code with no
nonzero codeword of weight `≤ 3e − 1` (distance `≥ 3e`), any stack `(u₀, u₁)`, and any
radius with `δ·n < e + 1` (error budget `e`): the bad-scalar set has size
`≤ max(2e−1, ⌊n/e⌋)`.

*Proof.*  Choose for each bad `γ` a witness `Tγ` (complement size `≤ e`,
`witness_compl_card_le`) and a line codeword `wγ`.  Two branches:

1. **Some pair has `|Tγ₁ᶜ ∪ Tγ₂ᶜ| ≤ 2e − 1`** (overlapping/small supports).  The pair
   pins an affine codeword frame `U + γ•D` (`D` the difference quotient, `U` the
   intercept): `u₀ = U`, `u₁ = D` on `Tγ₁ ∩ Tγ₂`.  *Absorption*: for **every** bad `γ`,
   `wγ` and `U + γ•D` agree off `Tγᶜ ∪ (Tγ₁ᶜ ∪ Tγ₂ᶜ)` (`≤ 3e − 1` points), hence are
   **equal** (distance forcing).  *Escape*: `γ`'s no-joint clause applied to the pair
   `(U, D)` produces a point `x ∈ Tγ₁ᶜ ∪ Tγ₂ᶜ` with `u₁ x ≠ D x` and
   `u₀ x + γ•u₁ x = U x + γ•D x` — which determines `γ` from `x`.  The bad set injects
   into a `≤ (2e−1)`-point set.
2. **Every pair has `|Tγ₁ᶜ ∪ Tγ₂ᶜ| ≥ 2e`**: all complements are pairwise-disjoint
   `e`-sets, so `N·e ≤ n`.

The branch dichotomy is exactly the measured maximizer taxonomy
(`probe_strip_sup_exactness.py`: `(e+1)`-point degenerate-pencil "triangles" vs the
disjoint fiber tiling of the telescoping family; criterion cross-validated word-level).
The absorption inequality `e + (2e−1) < d` is exactly what fails on the lower strip
rows (`2e+2 ≤ d ≤ 3e−1`) and at the boundary (`d ≤ 2e+1`) — sharpness, not slack.

**Consequences.**
* `topStrip_epsMCA_le` : `ε_mca(C, δ) ≤ max(2e−1, ⌊n/e⌋)/|F|` — the band-`(e+1)`
  analogue of the master collapse, one distance step below its `3b−2` threshold.
* `rs_topStrip_epsMCA_eq` : for smooth `μ_n` (`e ∣ n`, `e(2e−1) ≤ n`, `e ≥ 2`),
  `k = n − (3e−1)` (distance `d = 3e`, the top strip row of band `b = e+1`), and every
  radius `e ≤ δ·n < e+1`:  `ε_mca(RS[F, μ_n, k], δ) = (n/e)/|F|` **exactly** — the
  first exact values of the staircase strip (sup side meeting `strip_eps_ge`).
* `mcaDeltaStar_eq_strip_interior` : for `4 ∣ n`, `12 ≤ n`, `k = n − 5`, and every
  `ε* ∈ [(n/2)/|F|, n/|F|)`:  `δ*(RS[F, μ_n, n−5], ε*) = 3/n` — a new closed-form
  exact-`δ*` family on the band `[(n/2)/q, n/q)` (width `n/2` granularity steps), good
  side = this collapse at `e = 2`, bad side = the coset-clique boundary certificate
  (`clique_eps_ge`, `b = 4`).

**Honest scope:** the top strip row only (`d = 3e`; at `d ≥ 3e+1` the master collapse
is sharper).  For `b ≥ 4` the *lower* strip rows (`2b ≤ d ≤ 3b−4`) stay open — there
the absorption budget `e + (2e−1)` reaches `d` and wt-`d` codewords can deviate; and
the boundary rows (`d ≤ 2b−1`) are *not* covered — there the explosion provably
exceeds `n/e` (`CosetCliqueBoundary`).

Probes: `scripts/probes/probe_strip_sup_exactness.py` — criterion validated word-level
(120 random instances, 2 cells), exhaustive max over ALL pencils at `(6,2,7)` = 6
(boundary, known), `(6,1,7)` = 3, `(6,1,13)` = 3, `(8,3,17)` = 4 — every strip cell
`= max(2e−1, n/e)` exactly; `probe_boundary_sup_exactness.py` — boundary cells
`(8,4,17)` = 7, `(9,5,19)` = 9, `(12,8,13)` = 12 (= `n − [3∤n]`, the boundary law,
outside this file's coverage and pre-registered for the boundary brick).

## References

Issue #357 (closing-readiness audit item 4); `UniversalStaircaseCollapse.lean` (the
`d ≥ 3b−2` collapse this extends one row down), `MonomialStripExplosion.lean` (the
matching lower certificate), `CosetCliqueBoundary.lean` (the band-4 bad certificate for
the pin), `MCAExactPin.lean` (the pin combinator).
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.StripSupExactness

open scoped NNReal ENNReal ProbabilityTheory
open Finset
open ProximityGap Code
open ProximityGap.CensusLowerBound
open ProximityGap.SmoothLadderInstance
open ProximityGap.MCAStaircaseMaster
open ProximityGap.SpikeFloor
open ProximityGap.MCAThresholdLedger

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The two in-tree `NoWeightLE` surfaces (`MCAStaircaseMaster` / `SpikeFloor`) are the
same predicate; this bridges `evalCode_noWeightLE` to the collapse machinery. -/
theorem spikeFloor_noWeightLE_of_master {C : Submodule F (ι → A)} {m : ℕ}
    (h : MCAStaircaseMaster.NoWeightLE C m) : SpikeFloor.NoWeightLE C m :=
  fun w hw hT => h w hw hT

open Classical in
/-- **The top-strip per-stack bound, one distance step below the collapse threshold.**
For any linear code with no nonzero codeword of weight `≤ 3e − 1` (distance `≥ 3e`),
any radius with `δ·n < e + 1`, and any stack: at most `max(2e−1, ⌊n/e⌋)` bad scalars.
Sharp on both branches: `(e+1)`-point degenerate pencils realize the overlap branch,
the disjoint-fiber telescoping family realizes the tiling branch. -/
theorem topStrip_badScalars_card_le (e : ℕ) (he : 1 ≤ e) (C : Submodule F (ι → A))
    (hC : SpikeFloor.NoWeightLE C (3 * e - 1)) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < ((e + 1 : ℕ) : ℝ≥0)) (u₀ u₁ : ι → A) :
    (Finset.univ.filter
      (fun γ : F => mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ)).card
      ≤ max (2 * e - 1) (Fintype.card ι / e) := by
  set B := Finset.univ.filter
    (fun γ : F => mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ) with hB
  -- extract witnesses and line codewords for every bad scalar
  have hex : ∀ γ : F, γ ∈ B → ∃ S : Finset ι,
      ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι) ∧
      (∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧
      ¬ pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁ := by
    intro γ hγ
    exact (Finset.mem_filter.mp hγ).2
  choose! T hTsz hwEx hno using hex
  choose! w hwC hwAg using hwEx
  have hcompl : ∀ γ ∈ B, (T γ)ᶜ.card ≤ e := by
    intro γ hγ
    have h := witness_compl_card_le (j := e + 1) hδ (hTsz γ hγ)
    omega
  by_cases hover : ∃ γ₁, γ₁ ∈ B ∧ ∃ γ₂, γ₂ ∈ B ∧ γ₁ ≠ γ₂ ∧
      ((T γ₁)ᶜ ∪ (T γ₂)ᶜ).card ≤ 2 * e - 1
  · -- Branch 1: an overlapping/small pair exists — the whole family is a
    -- degenerate pencil on ≤ 2e−1 points; every bad scalar is an escape value.
    obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hne, hE3⟩ := hover
    set E12 := (T γ₁)ᶜ ∪ (T γ₂)ᶜ with hE12
    have h12 : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hne
    set D : ι → A := (γ₁ - γ₂)⁻¹ • (w γ₁ - w γ₂) with hD
    have hDC : D ∈ C := C.smul_mem _ (C.sub_mem (hwC γ₁ hγ₁) (hwC γ₂ hγ₂))
    set U : ι → A := w γ₁ - γ₁ • D with hU
    have hUC : U ∈ C := C.sub_mem (hwC γ₁ hγ₁) (C.smul_mem _ hDC)
    have hdiff : (γ₁ - γ₂) • D = w γ₁ - w γ₂ := by
      rw [hD, smul_smul, mul_inv_cancel₀ h12, one_smul]
    -- the affine frame explains both pinned codewords
    have hw₁ : w γ₁ = U + γ₁ • D := by rw [hU]; abel
    -- pointwise pinning on the common witness
    have hpin : ∀ x ∈ T γ₁, x ∈ T γ₂ → u₁ x = D x ∧ u₀ x = U x := by
      intro x hx₁ hx₂
      have ha₁ := hwAg γ₁ hγ₁ x hx₁
      have ha₂ := hwAg γ₂ hγ₂ x hx₂
      have hsub : (γ₁ - γ₂) • u₁ x = (γ₁ - γ₂) • D x := by
        have hDx : (γ₁ - γ₂) • D x = w γ₁ x - w γ₂ x := by
          have := congrFun hdiff x
          simpa using this
        rw [hDx, ha₁, ha₂, sub_smul]
        abel
      have hu₁ : u₁ x = D x := by
        have := congrArg (fun z => (γ₁ - γ₂)⁻¹ • z) hsub
        simpa [smul_smul, inv_mul_cancel₀ h12] using this
      refine ⟨hu₁, ?_⟩
      have hux : u₀ x + γ₁ • u₁ x = U x + γ₁ • D x := by
        rw [← ha₁, hw₁]; simp
      rw [hu₁] at hux
      exact add_right_cancel hux
    -- absorption: every bad scalar's codeword IS the affine frame
    have habs : ∀ γ ∈ B, w γ = U + γ • D := by
      intro γ hγ
      refine codeword_eq_of_eq_off C hC (hwC γ hγ)
        (C.add_mem hUC (C.smul_mem γ hDC)) (B := (T γ)ᶜ ∪ E12) ?_ ?_
      · have h1 := hcompl γ hγ
        have h2 := Finset.card_union_le ((T γ)ᶜ) E12
        omega
      · intro x hx
        rw [hE12] at hx
        simp only [Finset.mem_union, Finset.mem_compl, not_or, not_not] at hx
        obtain ⟨hxγ, hx₁, hx₂⟩ := hx
        obtain ⟨hu₁, hu₀⟩ := hpin x hx₁ hx₂
        rw [hwAg γ hγ x hxγ, hu₁, hu₀]
        simp
    -- escape: the no-joint clause at (U, D) tags every bad scalar with a point of E12
    have hesc : ∀ γ : F, γ ∈ B → ∃ x : ι, x ∈ E12 ∧ u₁ x ≠ D x ∧
        γ • (u₁ x - D x) = U x - u₀ x := by
      intro γ hγ
      have hfail : ¬ ∀ i ∈ T γ, U i = u₀ i ∧ D i = u₁ i := by
        intro hall
        exact hno γ hγ ⟨U, hUC, D, hDC, hall⟩
      push Not at hfail
      obtain ⟨x, hxT, hxne⟩ := hfail
      have hlin : u₀ x + γ • u₁ x = U x + γ • D x := by
        rw [← hwAg γ hγ x hxT, habs γ hγ]; simp
      have hu₁ne : u₁ x ≠ D x := by
        intro h
        rw [h] at hlin
        exact hxne (add_right_cancel hlin).symm h.symm
      refine ⟨x, ?_, hu₁ne, ?_⟩
      · by_contra hxE
        rw [hE12] at hxE
        simp only [Finset.mem_union, Finset.mem_compl, not_or, not_not] at hxE
        exact hu₁ne (hpin x hxE.1 hxE.2).1
      · calc γ • (u₁ x - D x)
            = (u₀ x + γ • u₁ x) - u₀ x - γ • D x := by rw [smul_sub]; abel
          _ = (U x + γ • D x) - u₀ x - γ • D x := by rw [hlin]
          _ = U x - u₀ x := by abel
    choose! ξ hξE hξne hξeq using hesc
    have hinj : Set.InjOn ξ B := by
      intro a ha b hb hab
      by_contra hne'
      have hsub : (a - b) • (u₁ (ξ a) - D (ξ a)) = 0 := by
        rw [sub_smul, hξeq a ha, hab, hξeq b hb]
        abel
      have hv : u₁ (ξ a) - D (ξ a) ≠ 0 := sub_ne_zero.mpr (hξne a ha)
      have hab0 : a - b ≠ 0 := sub_ne_zero.mpr hne'
      have hz : u₁ (ξ a) - D (ξ a) = 0 := by
        have := congrArg (fun z => (a - b)⁻¹ • z) hsub
        simpa [smul_smul, inv_mul_cancel₀ hab0] using this
      exact hv hz
    have hcard := Finset.card_le_card_of_injOn ξ
      (fun γ hγ => hξE γ hγ) hinj
    calc B.card ≤ E12.card := hcard
      _ ≤ 2 * e - 1 := hE3
      _ ≤ max (2 * e - 1) (Fintype.card ι / e) := le_max_left _ _
  · -- Branch 2: all pairs ≥ 2e — the complements are pairwise-disjoint e-sets.
    push Not at hover
    by_cases hB1 : B.card ≤ 1
    · exact le_trans hB1 (le_trans (by omega : 1 ≤ 2 * e - 1) (le_max_left _ _))
    have hpair : ∀ γ ∈ B, ∀ γ' ∈ B, γ ≠ γ' →
        (T γ)ᶜ.card = e ∧ Disjoint ((T γ)ᶜ) ((T γ')ᶜ) := by
      intro γ hγ γ' hγ' hneq
      have h4 : 2 * e ≤ ((T γ)ᶜ ∪ (T γ')ᶜ).card := by
        have := hover γ hγ γ' hγ' hneq
        omega
      have hle := Finset.card_union_le ((T γ)ᶜ) ((T γ')ᶜ)
      have h1 := hcompl γ hγ
      have h2 := hcompl γ' hγ'
      have hint := Finset.card_union_add_card_inter ((T γ)ᶜ) ((T γ')ᶜ)
      refine ⟨by omega, ?_⟩
      rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]
      omega
    have hcard2 : ∀ γ ∈ B, (T γ)ᶜ.card = e := by
      intro γ hγ
      obtain ⟨γ', hγ', hne'⟩ : ∃ γ' ∈ B, γ' ≠ γ := by
        by_contra hcon
        push Not at hcon
        have hsub : B ⊆ {γ} := fun x hx => Finset.mem_singleton.mpr (hcon x hx)
        have hle1 := Finset.card_le_card hsub
        rw [Finset.card_singleton] at hle1
        omega
      exact (hpair γ hγ γ' hγ' (Ne.symm hne')).1
    have hdisj : ∀ γ ∈ B, ∀ γ' ∈ B, γ ≠ γ' →
        Disjoint ((T γ)ᶜ) ((T γ')ᶜ) := by
      intro γ hγ γ' hγ' hneq
      exact (hpair γ hγ γ' hγ' hneq).2
    have hbi : (B.biUnion fun γ => (T γ)ᶜ).card = B.card * e := by
      rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hcard2,
        Finset.sum_const, smul_eq_mul]
    have hle : (B.biUnion fun γ => (T γ)ᶜ).card ≤ Fintype.card ι := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
    have hmul : B.card * e ≤ Fintype.card ι := hbi ▸ hle
    exact le_trans ((Nat.le_div_iff_mul_le (by omega : 0 < e)).mpr hmul)
      (le_max_right _ _)

open Classical in
/-- **The top-strip collapse-to-`⌊n/e⌋`:** `ε_mca(C, δ) ≤ max(2e−1, ⌊n/e⌋)/|F|` at
every radius with `δ·n < e+1`, for every linear code of distance `≥ 3e`.  One distance
step below the master collapse's `3b−2` threshold, the bound degrades from `e+1` to
`⌊n/e⌋` — and (by `strip_eps_ge`) not a step less for smooth Reed–Solomon. -/
theorem topStrip_epsMCA_le (e : ℕ) (he : 1 ≤ e) (C : Submodule F (ι → A))
    (hC : SpikeFloor.NoWeightLE C (3 * e - 1)) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < ((e + 1 : ℕ) : ℝ≥0)) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      ≤ ((max (2 * e - 1) (Fintype.card ι / e) : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  refine ENNReal.div_le_div_right ?_ _
  exact_mod_cast topStrip_badScalars_card_le e he C hC hδ (u 0) (u 1)

variable {n k : ℕ}

open Classical in
/-- **THE EXACT TOP-STRIP VALUE, every band.**  For the smooth domain `μ_n = ⟨γ⟩`
(`e ∣ n`, `e(2e−1) ≤ n`, `2 ≤ e`), dimension `k = n − (3e−1)` (distance `d = 3e`, the
top strip row of band `b = e+1`), and every radius `e ≤ δ·n < e+1`:

  `ε_mca(RS[F, μ_n, k], δ) = (n/e) / |F|`.

The first exact `ε_mca` values on the staircase strip: the `≥` is the monomial-pencil
explosion (`strip_eps_ge` at `g = e`), the `≤` is `topStrip_epsMCA_le` — sup-exactness
for the top strip row of every band (closing-audit item 4, strip half). -/
theorem rs_topStrip_epsMCA_eq [Nonempty (Fin n)] (γ : F) (hord : orderOf γ = n)
    (e : ℕ) (he2 : 2 ≤ e) (hen : e ∣ n) (hbig : e * (2 * e - 1) ≤ n)
    (hk : k = n - (3 * e - 1)) {δ : ℝ≥0}
    (hδlo : ((e : ℕ) : ℝ≥0) ≤ δ * n) (hδhi : δ * n < ((e + 1 : ℕ) : ℝ≥0)) :
    epsMCA (F := F) (A := F) (evalCode (smoothDom γ n) k : Set (Fin n → F)) δ
      = ((n / e : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  have hn3e : 3 * e ≤ n := by
    have h3 : 3 ≤ 2 * e - 1 := by omega
    calc 3 * e ≤ (2 * e - 1) * e := Nat.mul_le_mul_right e h3
      _ = e * (2 * e - 1) := Nat.mul_comm _ _
      _ ≤ n := hbig
  have hnpos : 0 < n := by omega
  have hinj : Function.Injective (smoothDom γ n) := smoothDom_injective γ hord
  refine le_antisymm ?_ ?_
  · -- sup side: the per-stack collapse
    have h := topStrip_epsMCA_le (F := F) e (by omega) (evalCode (smoothDom γ n) k)
      (spikeFloor_noWeightLE_of_master
        (StripEdgeDeltaStar.evalCode_noWeightLE (m := 3 * e - 1) (smoothDom γ n) hinj
          (by omega) (by omega)))
      (δ := δ) (by rw [Fintype.card_fin]; exact hδhi)
    have hmax : max (2 * e - 1) (Fintype.card (Fin n) / e) = n / e := by
      rw [Fintype.card_fin]
      refine max_eq_right ?_
      refine (Nat.le_div_iff_mul_le (by omega : 0 < e)).mpr ?_
      rw [Nat.mul_comm]
      exact hbig
    rwa [hmax] at h
  · -- explosion side: `strip_eps_ge` at `g = e`, transported up by monotonicity
    have hge := MonomialStripExplosion.strip_eps_ge (g := e) (k := k) γ hord
      (by omega) hen (by omega) (by omega) (by omega) (F := F)
    refine le_trans hge (epsMCA_mono _ ?_)
    -- `e/n ≤ δ` from `e ≤ δ·n`
    rw [div_le_iff₀ (by exact_mod_cast hnpos : (0 : ℝ≥0) < (n : ℝ≥0))]
    exact_mod_cast hδlo

open Classical in
/-- **The band-3 instance: `ε_mca(RS[F, μ_n, n−5], δ) = (n/2)/|F|` exactly** for
`2 ∣ n`, `6 ≤ n`, every radius `2 ≤ δ·n < 3` — the `d = 6` strip row, exhaustively
probe-matched at `(6,1,7)`, `(6,1,13)`, `(8,3,17)`. -/
theorem rs_strip_epsMCA_eq [Nonempty (Fin n)] (γ : F) (hord : orderOf γ = n)
    (h2n : 2 ∣ n) (hn6 : 6 ≤ n) (hk : k = n - 5) {δ : ℝ≥0}
    (hδlo : (2 : ℝ≥0) ≤ δ * n) (hδhi : δ * n < 3) :
    epsMCA (F := F) (A := F) (evalCode (smoothDom γ n) k : Set (Fin n → F)) δ
      = ((n / 2 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  refine rs_topStrip_epsMCA_eq γ hord 2 le_rfl h2n (by omega) (by omega)
    (by exact_mod_cast hδlo) (by exact_mod_cast hδhi)

open Classical in
/-- **Exact δ\* on the strip interior band: the first pin whose GOOD side is an
explosion value.**  For `μ_n = ⟨ζ⟩` with `4 ∣ n`, `12 ≤ n`, `k = n − 5`, and every
`ε* ∈ [(n/2)/|F|, n/|F|)`:

  `mcaDeltaStar(RS[F, μ_n, n−5], ε*) = 3/n`.

Good below `3/n` by the band-3 top-strip collapse (this file); bad at and above `3/n`
by the band-4 coset-clique boundary certificate (`clique_eps_ge`, worth `n/q`).  The
pinned `ε*`-band spans `n/2` granularity steps; together with the strip-edge pin
(`mcaDeltaStar_eq_strip_edge`, band `[2/q, (n/2)/q)`) the threshold function of these
codes is now exact on all of `[2/q, n/q)`. -/
theorem mcaDeltaStar_eq_strip_interior [Nonempty (Fin n)] (ζ : F)
    (hord : orderOf ζ = n) (h4n : 4 ∣ n) (hn12 : 12 ≤ n) (hk : k = n - 5)
    {εstar : ℝ≥0∞}
    (hlo : ((n / 2 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < ((n : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := F)
      (evalCode (smoothDom ζ n) k : Set (Fin n → F)) εstar
      = (3 : ℝ≥0) / (n : ℝ≥0) := by
  have hnpos : 0 < n := by omega
  have hn0 : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hnpos
  have hinj : Function.Injective (smoothDom ζ n) := smoothDom_injective ζ hord
  refine mcaDeltaStar_eq_of_good_below_of_bad_above _ εstar ?_ ?_ ?_
  · -- 3/n ≤ 1
    rw [div_le_one hn0]
    exact_mod_cast (by omega : 3 ≤ n)
  · -- good below 3/n: the band-3 top-strip collapse
    intro δ hδ
    have hδ3 : δ * (Fintype.card (Fin n) : ℝ≥0) < ((2 + 1 : ℕ) : ℝ≥0) := by
      rw [Fintype.card_fin]
      have hlt : δ * (n : ℝ≥0) < 3 := by
        calc δ * (n : ℝ≥0) < ((3 : ℝ≥0) / (n : ℝ≥0)) * n :=
              mul_lt_mul_of_pos_right hδ hn0
          _ = 3 := by field_simp
      exact_mod_cast hlt
    have h := topStrip_epsMCA_le (F := F) 2 (by omega) (evalCode (smoothDom ζ n) k)
      (spikeFloor_noWeightLE_of_master
        (StripEdgeDeltaStar.evalCode_noWeightLE (m := 3 * 2 - 1) (smoothDom ζ n) hinj
          (by omega) (by omega))) hδ3
    have hmax : max (2 * 2 - 1) (Fintype.card (Fin n) / 2) = n / 2 := by
      rw [Fintype.card_fin]
      omega
    rw [hmax] at h
    exact le_trans h hlo
  · -- bad at and above 3/n: the band-4 clique certificate
    intro δ hδ
    refine lt_of_lt_of_le hhi ?_
    have hclique := CosetCliqueBoundary.clique_eps_ge (b := 4) (k := k)
      (ζ := ζ) hord (by omega) h4n (by omega) (by omega) (by omega) (F := F)
    refine le_trans hclique (epsMCA_mono _ ?_)
    -- ((4:ℕ):ℝ≥0 − 1)/n = 3/n ≤ δ
    have h41 : ((4 : ℕ) : ℝ≥0) - 1 = 3 := by
      rw [show ((4 : ℕ) : ℝ≥0) = 4 from by norm_num]
      exact tsub_eq_of_eq_add (by norm_num)
    rw [h41]
    exact hδ

end ProximityGap.StripSupExactness

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.StripSupExactness.topStrip_badScalars_card_le
#print axioms ProximityGap.StripSupExactness.topStrip_epsMCA_le
#print axioms ProximityGap.StripSupExactness.rs_topStrip_epsMCA_eq
#print axioms ProximityGap.StripSupExactness.rs_strip_epsMCA_eq
#print axioms ProximityGap.StripSupExactness.mcaDeltaStar_eq_strip_interior

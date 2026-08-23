/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R2B_LargeZeroWitnessSplit
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._LowProfileFiberBound

/-!
# LANE W9 (#466, thread ll:low-profile-fiber): ROOT-PENCIL SATURATION —
# the safe large-zero bad-scalar budget is REFUTED at every sub-field size

**The question this lane was tasked with** (workbench §5(2), the weld's `hlow`/`hsafe`
production obligation): what is the TRUE low-profile fiber/stratum count `D(t)`, `t < k`, on
zero-direction-safe large-zero lines, and can it be bounded sub-`q`?

**The answer is NO — with an explicit, fully general construction.**  The *root pencil*: pick a
nonzero codeword `e` of degree `≤ k−1` whose root set `R` (inside the domain) is placed in the
direction's zero set, and set

* `u₁ = e` on a moving support `S` (disjoint from `R`, `e ≠ 0` on `S`), `u₁ = 0` elsewhere;
* `u₀ = 1` on a small safety set `W ⊆ Sᶜ ∖ R`, `u₀ = 0` elsewhere.

Then for EVERY scalar `γ` the codeword `γ • e` agrees with the line word `u₀ + γ • u₁` on all
of `S ∪ R` (both sides restrict to `γ·e` on `S` and to `0` on `R`), so as soon as
`a ≤ |S| + |R|` every scalar is bad: `lineBadScalars = Finset.univ`.  Meanwhile the line is
**zero-direction-safe by pure counting** — on the zero set `Sᶜ` the offset `u₀` is `0` off `W`
and `1` on `W`, so a codeword `c` matches it on at most `(k−1) + |W|` coordinates when `c ≠ 0`
(a nonzero codeword has `≤ k−1` zeros) and on exactly `|Sᶜ| − |W|` when `c = 0`; both are `< a`
under the numeric side conditions.  The saturating stratum is `t = |R| ≤ k−1 < k`:
**low-profile**, exactly the stratum this thread was asked to bound.

## Headlines (all axiom-clean, fully general in `F`, `dom`, `n`, `k`, `a`)

1. `exists_pencil_configuration` — the construction exists for every field, every injective
   domain, and every `(n, k, a)` with `1 ≤ k`, `k + 1 ≤ a`, `2a + 1 ≤ n + k` (i.e. strictly
   below unique decoding — in particular everywhere in the sub-Johnson window, see
   `forces_field_of_subJohnson`).
2. `largeZeroSafeLineBadScalarsBudgeted_forces_field` — the stack's named safe-branch residual
   `LargeZeroSafeLineBadScalarsBudgeted dom k a B` forces `B ≥ |F|`.  The weld consumers
   `mcaDeltaStar_ge_of_farLineListBudgeted_largeZeroSplit` (hypothesis `hsafe`) and
   `mcaDeltaStar_ge_of_farLineListBudgeted_lowProfileFibers` are therefore unsatisfiable at
   every useful budget: `largeZeroSplit_weld_hsafe_forces_epsilon_ge_one` shows any instance of
   the assembled consumer's budget arithmetic forces `ε* ≥ 1`.
3. `midBandSafeLineBadScalarsBudgeted_forces_field` — the mid-band residual of
   `_R2B_LargeZeroWitnessSplit` saturates as well (the construction automatically sits in the
   mid band `a < k + |S|`, because `a ≤ |S| + |R| ≤ |S| + k − 1`).
4. `uniformStrataBudget_forces_field_sub_two` — the TRUE stratum count at the low profile
   `t = k − 1` is `≥ |F| − 2` on a safe mid-band line: no stratum budget
   `N (k−1) < |F| − 2` exists.  This answers the lane's production question exactly.
5. `lowProfileFiberBudget_forces_field_at_top_profile` — the weld's localized `hlowFiber`
   hypothesis forces `M (k−1) ≥ |F|`: the field-power envelope `q^{k−t}` is EXACT at
   `t = k − 1`; the hoped-for `M t ≪ q^{k−t}` (LineListMCAWeld §9) is impossible.

## What survives (honesty)

* The construction REQUIRES `a ≤ |S| + |R| ≤ |S| + (k−1)`, i.e. direction support
  `s ≥ a − k + 1` — exactly the mid band.  The very-large-zero branch
  (`k + s ≤ a`, `_R2B_LargeZeroWitnessSplit`) is untouched: its unconditional
  threshold-choose budget stands, as do the sparse-support rate-quarter caps
  (`s ≤ 4` files).  Combined, the safe branch is now CLASSIFIED: binomially budgeted for
  `s ≤ a − k`, field-saturated (hence unusable as a `lineBadScalars` budget) for
  `s ≥ a − k + 1`.
* The construction does NOT refute the direct `mcaEvent` form of the weld's `hlow` (in
  `mcaDeltaStar_ge_of_farLineListBudgeted` itself): the pair `(0, e)` jointly explains the
  witness `S ∪ R` for every pencil scalar, so those scalars are NOT `mcaEvent`s.  Probe
  measurement (`probe_w9_lowprofile_pencil_saturation.py`, exhaustive over all `q^k` codewords
  at `n=16, k=4, a=9`, `q ∈ {17, 23}`, mid-band supports `s ∈ {6,7}`): `lineBadScalars`
  saturates to `q` while the true `mcaEvent` count on the same lines is `1 + |W| ≤ 3`.  The
  lossy step is exactly `mcaEvent_filter_subset_lineBadScalars`; any surviving line-list route
  must re-do the safe large-zero branch in the `mcaEvent` vocabulary (joint-pair exclusion is
  load-bearing), not on `lineBadScalars`.
* The refutation needs `2a + 1 ≤ n + k` — it dies exactly AT unique decoding, as it must
  (above unique decoding the per-line list is a singleton).  At rate `1/2`, `n = 16`: applies
  to `a ≤ 11` (in-window: Johnson is `√128 ≈ 11.31`), not to `a = 12`
  (`rateHalf_uniqueDecoding_boundary`).

Probe: `scripts/probes/probe_w9_lowprofile_pencil_saturation.py` (exit 0; exhaustive).
Issue #466; supersedes-as-refuted: the `hsafe`/`hlowFiber` production obligations of
`LineListMCAWeld.lean` §9 and `MidBandSafeLineBadScalarsBudgeted` of
`_R2B_LargeZeroWitnessSplit.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Frontier.W9LowProfilePencilSaturation

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.LargeZeroWitnessSplit

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ### 1. The root-pencil line -/

/-- The pencil direction: the codeword `e` restricted to the moving support `S`. -/
def pencilDirection (e : Fin n → F) (S : Finset (Fin n)) : Fin n → F :=
  fun i => if i ∈ S then e i else 0

/-- The pencil offset: the indicator word of the small safety set `W`. -/
def pencilOffset (W : Finset (Fin n)) : Fin n → F :=
  fun i => if i ∈ W then (1 : F) else 0

open Classical in
/-- **The pencil fires at every scalar.**  For every `γ`, the codeword `γ • e` agrees with the
line word `u₀ + γ • u₁` on all of `S ∪ R`: on `S` both sides are `γ · e`, on `R` both sides
are `0`. -/
theorem union_subset_agreeSet_pencil
    (e : Fin n → F) (S R W : Finset (Fin n))
    (heR : ∀ i ∈ R, e i = 0)
    (hSR : Disjoint S R) (hWS : Disjoint W S) (hWR : Disjoint W R) (γ : F) :
    S ∪ R ⊆ agreeSet (γ • e)
      (fun i => pencilOffset (n := n) (F := F) W i + γ • pencilDirection e S i) := by
  intro i hi
  rw [agreeSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases Finset.mem_union.mp hi with hiS | hiR
  · have hiW : i ∉ W := Finset.disjoint_right.mp hWS hiS
    simp only [pencilOffset, pencilDirection, if_neg hiW, if_pos hiS, Pi.smul_apply,
      smul_eq_mul, zero_add]
  · have hiW : i ∉ W := Finset.disjoint_right.mp hWR hiR
    have hiS : i ∉ S := Finset.disjoint_right.mp hSR hiR
    simp only [pencilOffset, pencilDirection, if_neg hiW, if_neg hiS, Pi.smul_apply,
      smul_eq_mul, heR i hiR, mul_zero, add_zero]

open Classical in
/-- **Total saturation.**  As soon as `a ≤ |S| + |R|`, EVERY scalar of the field is bad on the
pencil line. -/
theorem pencil_lineBadScalars_eq_univ
    (dom : Fin n ↪ F) (k a : ℕ) (e : Fin n → F) (S R W : Finset (Fin n))
    (he : e ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (heR : ∀ i ∈ R, e i = 0)
    (hSR : Disjoint S R) (hWS : Disjoint W S) (hWR : Disjoint W R)
    (ha : a ≤ S.card + R.card) :
    lineBadScalars dom k a (pencilOffset W) (pencilDirection e S) = Finset.univ := by
  refine Finset.eq_univ_iff_forall.mpr fun γ => ?_
  rw [lineBadScalars, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, γ • e, Submodule.smul_mem _ γ he, ?_⟩
  calc a ≤ S.card + R.card := ha
    _ = (S ∪ R).card := (Finset.card_union_of_disjoint hSR).symm
    _ ≤ _ := Finset.card_le_card
        (union_subset_agreeSet_pencil e S R W heR hSR hWS hWR γ)

open Classical in
/-- The pencil direction's zero set is exactly the complement of the moving support. -/
theorem directionZeroSet_pencil
    (e : Fin n → F) (S : Finset (Fin n)) (heS : ∀ i ∈ S, e i ≠ 0) :
    directionZeroSet (pencilDirection e S) = Finset.univ \ S := by
  ext i
  rw [directionZeroSet, Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨-, hz⟩
    refine ⟨Finset.mem_univ _, fun hiS => ?_⟩
    simp only [pencilDirection, if_pos hiS] at hz
    exact heS i hiS hz
  · rintro ⟨-, hiS⟩
    exact ⟨Finset.mem_univ _, by simp only [pencilDirection, if_neg hiS]⟩

open Classical in
/-- The pencil direction's moving support is exactly `S`. -/
theorem directionSupportSet_pencil
    (e : Fin n → F) (S : Finset (Fin n)) (heS : ∀ i ∈ S, e i ≠ 0) :
    directionSupportSet (pencilDirection e S) = S := by
  ext i
  rw [directionSupportSet, Finset.mem_filter]
  constructor
  · rintro ⟨-, hz⟩
    by_contra hiS
    simp only [pencilDirection, if_neg hiS] at hz
    exact hz rfl
  · intro hiS
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [pencilDirection, if_pos hiS]
    exact heS i hiS

/-- The pencil line is in the LARGE-ZERO class (not support-eligible) whenever
`a + |S| ≤ n`. -/
theorem pencil_not_supportEligible
    (a : ℕ) (e : Fin n → F) (S : Finset (Fin n))
    (heS : ∀ i ∈ S, e i ≠ 0) (hz : a + S.card ≤ n) :
    ¬ SupportEligibleLineDirection a (pencilDirection e S) := by
  intro hel
  have hlt : (directionZeroSet (pencilDirection e S)).card < a := hel
  rw [directionZeroSet_pencil e S heS] at hlt
  have hcard : (Finset.univ \ S).card = n - S.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]
  omega

open Classical in
/-- **The pencil line is zero-direction-SAFE, by pure counting.**  On the zero set `Sᶜ` the
offset is the indicator of `W`: the zero codeword matches it on `|Sᶜ| − |W|` coordinates, and
a nonzero codeword on at most `(k−1) + |W|` (a nonzero codeword has at most `k−1` zeros).
Both are `< a` under the stated numeric conditions. -/
theorem pencil_zeroDirectionSafeLine
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (e : Fin n → F) (S W : Finset (Fin n))
    (heS : ∀ i ∈ S, e i ≠ 0) (hWS : Disjoint W S)
    (hc0 : n - S.card - W.card < a) (hck : k - 1 + W.card < a) :
    ZeroDirectionSafeLine dom k a (pencilOffset W) (pencilDirection e S) := by
  intro c hc
  rw [directionZeroAgreementSet, directionZeroSet_pencil e S heS]
  by_cases hc0' : c = 0
  · subst hc0'
    have hWsub : W ⊆ Finset.univ \ S := fun i hiW =>
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, Finset.disjoint_left.mp hWS hiW⟩
    have hsub : ((Finset.univ \ S).filter
        (fun i => (0 : Fin n → F) i = pencilOffset W i)) ⊆ (Finset.univ \ S) \ W := by
      intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨hiZ, hieq⟩ := hi
      rw [Finset.mem_sdiff]
      refine ⟨hiZ, fun hiW => ?_⟩
      simp only [pencilOffset, if_pos hiW, Pi.zero_apply] at hieq
      exact zero_ne_one hieq
    have hZcard : (Finset.univ \ S).card = n - S.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset hWsub, hZcard] at hcard
    omega
  · have hzeros : (agreeSet c 0).card ≤ k - 1 :=
      rsCode_pairwise_agreeSet_card_le dom hk hc (Submodule.zero_mem _) hc0'
    have hsub : ((Finset.univ \ S).filter
        (fun i => c i = pencilOffset W i)) ⊆ agreeSet c 0 ∪ W := by
      intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨-, hieq⟩ := hi
      by_cases hiW : i ∈ W
      · exact Finset.mem_union_right _ hiW
      · refine Finset.mem_union_left _ ?_
        rw [agreeSet, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        simp only [pencilOffset, if_neg hiW] at hieq
        simpa using hieq
    have hcard := Finset.card_le_card hsub
    have hcard' := le_trans hcard (Finset.card_union_le _ _)
    omega

/-- The root stratum is LOW-PROFILE: a nonzero codeword has at most `k − 1` zeros, so
`|R| ≤ k − 1 < k`. -/
theorem pencil_root_card_le
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    (e : Fin n → F) (R : Finset (Fin n))
    (he : e ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (heR : ∀ i ∈ R, e i = 0) (hene : e ≠ 0) :
    R.card ≤ k - 1 := by
  classical
  have hsub : R ⊆ agreeSet e 0 := by
    intro i hi
    rw [agreeSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa using heR i hi⟩
  exact le_trans (Finset.card_le_card hsub)
    (rsCode_pairwise_agreeSet_card_le dom hk he (Submodule.zero_mem _) hene)

/-! ### 2. The TRUE `D(t)`: the low-profile stratum saturates the field -/

open Classical in
/-- **Stratum saturation — the answer to the lane's production question.**  On the pencil
line, the zero-agreement stratum at the LOW profile `t = |R|` contains `γ • e` for every
scalar `γ` outside the `≤ 1 + |W|` exceptional ones: `D(|R|) ≥ |F| − 1 − |W|`. -/
theorem pencil_zeroAgreementStratum_card_ge
    (dom : Fin n ↪ F) (k a : ℕ) (e : Fin n → F) (S R W : Finset (Fin n))
    (he : e ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (heRZ : ∀ i, e i = 0 ↔ i ∈ R)
    (hSR : Disjoint S R) (hWS : Disjoint W S) (hWR : Disjoint W R)
    (ha : a ≤ S.card + R.card) (hS0 : S.Nonempty) :
    Fintype.card F - (1 + W.card)
      ≤ (zeroAgreementStratum dom k a (pencilOffset W) (pencilDirection e S) R.card).card := by
  have heS : ∀ i ∈ S, e i ≠ 0 := fun i hi h0 =>
    (Finset.disjoint_left.mp hSR hi) ((heRZ i).mp h0)
  have heR : ∀ i ∈ R, e i = 0 := fun i hi => (heRZ i).mpr hi
  set badG : Finset F := insert (0 : F) (W.image fun i => (e i)⁻¹) with hbadG
  have hmem : ∀ γ ∈ Finset.univ \ badG,
      γ • e ∈ zeroAgreementStratum dom k a (pencilOffset W) (pencilDirection e S) R.card := by
    intro γ hγ
    rw [Finset.mem_sdiff] at hγ
    obtain ⟨-, hγnot⟩ := hγ
    have hγ0 : γ ≠ 0 := fun h => hγnot (h ▸ Finset.mem_insert_self _ _)
    have hγW : γ ∉ W.image fun i => (e i)⁻¹ := fun h => hγnot (Finset.mem_insert_of_mem h)
    rw [zeroAgreementStratum, Finset.mem_filter]
    constructor
    · rw [lineAppearingCodewords, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, Submodule.smul_mem _ γ he, γ, ?_⟩
      calc a ≤ S.card + R.card := ha
        _ = (S ∪ R).card := (Finset.card_union_of_disjoint hSR).symm
        _ ≤ _ := Finset.card_le_card
            (union_subset_agreeSet_pencil e S R W heR hSR hWS hWR γ)
    · have hset : directionZeroAgreementSet (γ • e) (pencilOffset W)
          (pencilDirection e S) = R := by
        ext i
        rw [directionZeroAgreementSet, directionZeroSet_pencil e S heS,
          Finset.mem_filter, Finset.mem_sdiff]
        constructor
        · rintro ⟨⟨-, hiS⟩, heq⟩
          by_cases hiW : i ∈ W
          · exfalso
            simp only [pencilOffset, if_pos hiW, Pi.smul_apply, smul_eq_mul] at heq
            exact hγW (Finset.mem_image.mpr
              ⟨i, hiW, inv_eq_of_mul_eq_one_right (by rwa [mul_comm] at heq)⟩)
          · simp only [pencilOffset, if_neg hiW, Pi.smul_apply, smul_eq_mul] at heq
            rcases mul_eq_zero.mp heq with h | h
            · exact absurd h hγ0
            · exact (heRZ i).mp h
        · intro hiR
          have hiS : i ∉ S := Finset.disjoint_right.mp hSR hiR
          have hiW : i ∉ W := Finset.disjoint_right.mp hWR hiR
          refine ⟨⟨Finset.mem_univ _, hiS⟩, ?_⟩
          simp only [pencilOffset, if_neg hiW, Pi.smul_apply, smul_eq_mul,
            (heRZ i).mpr hiR, mul_zero]
      rw [hset]
  have hinj : Set.InjOn (fun γ : F => γ • e) (Finset.univ \ badG : Finset F) := by
    intro γ hγ γ' hγ' heq
    obtain ⟨i0, hi0⟩ := hS0
    have hei0 : e i0 ≠ 0 := heS i0 hi0
    have hval := congrFun heq i0
    simp only [Pi.smul_apply, smul_eq_mul] at hval
    exact mul_right_cancel₀ hei0 hval
  have hcard := Finset.card_le_card_of_injOn _ hmem hinj
  have h1 : (Finset.univ \ badG).card = Fintype.card F - badG.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  have h2 : badG.card ≤ 1 + W.card := by
    calc badG.card ≤ (W.image fun i => (e i)⁻¹).card + 1 := Finset.card_insert_le _ _
      _ ≤ W.card + 1 := by
          have := Finset.card_image_le (s := W) (f := fun i => (e i)⁻¹)
          omega
      _ = 1 + W.card := by omega
  omega

open Classical in
/-- **Fiber saturation.**  The whole pencil `{γ • e}` sits inside the single coordinate fiber
over the root set `R`: the fiber at profile `|R| < k` has at least `|F|` elements — the
field-power envelope `q^{k−t}` is EXACT at `t = k − 1` (when `|R| = k − 1`). -/
theorem pencil_coordinateAgreementFiber_card_ge
    (dom : Fin n ↪ F) (k : ℕ) (e : Fin n → F) (S R W : Finset (Fin n))
    (he : e ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (heR : ∀ i ∈ R, e i = 0) (hWR : Disjoint W R)
    (heS : ∀ i ∈ S, e i ≠ 0) (hS0 : S.Nonempty) :
    Fintype.card F ≤ (coordinateAgreementFiber dom k (pencilOffset W) R).card := by
  have hmem : ∀ γ ∈ (Finset.univ : Finset F),
      γ • e ∈ coordinateAgreementFiber dom k (pencilOffset W) R := by
    intro γ _
    rw [coordinateAgreementFiber, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, Submodule.smul_mem _ γ he, fun i hi => ?_⟩
    have hiW : i ∉ W := Finset.disjoint_right.mp hWR hi
    simp only [pencilOffset, if_neg hiW, Pi.smul_apply, smul_eq_mul, heR i hi, mul_zero]
  have hinj : Set.InjOn (fun γ : F => γ • e) (Finset.univ : Finset F) := by
    intro γ hγ γ' hγ' heq
    obtain ⟨i0, hi0⟩ := hS0
    have hval := congrFun heq i0
    simp only [Pi.smul_apply, smul_eq_mul] at hval
    exact mul_right_cancel₀ (heS i0 hi0) hval
  calc Fintype.card F = (Finset.univ : Finset F).card := Finset.card_univ.symm
    _ ≤ _ := Finset.card_le_card_of_injOn _ hmem hinj

/-! ### 3. Existence: the configuration is constructible at EVERY sub-unique-decoding shape -/

open Polynomial in
/-- **Existence of the pencil configuration** for every field, every injective domain, and
every `(n, k, a)` with `1 ≤ k`, `k + 1 ≤ a`, `2a + 1 ≤ n + k` (strictly below unique
decoding).  Take `|R| = k − 1` domain points, `e = ∏_{j ∈ R} (X − dom j)` (so the zeros of
`e` are EXACTLY `R`), `|S| = n − a` further points, and a singleton `W`. -/
theorem exists_pencil_configuration (dom : Fin n ↪ F) {k a : ℕ}
    (hk : 1 ≤ k) (hka : k + 1 ≤ a) (h2a : 2 * a + 1 ≤ n + k) :
    ∃ (e : Fin n → F) (S R W : Finset (Fin n)),
      e ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
      (∀ i, e i = 0 ↔ i ∈ R) ∧
      Disjoint S R ∧ Disjoint W S ∧ Disjoint W R ∧ S.Nonempty ∧
      R.card = k - 1 ∧ W.card = 1 ∧
      a ≤ S.card + R.card ∧ a + S.card ≤ n ∧
      n - S.card - W.card < a ∧ k - 1 + W.card < a := by
  classical
  have han : a + 2 ≤ n := by omega
  obtain ⟨R, -, hRcard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (n := k - 1)
    (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  have hRuniv : ((Finset.univ : Finset (Fin n)) \ R).card = n - (k - 1) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ R), Finset.card_univ, Fintype.card_fin, hRcard]
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n)) \ R) (n := n - a) (by rw [hRuniv]; omega)
  have hWuniv : ((((Finset.univ : Finset (Fin n)) \ R) \ S)).card
      = n - (k - 1) - (n - a) := by
    rw [Finset.card_sdiff_of_subset hSsub, hRuniv, hScard]
  obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq
    (s := (((Finset.univ : Finset (Fin n)) \ R) \ S)) (n := 1) (by rw [hWuniv]; omega)
  set p : Polynomial F := ∏ j ∈ R, (X - C (dom j)) with hp
  have hfacne : ∀ j ∈ R, (X - C (dom j) : Polynomial F) ≠ 0 :=
    fun j _ => X_sub_C_ne_zero (dom j)
  have hpne : p ≠ 0 := Finset.prod_ne_zero_iff.mpr hfacne
  have hpdeg : p.natDegree = R.card := by
    rw [hp, Polynomial.natDegree_prod _ _ hfacne]
    simp [Polynomial.natDegree_X_sub_C]
  refine ⟨fun i => p.eval (dom i), S, R, W, ⟨p, ?_, rfl⟩, ?_, ?_, ?_, ?_, ?_,
    hRcard, hWcard, ?_, ?_, ?_, ?_⟩
  · rw [Polynomial.degree_eq_natDegree hpne, hpdeg, hRcard]
    exact_mod_cast (by omega : k - 1 < k)
  · intro i
    show p.eval (dom i) = 0 ↔ i ∈ R
    rw [hp, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
    constructor
    · rintro ⟨j, hjR, hj0⟩
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        sub_eq_zero] at hj0
      rwa [← dom.injective hj0] at hjR
    · intro hiR
      exact ⟨i, hiR, by simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]⟩
  · exact Finset.disjoint_left.mpr
      fun i hiS hiR => (Finset.mem_sdiff.mp (hSsub hiS)).2 hiR
  · exact Finset.disjoint_left.mpr
      fun i hiW hiS => (Finset.mem_sdiff.mp (hWsub hiW)).2 hiS
  · exact Finset.disjoint_left.mpr
      fun i hiW hiR => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hWsub hiW)).1).2 hiR
  · rw [← Finset.card_pos, hScard]; omega
  · rw [hScard, hRcard]; omega
  · rw [hScard]; omega
  · rw [hScard, hWcard]; omega
  · rw [hWcard]; omega

/-! ### 4. The packaged refutations -/

open Classical in
/-- **HEADLINE 1: the safe-branch budget is REFUTED at every sub-field size.**  For every
`1 ≤ k`, `k + 1 ≤ a`, `2a + 1 ≤ n + k` (all of the sub-Johnson window, see below):
`LargeZeroSafeLineBadScalarsBudgeted dom k a B` forces `B ≥ |F|`.  The weld's `hsafe`
production obligation (`mcaDeltaStar_ge_of_farLineListBudgeted_largeZeroSplit`) is therefore
unsatisfiable at every useful budget. -/
theorem largeZeroSafeLineBadScalarsBudgeted_forces_field
    (dom : Fin n ↪ F) {k a B : ℕ}
    (hk : 1 ≤ k) (hka : k + 1 ≤ a) (h2a : 2 * a + 1 ≤ n + k)
    (hB : LargeZeroSafeLineBadScalarsBudgeted dom k a B) :
    Fintype.card F ≤ B := by
  obtain ⟨e, S, R, W, he, heRZ, hSR, hWS, hWR, hS0, hRcard, hWcard, ha, hz, hc0, hck⟩ :=
    exists_pencil_configuration dom hk hka h2a
  have heS : ∀ i ∈ S, e i ≠ 0 := fun i hi h0 =>
    (Finset.disjoint_left.mp hSR hi) ((heRZ i).mp h0)
  have heR : ∀ i ∈ R, e i = 0 := fun i hi => (heRZ i).mpr hi
  have hbad := hB (pencilOffset W) (pencilDirection e S)
    (pencil_not_supportEligible a e S heS hz)
    (pencil_zeroDirectionSafeLine dom hk a e S W heS hWS hc0 hck)
  rw [pencil_lineBadScalars_eq_univ dom k a e S R W he heR hSR hWS hWR ha,
    Finset.card_univ] at hbad
  exact hbad

open Classical in
/-- Contrapositive scanner form of headline 1. -/
theorem not_largeZeroSafeLineBadScalarsBudgeted_of_lt_card
    (dom : Fin n ↪ F) {k a B : ℕ}
    (hk : 1 ≤ k) (hka : k + 1 ≤ a) (h2a : 2 * a + 1 ≤ n + k)
    (hlt : B < Fintype.card F) :
    ¬ LargeZeroSafeLineBadScalarsBudgeted dom k a B := fun hB =>
  absurd (largeZeroSafeLineBadScalarsBudgeted_forces_field dom hk hka h2a hB)
    (Nat.not_le.mpr hlt)

open Classical in
/-- Sub-Johnson coverage: strictly sub-Johnson agreement (`a² < n·k`, `k + 1 ≤ a`) satisfies
the numeric gate `2a + 1 ≤ n + k`, so the refutation covers the ENTIRE window. -/
theorem largeZeroSafeLineBadScalarsBudgeted_forces_field_of_subJohnson
    (dom : Fin n ↪ F) {k a B : ℕ}
    (hk : 1 ≤ k) (hka : k + 1 ≤ a) (hJ : a * a < n * k)
    (hB : LargeZeroSafeLineBadScalarsBudgeted dom k a B) :
    Fintype.card F ≤ B := by
  have h2a : 2 * a < n + k := ProximityGap.LowProfileFiber.two_mul_lt_add_of_sq_lt hJ
  exact largeZeroSafeLineBadScalarsBudgeted_forces_field dom hk hka (by omega) hB

open Classical in
/-- **HEADLINE 2: the mid-band residual saturates.**  The pencil line automatically sits in
the mid band (`a < k + |S|` because `a ≤ |S| + |R| ≤ |S| + k − 1`), so
`MidBandSafeLineBadScalarsBudgeted dom k a B` (`_R2B_LargeZeroWitnessSplit`) forces
`B ≥ |F|` as well: the `hlow` residual left open by the witness split cannot be closed. -/
theorem midBandSafeLineBadScalarsBudgeted_forces_field
    (dom : Fin n ↪ F) {k a B : ℕ}
    (hk : 1 ≤ k) (hka : k + 1 ≤ a) (h2a : 2 * a + 1 ≤ n + k)
    (hB : MidBandSafeLineBadScalarsBudgeted dom k a B) :
    Fintype.card F ≤ B := by
  obtain ⟨e, S, R, W, he, heRZ, hSR, hWS, hWR, hS0, hRcard, hWcard, ha, hz, hc0, hck⟩ :=
    exists_pencil_configuration dom hk hka h2a
  have heS : ∀ i ∈ S, e i ≠ 0 := fun i hi h0 =>
    (Finset.disjoint_left.mp hSR hi) ((heRZ i).mp h0)
  have heR : ∀ i ∈ R, e i = 0 := fun i hi => (heRZ i).mpr hi
  have hmid : a < k + (directionSupportSet (pencilDirection e S)).card := by
    rw [directionSupportSet_pencil e S heS]
    omega
  have hbad := hB (pencilOffset W) (pencilDirection e S)
    (pencil_not_supportEligible a e S heS hz) hmid
    (pencil_zeroDirectionSafeLine dom hk a e S W heS hWS hc0 hck)
  rw [pencil_lineBadScalars_eq_univ dom k a e S R W he heR hSR hWS hWR ha,
    Finset.card_univ] at hbad
  exact hbad

open Classical in
/-- **HEADLINE 3: the TRUE `D(t)` at the low profile `t = k − 1` is `≥ |F| − 2`.**  Any
uniform stratum budget on the safe large-zero branch
(`UniformLargeZeroSafeZeroAgreementStrataCardBudgeted`) must allow `N (k−1) ≥ |F| − 2`.
This is the exact answer to this lane's production question: the low-profile stratum count
is NOT sub-`q` — it is `q` up to an additive constant. -/
theorem uniformStrataBudget_forces_field_sub_two
    (dom : Fin n ↪ F) {k a : ℕ} {N : ℕ → ℕ}
    (hk : 1 ≤ k) (hka : k + 1 ≤ a) (h2a : 2 * a + 1 ≤ n + k)
    (hN : UniformLargeZeroSafeZeroAgreementStrataCardBudgeted dom k a N) :
    Fintype.card F - 2 ≤ N (k - 1) := by
  obtain ⟨e, S, R, W, he, heRZ, hSR, hWS, hWR, hS0, hRcard, hWcard, ha, hz, hc0, hck⟩ :=
    exists_pencil_configuration dom hk hka h2a
  have heS : ∀ i ∈ S, e i ≠ 0 := fun i hi h0 =>
    (Finset.disjoint_left.mp hSR hi) ((heRZ i).mp h0)
  have hstrata := hN (pencilOffset W) (pencilDirection e S)
    (pencil_not_supportEligible a e S heS hz)
    (pencil_zeroDirectionSafeLine dom hk a e S W heS hWS hc0 hck)
    (k - 1) (by omega)
  have hge := pencil_zeroAgreementStratum_card_ge dom k a e S R W he heRZ hSR hWS hWR ha hS0
  rw [hRcard] at hge
  rw [hWcard] at hge
  omega

open Classical in
/-- **HEADLINE 4: the weld's localized low-profile fiber hypothesis (`hlowFiber` of
`mcaDeltaStar_ge_of_farLineListBudgeted_lowProfileFibers`) forces `M (k−1) ≥ |F|`.**  The
field-power envelope `q^{k−t}` (shown satisfiable in `lowProfileFiber_obligation_satisfiable`)
is EXACT at the top low profile: the open production question "is `M t ≪ q^{k−t}` possible on
low fibers?" (LineListMCAWeld §9) is answered NO at `t = k − 1`. -/
theorem lowProfileFiberBudget_forces_field_at_top_profile
    (dom : Fin n ↪ F) {k a : ℕ} {M : ℕ → ℕ}
    (hk : 1 ≤ k) (hka : k + 1 ≤ a) (h2a : 2 * a + 1 ≤ n + k)
    (hfib : ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
      ZeroDirectionSafeLine dom k a u₀ u₁ →
        ∀ t : ℕ, t < a → t < k → ∀ Sf ∈ (directionZeroSet u₁).powersetCard t,
          (coordinateAgreementFiber dom k u₀ Sf).card ≤ M t) :
    Fintype.card F ≤ M (k - 1) := by
  obtain ⟨e, S, R, W, he, heRZ, hSR, hWS, hWR, hS0, hRcard, hWcard, ha, hz, hc0, hck⟩ :=
    exists_pencil_configuration dom hk hka h2a
  have heS : ∀ i ∈ S, e i ≠ 0 := fun i hi h0 =>
    (Finset.disjoint_left.mp hSR hi) ((heRZ i).mp h0)
  have heR : ∀ i ∈ R, e i = 0 := fun i hi => (heRZ i).mpr hi
  have hRmem : R ∈ (directionZeroSet (pencilDirection e S)).powersetCard (k - 1) := by
    rw [directionZeroSet_pencil e S heS, Finset.mem_powersetCard]
    exact ⟨fun i hiR => Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, Finset.disjoint_right.mp hSR hiR⟩, hRcard⟩
  have hcap := hfib (pencilOffset W) (pencilDirection e S)
    (pencil_not_supportEligible a e S heS hz)
    (pencil_zeroDirectionSafeLine dom hk a e S W heS hWS hc0 hck)
    (k - 1) (by omega) (by omega) R hRmem
  exact le_trans
    (pencil_coordinateAgreementFiber_card_ge dom k e S R W he heR hWR heS hS0) hcap

open Classical in
/-- **HEADLINE 5: the assembled weld consumer cannot certify any `ε* < 1` through its safe
branch.**  If `hsafe` and the budget arithmetic of
`mcaDeltaStar_ge_of_farLineListBudgeted_largeZeroSplit` both hold, then `ε* ≥ 1`. -/
theorem largeZeroSplit_weld_hsafe_forces_epsilon_ge_one
    (dom : Fin n ↪ F) {k a : ℕ} {Bfar Bsafe Bunsafe : ℕ} {εstar : ℝ≥0∞}
    (hk : 1 ≤ k) (hka : k + 1 ≤ a) (h2a : 2 * a + 1 ≤ n + k)
    (hsafe : LargeZeroSafeLineBadScalarsBudgeted dom k a Bsafe)
    (hBudget : ((max Bfar (max Bsafe Bunsafe) : ℕ) : ℝ≥0∞)
      / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    1 ≤ εstar := by
  have hq : Fintype.card F ≤ Bsafe :=
    largeZeroSafeLineBadScalarsBudgeted_forces_field dom hk hka h2a hsafe
  have hle : Fintype.card F ≤ max Bfar (max Bsafe Bunsafe) :=
    le_trans hq (le_trans (le_max_left _ _) (le_max_right _ _))
  have hq0 : (Fintype.card F : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hqt : (Fintype.card F : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc (1 : ℝ≥0∞) = (Fintype.card F : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
        (ENNReal.div_self hq0 hqt).symm
    _ ≤ ((max Bfar (max Bsafe Bunsafe) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
        ENNReal.div_le_div_right (by exact_mod_cast hle) _
    _ ≤ εstar := hBudget

/-! ### 5. Numeric gates at the campaign's concrete shapes -/

/-- The rate-quarter shape of the sibling support-climbing program (`n = 16`, `k = 4`,
`a = 9`) satisfies the refutation gate: the safe-branch program cannot close supports
`s ≥ a − k + 1 = 6`. -/
theorem rateQuarter_gate : 1 ≤ 4 ∧ 4 + 1 ≤ 9 ∧ 2 * 9 + 1 ≤ 16 + 4 := by norm_num

/-- The rate-half in-window shape (`n = 16`, `k = 8`, `a = 11 < √128 ≈ 11.31`) satisfies the
gate: the refutation covers the rate-half re-bracket window. -/
theorem rateHalf_inWindow_gate : 1 ≤ 8 ∧ 8 + 1 ≤ 11 ∧ 2 * 11 + 1 ≤ 16 + 8 := by norm_num

/-- Honesty: the gate fails exactly AT unique decoding (`a = 12` at rate half, `n = 16`), as
it must — above unique decoding the per-line list is a singleton. -/
theorem rateHalf_uniqueDecoding_boundary : ¬ (2 * 12 + 1 ≤ 16 + 8) := by norm_num

end ProximityGap.Frontier.W9LowProfilePencilSaturation

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.W9LowProfilePencilSaturation.union_subset_agreeSet_pencil
#print axioms ProximityGap.Frontier.W9LowProfilePencilSaturation.pencil_lineBadScalars_eq_univ
#print axioms ProximityGap.Frontier.W9LowProfilePencilSaturation.directionZeroSet_pencil
#print axioms ProximityGap.Frontier.W9LowProfilePencilSaturation.directionSupportSet_pencil
#print axioms ProximityGap.Frontier.W9LowProfilePencilSaturation.pencil_not_supportEligible
#print axioms ProximityGap.Frontier.W9LowProfilePencilSaturation.pencil_zeroDirectionSafeLine
#print axioms ProximityGap.Frontier.W9LowProfilePencilSaturation.pencil_root_card_le
#print axioms ProximityGap.Frontier.W9LowProfilePencilSaturation.pencil_zeroAgreementStratum_card_ge
#print axioms ProximityGap.Frontier.W9LowProfilePencilSaturation.pencil_coordinateAgreementFiber_card_ge
#print axioms ProximityGap.Frontier.W9LowProfilePencilSaturation.exists_pencil_configuration
#print axioms ProximityGap.Frontier.W9LowProfilePencilSaturation.largeZeroSafeLineBadScalarsBudgeted_forces_field
#print axioms ProximityGap.Frontier.W9LowProfilePencilSaturation.not_largeZeroSafeLineBadScalarsBudgeted_of_lt_card
#print axioms ProximityGap.Frontier.W9LowProfilePencilSaturation.largeZeroSafeLineBadScalarsBudgeted_forces_field_of_subJohnson
#print axioms ProximityGap.Frontier.W9LowProfilePencilSaturation.midBandSafeLineBadScalarsBudgeted_forces_field
#print axioms ProximityGap.Frontier.W9LowProfilePencilSaturation.uniformStrataBudget_forces_field_sub_two
#print axioms ProximityGap.Frontier.W9LowProfilePencilSaturation.lowProfileFiberBudget_forces_field_at_top_profile
#print axioms ProximityGap.Frontier.W9LowProfilePencilSaturation.largeZeroSplit_weld_hsafe_forces_epsilon_ge_one

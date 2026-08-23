/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26WitnessSpread

/-!
# The level-`j` sub-ceiling ladder: bad-line families strictly below the KKH26 ceiling

The in-tree KKH26 witness (`KKH26WitnessSpread.lean`) runs the sign-subset construction at
`Y = X^m` on the `n = 2^μ·m`-point smooth domain `⟨g⟩`: the stack `(X^{rm}, X^{(r−1)m})` has
`≥ 2^r·C(2^{μ−1}, r)` bad scalars at the **ceiling radius** `1 − r/2^μ`, witnessed by the
order-`2^μ` subgroup fibers.  This file formalizes the **level-`j` family** (`j ≥ 1`):
substituting `Y = X^{2^j·m}` runs the *same* construction on the order-`2^{μ−j}` subgroup
`⟨g^{2^j·m}⟩` against the *same* degree-`(r−2)m` code, producing bad lines at radius

  `δ_j = 1 − r'/2^{μ−j}`  **strictly below the ceiling**,

with `≥ 2^{r'}·C(2^{μ−j−1}, r')` bad scalars.  The construction is compatible with the code
iff `(r'−2)·2^j ≤ r−2` (the gap-expansion remainder stays inside the code) **and**
`r−2 < (r'−1)·2^j` (the direction `X^{(r'−1)·2^j·m}` is *not* itself a codeword — otherwise
the joint pair `(q − γ·u₁, u₁)` explains every scalar and the line is good); together these
force the **unique per-level rung** `r'_j = ⌊(r−2)/2^j⌋ + 2`.

## The envelope (the staircase law this file proves the bad side of)

For the degree-`(r−2)m` code, the level-`j` rungs give the two-dimensional staircase

  `δ*(C, ε*) ≤ min { 1 − r'_j/2^{μ−j} : level j valid, ε*·p < 2^{r'_j}·C(2^{μ−j−1}, r'_j) }`

— the deepest biting level wins.  Probe (`scripts/probes/probe_subceiling_envelope.py`,
all-exact, three-checker cross-validated):

* the subset-sum family is the **entire** bad set of the level-`j` stack at its radius
  (`0` extra bad scalars in every exhaustive candidate sweep), and its exact size obeys the
  `TwoPowerSubsetSumSpectrum` law `N(μ−j, r'_j)` at every tested prime (`97`, `12289`);
* at the landed pin instances the level-`j ≥ 1` counts sit strictly below the band bottom
  `C(n, d+2)/2` (e.g. `40 < 910` at `n = 16, d = 2`), so the proven pins are untouched —
  the landed bands live exactly where the deeper levels are too small to bite;
* at the F5/F17 granularity pins the family is parameter-vacuous (no lemma-regime rung).

Concretely, at `n = 16, p = 12289` this file lands the **first sub-ceiling upper bounds**:
for the dimension-three code (`d = 2`, the landed `δ* = 3/4` pin family) every budget
`ε* < 32/p` forces `δ* ≤ 5/8 < 3/4` (`subceiling_F12289_n16_d2`), and `ε* < 4/p` forces
`δ* ≤ 1/2` (`subceiling_F12289_n16_d2_level2`); for the sub-max-rate `r = 6` slice (`d = 4`,
where the level-0 pin band is empty) every `ε* < 16/p` forces `δ* ≤ 1/2 < 5/8`
(`subceiling_F12289_n16_d4`) — the machine-checked form of the `(μ = 4, r = 6)` attack-round
numerics.  Pinning these rungs (matching good side ≤ `K_j` at the next threshold) is open:
the in-tree ownership engine gives `C(n, d+2)/2`, a factor `≈ 28` above the level-1 budget
edge at the first biting instance, while the probed true worst-stack count there is `1`.

## Main results

* `subceiling_ca_failure` — the degree-decoupled far-word step: the direction
  `X^{(r−1)m}` agrees with no degree-≤`D` polynomial on `r·m` domain points when
  `D < (r−1)m`.
* `subceiling_epsMCA_lower_bound` — **the degree-decoupled engine**: the KKH26 witness
  spread against the degree-`D` code, for any `(r−2)m ≤ D < (r−1)m`.
* `levelJ_epsMCA_lower_bound` — **the level-`j` family**: the engine instantiated on the
  `2^j`-fold sub-tower, generalizing the in-tree `kkh26_epsMCA_lower_bound` (= `j = 0`).
* `mcaDeltaStar_le_subceiling` — **the sub-ceiling `δ*` upper bound** at any budget below
  the level-`j` count.
* `subceiling_radius_lt_ceiling` — for `j ≥ 1` the level-`j` radius is *strictly* below
  the KKH26 ceiling: the bound strictly improves `kkh26_mcaDeltaStar_le` wherever it bites.
* `subceiling_F12289_n16_d2`, `subceiling_F12289_n16_d2_level2`,
  `subceiling_F12289_n16_d4` — the first concrete sub-ceiling instances (see above).
* `levelOne_count_lt_band_bottom_n16_d2` — pin safety at the first biting instance: the
  level-1 count sits below the landed band bottom, so the `δ* = 3/4` pin is untouched.

## References

* [KKH26] D. Krachun, S. Kazanin, U. Haböck, *Failure of proximity gaps close to capacity*,
  ePrint 2026/782.
-/

open Polynomial Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ArkLib.ProximityGap.KKH26

/-! ### The degree-decoupled far-word step -/

/-- **Correlated-agreement failure, degree-decoupled.**  The direction word
`u₁ = X^{(r−1)m}` agrees with (the evaluation of) a polynomial of degree ≤ `D` on at most
`(r−1)·m < r·m` points of the domain, provided `D < (r−1)·m` — so no agreement set of size
`≥ r·m` exists.  At `D = (r−2)·m` this is the in-tree `kkh26_ca_failure`; the decoupling
lets the *same* direction defeat every code degree strictly below `(r−1)·m`. -/
theorem subceiling_ca_failure {p : ℕ} [Fact p.Prime] {g : ZMod p} {n m r D : ℕ}
    (hm : 1 ≤ m) (hD : D < (r - 1) * m)
    (S : Finset (ZMod p)) (hSH : S ⊆ (Finset.range n).image (fun i => g ^ i))
    (hScard : r * m ≤ S.card)
    (q : Polynomial (ZMod p)) (hq : q.natDegree ≤ D) :
    ¬ (∀ x ∈ S, x ^ ((r - 1) * m) = q.eval x) := by
  classical
  intro hagree
  have hsub : S ⊆ ((Finset.range n).image (fun i => g ^ i)).filter
      (fun x => x ^ ((r - 1) * m) = q.eval x) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hSH hx, hagree x hx⟩
  have h1 : r * m ≤ (r - 1) * m :=
    le_trans hScard (le_trans (Finset.card_le_card hsub)
      (farword_agreement_le _ hD q hq))
  have h2 : (r - 1) * m < r * m := by
    have hr1 : r - 1 < r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h; omega
      · omega
    exact Nat.mul_lt_mul_of_lt_of_le hr1 le_rfl (by omega)
  omega

/-- Injectivity of `i ↦ g^i` below the order of `g` (local copy of the `private` helper in
`KKH26WitnessSpread.lean`). -/
private lemma pow_inj_below_order' {F : Type*} [Field F] {h : F} (h0 : h ≠ 0) {N : ℕ}
    (hN : orderOf h = N) :
    ∀ i, i < N → ∀ j, j < N → h ^ i = h ^ j → i = j := by
  have main : ∀ i j, i ≤ j → j < N → h ^ i = h ^ j → i = j := by
    intro i j hij hj heq
    have hadd : i + (j - i) = j := by omega
    have h2 : h ^ i * h ^ (j - i) = h ^ i * 1 := by
      rw [mul_one, ← pow_add, hadd, heq]
    have h3 : h ^ (j - i) = 1 := mul_left_cancel₀ (pow_ne_zero i h0) h2
    have h4 : N ∣ j - i := hN ▸ orderOf_dvd_of_pow_eq_one h3
    have h5 : j - i = 0 :=
      Nat.eq_zero_of_dvd_of_lt h4 (lt_of_le_of_lt (Nat.sub_le j i) hj)
    omega
  intro i hi j hj heq
  rcases le_total i j with hle | hle
  · exact main i j hle hj heq
  · exact (main j i hle hi heq.symm).symm

/-! ### The degree-decoupled engine -/

open Classical in
/-- **The degree-decoupled witness spread.**  The KKH26 sign-subset construction at
`Y = X^m` on the `2^μ·m`-point domain produces `≥ 2^r·C(2^{μ−1}, r)` bad scalars at radius
`1 − r/2^μ` against the degree-`D` evaluation code, for **any** `D` in the compatibility
window `(r−2)·m ≤ D < (r−1)·m`: the lower edge keeps the gap-expansion remainder inside the
code, the upper edge keeps the direction word outside it.  At `D = (r−2)·m` this is exactly
the in-tree `kkh26_epsMCA_lower_bound`; instantiated at `(μ−j, 2^j·m)` it yields the
level-`j` sub-ceiling family (`levelJ_epsMCA_lower_bound`). -/
theorem subceiling_epsMCA_lower_bound {p n : ℕ} [Fact p.Prime] [NeZero n] {μ m r D : ℕ}
    (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1))
    (hD₁ : (r - 2) * m ≤ D) (hD₂ : D < (r - 1) * m) :
    ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)
      ≤ epsMCA (F := ZMod p) (evalCode g n D)
          (1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ)) := by
  classical
  subst hn
  -- basic positivity and order bookkeeping
  have hm0 : m ≠ 0 := by omega
  have hs1 : (1 : ℕ) ≤ 2 ^ μ := Nat.one_le_two_pow
  have hg0 : g ≠ 0 := by
    rintro rfl
    have h1 : (0 : ZMod p) ^ (2 ^ μ * m) = 1 := by
      rw [← hg]; exact pow_orderOf_eq_one 0
    rw [zero_pow (Nat.mul_ne_zero (by positivity) hm0)] at h1
    exact zero_ne_one h1
  have hgmord : orderOf (g ^ m) = 2 ^ μ := by
    have h1 : (g ^ m) ^ (2 ^ μ) = 1 := by
      rw [← pow_mul, mul_comm m (2 ^ μ), ← hg]; exact pow_orderOf_eq_one g
    have h2 : orderOf (g ^ m) ∣ 2 ^ μ := orderOf_dvd_of_pow_eq_one h1
    have h3 : g ^ (m * orderOf (g ^ m)) = 1 := by
      rw [pow_mul]; exact pow_orderOf_eq_one (g ^ m)
    have h4 : 2 ^ μ * m ∣ m * orderOf (g ^ m) := hg ▸ orderOf_dvd_of_pow_eq_one h3
    rw [mul_comm (2 ^ μ) m] at h4
    have h5 : 2 ^ μ ∣ orderOf (g ^ m) :=
      (Nat.mul_dvd_mul_iff_left (by omega : 0 < m)).mp h4
    exact Nat.dvd_antisymm h2 h5
  have hprim : IsPrimitiveRoot (g ^ m) (2 ^ μ) := by
    have h := IsPrimitiveRoot.orderOf (g ^ m)
    rwa [hgmord] at h
  -- Lemma 1: many distinct sums of r distinct elements of G = ⟨g^m⟩
  have hlem1 := kkh26_lemma1 hμ hprim hp hr
  set Gsub : Finset (ZMod p) :=
    (Finset.range (2 ^ μ)).image (fun i => (g ^ m) ^ i) with hGsub
  set sums : Finset (ZMod p) :=
    (Gsub.powersetCard r).image (fun T => ∑ x ∈ T, x) with hsums
  -- the word stack of the bad line
  set u : WordStack (ZMod p) (Fin 2) (Fin (2 ^ μ * m)) :=
    ![fun i => (g ^ (i : ℕ)) ^ (r * m), fun i => (g ^ (i : ℕ)) ^ ((r - 1) * m)] with hu
  -- the bad-scalar set
  set Λ : Finset (ZMod p) := sums.image (fun w => -w) with hΛ
  have hΛcard : (2 ^ r * (2 ^ (μ - 1)).choose r) ≤ Λ.card := by
    rw [hΛ, Finset.card_image_of_injective _ neg_injective]
    exact hlem1
  -- every λ ∈ Λ is a bad scalar: mcaEvent fires with the fiber witness
  have hbad : ∀ γ ∈ Λ, mcaEvent (evalCode g (2 ^ μ * m) D)
      (1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ)) (u 0) (u 1) γ := by
    intro γ hγ
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hγ
    obtain ⟨T, hT, hTsum⟩ := Finset.mem_image.mp hw
    obtain ⟨hTG, hTcard⟩ := Finset.mem_powersetCard.mp hT
    obtain ⟨q, hqdeg, hqagree⟩ :=
      badline_pointwise_agreement hm T (by omega : 2 ≤ T.card)
    rw [hTcard] at hqdeg hqagree
    -- the fiber witness set, at index level
    set S : Finset (Fin (2 ^ μ * m)) :=
      Finset.univ.filter (fun i => (g ^ (i : ℕ)) ^ m ∈ T) with hSdef
    -- index-level and domain-level fibers have the same cardinality
    have himg : (Finset.univ : Finset (Fin (2 ^ μ * m))).image
          (fun i : Fin (2 ^ μ * m) => g ^ (i : ℕ))
        = (Finset.range (2 ^ μ * m)).image (fun i => g ^ i) := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_image.mpr ⟨(i : ℕ), Finset.mem_range.mpr i.isLt, rfl⟩
      · intro hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_image.mpr ⟨⟨i, Finset.mem_range.mp hi⟩, Finset.mem_univ _, rfl⟩
    have hSimg : S.image (fun i : Fin (2 ^ μ * m) => g ^ (i : ℕ))
        = ((Finset.range (2 ^ μ * m)).image (fun i => g ^ i)).filter
            (fun x => x ^ m ∈ T) := by
      rw [← himg, Finset.filter_image]
    have hScard : S.card = m * r := by
      have h1 : (S.image (fun i : Fin (2 ^ μ * m) => g ^ (i : ℕ))).card = S.card :=
        Finset.card_image_of_injOn (fun i _ j _ hij =>
          Fin.ext (pow_inj_below_order' hg0 hg _ i.isLt _ j.isLt hij))
      rw [← h1, hSimg, fiber_count hm hs1 hg T hTG, hTcard]
    refine ⟨S, ?_, ⟨fun i => q.eval (g ^ (i : ℕ)), ⟨q, le_trans hqdeg hD₁, fun _ => rfl⟩,
      ?_⟩, ?_⟩
    · -- |S| ≥ (1 − δ)·n
      have hcardF : (Fintype.card (Fin (2 ^ μ * m)) : ℝ≥0) = ((2 ^ μ * m : ℕ) : ℝ≥0) := by
        rw [Fintype.card_fin]
      have hrs1 : (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : (r : ℝ≥0) ≤ ((2 ^ μ : ℕ) : ℝ≥0) := by
          exact_mod_cast le_trans hr (Nat.pow_le_pow_right (by omega) (by omega))
        simpa [Nat.cast_pow] using this
      have h1δ : (1 : ℝ≥0) - (1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ))
          = (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := tsub_tsub_cancel_of_le hrs1
      rw [hScard, hcardF, h1δ]
      have harith : ((r : ℝ≥0) / ((2 : ℝ≥0) ^ μ)) * ((2 ^ μ * m : ℕ) : ℝ≥0)
          = ((m * r : ℕ) : ℝ≥0) := by
        push_cast
        rw [div_mul_eq_mul_div, mul_comm ((r : ℝ≥0)) _, mul_comm ((2 : ℝ≥0) ^ μ) _,
          mul_assoc, mul_div_assoc,
          mul_div_cancel_left₀ _ (by positivity : ((2 : ℝ≥0) ^ μ) ≠ 0)]
      rw [harith]
    · -- the line point agrees with the codeword on S
      intro i hi
      have hxm : (g ^ (i : ℕ)) ^ m ∈ T := (Finset.mem_filter.mp hi).2
      have := hqagree (g ^ (i : ℕ)) hxm
      rw [hTsum] at this
      rw [hu]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
      linear_combination -this
    · -- no joint pair: the direction word is far (degree-decoupled far-word step)
      rintro ⟨v₀, _, v₁, hv₁, hpair⟩
      obtain ⟨q₁, hq₁deg, hq₁⟩ := hv₁
      have hS'H : S.image (fun i : Fin (2 ^ μ * m) => g ^ (i : ℕ))
          ⊆ (Finset.range (2 ^ μ * m)).image (fun i => g ^ i) := by
        rw [hSimg]
        exact Finset.filter_subset _ _
      have hS'card : r * m ≤ (S.image (fun i : Fin (2 ^ μ * m) => g ^ (i : ℕ))).card := by
        rw [hSimg, fiber_count hm hs1 hg T hTG, hTcard, mul_comm]
      refine subceiling_ca_failure (g := g) (n := 2 ^ μ * m) hm hD₂ _ hS'H hS'card
        q₁ hq₁deg ?_
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have h1 : v₁ i = u 1 i := (hpair i hi).2
      have h2 : v₁ i = q₁.eval (g ^ (i : ℕ)) := hq₁ i
      rw [hu] at h1
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
      rw [← h2, h1]
  -- feed the spread into the in-tree lower-bound engine
  have hengine := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (F := ZMod p) (evalCode g (2 ^ μ * m) D)
    (1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ)) u Λ hbad
  rw [ZMod.card p] at hengine
  refine le_trans ?_ hengine
  exact ENNReal.div_le_div_right (by exact_mod_cast hΛcard) _

/-! ### The level-`j` family -/

open Classical in
/-- **The level-`j` sub-ceiling family.**  For the degree-`(r−2)·m` code on the
`n = 2^μ·m`-point smooth domain, the sign-subset construction run on the order-`2^{μ−j}·m`
sub-tower (`Y = X^{2^j·m}`) produces, above the *level* prime threshold (weaker than the
level-0 one),

  `ε_mca(C, 1 − r'/2^{μ−j}) ≥ 2^{r'}·C(2^{μ−j−1}, r') / p`

for any rung `r'` in the compatibility window `(r'−2)·2^j ≤ r−2 < (r'−1)·2^j` (which forces
the unique `r' = ⌊(r−2)/2^j⌋ + 2`).  At `j = 0` (where `r' = r`) this is exactly the
in-tree `kkh26_epsMCA_lower_bound`; for `j ≥ 1` the radius is strictly below the KKH26
ceiling `1 − r/2^μ` (`subceiling_radius_lt_ceiling`). -/
theorem levelJ_epsMCA_lower_bound {p n : ℕ} [Fact p.Prime] [NeZero n] {μ m j r r' : ℕ}
    (hj : j + 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ (μ - j)) ^ 2 ^ (μ - j - 1) < p)
    (hr'2 : 2 ≤ r') (hr' : r' ≤ 2 ^ (μ - j - 1))
    (hrung₁ : (r' - 2) * 2 ^ j ≤ r - 2) (hrung₂ : r - 2 < (r' - 1) * 2 ^ j) :
    ((2 ^ r' * (2 ^ (μ - j - 1)).choose r' : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)
      ≤ epsMCA (F := ZMod p) (evalCode g n ((r - 2) * m))
          (1 - (r' : ℝ≥0) / ((2 : ℝ≥0) ^ (μ - j))) := by
  have hpow : (2 : ℕ) ^ (μ - j) * 2 ^ j = 2 ^ μ := by
    rw [← pow_add]
    congr 1
    omega
  have hm' : 1 ≤ 2 ^ j * m := by
    have h1 : (1 : ℕ) ≤ 2 ^ j := Nat.one_le_two_pow
    simpa using Nat.mul_le_mul h1 hm
  refine subceiling_epsMCA_lower_bound (μ := μ - j) (m := 2 ^ j * m) (r := r')
    (D := (r - 2) * m) (by omega) hm' ?_ ?_ hp hr'2 hr' ?_ ?_
  · rw [hn, ← hpow, mul_assoc]
  · rw [hg, ← hpow, mul_assoc]
  · calc (r' - 2) * (2 ^ j * m) = ((r' - 2) * 2 ^ j) * m := by ring
    _ ≤ (r - 2) * m := Nat.mul_le_mul_right m hrung₁
  · calc (r - 2) * m < ((r' - 1) * 2 ^ j) * m :=
        Nat.mul_lt_mul_of_lt_of_le hrung₂ le_rfl (by omega)
    _ = (r' - 1) * (2 ^ j * m) := by ring

open Classical in
/-- **The sub-ceiling `δ*` upper bound.**  At any budget `ε*` strictly below the level-`j`
bad-scalar mass `2^{r'}·C(2^{μ−j−1}, r')/p`, the MCA threshold of the degree-`(r−2)·m` code
is at most the level-`j` radius `1 − r'/2^{μ−j}` — for `j ≥ 1` strictly below the KKH26
ceiling `1 − r/2^μ`, hence strictly improving `kkh26_mcaDeltaStar_le` wherever it bites. -/
theorem mcaDeltaStar_le_subceiling {p n : ℕ} [Fact p.Prime] [NeZero n] {μ m j r r' : ℕ}
    (hj : j + 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ (μ - j)) ^ 2 ^ (μ - j - 1) < p)
    (hr'2 : 2 ≤ r') (hr' : r' ≤ 2 ^ (μ - j - 1))
    (hrung₁ : (r' - 2) * 2 ^ j ≤ r - 2) (hrung₂ : r - 2 < (r' - 1) * 2 ^ j)
    (εstar : ℝ≥0∞)
    (hεstar : εstar < ((2 ^ r' * (2 ^ (μ - j - 1)).choose r' : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
        (evalCode g n ((r - 2) * m)) εstar
      ≤ 1 - (r' : ℝ≥0) / ((2 : ℝ≥0) ^ (μ - j)) :=
  ProximityGap.MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hεstar
      (levelJ_epsMCA_lower_bound hj hm hn hg hp hr'2 hr' hrung₁ hrung₂))

/-! ### Strictness: the level-`j ≥ 1` radius sits strictly below the ceiling -/

/-- **Strict sub-ceiling separation.**  For every level `j ≥ 1`, the rung compatibility
window `r − 2 < (r'−1)·2^j` already forces `r < r'·2^j`, hence the level-`j` radius
`1 − r'/2^{μ−j}` is *strictly* below the KKH26 ceiling `1 − r/2^μ`: the sub-ceiling bound
is a strict improvement at every budget where it applies. -/
theorem subceiling_radius_lt_ceiling {μ j r r' : ℕ} (hj1 : 1 ≤ j) (hj : j + 1 ≤ μ)
    (hr'2 : 2 ≤ r') (hr' : r' ≤ 2 ^ (μ - j - 1))
    (hrung₂ : r - 2 < (r' - 1) * 2 ^ j) (hr2 : 2 ≤ r) :
    (1 : ℝ≥0) - (r' : ℝ≥0) / ((2 : ℝ≥0) ^ (μ - j))
      < 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  -- the ℕ core: `r < r'·2^j`
  have h2j : (2 : ℕ) ≤ 2 ^ j := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
  have hAB : 2 ^ j ≤ r' * 2 ^ j := by
    have h1 : 1 * 2 ^ j ≤ r' * 2 ^ j := Nat.mul_le_mul_right _ (by omega)
    simpa using h1
  have hsub : (r' - 1) * 2 ^ j = r' * 2 ^ j - 2 ^ j := by
    rw [Nat.sub_mul, one_mul]
  rw [hsub] at hrung₂
  have hnat : r < r' * 2 ^ j := by omega
  -- the radius comparison, through ℝ
  have ha1 : (r' : ℝ≥0) / ((2 : ℝ≥0) ^ (μ - j)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have h1 : (r' : ℕ) ≤ 2 ^ (μ - j) :=
      le_trans hr' (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : ((r' : ℕ) : ℝ≥0) ≤ ((2 ^ (μ - j) : ℕ) : ℝ≥0) := by exact_mod_cast h1
    simpa [Nat.cast_pow] using h2
  have hb_lt : (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) < (r' : ℝ≥0) / ((2 : ℝ≥0) ^ (μ - j)) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have hcast : (r : ℝ≥0) < (r' : ℝ≥0) * (2 : ℝ≥0) ^ j := by
      have : ((r : ℕ) : ℝ≥0) < ((r' * 2 ^ j : ℕ) : ℝ≥0) := by exact_mod_cast hnat
      simpa [Nat.cast_mul, Nat.cast_pow] using this
    calc (r : ℝ≥0) * (2 : ℝ≥0) ^ (μ - j)
        < ((r' : ℝ≥0) * (2 : ℝ≥0) ^ j) * (2 : ℝ≥0) ^ (μ - j) :=
          mul_lt_mul_of_pos_right hcast (by positivity)
      _ = (r' : ℝ≥0) * (2 : ℝ≥0) ^ μ := by
          rw [mul_assoc, ← pow_add]
          congr 2
          omega
  have hb1 : (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) ≤ 1 := le_trans hb_lt.le ha1
  rw [← NNReal.coe_lt_coe, NNReal.coe_sub ha1, NNReal.coe_sub hb1]
  have h := NNReal.coe_lt_coe.mpr hb_lt
  linarith

/-! ### The first concrete sub-ceiling instances (`n = 16`, `p = 12289`) -/

section Concrete12289

local instance fact_prime_12289' : Fact (Nat.Prime 12289) := ⟨by norm_num⟩

/-- `4134` has multiplicative order `16` in `F₁₂₂₈₉` (`4134⁸ = −1`; the element is
`11^((p−1)/16)` for the primitive root `11`). -/
theorem orderOf_4134 : orderOf (4134 : ZMod 12289) = 16 := by
  have h8 : ¬ (4134 : ZMod 12289) ^ (2 : ℕ) ^ 3 = 1 := by decide
  have h16 : (4134 : ZMod 12289) ^ (2 : ℕ) ^ 4 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (4134 : ZMod 12289)) h8 h16
  norm_num at h
  exact h

/-- **The first sub-ceiling upper bound** (`level 1` at the landed `r = 4` rung family):
for the dimension-three code on the 16-point smooth domain `⟨4134⟩ ⊆ F₁₂₂₈₉ˣ` — the same
shape as the landed `δ* = 3/4` pin — every budget `ε* < 32/p` forces

  `δ* ≤ 5/8 < 3/4`,

strictly below the KKH26 ceiling (count `2^3·C(4,3) = 32`, radius `1 − 3/8`).  Probe: the
true bad set of the level-1 stack at this radius is exactly `40` scalars (the spectrum law
`N(3,3) = 32 + 8`), and `40 < 910 =` the landed band bottom, so the `δ* = 3/4` pin band
`[910/p, 1120/p)` is untouched — the two results bracket different budget regimes. -/
theorem subceiling_F12289_n16_d2 (εstar : ℝ≥0∞)
    (hεstar : εstar < (32 : ℝ≥0∞) / (12289 : ℝ≥0∞)) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod 12289)
        (evalCode (4134 : ZMod 12289) 16 2) εstar
      ≤ 5 / 8 := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  have e1 : ((2 : ℕ) ^ 3 * ((2 : ℕ) ^ (4 - 1 - 1)).choose 3 : ℕ) = 32 := rfl
  have e2 : ((12289 : ℕ) : ℝ≥0∞) = (12289 : ℝ≥0∞) := by norm_num
  have h := mcaDeltaStar_le_subceiling (p := 12289) (μ := 4) (m := 1) (j := 1)
    (r := 4) (r' := 3) (by norm_num) (g := (4134 : ZMod 12289)) (by norm_num)
    (n := 16) (by norm_num) orderOf_4134 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) εstar (by rw [e1, e2]; exact_mod_cast hεstar)
  have e0 : ((4 : ℕ) - 2) * 1 = 2 := rfl
  have e3 : (1 : ℝ≥0) - ((3 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (4 - 1)) = 5 / 8 := by
    have hd : ((3 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (4 - 1)) = 3 / 8 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e0, e3] at h
  exact h

/-- **The level-2 rung at the same code**: every budget `ε* < 4/p` forces `δ* ≤ 1/2` for
the dimension-three code — the third step of the staircase `3/4 → 5/8 → 1/2` (counts
`1120 → 32 → 4`; probed exact bad sets `1233 → 40 → 5`). -/
theorem subceiling_F12289_n16_d2_level2 (εstar : ℝ≥0∞)
    (hεstar : εstar < (4 : ℝ≥0∞) / (12289 : ℝ≥0∞)) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod 12289)
        (evalCode (4134 : ZMod 12289) 16 2) εstar
      ≤ 1 / 2 := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  have e1 : ((2 : ℕ) ^ 2 * ((2 : ℕ) ^ (4 - 2 - 1)).choose 2 : ℕ) = 4 := rfl
  have e2 : ((12289 : ℕ) : ℝ≥0∞) = (12289 : ℝ≥0∞) := by norm_num
  have h := mcaDeltaStar_le_subceiling (p := 12289) (μ := 4) (m := 1) (j := 2)
    (r := 4) (r' := 2) (by norm_num) (g := (4134 : ZMod 12289)) (by norm_num)
    (n := 16) (by norm_num) orderOf_4134 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) εstar (by rw [e1, e2]; exact_mod_cast hεstar)
  have e0 : ((4 : ℕ) - 2) * 1 = 2 := rfl
  have e3 : (1 : ℝ≥0) - ((2 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (4 - 2)) = 1 / 2 := by
    have hd : ((2 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (4 - 2)) = 1 / 2 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e0, e3] at h
  exact h

/-- **The sub-max-rate instance** (the `(μ = 4, r = 6)` attack-round shape, machine-checked):
for the dimension-five code (`d = 4`, rate `5/16`) on the same domain — where the level-0
pin band is *empty* (`C(16,6)/2 = 4004 > 1792 = 2^6·C(8,6)`) — the level-1 family gives
`δ* ≤ 1/2` at every `ε* < 16/p`, strictly below the KKH26 ceiling `5/8` (count
`2^4·C(4,4) = 16`; probed exact bad set `41 = N(3,4)`, three-checker verified at `p = 97`
and `p = 12289`). -/
theorem subceiling_F12289_n16_d4 (εstar : ℝ≥0∞)
    (hεstar : εstar < (16 : ℝ≥0∞) / (12289 : ℝ≥0∞)) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod 12289)
        (evalCode (4134 : ZMod 12289) 16 4) εstar
      ≤ 1 / 2 := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  have e1 : ((2 : ℕ) ^ 4 * ((2 : ℕ) ^ (4 - 1 - 1)).choose 4 : ℕ) = 16 := rfl
  have e2 : ((12289 : ℕ) : ℝ≥0∞) = (12289 : ℝ≥0∞) := by norm_num
  have h := mcaDeltaStar_le_subceiling (p := 12289) (μ := 4) (m := 1) (j := 1)
    (r := 6) (r' := 4) (by norm_num) (g := (4134 : ZMod 12289)) (by norm_num)
    (n := 16) (by norm_num) orderOf_4134 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) εstar (by rw [e1, e2]; exact_mod_cast hεstar)
  have e0 : ((6 : ℕ) - 2) * 1 = 4 := rfl
  have e3 : (1 : ℝ≥0) - ((4 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (4 - 1)) = 1 / 2 := by
    have hd : ((4 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (4 - 1)) = 1 / 2 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e0, e3] at h
  exact h

/-- **Pin safety at the first biting instance**: the level-1 count `2^3·C(4,3) = 32` sits
strictly below the landed band bottom `C(16,4)/2 = 910`, so at every budget in the proven
`δ* = 3/4` pin band `[910/p, 1120/p)` the level-1 family is silent — the sub-ceiling bound
and the landed pin bracket disjoint budget regimes, exactly as the general ownership
theorem requires (the level-`j` fibers have size `> d + 2`). -/
theorem levelOne_count_lt_band_bottom_n16_d2 :
    2 ^ 3 * Nat.choose 4 3 < Nat.choose 16 4 / 2 := by decide

end Concrete12289

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.KKH26.subceiling_ca_failure
#print axioms ArkLib.ProximityGap.KKH26.subceiling_epsMCA_lower_bound
#print axioms ArkLib.ProximityGap.KKH26.levelJ_epsMCA_lower_bound
#print axioms ArkLib.ProximityGap.KKH26.mcaDeltaStar_le_subceiling
#print axioms ArkLib.ProximityGap.KKH26.subceiling_radius_lt_ceiling
#print axioms ArkLib.ProximityGap.KKH26.orderOf_4134
#print axioms ArkLib.ProximityGap.KKH26.subceiling_F12289_n16_d2
#print axioms ArkLib.ProximityGap.KKH26.subceiling_F12289_n16_d2_level2
#print axioms ArkLib.ProximityGap.KKH26.subceiling_F12289_n16_d4
#print axioms ArkLib.ProximityGap.KKH26.levelOne_count_lt_band_bottom_n16_d2

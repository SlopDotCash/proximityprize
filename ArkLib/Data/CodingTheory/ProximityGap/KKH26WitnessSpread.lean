/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26BadLineConstruction
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# KKH26 ⇒ the witness spread: an `ε_mca` lower bound and a `δ*` upper bracket for explicit
smooth-domain evaluation codes

`MCAWitnessSpread.lean` proves the sharp structural obstruction for the Grand MCA Challenge
lower bound (issue #232): a single common witness set yields at most one bad scalar
(`unique_bad_gamma_common_witness`), so any `n^{Ω(1)}/|F|` lower bound on `ε_mca` **must**
produce a line whose `δ`-close points are witnessed by a *spread of distinct coordinate
sets*.  That spread was the in-tree open survivor.

This file closes it for explicit smooth-domain evaluation codes, using the [KKH26] bad line
(`KKH26BadLineConstruction.lean`): on the line through `u₀ = X^{rm}` with direction
`u₁ = X^{(r−1)m}` over the `n = 2^μ·m`-point domain `H = ⟨g⟩ ⊆ F_p^×`, **each** of the
`≥ 2^r·(2^{μ−1}).choose r` close parameters `λ_T = −∑_{a∈T} a` is witnessed by its own fiber
`S_T = π^{-1}(T)` — the witness sets vary with the scalar exactly as the obstruction
demands.  Feeding the spread into the in-tree engine
`epsMCA_ge_card_div_of_mcaEvent_set` yields, above the explicit prime threshold
`p > s^{s/2}`:

  `ε_mca(C, 1 − r/2^μ) ≥ 2^r·(2^{μ−1}).choose r / p`

for the evaluation code `C` of degree ≤ `(r−2)m` on `H` — an **exponential-in-`s`** bad-scalar
count at radius just below the code's capacity, against the polynomial ceiling conjectured in
[BCIKS20].  Via the threshold-ledger bracket `mcaDeltaStar_le_of_bad`, this gives the first
machine-checked **upper bracket on the formal MCA threshold** of an explicit smooth-domain
code class:

  `mcaDeltaStar(C, ε*) ≤ 1 − r/2^μ`  whenever  `ε* < 2^r·(2^{μ−1}).choose r / p`.

## Main results

* `evalCode` — the explicit evaluation code (degree-≤`d` polynomial words on `{g^i : i < n}`).
* `badline_pointwise_agreement` — the per-point closeness identity behind the bad line.
* `kkh26_epsMCA_lower_bound` — **the witness spread**: the `ε_mca` lower bound above.
* `kkh26_mcaDeltaStar_le` — **the `δ*` upper bracket** from the threshold ledger.

## Relation to the open survivor

`MCAThresholdLedger.lean` records the exact `δ*` in the interior as OPEN.  This file does
*not* pin `δ*`; it moves the ledger's *upper* bracket from the trivial `1` down to
`1 − r/2^μ` (just below capacity `1 − (r−2)/2^μ − o(1)`) for the explicit code class, with a
fully explicit error budget.  The gap `(Johnson, 1 − r/2^μ)` remains the open survivor, now
two-sided inside the prize window.

## References

* [KKH26] D. Krachun, S. Kazanin, U. Haböck, *Failure of proximity gaps close to capacity*,
  ePrint 2026/782.
* [ABF26] G. Arnon, D. Boneh, G. Fenzi, *Open Problems in List Decoding and Correlated
  Agreement*, ePrint 2026/680.
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, ePrint 2020/654.
-/

open Polynomial Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ArkLib.ProximityGap.KKH26

/-- The explicit smooth-domain evaluation code: words on the `n`-point domain
`{g^i : i < n}` that are evaluations of polynomials of degree at most `d`.  For
`g` of multiplicative order `n` this is the (degree-bound form of the) Reed–Solomon
code on the smooth domain `⟨g⟩`. -/
def evalCode {p : ℕ} (g : ZMod p) (n d : ℕ) : Set (Fin n → ZMod p) :=
  {w | ∃ q : Polynomial (ZMod p), q.natDegree ≤ d ∧ ∀ i : Fin n, w i = q.eval (g ^ (i : ℕ))}

/-- Injectivity of `i ↦ g^i` below the order of `g`, for nonzero `g` in a field
(elementary cancellation; avoids `LeftCancelMonoid` assumptions unavailable at `0`). -/
private lemma pow_inj_below_order {F : Type*} [Field F] {h : F} (h0 : h ≠ 0) {N : ℕ}
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

/-- **Pointwise closeness on the bad line.**  For any `T` with `|T| ≥ 2` there is a single
polynomial `q` of degree ≤ `(|T|−2)m` such that every `x` with `x^m ∈ T` satisfies
`x^{|T|m} + λ_T·x^{(|T|−1)m} = q(x)`, where `λ_T = −∑_{a∈T} a`.  (Evaluation of the
`gap_expansion` identity at the zeros of `v_T ∘ π`.) -/
theorem badline_pointwise_agreement {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    (T : Finset (ZMod p)) (hT2 : 2 ≤ T.card) :
    ∃ q : Polynomial (ZMod p), q.natDegree ≤ (T.card - 2) * m ∧
      ∀ x : ZMod p, x ^ m ∈ T →
        x ^ (T.card * m) + (-(∑ a ∈ T, a)) * x ^ ((T.card - 1) * m) = q.eval x := by
  obtain ⟨E, hEeq, hEdeg⟩ := gap_expansion T hm hT2
  refine ⟨-E, by simpa [natDegree_neg] using hEdeg, ?_⟩
  intro x hxm
  have hvanish : ∏ a ∈ T, (x ^ m - a) = 0 := Finset.prod_eq_zero hxm (sub_self _)
  have heval := congrArg (Polynomial.eval x) hEeq
  rw [eval_prod] at heval
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at heval
  rw [hvanish] at heval
  rw [eval_neg]
  linear_combination -heval

open Classical in
/-- **The witness spread ([KKH26] ⇒ `ε_mca` lower bound).**  For the explicit evaluation
code of degree ≤ `(r−2)m` on the smooth `n = 2^μ·m`-point domain `⟨g⟩ ⊆ F_p^×`, above the
explicit prime threshold `p > (2^μ)^{2^{μ−1}}`:

  `ε_mca(C, 1 − r/2^μ) ≥ 2^r · (2^{μ−1}).choose r / p`.

Each bad scalar `λ_T` is witnessed by its own fiber — the spread of distinct witness sets
that `unique_bad_gamma_common_witness` proves is *necessary* for any such bound. -/
theorem kkh26_epsMCA_lower_bound {p n : ℕ} [Fact p.Prime] [NeZero n] {μ m r : ℕ}
    (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1)) :
    ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)
      ≤ epsMCA (F := ZMod p) (evalCode g n ((r - 2) * m))
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
  have hbad : ∀ γ ∈ Λ, mcaEvent (evalCode g (2 ^ μ * m) ((r - 2) * m))
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
          Fin.ext (pow_inj_below_order hg0 hg _ i.isLt _ j.isLt hij))
      rw [← h1, hSimg, fiber_count hm hs1 hg T hTG, hTcard]
    refine ⟨S, ?_, ⟨fun i => q.eval (g ^ (i : ℕ)), ⟨q, hqdeg, fun _ => rfl⟩, ?_⟩, ?_⟩
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
    · -- no joint pair: the direction word is far (kkh26_ca_failure)
      rintro ⟨v₀, _, v₁, hv₁, hpair⟩
      obtain ⟨q₁, hq₁deg, hq₁⟩ := hv₁
      have hS'H : S.image (fun i : Fin (2 ^ μ * m) => g ^ (i : ℕ))
          ⊆ (Finset.range (2 ^ μ * m)).image (fun i => g ^ i) := by
        rw [hSimg]
        exact Finset.filter_subset _ _
      have hS'card : r * m ≤ (S.image (fun i : Fin (2 ^ μ * m) => g ^ (i : ℕ))).card := by
        rw [hSimg, fiber_count hm hs1 hg T hTG, hTcard, mul_comm]
      refine kkh26_ca_failure (g := g) (n := 2 ^ μ * m) hm hr2 _ hS'H hS'card q₁ hq₁deg ?_
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have h1 : v₁ i = u 1 i := (hpair i hi).2
      have h2 : v₁ i = q₁.eval (g ^ (i : ℕ)) := hq₁ i
      rw [hu] at h1
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
      rw [← h2, h1]
  -- feed the spread into the in-tree lower-bound engine
  have hengine := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (F := ZMod p) (evalCode g (2 ^ μ * m) ((r - 2) * m))
    (1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ)) u Λ hbad
  rw [ZMod.card p] at hengine
  refine le_trans ?_ hengine
  exact ENNReal.div_le_div_right (by exact_mod_cast hΛcard) _

open Classical in
/-- **The `δ*` upper bracket from [KKH26].**  For any target error `ε*` strictly below the
explicit bad-scalar mass `2^r·(2^{μ−1}).choose r / p`, the formal MCA threshold of the
explicit smooth-domain evaluation code is at most `1 − r/2^μ` — strictly below the code's
capacity.  This is the threshold-ledger form of the [KKH26] ceiling
`δ* ≤ 1 − ρ − Θ_ρ(1/log n)` for the Grand MCA Challenge (issue #232). -/
theorem kkh26_mcaDeltaStar_le {p n : ℕ} [Fact p.Prime] [NeZero n] {μ m r : ℕ}
    (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1)) (εstar : ℝ≥0∞)
    (hεstar : εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
        (evalCode g n ((r - 2) * m)) εstar
      ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) :=
  ProximityGap.MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hεstar
      (kkh26_epsMCA_lower_bound hμ hm hn hg hp hr2 hr))

/-! ### The divisibility route (issue #334, [KKH26] Lemma 2 wiring)

The assembly above consumes [KKH26] Lemma 1 through the superpolynomial size hypothesis
`p > (2^μ)^{2^{μ−1}}`.  The variants below re-run the *identical* assembly through
`kkh26_lemma1_of_not_dvd` instead: the only hypotheses on `p` are the mild `p > 2^μ` and
that `p` divides none of the collision resultants `collisionResultant μ d₁ d₂` — exactly
what the conditional [TZ24] good prime `p = Θ(n^β)` of `kkh26_good_prime_of_TZ`
(`KKH26ThornerZaman.lean`) delivers.  The composition lives in
`KKH26PolyFieldCeiling.lean`.  The original theorems above are untouched. -/

open Classical in
/-- **The witness spread at a good prime** (issue #334): `kkh26_epsMCA_lower_bound` with the
size hypothesis `p > (2^μ)^{2^{μ−1}}` replaced by the divisibility hypothesis of
`kkh26_lemma1_of_not_dvd` — `p > 2^μ` and `p` divides no collision resultant.  This is the
form consumable at `p = Θ(n^β)` via the [TZ24] supply. -/
theorem kkh26_epsMCA_lower_bound_of_not_dvd {p n : ℕ} [Fact p.Prime] [NeZero n] {μ m r : ℕ}
    (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m)
    (hpl : (2 : ℕ) ^ μ < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1))
    (hndvd : ∀ d₁ ∈ sigData (2 ^ (μ - 1)) r, ∀ d₂ ∈ sigData (2 ^ (μ - 1)) r,
      d₁ ≠ d₂ → ¬ (p : ℤ) ∣ collisionResultant μ d₁ d₂) :
    ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)
      ≤ epsMCA (F := ZMod p) (evalCode g n ((r - 2) * m))
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
  -- Lemma 1 (divisibility form): many distinct sums of r distinct elements of G = ⟨g^m⟩
  have hlem1 := kkh26_lemma1_of_not_dvd hμ hprim hpl hr hndvd
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
  have hbad : ∀ γ ∈ Λ, mcaEvent (evalCode g (2 ^ μ * m) ((r - 2) * m))
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
          Fin.ext (pow_inj_below_order hg0 hg _ i.isLt _ j.isLt hij))
      rw [← h1, hSimg, fiber_count hm hs1 hg T hTG, hTcard]
    refine ⟨S, ?_, ⟨fun i => q.eval (g ^ (i : ℕ)), ⟨q, hqdeg, fun _ => rfl⟩, ?_⟩, ?_⟩
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
    · -- no joint pair: the direction word is far (kkh26_ca_failure)
      rintro ⟨v₀, _, v₁, hv₁, hpair⟩
      obtain ⟨q₁, hq₁deg, hq₁⟩ := hv₁
      have hS'H : S.image (fun i : Fin (2 ^ μ * m) => g ^ (i : ℕ))
          ⊆ (Finset.range (2 ^ μ * m)).image (fun i => g ^ i) := by
        rw [hSimg]
        exact Finset.filter_subset _ _
      have hS'card : r * m ≤ (S.image (fun i : Fin (2 ^ μ * m) => g ^ (i : ℕ))).card := by
        rw [hSimg, fiber_count hm hs1 hg T hTG, hTcard, mul_comm]
      refine kkh26_ca_failure (g := g) (n := 2 ^ μ * m) hm hr2 _ hS'H hS'card q₁ hq₁deg ?_
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have h1 : v₁ i = u 1 i := (hpair i hi).2
      have h2 : v₁ i = q₁.eval (g ^ (i : ℕ)) := hq₁ i
      rw [hu] at h1
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
      rw [← h2, h1]
  -- feed the spread into the in-tree lower-bound engine
  have hengine := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (F := ZMod p) (evalCode g (2 ^ μ * m) ((r - 2) * m))
    (1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ)) u Λ hbad
  rw [ZMod.card p] at hengine
  refine le_trans ?_ hengine
  exact ENNReal.div_le_div_right (by exact_mod_cast hΛcard) _

open Classical in
/-- **The `δ*` upper bracket at a good prime** (issue #334): `kkh26_mcaDeltaStar_le` with the
size hypothesis replaced by the divisibility hypothesis — the form composed with the
conditional [TZ24] good prime in `KKH26PolyFieldCeiling.lean` to obtain the ceiling at
polynomial field size `p = Θ(n^β)`. -/
theorem kkh26_mcaDeltaStar_le_of_not_dvd {p n : ℕ} [Fact p.Prime] [NeZero n] {μ m r : ℕ}
    (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m)
    (hpl : (2 : ℕ) ^ μ < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1))
    (hndvd : ∀ d₁ ∈ sigData (2 ^ (μ - 1)) r, ∀ d₂ ∈ sigData (2 ^ (μ - 1)) r,
      d₁ ≠ d₂ → ¬ (p : ℤ) ∣ collisionResultant μ d₁ d₂)
    (εstar : ℝ≥0∞)
    (hεstar : εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
        (evalCode g n ((r - 2) * m)) εstar
      ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) :=
  ProximityGap.MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hεstar
      (kkh26_epsMCA_lower_bound_of_not_dvd hμ hm hn hg hpl hr2 hr hndvd))

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.KKH26.badline_pointwise_agreement
#print axioms ArkLib.ProximityGap.KKH26.kkh26_epsMCA_lower_bound
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le
#print axioms ArkLib.ProximityGap.KKH26.kkh26_epsMCA_lower_bound_of_not_dvd
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_of_not_dvd

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubCeilingLadder
import ArkLib.Data.CodingTheory.ProximityGap.OwnershipCensusSharpened

/-!
# The level-1 rung: the antipodal pencil REFUTES the staircase below `1/2`; the `d = 2`
# rung pin is reduced to one named obligation on the trapped band `[16/p, 32/p)` (#371)

`SubCeilingLadder.lean` proved the **bad side** of the budget-indexed staircase envelope: at
the first biting instance (`n = 16, d = 2`, the dim-3 code on `⟨4134⟩ ⊆ F₁₂₂₈₉ˣ`) every
budget `ε* < 32/p` forces `δ* ≤ 5/8`, strictly below the KKH26 ceiling `3/4`.  **Pinning**
the rung (`δ* = 5/8` exactly) needs the matching good side at every radius `δ < 5/8`
(agreement threshold `7`).  Probing that good side adversarially produced a *discovery*
that re-draws the whole sub-`1/2` landscape, and this file lands both it and what remains
of the pin.

## THE DISCOVERY — the antipodal pencil family (`antipodal_pencil_epsMCA_lower_bound`)

The earlier S6 numeric ("worst stack at threshold 7 = 1") was a **search artifact** (its
pool capped monomial exponents at 4).  The corrected probe (`probe_level1_pin.py`: full
monomial sweeps at `p ∈ {17, 97}`, structured families + climbs at `p = 12289`) found the
stack `(X^h, X^{h+1})`, `h = n/2`: since `x^h = ±1`, the line `x^h(1+γx)` **is** the
degree-1 word `±(1+γX)` on an entire antipodal half-coset plus the one rotating
cross-coset point `x₀ = −1/γ`, while the direction `x^h·x = ±x` deviates there.  Hence
**`n` bad scalars** (the inversion orbit `−1/⟨g⟩`) at radius `1 − (h+1)/n`, for *every*
code degree `1 ≤ d ≤ h−1` — proven here in general, axiom-clean.  Consequences:

* **The level-`j` staircase is NOT the complete envelope**: the pencil bites at
  `7/16 < 1/2` (the deepest rung) with count `16 > 5 = N(2,2)` (instance `d = 2`).
* **The `d = 4` level-1 rung is REFUTED** (`deltaStar_lt_levelOne_rung_F12289_d4`,
  `level1_interior_unsat_F12289_d4`): the pencil count `16` *equals* the rung budget
  `K_1 = 16`, so on the rung's entire band `ε* < 16/p` the threshold is `≤ 7/16 < 1/2`:
  the staircase value is never `δ*` there — envelope-exactness at this rung is **false**.
* **The `d = 2` rung survives, trapped tightly**: the pencil forces any obligation budget
  up to `ε* ≥ 16/p` (`level1_interior_floor16_F12289`), so the conditional pin band is
  exactly `[16/p, 32/p)`; the probed worst stack at threshold 7 is `16` — the pencil
  itself — so the band is probe-tight at the bottom.

## What else is proven

* **The general level-`j` envelope-exactness reduction**
  (`SubCeilingInteriorCeiling` → `subceiling_deltaStar_pin_of_interior`): at *every* valid
  rung, the exact pin `δ* = 1 − r'_j/2^{μ−j}` on `ε* < K_j/p` follows from the single
  obligation "`ε_mca ≤ ε*` below the rung" — the `j ≥ 1` analogue of
  `kkh26_deltaStar_pin_of_interior_ceiling` (= the `j = 0` case).
* **The conditional `d = 2` pin** (`deltaStar_level1_pin_F12289_of_interior`): granting
  the obligation, `δ* = 5/8` exactly for every satisfying `ε* < 32/p`.
* **Floors**: `level2_epsMCA_floor_F12289` (`≥ 4/p` from the level-2 family at `1/2`) and
  the pencil floor `16/p` above.
* **The unconditional good side** (`level1_engine_goodSide_F12289`): the sharpened
  ownership census at `w₀ = 6` gives `ε_mca(C, δ) ≤ 208/p` for every `δ < 5/8` — hence
  unconditional `δ* ≥ 5/8` at every `ε* ≥ 208/p` (`deltaStar_ge_level1_radius_F12289`), a
  beyond-Johnson (`5/8 > 1 − √(3/16) ≈ 0.567`) lower bound at the small prime `p = 12289`
  where the level-0 pin family is unavailable (its `hp` needs `p > 2³²`).
* **The wall — why the `d = 2` obligation stays named** (`level1_budget_le_subset_cap`
  etc.): the engine value at threshold 7 is `C(16,3)·13/C(7,3) = 208 > 32`; the
  realizable-extremal cap (`deviation_ownership_card`) is `C(16,4)/C(6,3) = 91`; the
  **absolute** cap of per-witness `(d+2)`-subset counting — every bad scalar owning *all*
  `C(7,4) = 35` subsets of a minimal witness — is `C(16,4)/C(7,4) = 52`.  All exceed the
  budget edge `32`: **no refinement of per-witness subset counting can discharge the
  level-1 obligation** (and `K_j` shrinks exponentially down the staircase while the caps
  are polynomial in `n`, so the wall is uniform across instances) — the first concrete
  consequence of the saturation theorem of `OwnershipCensusSharpened.lean`.  Same shape at
  `d = 4`: engine `190 > 16` (`level1_budget_lt_engine_d4`).

Probed sub-`1/2` landscape at the instance (exact, `p ∈ {97, 12289}`): the pencil ladder
continues — `(X⁸, X^{10})` has `8` bad scalars at radius `3/8` (`d = 2`), and at `d = 4`
the pencil shows `49` bad at threshold 7 and `17` at threshold 8.  Mapping the full
refined envelope (staircase ⊔ pencil ladder) is the successor question.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26 Code
open ProximityGap.KKH26DeltaStarReduction
open ArkLib.ProximityGap.OwnershipCensus
open ArkLib.ProximityGap.KKH26DimGeneral

namespace ArkLib.ProximityGap.Level1Rung

/-! ## The general level-`j` envelope-exactness reduction -/

/-- **The level-`j` interior obligation** — the sub-ceiling analogue of the deployed-regime
`InteriorCeiling`: the MCA error of the degree-`(r−2)m` code stays below the budget at
*every* radius strictly below the level-`j` rung `1 − r'/2^{μ−j}`.  At `j = 0` (`r' = r`)
this is exactly `InteriorCeiling`; for `j ≥ 1` it is the open good side of the staircase
envelope.  The floor lemma below shows it forces `ε* ≥ K_{j+1}/p` whenever a deeper rung
exists, and the wall lemmas show the in-tree subset-counting engines cannot discharge it. -/
def SubCeilingInteriorCeiling (p n : ℕ) [Fact p.Prime] [NeZero n] (g : ZMod p)
    (μ m j r r' : ℕ) (εstar : ℝ≥0∞) : Prop :=
  ∀ δ : ℝ≥0, δ < 1 - (r' : ℝ≥0) / ((2 : ℝ≥0) ^ (μ - j)) →
    epsMCA (F := ZMod p) (evalCode g n ((r - 2) * m)) δ ≤ εstar

/-- **Envelope-exactness at every rung, modulo one obligation per rung.**  For any valid
level-`j` rung (`(r'−2)·2^j ≤ r−2 < (r'−1)·2^j`, level prime threshold, lemma regime),
any budget `ε* < K_j/p = (2^{r'}·C(2^{μ−j−1}, r'))/p` satisfying the level-`j` interior
obligation pins

  `mcaDeltaStar(evalCode g n ((r−2)m), ε*) = 1 − r'/2^{μ−j}`

**exactly**: the bad side is the in-tree level-`j` witness spread
(`levelJ_epsMCA_lower_bound`) propagated upward by monotonicity, the good side is the
obligation, and they meet at the rung.  At `j = 0` this reproduces
`kkh26_deltaStar_pin_of_interior_ceiling`; for `j ≥ 1` it shows the budget-indexed
staircase envelope is exact at every rung **iff** the per-rung obligations hold — the
envelope question is now a family of named good-side obligations and nothing else. -/
theorem subceiling_deltaStar_pin_of_interior
    {p n : ℕ} [Fact p.Prime] [NeZero n] {μ m j r r' : ℕ}
    (hj : j + 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ (μ - j)) ^ 2 ^ (μ - j - 1) < p)
    (hr'2 : 2 ≤ r') (hr' : r' ≤ 2 ^ (μ - j - 1))
    (hrung₁ : (r' - 2) * 2 ^ j ≤ r - 2) (hrung₂ : r - 2 < (r' - 1) * 2 ^ j)
    (εstar : ℝ≥0∞)
    (hεstar : εstar < ((2 ^ r' * (2 ^ (μ - j - 1)).choose r' : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))
    (hint : SubCeilingInteriorCeiling p n g μ m j r r' εstar) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n ((r - 2) * m)) εstar
      = 1 - (r' : ℝ≥0) / ((2 : ℝ≥0) ^ (μ - j)) := by
  have hbad_at : εstar < epsMCA (F := ZMod p) (A := ZMod p)
      (evalCode g n ((r - 2) * m)) (1 - (r' : ℝ≥0) / ((2 : ℝ≥0) ^ (μ - j))) :=
    lt_of_lt_of_le hεstar
      (levelJ_epsMCA_lower_bound hj hm hn hg hp hr'2 hr' hrung₁ hrung₂)
  refine mcaDeltaStar_eq_of_good_below_of_bad_above
    (evalCode g n ((r - 2) * m)) εstar tsub_le_self hint
    (fun δ hδ => lt_of_lt_of_le hbad_at
      (epsMCA_mono (F := ZMod p) (A := ZMod p) (evalCode g n ((r - 2) * m)) hδ))

/-! ## The antipodal pencil family: a bad family the staircase does NOT contain

The probe found it (`probe_level1_pin.py` P2: the monomial stack `(X^h, X^{h+1})`,
`h = n/2`): since `x^h = ±1` on the smooth domain, the line `u₀ + γu₁ = x^h·(1 + γx)`
agrees with the **degree-1** polynomial `±(1 + γX)` on an entire half-coset (`h` points)
*plus one rotating cross-coset point* `x₀ = −1/γ` — and the direction `u₁ = x^h·x` is a
single-deviation word on that witness, hence unfit.  Every `γ ∈ −1/⟨g⟩` is therefore bad
at radius `1 − (h+1)/n`, giving **`n` bad scalars strictly below the deepest staircase
rung** (`1 − (h+1)/n < 1/2` vs. the level-`(μ−1)`-rung counts `N(2,2) = 5`, `N(2,3) = 4`).
The budget-indexed level-`j` staircase is consequently **not the complete envelope**. -/

/-- Injectivity of `i ↦ g^i` below the order of `g` (local copy of the `private` helper of
the sibling files). -/
private lemma pow_inj_below_order'' {F : Type*} [Field F] {h : F} (h0 : h ≠ 0) {N : ℕ}
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

/-- `(−1)^a` depends only on the parity of `a`. -/
private lemma neg_one_pow_congr {R : Type*} [Monoid R] [HasDistribNeg R] {a b : ℕ}
    (hab : a % 2 = b % 2) : ((-1 : R)) ^ a = (-1) ^ b := by
  rcases Nat.even_or_odd a with ha | ha
  · have hb : Even b := by
      rw [Nat.even_iff] at ha ⊢
      omega
    rw [ha.neg_one_pow, hb.neg_one_pow]
  · have hb : Odd b := by
      rw [Nat.odd_iff] at ha ⊢
      omega
    rw [ha.neg_one_pow, hb.neg_one_pow]

open Classical in
/-- **The antipodal pencil lower bound.**  On the smooth domain `⟨g⟩` of even order
`n = 2h`, the stack `(X^h, X^{h+1})` has at least `n` bad scalars — the full inversion
orbit `{−(g^i)⁻¹}` — at radius `1 − (h+1)/n`, against the degree-`d` code for **every**
`1 ≤ d ≤ h − 1`.  Mechanism: `x^h = ±1` splits the domain into two antipodal cosets; on
the coset opposite to `x₀ = −1/γ` the line `x^h(1+γx)` *is* the degree-1 word
`±(1+γX)`, and at `x₀` both vanish — an `(h+1)`-point witness; the direction
`x^h·x = ±x` is a single-deviation word there, hence has no degree-`d` fit.  The radius
sits strictly below the deepest level-`j` staircase rung (`1 − (h+1)/n < 1/2`) with count
`n` strictly above the deep-rung spectra: the level-`j` sign-subset staircase is **not**
the complete bad-family envelope. -/
theorem antipodal_pencil_epsMCA_lower_bound {p n : ℕ} [Fact p.Prime] [NeZero n] {h d : ℕ}
    (hh : 1 ≤ h) (hn : n = 2 * h) {g : ZMod p} (hg : orderOf g = n)
    (hd1 : 1 ≤ d) (hdh : d + 1 ≤ h) :
    ((n : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)
      ≤ epsMCA (F := ZMod p) (evalCode g n d)
          (1 - ((h + 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) := by
  classical
  subst hn
  -- bookkeeping: `g ≠ 0`, index injectivity, `g^h = −1`, `−1 ≠ 1`
  have hg0 : g ≠ 0 := by
    rintro rfl
    have h1 : (0 : ZMod p) ^ (2 * h) = 1 := by
      rw [← hg]; exact pow_orderOf_eq_one 0
    rw [zero_pow (by omega : 2 * h ≠ 0)] at h1
    exact zero_ne_one h1
  have hginj : ∀ i j : Fin (2 * h), g ^ (i : ℕ) = g ^ (j : ℕ) → i = j := by
    intro i j hij
    exact Fin.ext (pow_inj_below_order'' hg0 hg _ i.isLt _ j.isLt hij)
  have hgn : g ^ (2 * h) = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hne1 : g ^ h ≠ 1 := by
    intro hcon
    have hdvd : 2 * h ∣ h := hg ▸ orderOf_dvd_of_pow_eq_one hcon
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hgh : g ^ h = -1 := by
    have hfac : (g ^ h - 1) * (g ^ h + 1) = 0 := by
      have hsq : g ^ h * g ^ h = 1 := by
        rw [← pow_add]
        have : h + h = 2 * h := by omega
        rw [this, hgn]
      linear_combination hsq
    rcases mul_eq_zero.mp hfac with hc | hc
    · exact absurd (by linear_combination hc) hne1
    · linear_combination hc
  have hm1 : (-1 : ZMod p) ≠ 1 := hgh ▸ hne1
  -- the antipodal values of the stack words
  have hu0v : ∀ i : Fin (2 * h), (g ^ (i : ℕ)) ^ h = (-1 : ZMod p) ^ (i : ℕ) := by
    intro i
    rw [← pow_mul, mul_comm (i : ℕ) h, pow_mul, hgh]
  have hu1v : ∀ i : Fin (2 * h),
      (g ^ (i : ℕ)) ^ (h + 1) = (-1 : ZMod p) ^ (i : ℕ) * g ^ (i : ℕ) := by
    intro i
    rw [pow_succ, hu0v i]
  -- the stack and the bad-scalar orbit
  set u : WordStack (ZMod p) (Fin 2) (Fin (2 * h)) :=
    ![fun i => (g ^ (i : ℕ)) ^ h, fun i => (g ^ (i : ℕ)) ^ (h + 1)] with hu
  set Λ : Finset (ZMod p) :=
    Finset.univ.image (fun i : Fin (2 * h) => -((g ^ (i : ℕ))⁻¹)) with hΛ
  have hΛcard : Λ.card = 2 * h := by
    have hinj : Function.Injective (fun i : Fin (2 * h) => -((g ^ (i : ℕ))⁻¹)) := by
      intro i j hij
      simp only at hij
      exact hginj i j (inv_injective (neg_injective hij))
    rw [hΛ, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  -- every orbit scalar is bad with the half-coset-plus-one witness
  have hbad : ∀ γ ∈ Λ, mcaEvent (evalCode g (2 * h) d)
      (1 - ((h + 1 : ℕ) : ℝ≥0) / ((2 * h : ℕ) : ℝ≥0)) (u 0) (u 1) γ := by
    intro γ hγ
    obtain ⟨i₀, -, rfl⟩ := Finset.mem_image.mp hγ
    set γ := -((g ^ ((i₀ : ℕ)))⁻¹) with hγdef
    have hγx : 1 + γ * g ^ ((i₀ : ℕ)) = 0 := by
      rw [hγdef, neg_mul, inv_mul_cancel₀ (pow_ne_zero _ hg0)]
      ring
    -- the witness: the coset of parity opposite to `i₀`, plus `i₀` itself
    set r : ℕ := 1 - (i₀ : ℕ) % 2 with hr_def
    have hrlt : r < 2 := by omega
    have hflt : ∀ k : Fin h, 2 * (k : ℕ) + r < 2 * h := fun k => by
      have := k.isLt
      omega
    set f : Fin h → Fin (2 * h) := fun k => ⟨2 * (k : ℕ) + r, hflt k⟩ with hf
    set Sbulk : Finset (Fin (2 * h)) := Finset.univ.image f with hSb
    have hbulk_par : ∀ i ∈ Sbulk, (i : ℕ) % 2 = r := by
      intro i hib
      obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hib
      subst hk
      show (2 * (k : ℕ) + r) % 2 = r
      omega
    have hi₀notin : i₀ ∉ Sbulk := by
      intro hmem
      have := hbulk_par i₀ hmem
      omega
    have hfinj : Function.Injective f := by
      intro a b hab
      have h1 := congrArg Fin.val hab
      simp only [hf] at h1
      exact Fin.ext (by omega)
    have hSbulk_card : Sbulk.card = h := by
      rw [hSb, Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
    set S : Finset (Fin (2 * h)) := insert i₀ Sbulk with hS
    have hScard : S.card = h + 1 := by
      rw [hS, Finset.card_insert_of_notMem hi₀notin, hSbulk_card]
    -- the sign of the opposite coset, and the degree-1 codeword
    set s : ZMod p := (-1 : ZMod p) ^ ((i₀ : ℕ) + 1) with hs_def
    have hpar : ∀ i ∈ Sbulk, (-1 : ZMod p) ^ (i : ℕ) = s := by
      intro i hib
      have h1 := hbulk_par i hib
      exact neg_one_pow_congr (by omega)
    set q : Polynomial (ZMod p) :=
      Polynomial.C s * (1 + Polynomial.C γ * Polynomial.X) with hq_def
    have hqdeg : q.natDegree ≤ d := by
      refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      refine le_trans (Polynomial.natDegree_add_le _ _) ?_
      refine max_le (by simp) ?_
      exact le_trans (Polynomial.natDegree_C_mul_le _ _)
        (by simp [Polynomial.natDegree_X, hd1])
    have hq_eval : ∀ x : ZMod p, q.eval x = s * (1 + γ * x) := by
      intro x
      rw [hq_def]
      simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one,
        Polynomial.eval_C, Polynomial.eval_X]
    refine ⟨S, ?_, ⟨fun i => q.eval (g ^ (i : ℕ)), polyEval_mem_evalCode q hqdeg, ?_⟩, ?_⟩
    · -- size: |S| = h + 1 = (1 − δ)·n
      have hcardF : ((Fintype.card (Fin (2 * h)) : ℕ) : ℝ≥0) = ((2 * h : ℕ) : ℝ≥0) := by
        rw [Fintype.card_fin]
      have hn0 : ((2 * h : ℕ) : ℝ≥0) ≠ 0 := by
        have hpos : (0 : ℕ) < 2 * h := by omega
        exact_mod_cast hpos.ne'
      have hle1 : ((h + 1 : ℕ) : ℝ≥0) / ((2 * h : ℕ) : ℝ≥0) ≤ 1 := by
        rw [div_le_one (lt_of_le_of_ne (zero_le _) (Ne.symm hn0))]
        exact_mod_cast (by omega : h + 1 ≤ 2 * h)
      have h1δ : (1 : ℝ≥0) - (1 - ((h + 1 : ℕ) : ℝ≥0) / ((2 * h : ℕ) : ℝ≥0))
          = ((h + 1 : ℕ) : ℝ≥0) / ((2 * h : ℕ) : ℝ≥0) := tsub_tsub_cancel_of_le hle1
      rw [hScard, hcardF, h1δ, div_mul_cancel₀ _ hn0]
    · -- agreement of the line with the degree-1 codeword on the witness
      intro i hi
      rw [hu]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
      rw [hq_eval, hu0v i, hu1v i]
      rcases Finset.mem_insert.mp hi with rfl | hib
      · linear_combination (s - (-1 : ZMod p) ^ (i : ℕ)) * hγx
      · rw [hpar i hib]
        ring
    · -- no joint pair: the direction is a single-deviation word on the witness
      rintro ⟨v₀, -, v₁, hv₁, hpair⟩
      obtain ⟨q₁, hq₁deg, hq₁⟩ := hv₁
      have hsX : (Polynomial.C s * Polynomial.X : Polynomial (ZMod p)).natDegree ≤ d :=
        le_trans (Polynomial.natDegree_C_mul_le _ _)
          (by simp [Polynomial.natDegree_X, hd1])
      have hqq : q₁ = Polynomial.C s * Polynomial.X := by
        refine fit_unique hginj (B := Sbulk) (by rw [hSbulk_card]; exact hdh)
          hq₁deg hsX fun i hib => ?_
        have h1 : v₁ i = u 1 i := (hpair i (Finset.mem_insert_of_mem hib)).2
        have h2 : v₁ i = q₁.eval (g ^ (i : ℕ)) := hq₁ i
        have h3 : u 1 i = s * g ^ (i : ℕ) := by
          rw [hu]
          simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
          rw [hu1v i, hpar i hib]
        rw [← h2, h1, h3]
        simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      -- contradiction at the deviation point `i₀`
      have h4 : v₁ i₀ = u 1 i₀ := (hpair i₀ (Finset.mem_insert_self _ _)).2
      have h5 : v₁ i₀ = q₁.eval (g ^ ((i₀ : ℕ))) := hq₁ i₀
      have h6 : u 1 i₀ = (-1 : ZMod p) ^ ((i₀ : ℕ)) * g ^ ((i₀ : ℕ)) := by
        rw [hu]
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
        exact hu1v i₀
      have h7 : q₁.eval (g ^ ((i₀ : ℕ))) = s * g ^ ((i₀ : ℕ)) := by
        rw [hqq]
        simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      have hkey : (-1 : ZMod p) ^ ((i₀ : ℕ)) * g ^ ((i₀ : ℕ))
          = -((-1 : ZMod p) ^ ((i₀ : ℕ)) * g ^ ((i₀ : ℕ))) := by
        calc (-1 : ZMod p) ^ ((i₀ : ℕ)) * g ^ ((i₀ : ℕ)) = u 1 i₀ := h6.symm
        _ = q₁.eval (g ^ ((i₀ : ℕ))) := by rw [← h4, h5]
        _ = s * g ^ ((i₀ : ℕ)) := h7
        _ = -((-1 : ZMod p) ^ ((i₀ : ℕ)) * g ^ ((i₀ : ℕ))) := by
            rw [hs_def, pow_succ]
            ring
      have hx0 : (-1 : ZMod p) ^ ((i₀ : ℕ)) * g ^ ((i₀ : ℕ)) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ hg0)
      have h2x : (2 : ZMod p) * ((-1 : ZMod p) ^ ((i₀ : ℕ)) * g ^ ((i₀ : ℕ))) = 0 := by
        linear_combination hkey
      rcases mul_eq_zero.mp h2x with h20 | hx
      · exact hm1 (by linear_combination -h20)
      · exact hx0 hx
  -- feed the orbit into the in-tree lower-bound engine
  have hengine := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (F := ZMod p) (evalCode g (2 * h) d)
    (1 - ((h + 1 : ℕ) : ℝ≥0) / ((2 * h : ℕ) : ℝ≥0)) u Λ hbad
  rw [ZMod.card p] at hengine
  refine le_trans ?_ hengine
  exact ENNReal.div_le_div_right (by exact_mod_cast hΛcard.ge) _

/-- **The antipodal `δ*` upper bound**: at every budget `ε* < n/p`, the MCA threshold of
the degree-`d` code (`1 ≤ d ≤ h−1`) is at most `1 − (h+1)/n` — strictly below the deepest
staircase rung `1/2`, at budgets where the deep-rung counts (`≤ 5`) are silent. -/
theorem mcaDeltaStar_le_antipodal {p n : ℕ} [Fact p.Prime] [NeZero n] {h d : ℕ}
    (hh : 1 ≤ h) (hn : n = 2 * h) {g : ZMod p} (hg : orderOf g = n)
    (hd1 : 1 ≤ d) (hdh : d + 1 ≤ h) (εstar : ℝ≥0∞)
    (hεstar : εstar < ((n : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n d) εstar
      ≤ 1 - ((h + 1 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) :=
  mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hεstar (antipodal_pencil_epsMCA_lower_bound hh hn hg hd1 hdh))

/-! ## The first biting instance: `n = 16`, `d = 2`, `p = 12289`, `g = 4134` -/

section Concrete12289

local instance fact_prime_12289'' : Fact (Nat.Prime 12289) := ⟨by norm_num⟩

/-- Index injectivity on the 16-point domain `⟨4134⟩ ⊆ F₁₂₂₈₉ˣ`. -/
theorem ginj_4134 : ∀ i j : Fin 16,
    (4134 : ZMod 12289) ^ (i : ℕ) = (4134 : ZMod 12289) ^ (j : ℕ) → i = j := by
  intro i j hij
  have hg0 : (4134 : ZMod 12289) ≠ 0 := by decide
  exact Fin.ext (pow_inj_below_order'' hg0 orderOf_4134 _ i.isLt _ j.isLt hij)

/-- **The floor: the level-2 family is bad strictly below the level-1 rung.**  The stack
`(X⁸, X⁴)` has `≥ 4` bad scalars (probed exact count `N(2,2) = 5`) at radius `1/2 < 5/8`
— its witnesses are full 8-point fibers of `x ↦ x⁴`, which survive every threshold `≤ 8`.
(The earlier S6 hill-climb that reported "worst stack = 1" at threshold 7 had this stack
outside its search pool; the probe `probe_level1_pin.py` corrects it.) -/
theorem level2_epsMCA_floor_F12289 :
    (4 : ℝ≥0∞) / (12289 : ℝ≥0∞)
      ≤ epsMCA (F := ZMod 12289) (evalCode (4134 : ZMod 12289) 16 2) (1 / 2 : ℝ≥0) := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  have h := levelJ_epsMCA_lower_bound (p := 12289) (n := 16) (μ := 4) (m := 1) (j := 2)
    (r := 4) (r' := 2) (by norm_num) (g := (4134 : ZMod 12289)) (by norm_num)
    (by norm_num) orderOf_4134 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have e0 : ((4 : ℕ) - 2) * 1 = 2 := rfl
  have e1 : ((2 : ℕ) ^ 2 * ((2 : ℕ) ^ (4 - 2 - 1)).choose 2 : ℕ) = 4 := rfl
  have e2 : ((12289 : ℕ) : ℝ≥0∞) = (12289 : ℝ≥0∞) := by norm_num
  have e3 : (1 : ℝ≥0) - ((2 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (4 - 2)) = 1 / 2 := by
    have hd : ((2 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (4 - 2)) = 1 / 2 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e0, e1, e2, e3] at h
  exact_mod_cast h

/-- **The level-1 obligation is not free**: any budget satisfying the level-1 interior
obligation at this instance is at least `4/p` (true floor `5/p`, the probed exact level-2
count).  Together with the bad side `32/p`, the conditional pin band is `⊆ [4/p, 32/p)`. -/
theorem level1_interior_floor_F12289 (εstar : ℝ≥0∞)
    (hint : ∀ δ : ℝ≥0, δ < 5 / 8 →
      epsMCA (F := ZMod 12289) (evalCode (4134 : ZMod 12289) 16 2) δ ≤ εstar) :
    (4 : ℝ≥0∞) / (12289 : ℝ≥0∞) ≤ εstar :=
  le_trans level2_epsMCA_floor_F12289 (hint (1 / 2) (by norm_num))

/-- **The antipodal pencil at the instance, `d = 2`**: sixteen bad scalars at radius
`7/16 = 1 − 9/16`, strictly below the deepest staircase rung `1/2` (where the exact count
was `5`) — verified exactly by the probe at `p ∈ {17, 97, 12289}`. -/
theorem antipodal_epsMCA_F12289_d2 :
    (16 : ℝ≥0∞) / (12289 : ℝ≥0∞)
      ≤ epsMCA (F := ZMod 12289) (evalCode (4134 : ZMod 12289) 16 2) (7 / 16 : ℝ≥0) := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  have h := antipodal_pencil_epsMCA_lower_bound (p := 12289) (n := 16) (h := 8) (d := 2)
    (by norm_num) (by norm_num) (g := (4134 : ZMod 12289)) orderOf_4134
    (by norm_num) (by norm_num)
  have e1 : ((16 : ℕ) : ℝ≥0∞) = (16 : ℝ≥0∞) := by norm_num
  have e2 : ((12289 : ℕ) : ℝ≥0∞) = (12289 : ℝ≥0∞) := by norm_num
  have e3 : (1 : ℝ≥0) - ((8 + 1 : ℕ) : ℝ≥0) / ((16 : ℕ) : ℝ≥0) = 7 / 16 := by
    have hd : ((8 + 1 : ℕ) : ℝ≥0) / ((16 : ℕ) : ℝ≥0) = 9 / 16 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e1, e2, e3] at h
  exact h

/-- The same sixteen-scalar family against the `d = 4` code (rate `5/16`). -/
theorem antipodal_epsMCA_F12289_d4 :
    (16 : ℝ≥0∞) / (12289 : ℝ≥0∞)
      ≤ epsMCA (F := ZMod 12289) (evalCode (4134 : ZMod 12289) 16 4) (7 / 16 : ℝ≥0) := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  have h := antipodal_pencil_epsMCA_lower_bound (p := 12289) (n := 16) (h := 8) (d := 4)
    (by norm_num) (by norm_num) (g := (4134 : ZMod 12289)) orderOf_4134
    (by norm_num) (by norm_num)
  have e1 : ((16 : ℕ) : ℝ≥0∞) = (16 : ℝ≥0∞) := by norm_num
  have e2 : ((12289 : ℕ) : ℝ≥0∞) = (12289 : ℝ≥0∞) := by norm_num
  have e3 : (1 : ℝ≥0) - ((8 + 1 : ℕ) : ℝ≥0) / ((16 : ℕ) : ℝ≥0) = 7 / 16 := by
    have hd : ((8 + 1 : ℕ) : ℝ≥0) / ((16 : ℕ) : ℝ≥0) = 9 / 16 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e1, e2, e3] at h
  exact h

/-- **The sharpened floor of the level-1 obligation** (`d = 2`): the antipodal pencil at
radius `7/16 < 5/8` forces any budget satisfying the obligation to be at least `16/p`.
Together with the bad side, the conditional pin band is exactly trapped in
`[16/p, 32/p)` — the probed truth of the good side (worst stack at threshold 7) is `16`,
attained by the pencil itself, so the band is tight at the bottom. -/
theorem level1_interior_floor16_F12289 (εstar : ℝ≥0∞)
    (hint : ∀ δ : ℝ≥0, δ < 5 / 8 →
      epsMCA (F := ZMod 12289) (evalCode (4134 : ZMod 12289) 16 2) δ ≤ εstar) :
    (16 : ℝ≥0∞) / (12289 : ℝ≥0∞) ≤ εstar :=
  le_trans antipodal_epsMCA_F12289_d2 (hint (7 / 16) (by norm_num))

/-- **THE `d = 4` LEVEL-1 RUNG IS REFUTED**: at every budget `ε* < 16/p` — the *entire*
band where the level-1 bad side bites at the second instance — the threshold is at most
`7/16`, strictly below the rung `1/2`.  The staircase value `1/2` is never `δ*` on its
own band: the antipodal pencil (count `16 = K_1` exactly) bites first.  Envelope-exactness
at this rung is **false**, not merely unproven. -/
theorem deltaStar_lt_levelOne_rung_F12289_d4 (εstar : ℝ≥0∞)
    (hεstar : εstar < (16 : ℝ≥0∞) / (12289 : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod 12289) (A := ZMod 12289)
        (evalCode (4134 : ZMod 12289) 16 4) εstar ≤ 7 / 16 :=
  mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le hεstar antipodal_epsMCA_F12289_d4)

/-- The `d = 4` level-1 interior obligation is **unsatisfiable** on the rung's band: the
obligation at `δ = 7/16 < 1/2` already forces `ε* ≥ 16/p`, contradicting `ε* < 16/p`.
(Contrast with the `d = 2` instance, where the band `[16/p, 32/p)` survives.) -/
theorem level1_interior_unsat_F12289_d4 (εstar : ℝ≥0∞)
    (hint : ∀ δ : ℝ≥0, δ < 1 / 2 →
      epsMCA (F := ZMod 12289) (evalCode (4134 : ZMod 12289) 16 4) δ ≤ εstar)
    (hhi : εstar < (16 : ℝ≥0∞) / (12289 : ℝ≥0∞)) : False :=
  absurd hhi (not_lt_of_ge
    (le_trans antipodal_epsMCA_F12289_d4 (hint (7 / 16) (by norm_num))))

/-- **The unconditional good side from the sharpened ownership engine**, at every radius
strictly below the level-1 rung: threshold `w₀ = 6` (i.e. witness `≥ 7`) applies whenever
`δ < 5/8`, giving `ε_mca ≤ (C(16,3)·13/C(7,3))/p = 208/p`.  This is the best the
per-witness counting surface can do here (see the wall lemmas) — a factor `≈ 40` above
the probed truth `5`, and strictly above the level-1 budget edge `32`. -/
theorem level1_engine_goodSide_F12289 (δ : ℝ≥0) (hδ : δ < 5 / 8) :
    epsMCA (F := ZMod 12289) (evalCode (4134 : ZMod 12289) 16 2) δ
      ≤ (208 : ℝ≥0∞) / (12289 : ℝ≥0∞) := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  have hδ6 : ((6 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin 16) : ℝ≥0) := by
    have hsum : δ + 3 / 8 < 1 := by
      calc δ + 3 / 8 < 5 / 8 + 3 / 8 := by gcongr
      _ = 1 := by norm_num
    have hlt : (3 / 8 : ℝ≥0) < 1 - δ := lt_tsub_iff_right.mpr (by rwa [add_comm] at hsum)
    have hcard : ((Fintype.card (Fin 16) : ℕ) : ℝ≥0) = 16 := by
      rw [Fintype.card_fin]; norm_num
    rw [hcard]
    calc ((6 : ℕ) : ℝ≥0) = (3 / 8 : ℝ≥0) * 16 := by norm_num
    _ < (1 - δ) * 16 := mul_lt_mul_of_pos_right hlt (by norm_num)
  have h := sharpened_epsMCA_le (p := 12289) (g := (4134 : ZMod 12289)) (n := 16)
    2 6 ginj_4134 (by norm_num) hδ6
  have e1 : ((16 : ℕ).choose (2 + 1) * (16 - (2 + 1)) / (6 + 1).choose (2 + 1) : ℕ)
      = 208 := rfl
  have e2 : ((12289 : ℕ) : ℝ≥0∞) = (12289 : ℝ≥0∞) := by norm_num
  calc epsMCA (F := ZMod 12289) (evalCode (4134 : ZMod 12289) 16 2) δ
      ≤ (((16 : ℕ).choose (2 + 1) * (16 - (2 + 1)) / (6 + 1).choose (2 + 1) : ℕ) : ℝ≥0∞)
        / ((12289 : ℕ) : ℝ≥0∞) := h
  _ = (208 : ℝ≥0∞) / (12289 : ℝ≥0∞) := by rw [e1, e2]; norm_num

/-- **Unconditional beyond-Johnson `δ*` lower bound at the small prime**: for every budget
`ε* ≥ 208/p`, the threshold of the dim-3 code at `p = 12289` is at least the level-1 rung
`5/8` — strictly beyond Johnson `1 − √(3/16) ≈ 0.567`.  Notable because the landed pin
family says nothing at this prime (its `hp` needs `p > 2³²`): the radius-decoupled engine
bound alone localizes `δ*` above the rung at budgets where the staircase is silent. -/
theorem deltaStar_ge_level1_radius_F12289 (εstar : ℝ≥0∞)
    (h : (208 : ℝ≥0∞) / (12289 : ℝ≥0∞) ≤ εstar) :
    (5 / 8 : ℝ≥0) ≤ mcaDeltaStar (F := ZMod 12289) (A := ZMod 12289)
      (evalCode (4134 : ZMod 12289) 16 2) εstar := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  by_contra hnot
  rw [not_le] at hnot
  obtain ⟨δ, hδlo, hδhi⟩ := exists_between hnot
  have h58 : (5 / 8 : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by norm_num : (0 : ℝ≥0) < 8)]
    norm_num
  have hgood : δ ≤ mcaDeltaStar (F := ZMod 12289) (A := ZMod 12289)
      (evalCode (4134 : ZMod 12289) 16 2) εstar :=
    le_mcaDeltaStar_of_good _ _ (le_of_lt (lt_of_lt_of_le hδhi h58))
      (le_trans (level1_engine_goodSide_F12289 δ hδhi) h)
  exact absurd hgood (not_le_of_gt hδlo)

/-- **THE CONDITIONAL LEVEL-1 PIN** (first biting instance): granting the level-1 interior
obligation, every budget `ε* < 32/p` satisfying it pins

  `mcaDeltaStar(evalCode 4134 16 2, ε*) = 5/8`

**exactly** — the first beyond-level-0 exactness statement of the staircase envelope.  The
obligation is genuinely open but trapped tightly: it forces `ε* ≥ 16/p`
(`level1_interior_floor16_F12289` — the antipodal pencil), so the live band is
`[16/p, 32/p)`; the probed worst stack at threshold 7 is exactly `16` (the pencil itself),
so the band is probe-consistent and tight at the bottom; and the wall lemmas below prove
the in-tree per-witness counting surface cannot discharge it (cap `52 > 31`).
Envelope-exactness at this rung is exactly this one hypothesis — and unlike the `d = 4`
instance (refuted below), it remains open rather than false. -/
theorem deltaStar_level1_pin_F12289_of_interior (εstar : ℝ≥0∞)
    (hint : ∀ δ : ℝ≥0, δ < 5 / 8 →
      epsMCA (F := ZMod 12289) (evalCode (4134 : ZMod 12289) 16 2) δ ≤ εstar)
    (hhi : εstar < (32 : ℝ≥0∞) / (12289 : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod 12289) (A := ZMod 12289)
        (evalCode (4134 : ZMod 12289) 16 2) εstar = 5 / 8 := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  have e1 : ((2 : ℕ) ^ 3 * ((2 : ℕ) ^ (4 - 1 - 1)).choose 3 : ℕ) = 32 := rfl
  have e2 : ((12289 : ℕ) : ℝ≥0∞) = (12289 : ℝ≥0∞) := by norm_num
  have e3 : (1 : ℝ≥0) - ((3 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (4 - 1)) = 5 / 8 := by
    have hd : ((3 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (4 - 1)) = 3 / 8 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  have e0 : ((4 : ℕ) - 2) * 1 = 2 := rfl
  have h := subceiling_deltaStar_pin_of_interior (p := 12289) (n := 16) (μ := 4)
    (m := 1) (j := 1) (r := 4) (r' := 3) (by norm_num) (g := (4134 : ZMod 12289))
    (by norm_num) (by norm_num) orderOf_4134 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) εstar (by rw [e1, e2]; exact_mod_cast hhi) ?_
  · rw [e0, e3] at h
    exact h
  · intro δ hδ
    rw [e0]
    exact hint δ (by rwa [e3] at hδ)

end Concrete12289

/-! ## The wall: per-witness subset counting provably cannot discharge the obligation

The level-1 budget edge is `K_1 = 2³·C(4,3) = 32`.  Any per-witness `(d+2)`-subset
ownership argument at threshold 7 bounds `#bad · X ≤ C(16,4)` with `X ≤ C(7,4) = 35` (a
minimal witness has only `35` subsets), and the realizable extremal ownership is
`C(6,3) = 20` (`deviation_ownership_card`).  All three resulting caps — the proven engine
value `208`, the realizable-extremal cap `91`, the absolute cap `52` — exceed the budget
edge: the obligation lies strictly outside the scheme, at this instance and (since `K_j`
shrinks exponentially down the staircase while the caps are polynomial in `n`) at every
sub-ceiling rung.  This is the concrete consequence of the saturation theorem: the next
move on the staircase good side must abandon per-witness subset counting. -/

/-- The engine value at threshold 7 exceeds the level-1 budget edge: `32 < 208`. -/
theorem level1_budget_lt_engine :
    2 ^ 3 * Nat.choose 4 3 < Nat.choose 16 3 * (16 - 3) / Nat.choose 7 3 := by decide

/-- The realizable-extremal cap (deviation ownership `C(6,3) = 20`) exceeds the budget:
`32 ≤ C(16,4)/C(6,3) = 91`. -/
theorem level1_budget_le_deviation_floor :
    2 ^ 3 * Nat.choose 4 3 ≤ Nat.choose 16 4 / Nat.choose 6 3 := by decide

/-- The **absolute** cap of the scheme — ownership of *every* subset of a minimal witness —
still exceeds the budget: `32 ≤ C(16,4)/C(7,4) = 52`.  No refinement of per-witness
`(d+2)`-subset counting can certify the level-1 good side. -/
theorem level1_budget_le_subset_cap :
    2 ^ 3 * Nat.choose 4 3 ≤ Nat.choose 16 4 / Nat.choose 7 4 := by decide

/-- Same wall at the second biting instance (`d = 4`, threshold 9, budget `K_1 = 16`):
the engine value is `C(16,5)·11/C(10,5) = 190 > 16`. -/
theorem level1_budget_lt_engine_d4 :
    2 ^ 4 * Nat.choose 4 4 < Nat.choose 16 5 * (16 - 5) / Nat.choose 10 5 := by decide

end ArkLib.ProximityGap.Level1Rung

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.Level1Rung.subceiling_deltaStar_pin_of_interior
#print axioms ArkLib.ProximityGap.Level1Rung.antipodal_pencil_epsMCA_lower_bound
#print axioms ArkLib.ProximityGap.Level1Rung.mcaDeltaStar_le_antipodal
#print axioms ArkLib.ProximityGap.Level1Rung.ginj_4134
#print axioms ArkLib.ProximityGap.Level1Rung.level2_epsMCA_floor_F12289
#print axioms ArkLib.ProximityGap.Level1Rung.level1_interior_floor_F12289
#print axioms ArkLib.ProximityGap.Level1Rung.antipodal_epsMCA_F12289_d2
#print axioms ArkLib.ProximityGap.Level1Rung.antipodal_epsMCA_F12289_d4
#print axioms ArkLib.ProximityGap.Level1Rung.level1_interior_floor16_F12289
#print axioms ArkLib.ProximityGap.Level1Rung.deltaStar_lt_levelOne_rung_F12289_d4
#print axioms ArkLib.ProximityGap.Level1Rung.level1_interior_unsat_F12289_d4
#print axioms ArkLib.ProximityGap.Level1Rung.level1_engine_goodSide_F12289
#print axioms ArkLib.ProximityGap.Level1Rung.deltaStar_ge_level1_radius_F12289
#print axioms ArkLib.ProximityGap.Level1Rung.deltaStar_level1_pin_F12289_of_interior
#print axioms ArkLib.ProximityGap.Level1Rung.level1_budget_lt_engine
#print axioms ArkLib.ProximityGap.Level1Rung.level1_budget_le_deviation_floor
#print axioms ArkLib.ProximityGap.Level1Rung.level1_budget_le_subset_cap
#print axioms ArkLib.ProximityGap.Level1Rung.level1_budget_lt_engine_d4

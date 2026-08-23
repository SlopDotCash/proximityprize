/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26WitnessSpread
import ArkLib.Data.CodingTheory.ProximityGap.QuotientDeepCore

/-!
# The DEEP-quotient transfer engine: list-decoding lower bounds ⟹ MCA lower bounds

Issue #334, hypothesis A4.  [KKH26] (ePrint 2026/782, Appendix A) converts a *list-decoding
configuration* into *MCA bad scalars*: given a word `u` on the smooth domain `H = ⟨g⟩ ⊆ F_p^×`
of size `n`, the projection `π : x ↦ x^m`, and a list of `m`-power codewords
`c(x) = ĉ(x^m)` (with `deg ĉ ≤ D`, so `deg c ≤ d = D·m`) agreeing with `u` on large sets,
pick `w` whose `m`-fiber is disjoint from `H` (`x^m ≠ w` on `H`) and form the *DEEP quotient
stack*

  `u₀(x) = u(x)/(x^m − w)`, `u₁(x) = 1/(x^m − w)`   (pointwise on `H`).

For each list element, `γ_c := −ĉ(w)` is a bad scalar of the line `(u₀, u₁)` against the
degree-`(D−1)·m` evaluation code: on the agreement set `S_c` the line point `u₀ + γ_c·u₁`
*equals* the evaluation of the divided-difference polynomial `((ĉ(Y) − ĉ(w))/(Y − w))∘Y:=X^m`,
and the agreement set itself is the `mcaEvent` witness — verbatim, with **no radius loss**
(probe ground truth: `scripts/probes/probe_deep_quotient_transfer.py`, exit 0).

The honest hard clause is the *joint-pair refusal*: `mcaEvent` demands that no pair of
codewords jointly agrees with `(u₀, u₁)` on `S_c`.  Since the pair requires **both** rows to
agree, refusing `u₁` alone suffices: a codeword `q₁` of degree ≤ `(D−1)·m` agreeing with
`1/(x^m − w)` on `S` makes `q₁(x)·(x^m − w) − 1` (degree ≤ `D·m`) vanish on `|S|` points, so
`|S| ≥ D·m + 1` kills it (`QuotientCore.farness_card_le`).  **This size threshold is
load-bearing, not cosmetic**: the probe's boundary diagnostic shows that once agreement sets
shrink to ≤ `D` fibers (`|S| ≤ D·m`), both `u₀` and `u₁` extend on the witness and the
joint-pair clause destroys the transfer.  The fiber-shaped hypothesis of [KKH26] (`≥ D+1`
full `m`-fibers, i.e. `|S| ≥ (D+1)·m`) implies the threshold via
`card_threshold_of_fiber_agreement`.

## Main results

* `deepU0`, `deepU1` — the DEEP-quotient stack.
* `deep_quotient_line_codeword` — the quotient step: an `m`-power list element agreeing with
  `u` on `S` yields a degree-`(D−1)·m` codeword equal to `u₀ + (−ĉ(w))·u₁` on `S`.
* `deepU1_not_extendable` — the joint-pair refusal: above the degree budget (`|S| ≥ D·m+1`),
  no degree-`(D−1)·m` codeword agrees with `u₁` on `S`.
* `deep_quotient_mcaEvent` — per-element assembly: each list element fires `mcaEvent` at
  `γ_c = −ĉ(w)` with witness `S_c`.
* `deep_quotient_epsMCA_lower_bound` — **the headline**: a list of `L` `m`-power elements
  with pairwise-distinct `ĉ(w)` values gives `ε_mca(C_{(D−1)m}, δ) ≥ L/p` — the generic
  transfer engine behind the [KKH26] witness-spread assembly
  (`kkh26_epsMCA_lower_bound` is its specialization to the gap word `X^{rm}`).

The separation-of-`ĉ(w)`-values supply (BCIKS20 Lemma 3 style averaging over `w`) is **not**
formalized here; distinctness is carried as a hypothesis of the headline, exactly as the
probe carries it as an assertion.

## References

* [KKH26] D. Krachun, S. Kazanin, U. Haböck, *Failure of proximity gaps close to capacity*,
  ePrint 2026/782, Appendix A.
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, ePrint 2020/654 (DEEP quotient / out-of-domain sampling).
* [ABF26] Arnon, Boneh, Fenzi, *Open Problems in List Decoding and Correlated Agreement*,
  ePrint 2026/680 (the `mcaEvent` / `ε_mca` formalism).  Tracking issue #334.
-/

set_option linter.unusedSectionVars false

open Polynomial Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ArkLib.ProximityGap.DeepQuotientTransfer

variable {p n : ℕ} [Fact p.Prime] [NeZero n] {g w : ZMod p} {m D : ℕ}

/-- First row of the DEEP-quotient stack: `u₀(x) = u(x)/(x^m − w)` evaluated along the
smooth domain `x = g^j`. -/
def deepU0 (g w : ZMod p) (m : ℕ) (u : Fin n → ZMod p) : Fin n → ZMod p :=
  fun j => u j * ((g ^ (j : ℕ)) ^ m - w)⁻¹

/-- Second row of the DEEP-quotient stack: `u₁(x) = 1/(x^m − w)` along `x = g^j`. -/
def deepU1 (g w : ZMod p) (m : ℕ) : Fin n → ZMod p :=
  fun j => ((g ^ (j : ℕ)) ^ m - w)⁻¹

/-- Injectivity of `i ↦ g^i` below the order of `g`, for nonzero `g` in a field.
(Local copy of the private helper in `KKH26WitnessSpread.lean`.) -/
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

/-- The fiber-shaped agreement hypothesis implies the degree-budget threshold:
agreement on at least `D + 1` full `m`-fibers (`(D+1)·m` points) exceeds the
quotient degree budget `D·m`.  This is the bridge the [KKH26] assembly instantiates
(its fibers have exactly `m` points each, by `fiber_count`). -/
theorem card_threshold_of_fiber_agreement {c : ℕ} (hm : 1 ≤ m) (hc : (D + 1) * m ≤ c) :
    D * m + 1 ≤ c := by
  have h1 : (D + 1) * m = D * m + m := by rw [Nat.add_mul, one_mul]
  exact le_trans (Nat.add_le_add_left hm (D * m)) (h1 ▸ hc)

/-- **The quotient step (per list element).**  If the `m`-power polynomial `ĉ(X^m)` (with
`deg ĉ ≤ D`) agrees with `u` on `S ⊆ H`, then for the scalar `γ = −ĉ(w)` the quotient line
point `u₀ + γ·u₁` agrees **on the same set `S`** with a codeword of the degree-`(D−1)·m`
evaluation code: the divided difference `(ĉ(Y) − ĉ(w))/(Y − w)` composed with `Y := X^m`.
The fiber-disjointness hypothesis `hw` keeps the denominator `x^m − w` invertible on `H`. -/
theorem deep_quotient_line_codeword (hm : 1 ≤ m)
    (u : Fin n → ZMod p) (qhat : Polynomial (ZMod p)) (hq : qhat.natDegree ≤ D)
    (S : Finset (Fin n))
    (hagree : ∀ j ∈ S, u j = qhat.eval ((g ^ (j : ℕ)) ^ m))
    (hw : ∀ j : Fin n, (g ^ (j : ℕ)) ^ m ≠ w) :
    ∃ v ∈ KKH26.evalCode g n ((D - 1) * m), ∀ j ∈ S,
      v j = deepU0 g w m u j + (-(qhat.eval w)) • deepU1 g w m j := by
  obtain ⟨h, hh⟩ := QuotientCore.quotient_exists qhat w m
  have hhdeg : h.natDegree ≤ (D - 1) * m :=
    QuotientCore.quotient_natDegree_le (m := m) (r := D + 1) hm (Nat.le_add_left 1 D) hq hh
  refine ⟨fun j => h.eval (g ^ (j : ℕ)), ⟨h, hhdeg, fun _ => rfl⟩, ?_⟩
  intro j hj
  have hne : (g ^ (j : ℕ)) ^ m - w ≠ 0 := sub_ne_zero.mpr (hw j)
  have hev := congrArg (Polynomial.eval (g ^ (j : ℕ))) hh
  simp only [eval_sub, eval_mul, eval_comp, eval_pow, eval_X, eval_C] at hev
  -- hev : qhat.eval ((g^j)^m) − qhat.eval w = ((g^j)^m − w) * h.eval (g^j)
  have hev' : h.eval (g ^ (j : ℕ)) * ((g ^ (j : ℕ)) ^ m - w)
      = qhat.eval ((g ^ (j : ℕ)) ^ m) - qhat.eval w := by linear_combination -hev
  have hkey : h.eval (g ^ (j : ℕ))
      = (qhat.eval ((g ^ (j : ℕ)) ^ m) - qhat.eval w) * ((g ^ (j : ℕ)) ^ m - w)⁻¹ := by
    rw [← hev', mul_assoc, mul_inv_cancel₀ hne, mul_one]
  simp only [deepU0, deepU1, smul_eq_mul]
  rw [hagree j hj, hkey]
  ring

/-- **The joint-pair refusal.**  Above the quotient degree budget — `|S| ≥ D·m + 1` — no
codeword of the degree-`(D−1)·m` evaluation code agrees with `u₁ = 1/(x^m − w)` on `S`:
agreement points are roots of `q₁(X)·(X^m − w) − 1` (degree ≤ `D·m`, never identically zero
because `X^m − w` is no unit).  Since `pairJointAgreesOn` requires **both** rows to be
matched, this single-row refusal already denies every joint pair on `S`.

This is exactly where the probe's boundary diagnostic lives: at `|S| ≤ D·m` (≤ `D` fibers)
the refusal genuinely fails and the transfer stops — the threshold cannot be weakened. -/
theorem deepU1_not_extendable (hg : orderOf g = n) (hm : 1 ≤ m) (hD : 1 ≤ D)
    (S : Finset (Fin n)) (hScard : D * m + 1 ≤ S.card)
    (hw : ∀ j : Fin n, (g ^ (j : ℕ)) ^ m ≠ w) :
    ¬ ∃ v ∈ KKH26.evalCode g n ((D - 1) * m), ∀ j ∈ S, v j = deepU1 g w m j := by
  rintro ⟨v, ⟨q₁, hq₁deg, hq₁⟩, hvS⟩
  have hg0 : g ≠ 0 := by
    rintro rfl
    have h1 : (0 : ZMod p) ^ n = 1 := by rw [← hg]; exact pow_orderOf_eq_one 0
    rw [zero_pow (NeZero.ne n)] at h1
    exact zero_ne_one h1
  -- push `S` into the field: distinct indices give distinct domain points
  set Hdom : Finset (ZMod p) := S.image (fun j : Fin n => g ^ (j : ℕ)) with hHdom
  have hcard : Hdom.card = S.card :=
    Finset.card_image_of_injOn fun i _ i' _ hii' =>
      Fin.ext (pow_inj_below_order hg0 hg _ i.isLt _ i'.isLt hii')
  -- on every point of `Hdom`, the candidate satisfies the unit equation
  have hall : ∀ x ∈ Hdom, q₁.eval x * (x ^ m - w) = 1 := by
    intro x hx
    obtain ⟨j, hjS, rfl⟩ := Finset.mem_image.mp hx
    have hne : (g ^ (j : ℕ)) ^ m - w ≠ 0 := sub_ne_zero.mpr (hw j)
    have hval : q₁.eval (g ^ (j : ℕ)) = ((g ^ (j : ℕ)) ^ m - w)⁻¹ :=
      (hq₁ j).symm.trans (hvS j hjS)
    rw [hval]
    exact inv_mul_cancel₀ hne
  -- root counting: `q₁(X)·(X^m − w) − 1` has degree ≤ D·m, so ≤ D·m agreement points
  have hsub : Hdom ⊆ Hdom.filter (fun x => q₁.eval x * (x ^ m - w) = 1) :=
    fun x hx => Finset.mem_filter.mpr ⟨hx, hall x hx⟩
  have hbound := QuotientCore.farness_card_le Hdom w (Nat.le_add_left 1 ((D - 1) * m)) hm q₁
    (Nat.lt_succ_of_le hq₁deg)
  have hineq : S.card ≤ (D - 1) * m + 1 + m - 1 := by
    rw [← hcard]
    exact le_trans (Finset.card_le_card hsub) hbound
  have e1 : (D - 1) * m + 1 + m - 1 = (D - 1) * m + m := by
    generalize (D - 1) * m = a
    omega
  have e2 : (D - 1) * m + m = D * m := by
    have hD' : D - 1 + 1 = D := Nat.sub_add_cancel hD
    calc (D - 1) * m + m = (D - 1 + 1) * m := by rw [Nat.add_mul, one_mul]
      _ = D * m := by rw [hD']
  have hfin : S.card ≤ D * m := by rw [← e2, ← e1]; exact hineq
  exact absurd (le_trans hScard hfin) (Nat.not_succ_le_self (D * m))

/-- **Per-element transfer: each list element fires `mcaEvent`.**  An `m`-power list element
`ĉ(X^m)` agreeing with `u` on a set `S` of size `≥ (1−δ)·n` *and* above the degree budget
(`|S| ≥ D·m + 1`) makes `γ = −ĉ(w)` a bad scalar of the DEEP-quotient stack against the
degree-`(D−1)·m` evaluation code, with witness set `S` **verbatim** (no radius loss). -/
theorem deep_quotient_mcaEvent (hg : orderOf g = n) (hm : 1 ≤ m) (hD : 1 ≤ D) (δ : ℝ≥0)
    (u : Fin n → ZMod p) (qhat : Polynomial (ZMod p)) (hq : qhat.natDegree ≤ D)
    (S : Finset (Fin n))
    (hSsize : ((S.card : ℝ≥0)) ≥ (1 - δ) * Fintype.card (Fin n))
    (hScard : D * m + 1 ≤ S.card)
    (hagree : ∀ j ∈ S, u j = qhat.eval ((g ^ (j : ℕ)) ^ m))
    (hw : ∀ j : Fin n, (g ^ (j : ℕ)) ^ m ≠ w) :
    mcaEvent (KKH26.evalCode g n ((D - 1) * m)) δ (deepU0 g w m u) (deepU1 g w m)
      (-(qhat.eval w)) := by
  obtain ⟨v, hvmem, hvagree⟩ := deep_quotient_line_codeword hm u qhat hq S hagree hw
  refine ⟨S, hSsize, ⟨v, hvmem, hvagree⟩, ?_⟩
  rintro ⟨v₀, -, v₁, hv₁, hpair⟩
  exact deepU1_not_extendable hg hm hD S hScard hw
    ⟨v₁, hv₁, fun j hj => (hpair j hj).2⟩

open Classical in
/-- **The DEEP-quotient transfer engine ([KKH26] Appendix A, generic form).**  Given a
list-decoding configuration for the `m`-power subfamily — a family of `L` polynomials
`ĉ_c` of degree ≤ `D` agreeing with the word `u` on sets `S_c` of size ≥ `(1−δ)·n` and
above the quotient degree budget (`|S_c| ≥ D·m + 1`) — and an out-of-domain shift `w`
(fiber disjoint from `H`) **separating** the list (`ĉ_c(w)` pairwise distinct), the MCA
error of the degree-`(D−1)·m` evaluation code satisfies

  `ε_mca(C_{(D−1)m}, δ) ≥ L / p`.

Each list element contributes its own bad scalar `γ_c = −ĉ_c(w)` witnessed by its own
agreement set `S_c` — the spread of distinct witness sets that
`MCAWitnessSpread.unique_bad_gamma_common_witness` proves is necessary for any multi-scalar
bound.  Composition with `epsMCA_ge_card_div_of_mcaEvent_set` is exact: list-decoding
lower bounds transfer to MCA lower bounds with **no loss in the count and no radius loss**. -/
theorem deep_quotient_epsMCA_lower_bound {ιL : Type*} [Fintype ιL]
    (hg : orderOf g = n) (hm : 1 ≤ m) (hD : 1 ≤ D) (δ : ℝ≥0)
    (u : Fin n → ZMod p)
    (qhat : ιL → Polynomial (ZMod p)) (S : ιL → Finset (Fin n))
    (hq : ∀ c, (qhat c).natDegree ≤ D)
    (hSsize : ∀ c, (((S c).card : ℝ≥0)) ≥ (1 - δ) * Fintype.card (Fin n))
    (hScard : ∀ c, D * m + 1 ≤ (S c).card)
    (hagree : ∀ c, ∀ j ∈ S c, u j = (qhat c).eval ((g ^ (j : ℕ)) ^ m))
    (hw : ∀ j : Fin n, (g ^ (j : ℕ)) ^ m ≠ w)
    (hsep : Function.Injective fun c => (qhat c).eval w) :
    (Fintype.card ιL : ℝ≥0∞) / (p : ℝ≥0∞)
      ≤ epsMCA (F := ZMod p) (KKH26.evalCode g n ((D - 1) * m)) δ := by
  classical
  -- the bad-scalar set: one scalar per list element, distinct by the separation hypothesis
  set G : Finset (ZMod p) := Finset.univ.image (fun c : ιL => -((qhat c).eval w)) with hG
  have hinj : Function.Injective fun c : ιL => -((qhat c).eval w) :=
    fun a b hab => hsep (neg_injective hab)
  have hGcard : G.card = Fintype.card ιL := by
    rw [hG, Finset.card_image_of_injective Finset.univ hinj, Finset.card_univ]
  -- every scalar in G fires mcaEvent on the DEEP-quotient stack
  have hbad : ∀ γ ∈ G,
      mcaEvent (KKH26.evalCode g n ((D - 1) * m)) δ
        ((![deepU0 g w m u, deepU1 g w m] : WordStack (ZMod p) (Fin 2) (Fin n)) 0)
        (![deepU0 g w m u, deepU1 g w m] 1) γ := by
    intro γ hγ
    rw [hG] at hγ
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hγ
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using
      deep_quotient_mcaEvent hg hm hD δ u (qhat c) (hq c) (S c) (hSsize c) (hScard c)
        (hagree c) hw
  -- compose with the in-tree multi-scalar engine
  have hengine := _root_.ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (F := ZMod p) (KKH26.evalCode g n ((D - 1) * m)) δ
    (![deepU0 g w m u, deepU1 g w m]) G hbad
  rw [ZMod.card p, hGcard] at hengine
  exact hengine

end ArkLib.ProximityGap.DeepQuotientTransfer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.DeepQuotientTransfer.card_threshold_of_fiber_agreement
#print axioms ArkLib.ProximityGap.DeepQuotientTransfer.deep_quotient_line_codeword
#print axioms ArkLib.ProximityGap.DeepQuotientTransfer.deepU1_not_extendable
#print axioms ArkLib.ProximityGap.DeepQuotientTransfer.deep_quotient_mcaEvent
#print axioms ArkLib.ProximityGap.DeepQuotientTransfer.deep_quotient_epsMCA_lower_bound

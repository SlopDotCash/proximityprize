/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WindowTwoLayerThreshold

/-!
# The generic folded-sum threshold engine: mod-p transfer for ANY weighted root-of-unity sum

Campaign #357. The two-layer transfer mechanism — fold a sum of `2^m`-th roots of unity into
a degree-`< 2^(m−1)` integer polynomial, bound its `ℓ¹` mass, and invoke the resultant
threshold (`not_isRoot_of_l1On_pow_lt`) — has so far been instantiated once, for the `e₂`
pair census (`WindowTwoLayerThreshold.lean`). The census programme needs the same transfer
for several other vanishing-sum surfaces (the vertical-stratum two-root threshold, the
slanted-stratum 12-term determinant sums, the excess-band minors of O147/O148). This file
provides the engine **once, in full generality**:

* `foldedCoeff` / `foldedSum` — for any finite index family `S : Finset ι` with exponents
  `e : ι → ℕ` and integer weights `w : ι → ℤ`, the canonical degree-`< 2^(m−1)`
  representative of `∑_{x∈S} w(x)·ζ^{e(x)}` modulo `Φ_{2^m}` (exponents reduced mod `2^m`,
  the upper half folded through `X^(2^(m−1)) ≡ −1`);
* `foldedSum_eval` — folding is faithful: evaluation at any primitive `2^m`-th root of
  unity mod `p` recovers the weighted sum;
* `l1On_foldedSum_le` — the `ℓ¹` mass is at most `2^(m−1) · ∑|w|`;
* **`foldedSum_vanishing_iff_char0`** — the two-layer law for arbitrary weighted sums: for
  `p` above the explicit threshold `(2^(m−1) · ∑|w|)^(2^(m−1))`, the sum vanishes mod `p`
  **iff** the folded polynomial vanishes in characteristic zero. Above the threshold there
  is no characteristic-`p` arithmetic at all: every vanishing is a classical (Lam–Leung
  territory) vanishing-sum configuration, and every characteristic-zero vanishing descends.
* `foldedSum_ne_zero_of_char0` — the consumable contrapositive (transfer of char-0
  nonvanishing to all large primes).
* `e2Folded_eq_foldedSum` — the `e₂` census engine is the `w ≡ 1` instance over
  `upperPairs` (definitional sanity weld back to the landed instance).

## Consumers

Any census/incidence surface of the form "this explicit sum of roots of unity vanishes":
instantiate `ι`, `e`, `w`, compute `∑|w|`, and both transfer directions are immediate. The
12-term slanted determinant sums have `∑|w| = 12`; two-root coincidences have `∑|w| = 2`;
excess-band minors have `∑|w| ≤` the minor's permanent bound. All results `sorry`-free and
axiom-clean.

## References

* [KKH26] ePrint 2026/782 (the resultant/`ℓ¹` machinery, `KKH26SumsOfRootsOfUnity.lean`).
* Issue #357 (census programme round 11: the mod-p transfer surfaces).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Finset
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.WindowTwoLayer

variable {ι : Type*}

/-! ## The folded polynomial of a weighted exponent family -/

/-- The `t`-th folded coefficient: weights of indices whose exponent reduces to `t` count
positively, those reducing to `t + 2^(m−1)` count negatively (the fold
`X^(2^(m−1)) ≡ −1`). -/
def foldedCoeff (m : ℕ) (S : Finset ι) (e : ι → ℕ) (w : ι → ℤ) (t : ℕ) : ℤ :=
  (∑ x ∈ S.filter (fun x => e x % 2 ^ m = t), w x)
    - ∑ x ∈ S.filter (fun x => e x % 2 ^ m = t + 2 ^ (m - 1)), w x

/-- The folded polynomial: the canonical degree-`< 2^(m−1)` representative of
`∑_{x∈S} w(x)·ζ^{e(x)}` modulo `Φ_{2^m}`. -/
noncomputable def foldedSum (m : ℕ) (S : Finset ι) (e : ι → ℕ) (w : ι → ℤ) : Polynomial ℤ :=
  ∑ t ∈ range (2 ^ (m - 1)), C (foldedCoeff m S e w t) * X ^ t

/-- The `ℓ¹` weight mass of the family. -/
def l1Weight (S : Finset ι) (w : ι → ℤ) : ℕ := ∑ x ∈ S, (w x).natAbs

theorem foldedSum_coeff (m : ℕ) (S : Finset ι) (e : ι → ℕ) (w : ι → ℤ) (j : ℕ) :
    (foldedSum m S e w).coeff j
      = if j < 2 ^ (m - 1) then foldedCoeff m S e w j else 0 := by
  rw [foldedSum, finset_sum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hj : j < 2 ^ (m - 1)
  · rw [if_pos hj]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hj)
      (fun t _ htj => by simp [Ne.symm htj])]
    simp
  · rw [if_neg hj]
    refine Finset.sum_eq_zero fun t ht => ?_
    have htj : j ≠ t := fun h => hj (h ▸ Finset.mem_range.mp ht)
    simp [htj]

theorem foldedSum_natDegree_lt (m : ℕ) (S : Finset ι) (e : ι → ℕ) (w : ι → ℤ) :
    (foldedSum m S e w).natDegree < 2 ^ (m - 1) := by
  by_cases h0 : foldedSum m S e w = 0
  · rw [h0]
    simpa using pow_pos (by norm_num : (0 : ℕ) < 2) (m - 1)
  · rw [Polynomial.natDegree_lt_iff_degree_lt h0, Polynomial.degree_lt_iff_coeff_zero]
    intro j hj
    rw [foldedSum_coeff]
    have : ¬ j < 2 ^ (m - 1) := not_lt.mpr (by exact_mod_cast hj)
    simp [this]

/-- Each folded coefficient is bounded by the total weight mass (the two residue fibers
are disjoint subfamilies of `S`). -/
theorem foldedCoeff_natAbs_le (m : ℕ) (hm : 1 ≤ m) (S : Finset ι) (e : ι → ℕ) (w : ι → ℤ)
    (t : ℕ) : (foldedCoeff m S e w t).natAbs ≤ l1Weight S w := by
  classical
  have hdisj : Disjoint (S.filter (fun x => e x % 2 ^ m = t))
      (S.filter (fun x => e x % 2 ^ m = t + 2 ^ (m - 1))) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    have e1 := (Finset.mem_filter.mp h1).2
    have e2 := (Finset.mem_filter.mp h2).2
    have hpos : 0 < 2 ^ (m - 1) := pow_pos (by norm_num) _
    omega
  calc (foldedCoeff m S e w t).natAbs
      ≤ (∑ x ∈ S.filter (fun x => e x % 2 ^ m = t), w x).natAbs
        + (∑ x ∈ S.filter (fun x => e x % 2 ^ m = t + 2 ^ (m - 1)), w x).natAbs :=
        Int.natAbs_sub_le _ _
    _ ≤ (∑ x ∈ S.filter (fun x => e x % 2 ^ m = t), (w x).natAbs)
        + ∑ x ∈ S.filter (fun x => e x % 2 ^ m = t + 2 ^ (m - 1)), (w x).natAbs :=
        Nat.add_le_add (Int.natAbs_sum_le _ _) (Int.natAbs_sum_le _ _)
    _ = ∑ x ∈ (S.filter (fun x => e x % 2 ^ m = t))
          ∪ (S.filter (fun x => e x % 2 ^ m = t + 2 ^ (m - 1))), (w x).natAbs :=
        (Finset.sum_union hdisj).symm
    _ ≤ ∑ x ∈ S, (w x).natAbs :=
        Finset.sum_le_sum_of_subset
          (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))

/-- The `ℓ¹` mass of the folded polynomial is at most `2^(m−1) · ∑|w|`. -/
theorem l1On_foldedSum_le (m : ℕ) (hm : 1 ≤ m) (S : Finset ι) (e : ι → ℕ) (w : ι → ℤ) :
    l1On (2 ^ (m - 1)) (foldedSum m S e w) ≤ 2 ^ (m - 1) * l1Weight S w := by
  unfold l1On
  calc ∑ j ∈ range (2 ^ (m - 1)), ((foldedSum m S e w).coeff j).natAbs
      ≤ ∑ _j ∈ range (2 ^ (m - 1)), l1Weight S w := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [foldedSum_coeff, if_pos (Finset.mem_range.mp hj)]
        exact foldedCoeff_natAbs_le m hm S e w j
    _ = 2 ^ (m - 1) * l1Weight S w := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-! ## Folding is faithful at primitive `2^m`-th roots -/

/-- Evaluating the folded polynomial at a primitive `2^m`-th root of unity mod `p` recovers
the weighted sum `∑_{x∈S} w(x)·g^{e(x)}`. -/
theorem foldedSum_eval {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m) {g : ZMod p}
    (hg : IsPrimitiveRoot g (2 ^ m)) (S : Finset ι) (e : ι → ℕ) (w : ι → ℤ) :
    ((foldedSum m S e w).map (Int.castRingHom (ZMod p))).eval g
      = ∑ x ∈ S, (w x : ZMod p) * g ^ (e x) := by
  classical
  have hhalf : g ^ (2 ^ (m - 1)) = -1 := pow_half_eq_neg_one hm hg
  -- LHS: the coefficient-vector form
  have hLHS : ((foldedSum m S e w).map (Int.castRingHom (ZMod p))).eval g
      = ∑ t ∈ range (2 ^ (m - 1)), ((foldedCoeff m S e w t : ZMod p)) * g ^ t := by
    rw [foldedSum, Polynomial.map_sum, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_pow, map_C, map_X, eval_mul, eval_pow, eval_C,
      eval_X]
    norm_cast
  -- RHS: reduce each exponent mod 2^m, then fold the upper half through g^(2^(m-1)) = −1.
  have hpow_mod : ∀ d : ℕ, g ^ d = g ^ (d % 2 ^ m) := by
    intro d
    conv_lhs => rw [← Nat.div_add_mod d (2 ^ m)]
    rw [pow_add, pow_mul, hg.pow_eq_one, one_pow, one_mul]
  have hfold : ∀ d : ℕ, 2 ^ (m - 1) ≤ d → g ^ d = -(g ^ (d - 2 ^ (m - 1))) := by
    intro d hge
    have : g ^ d = g ^ (d - 2 ^ (m - 1)) * g ^ (2 ^ (m - 1)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [this, hhalf, mul_neg_one]
  have hRHS : ∑ x ∈ S, (w x : ZMod p) * g ^ (e x)
      = ∑ t ∈ range (2 ^ (m - 1)), ((foldedCoeff m S e w t : ZMod p)) * g ^ t := by
    have hmaps : ∀ x ∈ S,
        (if e x % 2 ^ m < 2 ^ (m - 1) then e x % 2 ^ m
         else e x % 2 ^ m - 2 ^ (m - 1)) ∈ range (2 ^ (m - 1)) := by
      intro x _
      by_cases hc : e x % 2 ^ m < 2 ^ (m - 1)
      · simpa [hc] using hc
      · have hlt : e x % 2 ^ m < 2 ^ m := Nat.mod_lt _ (by positivity)
        have hsplit : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
          have h := pow_succ 2 (m - 1)
          rw [Nat.sub_add_cancel hm] at h
          omega
        simp only [hc, if_false, Finset.mem_range]
        omega
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => (w x : ZMod p) * g ^ (e x))]
    refine Finset.sum_congr rfl fun t ht => ?_
    have htlt : t < 2 ^ (m - 1) := Finset.mem_range.mp ht
    have hsplit : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
      have h := pow_succ 2 (m - 1)
      rw [Nat.sub_add_cancel hm] at h
      omega
    -- the fiber over t splits into the +1 part (residue t) and the −1 part (residue t+h)
    have hfiber : S.filter (fun x =>
        (if e x % 2 ^ m < 2 ^ (m - 1) then e x % 2 ^ m
         else e x % 2 ^ m - 2 ^ (m - 1)) = t)
      = S.filter (fun x => e x % 2 ^ m = t)
        ∪ S.filter (fun x => e x % 2 ^ m = t + 2 ^ (m - 1)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hx, hfoldx⟩
        by_cases hc : e x % 2 ^ m < 2 ^ (m - 1)
        · left; exact ⟨hx, by simpa [hc] using hfoldx⟩
        · right
          refine ⟨hx, ?_⟩
          rw [if_neg hc] at hfoldx
          have hlt : e x % 2 ^ m < 2 ^ m := Nat.mod_lt _ (by positivity)
          omega
      · rintro (⟨hx, hr⟩ | ⟨hx, hr⟩)
        · exact ⟨hx, by simp [hr, htlt]⟩
        · refine ⟨hx, ?_⟩
          have hc : ¬ e x % 2 ^ m < 2 ^ (m - 1) := by omega
          rw [if_neg hc, hr]
          omega
    have hdisj : Disjoint (S.filter (fun x => e x % 2 ^ m = t))
        (S.filter (fun x => e x % 2 ^ m = t + 2 ^ (m - 1))) := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      have e1 := (Finset.mem_filter.mp h1).2
      have e2 := (Finset.mem_filter.mp h2).2
      have hpos : 0 < 2 ^ (m - 1) := pow_pos (by norm_num) _
      omega
    rw [hfiber, Finset.sum_union hdisj]
    -- the + part: every term is (w x)·g^t
    have hplus : ∑ x ∈ S.filter (fun x => e x % 2 ^ m = t), (w x : ZMod p) * g ^ (e x)
        = ((∑ x ∈ S.filter (fun x => e x % 2 ^ m = t), w x : ℤ) : ZMod p) * g ^ t := by
      have hterm : ∀ x ∈ S.filter (fun x => e x % 2 ^ m = t),
          (w x : ZMod p) * g ^ (e x) = (w x : ZMod p) * g ^ t := by
        intro x hx
        have hr := (Finset.mem_filter.mp hx).2
        rw [hpow_mod, hr]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
      norm_cast
    -- the − part: every term is −(w x)·g^t
    have hminus : ∑ x ∈ S.filter (fun x => e x % 2 ^ m = t + 2 ^ (m - 1)),
          (w x : ZMod p) * g ^ (e x)
        = -(((∑ x ∈ S.filter (fun x => e x % 2 ^ m = t + 2 ^ (m - 1)), w x : ℤ) : ZMod p)
            * g ^ t) := by
      have hterm : ∀ x ∈ S.filter (fun x => e x % 2 ^ m = t + 2 ^ (m - 1)),
          (w x : ZMod p) * g ^ (e x) = -((w x : ZMod p) * g ^ t) := by
        intro x hx
        have hr := (Finset.mem_filter.mp hx).2
        have hsub : t + 2 ^ (m - 1) - 2 ^ (m - 1) = t := by omega
        rw [hpow_mod, hr, hfold _ (Nat.le_add_left _ _), hsub, mul_neg]
      rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, ← Finset.sum_mul]
      norm_cast
    rw [hplus, hminus, foldedCoeff]
    push_cast
    ring
  rw [hLHS, hRHS]

/-! ## The threshold theorem: the two-layer law for arbitrary weighted sums -/

/-- **The generic two-layer law.** For `p` above the explicit threshold
`(2^(m−1) · ∑|w|)^(2^(m−1))`, the weighted root-of-unity sum vanishes mod `p` **iff** its
folded polynomial vanishes in characteristic zero: above the threshold there is no
characteristic-`p` arithmetic — every vanishing is classical, and every characteristic-zero
vanishing descends to every large prime at once. -/
theorem foldedSum_vanishing_iff_char0 {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m)) (S : Finset ι) (e : ι → ℕ) (w : ι → ℤ)
    (hp : (2 ^ (m - 1) * l1Weight S w) ^ 2 ^ (m - 1) < p) :
    ∑ x ∈ S, (w x : ZMod p) * g ^ (e x) = 0 ↔ foldedSum m S e w = 0 := by
  constructor
  · intro hzero
    by_contra hR0
    have hdeg := foldedSum_natDegree_lt m S e w
    have hl1 : l1On (2 ^ (m - 1)) (foldedSum m S e w) ^ 2 ^ (m - 1) < p := by
      calc l1On (2 ^ (m - 1)) (foldedSum m S e w) ^ 2 ^ (m - 1)
          ≤ (2 ^ (m - 1) * l1Weight S w) ^ 2 ^ (m - 1) :=
            Nat.pow_le_pow_left (l1On_foldedSum_le m hm S e w) _
        _ < p := hp
    have hnoroot := not_isRoot_of_l1On_pow_lt hm hg hR0 hdeg hl1
    apply hnoroot
    unfold Polynomial.IsRoot
    rw [foldedSum_eval hm hg S e w, hzero]
  · intro hchar0
    rw [← foldedSum_eval hm hg S e w, hchar0]
    simp

/-- The consumable transfer: characteristic-zero nonvanishing of the folded polynomial
rules out vanishing of the weighted sum at every prime above the threshold. -/
theorem foldedSum_ne_zero_of_char0 {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m)) (S : Finset ι) (e : ι → ℕ) (w : ι → ℤ)
    (hR0 : foldedSum m S e w ≠ 0)
    (hp : (2 ^ (m - 1) * l1Weight S w) ^ 2 ^ (m - 1) < p) :
    ∑ x ∈ S, (w x : ZMod p) * g ^ (e x) ≠ 0 :=
  fun hzero => hR0 ((foldedSum_vanishing_iff_char0 hm hg S e w hp).mp hzero)

/-! ## The balance characterization: characteristic-zero vanishing is a counting condition -/

/-- **Characteristic-zero vanishing ⟺ antipodal fiber balance.** The folded polynomial of
a weight-one family vanishes iff every residue fiber `t` is exactly matched by its
antipodal fiber `t + 2^(m−1)` — the purely combinatorial form of the char-0 census layer
(the object O145 counts). Stated for weight-one families (covers the `e₂` census and all
incidence counts); the general-weight analogue replaces cards by weight sums. -/
theorem foldedSum_eq_zero_iff_balanced (m : ℕ) (S : Finset ι) (e : ι → ℕ) :
    foldedSum m S e (fun _ => 1) = 0 ↔ ∀ t < 2 ^ (m - 1),
      (S.filter (fun x => e x % 2 ^ m = t)).card
        = (S.filter (fun x => e x % 2 ^ m = t + 2 ^ (m - 1))).card := by
  constructor
  · intro h0 t ht
    have hc := congrArg (fun P : Polynomial ℤ => P.coeff t) h0
    simp only [Polynomial.coeff_zero] at hc
    rw [foldedSum_coeff, if_pos ht] at hc
    unfold foldedCoeff at hc
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hc
    omega
  · intro hbal
    rw [foldedSum]
    refine Finset.sum_eq_zero fun t ht => ?_
    have hc : foldedCoeff m S e (fun _ => 1) t = 0 := by
      unfold foldedCoeff
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      have := hbal t (Finset.mem_range.mp ht)
      omega
    rw [hc, map_zero, zero_mul]

/-! ## Sanity weld: the `e₂` census engine is the `w ≡ 1` instance -/

theorem e2Coeff_eq_foldedCoeff (m : ℕ) (A : Finset ℕ) (t : ℕ) :
    e2Coeff m A t = foldedCoeff m (upperPairs A) (fun q => q.1 + q.2) (fun _ => 1) t := by
  unfold e2Coeff foldedCoeff
  simp [Finset.sum_const]

/-- The landed `e₂` engine (`WindowTwoLayerThreshold.lean`) is the weight-one instance of
the generic engine over the pair family. -/
theorem e2Folded_eq_foldedSum (m : ℕ) (A : Finset ℕ) :
    e2Folded m A = foldedSum m (upperPairs A) (fun q => q.1 + q.2) (fun _ => 1) := by
  unfold e2Folded foldedSum
  exact Finset.sum_congr rfl fun t _ => by rw [e2Coeff_eq_foldedCoeff]

/-! ## Source audit -/

#print axioms foldedSum_eval
#print axioms l1On_foldedSum_le
#print axioms foldedSum_vanishing_iff_char0
#print axioms foldedSum_ne_zero_of_char0
#print axioms foldedSum_eq_zero_iff_balanced
#print axioms e2Folded_eq_foldedSum

end ArkLib.ProximityGap.WindowTwoLayer

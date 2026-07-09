/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PackingEnvelope

/-!
# The first overlap-packing jump at a field-normalized budget

This file turns the freshness hypotheses of
`PackingEnvelope.overlap_packing_epsMCA_lower_bound` into a cardinality theorem and
packages the exact integer arithmetic of the first packing jump.

For `B = floor (p / Q)`, code dimension `k`, and `D = n-k`, the packing family has
`2e+2` bad scalars at error radius `e/n` throughout

```text
  ceil(D/2) <= e <= D-1.
```

Thus its first budget-crossing error is `max(ceil(D/2), floor(B/2))`, provided this
does not exceed `D-1`.  This is only a bad-side consumer: no matching upper bound or
threshold equality is claimed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.KKH26 ArkLib.ProximityGap.PackingEnvelope

namespace ArkLib.ProximityGap.PackingBudgetFirstJump

/-- The six separation conditions required by the tuned overlap-packing construction. -/
structure OverlapFreshScalars {p n : ℕ} (g : ZMod p) (s c : ℕ) where
  γK : Fin n → ZMod p
  γA : Fin n → ZMod p
  ne : ∀ x : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s → γK x ≠ γA x
  k_not_dom : ∀ x : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
    ∀ j : Fin n, γK x ≠ -(g ^ (j : ℕ))
  a_not_dom : ∀ x : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
    ∀ j : Fin n, γA x ≠ -(g ^ (j : ℕ))
  k_inj : ∀ x y : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
    s - c ≤ (y : ℕ) → (y : ℕ) < s → γK x = γK y → x = y
  a_inj : ∀ x y : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
    s - c ≤ (y : ℕ) → (y : ℕ) < s → γA x = γA y → x = y
  cross : ∀ x y : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
    s - c ≤ (y : ℕ) → (y : ℕ) < s → γK x ≠ γA y

/-- Negated powers below the order are injective. -/
private lemma neg_pow_injective {p n : ℕ} [Fact p.Prime] [NeZero n]
    {g : ZMod p} (hg : orderOf g = n) :
    Function.Injective (fun j : Fin n ↦ -(g ^ (j : ℕ))) := by
  intro i j hij
  apply Fin.ext
  apply pow_injOn_Iio_orderOf (x := g)
  · rw [hg]
    exact i.isLt
  · rw [hg]
    exact j.isLt
  · exact neg_injective hij

/-- A prime `p ≡ 1 (mod n)` contains an element of multiplicative order `n`.
This exposes the standard cyclic-unit-group construction so concrete consumers do not
need to provide a giant generator explicitly. -/
theorem exists_orderOf_eq_of_modEq {p n : ℕ} [Fact p.Prime]
    (hmod : p ≡ 1 [MOD n]) :
    ∃ g : ZMod p, orderOf g = n := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdvd : n ∣ p - 1 := (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf u = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_eq_fintype_card,
      ZMod.card_units]
  have hdvd' : n ∣ orderOf u := hord ▸ hdvd
  have hne : orderOf u ≠ 0 := by omega
  refine ⟨((u ^ (orderOf u / n) : (ZMod p)ˣ) : ZMod p), ?_⟩
  rw [orderOf_units, orderOf_pow_orderOf_div hne hdvd']

open Classical in
/-- **Fresh-scalar supply.**  The six hypotheses of the overlap construction are
satisfiable as soon as the complement of the negated evaluation domain contains `2c`
elements.  The bound `2c ≤ p-n` is both the natural sufficient count and necessary for
this particular package (the two injective images are cross-disjoint). -/
theorem exists_overlapFreshScalars {p n s c : ℕ} [Fact p.Prime] [NeZero n]
    {g : ZMod p} (hg : orderOf g = n) (hcs : c ≤ s)
    (hsupply : 2 * c ≤ p - n) :
    Nonempty (OverlapFreshScalars (n := n) g s c) := by
  classical
  let forbidden : Finset (ZMod p) :=
    Finset.univ.image (fun j : Fin n ↦ -(g ^ (j : ℕ)))
  have hforbidden : forbidden.card = n := by
    dsimp only [forbidden]
    rw [Finset.card_image_of_injective _ (neg_pow_injective hg),
      Finset.card_univ, Fintype.card_fin]
  have hcompl : forbiddenᶜ.card = p - n := by
    rw [Finset.card_compl, hforbidden, ZMod.card]
  have hfreshCard : Fintype.card (Fin (2 * c)) ≤ forbiddenᶜ.card := by
    simpa [hcompl] using hsupply
  obtain ⟨fresh, hfresh⟩ :=
    Function.Embedding.exists_of_card_le_finset (s := forbiddenᶜ) hfreshCard
  let inY : Fin n → Prop := fun x ↦ s - c ≤ (x : ℕ) ∧ (x : ℕ) < s
  let off : (x : Fin n) → inY x → Fin c := fun x hx ↦
    ⟨(x : ℕ) - (s - c), by omega⟩
  let kIndex : (x : Fin n) → (hx : inY x) → Fin (2 * c) := fun x hx ↦
    ⟨(off x hx : ℕ), by have := (off x hx).isLt; omega⟩
  let aIndex : (x : Fin n) → (hx : inY x) → Fin (2 * c) := fun x hx ↦
    ⟨c + (off x hx : ℕ), by have := (off x hx).isLt; omega⟩
  let γK : Fin n → ZMod p := fun x ↦
    if hx : inY x then fresh (kIndex x hx) else 0
  let γA : Fin n → ZMod p := fun x ↦
    if hx : inY x then fresh (aIndex x hx) else 0
  have hoff_inj : ∀ {x y : Fin n} (hx : inY x) (hy : inY y),
      off x hx = off y hy → x = y := by
    intro x y hx hy heq
    apply Fin.ext
    have hv : (off x hx : ℕ) = (off y hy : ℕ) := congrArg Fin.val heq
    dsimp only [off] at hv
    dsimp only [inY] at hx hy
    omega
  have hk_ne_ha : ∀ x y : Fin n, (hx : inY x) → (hy : inY y) →
      kIndex x hx ≠ aIndex y hy := by
    intro x y hx hy heq
    have hv := congrArg Fin.val heq
    dsimp only [kIndex, aIndex] at hv
    have hlt := (off x hx).isLt
    omega
  refine ⟨⟨γK, γA, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x hx1 hx2 hEq
    have hx : inY x := ⟨hx1, hx2⟩
    simp only [γK, γA, dif_pos hx] at hEq
    exact hk_ne_ha x x hx hx (fresh.injective hEq)
  · intro x hx1 hx2 j hEq
    have hx : inY x := ⟨hx1, hx2⟩
    have hmem : fresh (kIndex x hx) ∈ forbiddenᶜ :=
      hfresh ⟨kIndex x hx, rfl⟩
    rw [Finset.mem_compl] at hmem
    apply hmem
    rw [Finset.mem_image]
    exact ⟨j, Finset.mem_univ _, by simpa [γK, hx] using hEq.symm⟩
  · intro x hx1 hx2 j hEq
    have hx : inY x := ⟨hx1, hx2⟩
    have hmem : fresh (aIndex x hx) ∈ forbiddenᶜ :=
      hfresh ⟨aIndex x hx, rfl⟩
    rw [Finset.mem_compl] at hmem
    apply hmem
    rw [Finset.mem_image]
    exact ⟨j, Finset.mem_univ _, by simpa [γA, hx] using hEq.symm⟩
  · intro x y hx1 hx2 hy1 hy2 hEq
    have hx : inY x := ⟨hx1, hx2⟩
    have hy : inY y := ⟨hy1, hy2⟩
    simp only [γK, dif_pos hx, dif_pos hy] at hEq
    have hi := fresh.injective hEq
    apply hoff_inj hx hy
    apply Fin.ext
    have hv := congrArg Fin.val hi
    dsimp only [kIndex] at hv
    exact hv
  · intro x y hx1 hx2 hy1 hy2 hEq
    have hx : inY x := ⟨hx1, hx2⟩
    have hy : inY y := ⟨hy1, hy2⟩
    simp only [γA, dif_pos hx, dif_pos hy] at hEq
    have hi := fresh.injective hEq
    apply hoff_inj hx hy
    apply Fin.ext
    have hv := congrArg Fin.val hi
    dsimp only [aIndex] at hv
    omega
  · intro x y hx1 hx2 hy1 hy2 hEq
    have hx : inY x := ⟨hx1, hx2⟩
    have hy : inY y := ⟨hy1, hy2⟩
    simp only [γK, γA, dif_pos hx, dif_pos hy] at hEq
    exact hk_ne_ha x y hx hy (fresh.injective hEq)

/-- Clearing the two finite denominators in the budget comparison. -/
private lemma inv_natCast_lt_natCast_div {Q p W : ℕ} (hQ : 0 < Q) (hp : 0 < p)
    (hsmall : p < Q * W) :
    ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) < (W : ℝ≥0∞) / (p : ℝ≥0∞) := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hpT : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hp0) (Or.inl hpT)]
  have hQ0 : (Q : ℝ≥0∞) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hQT : (Q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top Q
  rw [← ENNReal.div_eq_inv_mul,
    ENNReal.div_lt_iff (Or.inl hQ0) (Or.inl hQT)]
  exact_mod_cast (by simpa [Nat.mul_comm] using hsmall)

open Classical in
/-- **Overlap packing with freshness discharged by counting.**  At an error count `e`
in the deep half, the parameters

`s=e+1`, `c=2e-n+2`, `t=n-e`, `d=k-1`

satisfy the overlap identities.  The sole field-size input is the exact supply count
`2c ≤ p-n`. -/
theorem overlap_epsMCA_lower_bound_of_supply
    {p n k e : ℕ} [Fact p.Prime] [NeZero n]
    {g : ZMod p} (hg : orderOf g = n)
    (hk : 2 ≤ k) (hehalf : n ≤ 2 * e) (hecap : e + k + 1 ≤ n)
    (hsupply : 2 * (2 * e - n + 2) ≤ p - n) :
    ((2 * e + 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤
      epsMCA (F := ZMod p) (evalCode g n (k - 1))
        (1 - (((n - e : ℕ) : ℝ≥0) / (n : ℝ≥0))) := by
  classical
  let s := e + 1
  let c := 2 * e - n + 2
  let t := n - e
  have hcs : c ≤ s := by dsimp only [c, s]; omega
  obtain ⟨fresh⟩ := exists_overlapFreshScalars (g := g) hg hcs hsupply
  have h := overlap_packing_epsMCA_lower_bound (p := p) (n := n)
    (d := k - 1) (s := s) (c := c) (t := t) (g := g) hg fresh.γK fresh.γA
    (by omega) (by dsimp only [s]; omega) (by dsimp only [c, s]; omega)
    (by dsimp only [t, s]; omega) (by dsimp only [t, c, s]; omega)
    fresh.ne fresh.k_not_dom fresh.a_not_dom fresh.k_inj fresh.a_inj fresh.cross
  have hcount : n + c = 2 * e + 2 := by dsimp only [c]; omega
  simpa only [hcount, t] using h

open Classical in
/-- **The first deep packing crossing at the floor budget.**  Put

`B = p/Q` and `e∗ = max ((n-k)/2) (B/2)`.

If the normalized field budget lies in `n ≤ B ≤ 2(n-k)-1`, `n` is even, and
the complement supplies the required tuned scalars, then the overlap family proves the
operational bad-side ceiling at error `e∗`.  No upper bound below this point is asserted. -/
theorem mcaDeltaStar_le_first_deep_packing_of_floor_budget
    {p n k Q : ℕ} [Fact p.Prime] [NeZero n]
    {g : ZMod p} (hg : orderOf g = n)
    (hQ : 0 < Q) (hk : 2 ≤ k) (hnEven : n % 2 = 0)
    (hB_lo : n ≤ p / Q) (hB_hi : p / Q ≤ 2 * (n - k) - 1)
    (hsupply :
      let e := max ((n - k) / 2) ((p / Q) / 2)
      2 * (2 * e - n + 2) ≤ p - n) :
    let e := max ((n - k) / 2) ((p / Q) / 2)
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n (k - 1))
        ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞)
      ≤ 1 - (((n - e : ℕ) : ℝ≥0) / (n : ℝ≥0)) := by
  classical
  let B := p / Q
  let e := max ((n - k) / 2) (B / 2)
  change n ≤ B at hB_lo
  change B ≤ 2 * (n - k) - 1 at hB_hi
  have heB : B / 2 ≤ e := le_max_right _ _
  have hn2 : n = 2 * (n / 2) := by omega
  have hehalf : n ≤ 2 * e := by
    have hnhalf : n / 2 ≤ B / 2 := Nat.div_le_div_right hB_lo
    omega
  have hDpos : 1 ≤ n - k := by
    by_contra h0
    have : n - k = 0 := by omega
    simp only [this, mul_zero, Nat.zero_sub] at hB_hi
    have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    omega
  have hecap : e + k + 1 ≤ n := by
    have hBhalf : B / 2 ≤ n - k - 1 := by omega
    have hDhalf : (n - k) / 2 ≤ n - k - 1 := by omega
    have he : e ≤ n - k - 1 := by
      dsimp only [e]
      exact max_le hDhalf hBhalf
    omega
  have hlower := overlap_epsMCA_lower_bound_of_supply (p := p) (n := n)
    (k := k) (e := e) (g := g) hg hk hehalf hecap (by simpa [e, B] using hsupply)
  have hBW : B + 1 ≤ 2 * e + 2 := by omega
  have hpQ : p < Q * (B + 1) := by
    simpa [B] using Nat.lt_mul_div_succ p hQ
  have hpW : p < Q * (2 * e + 2) :=
    lt_of_lt_of_le hpQ (Nat.mul_le_mul_left Q hBW)
  have hp : 0 < p := (Fact.out (p := p.Prime)).pos
  have hbudget : ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) <
      ((2 * e + 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) :=
    inv_natCast_lt_natCast_div hQ hp hpW
  change mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n (k - 1))
      ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞)
    ≤ 1 - (((n - e : ℕ) : ℝ≥0) / (n : ℝ≥0))
  exact mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le hbudget hlower)

open Classical in
/-- **Tight-budget specialization.**  When `floor(p/Q)=n`, every even-length
rate-at-most-`1/4` RS code (`2 ≤ k ≤ n/4`) has an explicit overlap-packing bad point
at radius `1/2`, provided four scalars remain outside the evaluation domain.  Therefore
its operational MCA threshold is at most `1/2`.

This is a one-sided ceiling only.  In particular it does not claim the immediately
preceding lattice point is good. -/
theorem mcaDeltaStar_le_half_of_floor_eq_length
    {p n k Q : ℕ} [Fact p.Prime] [NeZero n]
    {g : ZMod p} (hg : orderOf g = n)
    (hQ : 0 < Q) (hk : 2 ≤ k) (hnEven : n % 2 = 0)
    (hfloor : p / Q = n) (hkquarter : k ≤ n / 4)
    (hsupply : 4 ≤ p - n) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n (k - 1))
        ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞)
      ≤ (1 / 2 : ℝ≥0) := by
  have hn8 : 8 ≤ n := by omega
  have hBhi : p / Q ≤ 2 * (n - k) - 1 := by omega
  have heq : max ((n - k) / 2) ((p / Q) / 2) = n / 2 := by
    rw [hfloor]
    apply max_eq_right
    apply Nat.div_le_div_right
    omega
  have hsupply' :
      let e := max ((n - k) / 2) ((p / Q) / 2)
      2 * (2 * e - n + 2) ≤ p - n := by
    dsimp only
    rw [heq]
    omega
  have h := mcaDeltaStar_le_first_deep_packing_of_floor_budget
    (p := p) (n := n) (k := k) (Q := Q) (g := g) hg hQ hk hnEven
    (by omega) hBhi hsupply'
  rw [heq] at h
  dsimp only at h
  have hn2 : n = 2 * (n / 2) := by omega
  have hnsub : n - n / 2 = n / 2 := by omega
  rw [hnsub] at h
  have hhalf : (((n / 2 : ℕ) : ℝ≥0) / (n : ℝ≥0)) = 1 / 2 := by
    have hn0 : (n : ℝ≥0) ≠ 0 := by positivity
    apply (div_eq_iff hn0).2
    have hncast : (n : ℝ≥0) = 2 * ((n / 2 : ℕ) : ℝ≥0) := by
      exact_mod_cast hn2
    rw [hncast]
    field_simp
  rw [hhalf] at h
  calc
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n (k - 1))
        ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞)
        ≤ 1 - 1 / 2 := h
    _ = 1 / 2 := by
      rw [tsub_eq_iff_eq_add_of_le (by norm_num : (1 / 2 : ℝ≥0) ≤ 1)]
      norm_num

open Classical in
/-- Generator-free form of `mcaDeltaStar_le_half_of_floor_eq_length`.  Prime and
congruence hypotheses remain explicit; cyclicity of `(ZMod p)ˣ` supplies the order-`n`
element. -/
theorem exists_order_mcaDeltaStar_le_half_of_floor_eq_length
    {p n k Q : ℕ} [Fact p.Prime] [NeZero n]
    (hmod : p ≡ 1 [MOD n])
    (hQ : 0 < Q) (hk : 2 ≤ k) (hnEven : n % 2 = 0)
    (hfloor : p / Q = n) (hkquarter : k ≤ n / 4)
    (hsupply : 4 ≤ p - n) :
    ∃ g : ZMod p, orderOf g = n ∧
      mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n (k - 1))
          ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞)
        ≤ (1 / 2 : ℝ≥0) := by
  obtain ⟨g, hg⟩ := exists_orderOf_eq_of_modEq (p := p) hmod
  exact ⟨g, hg, mcaDeltaStar_le_half_of_floor_eq_length hg hQ hk hnEven
    hfloor hkquarter hsupply⟩

end ArkLib.ProximityGap.PackingBudgetFirstJump

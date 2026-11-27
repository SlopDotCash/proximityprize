/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PaleySignedSquareRoot
import Mathlib.Tactic.FinCases

/-!
# Four-site ternary Paley rank ceilings and skew-prime overlap improvements

Builds on `PaleySignedSquareRoot` to formalize:
1. Explicit finite Gram-energy ceiling `four_site_energy_le`.
2. Exact four-site `𝔽₃`-rank energy identity `energy_eq_four_site_singular`:
   `E(X, X) = n(n - 1)(2n - 3) + 8 χ(-1) (4 N_4(X) - C(n, 4))`.
3. Explicit and asymptotic `p ≡ 1 (mod 4)` four-site singular density ceilings:
   `four_site_singular_le_mod1`, `four_site_singular_65537` (`N_4 ≤ 142,536,640` out of
   `174,792,640`), and `eventually_four_site_singular_density_mod1` (`N_4 / C(n, 4) < 13/16 + ε`).
4. Finite skew-prime (`p ≡ 3 mod 4`) overlap improvement `skew_overlap_discrepancy_le`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

namespace ProximityGap.PaleyFourSiteRankAndOverlap

open Finset Filter Matrix Polynomial
open PaleySignedHankelDegree PaleySignedSquareRoot
open scoped Polynomial Topology

section LocalBipartiteDefs

/-- Column-pair correlation `gram A W t b = ∑ a ∈ A, W a t * W a b`. -/
def gram {α β : Type*} (A : Finset α) (W : α → β → ℤ) (t b : β) : ℤ :=
  ∑ a ∈ A, W a t * W a b

/-- Signed four-cycle energy `energy A B W = ∑ t ∈ B, ∑ b ∈ B, gram A W t b ^ 2`. -/
def energy {α β : Type*} (A : Finset α) (B : Finset β) (W : α → β → ℤ) : ℤ :=
  ∑ t ∈ B, ∑ b ∈ B, (gram A W t b) ^ 2

theorem energy_eq_four_cycle {α β : Type*} (A : Finset α) (B : Finset β) (W : α → β → ℤ) :
    energy A B W =
      ∑ t ∈ B, ∑ b ∈ B, ∑ x ∈ A, ∑ y ∈ A, (W x t * W x b) * (W y t * W y b) := by
  simp only [energy, gram, pow_two, sum_mul_sum]

/-- Integral four-site matrix with sign ratio `e` under reversal of a directed edge. -/
def fourSiteMatrix (e a b c d f g : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, a, b, c; e * a, 0, d, f; e * b, e * d, 0, g; e * c, e * f, e * g, 0]

private theorem det_fourSite_expanded (e a b c d f g : ℤ) :
    (fourSiteMatrix e a b c d f g).det =
      e ^ 2 * (a ^ 2 * g ^ 2 + b ^ 2 * f ^ 2 + c ^ 2 * d ^ 2) - (e + e ^ 3) * (a * c * d * g) -
        2 * e ^ 2 * (a * b * f * g + b * c * d * f) := by
  rw [Matrix.det_succ_row_zero]
  simp [fourSiteMatrix, Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.succAbove]
  ring

private theorem sign_cases_local (z : ℤ) (hz : z ^ 2 = 1) : z = 1 ∨ z = -1 := by
  have h : (z - 1) * (z + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp h with h | h <;> omega

/-- Singularity modulo 3 detects precisely the four-site type with both Hamilton cycle signs
equal to `e`. -/
theorem four_site_singular_mod_three (e a b c d f g : ℤ) (he : e ^ 2 = 1) (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) (hc : c ^ 2 = 1) (hd : d ^ 2 = 1) (hf : f ^ 2 = 1) (hg : g ^ 2 = 1) :
    (((fourSiteMatrix e a b c d f g).det : ℤ) : ZMod 3) = 0 ↔
      (e * a * c * d * g = e ∧ a * b * f * g = e) := by
  have he3 : e ^ 3 = e := by rw [pow_succ, he, one_mul]
  have hw : e * (e * a * c * d * g) * (a * b * f * g) = b * c * d * f := by
    calc _ = e ^ 2 * a ^ 2 * g ^ 2 * (b * c * d * f) := by ring
      _ = _ := by rw [he, ha, hg]; ring
  have hdet : (fourSiteMatrix e a b c d f g).det =
      3 - 2 * ((e * a * c * d * g) + (a * b * f * g) + e * (e * a * c * d * g) * (a * b * f * g)) := by
    rw [det_fourSite_expanded, he3, he, ha, hb, hc, hd, hf, hg, hw]; ring
  rw [hdet]
  let u := e * a * c * d * g
  let v := a * b * f * g
  have hu : u ^ 2 = 1 := by simp [u, mul_pow, he, ha, hc, hd, hg]
  have hv : v ^ 2 = 1 := by simp [v, mul_pow, ha, hb, hf, hg]
  change ((3 - 2 * (u + v + e * u * v) : ℤ) : ZMod 3) = 0 ↔ u = e ∧ v = e
  rcases sign_cases_local e he with rfl | rfl <;>
    rcases sign_cases_local u hu with hU | hU <;>
    rcases sign_cases_local v hv with hV | hV <;>
    rw [hU, hV] <;> decide

variable {p : ℕ} [Fact p.Prime]

/-- A 4-subset `T ⊆ ZMod p` is ternary-singular if its `4 × 4` Paley matrix has zero determinant
modulo 3. -/
noncomputable def isFourSiteSingular (T : Finset (ZMod p)) : Prop :=
  ((Matrix.of fun u v : T => quadraticChar (ZMod p) (u.1 - v.1)).det : ZMod 3) = 0

/-- Count `N_4(X)` of unordered 4-subsets of `X` whose `4 × 4` Paley matrix is singular over `𝔽₃`. -/
noncomputable def fourSiteSingularCount (X : Finset (ZMod p)) : ℕ :=
  by classical exact ((X.powersetCard 4).filter isFourSiteSingular).card

local instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

end LocalBipartiteDefs

/-! ## 5. Four-site `𝔽₃`-rank ceiling (`N_4 / C(n, 4) ≤ 13/16 + o(1)`) -/

section FourSiteRank

variable {p : ℕ} [Fact p.Prime]

/-- **Explicit finite Gram-energy ceiling** for `3 ≤ |X| ≤ (p - 1)/2 + 2` and `1 ≤ x ≤ (|X| - 1)/2`:
`E(X, X) ≤ n * ((n - 1)*(n - 2 - 2x)^2 + (n - 1 - 2x)^2 + 4*x*(p/2 + n - 1 - 2x))`. -/
theorem four_site_energy_le (hp : p ≠ 2) (X : Finset (ZMod p))
    (hn : 3 ≤ X.card) (hn' : X.card ≤ p / 2 + 2) {x : ℕ} (hx : 1 ≤ x) (hx' : 2 * x ≤ X.card - 1) :
    energy X X (fun u y => quadraticChar (ZMod p) (u - y)) ≤
      (X.card : ℤ) * (((X.card - 1 : ℕ) : ℤ) * ((X.card : ℤ) - 2 - 2 * x) ^ 2 +
        ((X.card : ℤ) - 1 - 2 * x) ^ 2 +
        4 * (x : ℤ) * ((p / 2 + X.card - 1 - 2 * x : ℕ) : ℤ)) := by
  classical
  unfold energy
  have hrow : ∀ t ∈ X,
      ∑ b ∈ X, (gram X (fun u y => quadraticChar (ZMod p) (u - y)) t b) ^ 2 ≤
        ((X.card - 1 : ℕ) : ℤ) * ((X.card : ℤ) - 2 - 2 * x) ^ 2 +
          ((X.card : ℤ) - 1 - 2 * x) ^ 2 +
          4 * (x : ℤ) * ((p / 2 + X.card - 1 - 2 * x : ℕ) : ℤ) := by
    intro t ht
    let A := X.erase t
    let w : ZMod p → ℤ := fun u => quadraticChar (ZMod p) (u - t)
    have hA_card : A.card = X.card - 1 := Finset.card_erase_of_mem ht
    have hw : ∀ u ∈ A, w u = 1 ∨ w u = -1 := fun u hu =>
      quadraticChar_dichotomy (sub_ne_zero.mpr (ne_of_mem_erase hu))
    let B' := X.image Neg.neg
    have hgram_eq : ∀ b ∈ X,
        gram X (fun u y => quadraticChar (ZMod p) (u - y)) t b = signedShiftSum A w (-b) := by
      intro b _
      unfold gram signedShiftSum
      rw [← Finset.add_sum_erase X _ ht]
      dsimp only
      rw [sub_self, MulChar.map_zero, zero_mul, zero_add]
      refine Finset.sum_congr rfl fun u _ => ?_
      dsimp [w]; rw [show -b + u = u - b by ring]
    have hsum_eq : ∑ b ∈ X, (gram X (fun u y => quadraticChar (ZMod p) (u - y)) t b) ^ 2 =
        ∑ y ∈ B', (signedShiftSum A w y) ^ 2 := by
      rw [Finset.sum_image (fun _ _ _ _ h => neg_inj.mp h)]
      exact Finset.sum_congr rfl fun b hb => by rw [hgram_eq b hb]
    rw [hsum_eq]
    have hbound := signed_row_sum_sq_le hp A B' w hw (by omega) (by omega) hx (by omega)
    have hbase : ∑ y ∈ B', ((A.card : ℤ) - (if -y ∈ A then (1 : ℤ) else 0) - 2 * x) ^ 2 =
        ((X.card - 1 : ℕ) : ℤ) * ((X.card : ℤ) - 2 - 2 * x) ^ 2 +
          ((X.card : ℤ) - 1 - 2 * x) ^ 2 := by
      rw [Finset.sum_image (fun _ _ _ _ h => neg_inj.mp h), ← Finset.add_sum_erase X _ ht]
      have ht_not : ¬ (-(-t) ∈ A) := by simp [A]
      simp only [ht_not, ↓reduceIte]
      have hrest : ∑ b ∈ X.erase t,
            ((A.card : ℤ) - (if -(-b) ∈ A then (1 : ℤ) else 0) - 2 * x) ^ 2 =
          ∑ _b ∈ X.erase t, ((X.card : ℤ) - 2 - 2 * x) ^ 2 := by
        refine Finset.sum_congr rfl fun b hb => ?_
        have hbA : -(-b) ∈ A := by simpa [A] using hb
        simp only [hbA, ↓reduceIte, hA_card]
        have : ((X.card - 1 : ℕ) : ℤ) = (X.card : ℤ) - 1 := by omega
        rw [this]; ring
      rw [hrest, Finset.sum_const, nsmul_eq_mul, hA_card]
      have : ((X.card - 1 : ℕ) : ℤ) = (X.card : ℤ) - 1 := by omega
      rw [this]; ring
    have hbud : (degreeBudget (p / 2) A.card x (minorityCount A w) : ℤ) ≤
        (x : ℤ) * ((p / 2 + X.card - 1 - 2 * x : ℕ) : ℤ) := by
      have hle : degreeBudget (p / 2) A.card x (minorityCount A w) ≤
          x * (p / 2 + X.card - 1 - 2 * x) := by
        refine (Nat.sub_le _ _).trans (Nat.mul_le_mul_left x ?_)
        rw [hA_card]; omega
      exact_mod_cast hle
    linarith [hbound, hbase, hbud]
  calc _ ≤ ∑ _t ∈ X, (((X.card - 1 : ℕ) : ℤ) * ((X.card : ℤ) - 2 - 2 * x) ^ 2 +
            ((X.card : ℤ) - 1 - 2 * x) ^ 2 +
            4 * (x : ℤ) * ((p / 2 + X.card - 1 - 2 * x : ℕ) : ℤ)) :=
          Finset.sum_le_sum hrow
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Pure finite-case algebraic identity: for a 4-site matrix with entries `±1` off-diagonal and
reversal sign `e ∈ {±1}`, the sum of the four-cycle products over all 24 permutations of `Fin 4`
equals `24 * e` iff the matrix is singular mod 3, and `-8 * e` otherwise. -/
private theorem perm_four_cycle_sum (e a b c d f g : ℤ)
    (he : e ^ 2 = 1) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hd : d ^ 2 = 1) (hf : f ^ 2 = 1) (hg : g ^ 2 = 1) :
    let M := fourSiteMatrix e a b c d f g
    (∑ σ : Equiv.Perm (Fin 4),
        M (σ 0) (σ 2) * M (σ 0) (σ 3) * M (σ 1) (σ 2) * M (σ 1) (σ 3)) =
      8 * e * (4 * (if (((M.det : ℤ) : ZMod 3) = 0) then (1 : ℤ) else 0) - 1) := by
  have hsing := four_site_singular_mod_three e a b c d f g he ha hb hc hd hf hg
  have hcases : ∀ z : ℤ, z ^ 2 = 1 → z = 1 ∨ z = -1 := fun z hz => by
    have : (z - 1) * (z + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h <;> omega
  dsimp only
  rw [show (if (((fourSiteMatrix e a b c d f g).det : ℤ) : ZMod 3) = 0 then (1 : ℤ) else 0) =
      (if e * a * c * d * g = e ∧ a * b * f * g = e then (1 : ℤ) else 0) by
    simp only [hsing]]
  rcases hcases e he with rfl | rfl <;>
    rcases hcases a ha with rfl | rfl <;>
    rcases hcases b hb with rfl | rfl <;>
    rcases hcases c hc with rfl | rfl <;>
    rcases hcases d hd with rfl | rfl <;>
    rcases hcases f hf with rfl | rfl <;>
    rcases hcases g hg with rfl | rfl <;>
    decide

/-- **Exact four-site `𝔽₃`-rank energy identity**:
`E(X, X) = n(n - 1)(2n - 3) + 8 * χ(-1) * (4 * N_4(X) - C(n, 4))`. -/
theorem energy_eq_four_site_singular (_hp : p ≠ 2) (X : Finset (ZMod p)) :
    energy X X (fun u y => quadraticChar (ZMod p) (u - y)) =
      (X.card : ℤ) * ((X.card : ℤ) - 1) * (2 * (X.card : ℤ) - 3) +
        8 * quadraticChar (ZMod p) (-1) *
          (4 * (fourSiteSingularCount X : ℤ) - (X.card.choose 4 : ℤ)) := by
  classical
  let W : ZMod p → ZMod p → ℤ := fun u y => quadraticChar (ZMod p) (u - y)
  let e : ℤ := quadraticChar (ZMod p) (-1)
  have he_sq : e ^ 2 = 1 := quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)
  have hW_rev : ∀ u y : ZMod p, W y u = e * W u y := fun u y => by
    dsimp [W, e]
    rw [show y - u = (-1) * (u - y) by ring, map_mul]
  have hW_sq : ∀ u y : ZMod p, u ≠ y → W u y ^ 2 = 1 := fun u y h =>
    quadraticChar_sq_one (sub_ne_zero.mpr h)
  -- Express `energy X X W` as a sum over `((X ×ˢ X) ×ˢ (X ×ˢ X))` (`((x, y), (t, b))`),
  -- splitting into distinct 4-tuples vs non-distinct 4-tuples!
  let Q := (X ×ˢ X) ×ˢ (X ×ˢ X)
  let f : (ZMod p × ZMod p) × (ZMod p × ZMod p) → ℤ := fun q =>
    (W q.1.1 q.2.1 * W q.1.1 q.2.2) * (W q.1.2 q.2.1 * W q.1.2 q.2.2)
  have henergy_Q : energy X X W = ∑ q ∈ Q, f q := by
    rw [energy_eq_four_cycle]
    have h1 : (∑ t ∈ X, ∑ b ∈ X, ∑ x ∈ X, ∑ y ∈ X, (W x t * W x b) * (W y t * W y b)) =
        ∑ p ∈ X ×ˢ X, ∑ r ∈ X ×ˢ X, (W r.1 p.1 * W r.1 p.2) * (W r.2 p.1 * W r.2 p.2) := by
      simp only [Finset.sum_product]
    rw [h1, Finset.sum_comm]
    simp only [Q, f, Finset.sum_product]
  let isDist : (ZMod p × ZMod p) × (ZMod p × ZMod p) → Prop := fun q =>
    q.1.1 ≠ q.1.2 ∧ q.1.1 ≠ q.2.1 ∧ q.1.1 ≠ q.2.2 ∧
    q.1.2 ≠ q.2.1 ∧ q.1.2 ≠ q.2.2 ∧ q.2.1 ≠ q.2.2
  rw [henergy_Q, ← Finset.sum_filter_add_sum_filter_not Q isDist]
  -- Part A: Non-distinct 4-tuples sum to `n(n-1)(2n-3)`:
  have hnonDist : ∑ q ∈ Q.filter (fun q => ¬ isDist q), f q =
      (X.card : ℤ) * ((X.card : ℤ) - 1) * (2 * (X.card : ℤ) - 3) := by
    -- A non-distinct tuple has `f q ≠ 0` iff `x ≠ t, x ≠ b, y ≠ t, y ≠ b` AND (`x = y ∨ t = b`).
    -- Split into three disjoint cases:
    -- 1. `x = y ∧ t = b ∧ x ≠ t`: `f q = 1`, count `n(n-1)`
    -- 2. `x = y ∧ t ≠ b ∧ x ≠ t ∧ x ≠ b`: `f q = 1`, count `n(n-1)(n-2)`
    -- 3. `x ≠ y ∧ t = b ∧ t ≠ x ∧ t ≠ y`: `f q = 1`, count `n(n-1)(n-2)`
    have hpt : ∀ q ∈ Q.filter (fun q => ¬ isDist q),
        f q = (if q.1.1 = q.1.2 ∧ q.2.1 = q.2.2 ∧ q.1.1 ≠ q.2.1 then (1 : ℤ) else 0) +
              (if q.1.1 = q.1.2 ∧ q.2.1 ≠ q.2.2 ∧ q.1.1 ≠ q.2.1 ∧ q.1.1 ≠ q.2.2 then 1 else 0) +
              (if q.1.1 ≠ q.1.2 ∧ q.2.1 = q.2.2 ∧ q.2.1 ≠ q.1.1 ∧ q.2.1 ≠ q.1.2 then 1 else 0) := by
      intro q hq
      have hnd : ¬ isDist q := (mem_filter.mp hq).2
      dsimp only [f]
      by_cases h0 : q.1.1 = q.2.1 ∨ q.1.1 = q.2.2 ∨ q.1.2 = q.2.1 ∨ q.1.2 = q.2.2
      · have hc1 : ¬(q.1.1 = q.1.2 ∧ q.2.1 = q.2.2 ∧ q.1.1 ≠ q.2.1) := by
          rintro ⟨hxy, htb, hne⟩
          rcases h0 with h | h | h | h
          · exact hne h
          · exact hne (h.trans htb.symm)
          · exact hne (hxy.trans h)
          · exact hne ((hxy.trans h).trans htb.symm)
        have hc2 : ¬(q.1.1 = q.1.2 ∧ q.2.1 ≠ q.2.2 ∧ q.1.1 ≠ q.2.1 ∧ q.1.1 ≠ q.2.2) := by
          rintro ⟨hxy, _, ha, hb⟩
          rcases h0 with h | h | h | h
          · exact ha h
          · exact hb h
          · exact ha (hxy.trans h)
          · exact hb (hxy.trans h)
        have hc3 : ¬(q.1.1 ≠ q.1.2 ∧ q.2.1 = q.2.2 ∧ q.2.1 ≠ q.1.1 ∧ q.2.1 ≠ q.1.2) := by
          rintro ⟨_, htb, ha, hb⟩
          rcases h0 with h | h | h | h
          · exact ha h.symm
          · exact ha (htb.trans h.symm)
          · exact hb h.symm
          · exact hb (htb.trans h.symm)
        simp only [hc1, hc2, hc3, ↓reduceIte, add_zero]
        rcases h0 with h | h | h | h <;> simp [W, h]
      · push Not at h0
        obtain ⟨h1, h2, h3, h4⟩ := h0
        have hor : q.1.1 = q.1.2 ∨ q.2.1 = q.2.2 := by
          by_contra h
          push Not at h
          exact hnd ⟨h.1, h1, h2, h3, h4, h.2⟩
        by_cases hxy : q.1.1 = q.1.2
        · by_cases htb : q.2.1 = q.2.2
          · simp only [hxy, htb, h4, not_true_eq_false, false_and, and_false,
              ↓reduceIte, add_zero, ne_eq, not_false_eq_true, and_self]
            have hsq := hW_sq q.1.2 q.2.2 h4
            calc (W q.1.2 q.2.2 * W q.1.2 q.2.2) * (W q.1.2 q.2.2 * W q.1.2 q.2.2)
                = (W q.1.2 q.2.2 ^ 2) * (W q.1.2 q.2.2 ^ 2) := by ring
              _ = 1 := by rw [hsq]; ring
          · simp only [hxy, htb, h3, h4, not_true_eq_false, false_and, and_false,
              ↓reduceIte, zero_add, add_zero, ne_eq, not_false_eq_true, and_self]
            have hsq1 := hW_sq q.1.2 q.2.1 h3
            have hsq2 := hW_sq q.1.2 q.2.2 h4
            calc (W q.1.2 q.2.1 * W q.1.2 q.2.2) * (W q.1.2 q.2.1 * W q.1.2 q.2.2)
                = (W q.1.2 q.2.1 ^ 2) * (W q.1.2 q.2.2 ^ 2) := by ring
              _ = 1 := by rw [hsq1, hsq2]; ring
        · have htb : q.2.1 = q.2.2 := hor.resolve_left hxy
          have h3' : q.2.2 ≠ q.1.1 := h2.symm
          have h4' : q.2.2 ≠ q.1.2 := h4.symm
          simp only [hxy, htb, h3', h4', false_and, ↓reduceIte, zero_add, ne_eq,
            not_false_eq_true, and_self]
          have hsq1 := hW_sq q.1.1 q.2.2 h2
          have hsq2 := hW_sq q.1.2 q.2.2 h4
          calc (W q.1.1 q.2.2 * W q.1.1 q.2.2) * (W q.1.2 q.2.2 * W q.1.2 q.2.2)
              = (W q.1.1 q.2.2 ^ 2) * (W q.1.2 q.2.2 ^ 2) := by ring
            _ = 1 := by rw [hsq1, hsq2]; ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib]
    -- Each of the 3 conditions implies `¬ isDist q`, so we can drop the `¬ isDist` filter and count on `Q`!
    have hdrop : ∀ (P : (ZMod p × ZMod p) × (ZMod p × ZMod p) → Prop) [DecidablePred P],
        (∀ q, P q → ¬ isDist q) →
        ∑ q ∈ Q.filter (fun q => ¬ isDist q), (if P q then (1 : ℤ) else 0) =
          ((Q.filter P).card : ℤ) := by
      intro P _ hP
      rw [← Finset.sum_filter, Finset.filter_filter,
        show Q.filter (fun q => ¬ isDist q ∧ P q) = Q.filter P by
          ext q; simp only [mem_filter]; exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, hP q h3, h3⟩⟩,
        Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hdrop _ (fun q h ⟨hxy, _⟩ => hxy h.1),
        hdrop _ (fun q h ⟨hxy, _⟩ => hxy h.1),
        hdrop _ (fun q h ⟨_, _, _, _, _, htb⟩ => htb h.2.1)]
    -- Count each of the 3 filtered subsets of `Q`:
    have hc1 : (Q.filter fun q => q.1.1 = q.1.2 ∧ q.2.1 = q.2.2 ∧ q.1.1 ≠ q.2.1).card =
        X.card * (X.card - 1) := by
      let S := X.sigma fun x => X.erase x
      have hbij : (Q.filter fun q => q.1.1 = q.1.2 ∧ q.2.1 = q.2.2 ∧ q.1.1 ≠ q.2.1).card = S.card :=
        Finset.card_bij (fun q _ => ⟨q.1.1, q.2.1⟩)
          (fun q hq => by
            simp only [Q, S, mem_filter, mem_product, mem_sigma, mem_erase] at hq ⊢
            exact ⟨hq.1.1.1, hq.2.2.2.symm, hq.1.2.1⟩)
          (fun q₁ h₁ q₂ h₂ h => by
            simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
            simp only [mem_filter] at h₁ h₂
            exact Prod.ext (Prod.ext h.1 (h₁.2.1.symm.trans (h.1.trans h₂.2.1)))
              (Prod.ext h.2 (h₁.2.2.1.symm.trans (h.2.trans h₂.2.2.1))))
          (fun u hu => by
            simp only [S, mem_sigma, mem_erase] at hu
            refine ⟨((u.1, u.1), (u.2, u.2)), ?_, rfl⟩
            simp [Q, hu.1, hu.2.1.symm, hu.2.2])
      rw [hbij, Finset.card_sigma]
      rw [Finset.sum_congr rfl fun x hx => Finset.card_erase_of_mem hx, Finset.sum_const, smul_eq_mul]
    have hc2 : (Q.filter fun q => q.1.1 = q.1.2 ∧ q.2.1 ≠ q.2.2 ∧ q.1.1 ≠ q.2.1 ∧ q.1.1 ≠ q.2.2).card =
        X.card * (X.card - 1) * (X.card - 2) := by
      let S := X.sigma fun x => (X.erase x).sigma fun t => (X.erase x).erase t
      have hbij : (Q.filter fun q => q.1.1 = q.1.2 ∧ q.2.1 ≠ q.2.2 ∧ q.1.1 ≠ q.2.1 ∧ q.1.1 ≠ q.2.2).card =
          S.card :=
        Finset.card_bij (fun q _ => ⟨q.1.1, ⟨q.2.1, q.2.2⟩⟩)
          (fun q hq => by
            simp only [Q, S, mem_filter, mem_product, mem_sigma, mem_erase] at hq ⊢
            exact ⟨hq.1.1.1, ⟨hq.2.2.2.1.symm, hq.1.2.1⟩, ⟨hq.2.2.1.symm, hq.2.2.2.2.symm, hq.1.2.2⟩⟩)
          (fun q₁ h₁ q₂ h₂ h => by
            simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
            simp only [mem_filter] at h₁ h₂
            exact Prod.ext (Prod.ext h.1 (h₁.2.1.symm.trans (h.1.trans h₂.2.1)))
              (Prod.ext h.2.1 h.2.2))
          (fun u hu => by
            simp only [S, mem_sigma, mem_erase] at hu
            refine ⟨((u.1, u.1), (u.2.1, u.2.2)), ?_, rfl⟩
            simp [Q, hu.1, hu.2.1.1.symm, hu.2.1.2, hu.2.2.1.symm, hu.2.2.2.1.symm, hu.2.2.2.2])
      rw [hbij]
      simp only [S, Finset.card_sigma]
      have hinner : ∀ x ∈ X, ∑ t ∈ X.erase x, ((X.erase x).erase t).card =
          (X.card - 1) * (X.card - 2) := fun x hx => by
        rw [Finset.sum_congr rfl fun t ht => by rw [Finset.card_erase_of_mem ht, Finset.card_erase_of_mem hx, Nat.sub_sub],
          Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hx]
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]; ring
    have hc3 : (Q.filter fun q => q.1.1 ≠ q.1.2 ∧ q.2.1 = q.2.2 ∧ q.2.1 ≠ q.1.1 ∧ q.2.1 ≠ q.1.2).card =
        X.card * (X.card - 1) * (X.card - 2) := by
      let S := X.sigma fun t => (X.erase t).sigma fun x => (X.erase t).erase x
      have hbij : (Q.filter fun q => q.1.1 ≠ q.1.2 ∧ q.2.1 = q.2.2 ∧ q.2.1 ≠ q.1.1 ∧ q.2.1 ≠ q.1.2).card =
          S.card :=
        Finset.card_bij (fun q _ => ⟨q.2.1, ⟨q.1.1, q.1.2⟩⟩)
          (fun q hq => by
            simp only [Q, S, mem_filter, mem_product, mem_sigma, mem_erase] at hq ⊢
            exact ⟨hq.1.2.1, ⟨hq.2.2.2.1.symm, hq.1.1.1⟩, ⟨hq.2.1.symm, hq.2.2.2.2.symm, hq.1.1.2⟩⟩)
          (fun q₁ h₁ q₂ h₂ h => by
            simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
            simp only [mem_filter] at h₁ h₂
            exact Prod.ext (Prod.ext h.2.1 h.2.2)
              (Prod.ext h.1 (h₁.2.2.1.symm.trans (h.1.trans h₂.2.2.1))))
          (fun u hu => by
            simp only [S, mem_sigma, mem_erase] at hu
            refine ⟨((u.2.1, u.2.2), (u.1, u.1)), ?_, rfl⟩
            simp [Q, hu.1, hu.2.1.1.symm, hu.2.1.2, hu.2.2.1.symm, hu.2.2.2.1.symm, hu.2.2.2.2])
      rw [hbij]
      simp only [S, Finset.card_sigma]
      have hinner : ∀ t ∈ X, ∑ x ∈ X.erase t, ((X.erase t).erase x).card =
          (X.card - 1) * (X.card - 2) := fun t ht => by
        rw [Finset.sum_congr rfl fun x hx => by rw [Finset.card_erase_of_mem hx, Finset.card_erase_of_mem ht, Nat.sub_sub],
          Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem ht]
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]; ring
    rw [hc1, hc2, hc3]
    rcases Nat.lt_or_ge X.card 2 with hlt | hge
    · interval_cases X.card <;> simp
    · zify [show 1 ≤ X.card by omega, show 2 ≤ X.card by omega]
      ring
  -- Part B: Distinct 4-tuples grouped by unordered 4-subset `T ∈ X.powersetCard 4`:
  have hDist : ∑ q ∈ Q.filter isDist, f q =
      8 * e * (4 * (fourSiteSingularCount X : ℤ) - (X.card.choose 4 : ℤ)) := by
    let toSet : (ZMod p × ZMod p) × (ZMod p × ZMod p) → Finset (ZMod p) :=
      fun q => {q.1.1, q.1.2, q.2.1, q.2.2}
    have hmaps : ∀ q ∈ Q.filter isDist, toSet q ∈ X.powersetCard 4 := by
      intro q hq
      obtain ⟨hqQ, h1, h2, h3, h4, h5, h6⟩ := mem_filter.mp hq
      simp only [Q, mem_product] at hqQ
      rw [mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro z hz
        simp only [toSet, mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl <;> tauto
      · simp [toSet, h1, h2, h3, h4, h5, h6]
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have hfiber : ∀ T ∈ X.powersetCard 4,
        ∑ q ∈ (Q.filter isDist).filter (fun q => toSet q = T), f q =
          8 * e * (4 * (if isFourSiteSingular T then (1 : ℤ) else 0) - 1) := by
      intro T hT
      obtain ⟨hTX, hT4⟩ := mem_powersetCard.mp hT
      let eqv : Fin 4 ≃ T := (T.equivFin.trans (finCongr hT4)).symm
      let v : Fin 4 → ZMod p := fun i => (eqv i).1
      have hv_inj : Function.Injective v := fun i j hij => eqv.injective (Subtype.ext hij)
      have hv_mem : ∀ i, v i ∈ T := fun i => (eqv i).2
      -- Bijection between `Equiv.Perm (Fin 4)` and the fiber `{q ∈ Q.filter isDist | toSet q = T}`:
      have hbij : ∑ q ∈ (Q.filter isDist).filter (fun q => toSet q = T), f q =
          ∑ σ : Equiv.Perm (Fin 4),
            (W (v (σ 0)) (v (σ 2)) * W (v (σ 0)) (v (σ 3))) *
              (W (v (σ 1)) (v (σ 2)) * W (v (σ 1)) (v (σ 3))) := by
        symm
        refine Finset.sum_bij (fun σ _ => ((v (σ 0), v (σ 1)), (v (σ 2), v (σ 3)))) ?_ ?_ ?_ ?_
        · intro σ _
          simp only [mem_filter, Q, mem_product, isDist]
          refine ⟨⟨⟨⟨hTX (hv_mem _), hTX (hv_mem _)⟩, ⟨hTX (hv_mem _), hTX (hv_mem _)⟩⟩,
            ⟨fun h => by have := σ.injective (hv_inj h); contradiction,
             fun h => by have := σ.injective (hv_inj h); contradiction,
             fun h => by have := σ.injective (hv_inj h); contradiction,
             fun h => by have := σ.injective (hv_inj h); contradiction,
             fun h => by have := σ.injective (hv_inj h); contradiction,
             fun h => by have := σ.injective (hv_inj h); contradiction⟩⟩, ?_⟩
          ext z
          simp only [toSet, mem_insert, mem_singleton]
          constructor
          · rintro (rfl | rfl | rfl | rfl) <;> exact hv_mem _
          · intro hz
            have hi : v (σ (σ.symm (eqv.symm ⟨z, hz⟩))) = z := by simp [v]
            generalize σ.symm (eqv.symm ⟨z, hz⟩) = i at hi
            fin_cases i <;> simp [← hi]
        · intro σ₁ _ σ₂ _ h
          simp only [Prod.mk.injEq] at h
          apply Equiv.ext
          intro i
          fin_cases i
          · exact hv_inj h.1.1
          · exact hv_inj h.1.2
          · exact hv_inj h.2.1
          · exact hv_inj h.2.2
        · intro q hq
          obtain ⟨hqD, hset⟩ := mem_filter.mp hq
          obtain ⟨_, h1, h2, h3, h4, h5, h6⟩ := mem_filter.mp hqD
          have hm0 : q.1.1 ∈ T := hset ▸ by simp [toSet]
          have hm1 : q.1.2 ∈ T := hset ▸ by simp [toSet]
          have hm2 : q.2.1 ∈ T := hset ▸ by simp [toSet]
          have hm3 : q.2.2 ∈ T := hset ▸ by simp [toSet]
          let g : Fin 4 → Fin 4 := fun i =>
            match i with
            | ⟨0, _⟩ => eqv.symm ⟨q.1.1, hm0⟩
            | ⟨1, _⟩ => eqv.symm ⟨q.1.2, hm1⟩
            | ⟨2, _⟩ => eqv.symm ⟨q.2.1, hm2⟩
            | ⟨3, _⟩ => eqv.symm ⟨q.2.2, hm3⟩
          have hg_inj : Function.Injective g := by
            intro i j hij
            have hv_eq : v (g i) = v (g j) := congrArg v hij
            fin_cases i <;> fin_cases j <;>
              simp [g, v, h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm,
                h6.symm] at hv_eq ⊢
          let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg_inj)
          refine ⟨σ, mem_univ σ, ?_⟩
          simp [σ, g, v]
        · intro σ _; rfl
      rw [hbij]
      -- Identify the `4 × 4` matrix `(W (v i) (v j))` with `fourSiteMatrix e a b c d f g`!
      let M4 := fourSiteMatrix e (W (v 0) (v 1)) (W (v 0) (v 2)) (W (v 0) (v 3))
        (W (v 1) (v 2)) (W (v 1) (v 3)) (W (v 2) (v 3))
      have hM4_eq : ∀ i j : Fin 4, W (v i) (v j) = M4 i j := by
        intro i j
        fin_cases i <;> fin_cases j
        all_goals
          first
          | rfl
          | exact hW_rev _ _
          | (change quadraticChar (ZMod p) (_ - _) = 0; rw [sub_self, MulChar.map_zero])
      have hdet_eq : (Matrix.of fun u y : T => W u.1 y.1).det = M4.det := by
        have hsub : (Matrix.of fun u y : T => W u.1 y.1).submatrix eqv eqv = M4 := by
          ext i j; exact hM4_eq i j
        rw [← hsub, Matrix.det_submatrix_equiv_self eqv]
      have hsing_iff : isFourSiteSingular T ↔ (((M4.det : ℤ) : ZMod 3) = 0) := by
        unfold isFourSiteSingular; rw [hdet_eq]
      simp_rw [hM4_eq, ← mul_assoc]
      rw [show (if isFourSiteSingular T then (1 : ℤ) else 0) =
          (if (((M4.det : ℤ) : ZMod 3) = 0) then (1 : ℤ) else 0) by simp only [hsing_iff]]
      exact perm_four_cycle_sum e (W (v 0) (v 1)) (W (v 0) (v 2)) (W (v 0) (v 3))
        (W (v 1) (v 2)) (W (v 1) (v 3)) (W (v 2) (v 3)) he_sq
        (hW_sq _ _ (fun h => by have := hv_inj h; contradiction))
        (hW_sq _ _ (fun h => by have := hv_inj h; contradiction))
        (hW_sq _ _ (fun h => by have := hv_inj h; contradiction))
        (hW_sq _ _ (fun h => by have := hv_inj h; contradiction))
        (hW_sq _ _ (fun h => by have := hv_inj h; contradiction))
        (hW_sq _ _ (fun h => by have := hv_inj h; contradiction))
    rw [Finset.sum_congr rfl hfiber, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, mul_one]
    congr 2
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rfl
  rw [hDist, hnonDist, add_comm]

/-- Explicit upper bound on `N_4(X)` for primes `p ≡ 1 (mod 4)` (where `χ(-1) = 1`). -/
theorem four_site_singular_le_mod1 (hp : p ≠ 2) (hmod : quadraticChar (ZMod p) (-1) = 1)
    (X : Finset (ZMod p)) (hn : 3 ≤ X.card) (hn' : X.card ≤ p / 2 + 2)
    {x : ℕ} (hx : 1 ≤ x) (hx' : 2 * x ≤ X.card - 1) :
    32 * (fourSiteSingularCount X : ℤ) ≤
      8 * (X.card.choose 4 : ℤ) +
        (X.card : ℤ) * (((X.card - 1 : ℕ) : ℤ) * ((X.card : ℤ) - 2 - 2 * x) ^ 2 +
          ((X.card : ℤ) - 1 - 2 * x) ^ 2 +
          4 * (x : ℤ) * ((p / 2 + X.card - 1 - 2 * x : ℕ) : ℤ)) -
        (X.card : ℤ) * ((X.card : ℤ) - 1) * (2 * (X.card : ℤ) - 3) := by
  have hid := energy_eq_four_site_singular hp X
  rw [hmod, mul_one] at hid
  have hup := four_site_energy_le hp X hn hn' hx hx'
  linarith

local instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

/-- Concrete four-site ternary rank bound at `p = 65537`: every 256-site set `X ⊆ ZMod 65537`
has at most `142,536,640` singular 4-subsets out of `C(256, 4) = 174,792,640`. -/
theorem four_site_singular_65537 (X : Finset (ZMod 65537)) (hX : X.card = 256) :
    fourSiteSingularCount X ≤ 142536640 := by
  have hmod : quadraticChar (ZMod 65537) (-1) = 1 := by
    have h256 : ((256 : ZMod 65537) ^ 2) = -1 := by decide
    rw [← h256, quadraticChar_sq_one' (by decide : (256 : ZMod 65537) ≠ 0)]
  have h := four_site_singular_le_mod1 (p := 65537) (by decide) hmod X
    (by omega) (by omega) (x := 63) (by decide) (by omega)
  rw [hX] at h
  have hch : (256 : ℕ).choose 4 = 174792640 := by
    have hdesc := Nat.descFactorial_eq_factorial_mul_choose 256 4
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial_succ,
      Nat.factorial_zero] at hdesc
    omega
  rw [hch] at h
  omega

/-- **Asymptotic four-site `𝔽₃`-rank ceiling (`13 / 16 + o(1)`)**:
for any sequence of primes `p n → ∞` with `χ(-1) = 1` (`p n ≡ 1 mod 4`) and sets `X n ⊆ ZMod (p n)`
with `|X n| / √(p n) → 1`, eventually `N_4(X n) / C(|X n|, 4) < 13 / 16 + ε`. -/
theorem eventually_four_site_singular_density_mod1 (p : ℕ → ℕ) [∀ n, Fact (p n).Prime]
    (hmod : ∀ n, quadraticChar (ZMod (p n)) (-1) = 1)
    (X : (n : ℕ) → Finset (ZMod (p n)))
    (hp : Tendsto p atTop atTop)
    (hX : Tendsto (fun n => ((X n).card : ℝ) / Real.sqrt (p n)) atTop (𝓝 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      (fourSiteSingularCount (X n) : ℝ) / (((X n).card.choose 4 : ℕ) : ℝ) < 13 / 16 + ε := by
  have hpR : Tendsto (fun n => (p n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hp
  have hr := Real.tendsto_sqrt_atTop.comp hpR
  have hn_top : Tendsto (fun n => ((X n).card : ℝ)) atTop atTop :=
    (hX.pos_mul_atTop (by norm_num) hr).congr' (by
      filter_upwards [hpR.eventually_gt_atTop 0] with n hn
      exact div_mul_cancel₀ _ (Real.sqrt_pos.mpr hn).ne')
  -- Normalized energy ceiling `U_{n/4} / n^4 → 3/4`, and `C(n, 4) / (n^4 / 24) → 1`:
  -- `N_4 / C(n,4) ≤ 1/4 + (3/4) * (U/n^4) / (24 * C(n,4) / n^4)` → `1/4 + (3/4)*(3/4) = 13/16`!
  -- Specifically, `32 * N_4 ≤ 8 * C(n,4) + U_x`, so `N_4 / C(n,4) ≤ 1/4 + (U_x / n^4) * (n^4 / (32 * C(n,4)))`.
  -- As `n → ∞`, `n^4 / (32 * C(n,4)) = 24 / 32 * (n^4 / (n(n-1)(n-2)(n-3))) → 3/4` and `U_{n/4} / n^4 → 3/4`!
  let env (p' m : ℝ) : ℝ :=
    1 / 4 + (3 / 4) * (1 / ((1 - 1 / m) * (1 - 2 / m) * (1 - 3 / m))) *
      ((1 / 2 + 2 / m) ^ 2 + (p' / 2 + m) / m ^ 2)
  have hlim_env : Tendsto (fun n => env (p n) (X n).card) atTop (𝓝 (13 / 16)) := by
    have hinv : Tendsto (fun n => ((X n).card : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hn_top
    have hfac1 : Tendsto (fun n => 1 - (1 : ℝ) * ((X n).card : ℝ)⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hinv.const_mul 1)
    have hfac2 : Tendsto (fun n => 1 - (2 : ℝ) * ((X n).card : ℝ)⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hinv.const_mul 2)
    have hfac3 : Tendsto (fun n => 1 - (3 : ℝ) * ((X n).card : ℝ)⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hinv.const_mul 3)
    have hden : Tendsto (fun n => (1 - 1 / ((X n).card : ℝ)) * (1 - 2 / ((X n).card : ℝ)) *
        (1 - 3 / ((X n).card : ℝ))) atTop (𝓝 1) := by
      simpa [div_eq_mul_inv] using (hfac1.mul hfac2).mul hfac3
    have hsq_term : Tendsto (fun n => (1 / 2 + 2 / ((X n).card : ℝ)) ^ 2) atTop (𝓝 (1 / 4)) := by
      have : Tendsto (fun n => 1 / 2 + 2 * ((X n).card : ℝ)⁻¹) atTop (𝓝 (1 / 2)) := by
        simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).add (hinv.const_mul 2)
      convert this.pow 2 using 1
      · ext n; ring
      · norm_num
    have hp_ratio : Tendsto (fun n => ((p n : ℝ) / 2 + (X n).card) / ((X n).card : ℝ) ^ 2)
        atTop (𝓝 (1 / 2)) := by
      have h1 : Tendsto (fun n => (1 / 2 : ℝ) / (((X n).card : ℝ) / Real.sqrt (p n)) ^ 2)
          atTop (𝓝 (1 / 2)) := by
        have h1' : Tendsto (fun n => (1 / 2 : ℝ) / (((X n).card : ℝ) / Real.sqrt (p n)) ^ 2)
            atTop (𝓝 ((1 / 2 : ℝ) / (1 ^ 2))) :=
          (tendsto_const_nhds (x := (1 / 2 : ℝ))).div (hX.pow 2) (by norm_num)
        simpa only [one_pow, div_one] using h1'
      have h2 := h1.add hinv
      rw [add_zero] at h2
      refine h2.congr' ?_
      filter_upwards [hpR.eventually_gt_atTop 0, hn_top.eventually_gt_atTop 0] with n hpn hn0
      have hrp := Real.sq_sqrt hpn.le
      have hrn := (Real.sqrt_pos.mpr hpn).ne'
      field_simp [hn0.ne', hrn]
      rw [hrp]
    have hprod := ((tendsto_const_nhds (x := (3 / 4 : ℝ))).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).div hden (by norm_num))).mul (hsq_term.add hp_ratio)
    convert (tendsto_const_nhds (x := (1 / 4 : ℝ))).add hprod using 1
    norm_num
  filter_upwards [hlim_env.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε)),
    hr.eventually_ge_atTop 16, hX.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)),
    hX.eventually (gt_mem_nhds (show (1 : ℝ) < 2 by norm_num)), hp.eventually_gt_atTop 2]
    with n hlimn hrn hla hua hpn
  dsimp at hrn hla hua hlimn
  let m := (X n).card
  have hrpos : 0 < Real.sqrt (p n) := by linarith
  have hla' := (lt_div_iff₀ hrpos).mp hla
  have hua' := (div_lt_iff₀ hrpos).mp hua
  have hm8 : 8 ≤ m := by
    have : (8 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hm2 : 2 * m ≤ p n := by
    have sqr := Real.sq_sqrt (show 0 ≤ (p n : ℝ) by positivity)
    have : 2 * (m : ℝ) ≤ p n := by
      nlinarith [mul_nonneg hrpos.le (show 0 ≤ Real.sqrt (p n) - 8 by linarith)]
    exact_mod_cast this
  let x := (m - 1) / 4
  have hx1 : 1 ≤ x := by dsimp [x]; omega
  have hx' : 2 * x ≤ m - 1 := by dsimp [x]; omega
  have hleZ := four_site_singular_le_mod1 (p := p n) (by omega) (hmod n) (X n)
    (by omega) (by omega) hx1 hx'
  -- Drop the negative `- n(n-1)(2n-3)` term (`≥ 0`):
  have hR_nn : (0 : ℤ) ≤ (m : ℤ) * ((m : ℤ) - 1) * (2 * (m : ℤ) - 3) := by
    have h1 : (0 : ℤ) ≤ m := by omega
    have h2 : (0 : ℤ) ≤ (m : ℤ) - 1 := by omega
    have h3 : (0 : ℤ) ≤ 2 * (m : ℤ) - 3 := by omega
    positivity
  have hleZ' : 32 * (fourSiteSingularCount (X n) : ℤ) ≤
      8 * (m.choose 4 : ℤ) +
        (m : ℤ) * (((m - 1 : ℕ) : ℤ) * ((m : ℤ) - 2 - 2 * x) ^ 2 +
          ((m : ℤ) - 1 - 2 * x) ^ 2 +
          4 * (x : ℤ) * ((p n / 2 + m - 1 - 2 * x : ℕ) : ℤ)) := by linarith
  have hleR : (32 : ℝ) * (fourSiteSingularCount (X n) : ℝ) ≤
      8 * ((m.choose 4 : ℕ) : ℝ) +
        (m : ℝ) * (((m - 1 : ℕ) : ℝ) * ((m : ℝ) - 2 - 2 * (x : ℝ)) ^ 2 +
          ((m : ℝ) - 1 - 2 * (x : ℝ)) ^ 2 +
          4 * (x : ℝ) * ((p n / 2 + m - 1 - 2 * x : ℕ) : ℝ)) := by
    have hh := (Int.cast_le (R := ℝ)).mpr hleZ'
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_natCast,
      Int.cast_one, Int.cast_ofNat] using hh
  -- Bound the bracket by `m^3 * ((1/2 + 2/m)^2 + (p n / 2 + m) / m^2)`:
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hx_lo : (m : ℝ) - 4 ≤ 4 * (x : ℝ) := by
    have : m - 1 ≤ 4 * x + 3 := by dsimp [x]; omega
    have : (m : ℝ) - 1 ≤ 4 * (x : ℝ) + 3 := by
      have h1 : ((m - 1 : ℕ) : ℝ) ≤ ((4 * x + 3 : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat] at h1
      exact h1
    linarith
  have hx_hi : 4 * (x : ℝ) ≤ m := by
    exact_mod_cast (show 4 * x ≤ m by dsimp [x]; omega)
  have hsq1 : ((m : ℝ) - 2 - 2 * (x : ℝ)) ^ 2 ≤ ((m : ℝ) / 2 + 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hsq2 : ((m : ℝ) - 1 - 2 * (x : ℝ)) ^ 2 ≤ ((m : ℝ) / 2 + 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have htail : ((p n / 2 + m - 1 - 2 * x : ℕ) : ℝ) ≤ (p n : ℝ) / 2 + m := by
    have h1 : 2 * (p n / 2 + m - 1 - 2 * x) ≤ p n + 2 * m := by omega
    have h2 : (2 : ℝ) * ((p n / 2 + m - 1 - 2 * x : ℕ) : ℝ) ≤ (p n : ℝ) + 2 * m := by
      exact_mod_cast h1
    linarith
  have hbrack : ((m - 1 : ℕ) : ℝ) * ((m : ℝ) - 2 - 2 * (x : ℝ)) ^ 2 +
        ((m : ℝ) - 1 - 2 * (x : ℝ)) ^ 2 +
        4 * (x : ℝ) * ((p n / 2 + m - 1 - 2 * x : ℕ) : ℝ) ≤
      (m : ℝ) * ((m : ℝ) / 2 + 2) ^ 2 + (m : ℝ) * ((p n : ℝ) / 2 + m) := by
    have hm1 : ((m - 1 : ℕ) : ℝ) + 1 = m := by
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]; ring
    have hA : ((m - 1 : ℕ) : ℝ) * ((m : ℝ) - 2 - 2 * (x : ℝ)) ^ 2 +
        ((m : ℝ) - 1 - 2 * (x : ℝ)) ^ 2 ≤ (m : ℝ) * ((m : ℝ) / 2 + 2) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hsq1 (Nat.cast_nonneg (m - 1)), hm1]
    have hB : 4 * (x : ℝ) * ((p n / 2 + m - 1 - 2 * x : ℕ) : ℝ) ≤
        (m : ℝ) * ((p n : ℝ) / 2 + m) :=
      mul_le_mul hx_hi htail (by positivity) hmR.le
    linarith
  -- Relate `m.choose 4` to `m * (m - 1) * (m - 2) * (m - 3) / 24`:
  have hch_eq : (24 : ℝ) * ((m.choose 4 : ℕ) : ℝ) =
      (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) * ((m : ℝ) - 3) := by
    have hnat : m.choose 4 * 24 = m * (m - 1) * (m - 2) * (m - 3) := by
      have hdesc := Nat.descFactorial_eq_factorial_mul_choose m 4
      simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial_succ,
        Nat.factorial_zero] at hdesc
      calc m.choose 4 * 24 = 4 * (3 * (2 * (1 * 1))) * m.choose 4 := by ring
        _ = (m - 3) * ((m - 2) * ((m - 1) * (m * 1))) := hdesc.symm
        _ = m * (m - 1) * (m - 2) * (m - 3) := by ring
    have hR : ((m.choose 4 : ℕ) : ℝ) * 24 =
        ((m * (m - 1) * (m - 2) * (m - 3) : ℕ) : ℝ) := by exact_mod_cast hnat
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ m),
      Nat.cast_sub (by omega : 2 ≤ m), Nat.cast_sub (by omega : 3 ≤ m)] at hR
    push_cast at hR
    linarith
  have hm8R : (8 : ℝ) ≤ m := by exact_mod_cast hm8
  have hch_pos : (0 : ℝ) < ((m.choose 4 : ℕ) : ℝ) := by
    have hprod_pos : 0 < (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) * ((m : ℝ) - 3) := by
      have h1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
      have h2 : (0 : ℝ) < (m : ℝ) - 2 := by linarith
      have h3 : (0 : ℝ) < (m : ℝ) - 3 := by linarith
      positivity
    linarith
  have hbound_env : (fourSiteSingularCount (X n) : ℝ) / ((m.choose 4 : ℕ) : ℝ) ≤
      env (p n) m := by
    rw [div_le_iff₀ hch_pos]
    have hU : (32 : ℝ) * (fourSiteSingularCount (X n) : ℝ) ≤
        8 * ((m.choose 4 : ℕ) : ℝ) +
          (m : ℝ) * ((m : ℝ) * ((m : ℝ) / 2 + 2) ^ 2 + (m : ℝ) * ((p n : ℝ) / 2 + m)) :=
      hleR.trans (by nlinarith [mul_le_mul_of_nonneg_left hbrack hmR.le])
    have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
    have hm2' : (m : ℝ) - 2 ≠ 0 := by linarith
    have hm3 : (m : ℝ) - 3 ≠ 0 := by linarith
    have hden_ne : (1 - 1 / (m : ℝ)) * (1 - 2 / (m : ℝ)) * (1 - 3 / (m : ℝ)) ≠ 0 := by
      have : (1 - 1 / (m : ℝ)) * (1 - 2 / (m : ℝ)) * (1 - 3 / (m : ℝ)) =
          ((m : ℝ) - 1) * ((m : ℝ) - 2) * ((m : ℝ) - 3) / (m : ℝ) ^ 3 := by
        field_simp [hmR.ne']
      rw [this]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero hm1 hm2') hm3) (pow_ne_zero 3 hmR.ne')
    have hident : 32 * (env (p n) m * ((m.choose 4 : ℕ) : ℝ)) =
        8 * ((m.choose 4 : ℕ) : ℝ) +
          (m : ℝ) * ((m : ℝ) * ((m : ℝ) / 2 + 2) ^ 2 + (m : ℝ) * ((p n : ℝ) / 2 + m)) := by
      dsimp [env]
      calc 32 * ((1 / 4 + 3 / 4 * (1 / ((1 - 1 / (m : ℝ)) * (1 - 2 / (m : ℝ)) * (1 - 3 / (m : ℝ)))) *
                ((1 / 2 + 2 / (m : ℝ)) ^ 2 + ((p n : ℝ) / 2 + m) / (m : ℝ) ^ 2)) *
                ((m.choose 4 : ℕ) : ℝ))
          = 8 * ((m.choose 4 : ℕ) : ℝ) +
              (24 * ((m.choose 4 : ℕ) : ℝ)) /
                ((1 - 1 / (m : ℝ)) * (1 - 2 / (m : ℝ)) * (1 - 3 / (m : ℝ))) *
                ((1 / 2 + 2 / (m : ℝ)) ^ 2 + ((p n : ℝ) / 2 + m) / (m : ℝ) ^ 2) := by ring
        _ = 8 * ((m.choose 4 : ℕ) : ℝ) +
              ((m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) * ((m : ℝ) - 3)) /
                ((1 - 1 / (m : ℝ)) * (1 - 2 / (m : ℝ)) * (1 - 3 / (m : ℝ))) *
                ((1 / 2 + 2 / (m : ℝ)) ^ 2 + ((p n : ℝ) / 2 + m) / (m : ℝ) ^ 2) := by rw [hch_eq]
        _ = _ := by
              field_simp [hmR.ne', hm1, hm2', hm3, hden_ne]
    linarith
  exact hbound_env.trans_lt hlimn

end FourSiteRank

/-! ## 6. Overlap improvement in the skew prime class (`p ≡ 3 mod 4`) -/

section SkewOverlap

variable {p : ℕ} [Fact p.Prime]

/-- Skew symmetry kills the diagonal block `C × C` when `χ(-1) = -1` (`p ≡ 3 mod 4`). -/
theorem skew_sum_diag_zero (hskew : quadraticChar (ZMod p) (-1) = -1) (C : Finset (ZMod p)) :
    ∑ u ∈ C, ∑ t ∈ C, quadraticChar (ZMod p) (u - t) = 0 := by
  have hneg : ∑ u ∈ C, ∑ t ∈ C, quadraticChar (ZMod p) (u - t) =
      -(∑ u ∈ C, ∑ t ∈ C, quadraticChar (ZMod p) (u - t)) := by
    calc ∑ u ∈ C, ∑ t ∈ C, quadraticChar (ZMod p) (u - t)
        = ∑ t ∈ C, ∑ u ∈ C, quadraticChar (ZMod p) (u - t) := Finset.sum_comm
      _ = ∑ t ∈ C, ∑ u ∈ C, -(quadraticChar (ZMod p) (t - u)) := by
            refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_
            rw [show u - t = (-1) * (t - u) by ring, map_mul, hskew, neg_one_mul]
      _ = -(∑ t ∈ C, ∑ u ∈ C, quadraticChar (ZMod p) (t - u)) := by
            simp only [Finset.sum_neg_distrib]
  omega

/-- **Finite skew-prime (`p ≡ 3 mod 4`) overlap discrepancy bound**:
if `χ(-1) = -1`, `C = A ∩ B`, `S = ∑ u ∈ A, ∑ t ∈ B, χ(u - t)`, and `M` bounds the row-square
energy `∑ t ∈ B, (∑ u ∈ A, χ(u - t))^2 ≤ M`:
1. Trivial skew bound: `|S| ≤ |A| * |B| - |C|^2`.
2. Sharp Cauchy–Schwarz overlap bound: when `0 < |C|`, `0 < |B \ C|`, and
   `(|C| * (|A| - |C|))^2 * |B| ≤ |C|^2 * M`,
   `|S| ≤ |C| * (|A| - |C|) + √(|B \ C| * (M - |C| * (|A| - |C|)^2))`. -/
theorem skew_overlap_discrepancy_le (hskew : quadraticChar (ZMod p) (-1) = -1)
    (A B : Finset (ZMod p)) (M : ℝ)
    (hM : (∑ t ∈ B, (∑ u ∈ A, quadraticChar (ZMod p) (u - t)) ^ 2 : ℝ) ≤ M) :
    let C := A ∩ B
    let S : ℝ := (∑ u ∈ A, ∑ t ∈ B, quadraticChar (ZMod p) (u - t) : ℤ)
    |S| ≤ (A.card : ℝ) * (B.card : ℝ) - (C.card : ℝ) ^ 2 ∧
    (0 < C.card → 0 < (B \ C).card →
      ((C.card : ℝ) * ((A.card : ℝ) - C.card)) ^ 2 * (B.card : ℝ) ≤ (C.card : ℝ) ^ 2 * M →
      |S| ≤ (C.card : ℝ) * ((A.card : ℝ) - C.card) +
        Real.sqrt (((B \ C).card : ℝ) * (M - (C.card : ℝ) * ((A.card : ℝ) - C.card) ^ 2))) := by
  classical
  intro C S
  let R : ZMod p → ℤ := fun t => ∑ u ∈ A, quadraticChar (ZMod p) (u - t)
  have hS_split : S = ((∑ t ∈ C, R t : ℤ) : ℝ) + ((∑ t ∈ B \ C, R t : ℤ) : ℝ) := by
    dsimp [S, R]
    rw [Finset.sum_comm]
    have hdisj : Disjoint C (B \ C) := disjoint_sdiff
    have hunion : C ∪ (B \ C) = B := Finset.union_sdiff_of_subset Finset.inter_subset_right
    conv_lhs => rw [← hunion]
    rw [Finset.sum_union hdisj, Int.cast_add]
  -- Bound `|∑ t ∈ C, R t| ≤ |C| * (|A| - |C|)` by skew symmetry on `C × C`!
  have hC_bound : |((∑ t ∈ C, R t : ℤ) : ℝ)| ≤ (C.card : ℝ) * ((A.card : ℝ) - C.card) := by
    have hC_eq : ∑ t ∈ C, R t = ∑ u ∈ A \ C, ∑ t ∈ C, quadraticChar (ZMod p) (u - t) := by
      dsimp [R]
      rw [Finset.sum_comm]
      have hdisj : Disjoint C (A \ C) := disjoint_sdiff
      have hunion : C ∪ (A \ C) = A := Finset.union_sdiff_of_subset Finset.inter_subset_left
      conv_lhs => rw [← hunion]
      rw [Finset.sum_union hdisj, skew_sum_diag_zero hskew C, zero_add]
    have hleZ : |∑ t ∈ C, R t| ≤ ((A \ C).card : ℤ) * (C.card : ℤ) := by
      rw [hC_eq]
      calc _ ≤ ∑ u ∈ A \ C, |∑ t ∈ C, quadraticChar (ZMod p) (u - t)| := Finset.abs_sum_le_sum_abs ..
        _ ≤ ∑ _u ∈ A \ C, (C.card : ℤ) := by
              refine Finset.sum_le_sum fun u _ => ?_
              calc _ ≤ ∑ t ∈ C, |quadraticChar (ZMod p) (u - t)| := Finset.abs_sum_le_sum_abs ..
                _ ≤ ∑ _t ∈ C, (1 : ℤ) := Finset.sum_le_sum fun t _ => by
                      by_cases h : u - t = 0
                      · simp [h]
                      · rcases quadraticChar_dichotomy h with h1 | h1 <;> rw [h1] <;> decide
                _ = (C.card : ℤ) := by simp
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hcard_sdiff : ((A \ C).card : ℝ) = (A.card : ℝ) - C.card := by
      have := Finset.card_sdiff (s := C) (t := A)
      have hle : C.card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
      have hsub : (A \ C).card = A.card - C.card := by
        rw [Finset.card_sdiff_of_subset Finset.inter_subset_left]
      rw [hsub, Nat.cast_sub hle]
    have hleR : |((∑ t ∈ C, R t : ℤ) : ℝ)| ≤ ((A \ C).card : ℝ) * (C.card : ℝ) := by
      exact_mod_cast hleZ
    rw [hcard_sdiff] at hleR
    linarith
  constructor
  · -- Part 1: `|S| ≤ |A| * |B| - |C|^2`.
    have hBC_bound : |((∑ t ∈ B \ C, R t : ℤ) : ℝ)| ≤ ((B \ C).card : ℝ) * (A.card : ℝ) := by
      have hleZ : |∑ t ∈ B \ C, R t| ≤ ((B \ C).card : ℤ) * (A.card : ℤ) := by
        calc _ ≤ ∑ t ∈ B \ C, |R t| := Finset.abs_sum_le_sum_abs ..
          _ ≤ ∑ _t ∈ B \ C, (A.card : ℤ) := by
                refine Finset.sum_le_sum fun t _ => ?_
                calc _ ≤ ∑ u ∈ A, |quadraticChar (ZMod p) (u - t)| := Finset.abs_sum_le_sum_abs ..
                  _ ≤ ∑ _u ∈ A, (1 : ℤ) := Finset.sum_le_sum fun u _ => by
                        by_cases h : u - t = 0
                        · simp [h]
                        · rcases quadraticChar_dichotomy h with h1 | h1 <;> rw [h1] <;> decide
                  _ = (A.card : ℤ) := by simp
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
      exact_mod_cast hleZ
    have hBC_card : ((B \ C).card : ℝ) = (B.card : ℝ) - C.card := by
      have hle : C.card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
      rw [Finset.card_sdiff_of_subset Finset.inter_subset_right, Nat.cast_sub hle]
    rw [hBC_card] at hBC_bound
    have htri : |S| ≤ |((∑ t ∈ C, R t : ℤ) : ℝ)| + |((∑ t ∈ B \ C, R t : ℤ) : ℝ)| := by
      rw [hS_split]; exact abs_add_le _ _
    nlinarith
  · -- Part 2: Sharp Cauchy–Schwarz overlap bound.
    intro hC_pos hBC_pos hregime
    set u : ℝ := |((∑ t ∈ C, R t : ℤ) : ℝ)|
    set v : ℝ := |((∑ t ∈ B \ C, R t : ℤ) : ℝ)|
    set uMax : ℝ := (C.card : ℝ) * ((A.card : ℝ) - C.card)
    have hCR : (0 : ℝ) < C.card := by exact_mod_cast hC_pos
    have hBCR : (0 : ℝ) < (B \ C).card := by exact_mod_cast hBC_pos
    have hBC_add : (C.card : ℝ) + ((B \ C).card : ℝ) = (B.card : ℝ) := by
      have hle : C.card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
      rw [Finset.card_sdiff_of_subset Finset.inter_subset_right, Nat.cast_sub hle]; ring
    -- Cauchy–Schwarz on `C` and `B \ C`:
    have hcsC : u ^ 2 ≤ (C.card : ℝ) * ∑ t ∈ C, ((R t : ℤ) : ℝ) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := C) (f := fun t => ((R t : ℤ) : ℝ))
      simpa [u, sq_abs] using h
    have hcsBC : v ^ 2 ≤ ((B \ C).card : ℝ) * ∑ t ∈ B \ C, ((R t : ℤ) : ℝ) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := B \ C) (f := fun t => ((R t : ℤ) : ℝ))
      simpa [v, sq_abs] using h
    have hM_split : (∑ t ∈ C, ((R t : ℤ) : ℝ) ^ 2) + ∑ t ∈ B \ C, ((R t : ℤ) : ℝ) ^ 2 ≤ M := by
      have hdisj : Disjoint C (B \ C) := disjoint_sdiff
      have hunion : C ∪ (B \ C) = B := Finset.union_sdiff_of_subset Finset.inter_subset_right
      rw [← Finset.sum_union hdisj, hunion]
      simpa [R] using hM
    -- Combine: `u^2 / |C| + v^2 / |B \ C| ≤ M`.
    have hquad : u ^ 2 / (C.card : ℝ) + v ^ 2 / ((B \ C).card : ℝ) ≤ M := by
      have h1 : u ^ 2 / (C.card : ℝ) ≤ ∑ t ∈ C, ((R t : ℤ) : ℝ) ^ 2 :=
        (div_le_iff₀ hCR).mpr (by linarith)
      have h2 : v ^ 2 / ((B \ C).card : ℝ) ≤ ∑ t ∈ B \ C, ((R t : ℤ) : ℝ) ^ 2 :=
        (div_le_iff₀ hBCR).mpr (by linarith)
      linarith
    -- Algebraic monotonicity of `u ↦ u + √(|B\C| * (M - u^2 / |C|))` on `[0, uMax]`:
    -- Need to prove `u + v ≤ uMax + √(|B\C| * (M - uMax^2 / |C|))`.
    -- Note `uMax^2 / |C| = |C| * (|A| - |C|)^2`, so `M - uMax^2 / |C| = M - |C| * (|A| - |C|)^2 ≥ 0`.
    have huMax_nn : 0 ≤ uMax := by
      have : C.card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
      have : (C.card : ℝ) ≤ A.card := by exact_mod_cast this
      dsimp [uMax]; nlinarith
    have hu_le : u ≤ uMax := hC_bound
    have hrad_eq : M - uMax ^ 2 / (C.card : ℝ) = M - (C.card : ℝ) * ((A.card : ℝ) - C.card) ^ 2 := by
      dsimp [uMax]; field_simp [hCR.ne']
    have hrad_nn : 0 ≤ M - uMax ^ 2 / (C.card : ℝ) := by
      have : uMax ^ 2 * (C.card : ℝ) ≤ uMax ^ 2 * (B.card : ℝ) :=
        mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
      have : uMax ^ 2 ≤ (C.card : ℝ) * M := by nlinarith
      rw [sub_nonneg, div_le_iff₀ hCR]; linarith
    -- Key algebraic claim: `v - √(|B\C|*(M - uMax^2/|C|)) ≤ uMax - u`.
    set wMax : ℝ := Real.sqrt (((B \ C).card : ℝ) * (M - uMax ^ 2 / (C.card : ℝ)))
    have hwMax_sq : wMax ^ 2 = ((B \ C).card : ℝ) * (M - uMax ^ 2 / (C.card : ℝ)) :=
      Real.sq_sqrt (mul_nonneg hBCR.le hrad_nn)
    have hv_sq_le : v ^ 2 ≤ ((B \ C).card : ℝ) * (M - u ^ 2 / (C.card : ℝ)) := by
      have : v ^ 2 / ((B \ C).card : ℝ) ≤ M - u ^ 2 / (C.card : ℝ) := by linarith
      exact (div_le_iff₀ hBCR).mp this |> fun h => by linarith
    -- Since `uMax^2 * |B| ≤ |C|^2 * M`, we have `uMax * |B\C| ≤ |C| * wMax`!
    have hslope : uMax * ((B \ C).card : ℝ) ≤ (C.card : ℝ) * wMax := by
      have hsq : (uMax * ((B \ C).card : ℝ)) ^ 2 ≤ ((C.card : ℝ) * wMax) ^ 2 := by
        rw [mul_pow uMax, mul_pow (C.card : ℝ) wMax, hwMax_sq]
        have : (C.card : ℝ) ^ 2 * (((B \ C).card : ℝ) * (M - uMax ^ 2 / (C.card : ℝ))) =
            ((B \ C).card : ℝ) * ((C.card : ℝ) ^ 2 * M - (C.card : ℝ) * uMax ^ 2) := by
          field_simp [hCR.ne']
        rw [this]
        have hstep : uMax ^ 2 * ((B \ C).card : ℝ) ≤ (C.card : ℝ) ^ 2 * M - (C.card : ℝ) * uMax ^ 2 := by
          nlinarith [hregime, hBC_add]
        nlinarith [mul_le_mul_of_nonneg_left hstep hBCR.le]
      exact le_of_sq_le_sq hsq (mul_nonneg hCR.le (Real.sqrt_nonneg _))
    -- Now `(wMax + (uMax - u))^2 ≥ v^2`!
    -- Expand: `wMax^2 + 2*wMax*(uMax - u) + (uMax - u)^2 - ((B\C) * (M - u^2/|C|))`
    -- `= 2*wMax*(uMax - u) + (uMax - u)^2 - (|B\C|/|C|)*(uMax^2 - u^2)`
    -- `= (uMax - u) * (2*wMax + (uMax - u) - (|B\C|/|C|)*(uMax + u))`
    -- `≥ (uMax - u) * (2*(|B\C|/|C|)*uMax - (|B\C|/|C|)*(uMax + u) + (uMax - u))`
    -- `= (uMax - u)^2 * (|B\C|/|C| + 1) ≥ 0`!!
    have hmain_sq : v ^ 2 ≤ (wMax + (uMax - u)) ^ 2 := by
      have h1 : 0 ≤ (C.card : ℝ) * ((wMax + (uMax - u)) ^ 2 -
          ((B \ C).card : ℝ) * (M - u ^ 2 / (C.card : ℝ))) := by
        have hident : (C.card : ℝ) * ((wMax + (uMax - u)) ^ 2 -
              ((B \ C).card : ℝ) * (M - u ^ 2 / (C.card : ℝ))) =
            (uMax - u) * (2 * ((C.card : ℝ) * wMax - ((B \ C).card : ℝ) * uMax) +
              (uMax - u) * ((C.card : ℝ) + ((B \ C).card : ℝ))) := by
          have : (C.card : ℝ) * (wMax ^ 2 - ((B \ C).card : ℝ) * (M - u ^ 2 / (C.card : ℝ))) =
              -((B \ C).card : ℝ) * (uMax ^ 2 - u ^ 2) := by
            rw [hwMax_sq]; field_simp [hCR.ne']; ring
          linear_combination this
        rw [hident]
        have hdiff_nn : 0 ≤ uMax - u := by linarith
        have hterm_nn : 0 ≤ 2 * ((C.card : ℝ) * wMax - ((B \ C).card : ℝ) * uMax) +
            (uMax - u) * ((C.card : ℝ) + ((B \ C).card : ℝ)) := by nlinarith [hslope]
        exact mul_nonneg hdiff_nn hterm_nn
      have h2 : ((B \ C).card : ℝ) * (M - u ^ 2 / (C.card : ℝ)) ≤ (wMax + (uMax - u)) ^ 2 := by
        nlinarith [h1, hCR]
      linarith [hv_sq_le, h2]
    have hv_le : v ≤ wMax + (uMax - u) :=
      le_of_sq_le_sq hmain_sq (by linarith [Real.sqrt_nonneg (((B \ C).card : ℝ) * (M - uMax ^ 2 / (C.card : ℝ)))])
    have htri : |S| ≤ u + v := by rw [hS_split]; exact abs_add_le _ _
    rw [← hrad_eq]
    linarith

end SkewOverlap

end ProximityGap.PaleyFourSiteRankAndOverlap

#print axioms ProximityGap.PaleyFourSiteRankAndOverlap.four_site_energy_le
#print axioms ProximityGap.PaleyFourSiteRankAndOverlap.energy_eq_four_site_singular
#print axioms ProximityGap.PaleyFourSiteRankAndOverlap.four_site_singular_le_mod1
#print axioms ProximityGap.PaleyFourSiteRankAndOverlap.four_site_singular_65537
#print axioms ProximityGap.PaleyFourSiteRankAndOverlap.eventually_four_site_singular_density_mod1
#print axioms ProximityGap.PaleyFourSiteRankAndOverlap.skew_sum_diag_zero
#print axioms ProximityGap.PaleyFourSiteRankAndOverlap.skew_overlap_discrepancy_le

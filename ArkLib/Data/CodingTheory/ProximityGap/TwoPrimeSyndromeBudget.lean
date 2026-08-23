/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.TwoPrimeWindowLaw
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungTwoPow

/-!
# Issue #232 — The two-prime SYNDROME LIST BUDGET (the O61 consumer on `μ_{p^a·q^b}`)

O97 (`TwoPrimeWindowLaw`) made the mixed-radix tower unconditional.  This file
wires it into the prize-side consumer shape of
`LamLeungTwoPow.unit_syndrome_list_budget`/`tower_count` (O55/O61): counting the
power-sum-windowed subsets (= unit-syndrome-compatible error supports) of a
two-prime-smooth evaluation domain.

* `two_prime_tower_count` — **the count**: on any `D₀ ⊆ μ_{p^a·q^b}`, the
  `w`-subsets whose power sums vanish on the interval window
  `1 ≤ j < p^(t-1)·(q^b+1)` number at most `2^|D₀^(p^t)|` — each such subset is
  `μ_{p^t}`-closed (O97 `two_prime_partial_climb`), hence a union of full
  `μ_{p^t}`-cosets, hence determined by its `p^t`-th-power image.  The two-prime
  analogue of O55 `tower_count` (which is the pure 2-power case).
* `m31_syndrome_budget` — **the M31 landing**: on the multiplicative smooth domain
  `μ_18` of `F_{2^31−1}` (`18 = 3²·2`), supports killing the window `1 ≤ j < 9`
  number at most `2^|D₀^9|` per cardinality.  At `D₀ = μ_18` this budget is `4`
  and EXACT: the verified census (probe `probe_two_prime_window_law.py` at
  `n = 18`, full `2^18` space) finds exactly `∅`, the two rotated `μ_9`-cosets,
  and `μ_18` — cardinality pattern `(0, 9, 9, 18)`.

Honest scope: the bound counts windowed subsets of EVERY cardinality `w`; it is
the closure/coset-determinacy budget, not a decoding-radius statement.  The
window is the O97 interval form (slack ≤ 4 versus sharp, recorded in the probe).
-/

namespace TwoPrimeSyndromeBudget

open Finset

variable {F : Type*} [Field F]

/-- **The two-prime tower count** (O55 `tower_count` at two-prime moduli): subsets
of `D₀ ⊆ μ_{p^a·q^b}` with power sums vanishing on `1 ≤ j < p^(t-1)·(q^b+1)` are
`μ_{p^t}`-closed (O97), hence determined by their `p^t`-th-power image — at most
`2^|D₀^(p^t)|` of them in every cardinality `w`. -/
theorem two_prime_tower_count [DecidableEq F] [CharZero F] {p q a b t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (ht : t ≤ a)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b))
    {D₀ : Finset F} (hD₀ : ∀ x ∈ D₀, x ^ (p ^ a * q ^ b) = 1) (w : ℕ) :
    ((D₀.powersetCard w).filter (fun S =>
        ∀ j, 1 ≤ j → j < p ^ (t - 1) * (q ^ b + 1) → ∑ x ∈ S, x ^ j = 0)).card
      ≤ 2 ^ (D₀.image (· ^ p ^ t)).card := by
  classical
  have hnpos : 0 < p ^ a * q ^ b := Nat.mul_pos (pow_pos hp.pos a) (pow_pos hq.pos b)
  have hne0 : ∀ x ∈ D₀, x ≠ 0 := by
    intro x hx h0
    have h1 := hD₀ x hx
    rw [h0, zero_pow hnpos.ne'] at h1
    exact zero_ne_one h1
  rw [← Finset.card_powerset]
  apply Finset.card_le_card_of_injOn (fun S => S.image (· ^ p ^ t))
  · -- maps into the powerset of the image space
    intro S hS
    have hS2 := Finset.mem_coe.mp hS
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hS2
    simp only [Finset.mem_coe, Finset.mem_powerset]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨x, hS2.1.1 hx, rfl⟩
  · -- injectivity: closure makes each subset recoverable from its image
    intro S hSm S' hSm' himg
    have hmem := Finset.mem_coe.mp hSm
    have hmem' := Finset.mem_coe.mp hSm'
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hmem hmem'
    obtain ⟨⟨hSD, _⟩, hPS⟩ := hmem
    obtain ⟨⟨hSD', _⟩, hPS'⟩ := hmem'
    have h0S : (0 : F) ∉ S := fun h => hne0 0 (hSD h) rfl
    have h0S' : (0 : F) ∉ S' := fun h => hne0 0 (hSD' h) rfl
    have hclos : ∀ x ∈ S, ∀ h : F, h ^ p ^ t = 1 → h * x ∈ S :=
      TwoPrimeWindowLaw.two_prime_partial_climb hp hq hpq ht hζ h0S
        (fun x hx => hD₀ x (hSD hx)) hPS
    have hclos' : ∀ x ∈ S', ∀ h : F, h ^ p ^ t = 1 → h * x ∈ S' :=
      TwoPrimeWindowLaw.two_prime_partial_climb hp hq hpq ht hζ h0S'
        (fun x hx => hD₀ x (hSD' hx)) hPS'
    -- recovery: a closed subset is the filter of its image fiber
    have hrec : ∀ T : Finset F, T ⊆ D₀ →
        (∀ x ∈ T, ∀ h : F, h ^ p ^ t = 1 → h * x ∈ T) →
        T = D₀.filter (fun x => x ^ p ^ t ∈ T.image (· ^ p ^ t)) := by
      intro T hTD hTclos
      apply Finset.Subset.antisymm
      · intro x hx
        exact Finset.mem_filter.mpr ⟨hTD hx, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
      · intro x hx
        obtain ⟨hxD, hxim⟩ := Finset.mem_filter.mp hx
        obtain ⟨x₀, hx₀, hpow⟩ := Finset.mem_image.mp hxim
        have hx₀0 : x₀ ≠ 0 := hne0 x₀ (hTD hx₀)
        have hx00 : x₀ ^ p ^ t ≠ 0 := pow_ne_zero _ hx₀0
        have hquot : (x / x₀) ^ p ^ t = 1 := by
          rw [div_pow, ← hpow, div_self hx00]
        have hmul := hTclos x₀ hx₀ (x / x₀) hquot
        rwa [div_mul_cancel₀ x hx₀0] at hmul
    have himg' : S.image (· ^ p ^ t) = S'.image (· ^ p ^ t) := himg
    rw [hrec S hSD hclos, hrec S' hSD' hclos', himg']

/-- **The M31 syndrome budget**: on the two-prime-smooth multiplicative domain
`μ_18` of `F_{2^31−1}`, error supports killing the unit-syndrome window
`1 ≤ j < 9` number at most `2^|D₀^9|` per cardinality — at `D₀ = μ_18` the budget
is `4` and exact (census: `∅`, the two rotated `μ_9`-cosets, `μ_18`). -/
theorem m31_syndrome_budget [DecidableEq F] [CharZero F] {ζ : F}
    (hζ : IsPrimitiveRoot ζ 18) {D₀ : Finset F} (hD₀ : ∀ x ∈ D₀, x ^ 18 = 1)
    (w : ℕ) :
    ((D₀.powersetCard w).filter (fun S =>
        ∀ j, 1 ≤ j → j < 9 → ∑ x ∈ S, x ^ j = 0)).card
      ≤ 2 ^ (D₀.image (· ^ 9)).card := by
  have h18 : (18 : ℕ) = 3 ^ 2 * 2 ^ 1 := by norm_num
  rw [h18] at hζ hD₀
  have h := two_prime_tower_count (t := 2) Nat.prime_three Nat.prime_two
    (by norm_num) le_rfl hζ hD₀ w
  norm_num at h
  exact h

open Classical in
/-- **The literal O61 consumer on `μ_18`**: unit-syndrome-compatible supports
(`TopLine.CompatC` at the unit vector, syndrome length `8`) over any
`D₀ ⊆ μ_18` number at most `2^|D₀^9|` per cardinality — the
`unit_syndrome_list_budget` shape transported from the 2-power tower (O61) to the
M31 multiplicative two-prime domain: CompatC ⟷ esymm window (O45
`zero_fiber_filter_eq`) ⟷ power-sum window (O60 Newton bridge) → the O98 count. -/
theorem m31_unit_syndrome_budget [DecidableEq F] [CharZero F] {ζ : F}
    (hζ : IsPrimitiveRoot ζ 18) {D₀ : Finset F} (hD₀ : ∀ x ∈ D₀, x ^ 18 = 1)
    {w N : ℕ} (hw : w + 8 = N) (hcw : 8 ≤ w) :
    ((D₀.powersetCard w).filter (fun E =>
        TopLine.CompatC (TopLine.unitVec (w - 1)) N 8 E)).card
      ≤ 2 ^ (D₀.image (· ^ 9)).card := by
  rw [TopLine.zero_fiber_filter_eq hw (by norm_num) hcw D₀]
  refine le_trans (le_of_eq ?_) (m31_syndrome_budget hζ hD₀ w)
  congr 1
  refine Finset.filter_congr fun E _ => ?_
  constructor
  · intro he j hj1 hj2
    exact LamLeungTwoPow.psum_window_of_esymm_window he j
      (Finset.mem_Icc.mpr ⟨hj1, by omega⟩)
  · intro hp
    refine LamLeungTwoPow.esymm_window_of_psum_window fun j hj => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
    exact hp j h1 (by omega)

end TwoPrimeSyndromeBudget

#print axioms TwoPrimeSyndromeBudget.two_prime_tower_count
#print axioms TwoPrimeSyndromeBudget.m31_syndrome_budget
#print axioms TwoPrimeSyndromeBudget.m31_unit_syndrome_budget

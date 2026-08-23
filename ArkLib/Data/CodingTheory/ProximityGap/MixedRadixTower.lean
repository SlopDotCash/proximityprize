/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.CRTDoubleSlice
import ArkLib.Data.CodingTheory.ProximityGap.TopDirectionLineCount

/-!
# Issue #232 — The MIXED-RADIX tower skeleton (conditional on the de Bruijn base case)

The two-prime-smooth-domain analogue of `LamLeungTwoPow.full_tower`, assembled exactly
the way `TopLine.t2_tower_resolution` preceded the proven Lam–Leung brick: every piece of
DESCENT machinery is machine-checked here, and the CLASSICAL BASE CASES (the de
Bruijn/packet-closure statements at each tower level, DISPROOF_LOG O67/O70) enter as
named, documented hypotheses — so the day the de Bruijn brick lands, the mixed tower goes
unconditional by plugging it in, with zero re-proving.

## Architecture (all proven, 0 sorry)

* `mu_mul_closure` — the generic mixed rung-assembly step: closure under `μ_d` plus
  `μ_p`-closure of the `d`-th-power image upgrades to closure under `μ_{p·d}`
  (characteristic-free; the radix-`d` analogue of
  `LamLeungTwoPow.mu_double_closure`/`TopLine.mul_root_closure`).
* `pow_fiber_coset` / `pow_fiber_card` / `pow_fiber_sum_pow` — the radix-`d` descent
  sums: on a `μ_d`-closed set every fiber of `x ↦ x^d` is a FULL coset of size `d`, and
  `p_{d·j}(S) = d • p_j(S^d)` (generalizing `LamLeungTwoPow.pow_fiber_sum`, which is the
  `j = 1` case).
* `descended_window` — windows descend: vanishing `p_j(S)` for `1 ≤ j < d·w` gives
  vanishing `p_j(S^d)` for `1 ≤ j < w` (characteristic zero divides by `d`).
* `mixed_rung_conditional` — ONE RUNG: for `n = d·M`, window vanishing below `d·w` plus
  the level-`M` base case (hypothesis `hBase`) upgrades `μ_d`-closure to
  `μ_{p·d}`-closure.
* `prime_climb_conditional` — the rungs stacked by induction up one prime: `μ_{p^t}`-
  closure, conditional on the base-case family `hBase k` for `k < t`.
* `coprime_mu_closure_combine` — CRT welding: `μ_A`- and `μ_B`-closure for coprime
  `A, B` give `μ_{A·B}`-closure (characteristic-free, via `Nat.chineseRemainder`).
* `two_prime_tower_conditional` — **the conditional mixed-radix tower**: on `μ_n` with
  `p^a·q^b ∣ n`, the two climbs welded into `μ_{p^a·q^b}`-closure, every classical base
  case a named hypothesis.
* `base_case_level_one`, `base_case_window_ge_level` — unconditional discharges of the
  base-case hypothesis in the degenerate regimes (level 1; window longer than the level),
  witnessing satisfiability.
* `prime_power_tower` — **the skeleton closes when base cases exist**: plugging the
  proven Lam–Leung prime-power brick (`vanishing_sum_mu_p_closed`, copied below with
  provenance) into `prime_climb_conditional` yields the UNCONDITIONAL `p`-power tower for
  EVERY prime `p` — the generalization of `LamLeungTwoPow.full_tower` from `p = 2` to all
  primes, with the same window scale (`j < 2·p^{t-1}`, which at `p = 2` is `j < 2^t`).

## The base-case hypotheses, documented (what is known about each)

`hBase` (and the families `hBasep`/`hBaseq`) assert: every subset `T` of the `M`-th roots
of unity with `0 ∉ T` and vanishing power sums in the window `1 ≤ j < w` is closed under
multiplication by every `p`-th root of unity.

* **TRUE at prime-power levels** `M = p^(m+1)`, already at window `w = 2` (sum-only):
  this is Lam–Leung at prime powers, machine-checked as
  `LamLeungTwoPow.vanishing_sum_mu_p_closed` (DISPROOF_LOG O66) and copied below; the
  in-file `prime_power_tower` discharges the whole family this way on pure `p`-power
  domains.
* **FALSE at genuinely two-prime levels in the sum-only form** (`w = 2`): a rotated full
  `μ_q`-packet inside `μ_{pq}` has vanishing sum but is NOT `μ_p`-closed (the `μ_3`-packet
  at `n = 6` is not `μ_2`-closed — the O70 refutation in DISPROOF_LOG). This is why the
  skeleton carries the WINDOW PARAMETER `w`: the de Bruijn-derived true candidate needs
  the window to exceed the largest `p`-free divisor of `M` (killing pure-`q` packets), and
  numerically verified de Bruijn structure (O67: exhaustive at `n = 12, 18`) supports
  exactly that windowed form.
* **The open formalization target** is therefore: de Bruijn's theorem (Indag. Math. 1953;
  two-prime vanishing sums are ℕ-combinations of rotated prime packets), in the windowed
  closure form above. The in-tree route is the CRT double-slice engine
  (`CRTDoubleSlice.lean`, O70) + `LamLeungTwoPow.vanishing_coeff_slices` (O68); the
  remaining steps are the cyclotomic-irreducibility-over-`ℚ(ζ_{p^a})` discharge and the
  disjointness/positivity step (O70 entry, "What remains for full de Bruijn").

## Honest scope

Nothing here pins the two-prime tower unconditionally — that is exactly the de Bruijn
brick. What IS new and unconditional: the complete rung/climb/weld machinery at every
radix, and `prime_power_tower` (all-primes tower, previously only `p = 2` via
`full_tower`). All axiom-clean, 0 sorry.
-/

namespace MixedRadixTower

open Polynomial Finset

variable {F : Type*} [Field F]

/-! ## The generic mixed rung-assembly step (characteristic-free) -/

section PacketClosure

/-- **The mixed-radix packet-closure step**: if `S` is closed under the full `μ_d` and
its `d`-th-power image is closed under `μ_p`, then `S` is closed under `μ_{p·d}`.
Radix-`d` analogue of `LamLeungTwoPow.mu_double_closure` (which is `p = 2` with the
image-closure repackaged through `ω`), characteristic-free. -/
lemma mu_mul_closure [DecidableEq F] {S : Finset F} {d p : ℕ} (hd : 0 < d) (hp : 0 < p)
    (h0 : (0 : F) ∉ S)
    (hμ : ∀ x ∈ S, ∀ h : F, h ^ d = 1 → h * x ∈ S)
    (himg : ∀ y ∈ S.image (· ^ d), ∀ g : F, g ^ p = 1 → g * y ∈ S.image (· ^ d)) :
    ∀ x ∈ S, ∀ h : F, h ^ (p * d) = 1 → h * x ∈ S := by
  intro x hx h hh
  have hx0 : x ≠ 0 := fun hx' => h0 (hx' ▸ hx)
  have hpd : 0 < p * d := Nat.mul_pos hp hd
  have hh0 : h ≠ 0 := by
    intro h'
    rw [h', zero_pow hpd.ne'] at hh
    exact zero_ne_one hh
  have hg : (h ^ d) ^ p = 1 := by
    rw [← pow_mul, mul_comm d p]
    exact hh
  have hyim : (h * x) ^ d ∈ S.image (· ^ d) := by
    have hmem := himg (x ^ d) (Finset.mem_image.mpr ⟨x, hx, rfl⟩) (h ^ d) hg
    rw [mul_pow]
    exact hmem
  obtain ⟨x', hx', hx'd⟩ := Finset.mem_image.mp hyim
  have hhx0 : h * x ≠ 0 := mul_ne_zero hh0 hx0
  have hx'0 : x' ≠ 0 := by
    intro h'
    rw [h', zero_pow hd.ne'] at hx'd
    exact pow_ne_zero d hhx0 hx'd.symm
  have hq : ((h * x) / x') ^ d = 1 := by
    rw [div_pow, hx'd, div_self (pow_ne_zero d hhx0)]
  have hrw : h * x = ((h * x) / x') * x' := by
    field_simp
  rw [hrw]
  exact hμ x' hx' _ hq

end PacketClosure

/-! ## The radix-`d` descent sums: fibers are full cosets

Provenance: generalized from `LamLeungTwoPow.pow_fiber_sum` (which is the `j = 1` case of
`pow_fiber_sum_pow`); that file has no `.olean`, so the fiber-coset argument is reproved
here rather than imported. -/

section FiberCosets

variable [DecidableEq F]

/-- **Fibers are full cosets**: on a `μ_d`-closed set, the fiber of `x ↦ x^d` over
`x₀^d` is exactly the coset `x₀·μ_d`. -/
lemma pow_fiber_coset {S : Finset F} {d : ℕ} {ξ : F} (hξ : IsPrimitiveRoot ξ d)
    (hd : 0 < d) (h0 : (0 : F) ∉ S)
    (hμ : ∀ x ∈ S, ∀ h : F, h ^ d = 1 → h * x ∈ S) {x₀ : F} (hx₀ : x₀ ∈ S) :
    S.filter (fun x => x ^ d = x₀ ^ d) = (Finset.range d).image (fun i => ξ ^ i * x₀) := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have hx₀0 : x₀ ≠ 0 := fun h => h0 (h ▸ hx₀)
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨hxS, hxd⟩ := Finset.mem_filter.mp hx
    have hq : (x / x₀) ^ d = 1 := by
      rw [div_pow, hxd, div_self (pow_ne_zero d hx₀0)]
    obtain ⟨i, hi, hqi⟩ := hξ.eq_pow_of_pow_eq_one hq
    refine Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, ?_⟩
    rw [hqi]
    field_simp
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    have hξi : (ξ ^ i) ^ d = 1 := by
      rw [← pow_mul, mul_comm i d, pow_mul, hξ.pow_eq_one, one_pow]
    refine Finset.mem_filter.mpr ⟨hμ x₀ hx₀ _ hξi, ?_⟩
    rw [mul_pow, hξi, one_mul]

/-- Each fiber has exactly `d` elements. -/
lemma pow_fiber_card {S : Finset F} {d : ℕ} {ξ : F} (hξ : IsPrimitiveRoot ξ d)
    (hd : 0 < d) (h0 : (0 : F) ∉ S)
    (hμ : ∀ x ∈ S, ∀ h : F, h ^ d = 1 → h * x ∈ S) {x₀ : F} (hx₀ : x₀ ∈ S) :
    (S.filter (fun x => x ^ d = x₀ ^ d)).card = d := by
  have hx₀0 : x₀ ≠ 0 := fun h => h0 (h ▸ hx₀)
  rw [pow_fiber_coset hξ hd h0 hμ hx₀, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  have hpow : ξ ^ i = ξ ^ j := mul_right_cancel₀ hx₀0 hij
  exact hξ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hpow

/-- **The radix-`d` descent sum at every exponent**: closure under the full `μ_d` makes
every fiber of `x ↦ x^d` a full coset of size `d`, so `p_{d·j}(S) = d • p_j(S^d)`.
(`j = 1` is `LamLeungTwoPow.pow_fiber_sum`.) -/
lemma pow_fiber_sum_pow {S : Finset F} {d : ℕ} {ξ : F} (hξ : IsPrimitiveRoot ξ d)
    (hd : 0 < d) (h0 : (0 : F) ∉ S)
    (hμ : ∀ x ∈ S, ∀ h : F, h ^ d = 1 → h * x ∈ S) (j : ℕ) :
    ∑ x ∈ S, x ^ (d * j) = d • ∑ y ∈ S.image (· ^ d), y ^ j := by
  classical
  have hmaps : ∀ x ∈ S, x ^ d ∈ S.image (· ^ d) :=
    fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => x ^ (d * j)), Finset.smul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hy
  have hconst : ∀ x ∈ S.filter (fun x => x ^ d = x₀ ^ d), x ^ (d * j) = (x₀ ^ d) ^ j := by
    intro x hx
    have hxy : x ^ d = x₀ ^ d := (Finset.mem_filter.mp hx).2
    rw [pow_mul, hxy]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, pow_fiber_card hξ hd h0 hμ hx₀]

/-- **Windows descend through the `d`-th-power map** (characteristic zero): vanishing
power sums on `1 ≤ j < d·w` upstairs give vanishing power sums on `1 ≤ j < w` on the
`d`-th-power image. -/
lemma descended_window [CharZero F] {S : Finset F} {d : ℕ} {ξ : F}
    (hξ : IsPrimitiveRoot ξ d) (hd : 0 < d) (h0 : (0 : F) ∉ S)
    (hμ : ∀ x ∈ S, ∀ h : F, h ^ d = 1 → h * x ∈ S) {w : ℕ}
    (hwin : ∀ j, 1 ≤ j → j < d * w → ∑ x ∈ S, x ^ j = 0) :
    ∀ j, 1 ≤ j → j < w → ∑ y ∈ S.image (· ^ d), y ^ j = 0 := by
  intro j hj1 hj2
  have hfs := pow_fiber_sum_pow hξ hd h0 hμ j
  have hd1 : 1 ≤ d * j := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hd.ne' (by omega))
  have hdlt : d * j < d * w := by
    have h1 : d * (j + 1) ≤ d * w := Nat.mul_le_mul (le_refl d) (by omega)
    have h2 : d * (j + 1) = d * j + d := by ring
    omega
  have hz := hwin (d * j) hd1 hdlt
  rw [hz, nsmul_eq_mul] at hfs
  have hdF : ((d : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rcases mul_eq_zero.mp hfs.symm with h | h
  · exact absurd h hdF
  · exact h

end FiberCosets

/-! ## One rung of the mixed tower, conditional on the level base case -/

section Rung

/-- **The conditional mixed rung**: let `n = d·M` and let `S ⊆ μ_n` (`0 ∉ S`) be closed
under `μ_d` with power sums vanishing on `1 ≤ j < d·w`. Given the level-`M` base case
`hBase` — every windowed-vanishing subset of `μ_M` is `μ_p`-closed — `S` is closed under
`μ_{p·d}`.

`hBase` is the named classical import (see the file docstring): TRUE with `w = 2` when
`M` is a power of `p` (Lam–Leung, `vanishing_sum_mu_p_closed` below); at genuinely
two-prime `M` it is the windowed de Bruijn statement, FALSE for `w = 2` (rotated
`μ_q`-packet) and the open formalization target for
`w > (largest p-free divisor of M)`. -/
theorem mixed_rung_conditional [DecidableEq F] [CharZero F] {S : Finset F}
    {n d M p w : ℕ} (hd : 0 < d) (hp : 0 < p) (hn : n = d * M)
    {ξ : F} (hξ : IsPrimitiveRoot ξ d)
    (h0 : (0 : F) ∉ S) (hS : ∀ x ∈ S, x ^ n = 1)
    (hμ : ∀ x ∈ S, ∀ h : F, h ^ d = 1 → h * x ∈ S)
    (hwin : ∀ j, 1 ≤ j → j < d * w → ∑ x ∈ S, x ^ j = 0)
    (hBase : ∀ T : Finset F, (0 : F) ∉ T → (∀ y ∈ T, y ^ M = 1) →
      (∀ j, 1 ≤ j → j < w → ∑ y ∈ T, y ^ j = 0) →
      ∀ y ∈ T, ∀ g : F, g ^ p = 1 → g * y ∈ T) :
    ∀ x ∈ S, ∀ h : F, h ^ (p * d) = 1 → h * x ∈ S := by
  have h0img : (0 : F) ∉ S.image (· ^ d) := by
    intro hmem
    obtain ⟨x, hx, hxd⟩ := Finset.mem_image.mp hmem
    have hx0 : x ≠ 0 := fun h' => h0 (h' ▸ hx)
    exact pow_ne_zero d hx0 hxd
  have hroots : ∀ y ∈ S.image (· ^ d), y ^ M = 1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [← pow_mul, ← hn]
    exact hS x hx
  have himg := hBase (S.image (· ^ d)) h0img hroots
    (descended_window hξ hd h0 hμ hwin)
  exact mu_mul_closure hd hp h0 hμ himg

end Rung

/-! ## The climb: rungs stacked up one prime by induction -/

section Climb

/-- **The conditional prime climb**: stacking `mixed_rung_conditional` by induction.
For `p^t ∣ n`, a subset of `μ_n` whose power-sum windows cover `j < p^k·(w k)` for each
rung `k < t` is closed under `μ_{p^t}` — conditional on the base-case family
`hBase k` (the level-`n/p^k` de Bruijn/packet-closure statement, one per rung; each is
documented at `mixed_rung_conditional`). This is the strong-induction assembly of the
mixed tower along one prime. -/
theorem prime_climb_conditional [DecidableEq F] [CharZero F] {S : Finset F}
    {n p : ℕ} (hp : 0 < p) (hn : 0 < n)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (h0 : (0 : F) ∉ S) (hS : ∀ x ∈ S, x ^ n = 1) (w : ℕ → ℕ) :
    ∀ t, p ^ t ∣ n →
      (∀ k < t, ∀ j, 1 ≤ j → j < p ^ k * w k → ∑ x ∈ S, x ^ j = 0) →
      (∀ k < t, ∀ T : Finset F, (0 : F) ∉ T → (∀ y ∈ T, y ^ (n / p ^ k) = 1) →
        (∀ j, 1 ≤ j → j < w k → ∑ y ∈ T, y ^ j = 0) →
        ∀ y ∈ T, ∀ g : F, g ^ p = 1 → g * y ∈ T) →
      ∀ x ∈ S, ∀ h : F, h ^ (p ^ t) = 1 → h * x ∈ S := by
  intro t
  induction t with
  | zero =>
    intro _ _ _ x hx h hh
    rw [pow_zero, pow_one] at hh
    rw [hh, one_mul]
    exact hx
  | succ k ih =>
    intro hdvd hwin hBase
    have hdvdk : p ^ k ∣ n := dvd_trans (pow_dvd_pow p (Nat.le_succ k)) hdvd
    have hμ := ih hdvdk (fun k' hk' => hwin k' (Nat.lt_succ_of_lt hk'))
      (fun k' hk' => hBase k' (Nat.lt_succ_of_lt hk'))
    have hdpos : 0 < p ^ k := pow_pos hp k
    have hξ : IsPrimitiveRoot (ζ ^ (n / p ^ k)) (p ^ k) :=
      hζ.pow hn (Nat.div_mul_cancel hdvdk).symm
    have hrung := mixed_rung_conditional (n := n) (d := p ^ k) (M := n / p ^ k)
      (p := p) (w := w k) hdpos hp (Nat.mul_div_cancel' hdvdk).symm hξ h0 hS hμ
      (hwin k (Nat.lt_succ_self k)) (hBase k (Nat.lt_succ_self k))
    intro x hx h hh
    exact hrung x hx h (by rw [show p * p ^ k = p ^ (k + 1) from by
      rw [pow_succ, Nat.mul_comm]]; exact hh)

end Climb

/-! ## The CRT weld: coprime closures combine (characteristic-free) -/

section CoprimeCombine

/-- **The coprime weld**: closure under `μ_A` and under `μ_B` for coprime `A, B`
combine into closure under `μ_{A·B}`. Mechanism: CRT exponents `e₁ ≡ (1,0)`,
`e₂ ≡ (0,1)` mod `(A,B)` split any `h ∈ μ_{A·B}` as `h = h^{e₁}·h^{e₂}` with
`h^{e₁} ∈ μ_A`, `h^{e₂} ∈ μ_B`. -/
lemma coprime_mu_closure_combine {S : Finset F} {A B : ℕ}
    (hco : Nat.Coprime A B)
    (hclA : ∀ x ∈ S, ∀ h : F, h ^ A = 1 → h * x ∈ S)
    (hclB : ∀ x ∈ S, ∀ h : F, h ^ B = 1 → h * x ∈ S) :
    ∀ x ∈ S, ∀ h : F, h ^ (A * B) = 1 → h * x ∈ S := by
  intro x hx h hh
  by_cases hAB1 : A * B ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hAB1 with h0' | h1'
    · rcases Nat.mul_eq_zero.mp h0' with hA0 | hB0
      · subst hA0
        exact hclA x hx h (pow_zero h)
      · subst hB0
        exact hclB x hx h (pow_zero h)
    · rw [h1', pow_one] at hh
      rw [hh, one_mul]
      exact hx
  · push Not at hAB1
    obtain ⟨e₁, he₁A, he₁B⟩ := Nat.chineseRemainder hco 1 0
    obtain ⟨e₂, he₂A, he₂B⟩ := Nat.chineseRemainder hco 0 1
    have hBdvd : B ∣ e₁ := (Nat.modEq_zero_iff_dvd).mp he₁B
    have hAdvd : A ∣ e₂ := (Nat.modEq_zero_iff_dvd).mp he₂A
    have hμA : (h ^ e₁) ^ A = 1 := by
      obtain ⟨m, hm⟩ := hBdvd
      rw [← pow_mul, hm, show B * m * A = A * B * m from by ring, pow_mul, hh, one_pow]
    have hμB : (h ^ e₂) ^ B = 1 := by
      obtain ⟨m, hm⟩ := hAdvd
      rw [← pow_mul, hm, show A * m * B = A * B * m from by ring, pow_mul, hh, one_pow]
    have hmodA : e₁ + e₂ ≡ 1 [MOD A] := by simpa using he₁A.add he₂A
    have hmodB : e₁ + e₂ ≡ 1 [MOD B] := by simpa using he₁B.add he₂B
    have hmodAB : e₁ + e₂ ≡ 1 [MOD A * B] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hco).mp ⟨hmodA, hmodB⟩
    have hmod1 : (e₁ + e₂) % (A * B) = 1 := by
      have h' : (e₁ + e₂) % (A * B) = 1 % (A * B) := hmodAB
      rwa [Nat.mod_eq_of_lt hAB1] at h'
    have hsplit : e₁ + e₂ = A * B * ((e₁ + e₂) / (A * B)) + 1 := by
      conv_lhs => rw [← Nat.div_add_mod (e₁ + e₂) (A * B)]
      rw [hmod1]
    have hpow : h ^ (e₁ + e₂) = h := by
      rw [hsplit, pow_add, pow_mul, hh, one_pow, one_mul, pow_one]
    have hstep := hclA (h ^ e₂ * x) (hclB x hx (h ^ e₂) hμB) (h ^ e₁) hμA
    rwa [← mul_assoc, ← pow_add, hpow] at hstep

end CoprimeCombine

/-! ## THE CONDITIONAL TWO-PRIME TOWER -/

section TwoPrimeTower

/-- **The conditional mixed-radix (two-prime) tower theorem**: on a domain of `n`-th
roots of unity with `p^a·q^b ∣ n` (`p, q` coprime — the intended instance is two distinct
primes, e.g. M31-style `n = 2^a·3^b`), a subset `S` (`0 ∉ S`) whose power-sum windows
cover every rung of both climbs is closed under the FULL `μ_{p^a·q^b}` — i.e. `S` is a
union of `μ_{p^a q^b}`-cosets — CONDITIONAL on the named classical base cases:

* `hBasep k` (`k < a`): the de Bruijn/packet-closure statement at level `n/p^k` for the
  prime `p`, with window `wp k`;
* `hBaseq k` (`k < b`): the same at level `n/q^k` for the prime `q`, window `wq k`.

Each base case is documented at `mixed_rung_conditional` and in the file docstring:
prime-power levels are PROVEN (`vanishing_sum_mu_p_closed`), genuinely two-prime levels
are the open de Bruijn brick (windowed form — the sum-only form is refuted). This
theorem stands to the de Bruijn brick exactly as `TopLine.t2_tower_resolution` stood to
`LamLeungTwoPow.vanishing_sum_antipodal` before O50 landed. -/
theorem two_prime_tower_conditional [DecidableEq F] [CharZero F] {S : Finset F}
    {n p q a b : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q)
    (hn : 0 < n) (hdvd : p ^ a * q ^ b ∣ n)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (h0 : (0 : F) ∉ S) (hS : ∀ x ∈ S, x ^ n = 1)
    (wp wq : ℕ → ℕ)
    (hwinp : ∀ k < a, ∀ j, 1 ≤ j → j < p ^ k * wp k → ∑ x ∈ S, x ^ j = 0)
    (hBasep : ∀ k < a, ∀ T : Finset F, (0 : F) ∉ T → (∀ y ∈ T, y ^ (n / p ^ k) = 1) →
      (∀ j, 1 ≤ j → j < wp k → ∑ y ∈ T, y ^ j = 0) →
      ∀ y ∈ T, ∀ g : F, g ^ p = 1 → g * y ∈ T)
    (hwinq : ∀ k < b, ∀ j, 1 ≤ j → j < q ^ k * wq k → ∑ x ∈ S, x ^ j = 0)
    (hBaseq : ∀ k < b, ∀ T : Finset F, (0 : F) ∉ T → (∀ y ∈ T, y ^ (n / q ^ k) = 1) →
      (∀ j, 1 ≤ j → j < wq k → ∑ y ∈ T, y ^ j = 0) →
      ∀ y ∈ T, ∀ g : F, g ^ q = 1 → g * y ∈ T) :
    ∀ x ∈ S, ∀ h : F, h ^ (p ^ a * q ^ b) = 1 → h * x ∈ S := by
  have hclp := prime_climb_conditional hp hn hζ h0 hS wp a
    (dvd_trans (dvd_mul_right _ _) hdvd) hwinp hBasep
  have hclq := prime_climb_conditional hq hn hζ h0 hS wq b
    (dvd_trans (dvd_mul_left _ _) hdvd) hwinq hBaseq
  have hcop : Nat.Coprime (p ^ a) (q ^ b) := Nat.Coprime.pow a b hpq
  exact coprime_mu_closure_combine hcop hclp hclq

end TwoPrimeTower

/-! ## Unconditional discharges of the base-case hypothesis (degenerate regimes)

These witness that the `hBase` hypothesis family is satisfiable — they are NOT the de
Bruijn content (which lives at window `≤` level), but they pin down the trivial sectors:
level `1`, and any level shorter than its window (where the window forces emptiness, the
`v ≡ 1` instance of `LamLeungTwoPow.window_forces_weight`, reproved here from the
importable `TopLine.loc` toolkit with the window starting at `j = 1`). -/

section BaseCaseDischarges

/-- A torsion subset has at most `M` elements (it sits inside the `M`-th roots). -/
lemma card_le_of_torsion {T : Finset F} {M : ℕ} (hM : 0 < M)
    (h : ∀ y ∈ T, y ^ M = 1) : T.card ≤ M := by
  classical
  have hsub : T ⊆ (Polynomial.nthRoots M (1 : F)).toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hM]
    exact h y hy
  calc T.card ≤ (Polynomial.nthRoots M (1 : F)).toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (Polynomial.nthRoots M (1 : F)) := Multiset.toFinset_card_le _
    _ ≤ M := Polynomial.card_nthRoots M 1

/-- **Windows starting at `j = 1` force emptiness** on `0`-free sets no larger than the
window: the `1 ≤ j ≤ t` power-sum window has trivial kernel on `≤ t` distinct nonzero
points (pair against `X·loc(T \ {y₀})`, whose constant coefficient vanishes).
Provenance: the `v ≡ 1`, shifted-window variant of
`LamLeungTwoPow.window_forces_weight`. -/
lemma window_forces_empty [DecidableEq F] {T : Finset F} {t : ℕ} (h0 : (0 : F) ∉ T)
    (hcard : T.card ≤ t)
    (hwin : ∀ j, 1 ≤ j → j ≤ t → ∑ y ∈ T, y ^ j = 0) :
    T = ∅ := by
  by_contra hne
  obtain ⟨y₀, hy₀⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  set P : F[X] := Polynomial.X * TopLine.loc (T.erase y₀) with hP
  have hcard1 : 1 ≤ T.card := Finset.card_pos.mpr ⟨y₀, hy₀⟩
  have hloc0 : TopLine.loc (T.erase y₀) ≠ 0 := (TopLine.loc_monic _).ne_zero
  have hdegP : P.natDegree ≤ t := by
    rw [hP, Polynomial.natDegree_mul Polynomial.X_ne_zero hloc0,
      Polynomial.natDegree_X, TopLine.loc_natDegree, Finset.card_erase_of_mem hy₀]
    omega
  have hcoeff0 : P.coeff 0 = 0 := by
    rw [hP, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul]
  have hpair : ∑ y ∈ T, P.eval y = 0 := by
    have hev : ∀ y ∈ T, P.eval y = ∑ j ∈ Finset.range (t + 1), P.coeff j * y ^ j := by
      intro y _
      exact Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdegP) y
    rw [Finset.sum_congr rfl hev, Finset.sum_comm]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hjr := Finset.mem_range.mp hj
    by_cases hj0 : j = 0
    · subst hj0
      exact Finset.sum_eq_zero fun y _ => by rw [hcoeff0, zero_mul]
    · rw [← Finset.mul_sum, hwin j (by omega) (by omega), mul_zero]
  have hkill : ∀ y ∈ T, y ≠ y₀ → P.eval y = 0 := by
    intro y hy hyne
    rw [hP, Polynomial.eval_mul,
      TopLine.loc_eval_zero (Finset.mem_erase.mpr ⟨hyne, hy⟩), mul_zero]
  rw [← Finset.add_sum_erase _ _ hy₀] at hpair
  rw [Finset.sum_eq_zero (fun y hy => hkill y (Finset.mem_of_mem_erase hy)
    (Finset.ne_of_mem_erase hy)), add_zero] at hpair
  have hy₀0 : y₀ ≠ 0 := fun h => h0 (h ▸ hy₀)
  have hPy₀ : P.eval y₀ ≠ 0 := by
    rw [hP, Polynomial.eval_mul, Polynomial.eval_X]
    exact mul_ne_zero hy₀0 (TopLine.loc_eval_ne_zero (Finset.notMem_erase y₀ T))
  exact hPy₀ hpair

/-- The base-case hypothesis holds unconditionally at level `M = 1` (any window `≥ 2`):
the only candidate subset `{1}` has nonzero sum. -/
lemma base_case_level_one {p w : ℕ} (hw : 2 ≤ w) :
    ∀ T : Finset F, (0 : F) ∉ T → (∀ y ∈ T, y ^ 1 = 1) →
      (∀ j, 1 ≤ j → j < w → ∑ y ∈ T, y ^ j = 0) →
      ∀ y ∈ T, ∀ g : F, g ^ p = 1 → g * y ∈ T := by
  intro T _ hT hwin y hy _ _
  have hy1 : ∀ z ∈ T, z = 1 := fun z hz => by
    have := hT z hz
    rwa [pow_one] at this
  have hTsub : T ⊆ {1} := fun z hz => Finset.mem_singleton.mpr (hy1 z hz)
  have h1T : (1 : F) ∈ T := hy1 y hy ▸ hy
  have hT1 : T = {1} :=
    Finset.Subset.antisymm hTsub (Finset.singleton_subset_iff.mpr h1T)
  have hsum := hwin 1 le_rfl (by omega)
  rw [hT1, Finset.sum_singleton, pow_one] at hsum
  exact absurd hsum one_ne_zero

/-- The base-case hypothesis holds unconditionally whenever the window is longer than
the level (`w > M`): the window then forces `T = ∅`. The genuine de Bruijn regime is
`w ≤ M`. -/
lemma base_case_window_ge_level [DecidableEq F] {M p w : ℕ} (hM : 0 < M) (hw : M < w) :
    ∀ T : Finset F, (0 : F) ∉ T → (∀ y ∈ T, y ^ M = 1) →
      (∀ j, 1 ≤ j → j < w → ∑ y ∈ T, y ^ j = 0) →
      ∀ y ∈ T, ∀ g : F, g ^ p = 1 → g * y ∈ T := by
  intro T h0T hroots hwin y hy _ _
  have hT : T = ∅ :=
    window_forces_empty h0T (card_le_of_torsion hM hroots)
      (fun j hj1 hj2 => hwin j hj1 (by omega))
  rw [hT] at hy
  exact absurd hy (Finset.notMem_empty y)

end BaseCaseDischarges

/-! ## Lam–Leung at prime powers (the proven base case)

The sparse packet coefficient calculation is shared with the CRT double-slice layer via
`CRTDoubleSlice.packet_slice_coeff`; the closure theorem below packages the resulting
prime-power Lam–Leung base case in the form consumed by the mixed-radix tower. -/

section PrimePowerBase

/-- Slices of a geometric-packet multiple: if `deg R < q` then
`(Σ_{i<p} X^{iq} · R).coeff (iq + s) = R.coeff s` for `i < p`, `s < q`.
(Wrapper around `CRTDoubleSlice.packet_slice_coeff`.) -/
lemma packet_mul_coeff {p q : ℕ} (_hq : 0 < q) {R : ℚ[X]} (hR : R.natDegree < q)
    {i s : ℕ} (hi : i < p) (hs : s < q) :
    ((∑ i ∈ Finset.range p, (Polynomial.X : ℚ[X]) ^ (i * q)) * R).coeff (i * q + s)
      = R.coeff s := by
  exact CRTDoubleSlice.packet_slice_coeff (K := ℚ) (p := p) (q := q) (R := R)
    hR hi hs

/-- **Lam–Leung at prime powers**: in characteristic zero, a finite set of `p^(m+1)`-th
roots of unity with vanishing sum is closed under multiplication by every `p`-th root of
unity. (Provenance: `LamLeungTwoPow.vanishing_sum_mu_p_closed`, verbatim; DISPROOF_LOG
O66.) -/
theorem vanishing_sum_mu_p_closed [CharZero F] {p m : ℕ} (hp : p.Prime) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (p ^ (m + 1)))
    {S : Finset F} (hS : ∀ x ∈ S, x ^ (p ^ (m + 1)) = 1)
    (hsum : ∑ x ∈ S, x = 0) :
    ∀ x ∈ S, ∀ h : F, h ^ p = 1 → h * x ∈ S := by
  classical
  set n := p ^ (m + 1) with hn
  set q := p ^ m with hq
  have hppos : 0 < p := hp.pos
  have hqpos : 0 < q := by positivity
  have hnq : n = p * q := by rw [hn, hq]; ring
  have hnpos : 0 < n := by rw [hn]; positivity
  haveI : NeZero n := ⟨hnpos.ne'⟩
  haveI : NeZero p := ⟨hppos.ne'⟩
  -- exponent set and indicator polynomial
  set I : Finset ℕ := (Finset.range n).filter (fun i => ζ ^ i ∈ S) with hI
  set P : ℚ[X] := ∑ i ∈ I, X ^ i with hP
  have hPcoeff : ∀ j, P.coeff j = if j ∈ I then 1 else 0 := by
    intro j
    rw [hP, Polynomial.finset_sum_coeff]
    rw [Finset.sum_congr rfl (fun i _ => Polynomial.coeff_X_pow i j)]
    rw [Finset.sum_ite_eq I j (fun _ => (1 : ℚ))]
  have hPζ : Polynomial.aeval ζ P = 0 := by
    rw [hP, map_sum]
    have hterm : ∀ i ∈ I, Polynomial.aeval ζ ((X : ℚ[X]) ^ i) = ζ ^ i := by
      intro i _
      simp
    rw [Finset.sum_congr rfl hterm, ← hsum]
    apply Finset.sum_bij (fun i _ => ζ ^ i)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i hi j hj hij
      exact hζ.pow_inj (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) hij
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := hζ.eq_pow_of_pow_eq_one (hS x hx)
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hxi.symm ▸ hx⟩, hxi⟩
    · intro i _
      rfl
  -- the cyclotomic packet divides P
  have hdvd : (∑ i ∈ Finset.range p, (X : ℚ[X]) ^ (i * q)) ∣ P := by
    have hmin := minpoly.dvd ℚ ζ hPζ
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hζ (by positivity)] at hmin
    have hcyc : Polynomial.cyclotomic (p ^ (m + 1)) ℚ
        = ∑ i ∈ Finset.range p, (X : ℚ[X]) ^ (i * q) := by
      rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hp]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← pow_mul, hq, mul_comm]
    rwa [hn, hcyc] at hmin
  -- slice equality: P.coeff (i·q + s) is independent of i < p
  have hslice : ∀ s < q, ∀ i < p, ∀ i' < p,
      P.coeff (i * q + s) = P.coeff (i' * q + s) := by
    obtain ⟨R, hR⟩ := hdvd
    by_cases hP0 : P = 0
    · intro s _ i _ i' _
      simp [hP0]
    have hG : (∑ i ∈ Finset.range p, (X : ℚ[X]) ^ (i * q)) ≠ 0 := by
      intro h
      have := congrArg (fun Q : ℚ[X] => Q.coeff 0) h
      simp only [Polynomial.finset_sum_coeff] at this
      rw [Finset.sum_eq_single 0 (fun j _ hj => by
        rw [Polynomial.coeff_X_pow]
        rw [if_neg (by
          intro h0
          rcases Nat.mul_eq_zero.mp h0.symm with h | h
          · exact hj h
          · omega)]) (fun h0 => absurd (Finset.mem_range.mpr hppos) h0)] at this
      simp at this
    have hR0 : R ≠ 0 := fun h => hP0 (by rw [hR, h, mul_zero])
    have hdegP : P.natDegree < n := by
      rw [hP]
      have hle : (∑ i ∈ I, (X : ℚ[X]) ^ i).natDegree ≤ n - 1 :=
        Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => by
          rw [Polynomial.natDegree_X_pow]
          have := Finset.mem_range.mp (Finset.mem_filter.mp (hI ▸ hi)).1
          omega
      omega
    have hdegR : R.natDegree < q := by
      have hmul := Polynomial.natDegree_mul hG hR0
      rw [← hR] at hmul
      have hGlow : (p - 1) * q
          ≤ (∑ i ∈ Finset.range p, (X : ℚ[X]) ^ (i * q)).natDegree := by
        apply Polynomial.le_natDegree_of_ne_zero
        rw [Polynomial.finset_sum_coeff]
        rw [Finset.sum_eq_single (p - 1) (fun j hj hjne => by
          rw [Polynomial.coeff_X_pow, if_neg (fun h => hjne (by
            have := Nat.eq_of_mul_eq_mul_right hqpos h
            omega))]) (fun h0 => absurd (Finset.mem_range.mpr (by omega)) h0)]
        rw [Polynomial.coeff_X_pow, if_pos rfl]
        norm_num
      have hcount : (p - 1) * q + q = n := by
        rw [hnq]
        calc (p - 1) * q + q = ((p - 1) + 1) * q := by ring
        _ = p * q := by congr 1; omega
      omega
    intro s hs i hi i' hi'
    rw [hR, packet_mul_coeff hqpos hdegR hi hs, packet_mul_coeff hqpos hdegR hi' hs]
  -- conclusion: membership is q-shift invariant; μ_p = powers of ζ^q
  have hmem : ∀ s < q, ∀ i < p, ∀ i' < p,
      (ζ ^ (i * q + s) ∈ S ↔ ζ ^ (i' * q + s) ∈ S) := by
    intro s hs i hi i' hi'
    have := hslice s hs i hi i' hi'
    rw [hPcoeff, hPcoeff] at this
    have hiI : (i * q + s ∈ I) ↔ (i' * q + s ∈ I) := by
      by_cases h1 : i * q + s ∈ I <;> by_cases h2 : i' * q + s ∈ I <;>
        simp [h1, h2] at this ⊢
    rw [hI] at hiI
    simp only [Finset.mem_filter, Finset.mem_range] at hiI
    have hb1 : i * q + s < n := by
      rw [hnq]
      have : (i + 1) * q ≤ p * q := Nat.mul_le_mul_right q (by omega)
      have : i * q + q ≤ p * q := by
        calc i * q + q = (i + 1) * q := by ring
        _ ≤ p * q := this
      omega
    have hb2 : i' * q + s < n := by
      rw [hnq]
      have h' : (i' + 1) * q ≤ p * q := Nat.mul_le_mul_right q (by omega)
      have : i' * q + q ≤ p * q := by
        calc i' * q + q = (i' + 1) * q := by ring
        _ ≤ p * q := h'
      omega
    constructor
    · intro hx
      exact (hiI.mp ⟨hb1, hx⟩).2
    · intro hx
      exact (hiI.mpr ⟨hb2, hx⟩).2
  -- assemble: h with h^p = 1 is (ζ^q)^k; shift the coset index
  intro x hx h hh
  obtain ⟨e, he, rfl⟩ := hζ.eq_pow_of_pow_eq_one (hS x hx)
  have hζq : IsPrimitiveRoot (ζ ^ q) p := by
    refine hζ.pow hnpos ?_
    rw [hn, hq]
    ring
  obtain ⟨k, hk, hkq⟩ := hζq.eq_pow_of_pow_eq_one hh
  obtain ⟨i, s, rfl, hs⟩ : ∃ i s, e = i * q + s ∧ s < q :=
    ⟨e / q, e % q, by rw [mul_comm]; exact (Nat.div_add_mod e q).symm, Nat.mod_lt _ hqpos⟩
  have hi : i < p := by
    by_contra hge
    push Not at hge
    have : p * q ≤ i * q := Nat.mul_le_mul_right q hge
    rw [hnq] at he
    omega
  set i2 := (k + i) % p with hi2def
  have hi2p : i2 < p := Nat.mod_lt _ hppos
  have hxmem : ζ ^ (i2 * q + s) ∈ S := (hmem s hs i hi i2 hi2p).mp hx
  have hfinal : h * ζ ^ (i * q + s) = ζ ^ (i2 * q + s) := by
    rw [← hkq, ← pow_mul, ← pow_add]
    have hdecomp : q * k + (i * q + s) = n * ((k + i) / p) + (i2 * q + s) := by
      calc q * k + (i * q + s) = (k + i) * q + s := by ring
      _ = (p * ((k + i) / p) + i2) * q + s := by
          rw [hi2def]
          congr 2
          exact (Nat.div_add_mod (k + i) p).symm
      _ = (p * q) * ((k + i) / p) + (i2 * q + s) := by ring
      _ = n * ((k + i) / p) + (i2 * q + s) := by rw [hnq]
    rw [hdecomp, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  rw [hfinal]
  exact hxmem

end PrimePowerBase

/-! ## The skeleton CLOSES where base cases exist: the all-primes prime-power tower

Plugging the proven Lam–Leung brick into the conditional climb yields the UNCONDITIONAL
tower on pure `p`-power domains for EVERY prime `p` — the generalization of
`LamLeungTwoPow.full_tower` (`p = 2`) to all primes, at the same window scale:
`j < 2·p^{t-1}` specializes at `p = 2` to `j < 2^t`, exactly `full_tower`'s window. -/

section PrimePowerTower

/-- **The all-primes prime-power tower theorem** (unconditional, characteristic zero):
a finite set of `p^M`-th roots of unity whose power sums vanish for
`1 ≤ j < 2·p^(t-1)` (`t ≤ M`) is closed under multiplication by every `p^t`-th root of
unity — a union of `μ_{p^t}`-cosets. `p = 2` recovers `LamLeungTwoPow.full_tower`. -/
theorem prime_power_tower [DecidableEq F] [CharZero F] {p : ℕ} (hp : p.Prime) {M : ℕ}
    {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ M)) {S : Finset F}
    (hS : ∀ x ∈ S, x ^ (p ^ M) = 1) {t : ℕ} (htM : t ≤ M)
    (hwin : ∀ j, 1 ≤ j → j < 2 * p ^ (t - 1) → ∑ x ∈ S, x ^ j = 0) :
    ∀ x ∈ S, ∀ h : F, h ^ (p ^ t) = 1 → h * x ∈ S := by
  have hnpos : 0 < p ^ M := pow_pos hp.pos M
  have h0 : (0 : F) ∉ S := by
    intro h0S
    have h1 := hS 0 h0S
    rw [zero_pow hnpos.ne'] at h1
    exact one_ne_zero (α := F) h1.symm
  refine prime_climb_conditional hp.pos hnpos hζ h0 hS (fun _ => 2) t
    (pow_dvd_pow p htM) ?_ ?_
  · -- the rung windows are inside the single window `j < 2·p^(t-1)`
    intro k hk j hj1 hj2
    refine hwin j hj1 ?_
    have hk' : k ≤ t - 1 := by omega
    have hpk : p ^ k ≤ p ^ (t - 1) := Nat.pow_le_pow_right hp.pos hk'
    calc j < p ^ k * 2 := hj2
      _ = 2 * p ^ k := by ring
      _ ≤ 2 * p ^ (t - 1) := by omega
  · -- the base cases are Lam–Leung at prime powers, one level down per rung
    intro k hk T _ hroots hwinT
    have hkM : k < M := by omega
    have hMk : p ^ M / p ^ k = p ^ (M - k) := Nat.pow_div hkM.le hp.pos
    have hζk : IsPrimitiveRoot (ζ ^ (p ^ k)) (p ^ ((M - k - 1) + 1)) := by
      refine hζ.pow hnpos ?_
      rw [← pow_add]
      congr 1
      omega
    have hT : ∀ y ∈ T, y ^ (p ^ ((M - k - 1) + 1)) = 1 := by
      intro y hy
      have := hroots y hy
      rwa [hMk, show M - k = (M - k - 1) + 1 from by omega] at this
    have hsum : ∑ y ∈ T, y = 0 := by
      have := hwinT 1 le_rfl (by simp only []; omega)
      simpa using this
    exact vanishing_sum_mu_p_closed hp hζk hT hsum

end PrimePowerTower

end MixedRadixTower

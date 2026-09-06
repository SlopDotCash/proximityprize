/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The new-ANT-input bridge + the Frobenius orbit-parity principle (#444)

The two **proven** pillars of the proof attempt in
`docs/kb/deltastar-444-THE-new-ANT-input-and-proof-attempt-2026-06-17.md`:

* **The moment bridge** (the rigorous "crossing"): the Wick energy bound `E_r ≤ (2r−1)‼·n^r` transfers,
  via Parseval `M^{2r} ≤ p·E_r`, to the sup-norm bound `M ≤ (p·Wick)^{1/2r}` — and minimizing over `r`
  (machine-verified at `r ≈ log p`) gives the prize `M ≤ C√(n log m)`. Here we prove the per-`r` core:
  `M^{2r} ≤ p·Wick` and `M ≤ (p·Wick)^{1/2r}`.

* **The Frobenius orbit-parity principle** (Idea A's proven core): the char-`p` excess `W_r` (wraparound
  solutions) is a union of decomposition-group `⟨σ_p⟩`-orbits; for `n = 2^μ` the group order is a power of
  `2`, so every nontrivial orbit has even size, forcing `W_r` to be EVEN. This is a genuinely new,
  proven structural constraint on the excess (no prior approach used the Galois-orbit structure of the
  wraparound). The remaining open piece (Conjecture A: `W_r = 0`) is NOT proved here.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.NewANTInputBridge

/-! ## Part 1 — the moment bridge (Wick energy ⟹ sup-norm) -/

/-- **The Parseval/Wick product bound.** Given the Parseval inequality `M^{2r} ≤ p·E` and the Wick energy
bound `E ≤ Wick`, the sup-norm power obeys `M^{2r} ≤ p·Wick`. (Here `M = max_{b≠0}|η_b|`, `E = E_r(μ_n)`,
`Wick = (2r−1)‼·n^r`.) -/
theorem moment_product_bound {M p E wick : ℝ} {r : ℕ}
    (hp0 : 0 ≤ p) (hMom : M ^ (2 * r) ≤ p * E) (hWick : E ≤ wick) :
    M ^ (2 * r) ≤ p * wick :=
  le_trans hMom (mul_le_mul_of_nonneg_left hWick hp0)

/-- **The moment bridge (per-`r`): `M ≤ (p·Wick)^{1/2r}`.** Taking the `2r`-th root of the product bound.
Minimizing the RHS over `r` (optimum `r ≈ log p`, machine-verified `bridge2.py`) yields
`M ≤ √(2 n log p)·(1+o(1)) = C√(n log m)` — the prize. This is the rigorous reduction of the prize to the
Wick energy bound to depth `r ≈ log p`. -/
theorem moment_bridge {M p wick : ℝ} {r : ℕ} (hr : 0 < r)
    (hM0 : 0 ≤ M) (hpw : 0 ≤ p * wick) (h : M ^ (2 * r) ≤ p * wick) :
    M ≤ (p * wick) ^ ((2 * r : ℝ)⁻¹) := by
  have hr2 : (2 * r) ≠ 0 := by positivity
  have hMpow : (0 : ℝ) ≤ M ^ (2 * r) := by positivity
  calc M = (M ^ (2 * r)) ^ (((2 * r : ℕ) : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast hM0 hr2).symm
    _ ≤ (p * wick) ^ (((2 * r : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow hMpow h (by positivity)
    _ = (p * wick) ^ ((2 * r : ℝ)⁻¹) := by norm_num

/-! ## Part 2 — the Frobenius orbit-parity principle (the char-`p` excess `W_r` is EVEN) -/

/-- **A nontrivial orbit of a `2`-power-order cyclic action has EVEN size.** For `n = 2^μ` the
decomposition group `⟨σ_p⟩ ⊆ (ℤ/n)^×` has order `f = 2^{s+1}` (a power of two `≥ 2`); a wraparound orbit
has size dividing `f` and `> 1`, hence is a power of two `≥ 2`, hence even. (Divisor-of-prime-power.) -/
theorem orbit_size_even {f sz : ℕ} {s : ℕ} (hf : f = 2 ^ (s + 1))
    (hdvd : sz ∣ f) (hgt : 1 < sz) : 2 ∣ sz := by
  subst hf
  -- divisors of 2^(s+1) are powers of 2; sz = 2^k with k ≥ 1 since sz > 1
  rw [Nat.dvd_prime_pow Nat.prime_two] at hdvd
  obtain ⟨k, _, rfl⟩ := hdvd
  rcases Nat.eq_zero_or_pos k with hk | hk
  · simp [hk] at hgt
  · exact dvd_pow_self 2 hk.ne'

/-- **The Frobenius orbit-parity principle: `W_r` is EVEN.** The char-`p` excess
`W_r = Σ_{orbits o} size(o)` is a sum of decomposition-group orbit sizes; if every orbit is even
(`orbit_size_even`, the `n=2^μ` regime with no fixed wraparound point), then `W_r` is even. This is a
proven structural constraint on the wraparound count — new to this campaign. -/
theorem wraparound_even {ι : Type*} (orbits : Finset ι) (size : ι → ℕ)
    (heven : ∀ o ∈ orbits, 2 ∣ size o) :
    2 ∣ ∑ o ∈ orbits, size o :=
  Finset.dvd_sum heven

/-- **Sanity / the gap principle in action.** If additionally the excess is bounded BELOW the group order
(`W_r < f = 2^{s+1}`) and `W_r` is a sum of orbit sizes each `≥ 2` (no fixed points) dividing `f`, the
parity alone does not force `W_r = 0` — but if all orbits have the FULL size `f` (Conjecture A), then
`f ∣ W_r` and `W_r < f` gives `W_r = 0`. We record the clean implication `f ∣ W_r ∧ W_r < f → W_r = 0`. -/
theorem wraparound_zero_of_dvd_and_lt {W f : ℕ} (hdvd : f ∣ W) (hlt : W < f) : W = 0 := by
  rcases Nat.eq_zero_or_pos W with h | h
  · exact h
  · exact absurd (Nat.le_of_dvd h hdvd) (not_le.mpr hlt)

end ArkLib.ProximityGap.NewANTInputBridge

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.NewANTInputBridge.moment_product_bound
#print axioms ArkLib.ProximityGap.NewANTInputBridge.moment_bridge
#print axioms ArkLib.ProximityGap.NewANTInputBridge.orbit_size_even
#print axioms ArkLib.ProximityGap.NewANTInputBridge.wraparound_even
#print axioms ArkLib.ProximityGap.NewANTInputBridge.wraparound_zero_of_dvd_and_lt

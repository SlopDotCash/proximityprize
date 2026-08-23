/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SidonSubgroupClosed
import ArkLib.Data.CodingTheory.ProximityGap.RepCountSidonBound

/-!
# The Garcia–Voloch rep bound is unconditional for the small subgroup (#389)

Composing the small-subgroup Sidon pin (`sidonModNeg_mu_n`, `SidonSubgroupClosed.lean`) with the
conditional closure `gvRepBound_of_sidonModNeg` (`RepCountSidonBound.lean`) gives the
`GVRepBound` — the representation bound the *entire* proximity-gap supply chain consumes —
**unconditionally** and **fully instantiated** on the actual `n`-th-roots Finset, with no abstract
`hGmem`/`hcard`/`SidonModNeg` hypotheses left for the caller: it follows purely from `p > 2^n`.

This closes the supply side of the δ* programme in the small-subgroup regime `n < log₂ p` with no
Weil, no Stepanov, no open conjecture.  (The deployed prize `n ≫ log₂ p` and the window-interior
prize remain the recognized open problems; see `SidonSubgroupClosed.lean`.)  Axiom-clean.
-/

open Polynomial
open ArkLib.ProximityGap.AdditiveEnergyRepBound

namespace ArkLib.ProximityGap.AdditiveEnergySidonModNeg

/-- **The Garcia–Voloch rep bound closes unconditionally for the small subgroup.** For `n = 2^m`
(`m ≥ 1`), a prime `p > 2^n`, a primitive `n`-th root `ω ∈ ZMod p`, and any `M` with `3n ≤ M²` and
`M³ ≤ 64n²` (e.g. `M = ⌈√(3n)⌉ = O(√n)`), the actual `n`-th-roots Finset satisfies `GVRepBound`.
This is the rep bound the entire proximity-gap supply chain consumes, instantiated with NO abstract
hypotheses — purely from `p > 2^n` (the small-subgroup Sidon pin `sidonModNeg_mu_n`). -/
theorem gvRepBound_nthRoots {p : ℕ} [Fact p.Prime] {n m M : ℕ} (hn2 : n = 2 ^ m) (hm : 1 ≤ m)
    (hp : 2 ^ n < p) {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    (hM : 3 * n ≤ M ^ 2) (hM3 : M ^ 3 ≤ 64 * n ^ 2) :
    GVRepBound (nthRootsFinset n (1 : ZMod p)) M := by
  have hn : n ≠ 0 := by rw [hn2]; positivity
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have h2n : 2 ≤ 2 ^ n :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hn))
  have hp2 : 2 < p := by omega
  have hGmem : ∀ z : ZMod p, z ∈ nthRootsFinset n (1 : ZMod p) ↔ z ^ n = 1 :=
    fun z => mem_nthRootsFinset hnpos 1
  have hcard : (nthRootsFinset n (1 : ZMod p)).card = n := hω.card_nthRootsFinset
  have h2F : (2 : ZMod p) ≠ 0 := by
    intro hcontra
    have hdvd : (p : ℕ) ∣ 2 := by
      rw [← ZMod.natCast_eq_zero_iff]; exact_mod_cast hcontra
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have h0 : (0 : ZMod p) ∉ nthRootsFinset n (1 : ZMod p) := by
    rw [hGmem]; simp [zero_pow hn]
  have hneg : ∀ x ∈ nthRootsFinset n (1 : ZMod p), -x ∈ nthRootsFinset n (1 : ZMod p) := by
    intro x hx
    rw [hGmem] at hx ⊢
    have he : Even n := by rw [hn2]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩
    rw [neg_pow, he.neg_one_pow, one_mul]; exact hx
  have hS := sidonModNeg_mu_n hn2 hm hp hω hGmem
  exact gvRepBound_of_sidonModNeg (Nat.one_le_iff_ne_zero.mpr hn) hGmem hcard h2F h0 hneg hS
    hM (by rw [hcard]; exact hM3)

end ArkLib.ProximityGap.AdditiveEnergySidonModNeg

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.gvRepBound_nthRoots

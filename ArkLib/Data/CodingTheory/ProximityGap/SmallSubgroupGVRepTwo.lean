/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountSidonBound
import ArkLib.Data.CodingTheory.ProximityGap.SidonModNegEnergyEquality

/-!
# WF2-C4 audit: the SHARP rep-two bound from `SidonModNeg` (the honest derivation of `M = 2`)

Issue #389.  Conjecture WF2-C4 claims `GVRepBound (μ_n) 2` (max representation count `≤ 2`)
for `n = 2^m` and almost all primes `p ≡ 1 (mod n)`, attributing the derivation to
"`C1` + the landed `gvRepBound_of_excess_le` / `repCount_sq_card_le_via_excess`" (the
**energy / coset-concentration** route).

**That attribution is mathematically wrong.**  The coset-concentration route only delivers
`n · r(c)² ≤ E(G) = 3n² − 3n`, hence `r(c)² ≤ 3n − 3`, i.e. `r(c) ≤ √(3n) = O(√n)`
(this is exactly the in-tree `gvRepBound_of_sidonModNeg`, `M = O(√n)`).  It can **never**
yield the constant `M = 2`: for `n = 32` it caps `r` only at `⌊√93⌋ = 9`.

The constant `M = 2` is a strictly **sharper** combinatorial fact, and it follows
**directly from the definition of `SidonModNeg`** (not from any energy count):
`SidonModNeg G` literally says that for `t ≠ 0` any two ordered representations
`a + b = t = c + d` coincide up to swap, i.e. `repCount G t ≤ 2`.

This file proves that honest derivation:

* `repCount_le_two_of_sidonModNeg` — `SidonModNeg G → ∀ t ≠ 0, repCount G t ≤ 2`
  (the sharp bound, from the definition; no energy, no `√n`).
* `gvRepBound_two_of_sidonModNeg` — hence `GVRepBound G 2` whenever `8 ≤ |G|`
  (the cube side `2³ = 8 ≤ 64·|G|²` is automatic for `|G| ≥ 1`).
* `mu_n_gvRepBound_two` — specialised to `μ_n ⊂ F_p` for `n = 2^m`, `m ≥ 1`, `p > 2^n`:
  `GVRepBound (μ_n) 2`, via the proven `mu_n_isSidonModNeg`.

**Verdict on WF2-C4.**  The *conclusion* (`M = 2` for `p` such that `μ_n` is Sidon-mod-neg)
is TRUE and here proven axiom-clean; the conjecture's *stated derivation* (via the energy /
coset-concentration lemmas) is FALSE and is replaced by the correct one.  The "almost-all-p"
scope is genuine: `SidonModNeg(μ_n)` is proven only for the exponential window `p > 2^n`;
in the production boundary window `p ≈ n²` it is the open specific-prime cyclotomic-coincidence
predicate, with confirmed sporadic large failures (e.g. `p = 21523361` for `n = 32`).

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.WF2SidonRepTwo

open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg
open ArkLib.ProximityGap.EnergyEqualitySidonModNeg

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The sharp rep-two bound — the HONEST derivation of `M = 2`.**
`SidonModNeg G` *says*, for `t ≠ 0`, that any two ordered pairs in `G` summing to `t`
coincide up to swap.  So the filter set `{y ∈ G : t − y ∈ G}` (whose card is `repCount`)
is contained in `{y₀, t − y₀}` for any one of its members `y₀`, hence has `≤ 2` elements.
No energy / coset-concentration is used — that route only gives `r ≤ √(3n)`. -/
theorem repCount_le_two_of_sidonModNeg {G : Finset F} (hS : SidonModNeg G)
    {t : F} (ht : t ≠ 0) : repCount G t ≤ 2 := by
  classical
  unfold repCount
  set S : Finset F := G.filter (fun y => t - y ∈ G) with hSdef
  -- Each `y ∈ S` gives a pair `(y, t - y)` in `G × G` summing to `t`.
  -- Membership unpacking.
  have hmem : ∀ y ∈ S, y ∈ G ∧ (t - y) ∈ G := by
    intro y hy
    rw [hSdef, mem_filter] at hy
    exact hy
  -- If `S` is empty its card is `0 ≤ 2`.
  rcases S.eq_empty_or_nonempty with hempty | ⟨y₀, hy₀⟩
  · simp [hempty]
  · -- Fix a witness `y₀ ∈ S`.  Show `S ⊆ {y₀, t - y₀}`.
    obtain ⟨hy₀G, hty₀G⟩ := hmem y₀ hy₀
    have hsub : S ⊆ {y₀, t - y₀} := by
      intro y hy
      obtain ⟨hyG, htyG⟩ := hmem y hy
      -- `y + (t − y) = t = y₀ + (t − y₀)`; apply `SidonModNeg`.
      have hsum : y + (t - y) = y₀ + (t - y₀) := by ring
      have hcase := hS y hyG (t - y) htyG y₀ hy₀G (t - y₀) hty₀G hsum
      have htne : y + (t - y) ≠ 0 := by
        have : y + (t - y) = t := by ring
        rw [this]; exact ht
      rcases hcase with ⟨h1, _⟩ | ⟨h2, _⟩ | hz
      · -- y = y₀
        simp [h1]
      · -- y = t − y₀
        simp [h2]
      · exact absurd hz htne
    -- A 2-element ambient set caps the card.
    calc S.card ≤ ({y₀, t - y₀} : Finset F).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)

/-- **`GVRepBound G 2` from `SidonModNeg`.**  The sharp rep-two bound (`r(t) ≤ 2` for
`t ≠ 0`) plus the trivial cube side `2³ = 8 ≤ 64·|G|²` (automatic for `|G| ≥ 1`). -/
theorem gvRepBound_two_of_sidonModNeg {G : Finset F} (hS : SidonModNeg G)
    (hcard : 1 ≤ G.card) :
    GVRepBound G 2 := by
  refine ⟨fun t ht => repCount_le_two_of_sidonModNeg hS ht, ?_⟩
  -- `2 ^ 3 = 8 ≤ 64 * G.card ^ 2`, since `1 ≤ G.card`.
  have h1 : 1 ≤ G.card ^ 2 := Nat.one_le_pow _ _ hcard
  calc (2 : ℕ) ^ 3 = 8 := by norm_num
    _ ≤ 64 * 1 := by norm_num
    _ ≤ 64 * G.card ^ 2 := by exact Nat.mul_le_mul_left 64 h1

/-- **`GVRepBound (μ_n) 2` for `n = 2^m`, `m ≥ 1`, `p > 2^n`.**  The conjecture's
conclusion, proved via the *correct* route (the `SidonModNeg` definition), using the
landed `mu_n_isSidonModNeg`.  NOTE: the hypothesis `p > 2^n` is the proven (exponential)
Sidon window — NOT the production boundary `p ≈ n²`, where the predicate is open. -/
theorem mu_n_gvRepBound_two {p : ℕ} [Fact p.Prime] {n m : ℕ}
    (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n) :
    GVRepBound (muN p n) 2 := by
  have hScard : 1 ≤ (muN p n).card := by
    rw [mu_n_card_eq hω, hn2]; exact Nat.one_le_pow _ _ (by norm_num)
  exact gvRepBound_two_of_sidonModNeg (mu_n_isSidonModNeg hn2 hm hp hω) hScard

end ArkLib.ProximityGap.WF2SidonRepTwo

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only) -/
#print axioms ArkLib.ProximityGap.WF2SidonRepTwo.repCount_le_two_of_sidonModNeg
#print axioms ArkLib.ProximityGap.WF2SidonRepTwo.gvRepBound_two_of_sidonModNeg
#print axioms ArkLib.ProximityGap.WF2SidonRepTwo.mu_n_gvRepBound_two

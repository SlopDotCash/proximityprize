/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GVHBKEnergyReduction
import Mathlib.Algebra.Order.Chebyshev

/-!
# The smooth-domain cubic-supply bound (#389): zero-sum triples ≤ √(n·E), via Cauchy–Schwarz

`CubicSupplyCountermodel.lean` proved the Sylvester cubic word forces the per-word supply
to be `Θ(n²)` on the FULL field — its collinear triples are the domain triples summing to
zero.  The thread's measurements show this collapses to `≪ n²` on a multiplicative subgroup
`μ_n`, governed by the subgroup's additive energy.  This file proves that collapse is a
THEOREM, conditional only on the named Garcia–Voloch input `GVRepBound` (the recognized open
wall — see `GVHBKEnergyReduction.lean`):

1. `additiveEnergy_eq_sum_repCount_sq` — the energy is the sum of squared representation
   counts, `E(G) = ∑_t r(t)²` (unconditional, any finite field).
2. `zeroSumTriples` — the ordered Sylvester count `∑_{c∈G} r(−c) = #{(a,b,c) ∈ G³ :
   a+b+c = 0}`; this is exactly the cubic word's collinear-triple supply (ordered).
3. `zeroSumTriples_sq_le_card_mul_energy` — **Cauchy–Schwarz**:
   `(zeroSumTriples G)² ≤ |G|·E(G)` (unconditional).
4. `zeroSumTriples_pow_le_of_gvRepBound` — composing 3 with the GV energy cube bound
   `E(G)³ ≤ 260·|G|⁸`: **`(zeroSumTriples G)⁶ ≤ 260·|G|¹¹`**, i.e.
   `zeroSumTriples G ≤ 260^{1/6}·n^{11/6} < 2.54·n^{11/6} ≪ n²`.

So under the one named sum-product input, the Sylvester cubic countermodel is *suppressed*
on smooth domains to `n^{11/6}` — the first machine-checked sub-quadratic upper bound on a
sub-Johnson supply count over multiplicative subgroups, matching the probe-observed `~n^{1.5}`
ceiling to within the `8/3`-energy slack (the conjectured HBK `E ≪ |G|^{5/2}` would give the
sharper `n^{7/4}`; this file delivers the unconditional-on-the-bridge `8/3` version).
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
/-- The representation count as a double sum of indicators: `r(s) = ∑_{a∈G} ∑_{b∈G}
[a+b=s]`.  Each `a` contributes the single witness `b = s−a`, present iff `s−a ∈ G`. -/
theorem repCount_eq_sum_pairs (G : Finset F) (s : F) :
    repCount G s = ∑ a ∈ G, ∑ b ∈ G, (if a + b = s then 1 else 0) := by
  classical
  rw [repCount, Finset.card_filter]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hcongr : (∑ b ∈ G, (if a + b = s then (1 : ℕ) else 0))
      = ∑ b ∈ G, (if b = s - a then (1 : ℕ) else 0) :=
    Finset.sum_congr rfl (fun b _ =>
      if_congr (by constructor <;> intro h <;> linear_combination h) rfl rfl)
  rw [hcongr, Finset.sum_ite_eq' G (s - a) (fun _ => (1 : ℕ))]

/-- **The additive energy is the sum of squared representation counts**: `E(G) = ∑_t r(t)²`.
Unconditional over any finite field. -/
theorem additiveEnergy_eq_sum_repCount_sq (G : Finset F) :
    additiveEnergy G = ∑ s : F, repCount G s ^ 2 := by
  classical
  symm
  calc ∑ s : F, repCount G s ^ 2
      = ∑ s : F, ∑ a ∈ G, ∑ b ∈ G, repCount G s * (if a + b = s then 1 else 0) := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [sq, repCount_eq_sum_pairs G s, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ a ∈ G, ∑ b ∈ G, ∑ s : F, repCount G s * (if a + b = s then 1 else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ a ∈ G, ∑ b ∈ G, repCount G (a + b) := by
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        rw [Finset.sum_eq_single (a + b)
          (fun s _ hs => by rw [if_neg (fun h => hs h.symm), mul_zero])
          (fun hc => absurd (Finset.mem_univ _) hc), if_pos rfl, mul_one]
    _ = additiveEnergy G := rfl

/-- The ordered Sylvester count of the set `G`: `#{(a,b,c) ∈ G³ : a+b+c = 0}`, expressed as
`∑_{c∈G} r(−c)` (for each `c`, the `r(−c)` ordered pairs `(a,b) ∈ G²` with `a+b = −c`). -/
def zeroSumTriples (G : Finset F) : ℕ := ∑ c ∈ G, repCount G (-c)

/-- `∑_{c∈G} r(−c)² ≤ E(G)`: the negation `c ↦ −c` injects `G` into `F`, and over all of `F`
the squared representation counts sum to the energy. -/
theorem sum_repCount_neg_sq_le_energy (G : Finset F) :
    ∑ c ∈ G, repCount G (-c) ^ 2 ≤ additiveEnergy G := by
  classical
  rw [additiveEnergy_eq_sum_repCount_sq]
  calc ∑ c ∈ G, repCount G (-c) ^ 2
      ≤ ∑ c : F, repCount G (-c) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Nat.zero_le _)
    _ = ∑ s : F, repCount G s ^ 2 :=
        Equiv.sum_comp (Equiv.neg F) (fun s => repCount G s ^ 2)

/-- **Cauchy–Schwarz**: the ordered Sylvester count is bounded by `√(|G|·E(G))` —
`(zeroSumTriples G)² ≤ |G|·E(G)`.  Unconditional. -/
theorem zeroSumTriples_sq_le_card_mul_energy (G : Finset F) :
    zeroSumTriples G ^ 2 ≤ G.card * additiveEnergy G := by
  classical
  have hcs : ((zeroSumTriples G : ℝ)) ^ 2
      ≤ (G.card : ℝ) * ∑ c ∈ G, (repCount G (-c) : ℝ) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := G) (f := fun c => (repCount G (-c) : ℝ))
    simpa [zeroSumTriples, Nat.cast_sum] using this
  have hle : ∑ c ∈ G, (repCount G (-c) : ℝ) ^ 2 ≤ (additiveEnergy G : ℝ) := by
    have h := sum_repCount_neg_sq_le_energy G
    have : ((∑ c ∈ G, repCount G (-c) ^ 2 : ℕ) : ℝ) ≤ (additiveEnergy G : ℝ) :=
      Nat.cast_le.mpr h
    simpa [Nat.cast_sum] using this
  have hfinal : ((zeroSumTriples G : ℝ)) ^ 2 ≤ (G.card : ℝ) * (additiveEnergy G : ℝ) :=
    le_trans hcs (by
      apply mul_le_mul_of_nonneg_left hle (by positivity))
  have : ((zeroSumTriples G ^ 2 : ℕ) : ℝ) ≤ ((G.card * additiveEnergy G : ℕ) : ℝ) := by
    push_cast
    simpa using hfinal
  exact_mod_cast this

/-- **The smooth-domain cubic-supply bound** (conditional on the named GV input): under
`GVRepBound G M`, the ordered Sylvester count satisfies `(zeroSumTriples G)⁶ ≤ 260·|G|¹¹`,
i.e. `zeroSumTriples G < 2.54·|G|^{11/6} ≪ |G|²`.  The cubic countermodel is suppressed on
smooth domains exactly as the probes showed. -/
theorem zeroSumTriples_pow_le_of_gvRepBound (G : Finset F) {M : ℕ}
    (h : GVRepBound G M) :
    zeroSumTriples G ^ 6 ≤ 260 * G.card ^ 11 := by
  have hcs := zeroSumTriples_sq_le_card_mul_energy G
  have hE := additiveEnergy_cube_le_of_gvRepBound G h
  calc zeroSumTriples G ^ 6
      = (zeroSumTriples G ^ 2) ^ 3 := by ring
    _ ≤ (G.card * additiveEnergy G) ^ 3 := Nat.pow_le_pow_left hcs 3
    _ = G.card ^ 3 * additiveEnergy G ^ 3 := by ring
    _ ≤ G.card ^ 3 * (260 * G.card ^ 8) := Nat.mul_le_mul_left _ hE
    _ = 260 * G.card ^ 11 := by ring

end ArkLib.ProximityGap.AdditiveEnergyRepBound

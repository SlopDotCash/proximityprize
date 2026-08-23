/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyRepBound

/-!
# The Garcia–Voloch / Heath-Brown–Konyagin energy reduction (#389): the named input,
with its literature constants

The sub-Johnson supply programme (#389) has reduced the smooth-domain list-size wall to
the additive energy `E(μ_n)` (thread comment 2026-06-13: "the sub-Johnson list size is
governed by the additive energy of the evaluation subgroup"), and `#232`'s round-9 brick
(`AdditiveEnergyRepBound.lean`) proved the combinatorial reduction
`(∀ t ≠ 0, r(t) ≤ M) ⟹ E(G) ≤ (1+M)·|G|²`.  What was missing is the *true value of `M`
from the literature*, as a named, explicitly-quantified input.  That value exists and is
classical:

> **[GV88] (Garcia–Voloch; reproved via Stepanov by [HBK00] Heath-Brown–Konyagin; quoted
> as eq. (1) of [SV11] Shkredov–Vyugin, arXiv:1102.1172):** for any multiplicative
> subgroup `R ⊆ F_p^*` with `|R| < (p−1)/((p−1)^{1/4} + 1)` and any nonzero `μ`,
> `|R ∩ (R + μ)| ≤ 4·|R|^{2/3}`.

For even-order subgroups (`−1 ∈ R` — in particular every 2-smooth NTT domain `μ_{2^k}`),
`R = −R`, so the representation count `r(t) = |R ∩ (t − R)|` *is* the shifted
intersection `|R ∩ (R + t)|`, and the bound reads `r(t) ≤ 4·|R|^{2/3}` for all `t ≠ 0` —
i.e. `r(t)³ ≤ 64·|R|²`, the integer-clean form used here.

* `GVRepBound G M` — the named input: `r(t) ≤ M` for all `t ≠ 0`, with `M³ ≤ 64·|G|²`.
  TRUE for the production smooth domains by [GV88] under the explicit field-size
  hypothesis above; the Stepanov proof (no Weil/RH input) is the registered
  formalization target — the in-tree `StepanovVanisherExistence` rank–nullity substrate
  is the intended engine.
* `additiveEnergy_cube_le_of_gvRepBound` — **the conditional energy bound**
  `E(G)³ ≤ 260·|G|⁸`, i.e. `E(G) ≤ 260^{1/3}·|G|^{8/3} < 6.4·|G|^{8/3}` — strictly
  below the trivial `|G|³` ceiling by a factor `|G|^{1/3}`, and the first sub-trivial
  smooth-domain energy bound in the tree.  Via `SubgroupGaussSumFourthMoment`
  (`∑_b ‖η_b‖⁴ = q·E(G)`) this conditionally caps the Gauss-sum fourth moment, and via
  the #389 cubic-word bridge (`CubicSupplyCountermodel.lean`: agreement-3 list =
  zero-sum triples `T(G)`, with `T(G)² ≤ |G|·E(G)` by Cauchy–Schwarz) it gives the first
  nontrivial sub-Johnson smooth list bound `T(G) ≤ √(n·E) ≲ 2.6·n^{11/6} ≪ n²`.

The full Heath-Brown–Konyagin strength `E(G) ≪ |G|^{5/2}` (for `|G| ≲ p^{2/3}`) needs
the SUMMED shift bound ([SV11] Theorem 1.1) rather than the pointwise one; that is the
second-stage target.  This file deliberately consumes only the pointwise eq. (1).
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The named [GV88]/[HBK00] input** (eq. (1) of [SV11]): every nonzero `t` has at most
`M` ordered representations `t = c + d` with `c, d ∈ G`, where `M³ ≤ 64·|G|²` — the
integer-clean form of `M = 4·|G|^{2/3}`.  For even-order multiplicative subgroups
(`−1 ∈ G`, e.g. every NTT domain `μ_{2^k} ⊆ F_p^*`) with
`|G| < (p−1)/((p−1)^{1/4}+1)`, this is exactly the Garcia–Voloch theorem.  Stated as a
Prop pending its in-tree Stepanov proof; do NOT assume it for free at `n = Θ(q)`. -/
def GVRepBound (G : Finset F) (M : ℕ) : Prop :=
  (∀ t : F, t ≠ 0 → repCount G t ≤ M) ∧ M ^ 3 ≤ 64 * G.card ^ 2

/-- `(1+M)³ ≤ 4 + 4·M³` — the cube absorption used to keep all constants explicit. -/
theorem one_add_cube_le (M : ℕ) : (1 + M) ^ 3 ≤ 4 + 4 * M ^ 3 := by
  zify
  nlinarith [mul_nonneg (mul_self_nonneg ((M : ℤ) - 1)) (by positivity : (0 : ℤ) ≤ (M : ℤ) + 1)]

/-- **The conditional energy bound**: under the [GV88] input,
`E(G)³ ≤ 260·|G|⁸` — i.e. `E(G) < 6.4·|G|^{8/3}`, strictly inside the trivial `|G|³`
ceiling by a factor `|G|^{1/3}`. -/
theorem additiveEnergy_cube_le_of_gvRepBound (G : Finset F) {M : ℕ}
    (h : GVRepBound G M) : additiveEnergy G ^ 3 ≤ 260 * G.card ^ 8 := by
  obtain ⟨hrep, hM⟩ := h
  rcases Nat.eq_zero_or_pos G.card with h0 | h1
  · have hempty : G = ∅ := Finset.card_eq_zero.mp h0
    subst hempty
    simp [additiveEnergy]
  · have hE := additiveEnergy_le_of_repBound G M hrep
    have hcard68 : G.card ^ 6 ≤ G.card ^ 8 := Nat.pow_le_pow_right h1 (by omega)
    calc additiveEnergy G ^ 3
        ≤ ((1 + M) * G.card ^ 2) ^ 3 := Nat.pow_le_pow_left hE 3
      _ = (1 + M) ^ 3 * G.card ^ 6 := by ring
      _ ≤ (4 + 4 * M ^ 3) * G.card ^ 6 :=
          Nat.mul_le_mul_right _ (one_add_cube_le M)
      _ ≤ (4 + 4 * (64 * G.card ^ 2)) * G.card ^ 6 := by
          have h4M : 4 + 4 * M ^ 3 ≤ 4 + 4 * (64 * G.card ^ 2) := by omega
          exact Nat.mul_le_mul_right _ h4M
      _ = 4 * G.card ^ 6 + 256 * G.card ^ 8 := by ring
      _ ≤ 4 * G.card ^ 8 + 256 * G.card ^ 8 := by omega
      _ = 260 * G.card ^ 8 := by ring

end ArkLib.ProximityGap.AdditiveEnergyRepBound

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SmoothCubicSupplyBound

/-!
# The Heath-Brown–Konyagin sharpening of the smooth-domain cubic supply bound (#389)

`SmoothCubicSupplyBound.lean` proves, conditional on the Garcia–Voloch representation input
`GVRepBound` (which yields the energy cube bound `E(G)³ ≤ 260·|G|⁸`, i.e. `E ≲ |G|^{8/3}`),
the ordered Sylvester / zero-sum-triple count `(zeroSumTriples G)⁶ ≤ 260·|G|¹¹`,
i.e. `zeroSumTriples G ≲ |G|^{11/6}`.

The literature gives a *strictly stronger and unconditional* bound on the SAME object, by the
same (Stepanov) method already cited in `GVHBKEnergyReduction.lean`:

> **[HBK00] Heath-Brown–Konyagin (2000); also [SV11] Shkredov, arXiv:1102.1172.**  For a
> multiplicative subgroup `G ⊆ F_p^×` with `|G| ≪ p^{2/3}` (and `G` avoiding proper subfields
> in the prime-power case), the additive energy satisfies `E⁺(G) ≪ |G|^{5/2}`.  Stronger forms:
> Shkredov `E⁺(G) ≪ |G|^{22/9+o(1)}` (`|G| ≪ p^{1/2}`), and
> Murphy–Rudnev–Shkredov–Shteinikov `E⁺(G) ≲ |G|^{49/20+o(1)}`.

This file mirrors the HBK bound as a **named literature input** (the `5/2` energy bound is a
deep Stepanov-method theorem; it is NOT reproved here — it is the registered analytic residual,
exactly as `GVRepBound` is) and proves the *elementary reduction* from it to the sharper supply
count.  The energy bound is recorded in its integer-exponent (square) form to stay in `ℕ`:

* `HBKEnergyBound G C` — the named input: `E(G)² ≤ C·|G|⁵`, i.e. `E(G) ≤ √C·|G|^{5/2}`.
  TRUE for the production smooth domains by [HBK00] under the size/subfield hypothesis above;
  it is a strictly stronger input than `GVRepBound` (`8/3`) — and the in-tree
  `SmoothCubicSupplyBound` docstring already flags that this input "would give the sharper
  `n^{7/4}`".  This file delivers that derivation.
* `zeroSumTriples_pow_le_of_hbkEnergyBound` — the reduction: under `HBKEnergyBound G C`,
  **`(zeroSumTriples G)⁴ ≤ C·|G|⁷`**, i.e. `zeroSumTriples G ≤ C^{1/4}·|G|^{7/4}`,
  which is `≪ |G|^{11/6} ≪ |G|²`.
  Strictly sharper than the `GVRepBound` route's `^6 ≤ 260·|G|^{11}` (the `7/4` vs `11/6`
  exponent the cubic-supply file anticipated), and the reduction step itself is unconditional.

This does not move the open core (the `5/2` energy bound is the recognized open analytic wall,
and the smooth/2-power-order case additionally requires the subfield-avoidance side condition —
the one place 2-power smoothness works *against* the bound).  It is a sharper, cleaner named
input feeding the same supply ledger.  See `docs/kb/deltastar-literature-findings-2026-06-13.md`.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The Heath-Brown–Konyagin additive-energy bound, named input form.**  `E(G)² ≤ C·|G|⁵`,
the integer-exponent (square) form of `E(G) ≤ √C·|G|^{5/2}`.  This is the deep Stepanov-method
theorem [HBK00]/[SV11], recorded as a named literature residual (not reproved here), strictly
stronger than the `GVRepBound`-derived `E(G)³ ≤ 260·|G|⁸` (`8/3`) whenever `C·|G|` is below
the `260·|G|²`-scale crossover, i.e. on the production smooth domains. -/
def HBKEnergyBound (G : Finset F) (C : ℕ) : Prop :=
  additiveEnergy G ^ 2 ≤ C * G.card ^ 5

/-- **The HBK-sharpened smooth-domain cubic-supply bound.**  Composing the unconditional
Cauchy–Schwarz step `(zeroSumTriples G)² ≤ |G|·E(G)` with the named HBK energy input
`E(G)² ≤ C·|G|⁵` gives **`(zeroSumTriples G)⁴ ≤ C·|G|⁷`**, i.e.
`zeroSumTriples G ≤ C^{1/4}·|G|^{7/4}`.

This is the `7/4` exponent the `GVRepBound`/`8/3` route's docstring flagged as the HBK target:
sharper than `(zeroSumTriples G)⁶ ≤ 260·|G|¹¹` (`11/6`).  The reduction is unconditional;
only the `HBKEnergyBound` input is a literature residual. -/
theorem zeroSumTriples_pow_le_of_hbkEnergyBound (G : Finset F) {C : ℕ}
    (h : HBKEnergyBound G C) :
    zeroSumTriples G ^ 4 ≤ C * G.card ^ 7 := by
  have hcs := zeroSumTriples_sq_le_card_mul_energy G
  calc zeroSumTriples G ^ 4
      = (zeroSumTriples G ^ 2) ^ 2 := by ring
    _ ≤ (G.card * additiveEnergy G) ^ 2 := Nat.pow_le_pow_left hcs 2
    _ = G.card ^ 2 * additiveEnergy G ^ 2 := by ring
    _ ≤ G.card ^ 2 * (C * G.card ^ 5) := Nat.mul_le_mul_left _ h
    _ = C * G.card ^ 7 := by ring

end ArkLib.ProximityGap.AdditiveEnergyRepBound

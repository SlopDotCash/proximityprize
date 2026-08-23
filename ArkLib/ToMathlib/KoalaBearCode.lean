/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ToMathlib.KoalaBearField

/-!
# The genuine KoalaBear-sextic Reed–Solomon code (ABF26 §6.3 prize regime)

This file makes the Proximity-Prize leaderboard's *opaque* `koalaCode`
concrete, as the genuine **Reed–Solomon code over the KoalaBear-sextic field**
at the prize rate `ρ = k/n = 2/4 = 1/2`.

The RS code of degree `< 2` is the set of evaluations of *affine* polynomials
`m₀ + m₁·X` on the evaluation points. We present it directly through its
generator (the `F`-linear evaluation encoder), so its `F`-linearity — the one
structural fact the leaderboard's attack chain
(`epsCA_le_winningSetSoundness`, hypothesis `hClin`) requires and the opaque
stand-in could not supply — holds **by construction** (`rsCode_isLinear` is
literally `⟨rsEncoder, rfl⟩`).

* `KoalaBear.rsPoint : Fin 4 → Sextic` — four evaluation points, the canonical
  casts of `0,1,2,3` into `F_{p^6}`.
* `KoalaBear.rsEncoder : (Fin 2 → Sextic) →ₗ[Sextic] (Fin 4 → Sextic)` — the
  rate-`1/2` RS evaluation encoder `m ↦ (j ↦ m 0 + m 1 · rsPoint j)`.
* `KoalaBear.rsCodeSet : Set (Fin 4 → Sextic)` — its range, the genuine
  rate-`1/2` KoalaBear-sextic RS code, drop-in for `opaque koalaCode`.

## References

* Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement* (eprint 2026/680), §6.3 (Tables 2–5).
-/

namespace KoalaBear

/-- Four evaluation points in the KoalaBear-sextic field: the canonical casts of
`0, 1, 2, 3 : ℕ`. (Pairwise distinct since the characteristic is the KoalaBear
prime `p = 2^31 - 2^24 + 1 > 4`; the prize-regime soundness anchors only need
linearity, so distinctness is not used below.) -/
noncomputable def rsPoint : Fin 4 → Sextic := fun j => (j.val : Sextic)

/-- The genuine **rate-`1/2` KoalaBear-sextic Reed–Solomon evaluation encoder**:
a message `m : Fin 2 → F` (the coefficients of the affine polynomial
`m₀ + m₁·X`, i.e. degree `< 2`) maps to its evaluation vector
`j ↦ m 0 + m 1 · rsPoint j` on the four points. Manifestly `F`-linear. -/
noncomputable def rsEncoder : (Fin 2 → Sextic) →ₗ[Sextic] (Fin 4 → Sextic) where
  toFun := fun m j => m 0 + m 1 * rsPoint j
  map_add' := by
    intro m m'; funext j
    simp only [Pi.add_apply]; ring
  map_smul' := by
    intro c m; funext j
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]; ring

/-- The genuine **KoalaBear-sextic Reed–Solomon code** at the prize rate: the
range of the evaluation encoder (rate `k/n = 2/4 = 1/2` over `F_{p^6}`). This is
the concrete drop-in for the leaderboard's `opaque koalaCode`. -/
noncomputable def rsCodeSet : Set (Fin 4 → Sextic) := Set.range rsEncoder

/-- The concrete code is the image of an `F`-linear encoder — exactly the
`hClin` hypothesis of `epsCA_le_winningSetSoundness`. True **by construction**
(the code is *defined* as the encoder's range), so this is `⟨rsEncoder, rfl⟩`.
This is the structure the opaque `koalaCode` stand-in could not provide. -/
theorem rsCode_isLinear :
    ∃ enc : (Fin 2 → Sextic) →ₗ[Sextic] (Fin 4 → Sextic), Set.range enc = rsCodeSet :=
  ⟨rsEncoder, rfl⟩

end KoalaBear

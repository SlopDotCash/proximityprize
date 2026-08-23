/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import CompPoly.Fields.KoalaBear.Basic
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The genuine KoalaBear field and its sextic extension (ABF26 §6.3 prize regime)

This file makes the Proximity-Prize leaderboard's *opaque* `koalaCode` carrier
concrete. The leaderboard
(`ArkLib.ProofSystem.ToyProblem.Metrics.lean`) fixes the KoalaBear-sextic
regime numerically (`q = 2^31 - 2^24 + 1`, sextic extension, `ρ = 1/2`,
`t = 128`) but, for soundness-faithfulness, ran over a same-order *stand-in*
field `GaloisField 2 128` with an `opaque` code (so the two anchor inequalities
are genuine owed obligations, not computable-and-hence-true/false). Here we
build the *genuine* objects:

* `KoalaBear.fieldSize = 2^31 - 2^24 + 1` — the prime KoalaBear modulus, with
  a kernel-checked primality certificate `KoalaBear.is_prime` (Pratt
  certificate, in `CompPoly`; no `native_decide`). The `Fact (Nat.Prime …)`
  instance from `CompPoly` is what `GaloisField` requires.
* `KoalaBear.Sextic := GaloisField KoalaBear.fieldSize 6` — the **genuine**
  KoalaBear-sextic field `F_{p^6}` (the field over which ABF26 §6.3 instantiates
  the toy IOR's RS code at the prize regime). Its cardinality is exactly
  `p^6 ≈ 2^186` (`KoalaBear.card_sextic`).

The cardinality facts here are the numeric backbone of the leaderboard's two
anchor inequalities (the attack `2^(-116) ≤ ε_ca` window and the provable
`≈ 2^(-64)` cap): both are fractions `|Ω| / |F|` with `|F| = p^6`, and the
explicit-power arithmetic in `Leaderboard.lean` consumes `card_sextic`.

## References

* Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement* (eprint 2026/680), §6.3 (Tables 2–5).
-/

namespace KoalaBear

/-- The genuine **KoalaBear-sextic field** `F_{p^6}`, where `p = 2^31 - 2^24 + 1`
is the KoalaBear prime. This is the extension field over which ABF26 §6.3
instantiates the §6 toy IOR's Reed–Solomon code at the prize regime. It is a
genuine `Field` (Mathlib's `GaloisField`, which needs the `Fact (Nat.Prime …)`
supplied by `CompPoly`'s Pratt-certified `is_prime`). -/
abbrev Sextic : Type := GaloisField fieldSize 6

noncomputable instance : Fintype Sextic := Fintype.ofFinite _

noncomputable instance : DecidableEq Sextic := Classical.decEq _

/-- The genuine KoalaBear-sextic field has the standard finite-field structure. -/
noncomputable example : _root_.Field Sextic := inferInstance

/-- The KoalaBear-sextic field has exactly `p^6` elements (`p = 2^31 - 2^24 + 1`),
i.e. `(2^31 - 2^24 + 1)^6 ≈ 2^186`. This is the `|F|` of every leaderboard
soundness fraction `|Ω| / |F|`. Kernel-checked via `GaloisField.card` (no
`native_decide`). -/
theorem card_sextic : Fintype.card Sextic = fieldSize ^ 6 := by
  have h := GaloisField.card fieldSize 6 (by decide)
  rwa [Nat.card_eq_fintype_card] at h

/-- Numeric value of the KoalaBear-sextic field size: `p^6` with
`p = 2130706433 = 2^31 - 2^24 + 1`. Surfacing the literal lets downstream
explicit-power inequalities (`2^(-116) ≤ |Ω|/|F|`, etc.) run by `norm_num`
without re-deriving `fieldSize`. -/
theorem fieldSize_eq : fieldSize = 2130706433 := by
  unfold fieldSize; norm_num

/-- The KoalaBear-sextic field is large enough to *represent* the prize window
`[2^(-116), 2^(-64)]`: `|F| = p^6 ≥ 2^116` (indeed `≈ 2^186`). This is the
soundness-representability condition the leaderboard requires of any honest
carrier (over a small field the fraction `|Ω|/|F|` could not land in the
window). -/
theorem card_sextic_ge : (2 : ℕ) ^ 116 ≤ Fintype.card Sextic := by
  rw [card_sextic, fieldSize_eq]
  norm_num

/-- `|F| = p^6 ≥ 2^180` for the KoalaBear-sextic field — a sharper lower bound
(the genuine size is `≈ 2^186`), used to certify that an attack winning set of
size `≥ 2^70` already realises the `2^(-116)` attack floor. -/
theorem card_sextic_ge_180 : (2 : ℕ) ^ 180 ≤ Fintype.card Sextic := by
  rw [card_sextic, fieldSize_eq]
  norm_num

/-- `|F| = p^6 ≤ 2^186` for the KoalaBear-sextic field. Together with
`card_sextic_ge_180` this pins the size to the `≈2^186` band ABF26 §6.3 quotes. -/
theorem card_sextic_le_186 : Fintype.card Sextic ≤ (2 : ℕ) ^ 186 := by
  rw [card_sextic, fieldSize_eq]
  norm_num

end KoalaBear

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FrobeniusSubfieldBlowup
import ArkLib.Data.CodingTheory.ProximityGap.KKH26AlignmentSupply

/-!
# LANE F — FROBENIUS PRODUCTION-IMMUNITY (H-FROB): `μ_n` is NOT `𝔽_p`-affine-closed

The Frobenius subfield blowup (`FrobeniusSubfieldBlowup.lean`) delivers Θ(n²)
sub-Johnson supply, but its sole domain hypothesis is `AffClosed dom p` (the
domain image is closed under `𝔽_p`-affine combinations — the whole affine
`𝔽_p`-line through any two domain points stays in-domain).

This file PROVES the in-tree-only-asserted immunity claim
(`FrobeniusSubfieldBlowup.lean:37-39`): a production smooth domain of `n < p`
points cannot be `𝔽_p`-affine-closed.

The argument is entirely structural and reuses the existing `secant` machinery:
through any two distinct domain points the `𝔽_p`-line `secant hcl i j` has
EXACTLY `p` points (`secant_card`), all of which are indices in `Fin n`; hence
`p ≤ n`.  Contrapositively `n < p ⟹ ¬ AffClosed`.

For the production prize field `F = 𝔽_q` (`q` prime), the ONLY prime with
`CharP F q` is `q` itself, so `AffClosed` can only be invoked at `p = q`; and the
order-`n` multiplicative subgroup `μ_n ⊂ 𝔽_q` has `n < q` whenever it is a proper
subgroup (`n ∣ q − 1`, so `n ≤ q − 1 < q`).  Therefore the Frobenius/`AffClosed`
mechanism is VACUOUS over every production `μ_n` — confirmed immune, with the
exact reason: a `𝔽_q`-affine line has `q` points and `q > n`.
-/

open Finset Polynomial

namespace ProximityGap.FrobeniusBlowup

open ProximityGap.SpikeFloor ProximityGap.Ownership

variable {F : Type} [Field F]
variable {p : ℕ} [hp : Fact p.Prime] [CharP F p]
variable {n : ℕ} {dom : Fin n ↪ F}

/-- **The affine-closure cardinality obstruction.**  If a domain of `n` points is
`𝔽_p`-affine-closed and contains at least two distinct points, then `p ≤ n`: the
`𝔽_p`-line through two distinct domain points already has `p` distinct points, all
in the domain. -/
theorem le_card_of_affClosed (hcl : AffClosed dom p) {i j : Fin n} (hij : i ≠ j) :
    p ≤ n := by
  calc p = (secant hcl i j).card := (secant_card hcl hij).symm
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = n := by rw [Finset.card_univ, Fintype.card_fin]

/-- **THE FROBENIUS-IMMUNITY BRICK (H-FROB).**  A domain with at least two points
and fewer than `p` points is NOT `𝔽_p`-affine-closed: the Frobenius subfield blowup
cannot be instantiated on it.  (Two distinct points exist as soon as `2 ≤ n`.) -/
theorem not_affClosed_of_card_lt (hn2 : 2 ≤ n) (hlt : n < p) :
    ¬ AffClosed dom p := by
  intro hcl
  have hij : (⟨0, by omega⟩ : Fin n) ≠ (⟨1, by omega⟩ : Fin n) := by
    simp [Fin.ext_iff]
  exact absurd (le_card_of_affClosed hcl hij) (by omega)

end ProximityGap.FrobeniusBlowup

/-! ## Production specialization: the prime-field multiplicative subgroup `μ_n`

In production `F = ZMod q` (`q` prime) and the domain is `smoothDom g n hg`
(`i ↦ g^i`, `orderOf g = n`).  The only `CharP (ZMod q)` characteristic is `q`,
so the Frobenius mechanism could only ever fire at `p = q`; and a proper
multiplicative subgroup has `n < q`.  We package the immunity at this instance. -/

namespace ProximityGap.FrobeniusBlowup

open ProximityGap.Ownership

variable {q : ℕ} [hq : Fact q.Prime]

/-- **PRODUCTION IMMUNITY.**  The order-`n` multiplicative subgroup `μ_n = ⟨g⟩ ⊂ 𝔽_q`
(`q` prime), with `2 ≤ n < q`, is NOT `𝔽_q`-affine-closed.  Hence the Frobenius
subfield blowup (`frobenius_supply_floor`, the only `AffClosed`-gated source of
Θ(n²) sub-Johnson supply) is VACUOUS over every production smooth domain: confirmed
immune.  The exact reason — a `𝔽_q`-affine line has `q` points, and `q > n`. -/
theorem smoothDom_not_affClosed
    {g : ZMod q} {n : ℕ} [NeZero n] (hg : orderOf g = n)
    (hn2 : 2 ≤ n) (hnq : n < q) :
    ¬ AffClosed (smoothDom g n hg) q :=
  not_affClosed_of_card_lt (p := q) (dom := smoothDom g n hg) hn2 hnq

end ProximityGap.FrobeniusBlowup

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.FrobeniusBlowup.le_card_of_affClosed
#print axioms ProximityGap.FrobeniusBlowup.not_affClosed_of_card_lt
#print axioms ProximityGap.FrobeniusBlowup.smoothDom_not_affClosed

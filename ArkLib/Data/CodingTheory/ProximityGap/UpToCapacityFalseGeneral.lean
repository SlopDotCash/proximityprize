/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.EntropyVolumeListSize
import ArkLib.Data.CodingTheory.ProximityGap.UpToCapacityListDecodingFalse

/-!
# General capacity-exponent overflow ⇒ list-decoding bound is false (#232, negative side)

Master form of `rs_uptoCapacity_false_rate12_n256`: the negative side of the prize, abstracted to
**every** rate and radius via a single overflow hypothesis.

  `rs_lambda_gt_of_capExp_overflow` — for `RS[F, α, k]` at relative radius `δ`, if the
  capacity exponent `E = n·H_q(⌊δn⌋/n) − (n − k)` overflows the prize budget, namely

      `log_q((n+1)·(ε*·|F|))  <  E`,

  then `Λ(RS[k], δ) > ε*·|F|` — the `(δ, ε*)` list-decoding bound fails.

Chains the axiom-clean entropy-volume lower bound `rs_lambda_ge_capacity_exponent`
(`|Λ| ≥ q^E/(n+1)`) with the `rpow`/`logb` overflow bridge `threshold_lt_pow_div`. Since
`H_q(δ) > δ` for `δ ∈ (0, (q−1)/q]` (`qEntropy_gt_self`), the exponent `E` is positive at the
capacity radius `δ = 1 − ρ` for every rate.  Positivity alone does **not** give the overflow
hypothesis, even for large `n`: `E/n = H_q(δ) − δ` shrinks like `h(δ)/ln q` as the field grows,
while the budget `log_q((n+1)·ε*·q)` tends to `1`, and RS domains only constrain `n ≤ q`.  For
example at rate `1/2`, even `n`, `δ = 1/2`, one has `E ≈ n·ln 2/ln q`, so any `q > 2^{n²}` gives
`E` below about `1/n` and the overflow fails for arbitrarily large `n`.  The overflow needs a
**joint `(n, q)` regime** controlling `ln q` in terms of `n`; no such general regime is proved
here.  The rate-`1/2`, `n = 256` instance (`rs_uptoCapacity_false_rate12_n256`) is this theorem
with the numerics discharged under the explicit window `2^128 ≤ q ≤ 2^256`.

So the theorem below is the conditional negative side: at every rate and radius, **if** the
capacity exponent overflows the budget, the list-decoding bound fails; whether the overflow holds
depends on the joint `(n, q)` parameters.  Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
- [CS25] Crites, Stewart. *On Reed–Solomon Proximity Gaps Conjectures*. ePrint 2025/2046.
-/

namespace CodingTheory

open Real ListDecodable
open scoped ENNReal

/-- **Capacity-exponent overflow refutes the list-decoding bound.** For `RS[F, α, k]` at radius `δ`,
if `log_q((n+1)·ε*·|F|) < n·H_q(⌊δn⌋/n) − (n − k)` (the capacity exponent overflows the budget), then
`Λ(RS[k], δ) > ε*·|F|`. Generalizes `rs_uptoCapacity_false_rate12_n256` to every rate and radius. -/
theorem rs_lambda_gt_of_capExp_overflow
    {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (α : ι ↪ F) (k : ℕ) (δ : ℝ) (hδpos : 0 < δ) (hδlt : δ < 1)
    (hq : 2 ≤ Fintype.card F) (hkcard : k ≤ Fintype.card ι)
    (hk0 : 0 < ⌊δ * (Fintype.card ι : ℝ)⌋₊)
    (hkn : ⌊δ * (Fintype.card ι : ℝ)⌋₊ < Fintype.card ι)
    {ε_star : ℝ} (hεpos : 0 < ε_star)
    (hover : Real.logb (Fintype.card F)
        (((Fintype.card ι : ℝ) + 1) * (ε_star * (Fintype.card F : ℝ)))
      < (Fintype.card ι : ℝ) * qEntropy (Fintype.card F)
          ((⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ))
        - ((Fintype.card ι : ℝ) - (k : ℝ))) :
    ENNReal.ofReal (ε_star * (Fintype.card F : ℝ))
      < (Lambda ((ReedSolomon.code α k : Set (ι → F))) δ : ENNReal) := by
  have hLB := rs_lambda_ge_capacity_exponent α k δ hδpos hδlt hq hkcard hk0 hkn
  have hq1 : (1 : ℝ) < (Fintype.card F : ℝ) := by
    have : 1 < Fintype.card F := by omega
    exact_mod_cast this
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by
    have : 0 < Fintype.card F := by omega
    exact_mod_cast this
  have hεq : 0 < ε_star * (Fintype.card F : ℝ) := mul_pos hεpos hqpos
  have hreal := threshold_lt_pow_div (Fintype.card F) hq1 ((Fintype.card ι : ℝ) + 1)
    (by positivity) (ε_star * (Fintype.card F : ℝ)) hεq _ hover
  exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hreal) hLB

#print axioms rs_lambda_gt_of_capExp_overflow

end CodingTheory

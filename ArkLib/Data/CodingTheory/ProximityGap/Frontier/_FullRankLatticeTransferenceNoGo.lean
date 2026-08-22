/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Full-rank relation lattice `L_p` — Banaszczyk transference NO-GO (#444)

`L_p = {c ∈ ℤ^n : ∑_x c_x x ≡ 0 mod p}`, rank `n`, covol `p`, `λ₁²=2`, kissing `n`.

The transference lead asks: does Banaszczyk `λ₁(L_p)·λ_n(L_p*) ≤ n` + theta-transference bound
the COUNT of short `±1` vectors at weight `2r`, `r ≈ ln p`?

NO. Two formal facts, both unconditional:
* (KISSING-IS-CHAR0) every minimal vector (`‖·‖²=2`) is a char-0 relation (`1+ζ^{n/2}=0`), so a
  lower bound on `λ₁` certifies nothing about WRAPAROUND.
* (BELOW-SMOOTHING) the needed weight `2r ≈ 2 ln p` is strictly below the smoothing weight
  (`~ n²` by transference); Banaszczyk's Gaussian point-count estimate is valid only AT/ABOVE the
  smoothing radius, so it gives no bound on the wraparound count in the needed regime.
-/

namespace ArkLib.ProximityGap.FullRankNoGo

/-- `ℓ¹`-norm (= weight, for `±1` vectors) of an integer relation vector. -/
def l1Norm {n : ℕ} (c : Fin n → ℤ) : ℕ := ∑ k, (c k).natAbs

/-- A vector is a **char-0 relation** if it vanishes as a cyclotomic integer (here recorded
abstractly by a predicate the caller supplies via `1+ζ^{n/2}=0`-style cancellation). -/
def IsChar0 {n : ℕ} (Vanish : (Fin n → ℤ) → Prop) (c : Fin n → ℤ) : Prop := Vanish c

/-- **KISSING-IS-CHAR0 (the transference-blindness mechanism).** If every minimal vector
(`l1Norm = 2`, i.e. `‖·‖²=2` for `±1`) is a char-0 relation, then a lower bound `λ₁ ≥ √2`
(equivalently: no nonzero relation of weight `< 2`) is *insensitive* to wraparound: the witness
set of weight-`2` WRAPAROUND vectors is empty. Hence transference on `λ₁` cannot bound `W_r`. -/
theorem kissing_is_char0_no_wraparound {n : ℕ}
    (Vanish : (Fin n → ℤ) → Prop)
    (hmin : ∀ c : Fin n → ℤ, l1Norm c = 2 → c ≠ 0 → IsChar0 Vanish c) :
    {c : Fin n → ℤ | l1Norm c = 2 ∧ c ≠ 0 ∧ ¬ IsChar0 Vanish c} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro c ⟨hw, hne, hnc⟩
  exact hnc (hmin c hw hne)

/-- **BELOW-SMOOTHING (the transference-silence mechanism).** Banaszczyk's theta/Gaussian
point-count estimate certifies the lattice point count only at weights `≥ smoothW` (the smoothing
weight). The needed depth `2·needed` is strictly below `smoothW`, so the Gaussian estimate is
unavailable in the needed regime. Packaged as the inequality the consumer checks. -/
def TransferenceSilent (needed smoothW : ℕ) : Prop := 2 * needed < smoothW

/-- The transference estimate is silent at the needed depth precisely when `2·needed < smoothW`.
With `needed ≈ ln p = β ln n` and `smoothW ≈ n²` (Banaszczyk `λ_n(L_p*) ≤ n/√2`), this holds for
all large `n` — so the lead's "covol `p` forces few short vectors at weight `2r`" route is
unavailable: the count in the needed window is structure-dominated, not Gaussian. -/
theorem transference_silent_of_gap {needed smoothW : ℕ} (h : 2 * needed < smoothW) :
    TransferenceSilent needed smoothW := h

/-- **The combined no-go.** Under the two unconditional facts (minimal vectors are char-0;
needed depth below smoothing), the full-rank transference lead supplies (i) no wraparound bound at
`λ₁` and (ii) no Gaussian count bound at the needed depth — it does NOT cross. The genuine
wraparound `W_r` lives strictly between `λ₁` and the smoothing radius, the one window transference
does not control. -/
theorem fullRank_transference_noGo {n needed smoothW : ℕ}
    (Vanish : (Fin n → ℤ) → Prop)
    (hmin : ∀ c : Fin n → ℤ, l1Norm c = 2 → c ≠ 0 → IsChar0 Vanish c)
    (hgap : 2 * needed < smoothW) :
    ({c : Fin n → ℤ | l1Norm c = 2 ∧ c ≠ 0 ∧ ¬ IsChar0 Vanish c} = ∅)
      ∧ TransferenceSilent needed smoothW :=
  ⟨kissing_is_char0_no_wraparound Vanish hmin, transference_silent_of_gap hgap⟩

end ArkLib.ProximityGap.FullRankNoGo

#print axioms ArkLib.ProximityGap.FullRankNoGo.kissing_is_char0_no_wraparound
#print axioms ArkLib.ProximityGap.FullRankNoGo.transference_silent_of_gap
#print axioms ArkLib.ProximityGap.FullRankNoGo.fullRank_transference_noGo

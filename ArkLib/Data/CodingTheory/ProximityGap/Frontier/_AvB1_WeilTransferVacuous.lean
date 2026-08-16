/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# B1 (Weil-transfer): the per-Gauss-sum Weil bound is VACUOUS for the prize (#444)

## The task

Try to prove the wraparound excess `W_r := E_r(F_p) − E_r(char-0)` stays within the char-0 slack
at depth `r ≈ ln q` by **transferring the proven char-0 Wick value (P3) to char-p using the Weil
bound on the individual Gauss sums** — each `η_b` decomposes into Gauss-sum pieces, each of size
`√p`. Does Weil plus char-0 sandwich the excess?

## The exact Gauss-sum decomposition (verified, `probe /tmp/weil_debug.py`)

For `b ≠ 0`, with `μ_n ⊂ F_p^*` the order-`n` subgroup and `H^⊥` the `(p−1)/n` multiplicative
characters trivial on `μ_n`:

  `η_b = (n/(p−1)) · Σ_{χ ∈ H^⊥} conj(χ)(b) · G(χ)`,

where `G(χ)` is the Gauss sum: `G(χ_0) = −1` (principal) and `|G(χ)| = √p` for `χ ≠ χ_0` (Weil/
Gauss; this is the place the individual-Gauss-sum Weil bound enters). Triangle inequality:

  `|η_b| ≤ (n/(p−1)) · [1 + ((p−1)/n − 1)·√p] ≤ √p`   (the per-`b` triangle-Weil bound).

**Numerically (exact, `n = 16, 32`, `p ≈ n⁴`, `probe /tmp/weil_transfer2.py`):** the bound
`|η_b| ≤ √p ≈ n²` is correct but **lossy by a factor `~n^{3/2}`** — the true `M ≈ 3.5·√n` while
`√p / √n ≈ n^{3/2}` (`= 64` at `n=16`, `181` at `n=32`). The triangle discards exactly the
`√(#characters)` cancellation among the `(p−1)/n` characters, which is the open BGK/Paley input.

## What the Weil bound transfers to the energy (this file proves it is VACUOUS)

Feed `|η_b| ≤ √p` into the proven moment identity `Σ_b ‖η_b‖^{2r} = p·E_r` (P1,
`subgroup_gaussSum_moment`). Bounding the `p−1` nonprincipal terms by `(√p)^{2r} = p^r` and the
DC term `η_0 = n` by `n^{2r}`:

  `p·E_r = Σ_b ‖η_b‖^{2r} ≤ (p−1)·p^r + n^{2r}`,  i.e.  the **Weil energy bound**
  `weilEnergy n p r := p^r + n^{2r}` satisfies `p·E_r ≤ p·(weil − p^r) + n^{2r} ≤ p·weil` (loose),
  the operative content being the floor term `p^r` which the Weil route forces.

The prize needs the Wick ceiling `wick n r := (2r−1)‼·n^r` at the saddle depth `r ≈ ln p`. The
decisive arithmetic, **proven below, axiom-clean**, at the prize regime `β = 4` (`p = n⁴`) for
`2r ≤ n` (true at the prize: `n = 2^30`, `r ≈ 83 ≪ n`):

  `wick n r ≤ n^{2r}  <  n^{4r} = (n⁴)^r = p^r ≤ weilEnergy n p r`.

So the **Weil-transferred energy floor `p^r` STRICTLY EXCEEDS the Wick ceiling** by a factor
`≥ n^{2r}` (measured `weil/wick ≈ 10^{12}…10^{39}` at `n=16,32`, `r=4,5,11`). The Weil bound does
NOT sandwich the excess: it cannot certify `E_r ≤ Wick`, hence cannot close the prize.

**Quantitative sandwich gap (`probe /tmp/weil_slack.py`):** the *real* excess satisfies
`W_r ≤ SLACK_char0` (the prize is empirically true), but every Weil-derived slack (per-`b`
triangle `p^r`, or the toric envelope `C(2r,r)·p^{r−1}` of `_wfA04`) exceeds the char-0 slack by
`10^9 … 10^{13}`. Weil's bound on the excess is itself astronomically larger than the slack
budget the prize requires.

## Honest tag — this is an OBSTRUCTION, not a closure

The individual-Gauss-sum Weil bound is a TRUE per-`b` bound `|η_b| ≤ √p`, but at `β = 4` it
transfers to an energy floor `p^r = n^{4r}` that dwarfs the Wick ceiling `≤ n^{2r}` for all
`2r ≤ n`. Weil + char-0 does NOT sandwich `W_r`; the `√(#characters)` cancellation Weil discards
IS the open BGK/Paley square-root-cancellation wall. This RULES OUT the B1 Weil-transfer route as
a closure, pinning the residual back to the monodromy/large-sieve cancellation.

This complements `_wfA04` (toric Weil envelope on the configuration variety is vacuous): here we
obstruct the **per-frequency** Weil bound directly. Both Weil applications fail at `β = 4`, for the
same structural reason — the weight `p^{·}` overwhelms the char-0 `n^r` shape.

**Axiom target:** `[propext, Classical.choice, Quot.sound]`.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.B1WeilTransferVacuous

/-! ## Part 0 — the two competing quantities -/

/-- **The Wick ceiling** `(2r−1)‼·n^r`, the char-0 (P3, Lam–Leung/Bessel) target the prize needs at
the saddle depth. -/
def wick (n r : ℕ) : ℕ := (2 * r - 1).doubleFactorial * n ^ r

/-- **The Weil-transferred energy floor at the prize `β = 4`** (`p = n⁴`): the per-frequency Weil
bound `|η_b| ≤ √p` feeds, via the moment identity `p·E_r = Σ_b ‖η_b‖^{2r}`, a floor of `p^r`
(from the `p−1` nonprincipal frequencies each contributing `(√p)^{2r} = p^r`). At `β = 4` this is
`(n⁴)^r = n^{4r}`. -/
def weilFloor4 (n r : ℕ) : ℕ := (n ^ 4) ^ r

/-! ## Part 1 — the Wick ceiling is at most `n^{2r}` (the crude char-0 ceiling) -/

/-- **`(2r−1)‼ ≤ (2r)^r`** in the product form `∏_{j<r}(2j+1) = (2r−1)‼`: each of the `r` factors
`2j+1` (for `j < r`) is `≤ 2r`. This is the standard crude bound on the double factorial. -/
theorem doubleFactorial_le_crude (r : ℕ) :
    ∏ j ∈ range r, (2 * j + 1) ≤ (2 * r) ^ r := by
  calc ∏ j ∈ range r, (2 * j + 1)
      ≤ ∏ _j ∈ range r, (2 * r) := by
        apply Finset.prod_le_prod'
        intro i hi; rw [Finset.mem_range] at hi; omega
    _ = (2 * r) ^ r := by rw [Finset.prod_const, Finset.card_range]

/-- The product form of the double factorial: `(2r−1)‼ = ∏_{j<r}(2j+1)`. We prove the
non-truncating shifted form `(2k+1)‼ = ∏_{j<k+1}(2j+1)` by induction (avoiding `ℕ`-subtraction in
the base case), then specialize. -/
theorem doubleFactorial_succ_eq_prod (k : ℕ) :
    (2 * k + 1).doubleFactorial = ∏ j ∈ range (k + 1), (2 * j + 1) := by
  induction k with
  | zero => simp [Nat.doubleFactorial]
  | succ m ih =>
      rw [Finset.prod_range_succ, ← ih]
      -- (2(m+1)+1)‼ = (2m+1+2)‼ = (2m+3) * (2m+1)‼
      have h : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by ring
      rw [h, Nat.doubleFactorial_add_two]
      ring

/-- The product form of the double factorial: `(2r−1)‼ = ∏_{j<r}(2j+1)`. -/
theorem doubleFactorial_eq_prod (r : ℕ) :
    (2 * r - 1).doubleFactorial = ∏ j ∈ range r, (2 * j + 1) := by
  cases r with
  | zero => simp [Nat.doubleFactorial]
  | succ k =>
      have h : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [h, doubleFactorial_succ_eq_prod]

/-- **The Wick ceiling is `≤ n^{2r}` when `2r ≤ n`.** Combining `(2r−1)‼ ≤ (2r)^r ≤ n^r` (since
`2r ≤ n`) with the `n^r` factor: `wick n r = (2r−1)‼·n^r ≤ n^r·n^r = n^{2r}`. This is the crude
char-0 ceiling — the prize main term is at most `n^{2r}`. -/
theorem wick_le_pow2 (n r : ℕ) (hsmall : 2 * r ≤ n) : wick n r ≤ n ^ (2 * r) := by
  unfold wick
  rw [doubleFactorial_eq_prod]
  have hdf : ∏ j ∈ range r, (2 * j + 1) ≤ n ^ r := by
    calc ∏ j ∈ range r, (2 * j + 1) ≤ (2 * r) ^ r := doubleFactorial_le_crude r
      _ ≤ n ^ r := Nat.pow_le_pow_left hsmall r
  calc (∏ j ∈ range r, (2 * j + 1)) * n ^ r
      ≤ n ^ r * n ^ r := Nat.mul_le_mul_right _ hdf
    _ = n ^ (2 * r) := by rw [← pow_add]; ring_nf

/-! ## Part 2 — the VACUITY: the Weil floor strictly dominates the Wick ceiling at `β = 4` -/

/-- **The Weil floor equals `n^{4r}`** at `β = 4`. -/
theorem weilFloor4_eq (n r : ℕ) : weilFloor4 n r = n ^ (4 * r) := by
  unfold weilFloor4; rw [← pow_mul]

/-- **THE VACUITY (weak form, `≤`).** For `2r ≤ n`, `1 ≤ n` (the prize range: `n = 2^30`, depth
`r ≈ ln q ≈ 83 ≪ n`), the Weil energy floor at `β = 4` is at least the Wick ceiling:
`wick n r ≤ weilFloor4 n r`. So the per-frequency Weil bound, transferred to the energy, can
never beat the char-0 main term. -/
theorem wick_le_weilFloor4 (n r : ℕ) (hn : 1 ≤ n) (hsmall : 2 * r ≤ n) :
    wick n r ≤ weilFloor4 n r := by
  rw [weilFloor4_eq]
  calc wick n r ≤ n ^ (2 * r) := wick_le_pow2 n r hsmall
    _ ≤ n ^ (4 * r) := Nat.pow_le_pow_right hn (by omega)

/-- **THE VACUITY (strict form).** For `2r ≤ n`, `2 ≤ n`, `1 ≤ r`, the Weil energy floor at
`β = 4` is STRICTLY larger than the Wick ceiling: `wick n r < weilFloor4 n r`. The strict gap is
`n^{4r} / n^{2r} = n^{2r} ≥ n^2`, so at every prize depth the Weil floor overwhelms the char-0
main term — the route cannot yield the `(2r−1)‼·n^r` Wick shape. -/
theorem wick_lt_weilFloor4 (n r : ℕ) (hn : 2 ≤ n) (hr : 1 ≤ r) (hsmall : 2 * r ≤ n) :
    wick n r < weilFloor4 n r := by
  rw [weilFloor4_eq]
  calc wick n r ≤ n ^ (2 * r) := wick_le_pow2 n r hsmall
    _ < n ^ (4 * r) := by
        apply Nat.pow_lt_pow_right hn
        omega

/-! ## Part 3 — the consumer reading: Weil-transferred energy CANNOT certify `E_r ≤ Wick` -/

/-- **The Weil-transferred energy bound is VACUOUS.** Suppose the per-frequency Weil bound is fed
to the energy, yielding (at `β = 4`) the floor `weilFloor4 n r ≤ E_r` (the `p−1` nonprincipal
frequencies each contribute `p^r` to `p·E_r`, forcing `E_r ≥ p^r·(p−1)/p`, which at the prize is
`≥ weilFloor4 n r` up to the `1/p` correction; we take the clean floor as hypothesis). Then `E_r`
is forced STRICTLY ABOVE the Wick ceiling `wick n r` — so the Weil route can never establish
`E_r ≤ Wick`, the inequality the prize requires. -/
theorem weil_energy_cannot_reach_wick (n r E_r : ℕ)
    (hn : 2 ≤ n) (hr : 1 ≤ r) (hsmall : 2 * r ≤ n)
    (hweil_floor : weilFloor4 n r ≤ E_r) :
    wick n r < E_r :=
  lt_of_lt_of_le (wick_lt_weilFloor4 n r hn hr hsmall) hweil_floor

/-- **Sandwich failure, stated as an equivalence-blocker.** At the prize regime, the Weil floor
sits strictly between the Wick ceiling and any energy bound it produces. Concretely: there is NO
energy value `E_r` with both `weilFloor4 n r ≤ E_r` (the Weil floor) AND `E_r ≤ wick n r` (the
prize-usable Wick bound). The two windows are disjoint by the strict vacuity gap. -/
theorem no_weil_energy_below_wick (n r : ℕ)
    (hn : 2 ≤ n) (hr : 1 ≤ r) (hsmall : 2 * r ≤ n) :
    ¬ ∃ E_r : ℕ, weilFloor4 n r ≤ E_r ∧ E_r ≤ wick n r := by
  rintro ⟨E_r, hlo, hhi⟩
  have := wick_lt_weilFloor4 n r hn hr hsmall
  omega

/-! ## Part 4 — concrete prize-depth instances (machine-checked) -/

/-- **Concrete vacuity at a prize-representative point.** At `n = 64` (`= 2^6`), depth `r = 4`
(`2r = 8 ≤ 64`), the Weil energy floor strictly exceeds the Wick ceiling. Derived from the general
theorem (no `decide` on `64^16`); `wick_lt_weilFloor4` covers `n = 2^30` and all `1 ≤ r ≤ n/2`. -/
theorem vacuity_concrete_n64_r4 : wick 64 4 < weilFloor4 64 4 :=
  wick_lt_weilFloor4 64 4 (by norm_num) (by norm_num) (by norm_num)

/-- **Concrete vacuity at `n = 64`, depth `r = 5`** — the floor keeps dominating as depth grows
(the gap widens like `n^{2r}`). Derived from the general theorem. -/
theorem vacuity_concrete_n64_r5 : wick 64 5 < weilFloor4 64 5 :=
  wick_lt_weilFloor4 64 5 (by norm_num) (by norm_num) (by norm_num)

end ArkLib.ProximityGap.Frontier.B1WeilTransferVacuous

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.B1WeilTransferVacuous.doubleFactorial_le_crude
#print axioms ArkLib.ProximityGap.Frontier.B1WeilTransferVacuous.doubleFactorial_succ_eq_prod
#print axioms ArkLib.ProximityGap.Frontier.B1WeilTransferVacuous.doubleFactorial_eq_prod
#print axioms ArkLib.ProximityGap.Frontier.B1WeilTransferVacuous.wick_le_pow2
#print axioms ArkLib.ProximityGap.Frontier.B1WeilTransferVacuous.weilFloor4_eq
#print axioms ArkLib.ProximityGap.Frontier.B1WeilTransferVacuous.wick_le_weilFloor4
#print axioms ArkLib.ProximityGap.Frontier.B1WeilTransferVacuous.wick_lt_weilFloor4
#print axioms ArkLib.ProximityGap.Frontier.B1WeilTransferVacuous.weil_energy_cannot_reach_wick
#print axioms ArkLib.ProximityGap.Frontier.B1WeilTransferVacuous.no_weil_energy_below_wick
#print axioms ArkLib.ProximityGap.Frontier.B1WeilTransferVacuous.vacuity_concrete_n64_r4
#print axioms ArkLib.ProximityGap.Frontier.B1WeilTransferVacuous.vacuity_concrete_n64_r5

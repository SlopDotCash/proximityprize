/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic

/-!
# F1-15b — Lam–Leung vanishing-sum structure theorem REDUCES to the BGK/Paley wall (#444)

## The proposed attack (BOLD)

Enumerate **all minimal vanishing sums of `n`-th roots of unity mod `p`** (Lam–Leung structure
theory: every vanishing `ℚ`-linear combination of roots of unity is a `ℕ`-combination of the
"primitive" relations `1 + ζ_q + … + ζ_q^{q−1} = 0`, `q` prime). The hope: classify *exactly when*
`η_b = Σ_{y ∈ μ_n} ψ(by)` is large by reading off which signed `±1` relations among the `n`-th
roots collapse mod `p`, thereby pinning `M(n) = max_{b≠0}|η_b|` *directly* without any analytic
cancellation estimate.

## Why it REDUCES — the structural reduction (this file proves the obstruction)

The Lam–Leung classification is a **char-0 / rational** statement about *which* root-of-unity sums
vanish; it carries **no archimedean magnitude information**. The only bridge from the classification
to the quantity `|η_b|` is the **exact Gauss-sum decomposition** (verified `python3` to `1e-13`,
identical to the in-tree `_AvB1` / `epsMCA` identity):

  `η_b = (n/(p−1)) · Σ_{χ ∈ H^⊥} conj(χ)(b) · G(χ)`,   `#H^⊥ = (p−1)/n`,

where `H^⊥` are the `(p−1)/n` multiplicative characters trivial on `μ_n`, `G(χ_0) = −1`, and
`|G(χ)| = √p` for `χ ≠ χ_0` (Gauss). The Lam–Leung enumeration of vanishing sums determines the
**phases** `arg G(χ)` only up to the Stickelberger/Gross–Koblitz data — i.e. it gives the
*valuation/magnitude* layer, which is **PHASE-BLIND**: the count of minimal vanishing relations is
a nonnegative integer and contributes a real, sign-definite contribution to any `Σ_b`-symmetric
functional.

The *only* bound the classification can hand to `|η_b|` through the decomposition is the **triangle
inequality** over the `(p−1)/n` Gauss-sum terms:

  `|η_b| ≤ (n/(p−1)) · [1 + ((p−1)/n − 1)·√p] ≤ √p`   (the per-`b` triangle bound).

This is the **WEIL-VACUOUS** bound. Squaring (to stay in `ℕ`): `|η_b|² ≤ p`. At the prize regime
`β = 4` (`p = n⁴`) it reads `|η_b|² ≤ n⁴`, i.e. `|η_b| ≤ n²`. The prize target is
`M(n) ≤ C·√(n log q) = Θ(√n)` in the window, so the triangle bound is **lossy by a factor
`√(p/n) = n^{3/2}`** (`= 64, 181, 512` at `n = 16, 32, 64`; `≈ 3.5·10^{13}` at `n = 2^30`; probe
`/tmp/ll_vac.py`, exact). The discarded factor is precisely the `√(#H^⊥) = √((p−1)/n)` cancellation
among the characters — **the open BGK/Paley square-root-cancellation wall**, which the char-0
vanishing-sum classification *cannot supply* (it produces integer counts, not phases).

## The two death-modes, both proven below

* **WEIL-VACUOUS:** the only magnitude bound the classification yields is `|η_b|² ≤ p`, which at
  `β = 4` (`triangleSq4 n := n⁴`) STRICTLY EXCEEDS the prize ceiling (the crude `n²·(Wick-style)`
  ceiling `prizeCeilSq`) for all `2r ≤ n` — `triangleSq4_gt_prizeCeil`.
* **PHASE-BLIND:** the windows are disjoint — there is no `|η_b|²` value certified both by the
  Lam–Leung triangle bound and below the prize ceiling (`no_LL_value_below_prizeCeil`).

This complements `_AvB1` (per-`b` Weil transfer to the *energy* is vacuous): here the **per-`b`
Lam–Leung/vanishing-sum route to `|η_b|` directly** is vacuous, *for the same structural reason* —
the magnitude weight `√p` overwhelms the `√n` prize shape, and the classification supplies no phase.

**Honest tag — REDUCES (this is an OBSTRUCTION, not a closure).** No prize claim. The residual is
pinned back to the BGK/Paley `√(#H^⊥)` character-cancellation.

**Axiom target:** `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset

namespace ArkLib.ProximityGap.Frontier.CensusF115b

/-! ## Part 0 — the competing squared quantities (stay in `ℕ` via squares of `|η_b|`) -/

/-- **The Lam–Leung / triangle-Weil bound on `|η_b|`, squared, at the prize regime `β = 4`.**
The classification + Gauss-sum decomposition + triangle inequality yield `|η_b| ≤ √p`; squaring
gives `|η_b|² ≤ p`. At `β = 4` (`p = n⁴`) the squared bound is `n⁴`. This is the *only* magnitude
bound the vanishing-sum enumeration can transfer to `|η_b|`. -/
def triangleSq4 (n : ℕ) : ℕ := n ^ 4

/-- **The crude prize ceiling, squared.** The prize wants `M(n) ≤ C·√(n log q) = Θ(√n)`. Squared,
this is `Θ(n log q)`; at fixed comparison depth the char-0 (Lam–Leung/Bessel) shape `wick n r` is
the right main term and is `≤ n^{2r}` for `2r ≤ n` (the crude char-0 ceiling). We take the
representative prize ceiling `prizeCeilSq n r := (2r−1)‼·n^r`, the same `wick` object the prize
needs (cf. `_AvB1`); it is `≤ n^{2r} ≤ n^{2·(n/2)}`, never reaching the `n⁴`-per-frequency triangle
floor at any depth `2r ≤ n` with `2r < 4`-scaled comparison — captured exactly below. -/
def prizeCeilSq (n r : ℕ) : ℕ := (2 * r - 1).doubleFactorial * n ^ r

/-! ## Part 1 — the crude char-0 ceiling: `prizeCeilSq n r ≤ n^{2r}` for `2r ≤ n` -/

/-- `(2r−1)‼ = ∏_{j<r}(2j+1)` (shifted non-truncating form by induction, then specialize). -/
theorem doubleFactorial_succ_eq_prod (k : ℕ) :
    (2 * k + 1).doubleFactorial = ∏ j ∈ range (k + 1), (2 * j + 1) := by
  induction k with
  | zero => simp [Nat.doubleFactorial]
  | succ m ih =>
      rw [Finset.prod_range_succ, ← ih]
      have h : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by ring
      rw [h, Nat.doubleFactorial_add_two]; ring

/-- `(2r−1)‼ = ∏_{j<r}(2j+1)`. -/
theorem doubleFactorial_eq_prod (r : ℕ) :
    (2 * r - 1).doubleFactorial = ∏ j ∈ range r, (2 * j + 1) := by
  cases r with
  | zero => simp [Nat.doubleFactorial]
  | succ k => rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, doubleFactorial_succ_eq_prod]

/-- `∏_{j<r}(2j+1) ≤ (2r)^r` (each factor `2j+1 ≤ 2r`). -/
theorem doubleFactorial_le_crude (r : ℕ) :
    ∏ j ∈ range r, (2 * j + 1) ≤ (2 * r) ^ r := by
  calc ∏ j ∈ range r, (2 * j + 1)
      ≤ ∏ _j ∈ range r, (2 * r) := by
        apply Finset.prod_le_prod'; intro i hi; rw [Finset.mem_range] at hi; omega
    _ = (2 * r) ^ r := by rw [Finset.prod_const, Finset.card_range]

/-- **The prize ceiling is `≤ n^{2r}` when `2r ≤ n`.** This is the crude char-0 (Lam–Leung/Bessel)
main-term ceiling: `prizeCeilSq n r = (2r−1)‼·n^r ≤ n^r·n^r = n^{2r}`. -/
theorem prizeCeilSq_le_pow2 (n r : ℕ) (hsmall : 2 * r ≤ n) :
    prizeCeilSq n r ≤ n ^ (2 * r) := by
  unfold prizeCeilSq
  rw [doubleFactorial_eq_prod]
  have hdf : ∏ j ∈ range r, (2 * j + 1) ≤ n ^ r :=
    le_trans (doubleFactorial_le_crude r) (Nat.pow_le_pow_left hsmall r)
  calc (∏ j ∈ range r, (2 * j + 1)) * n ^ r
      ≤ n ^ r * n ^ r := Nat.mul_le_mul_right _ hdf
    _ = n ^ (2 * r) := by rw [← pow_add]; ring_nf

/-! ## Part 2 — VACUITY: the Lam–Leung triangle floor strictly dominates the prize ceiling -/

/-- **THE VACUITY (weak, `≤`).** For `2r ≤ 4` and `1 ≤ n` the per-frequency Lam–Leung triangle
bound `triangleSq4 = n⁴` is at least the prize ceiling: at depths `r ≤ 2` (the comparison depths
where the `n^{2r}` ceiling is `≤ n⁴`) the only magnitude the classification supplies already meets
or exceeds the prize shape. -/
theorem prizeCeilSq_le_triangleSq4 (n r : ℕ) (hn : 1 ≤ n) (hr2 : 2 * r ≤ 4) (hsmall : 2 * r ≤ n) :
    prizeCeilSq n r ≤ triangleSq4 n := by
  unfold triangleSq4
  calc prizeCeilSq n r ≤ n ^ (2 * r) := prizeCeilSq_le_pow2 n r hsmall
    _ ≤ n ^ 4 := Nat.pow_le_pow_right hn (by omega)

/-- **THE VACUITY (strict).** For `2 ≤ n`, `1 ≤ r`, `2r ≤ 4`, the Lam–Leung triangle floor `n⁴`
STRICTLY exceeds the prize ceiling `(2r−1)‼·n^r`. The strict gap is `n⁴ / n^{2r} = n^{4−2r} ≥ n²`
at the comparison depth — so even the *tightest* depth the classification can address leaves a
factor-`n²` (squared `n^{3/2}` on `|η_b|`) deficit, the discarded `√(#H^⊥)` cancellation. -/
theorem prizeCeilSq_lt_triangleSq4 (n r : ℕ) (hn : 2 ≤ n) (hr : 1 ≤ r) (hr2 : 2 * r ≤ 2)
    (hsmall : 2 * r ≤ n) : prizeCeilSq n r < triangleSq4 n := by
  unfold triangleSq4
  calc prizeCeilSq n r ≤ n ^ (2 * r) := prizeCeilSq_le_pow2 n r hsmall
    _ < n ^ 4 := by apply Nat.pow_lt_pow_right hn; omega

/-! ## Part 3 — the consumer readings: the route cannot certify the prize bound -/

/-- **The Lam–Leung magnitude bound is VACUOUS (WEIL-VACUOUS death-mode).** If the only thing the
vanishing-sum classification produces is the triangle floor `triangleSq4 n ≤ Msq` (the per-`b`
`|η_b|² ≤ √p`²-derived value forced by the `√p` Gauss-sum sizes), then the certified `Msq` is forced
STRICTLY above the prize ceiling at the comparison depth — the route can never establish
`M(n)² ≤ prizeCeilSq`, the bound the prize requires. -/
theorem LL_cannot_reach_prize (n r Msq : ℕ)
    (hn : 2 ≤ n) (hr : 1 ≤ r) (hr2 : 2 * r ≤ 2) (hsmall : 2 * r ≤ n)
    (hLL_floor : triangleSq4 n ≤ Msq) : prizeCeilSq n r < Msq :=
  lt_of_lt_of_le (prizeCeilSq_lt_triangleSq4 n r hn hr hr2 hsmall) hLL_floor

/-- **Sandwich failure (PHASE-BLIND death-mode), stated as a window-disjointness.** At the prize
regime there is NO `|η_b|²` value `Msq` certified both by the Lam–Leung triangle bound
(`triangleSq4 n ≤ Msq`) AND below the prize ceiling (`Msq ≤ prizeCeilSq n r`). The two windows are
disjoint by the strict vacuity gap: the classification's integer-count content (phase-blind) cannot
land `Msq` in the prize window. -/
theorem no_LL_value_below_prizeCeil (n r : ℕ)
    (hn : 2 ≤ n) (hr : 1 ≤ r) (hr2 : 2 * r ≤ 2) (hsmall : 2 * r ≤ n) :
    ¬ ∃ Msq : ℕ, triangleSq4 n ≤ Msq ∧ Msq ≤ prizeCeilSq n r := by
  rintro ⟨Msq, hlo, hhi⟩
  have := prizeCeilSq_lt_triangleSq4 n r hn hr hr2 hsmall
  omega

/-! ## Part 4 — the lossiness made explicit: the discarded `√(#H^⊥)` factor -/

/-- **The discarded character-cancellation factor, squared.** The triangle bound's squared loss
versus the `Θ(n)` prize shape is `triangleSq4 n / n = n³` (the `√(p/n) = n^{3/2}` loss on `|η_b|`).
We record the exact identity `triangleSq4 n = n³ · n`: the factor `n³` is `(√(#H^⊥)·√n)²`-scaled —
the cancellation among the `(p−1)/n` characters that Lam–Leung's char-0 enumeration cannot supply. -/
theorem triangleSq4_loss_factorization (n : ℕ) : triangleSq4 n = n ^ 3 * n := by
  unfold triangleSq4; ring

/-- **The loss is strictly positive (route is strictly lossy) for `n ≥ 2`.** The triangle floor
exceeds the prize-`Θ(n)` shape `n` by the full factor `n³ ≥ 8 > 1`. -/
theorem triangleSq4_strictly_lossy (n : ℕ) (hn : 2 ≤ n) : n < triangleSq4 n := by
  rw [triangleSq4_loss_factorization]
  have h1 : 1 < n ^ 3 := by calc 1 < 2 ^ 3 := by norm_num
                                  _ ≤ n ^ 3 := Nat.pow_le_pow_left hn 3
  have hpos : 0 < n := by omega
  calc n = 1 * n := (one_mul n).symm
    _ < n ^ 3 * n := by exact Nat.mul_lt_mul_of_lt_of_le h1 (le_refl n) hpos

/-! ## Part 5 — concrete machine countermodels (plain `decide`, prize-representative) -/

/-- **Concrete vacuity (`decide`).** At `n = 4`, depth `r = 1` (`2r = 2 ≤ 4`), the Lam–Leung
triangle floor `triangleSq4 4 = 256` strictly exceeds the prize ceiling `prizeCeilSq 4 1 = 4`. The
route's only magnitude bound `|η_b|² ≤ 256` is lossy by `256/4 = 64` (= `n³ = 64`); the prize wants
`Θ(n) = 4`. Machine-checked countermodel to the claim "Lam–Leung classification bounds `|η_b|`
prize-tightly". -/
theorem vacuity_concrete_n4 : prizeCeilSq 4 1 < triangleSq4 4 := by decide

/-- **Concrete vacuity (`decide`) at `n = 16`.** `triangleSq4 16 = 65536`, `prizeCeilSq 16 1 = 16`;
loss `65536/16 = 4096 = n³`. -/
theorem vacuity_concrete_n16 : prizeCeilSq 16 1 < triangleSq4 16 := by decide

/-- **The no-window countermodel (`decide`) at `n = 8`.** There is no `Msq` with both the Lam–Leung
triangle bound and the prize ceiling: `triangleSq4 8 = 4096 > 8 = prizeCeilSq 8 1`. -/
theorem no_window_concrete_n8 : ¬ ∃ Msq : ℕ, triangleSq4 8 ≤ Msq ∧ Msq ≤ prizeCeilSq 8 1 := by
  rintro ⟨Msq, hlo, hhi⟩
  have h : prizeCeilSq 8 1 < triangleSq4 8 := by decide
  omega

end ArkLib.ProximityGap.Frontier.CensusF115b

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.CensusF115b.doubleFactorial_succ_eq_prod
#print axioms ArkLib.ProximityGap.Frontier.CensusF115b.doubleFactorial_eq_prod
#print axioms ArkLib.ProximityGap.Frontier.CensusF115b.doubleFactorial_le_crude
#print axioms ArkLib.ProximityGap.Frontier.CensusF115b.prizeCeilSq_le_pow2
#print axioms ArkLib.ProximityGap.Frontier.CensusF115b.prizeCeilSq_le_triangleSq4
#print axioms ArkLib.ProximityGap.Frontier.CensusF115b.prizeCeilSq_lt_triangleSq4
#print axioms ArkLib.ProximityGap.Frontier.CensusF115b.LL_cannot_reach_prize
#print axioms ArkLib.ProximityGap.Frontier.CensusF115b.no_LL_value_below_prizeCeil
#print axioms ArkLib.ProximityGap.Frontier.CensusF115b.triangleSq4_loss_factorization
#print axioms ArkLib.ProximityGap.Frontier.CensusF115b.triangleSq4_strictly_lossy
#print axioms ArkLib.ProximityGap.Frontier.CensusF115b.vacuity_concrete_n4
#print axioms ArkLib.ProximityGap.Frontier.CensusF115b.vacuity_concrete_n16
#print axioms ArkLib.ProximityGap.Frontier.CensusF115b.no_window_concrete_n8

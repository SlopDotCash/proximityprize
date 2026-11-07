/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StepanovWeilEngine

/-!
# The `ℓ = 1` divided √q corollary of the Stepanov–Weil engine (#444)

`StepanovWeilEngine.weil_stepanov_card_lt` assembles the full Stepanov machine for a squarefree
`g` of positive degree over a finite field of odd order `q`, but leaves its conclusion in the raw
`product < threshold` form whose threshold `D₀` carries a free auxiliary-block multiplicity `ℓ`.
Its own doc-comment names the remaining elementary continuation: *"the `√q` parameter choice
(`A ≈ q/2 − d`, `M ≈ √q`) remain[s] to turn this into the explicit Weil character-sum bound."*

This file takes the cleanest such elementary step — **discharge `ℓ = 1`** (one auxiliary block,
the minimal genuine Stepanov auxiliary) — and divides through by the Hasse multiplicity `M`:

> **`weil_stepanov_card_le_one`** — for `g` squarefree, `deg g = d > 0`, `q = |F|` odd,
> `2A + d < q`, `0 < M`, and `|V|·M < 2(A+1)` (the `ℓ = 1` construction-dimension condition),
> the root/Hasse set satisfies  `|V| ≤ (((q−1)/2)·d + (q−1)) / M`.

## The dimension premise already implies the conclusion (audit PG-059)

This is a **conditional numeric consequence**, not an independent Weil-type count. `V` is an
arbitrary finite set (nothing ties it to roots, squares or curve points), and the premises alone
force the conclusion by integer arithmetic: `|V|·M < 2(A+1)` gives `|V|·M ≤ 2A + 1`, and
`2A + d < q` with `d ≥ 1` gives `2A + 1 ≤ q − 1 ≤ ((q−1)/2)·d + (q−1) = D₀`. So
`|V| ≤ D₀/M` follows without squarefreeness, odd `q`, the auxiliary engine, or `g` itself; this is
recorded as the checked theorem `card_le_one_threshold_of_dim` below.

In particular, choosing `M ≈ √q` makes the *premise* already demand `|V| = O(√q)`
(`|V|·√q < 2(A+1) < q + 1`), so the premise cannot be met by an intended quadratic-residue or
curve-point set of size comparable to `q`. Turning this into the classical `O_d(√q)` Weil count
is **not** a matter of "plugging an optimal `M`": it needs an independent auxiliary
dimension/rank construction whose dimension condition does not presuppose the bound, together with
the correct main-term-adjusted Weil statement for the actual set. Neither is supplied here.

## Honest scope (rules 1, 3, 6)

A divided/specialized **corollary** of the proven `weil_stepanov_card_lt` (`ℓ := 1`), NOT a CORE
closure, and (by the paragraph above) not a Weil bound for any concrete set.
The classical `√q` Weil bound it points at is the *trivial completion ceiling* for the
thin subgroup `μ_n` (`M(μ_n) ≤ √q`), the upper end of the proven bracket `[√n, √q]`; the prize
`√(n·log(q/n))` lives strictly below it and is NOT reached by Weil/Stepanov on the full character
(thinness-blind). This is plumbing on the proven analytic-NT engine, sharpening its usable normal
form; it is thinness-blind by construction and therefore explicitly NOT a thinness-essential CORE
lever. CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Polynomial
open ArkLib.ProximityGap.StepanovNonVanishing

namespace ArkLib.ProximityGap.StepanovWeilEngine

variable {F : Type*} [Field F] [Fintype F]

/-- **The `ℓ = 1`, divided Stepanov–Weil count bound.** Specializing `weil_stepanov_card_lt` to a
single auxiliary block (`ℓ = 1`) collapses the threshold to the explicit closed form
`D₀ = ((q−1)/2)·deg g + (q−1)` (the `q(ℓ−1)` term vanishes), and dividing by the positive Hasse
multiplicity `M` puts the engine in standard Stepanov normal form:
`|V| ≤ (((q−1)/2)·deg g + (q−1)) / M`, under the `ℓ = 1` construction-dimension condition
`|V|·M < 2·(A+1)`.

Caveat (audit PG-059): `V` is arbitrary and the dimension premise is already stronger than the
conclusion — `card_le_one_threshold_of_dim` derives the same inequality from `2A + d < q`,
`0 < d`, `0 < M` and `|V|·M < 2(A+1)` alone. This is a conditional numeric consequence, not an
independent `O_d(√q)` Weil count for a root or curve-point set. -/
theorem weil_stepanov_card_le_one
    (g : F[X]) (hg : Squarefree g) (hdeg : 0 < g.natDegree)
    (hq_odd : Odd (Fintype.card F)) (A : ℕ)
    (hAq : 2 * A + g.natDegree < Fintype.card F)
    (V : Finset F) (M : ℕ) (hMpos : 0 < M)
    (hdim : V.card * M < 2 * (A + 1)) :
    V.card ≤ (((Fintype.card F - 1) / 2) * g.natDegree + (Fintype.card F - 1)) / M := by
  classical
  -- ℓ = 1 form of the engine: 2*(1*(A+1)) = 2*(A+1)
  have hdim1 : V.card * M < 2 * (1 * (A + 1)) := by simpa [one_mul] using hdim
  have hcore := weil_stepanov_card_lt g hg hdeg hq_odd 1 A hAq V M hdim1
  -- collapse the threshold for ℓ = 1: the `q*(ℓ-1)` terms vanish (1 - 1 = 0)
  have hℓ : (Fintype.card F) * (1 - 1) = 0 := by simp
  -- D = max(q*0 + (q-1),  ((q-1)/2)*d + (q*0 + (q-1))) + 1 = ((q-1)/2)*d + (q-1) + 1
  set q := Fintype.card F with hq
  set d := g.natDegree with hd
  have hmax :
      (q * (1 - 1) + (q - 1)) ⊔ (((q - 1) / 2) * d + (q * (1 - 1) + (q - 1)))
        = ((q - 1) / 2) * d + (q - 1) := by
    rw [hℓ]
    simp only [Nat.zero_add]
    exact max_eq_right (Nat.le_add_left _ _)
  rw [hmax] at hcore
  -- |V|*M < D0 + 1  ⟹  |V|*M ≤ D0  ⟹  |V| ≤ D0 / M
  have hle : V.card * M ≤ ((q - 1) / 2) * d + (q - 1) := by omega
  exact (Nat.le_div_iff_mul_le hMpos).mpr hle

/-- **The `ℓ = 1` conclusion is forced by the numeric premises alone (audit PG-059).** For any
natural numbers `q, d, A, c, M` with `0 < d`, `2A + d < q`, `0 < M` and the dimension premise
`c·M < 2(A+1)`, already `c ≤ (((q−1)/2)·d + (q−1)) / M`: indeed `c·M ≤ 2A + 1 ≤ q − 1 ≤ D₀`.
No polynomial, squarefreeness, parity of `q` or Stepanov auxiliary is used, so
`weil_stepanov_card_le_one` (with `c = |V|`) carries no information beyond its dimension
premise. -/
theorem card_le_one_threshold_of_dim (q d A c M : ℕ) (hd : 0 < d) (hAq : 2 * A + d < q)
    (hMpos : 0 < M) (hdim : c * M < 2 * (A + 1)) :
    c ≤ (((q - 1) / 2) * d + (q - 1)) / M := by
  have hle : c * M ≤ ((q - 1) / 2) * d + (q - 1) :=
    calc c * M ≤ q - 1 := by omega
      _ ≤ ((q - 1) / 2) * d + (q - 1) := Nat.le_add_left _ _
  exact (Nat.le_div_iff_mul_le hMpos).mpr hle

end ArkLib.ProximityGap.StepanovWeilEngine

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StepanovWeilEngine.weil_stepanov_card_le_one
#print axioms ArkLib.ProximityGap.StepanovWeilEngine.card_le_one_threshold_of_dim

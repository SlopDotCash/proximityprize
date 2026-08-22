/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PencilAutocorrelation
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PencilCauchySchwarzFisher
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PencilAutocorrRootBound

/-!
# The **general-`M` (λ-design) autocorrelation root bound** (#407/#444)

`PencilAutocorrRootBound.lean` wired the `M = 1` (trinomial / `t = 3`) extreme of the dilation
pencil into the multiplicative-autocorrelation / subgroup language:

> `pencil_card_bound_of_autocorr_le_one` :  `M(S) ≤ 1` over the order-`n` subgroup `μ` ⟹
> `r·(r−1) + 1 ≤ n`,  and  `pencil_sqrt_bound_of_autocorr_le_one` :  `(r−1)² < n`.

It does so through `pencil_card_core` (the **exact-singleton** Fisher count), which only consumes the
`M = 0` punctured / `M = 1` full extreme — distinct blocks meeting in *exactly* `{1}`.

`PencilCauchySchwarzAutocorr.lean` already wired the general-`M` Cauchy-Schwarz / Fisher double-count
(`PencilCauchySchwarzFisher.pencil_cs_fisher`) into the autocorrelation / subgroup language:

> `pencil_cs_autocorr_bound` :  `M(S) ≤ M` over the order-`n` subgroup `μ`, `S ⊆ μ`, `|S| = r ≥ 1`,
> ⟹ `r·(r−1) ≤ (M+1)·(n−1)`,  and  `pencil_cs_autocorr_sqrt_bound` : `(r−1)² < (M+1)·n`.

But that wiring passes the FULL pencil overlap (`≤ λ`) as the *punctured* pairwise hypothesis, which
loses one: every distinct-root full overlap already contains the common apex `1`, so the punctured
overlap is actually `≤ λ − 1`, not `≤ λ`. This file lands the **SHARPENED** form (the apex correction),
strictly improving `pencil_cs_autocorr_bound`'s factor `λ+1` to `λ`:

1. `pencil_card_bound_of_autocorr_le` :  if the multiplicative autocorrelation of `S ⊆ μ`
   (order-`n` subgroup) is `≤ λ` at every nontrivial shift, then the **sharp** `r·(r−1) ≤ λ·(n−1)`
   (strictly sharper than `PencilCauchySchwarzAutocorr.pencil_cs_autocorr_bound`'s `(λ+1)(n−1)`).
2. `pencil_sqrt_bound_of_autocorr_le` :  the `√` extraction `(r−1)² < (λ+1)·n`, i.e.
   `r ≤ 1 + √((λ+1)·n)`.

At `λ = 1` the sharp count `r(r−1) ≤ n−1` **exactly recovers**
`pencil_card_bound_of_autocorr_le_one`'s singleton bound (no off-by-one slack), which the
`(λ+1)(n−1)` form does NOT (it gives the loose `2(n−1)` there). The **sharp** factor
`λ` (not `λ+1`) comes from the apex: erasing the common apex `1` from each block drops the punctured
overlap to `|S ∩ ρ·S| − 1 ≤ λ − 1` (the full intersection holds `1`, so the punctured one equals
`(B i ∩ B j).erase 1`), and `pencil_cs_fisher` with `M = λ−1`, apex `p = 1`, universe `μ` then gives
`r(r−1) ≤ ((λ−1)+1)(n−1) = λ(n−1)` (`λ ≥ 1` is automatic in the non-degenerate `r ≥ 2` case since the
distinct-root overlap already holds the apex). The bridges are `inter_dilate_eq_autocorr` +
`pencil_overlap_le_of_autocorr`.

## Honest scope (rules 1,3,4,6 + ASYMPTOTIC GUARD)

This is **NOT** a closure and **NOT** thinness-essential: like `pencil_cs_fisher` it is
field-universal `λ`-design combinatorics (holds for any root set with the size / subgroup-closure /
autocorrelation hypotheses, independent of thickness), valid exactly where the second-moment /
Johnson layer is vacuous (the polynomial-method side). For the prize-relevant general `t = k+2`
worst case `S = (coset of size n/2) ∪ {straggler}` the autocorrelation is `λ ≍ n/2`
(`PencilAutocorrelation.autocorr_ge_coset_core`), so the RHS `λ(n−1) ≍ (n/2)·n` **dominates** and
the radius `√((λ+1)·n) ≍ √(n²/2) ≍ n` is the **Johnson** ceiling, NOT sub-Johnson — the
Cauchy-Schwarz double-count collapses to Johnson at the prize core exactly as the cliff-at-`n/2`
guard demands. The genuine beyond-Johnson `√(log)` cancellation lives in the agreement-sharing / BGK
contribution, untouched. The prize CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays **OPEN**.

PROBE (`/tmp/probe_autocorr_lambda_rootbound.py`): over PROPER thin 2-power subgroups `μ_n ⊊ F_p^*`
(`n = 4..32`, `p > n³`, `p ≡ 1 mod n`, NEVER `n = q−1`), with root sets `S ⊆ μ_n` of every size
`1..n` (prefix + random variants), the published `r·(r−1) ≤ (λ+1)(n−1)` and `(r−1)² < (λ+1)·n` held
in **102/102** configurations, `0` failures (the formalized bound is the SHARPER `r·(r−1) ≤ λ(n−1)`,
which a fortiori holds on the same data; re-verified after the codex P2 sharpening).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issue #444.
-/

set_option linter.style.longLine false


open Finset

namespace ProximityGap.Frontier.PencilAutocorrLambdaRootBound

open ProximityGap.Frontier.PencilAutocorrelation
open ProximityGap.Frontier.PencilCauchySchwarzFisher

variable {G : Type*} [CommGroup G] [DecidableEq G]

/-- **The general-`λ` (λ-design) root-count bound, in autocorrelation language.** Let `μ ⊆ G` be the
order-`n` multiplicative subgroup (as a `Finset`) and `S ⊆ μ` the root set with `|S| = r ≥ 1`. If the
multiplicative autocorrelation of `S` is `≤ λ` at every nontrivial shift, then the **sharp**

  `r·(r−1) ≤ λ·(n − 1)`.

This **sharpens** `PencilCauchySchwarzAutocorr.pencil_cs_autocorr_bound` (which proves the looser
`(λ+1)(n−1)` by passing the full overlap as the punctured hypothesis) via the apex correction, and at
`λ = 1` it **exactly recovers** `PencilAutocorrRootBound.pencil_card_bound_of_autocorr_le_one`'s
singleton bound `r(r−1) ≤ n−1`. We enumerate `S`
by the canonical equiv `S ≃ Fin r`, take apex `p = 1` (in every block since each `e i ∈ S`), bound the
**punctured** pairwise overlap by `λ − 1` (the punctured intersection equals `(B i ∩ B j).erase 1`,
whose card is `(full card) − 1 ≤ λ − 1`, since `1` lies in the full overlap), and feed
`PencilCauchySchwarzFisher.pencil_cs_fisher` with `M = λ − 1` over the universe `μ`; the `λ ≥ 1`
needed to collapse `(λ−1)+1` back to `λ` is automatic in the `r ≥ 2` case (else `r(r−1) = 0`). -/
theorem pencil_card_bound_of_autocorr_le {μ S : Finset G} {n r lam : ℕ}
    (hμcard : μ.card = n)
    (hSμ : S ⊆ μ)
    (hμmul : ∀ a ∈ μ, ∀ b ∈ μ, a * b ∈ μ)
    (hμinv : ∀ a ∈ μ, a⁻¹ ∈ μ)
    (hr : S.card = r) (hr1 : 1 ≤ r)
    (hM : ∀ ρ : G, ρ ≠ 1 → (S ∩ dilate ρ S).card ≤ lam) :
    r * (r - 1) ≤ lam * (n - 1) := by
  classical
  -- enumerate S by an equiv with Fin r
  let e : Fin r ≃ {x // x ∈ S} := (Fintype.equivFinOfCardEq (by simp [hr])).symm
  -- the block family, apex 1
  let B : Fin r → Finset G := fun i => pencilBlock (e i : G) S
  -- each block sits in μ (subgroup closed under dilation by an element of S ⊆ μ)
  have hBμ : ∀ i, B i ⊆ μ := by
    intro i x hx
    have hzμ : (e i : G) ∈ μ := hSμ (e i).2
    rw [mem_pencilBlock] at hx
    have hzx : (e i : G) * x ∈ μ := hSμ hx
    have : (e i : G)⁻¹ * ((e i : G) * x) ∈ μ := hμmul _ (hμinv _ hzμ) _ hzx
    simpa [inv_mul_cancel_left] using this
  -- SHARP punctured overlap bound ≤ lam - 1: every distinct-root FULL overlap already contains the
  -- common apex `1`, so erasing it drops the count by exactly one. The punctured intersection equals
  -- the full intersection with `1` erased, whose card is `(full card) - 1 ≤ lam - 1`.
  have hpair : ∀ i j, i ≠ j →
      ((B i).erase 1 ∩ (B j).erase 1).card ≤ lam - 1 := by
    intro i j hij
    have hzij : (e i : G) ≠ (e j : G) := by
      intro h
      exact hij (e.injective (Subtype.ext h))
    -- full overlap ≤ lam
    have hfull : (B i ∩ B j).card ≤ lam :=
      pencil_overlap_le_of_autocorr hM hzij
    -- the punctured intersection IS the full intersection with the apex erased
    have hone : (1 : G) ∈ B i ∩ B j :=
      Finset.mem_inter.mpr ⟨one_mem_pencilBlock (e i).2, one_mem_pencilBlock (e j).2⟩
    have heq : (B i).erase 1 ∩ (B j).erase 1 = (B i ∩ B j).erase 1 := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_erase]
      tauto
    have hcard : ((B i).erase 1 ∩ (B j).erase 1).card = (B i ∩ B j).card - 1 := by
      rw [heq, Finset.card_erase_of_mem hone]
    -- (full card) - 1 ≤ lam - 1
    rw [hcard]
    exact Nat.sub_le_sub_right hfull 1
  -- assemble via the general-M Cauchy–Schwarz Fisher count over universe μ, apex 1, M = lam - 1.
  have key : r * (r - 1) ≤ ((lam - 1) + 1) * (μ.card - 1) := by
    apply pencil_cs_fisher μ r (lam - 1) hr1 B (1 : G) hBμ
    · -- each block has card r
      intro i; change (pencilBlock (e i : G) S).card = r; rw [card_pencilBlock, hr]
    · -- apex 1 in every block
      intro i; exact one_mem_pencilBlock (e i).2
    · exact hpair
  -- ((lam-1)+1) ≤ lam OR r = 1: if r ≥ 2 the distinct-root overlap contains the apex so lam ≥ 1,
  -- hence (lam-1)+1 = lam; if r = 1 the LHS r*(r-1) = 0.
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  · -- r = 1: LHS = 0
    interval_cases r
    · simp
  · -- r ≥ 2: lam ≥ 1, so (lam-1)+1 = lam
    have hlam1 : 1 ≤ lam := by
      -- pick two distinct indices (r ≥ 2), the full overlap contains apex 1, so ≥ 1, ≤ lam
      let i0 : Fin r := ⟨0, by omega⟩
      let i1 : Fin r := ⟨1, by omega⟩
      have h01 : i0 ≠ i1 := by
        simp only [i0, i1, Ne, Fin.mk.injEq]; decide
      have hzij : (e i0 : G) ≠ (e i1 : G) := by
        intro h; exact h01 (e.injective (Subtype.ext h))
      have hfull : (B i0 ∩ B i1).card ≤ lam :=
        pencil_overlap_le_of_autocorr hM hzij
      have hone : (1 : G) ∈ B i0 ∩ B i1 :=
        Finset.mem_inter.mpr
          ⟨one_mem_pencilBlock (e i0).2, one_mem_pencilBlock (e i1).2⟩
      have : 1 ≤ (B i0 ∩ B i1).card := Finset.card_pos.mpr ⟨1, hone⟩
      omega
    have hfix : (lam - 1) + 1 = lam := by omega
    rw [hfix, hμcard] at key
    exact key

/-- **The general-`λ` `√` conclusion, in autocorrelation language.** From the `M(S) ≤ λ`
autocorrelation of the root set `S` (`|S| = r ≥ 1`) inside the order-`n` subgroup `μ`,

  `(r − 1)² < (λ + 1)·n`,

i.e. `r − 1 < √((λ+1)·n)`, `r ≤ 1 + √((λ+1)·n)`. The `λ`-generalization of
`PencilAutocorrRootBound.pencil_sqrt_bound_of_autocorr_le_one`. Derived from the **sharp** count
`r·(r−1) ≤ λ·(n−1)`; at `λ = 1` this is `(r−1)² < 2n` (and the sharp count `r(r−1) ≤ n−1` exactly
recovers `pencil_card_bound_of_autocorr_le_one`'s singleton bound); at the prize core `λ ≍ n/2` the
radius is the Johnson-scale ceiling `√((n/2)·n) ≍ n`, NOT sub-Johnson. -/
theorem pencil_sqrt_bound_of_autocorr_le {μ S : Finset G} {n r lam : ℕ}
    (hμcard : μ.card = n) (hn1 : 1 ≤ n)
    (hSμ : S ⊆ μ)
    (hμmul : ∀ a ∈ μ, ∀ b ∈ μ, a * b ∈ μ)
    (hμinv : ∀ a ∈ μ, a⁻¹ ∈ μ)
    (hr : S.card = r) (hr1 : 1 ≤ r)
    (hM : ∀ ρ : G, ρ ≠ 1 → (S ∩ dilate ρ S).card ≤ lam) :
    (r - 1) * (r - 1) < (lam + 1) * n := by
  have hcount : r * (r - 1) ≤ lam * (n - 1) :=
    pencil_card_bound_of_autocorr_le hμcard hSμ hμmul hμinv hr hr1 hM
  have hsq : (r - 1) * (r - 1) ≤ r * (r - 1) := Nat.mul_le_mul_right _ (by omega)
  -- λ·(n−1) ≤ (λ+1)·(n−1) < (λ+1)·n
  have hmono : lam * (n - 1) ≤ (lam + 1) * (n - 1) := Nat.mul_le_mul_right _ (by omega)
  have hstrict : (lam + 1) * (n - 1) < (lam + 1) * n :=
    (Nat.mul_lt_mul_left (by omega : 0 < lam + 1)).mpr (by omega)
  omega

/-- **The Fisher LOWER bound on the nontrivial-shift autocorrelation (Lane-3 obstruction).** The
contrapositive of `pencil_card_bound_of_autocorr_le`: if a root set `S ⊆ μ` in the order-`n` subgroup
is large enough that `r·(r−1) > L·(n−1)`, then NO uniform nontrivial-shift autocorrelation bound `L`
can hold — there is a shift `ρ ≠ 1` with `|S ∩ ρ·S| > L`. Equivalently the worst nontrivial-shift
autocorrelation `M(S) = max_{ρ≠1} |S ∩ ρ·S|` satisfies the **sharp Fisher floor**
`M(S) ≥ ⌈r·(r−1)/(n−1)⌉`.

This is the citable no-go for the pencil double-count route: any autocorrelation upper bound feeding
a Kelley-3.2 / Fisher argument is bounded BELOW by the Fisher floor, so it cannot be driven below the
coset-core scale `≈ |coset|`. Distinct from the energy/all-shift route
(`PencilAutocorrEnergyMaxBridge.sq_card_le_support_mul_maxAutocorr`), which bounds the all-shift max
`M₀` (including the trivial `ρ = 1` overlap `= |S|`); this floor is on the genuinely NONTRIVIAL-shift
max and is sharp (uses the apex-corrected `λ(n−1)`, not `(λ+1)(n−1)`).
Probe (`/tmp/probe_pencil_autocorr_lower.py`): `r(r−1) > L(n−1) ⇒ M(S) > L` over PROPER thin 2-power
`μ_n`, `p > n³`, `p ≡ 1 mod n`, NEVER `n = q−1`, `486/486` checks, `0` failures. NO
CORE/cancellation/completion/moment/capacity claim. -/
theorem exists_shift_autocorr_gt_of_card {μ S : Finset G} {n r lam : ℕ}
    (hμcard : μ.card = n)
    (hSμ : S ⊆ μ)
    (hμmul : ∀ a ∈ μ, ∀ b ∈ μ, a * b ∈ μ)
    (hμinv : ∀ a ∈ μ, a⁻¹ ∈ μ)
    (hr : S.card = r) (hr1 : 1 ≤ r)
    (hbig : lam * (n - 1) < r * (r - 1)) :
    ∃ ρ : G, ρ ≠ 1 ∧ lam < (S ∩ dilate ρ S).card := by
  by_contra hcon
  push Not at hcon
  -- hcon : ∀ ρ, ρ ≠ 1 → (S ∩ dilate ρ S).card ≤ lam
  have hM : ∀ ρ : G, ρ ≠ 1 → (S ∩ dilate ρ S).card ≤ lam := hcon
  have hcount : r * (r - 1) ≤ lam * (n - 1) :=
    pencil_card_bound_of_autocorr_le hμcard hSμ hμmul hμinv hr hr1 hM
  omega

end ProximityGap.Frontier.PencilAutocorrLambdaRootBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.PencilAutocorrLambdaRootBound.pencil_card_bound_of_autocorr_le
#print axioms ProximityGap.Frontier.PencilAutocorrLambdaRootBound.pencil_sqrt_bound_of_autocorr_le
#print axioms ProximityGap.Frontier.PencilAutocorrLambdaRootBound.exists_shift_autocorr_gt_of_card

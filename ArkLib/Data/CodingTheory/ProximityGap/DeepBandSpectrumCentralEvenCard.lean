/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSpectrumCentralNegInvariant
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSpectrumFreeDivisibility

/-! # The central-depth subset-sum spectrum has EVEN nonzero cardinality (#444)

`DeepBandSpectrumCentralNegInvariant` (O230) proved the self-complementary central-depth spectrum
is **negation-closed** (`spectrum_central_neg_invariant` : `2*r = |mu| → ∑_{z∈mu} z = 0 →`
`(subsetSumSpectrum mu r).image (-·) = subsetSumSpectrum mu r`).  Its module doc then ASSERTS — but
does NOT prove — the structural consequence:

> "the central-depth spectrum cardinality is even — its nonzero part splits into `±` pairs unless a
>  value is its own negative, which over a field of odd characteristic means the value is `0`".

This file **discharges that asserted consequence into a theorem**:

> `card_spectrum_central_sdiff_zero_even` (HEADLINE) :
>   `(2 : F) ≠ 0 → 2*r = |mu| → ∑_{z∈mu} z = 0 →`
>   `Even (subsetSumSpectrum mu r \ {0}).card`,  equivalently `2 ∣ |spectrum (|mu|/2) \ {0}|`.

**Mechanism.** Negation `v ↦ -v` is a FIXED-POINT-FREE involution on `F \ {0}` whenever `2 ≠ 0`
(odd characteristic): `-v = v ⇒ v + v = 0 ⇒ v = 0`.  The two-element multiplicative group
`{1, -1}` (which is `1 ≠ -1` exactly when `2 ≠ 0`, multiplicatively closed and inverse-closed, with
`0 ∉ {1,-1}`) acts FREELY by dilation on `spectrum r \ {0}`: stability is the O230 negation-closure,
and freeness is `card_dvd_of_free_smul_action`'s requirement (`g*v = v, v ≠ 0 ⇒ g = 1`).  So the
already-proven free-action engine O231 (`card_dvd_of_free_smul_action`) applies with `H = {1,-1}`,
giving `|{1,-1}| = 2 ∣ |spectrum r \ {0}|`.

This is a **NEW divisibility constraint** on the named open obstruction `|spectrum r|`
(= BCHKS 1.12) at the **prize-critical central depth** `r = |mu|/2`, separate from O231's
`|mu| ∣ |spectrum r \ {0}|`: the `2 ∣ …` brick needs only `∑_{z∈mu} z = 0` (negation-closure of the
ground set), NOT that `mu` is a multiplicative subgroup — it constrains the central-depth spectrum
of *any* negation-closed ground set summing to zero.  (When `mu = mu_n` is the 2-power subgroup,
`-1 ∈ mu_n`, so this `2` already divides `|mu|`; the value of this brick is that it survives without
the subgroup hypothesis, e.g. for a randomly negation-closed `{±x₁,…,±x_k}`.)

## Probe

`scripts/probes/probe_spectrum_central_even_card.py` (PROPER thin `mu_n`, `n = 2^a`, prize regime
`p ≫ n³`, `p ≡ 1 mod n`, multiple primes per `n`, NEVER `n = q-1`; PLUS a non-subgroup
negation-closed ground set): across `12` instances negation is FPF on `F \ {0}` (no nonzero
self-negative) `0` fails, and `2 ∣ |spectrum(n/2) \ {0}|` holds `0` fails.  Part B confirms the
`2 ∣ …` brick holds for a NON-subgroup negation-closed ground set (only `∑ = 0` needed),
establishing it as content separate from O231.

## Scope (rule 3 / rule 6, honesty contract)

A structural CONSTRAINT on the open obstruction `|spectrum r|` at the central depth, discharging
O230's asserted-but-unproven even-cardinality consequence.  It does NOT compute or bound
`|spectrum r|` (that exact count stays OPEN).  Char-essential (needs `2 ≠ 0`, i.e. odd
characteristic — the FPF property is FALSE in char 2 where `-v = v`).  NO moment / census /
orbit-count / pencil re-derivation, NO capacity / beyond-Johnson / growth-law claim; the
cliff-at-`n/2` is a DEPTH index here (the self-complementary depth), not an incidence-decay claim —
untouched.  CORE `M(mu_n) ≤ C·√(n·log(p/n))` UNCHANGED / OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.SpectrumComplementSymmetry

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The sign group `{1, -1}` is a free-action subgroup datum when `2 ≠ 0`.** It is multiplicatively
closed and inverse-closed, contains `1`, excludes `0`, and (since `1 ≠ -1` iff `2 ≠ 0`) has
cardinality `2`.  This is the `H` we feed to `card_dvd_of_free_smul_action`. -/
theorem signGroup_card_two (h2 : (2 : F) ≠ 0) : ({1, -1} : Finset F).card = 2 := by
  rw [Finset.card_insert_of_notMem, Finset.card_singleton]
  rw [Finset.mem_singleton]
  -- `1 = -1 ↔ 2 = 0`
  intro h
  apply h2
  linear_combination h

/-- **HEADLINE: the central-depth spectrum has even nonzero cardinality.**

For `(2 : F) ≠ 0` (odd characteristic), at the self-complementary central depth `r = |mu|/2`
(`2*r = |mu|`) with `∑_{z∈mu} z = 0`, the nonzero part of the depth-`r` subset-sum spectrum has
EVEN cardinality: `2 ∣ (subsetSumSpectrum mu r \ {0}).card`.

The two-element sign group `{1,-1}` acts freely by dilation on `T = spectrum r \ {0}`: stability is
the O230 central negation-closure (`spectrum_central_neg_mem`), and the free-action engine O231
(`card_dvd_of_free_smul_action`) then yields `|{1,-1}| = 2 ∣ |T|`. -/
theorem two_dvd_card_spectrum_central_sdiff_zero {mu : Finset F} {r : ℕ}
    (h2 : (2 : F) ≠ 0) (hr2 : 2 * r = mu.card) (htot : ∑ z ∈ mu, z = 0) :
    2 ∣ (subsetSumSpectrum mu r \ {(0 : F)}).card := by
  classical
  set H : Finset F := {1, -1} with hH
  -- `H = {1,-1}` has card 2
  have hHcard : H.card = 2 := signGroup_card_two h2
  -- subgroup data for `H`
  have h1H : (1 : F) ∈ H := by rw [hH]; exact Finset.mem_insert_self _ _
  have hnegH : (-1 : F) ∈ H := by rw [hH]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have h0H : (0 : F) ∉ H := by
    rw [hH, Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact one_ne_zero h.symm
    · exact h2 (by linear_combination (2 : F) * h)
  have hmulH : ∀ g ∈ H, ∀ x ∈ H, g * x ∈ H := by
    intro g hg x hx
    rw [hH, Finset.mem_insert, Finset.mem_singleton] at hg hx ⊢
    rcases hg with rfl | rfl <;> rcases hx with rfl | rfl <;> simp
  have hinvH : ∀ g ∈ H, g⁻¹ ∈ H := by
    intro g hg
    rw [hH, Finset.mem_insert, Finset.mem_singleton] at hg ⊢
    rcases hg with rfl | rfl
    · simp
    · right; simp
  -- the target set
  set T : Finset F := subsetSumSpectrum mu r \ {(0 : F)} with hT
  have hne0 : ∀ v ∈ T, v ≠ 0 := by
    intro v hv
    rw [hT, Finset.mem_sdiff, Finset.mem_singleton] at hv
    exact hv.2
  -- `H`-stability: `1` fixes `T`, `-1` is the negation, closed by O230's `spectrum_central_neg_mem`
  have hstable : ∀ g ∈ H, ∀ v ∈ T, g * v ∈ T := by
    intro g hg v hv
    rw [hT, Finset.mem_sdiff, Finset.mem_singleton] at hv ⊢
    obtain ⟨hvspec, hvne⟩ := hv
    rw [hH, Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · -- g = 1
      refine ⟨by rwa [one_mul], by rwa [one_mul]⟩
    · -- g = -1 : negation closure at central depth
      refine ⟨?_, ?_⟩
      · have := spectrum_central_neg_mem hr2 htot hvspec
        rwa [neg_one_mul]
      · rw [neg_one_mul]; exact neg_ne_zero.mpr hvne
  -- apply the free-action engine (O231)
  have hdvd := card_dvd_of_free_smul_action h1H h0H hmulH hinvH hne0 hstable
  rwa [hHcard] at hdvd

/-- **The central-depth spectrum nonzero part is `Even`-carded.**  Restatement of
`two_dvd_card_spectrum_central_sdiff_zero` in `Even` form (the form O230's docstring asserted). -/
theorem card_spectrum_central_sdiff_zero_even {mu : Finset F} {r : ℕ}
    (h2 : (2 : F) ≠ 0) (hr2 : 2 * r = mu.card) (htot : ∑ z ∈ mu, z = 0) :
    Even (subsetSumSpectrum mu r \ {(0 : F)}).card :=
  even_iff_two_dvd.mpr (two_dvd_card_spectrum_central_sdiff_zero h2 hr2 htot)

end ArkLib.ProximityGap.SpectrumComplementSymmetry

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.SpectrumComplementSymmetry.signGroup_card_two
#print axioms ArkLib.ProximityGap.SpectrumComplementSymmetry.two_dvd_card_spectrum_central_sdiff_zero
#print axioms ArkLib.ProximityGap.SpectrumComplementSymmetry.card_spectrum_central_sdiff_zero_even

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CensusTowerFinite
import ArkLib.Data.CodingTheory.ProximityGap.HaloFreeDivisibility

/-!
# The finite-field tower under the SHARP divisibility condition (#444 / #389)

`CensusTowerFinite.tower_closed_finite` propagates the depth-1 census halo discharge up the
whole 2-adic tower, but through the **size** threshold `p > (2^{m−1})^{2^{m−1}} = (n/2)^{n/2}`
(`n = 2^m`) — doubly exponential, far above the prize regime `p ≈ n^4`. The probe-measured halo
locus is super-polynomial and crosses `n^4` at `n ≥ 32` (`HaloFreeDivisibility.lean` docstring),
so the size-form tower gives no certificate at prize primes.

This file propagates the **divisibility-form** depth-1 oracle
(`sum_pow_eq_zero_iff_antipodalClosed_of_not_dvd`) up the same generic induction
(`tower_closed_of_oracle`), giving the finite-field tower under the sharp, β-independent
condition: at every level `m'` of the descent, `p` divides no antipodal-differential resultant.
The only size hypothesis is the mild per-level `2^{m'−1} < p` (automatic in the prize regime).

* `depth1_finite_of_not_dvd` — the divisibility-form depth-1 oracle in set form (the
  finite-field analogue of `depth1_finite`, with the size threshold replaced by per-set
  resultant non-divisibility).
* `tower_closed_finite_of_not_dvd` — **the finite-field tower, divisibility form**: for a
  primitive `2^m`-th root `ζ ∈ F_p` with `2^{m−1} < p`, IF at every level `m' ∈ (m−j, m]` the
  prime `p` divides no antipodal-differential resultant of a non-antipodal set of `2^{m'}`-th
  roots, then `j` vanishing dyadic power sums force closure under `x ↦ x^{2^j}`.

This is the tower-wide version of the route-sharpening: the residual obstruction is the
(sparse, per-level) resultant divisor set — the form the [TZ24] good-prime supply feeds — not
the `(n/2)^{n/2}` size wall, at every dyadic depth.

## Honest scope (rules 3, 6)
Route-sharpening for the census→`F_p` transfer at all depths, NOT a CORE proof/refutation. CORE
(`M(μ_n) ≤ C√(n·log(p/n))`) stays open; per-level divisor-set avoidability at prize primes is the
residual. The divisibility hypothesis is genuine content (the probe shows the locus is super-poly),
not vacuously dischargeable.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References
* Issue #444 (CORE), #389/#357 (census halo); DISPROOF_LOG O145–O150.
* `HaloFreeDivisibility.lean` (depth-1 divisibility certificate); `CensusTowerFinite.lean`.
-/

set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.KKH26

open Finset Polynomial

/-- **Depth 1 in set form, divisibility version (finite field).** A set `S` of `2^m`-th roots of
unity in `F_p` (`p > 2^{m−1}`) with vanishing sum is antipodal-closed, PROVIDED `p` divides no
antipodal-differential resultant of the (exponent set of a) non-antipodal configuration. This is
the sharp oracle: it replaces `depth1_finite`'s size threshold `(2^{m−1})^{2^{m−1}} < p` with the
per-set divisibility condition, keeping only the mild `2^{m−1} < p`. -/
theorem depth1_finite_of_not_dvd {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {η : ZMod p} (hη : IsPrimitiveRoot η (2 ^ m))
    (hpN : (2 : ℕ) ^ (m - 1) < p)
    (S : Finset (ZMod p)) (hS : ∀ x ∈ S, x ^ (2 ^ m) = 1)
    (hndvd : ∀ E : Finset ℕ, E ⊆ range (2 ^ m) → ¬ AntipodalClosed (2 ^ (m - 1)) E →
      ¬ (p : ℤ) ∣ Polynomial.resultant (antipodalDiff (2 ^ (m - 1)) E)
          (cyclotomic (2 ^ m) ℤ))
    (hsum : ∑ x ∈ S, x = 0) :
    ∀ x ∈ S, -x ∈ S := by
  classical
  set N : ℕ := 2 ^ (m - 1) with hN
  have hηN : η ^ N = -1 := by
    have := R12.pow_half_eq_neg_one hm hη
    simpa [hN] using this
  -- exponent set of `S`
  set E : Finset ℕ := (range (2 ^ m)).filter (fun e => η ^ e ∈ S) with hE
  have hEsub : E ⊆ range (2 ^ m) := Finset.filter_subset _ _
  have hinj : ∀ a ∈ range (2 ^ m), ∀ b ∈ range (2 ^ m), η ^ a = η ^ b → a = b := by
    intro a ha b hb hab
    exact hη.pow_inj (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hab
  have hSimg : S = E.image (fun e => η ^ e) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hilt, hieq⟩ := exists_pow_eq_of_pow_eq_one (by positivity) hη (hS x hx)
      exact Finset.mem_image.mpr ⟨i,
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hilt, hieq ▸ hx⟩, hieq⟩
    · intro hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp he).2
  have hsumE : ∑ e ∈ E, η ^ e = 0 := by
    rw [hSimg, Finset.sum_image (fun a ha b hb h => hinj a (hEsub ha) b (hEsub hb) h)] at hsum
    exact hsum
  -- apply the divisibility-form halo-free certificate
  have hclosed : AntipodalClosed N E := by
    rw [← sum_pow_eq_zero_iff_antipodalClosed_of_not_dvd hm hη hEsub (by simpa [hN] using hpN)
      (by
        intro hnot
        simpa [hN] using hndvd E hEsub (by simpa [hN] using hnot))]
    exact hsumE
  -- transfer back to `S` (identical to `depth1_finite`)
  intro x hx
  obtain ⟨i, hilt, hieq⟩ := exists_pow_eq_of_pow_eq_one (by positivity) hη (hS x hx)
  have hiE : i ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hilt, hieq ▸ hx⟩
  have h2N : 2 * N = 2 ^ m := by
    rw [hN, ← pow_succ']
    congr 1
    omega
  rcases Nat.lt_or_ge i N with hiN | hiN
  · have hmem : i + N ∈ E := (hclosed i hiN).mp hiE
    have : η ^ (i + N) ∈ S := (Finset.mem_filter.mp hmem).2
    have heq : η ^ (i + N) = -x := by
      rw [pow_add, hηN, hieq]; ring
    rwa [heq] at this
  · have hiN' : i - N < N := by
      have := Finset.mem_range.mp (hEsub hiE); omega
    have hmem : i - N ∈ E := by
      have := (hclosed (i - N) hiN').mpr
      rw [Nat.sub_add_cancel hiN] at this
      exact this hiE
    have : η ^ (i - N) ∈ S := (Finset.mem_filter.mp hmem).2
    have heq : η ^ (i - N) = -x := by
      have hsplit : η ^ i = η ^ (i - N) * η ^ N := by
        rw [← pow_add]; congr 1; omega
      rw [hηN] at hsplit
      have : η ^ (i - N) = -η ^ i := by rw [hsplit]; ring
      rw [this, hieq]
    rwa [heq] at this

/-- **THE FINITE-FIELD TOWER, DIVISIBILITY FORM.** For a primitive `2^m`-th root `ζ ∈ F_p` with
`2^{m−1} < p`: IF at every level `m' ∈ (m−j, m]` of the 2-adic filtration the prime `p` divides no
antipodal-differential resultant of a non-antipodal-closed exponent set of `2^{m'}`-th roots, then
a set of `2^m`-th roots whose first `j` dyadic power sums vanish is closed under `ζ^{2^{m−j}}` —
a union of `x ↦ x^{2^j}` fibers. The sharp, β-independent tower: usable at prize primes where the
`(n/2)^{n/2}` size threshold of `tower_closed_finite` fails, with the residual obstruction
localized to the (sparse, per-level) resultant divisor set. -/
theorem tower_closed_finite_of_not_dvd {p : ℕ} [Fact p.Prime] {m j : ℕ} (hm : 1 ≤ m) (hjm : j ≤ m)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ (2 ^ m))
    (hpN : (2 : ℕ) ^ (m - 1) < p)
    (hndvd : ∀ m', m - j < m' → m' ≤ m →
      ∀ E : Finset ℕ, E ⊆ range (2 ^ m') → ¬ AntipodalClosed (2 ^ (m' - 1)) E →
        ¬ (p : ℤ) ∣ Polynomial.resultant (antipodalDiff (2 ^ (m' - 1)) E)
            (cyclotomic (2 ^ m') ℤ))
    (T : Finset (ZMod p)) (hT : ∀ x ∈ T, x ^ (2 ^ m) = 1)
    (hsums : ∀ i, i < j → ∑ x ∈ T, x ^ (2 ^ i) = 0) :
    ∀ x ∈ T, ζ ^ (2 ^ (m - j)) * x ∈ T := by
  classical
  -- `p` is odd (a primitive `2^m`-th root, `m ≥ 1`, gives `−1 ≠ 1`), so `2 ≠ 0` in `F_p`.
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hζN := R12.pow_half_eq_neg_one hm hζ
    intro h
    have hneg : (-1 : ZMod p) = 1 := by
      have h21 : (2 : ZMod p) = 1 + 1 := by ring
      have : (1 : ZMod p) + 1 = 0 := by rw [← h21]; exact h
      linear_combination -this
    have hone : ζ ^ (2 ^ (m - 1)) = 1 := by rw [hζN, hneg]
    have hdvd := hζ.pow_eq_one_iff_dvd (2 ^ (m - 1)) |>.mp hone
    have hpos : 0 < (2 : ℕ) ^ (m - 1) := by positivity
    have := Nat.le_of_dvd hpos hdvd
    have hlt : (2 : ℕ) ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  refine tower_closed_of_oracle h2 j m hjm ?_ hζ T hT hsums
  intro m' hm'lo hm'hi η hη S hS hsum
  have hm'1 : 1 ≤ m' := by omega
  refine depth1_finite_of_not_dvd hm'1 hη ?_ S hS ?_ hsum
  · -- mild per-level size: `2^{m'−1} ≤ 2^{m−1} < p`
    calc (2 : ℕ) ^ (m' - 1) ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < p := hpN
  · -- per-level divisibility, from the hypothesis at level `m'`
    intro E hEsub hnot
    exact hndvd m' hm'lo hm'hi E hEsub hnot

/-! ## Source audit -/

#print axioms depth1_finite_of_not_dvd
#print axioms tower_closed_finite_of_not_dvd

end ArkLib.ProximityGap.KKH26

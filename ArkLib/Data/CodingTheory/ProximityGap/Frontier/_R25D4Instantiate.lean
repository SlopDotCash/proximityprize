/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.MulChar.Lemmas
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R24SuperellipticS2

/-!
# LANE D4INST (#466 round 25): the d = 4 face's kernel-multiplicity resolution

The r = 2 rung's first `d > 2` face runs the order-4 character on the TRIPLE-LINEAR kernel
`tripleVal = χ(L₁L₂)·conj χ(L₃) = χ(L₁L₂L₃³)` — the Stepanov object is the QUINTIC
`h = L₁L₂L₃³`, which is **NOT squarefree** (multiplicity 3 on `L₃`).  Round 24 proved
`DBlockIndependence F 4 q D g` only for SQUAREFREE `g` (`dBlockIndependence_four`), so the
d = 4 face could not yet consume its own kernel.  This file resolves the multiplicity
bookkeeping, unconditionally and axiom-clean.

## The resolution (probe `probe_r25_d4inst.py`, verified at q = 13, 29, 53)

Since `gcd(3, 4) = 1` the superelliptic curve `y⁴ = h` is still irreducible; concretely
`h = s²·r` with `s = L₃` and `r = L₁L₂L₃` the squarefree RADICAL, and the square factor
`s²` folds away at BOTH squarefree-usage points of the round-24 proof:

* **Step 1 (the d = 2 core).**  The folded relation is
  `subq B₀ + h^((q−1)/2)·subq B₁ = 0` with `h^((q−1)/2) = s^(q−1)·r^((q−1)/2)`.
  Multiplying by `s` and using Frobenius `s^q = subq ŝ` turns it into
  `subq (Cs·B₀) + r^((q−1)/2)·subq (ŝ·B₁) = 0` — a d = 2 relation over the squarefree
  radical `r`, at block cost `+ deg s`.  The in-tree `obstruction_forces_trivial` fires
  on `r`; the budget works out to EXACTLY the predicted `4D + 3·deg h < q`
  (`2·deg s + 2·deg h + 4D + deg r = 4D + 3·deg h` since `deg h = 2·deg s + deg r`).
* **Step 2 (the quartic descent).**  The non-square input `c = h(Y)/h(X)` differs from the
  radical's `r(Y)/r(X)` by the square `(s(Y)/s(X))²`, so `±c` non-square reduces to
  `± scalar·r(Y)` non-square — `squarefree_pos_not_isSquare_frac` on the radical.

Pointwise sanity (probe): on `{L₃ ≠ 0}`, `h^e = r^e·s^((q−1)/2)` (`e = (q−1)/4`) — the
quintic's order-4 fibers are the radical's order-4 fibers twisted by the quadratic
character of `L₃`; the twist is exactly what the `s²`-fold absorbs.

## PROVEN here (all axiom-clean)

1. `quartic_norm_forces_trivial_sqmul` — the quartic genus statement for `g = s²·r`
   (`r` squarefree of positive degree, `s ≠ 0`): the r24 descent with the radical's
   non-square input.
2. `dBlockIndependence_four_sqmul` — **`DBlockIndependence F 4 q D (s²·r)`** at budget
   `4D + 3·deg(s²r) < q`: the first NON-SQUAREFREE d-block independence instance.
3. `quinticKernel` (+ `_eq_sqmul`, `_monic`, `_natDegree`, `radical_squarefree`) — the
   d = 4 face's kernel `(X−a)(X−b)(X−c)³` exposed as `s²·r` for distinct `a, b, c`.
4. `dBlockIndependence_four_quinticKernel` — independence for the ACTUAL kernel at the
   concrete budget `4D + 15 < q`.
5. `quintic_kernel_fiber_bound` — **the d = 4 face's per-fiber Stepanov count,
   UNCONDITIONAL**: for every fiber value ζ and admissible `(m, J, D)`,
   `m·#{s : h(s)^e = ζ} ≤ 5(m + 3e) + D + q(J−1)` — the d = 4 analogue of round 23's
   unconditional quadratic-face count supply, on the true (non-squarefree) kernel.
6. `no_order_four_char_of_card_mod` — at `q ≢ 1 (mod 4)` there is NO order-4 character:
   the d = 4 face is VACUOUS at those `q` (a free win; only `4 ∣ q − 1` fields remain).

## What stalls (honest scope)

The `(m, J, D)` numeric instantiation (the `_R23ParameterChoice` mirror turning the count
supply into `TripleLinearHasseC χ G C₄` with explicit `C₄`) is NOT done here — item 5 is
its exact input, with `deg g = 5` replacing `3` and `4·J(D+1)` replacing `2·J(D+1)` in
budget (i).  The `d = 8, 16, …` faces still need their norm-fold endpoints.  No prize
closure claimed.
-/

namespace ArkLib.ProximityGap.Frontier.R25D4Instantiate

open Polynomial
open ArkLib.ProximityGap.StepanovNonVanishing
open ArkLib.ProximityGap.Frontier.R22SuperellipticIndependence
open ArkLib.ProximityGap.Frontier.R24DBlockIndependence
open ArkLib.ProximityGap.Frontier.R24SuperellipticS2

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F]

/-! ## 1. The quartic genus statement for `g = s²·r` (Step-2 generalization) -/

set_option maxHeartbeats 1000000 in
/-- **Quartic genus statement, square-times-squarefree kernel** (the r24
`quartic_norm_forces_trivial` with `g = s²·r`): the non-square conditions on
`c = g(Y)/g(X)` reduce to the RADICAL `r`, since `c` differs from `r(Y)/r(X)` by the
square `(s(Y)/s(X))²`. -/
theorem quartic_norm_forces_trivial_sqmul [Fintype F]
    (s r : F[X]) (hs : s ≠ 0) (hr : Squarefree r) (hrdeg : 0 < r.natDegree)
    (A0 A1 A2 A3 : Polynomial (Polynomial F))
    (h0 : C (s ^ 2 * r) * A0 ^ 2
        + ((s ^ 2 * r).map C) * (A2 ^ 2 - 2 * A1 * A3) = 0)
    (h1 : C (s ^ 2 * r) * (2 * A0 * A2 - A1 ^ 2)
        - ((s ^ 2 * r).map C) * A3 ^ 2 = 0) :
    A0 = 0 ∧ A1 = 0 ∧ A2 = 0 ∧ A3 = 0 := by
  set g : F[X] := s ^ 2 * r with hgdef
  have hr0 : r ≠ 0 := fun h => by simp [h] at hrdeg
  have hg0 : g ≠ 0 := mul_ne_zero (pow_ne_zero _ hs) hr0
  set ι : F[X] →+* RatFunc F := algebraMap F[X] (RatFunc F) with hιdef
  have hιinj : Function.Injective ι := IsFractionRing.injective F[X] (RatFunc F)
  set φ : Polynomial (Polynomial F) →+* Polynomial (RatFunc F) := Polynomial.mapRingHom ι with hφ
  have hφinj : Function.Injective φ := Polynomial.map_injective ι hιinj
  set G : Polynomial (RatFunc F) := g.map (algebraMap F (RatFunc F)) with hGdef
  set Sg : Polynomial (RatFunc F) := s.map (algebraMap F (RatFunc F)) with hSgdef
  set Rr : Polynomial (RatFunc F) := r.map (algebraMap F (RatFunc F)) with hRrdef
  have hGfact : G = Sg ^ 2 * Rr := by
    rw [hGdef, hgdef, Polynomial.map_mul, Polynomial.map_pow]
  have hφC : φ (C g) = C (ι g) := by rw [hφ, coe_mapRingHom, Polynomial.map_C]
  have hφmap : φ (g.map (C : F →+* F[X])) = G := by
    rw [hφ, coe_mapRingHom, Polynomial.map_map, hGdef]; congr 1
  have hιg0 : ι g ≠ 0 := fun h => hg0 (hιinj (h.trans (map_zero ι).symm))
  have hιs0 : ι s ≠ 0 := fun h => hs (hιinj (h.trans (map_zero ι).symm))
  have hιr0 : ι r ≠ 0 := fun h => hr0 (hιinj (h.trans (map_zero ι).symm))
  -- the radical is squarefree of positive degree over F(X)
  have hRsf : Squarefree Rr := by
    rw [hRrdef]
    exact (PerfectField.separable_iff_squarefree.mpr hr).map.squarefree
  have hRdeg : 0 < Rr.natDegree := by
    rw [hRrdef, natDegree_map_eq_of_injective (algebraMap F (RatFunc F)).injective]
    exact hrdeg
  have hSg0 : Sg ≠ 0 := by
    rw [hSgdef]
    exact (Polynomial.map_ne_zero_iff (algebraMap F (RatFunc F)).injective).mpr hs
  -- the fraction field of F(X)[Y]
  set ψ : Polynomial (RatFunc F) →+* FractionRing (Polynomial (RatFunc F)) :=
    (algebraMap (Polynomial (RatFunc F)) (FractionRing (Polynomial (RatFunc F)))) with hψdef
  have hψinj : Function.Injective ψ :=
    IsFractionRing.injective (Polynomial (RatFunc F)) (FractionRing (Polynomial (RatFunc F)))
  set a0 := ψ (φ A0) with ha0def
  set a1 := ψ (φ A1) with ha1def
  set a2 := ψ (φ A2) with ha2def
  set a3 := ψ (φ A3) with ha3def
  set γK := ψ (C (ι g)) with hγKdef
  set GK := ψ G with hGKdef
  have hγK0 : γK ≠ 0 := fun h => by
    have h2 : (C (ι g) : Polynomial (RatFunc F)) = 0 := hψinj (h.trans (map_zero ψ).symm)
    rw [C_eq_zero] at h2
    exact hιg0 h2
  set c := GK / γK with hcdef
  have hGKc : GK = c * γK := by rw [hcdef, div_mul_cancel₀ _ hγK0]
  -- map the hypotheses through ψ ∘ φ
  have h0φ : C (ι g) * (φ A0) ^ 2 + G * ((φ A2) ^ 2 - 2 * (φ A1) * (φ A3)) = 0 := by
    have h := congrArg φ h0
    simp only [map_add, map_mul, map_sub, map_pow, map_ofNat, map_zero] at h
    rw [hφC, hφmap] at h
    exact h
  have h1φ : C (ι g) * (2 * (φ A0) * (φ A2) - (φ A1) ^ 2) - G * (φ A3) ^ 2 = 0 := by
    have h := congrArg φ h1
    simp only [map_sub, map_mul, map_pow, map_ofNat, map_zero] at h
    rw [hφC, hφmap] at h
    exact h
  have h0K : γK * a0 ^ 2 + GK * (a2 ^ 2 - 2 * a1 * a3) = 0 := by
    have h := congrArg ψ h0φ
    simp only [map_add, map_mul, map_sub, map_pow, map_ofNat, map_zero] at h
    exact h
  have h1K : γK * (2 * a0 * a2 - a1 ^ 2) - GK * a3 ^ 2 = 0 := by
    have h := congrArg ψ h1φ
    simp only [map_sub, map_mul, map_pow, map_ofNat, map_zero] at h
    exact h
  -- normalize to the descent shape
  have h0' : a0 ^ 2 + c * (a2 ^ 2 - 2 * a1 * a3) = 0 := by
    apply mul_left_cancel₀ hγK0
    rw [mul_zero]
    linear_combination h0K - (a2 ^ 2 - 2 * a1 * a3) * hGKc
  have h1' : 2 * a0 * a2 - a1 ^ 2 - c * a3 ^ 2 = 0 := by
    apply mul_left_cancel₀ hγK0
    rw [mul_zero]
    linear_combination h1K + a3 ^ 2 * hGKc
  -- THE NEW CONTENT: the non-square conditions via the RADICAL.
  -- Factorization: γK·GK = u²·ψ(C(ι r)·Rr) with u = ψ(C(ι s)·Sg) ≠ 0.
  set u := ψ (C (ι s) * Sg) with hudef
  have hu0 : u ≠ 0 := fun h => by
    have h2 : (C (ι s) * Sg : Polynomial (RatFunc F)) = 0 :=
      hψinj (h.trans (map_zero ψ).symm)
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rw [C_eq_zero] at h3; exact hιs0 h3
    · exact hSg0 h3
  have hfact : γK * GK = u ^ 2 * ψ (C (ι r) * Rr) := by
    rw [hγKdef, hGKdef, hudef, ← map_pow, ← map_mul, ← map_mul]
    congr 1
    have hCg : (C (ι g) : Polynomial (RatFunc F)) = C (ι s) ^ 2 * C (ι r) := by
      rw [hgdef]; simp [map_mul, map_pow]
    rw [hCg, hGfact]
    ring
  -- ¬IsSquare(± scalar · Rr) in the fraction field, from the radical's squarefreeness
  have hnotsq : ∀ δ : RatFunc F, δ ≠ 0 → ¬ IsSquare (ψ (C δ * Rr)) := by
    intro δ hδ
    have hsf2 : Squarefree (C δ * Rr) := by
      have hassoc : Associated (C δ * Rr) Rr :=
        ⟨(isUnit_C.mpr (Ne.isUnit (inv_ne_zero hδ))).unit, by
          rw [IsUnit.unit_spec]
          rw [mul_comm (C δ) Rr, mul_assoc, ← C_mul, mul_inv_cancel₀ hδ, C_1, mul_one]⟩
      exact hassoc.squarefree_iff.mpr hRsf
    have hdeg2 : 0 < (C δ * Rr).natDegree := by
      rw [natDegree_C_mul hδ]; exact hRdeg
    exact squarefree_pos_not_isSquare_frac (C δ * Rr) hsf2 hdeg2
  have hc : ¬ IsSquare c := by
    rintro ⟨ρ, hρ⟩
    apply hnotsq (ι r) hιr0
    refine ⟨ρ * γK / u, ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hu0 hu0)]
    have hexp : ψ (C (ι r) * Rr) * (u * u) = u ^ 2 * ψ (C (ι r) * Rr) := by ring
    rw [hexp, ← hfact, hGKc, hρ]
    ring
  have hnc : ¬ IsSquare (-c) := by
    rintro ⟨ρ, hρ⟩
    apply hnotsq (-(ι r)) (neg_ne_zero.mpr hιr0)
    refine ⟨ρ * γK / u, ?_⟩
    have hcval : c = -(ρ * ρ) := by linear_combination -hρ
    have hCneg : (C (-(ι r)) : Polynomial (RatFunc F)) = -(C (ι r)) := by rw [map_neg]
    rw [hCneg, neg_mul, map_neg, div_mul_div_comm, eq_div_iff (mul_ne_zero hu0 hu0)]
    have hexp : -ψ (C (ι r) * Rr) * (u * u) = -(u ^ 2 * ψ (C (ι r) * Rr)) := by ring
    rw [hexp, ← hfact, hGKc, hcval]
    ring
  obtain ⟨hz0, hz1, hz2, hz3⟩ := quartic_descent c a0 a1 a2 a3 hc hnc h0' h1'
  refine ⟨hφinj (hψinj ?_), hφinj (hψinj ?_), hφinj (hψinj ?_), hφinj (hψinj ?_)⟩ <;>
    simp only [map_zero]
  · exact hz0
  · exact hz1
  · exact hz2
  · exact hz3

/-! ## 2. `DBlockIndependence` at `d = 4` for `g = s²·r` (Step-1 generalization) -/

set_option maxHeartbeats 1000000 in
/-- **`DBlockIndependence F 4 q D (s²·r)`, PROVEN** — the first NON-squarefree d-block
independence instance, at the same budget shape `4D + 3·deg g < q` as the squarefree
case.  Step 1 folds the 4-block relation to the d = 2 norm-block relation exactly as in
`dBlockIndependence_four`, then multiplies by `s` and folds `s^q = subq ŝ` to land the
d = 2 core on the squarefree RADICAL `r`; Step 2 is
`quartic_norm_forces_trivial_sqmul`. -/
theorem dBlockIndependence_four_sqmul [Fintype F]
    (s r : F[X]) (hs : s ≠ 0) (hr : Squarefree r) (hrdeg : 0 < r.natDegree)
    (hq_odd : Odd (Fintype.card F)) (h4 : 4 ∣ (Fintype.card F - 1))
    {D : ℕ} (hD : 4 * D + 3 * (s ^ 2 * r).natDegree < Fintype.card F) :
    DBlockIndependence F 4 (Fintype.card F) D (s ^ 2 * r) := by
  intro A hblk hsum j
  set g : F[X] := s ^ 2 * r with hgdef
  have hr0 : r ≠ 0 := fun h => by simp [h] at hrdeg
  set q := Fintype.card F with hqdef
  obtain ⟨e, he⟩ := h4
  have hq1 : 1 ≤ q := Fintype.card_pos
  have hqe : q = 4 * e + 1 := by omega
  have h2e : (q - 1) / 2 = 2 * e := by omega
  have h4e : (q - 1) / 4 = e := by omega
  have hgdegeq : g.natDegree = 2 * s.natDegree + r.natDegree := by
    rw [hgdef, natDegree_mul (pow_ne_zero _ hs) hr0, natDegree_pow]
  -- the folded 4-block relation
  have hsum4 : subq q (A 0) + g ^ e * subq q (A 1) + g ^ (2 * e) * subq q (A 2)
      + g ^ (3 * e) * subq q (A 3) = 0 := by
    have h := hsum
    rw [Fin.sum_univ_four] at h
    have h0v : ((0 : Fin 4) : ℕ) = 0 := rfl
    have h1v : ((1 : Fin 4) : ℕ) = 1 := rfl
    have h2v : ((2 : Fin 4) : ℕ) = 2 := rfl
    have h3v : ((3 : Fin 4) : ℕ) = 3 := rfl
    rw [h0v, h1v, h2v, h3v, h4e] at h
    linear_combination h
  -- the norm blocks
  set B0 : Polynomial (Polynomial F) :=
    C g * (A 0) ^ 2 + (g.map C) * ((A 2) ^ 2 - 2 * (A 1) * (A 3)) with hB0def
  set B1 : Polynomial (Polynomial F) :=
    C g * (2 * (A 0) * (A 2) - (A 1) ^ 2) - (g.map C) * (A 3) ^ 2 with hB1def
  -- fold subq through the blocks
  have hgq : subq q (g.map (C : F →+* F[X])) = g ^ q := (pow_card_eq_subq_map_C g).symm
  have hSB0 : subq q B0 = g * (subq q (A 0)) ^ 2
      + g ^ q * ((subq q (A 2)) ^ 2 - 2 * (subq q (A 1)) * (subq q (A 3))) := by
    rw [hB0def]
    change subqHom q _ = _
    simp only [map_add, map_mul, map_sub, map_pow, map_ofNat]
    simp only [subqHom_apply, subq_C]
    rw [hgq]
  have hSB1 : subq q B1 = g * (2 * (subq q (A 0)) * (subq q (A 2)) - (subq q (A 1)) ^ 2)
      - g ^ q * (subq q (A 3)) ^ 2 := by
    rw [hB1def]
    change subqHom q _ = _
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    simp only [subqHom_apply, subq_C]
    rw [hgq]
  -- the d = 2 relation for the norm blocks, in g
  have hRe : subq q B0 + g ^ (2 * e) * subq q B1 = 0 := by
    have hkey : (subq q (A 0) + g ^ (2 * e) * subq q (A 2)) ^ 2
        - g ^ (2 * e) * (subq q (A 1) + g ^ (2 * e) * subq q (A 3)) ^ 2 = 0 := by
      linear_combination (subq q (A 0) - g ^ e * subq q (A 1) + g ^ (2 * e) * subq q (A 2)
        - g ^ (3 * e) * subq q (A 3)) * hsum4
    have hgq4 : g ^ q = g ^ (4 * e + 1) := by rw [← hqe]
    rw [hSB0, hSB1, hgq4]
    linear_combination g * hkey
  -- THE NEW FOLD: multiply by s and land on the radical r.
  set B0' : Polynomial (Polynomial F) := C s * B0 with hB0'def
  set B1' : Polynomial (Polynomial F) := (s.map (C : F →+* F[X])) * B1 with hB1'def
  have hs1 : subq q B0' = s * subq q B0 := by
    rw [hB0'def]
    change subqHom q _ = _
    rw [map_mul, subqHom_apply, subqHom_apply, subq_C]
  have hs2 : subq q B1' = s ^ q * subq q B1 := by
    rw [hB1'def]
    change subqHom q _ = _
    rw [map_mul, subqHom_apply, subqHom_apply, ← pow_card_eq_subq_map_C]
  have hsplit : g ^ (2 * e) = s ^ (4 * e) * r ^ (2 * e) := by
    rw [hgdef, mul_pow, ← pow_mul]
    congr 2
    ring
  rw [hsplit] at hRe
  have hspow : s ^ q = s * s ^ (4 * e) := by
    rw [hqe, pow_succ']
  have hR' : subq q B0' + r ^ ((q - 1) / 2) * subq q B1' = 0 := by
    rw [hs1, hs2, h2e, hspow]
    linear_combination s * hRe
  -- budget: blocks of B₀, B₁ ≤ deg g + 2D, so blocks of B₀', B₁' ≤ deg s + deg g + 2D
  have hsq : ∀ i : Fin 4, ∀ k, (((A i) ^ 2).coeff k).natDegree ≤ 2 * D := fun i =>
    blocks_pow_le (hblk i) 2
  have h13 : ∀ k, ((2 * (A 1) * (A 3)).coeff k).natDegree ≤ 2 * D := by
    intro k
    have := blocks_two_mul_mul_le (hblk 1) (hblk 3) k
    omega
  have h02 : ∀ k, ((2 * (A 0) * (A 2)).coeff k).natDegree ≤ 2 * D := by
    intro k
    have := blocks_two_mul_mul_le (hblk 0) (hblk 2) k
    omega
  have hb0 : ∀ k, (B0.coeff k).natDegree ≤ g.natDegree + 2 * D := by
    intro k
    rw [hB0def, coeff_add]
    have ht1 := blocks_C_mul_le g (hsq 0) k
    have ht2 := blocks_mapC_mul_le g (blocks_sub_le (hsq 2) h13) k
    exact (natDegree_add_le _ _).trans (max_le ht1 (by omega))
  have hb1 : ∀ k, (B1.coeff k).natDegree ≤ g.natDegree + 2 * D := by
    intro k
    rw [hB1def, coeff_sub]
    have ht1 := blocks_C_mul_le g (blocks_sub_le h02 (hsq 1)) k
    have ht2 := blocks_mapC_mul_le g (hsq 3) k
    exact (natDegree_sub_le _ _).trans (max_le ht1 (by omega))
  have hb0' : ∀ k, (B0'.coeff k).natDegree ≤ s.natDegree + (g.natDegree + 2 * D) := by
    intro k
    rw [hB0'def]
    exact blocks_C_mul_le s hb0 k
  have hb1' : ∀ k, (B1'.coeff k).natDegree ≤ s.natDegree + (g.natDegree + 2 * D) := by
    intro k
    rw [hB1'def]
    have := blocks_mapC_mul_le s hb1 k
    omega
  -- the combined-block budget for the radical: 2(deg s + deg g + 2D) + deg r = 4D + 3 deg g
  have hDr : 2 * (s.natDegree + (g.natDegree + 2 * D)) + r.natDegree < q := by
    have hgd : g.natDegree = 2 * s.natDegree + r.natDegree := hgdegeq
    omega
  have hcomb : ∀ k, ((C r * B0' ^ 2 - (r.map C) * B1' ^ 2).coeff k).natDegree < q :=
    combined_blocks_lt_general r hDr B0' B1' hb0' hb1'
  -- the d = 2 core fires on the RADICAL
  obtain ⟨hB0'z, hB1'z⟩ := obstruction_forces_trivial r hr hrdeg hq_odd B0' B1' hcomb hR'
  -- strip the s-factors (F[X][Y] is a domain)
  have hCs0 : (C s : Polynomial (Polynomial F)) ≠ 0 := by
    rw [ne_eq, C_eq_zero]
    exact hs
  have hmapCs0 : s.map (C : F →+* F[X]) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (C_injective)).mpr hs
  have hB0z : B0 = 0 := by
    rcases mul_eq_zero.mp (hB0'def.symm.trans hB0'z) with h | h
    · exact absurd h hCs0
    · exact h
  have hB1z : B1 = 0 := by
    rcases mul_eq_zero.mp (hB1'def.symm.trans hB1'z) with h | h
    · exact absurd h hmapCs0
    · exact h
  -- the quartic descent finishes (radical non-square input)
  obtain ⟨h0z, h1z, h2z, h3z⟩ := quartic_norm_forces_trivial_sqmul s r hs hr hrdeg
    (A 0) (A 1) (A 2) (A 3) (hB0def.symm.trans hB0z) (hB1def.symm.trans hB1z)
  fin_cases j
  · exact h0z
  · exact h1z
  · exact h2z
  · exact h3z

/-! ## 3. The d = 4 face's actual kernel: the quintic `(X−a)(X−b)(X−c)³` -/

/-- The (monic-normalized) triple-linear kernel of the order-4 face:
`χ(L₁L₂)·conj χ(L₃) = χ(L₁L₂L₃³)` up to the nonzero scalar `uvw³`. -/
noncomputable def quinticKernel (a b c : F) : F[X] :=
  (X - C a) * (X - C b) * (X - C c) ^ 3

/-- The square-times-radical factorization: `s = X − c`, `r = (X−a)(X−b)(X−c)`. -/
theorem quinticKernel_eq_sqmul (a b c : F) :
    quinticKernel a b c = (X - C c) ^ 2 * ((X - C a) * (X - C b) * (X - C c)) := by
  rw [quinticKernel]
  ring

/-- The radical `(X−a)(X−b)(X−c)` is squarefree for distinct `a, b, c`. -/
theorem radical_squarefree [DecidableEq F] {a b c : F}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Squarefree ((X - C a) * (X - C b) * (X - C c)) := by
  have h1 : a ∉ ({b, c} : Finset F) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact hab h
    · exact hac h
  have h2 : b ∉ ({c} : Finset F) := by
    simp only [Finset.mem_singleton]; exact hbc
  have hprod : (∏ x ∈ ({a, b, c} : Finset F), (X - C x))
      = (X - C a) * (X - C b) * (X - C c) := by
    rw [Finset.prod_insert h1, Finset.prod_insert h2, Finset.prod_singleton, mul_assoc]
  rw [← hprod]
  exact (separable_prod_X_sub_C_iff'.mpr fun x _ y _ h => h).squarefree

theorem radical_natDegree (a b c : F) :
    ((X - C a) * (X - C b) * (X - C c)).natDegree = 3 := by
  rw [natDegree_mul (mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b)) (X_sub_C_ne_zero c),
    natDegree_mul (X_sub_C_ne_zero a) (X_sub_C_ne_zero b),
    natDegree_X_sub_C, natDegree_X_sub_C, natDegree_X_sub_C]

theorem quinticKernel_monic (a b c : F) : (quinticKernel a b c).Monic := by
  rw [quinticKernel]
  exact ((monic_X_sub_C a).mul (monic_X_sub_C b)).mul ((monic_X_sub_C c).pow 3)

theorem quinticKernel_natDegree (a b c : F) : (quinticKernel a b c).natDegree = 5 := by
  rw [quinticKernel_eq_sqmul,
    natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero c))
      (mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b)) (X_sub_C_ne_zero c)),
    natDegree_pow, natDegree_X_sub_C, radical_natDegree]

/-- **`DBlockIndependence` for the ACTUAL d = 4 kernel** at the concrete budget
`4D + 15 < q` (= `4D + 3·deg h`, `deg h = 5`). -/
theorem dBlockIndependence_four_quinticKernel [Fintype F] [DecidableEq F]
    {a b c : F} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hq_odd : Odd (Fintype.card F)) (h4 : 4 ∣ (Fintype.card F - 1))
    {D : ℕ} (hD : 4 * D + 15 < Fintype.card F) :
    DBlockIndependence F 4 (Fintype.card F) D (quinticKernel a b c) := by
  rw [quinticKernel_eq_sqmul]
  refine dBlockIndependence_four_sqmul (X - C c) ((X - C a) * (X - C b) * (X - C c))
    (X_sub_C_ne_zero c) (radical_squarefree hab hac hbc)
    (by rw [radical_natDegree]; omega) hq_odd h4 ?_
  rw [← quinticKernel_eq_sqmul, quinticKernel_natDegree]
  omega

/-! ## 4. THE UNCONDITIONAL d = 4 PER-FIBER COUNT on the true kernel -/

/-- **The d = 4 face's per-fiber Stepanov count, UNCONDITIONAL** (the round-25
deliverable): for every fiber value ζ and every admissible `(m, J, D)`,
`m·#{s : h(s)^e = ζ} ≤ 5(m + 3e) + D + q(J−1)` on the QUINTIC kernel
`h = (X−a)(X−b)(X−c)³` — the multiplicity-3 factor handled by the radical fold.  This is
the exact count-supply input of the `_R23ParameterChoice`-style numeric instantiation for
`TripleLinearHasseC` at `d = 4`. -/
theorem quintic_kernel_fiber_bound [Fintype F] [DecidableEq F]
    {a b c : F} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hq_odd : Odd (Fintype.card F)) (h4 : 4 ∣ (Fintype.card F - 1))
    {m e J D : ℕ} (hJ : 0 < J)
    (he : e = (Fintype.card F - 1) / 4)
    (hmq : m < Fintype.card F)
    (hD : 4 * D + 15 < Fintype.card F)
    (hcount : m * (D + 4 * m + J) < 4 * (J * (D + 1)))
    (ζ : F) :
    m * (Finset.univ.filter fun t : F =>
        ((quinticKernel a b c).eval t) ^ e = ζ).card
      ≤ 5 * (m + 3 * e) + D + Fintype.card F * (J - 1) := by
  have hdeg5 := quinticKernel_natDegree a b c
  have hbound := superelliptic_stepanov_fiber_bound (quinticKernel a b c)
    (quinticKernel_monic a b c) (by rw [hdeg5]; omega) hJ
    (dBlockIndependence_four_quinticKernel hab hac hbc hq_odd h4 hD)
    he hmq (by simpa [hdeg5] using hcount) ζ
  rw [hdeg5] at hbound
  norm_num at hbound
  exact hbound

/-! ## 5. The free win: the d = 4 face is VACUOUS at `q ≢ 1 (mod 4)` -/

/-- **Vacuity of the d = 4 face away from `q ≡ 1 (mod 4)`**: if `4 ∤ q − 1` there is NO
multiplicative character of order 4 at all, so the order-4 member of the `chiFamily`
simply does not exist — nothing to bound.  (Mathlib: character orders divide `q − 1`.) -/
theorem no_order_four_char_of_card_mod [Fintype F] {R : Type*} [CommRing R]
    (h : ¬ (4 ∣ Fintype.card F - 1)) (χ : MulChar F R) : orderOf χ ≠ 4 := fun hord =>
  h (hord ▸ MulChar.orderOf_dvd_card_sub_one F χ)

end ArkLib.ProximityGap.Frontier.R25D4Instantiate

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.R25D4Instantiate in
#print axioms quartic_norm_forces_trivial_sqmul
open ArkLib.ProximityGap.Frontier.R25D4Instantiate in
#print axioms dBlockIndependence_four_sqmul
open ArkLib.ProximityGap.Frontier.R25D4Instantiate in
#print axioms dBlockIndependence_four_quinticKernel
open ArkLib.ProximityGap.Frontier.R25D4Instantiate in
#print axioms quintic_kernel_fiber_bound
open ArkLib.ProximityGap.Frontier.R25D4Instantiate in
#print axioms no_order_four_char_of_card_mod

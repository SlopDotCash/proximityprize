/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecoding.Bounds
import ArkLib.Data.CodingTheory.EntropyVolumeBound

/-!
# Unconditional entropy-volume list-size lower bound (`/(n+1)` form)

The elementary, **all-`δ`** companion to ABF26 Corollary 3.8 (`linear_lambda_ge_entropy_volume`).
That corollary uses the MacWilliams–Sloane `1/√(8nδ(1−δ))` Hamming-ball estimate, which is
genuinely **false off the lattice** `δ·n ∈ ℕ` (see the `ms77` discussion in
`ListDecoding/Bounds.lean`); it therefore needs the integer-radius side condition.

Combining instead the proven Elias volume bound `linear_lambda_ge_elias_volume_eli57` (ABF26 L3.7,
`|Λ(C,δ)| ≥ Vol_q(δ,n)/q^{n−k}`) with the elementary, Stirling-free entropy-volume bound
`hammingBallVolume_ge_qEntropy` (`q^{n·H_q(⌊δn⌋/n)} ≤ (n+1)·Vol_q(δ,n)`, `EntropyVolumeBound.lean`)
yields the list-size lower bound with the weaker `1/(n+1)` prefactor but **no lattice restriction**:

  `|Λ(C,δ)| ≥ q^{n·H_q(⌊δn⌋/n)} / ((n+1) · q^{n−k})`.

Since `n−k = n(1−ρ)` with `ρ = k/n`, the exponent is `n(ρ − 1 + H_q(⌊δn⌋/n))`, matching C3.8's
numerator with the floor-honest entropy argument. `sorry`/`axiom`-free, axiom-clean.
-/

namespace CodingTheory

open Real ListDecodable

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Unconditional entropy-volume list-size lower bound (`/(n+1)` form), alphabet-generic.**

For any code `C ⊆ (ι → A)` over an arbitrary alphabet `A` with `|C| = |A|^k`, `2 ≤ |A|`, and
mode index `⌊δ·n⌋ ∈ (0, n)`:

  `|Λ(C, δ)| ≥ |A|^{n·H_{|A|}(⌊δn⌋/n)} / ((n+1) · |A|^{n − k})`.

This is the alphabet-generic companion to `lambda_ge_entropy_volume` (ABF26 C3.8), chaining
`lambda_ge_elias_volume_eli57` (L3.7) with `hammingBallVolume_ge_qEntropy` with no `δ·n ∈ ℕ`
lattice restriction. -/
theorem lambda_ge_entropy_volume_div_succ_generic
    {ι A : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
    (C : Set (ι → A)) (k : ℕ) (hcard : C.ncard = Fintype.card A ^ k)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hq : 2 ≤ Fintype.card A)
    (hk0 : 0 < ⌊δ * (Fintype.card ι : ℝ)⌋₊)
    (hkn : ⌊δ * (Fintype.card ι : ℝ)⌋₊ < Fintype.card ι) :
    ENNReal.ofReal
        ((Fintype.card A : ℝ) ^ ((Fintype.card ι : ℝ)
              * qEntropy (Fintype.card A)
                  ((⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ)))
          / (((Fintype.card ι : ℝ) + 1)
              * (Fintype.card A : ℝ) ^ ((Fintype.card ι : ℝ) - (k : ℝ))))
      ≤ (Lambda C δ : ENNReal) := by
  set q := Fintype.card A with hq_def
  set n := Fintype.card ι with hn_def
  have hvol := hammingBallVolume_ge_qEntropy hq δ n hk0 hkn
  have hL37 := lambda_ge_elias_volume_eli57 C k hcard δ hδ_pos hδ_lt
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hL37
  have hqR : (0 : ℝ) < (q : ℝ) := by
    have h1 : 1 < q := by omega
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1.le
  have hP : (0 : ℝ) < (q : ℝ) ^ ((n : ℝ) - (k : ℝ)) :=
    Real.rpow_pos_of_pos hqR _
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [← div_div, div_le_div_iff_of_pos_right hP, div_le_iff₀ hn1]
  nlinarith [hvol]

/-- **Unconditional entropy-volume list-size lower bound (`/(n+1)` form), linear code.**

For a linear code `C ≤ (ι → F)` with `q = |F| ≥ 2`, `n = |ι|`, mode index `⌊δ·n⌋ ∈ (0, n)`:

  `|Λ(C, δ)| ≥ q^{n·H_q(⌊δn⌋/n)} / ((n+1) · q^{n − dim C})`.

Specialization of `lambda_ge_entropy_volume_div_succ_generic` with `|C| = |F|^dim(C)`. -/
theorem linear_lambda_ge_entropy_volume_div_succ
    (C : Submodule F (ι → F)) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hq : 2 ≤ Fintype.card F)
    (hk0 : 0 < ⌊δ * (Fintype.card ι : ℝ)⌋₊)
    (hkn : ⌊δ * (Fintype.card ι : ℝ)⌋₊ < Fintype.card ι) :
    ENNReal.ofReal
        ((Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ)
              * qEntropy (Fintype.card F)
                  ((⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ)))
          / (((Fintype.card ι : ℝ) + 1)
              * (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ) - Module.finrank F C)))
      ≤ (Lambda ((C : Set (ι → F))) δ : ENNReal) := by
  apply lambda_ge_entropy_volume_div_succ_generic (C := (C : Set (ι → F)))
    (k := Module.finrank F C) (δ := δ) ?_ hδ_pos hδ_lt hq hk0 hkn
  classical
  haveI : Fintype (↥C) := Fintype.ofFinite _
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact Module.card_eq_pow_finrank (K := F) (V := ↥C)

/-- **Reed–Solomon specialization (RS codewords in a `δ`-ball).**

For `RS[F, α, k]` with `q = |F| ≥ 2`, `n = |ι|`, `k ≤ n`, mode index `⌊δ·n⌋ ∈ (0, n)`:

  `|Λ(RS[α,k], δ)| ≥ q^{n·H_q(⌊δn⌋/n)} / ((n+1) · q^{n−k})`.

The RS instance of `linear_lambda_ge_entropy_volume_div_succ` (RS is a linear code, with
`Module.finrank F (RS[α,k]) = k` via `ReedSolomon.dim_eq_deg_of_le'`).  This is the
"number of RS codewords in a `δ`-ball" lower bound feeding the CS25 / Grand-LD prize lower
bounds (issues #82, #69). -/
theorem rs_lambda_ge_entropy_volume_div_succ
    (α : ι ↪ F) (k : ℕ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hq : 2 ≤ Fintype.card F)
    (hkcard : k ≤ Fintype.card ι)
    (hk0 : 0 < ⌊δ * (Fintype.card ι : ℝ)⌋₊)
    (hkn : ⌊δ * (Fintype.card ι : ℝ)⌋₊ < Fintype.card ι) :
    ENNReal.ofReal
        ((Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ)
              * qEntropy (Fintype.card F)
                  ((⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ)))
          / (((Fintype.card ι : ℝ) + 1)
              * (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ) - (k : ℝ))))
      ≤ (Lambda ((ReedSolomon.code α k : Set (ι → F))) δ : ENNReal) := by
  have hdim : Module.finrank F (ReedSolomon.code α k) = k :=
    ReedSolomon.dim_eq_deg_of_le' hkcard
  have h := linear_lambda_ge_entropy_volume_div_succ
    (ReedSolomon.code α k) δ hδ_pos hδ_lt hq hk0 hkn
  rwa [hdim] at h

/-- **Capacity-exponent form of the list-size lower bound, alphabet-generic.** -/
theorem lambda_ge_capacity_exponent_generic
    {ι A : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
    (C : Set (ι → A)) (k : ℕ) (hcard : C.ncard = Fintype.card A ^ k)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hq : 2 ≤ Fintype.card A)
    (hk0 : 0 < ⌊δ * (Fintype.card ι : ℝ)⌋₊)
    (hkn : ⌊δ * (Fintype.card ι : ℝ)⌋₊ < Fintype.card ι) :
    ENNReal.ofReal
        ((Fintype.card A : ℝ) ^ ((Fintype.card ι : ℝ)
              * qEntropy (Fintype.card A)
                  ((⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ))
            - ((Fintype.card ι : ℝ) - (k : ℝ)))
          / ((Fintype.card ι : ℝ) + 1))
      ≤ (Lambda C δ : ENNReal) := by
  have hq0 : (0 : ℝ) < (Fintype.card A : ℝ) := by
    have : 0 < Fintype.card A := by omega
    exact_mod_cast this
  have heq :
      (Fintype.card A : ℝ) ^ ((Fintype.card ι : ℝ)
            * qEntropy (Fintype.card A)
                ((⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ))
          - ((Fintype.card ι : ℝ) - (k : ℝ)))
        / ((Fintype.card ι : ℝ) + 1)
      = (Fintype.card A : ℝ) ^ ((Fintype.card ι : ℝ)
            * qEntropy (Fintype.card A)
                ((⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ)))
        / (((Fintype.card ι : ℝ) + 1)
            * (Fintype.card A : ℝ) ^ ((Fintype.card ι : ℝ) - (k : ℝ))) := by
    have hpow : (Fintype.card A : ℝ) ^ ((Fintype.card ι : ℝ) - (k : ℝ)) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hq0 _)
    have hn1 : ((Fintype.card ι : ℝ) + 1) ≠ 0 := by positivity
    rw [Real.rpow_sub hq0]
    field_simp
  rw [heq]
  exact lambda_ge_entropy_volume_div_succ_generic C k hcard δ hδ_pos hδ_lt hq hk0 hkn

/-- **Capacity-exponent form of the RS list-size lower bound.**

The single-power form of `rs_lambda_ge_entropy_volume_div_succ`, with the two `q`-powers combined
into the capacity exponent `n·H_q(⌊δn⌋/n) − (n − k)` (`= n·(ρ − 1 + H_q)` with `ρ = k/n`):

  `|Λ(RS[α,k], δ)| ≥ q^{n·H_q(⌊δn⌋/n) − (n − k)} / (n + 1)`.

This is the explicit Johnson-to-capacity LD-threshold form: the list size is super-polynomial
exactly when the capacity exponent is positive (`H_q(⌊δn⌋/n) > 1 − ρ`). -/
theorem rs_lambda_ge_capacity_exponent
    (α : ι ↪ F) (k : ℕ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hq : 2 ≤ Fintype.card F)
    (hkcard : k ≤ Fintype.card ι)
    (hk0 : 0 < ⌊δ * (Fintype.card ι : ℝ)⌋₊)
    (hkn : ⌊δ * (Fintype.card ι : ℝ)⌋₊ < Fintype.card ι) :
    ENNReal.ofReal
        ((Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ)
              * qEntropy (Fintype.card F)
                  ((⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ))
            - ((Fintype.card ι : ℝ) - (k : ℝ)))
          / ((Fintype.card ι : ℝ) + 1))
      ≤ (Lambda ((ReedSolomon.code α k : Set (ι → F))) δ : ENNReal) := by
  have hq0 : (0 : ℝ) < (Fintype.card F : ℝ) := by
    have : 0 < Fintype.card F := by omega
    exact_mod_cast this
  have heq :
      (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ)
            * qEntropy (Fintype.card F)
                ((⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ))
          - ((Fintype.card ι : ℝ) - (k : ℝ)))
        / ((Fintype.card ι : ℝ) + 1)
      = (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ)
            * qEntropy (Fintype.card F)
                ((⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ)))
        / (((Fintype.card ι : ℝ) + 1)
            * (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ) - (k : ℝ))) := by
    have hpow : (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ) - (k : ℝ)) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hq0 _)
    have hn1 : ((Fintype.card ι : ℝ) + 1) ≠ 0 := by positivity
    rw [Real.rpow_sub hq0]
    field_simp
  rw [heq]
  exact rs_lambda_ge_entropy_volume_div_succ α k δ hδ_pos hδ_lt hq hkcard hk0 hkn

end CodingTheory

-- Axiom audit: depends on exactly `[propext, Classical.choice, Quot.sound]`.
#print axioms CodingTheory.lambda_ge_entropy_volume_div_succ_generic
#print axioms CodingTheory.lambda_ge_capacity_exponent_generic
#print axioms CodingTheory.linear_lambda_ge_entropy_volume_div_succ
#print axioms CodingTheory.rs_lambda_ge_entropy_volume_div_succ
#print axioms CodingTheory.rs_lambda_ge_capacity_exponent

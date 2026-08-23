/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib

/-!
# [GG25] Lemma 3.2 — the mutual-correlated-agreement spread bound (issue #389 / #334 B2)

Goyal–Guruswami (ECCC TR25-166 / ePrint 2025/2054, *Optimal Proximity Gaps for
Subspace-Design Codes and (Random) Reed–Solomon Codes*) **Lemma 3.2** — the combinatorial
heart that turns *curve-decodability* (Def 3.1) into *mutual correlated agreement* (Thm 3.3).

Given two curves `α ↦ ∑ⱼ αʲ • uⱼ` and `α ↦ ∑ⱼ αʲ • cⱼ` over an `F`-module alphabet `A`,
let `T = {i : ∃ j, uⱼᵢ ≠ cⱼᵢ}` be the union of their disagreement coordinates. If the two
curves are within Hamming distance `D` at `≥ t` field points, with `ℓ < t`, then

  `disagree_spread_bound`  :  `t·|T| ≤ ℓ·|T| + t·D`   (i.e. `(t − ℓ)·|T| ≤ t·D`)
  `all_seeds_close`        :  `∀ β, (t − ℓ)·dist(curve_u β, curve_c β) ≤ t·D`.

Equivalently `|T| ≤ D·(1 + ℓ/(t−ℓ))`, so the two curves agree on all but a `δ(1+ℓ/(t−ℓ))`
fraction of coordinates at *every* seed — the spreading statement of GG25 Lemma 3.2.

## The argument (the paper's, formalized)

* **Degree-`ℓ` root bound** (`gdiff_zero_card_le`): at a disagreement coordinate `i`, the
  difference value `gdiff i α = ∑ⱼ αʲ • (uⱼᵢ − cⱼᵢ)` is a nonzero module-valued polynomial of
  degree `≤ ℓ`. Dual-separating the nonzero leading data to a scalar functional `φ` yields a
  *nonzero* `F`-polynomial of degree `≤ ℓ`; `Polynomial.card_roots'` then bounds the vanishing
  set by `ℓ`. So each `i ∈ T` is "killed" for at most `ℓ` field values.
* **Double-count + averaging** (`disagree_spread_bound`): summing the agree-counts over the
  `≥ t` close seeds and swapping the order of summation gives `∑_{α close} #(agree at α) ≤ ℓ·|T|`;
  the minimizing close seed `α₀` then satisfies `t·#(agree at α₀) ≤ ℓ·|T|`, and combining with
  `|T| = dist(α₀) + #(agree at α₀) ≤ D + #(agree at α₀)` yields the master inequality.

This is the curve-decodability half of the issue's class-B2 item: the in-tree
`GG25CurveDecodability.lean` supplies the *definition* (`CurveDecodable`, `curveCloseSet`) and
the dual-separation root core (`GG25NonCovering.eq_zero_of_curve_agree_many`); this file supplies
the **spread reduction** itself, the substantive content of [GG25] Thm 3.3. Axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

open Finset Polynomial

namespace ProximityGap.GG25Lemma32

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The curve combiner `∑ⱼ αʲ • uⱼ` at coordinate `i` (matching the in-tree
`MCACurveEvent` / `curveCloseSet` combiner convention). -/
def comb {ℓ : ℕ} (u : Fin (ℓ + 1) → ι → A) (α : F) (i : ι) : A :=
  ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j i

/-- The difference value `g i α = ∑ⱼ αʲ • (uⱼᵢ − cⱼᵢ)` between the two curves at coordinate `i`. -/
def gdiff {ℓ : ℕ} (u c : Fin (ℓ + 1) → ι → A) (i : ι) (α : F) : A :=
  ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • (u j i - c j i)

/-- The disagreement support `T = {i : ∃ j, uⱼᵢ ≠ cⱼᵢ}`. -/
def disagree {ℓ : ℕ} (u c : Fin (ℓ + 1) → ι → A) : Finset ι :=
  univ.filter (fun i => ∃ j, u j i ≠ c j i)

/-- An averaging step: in a nonempty finite family with total `≤ B`, some element's value,
scaled by the family size, is still `≤ B`. -/
lemma exists_mem_card_mul_le {β : Type*} (s : Finset β) (g : β → ℕ) {B : ℕ}
    (hne : s.Nonempty) (hsum : ∑ b ∈ s, g b ≤ B) : ∃ b ∈ s, s.card * g b ≤ B := by
  classical
  obtain ⟨b₀, hb₀, hmin⟩ := Finset.exists_min_image s g hne
  refine ⟨b₀, hb₀, ?_⟩
  calc s.card * g b₀ = ∑ _b ∈ s, g b₀ := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ b ∈ s, g b := Finset.sum_le_sum (fun b hb => hmin b hb)
    _ ≤ B := hsum

/-- The two combiners differ at `i` exactly by `gdiff`. -/
lemma comb_sub {ℓ : ℕ} (u c : Fin (ℓ + 1) → ι → A) (α : F) (i : ι) :
    comb u α i - comb c α i = gdiff u c i α := by
  rw [comb, comb, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _ => (smul_sub (α ^ (j : ℕ)) (u j i) (c j i)).symm)

/-- Outside the disagreement support, the difference value vanishes identically. -/
lemma gdiff_eq_zero_of_not_disagree {ℓ : ℕ} (u c : Fin (ℓ + 1) → ι → A) {i : ι}
    (hi : i ∉ disagree u c) (α : F) : gdiff u c i α = 0 := by
  simp only [disagree, mem_filter, mem_univ, true_and, not_exists, not_not] at hi
  simp only [gdiff]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [hi j, sub_self, smul_zero]

/-- **The degree-`ℓ` root bound.** For a disagreement coordinate `i`, the difference value
`gdiff u c i α` vanishes for at most `ℓ` field values `α`. (Dual-separate the nonzero
difference vector to a nonzero scalar polynomial of degree `≤ ℓ`, then count roots.) -/
lemma gdiff_zero_card_le {ℓ : ℕ} (u c : Fin (ℓ + 1) → ι → A) {i : ι}
    (hi : i ∈ disagree u c) :
    (univ.filter (fun α : F => gdiff u c i α = 0)).card ≤ ℓ := by
  classical
  simp only [disagree, mem_filter, mem_univ, true_and] at hi
  obtain ⟨j₀, hj₀⟩ := hi
  have hd : u j₀ i - c j₀ i ≠ 0 := sub_ne_zero.mpr hj₀
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero F hd
  set P : F[X] := ∑ j : Fin (ℓ + 1), C (φ (u j i - c j i)) * X ^ (j : ℕ) with hP
  -- coefficient at `j₀` is `φ (dⱼ₀)`, nonzero ⇒ `P ≠ 0`
  have hcoeff : P.coeff (j₀ : ℕ) = φ (u j₀ i - c j₀ i) := by
    rw [hP, finset_sum_coeff]
    rw [Finset.sum_eq_single j₀]
    · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
    · intro j _ hj
      rw [coeff_C_mul, coeff_X_pow, if_neg (fun h => hj (Fin.val_injective h).symm), mul_zero]
    · intro h; exact absurd (mem_univ j₀) h
  have hPne : P ≠ 0 := by
    intro h0
    rw [h0, coeff_zero] at hcoeff
    exact hφ hcoeff.symm
  have hdeg : P.natDegree ≤ ℓ := by
    rw [hP]
    refine natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
    have hj : (j : ℕ) ≤ ℓ := by have := j.isLt; omega
    calc (C (φ (u j i - c j i)) * X ^ (j : ℕ)).natDegree
        ≤ (X ^ (j : ℕ) : F[X]).natDegree := natDegree_C_mul_le _ _
      _ = (j : ℕ) := natDegree_X_pow _
      _ ≤ ℓ := hj
  -- every vanishing `α` is a root of `P`
  have hsub : (univ.filter (fun α : F => gdiff u c i α = 0)) ⊆ P.roots.toFinset := by
    intro α hα
    simp only [mem_filter, mem_univ, true_and] at hα
    rw [Multiset.mem_toFinset, mem_roots hPne, IsRoot.def]
    have hev : P.eval α = φ (gdiff u c i α) := by
      rw [hP, gdiff, eval_finset_sum, map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [eval_mul, eval_C, eval_pow, eval_X, map_smul, smul_eq_mul]
      ring
    rw [hev, hα, map_zero]
  calc (univ.filter (fun α : F => gdiff u c i α = 0)).card
      ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card P.roots := P.roots.toFinset_card_le
    _ ≤ P.natDegree := P.card_roots'
    _ ≤ ℓ := hdeg

/-- The Hamming distance between the two combiners equals the number of disagreement
coordinates where the difference value is nonzero. -/
lemma hammingDist_comb_eq {ℓ : ℕ} (u c : Fin (ℓ + 1) → ι → A) (α : F) :
    hammingDist (comb u α) (comb c α)
      = ((disagree u c).filter (fun i => gdiff u c i α ≠ 0)).card := by
  classical
  unfold hammingDist
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro hne
    have hg : gdiff u c i α ≠ 0 := by rw [← comb_sub]; exact sub_ne_zero.mpr hne
    refine ⟨?_, hg⟩
    by_contra hi
    exact hg (gdiff_eq_zero_of_not_disagree u c hi α)
  · rintro ⟨_, hg⟩
    rw [← comb_sub] at hg; exact sub_ne_zero.mp hg

/-- The disagreement support splits into the disagreeing-at-`α` (= Hamming distance) and
agreeing-at-`α` parts. -/
lemma disagree_card_split {ℓ : ℕ} (u c : Fin (ℓ + 1) → ι → A) (α : F) :
    hammingDist (comb u α) (comb c α)
      + ((disagree u c).filter (fun i => gdiff u c i α = 0)).card = (disagree u c).card := by
  rw [hammingDist_comb_eq, add_comm]
  exact Finset.filter_card_add_filter_neg_card_eq_card (fun i => gdiff u c i α = 0)

/-- **[GG25] Lemma 3.2 (the master spread inequality), integer form.** If the two curves are
within Hamming distance `D` at `≥ t` field points (`ℓ < t`), then the disagreement support `T`
satisfies `t·|T| ≤ ℓ·|T| + t·D`, i.e. `(t − ℓ)·|T| ≤ t·D` — equivalently `|T| ≤ D·(1+ℓ/(t−ℓ))`. -/
theorem disagree_spread_bound {ℓ t D : ℕ} (hlt : ℓ < t)
    (u c : Fin (ℓ + 1) → ι → A)
    (hclose : t ≤ (univ.filter
      (fun α : F => hammingDist (comb u α) (comb c α) ≤ D)).card) :
    t * (disagree u c).card ≤ ℓ * (disagree u c).card + t * D := by
  classical
  set Aset := univ.filter (fun α : F => hammingDist (comb u α) (comb c α) ≤ D) with hA
  -- (1) double-count: ∑_{α∈Aset} #(agree at α) ≤ ℓ·|T|
  have hsum : ∑ α ∈ Aset, ((disagree u c).filter (fun i => gdiff u c i α = 0)).card
              ≤ ℓ * (disagree u c).card := by
    have hswap : (∑ α ∈ Aset, ((disagree u c).filter (fun i => gdiff u c i α = 0)).card)
        = ∑ i ∈ disagree u c, (Aset.filter (fun α => gdiff u c i α = 0)).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
    rw [hswap]
    calc ∑ i ∈ disagree u c, (Aset.filter (fun α => gdiff u c i α = 0)).card
        ≤ ∑ _i ∈ disagree u c, ℓ := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          refine le_trans (Finset.card_le_card ?_) (gdiff_zero_card_le u c hi)
          exact Finset.filter_subset_filter _ (Finset.filter_subset _ _)
      _ = ℓ * (disagree u c).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- (2) Aset nonempty (card ≥ t ≥ 1)
  have htpos : 0 < t := lt_of_le_of_lt (Nat.zero_le _) hlt
  have hAne : Aset.Nonempty := by rw [← Finset.card_pos]; omega
  -- (3) averaging: some α₀ with |Aset|·#(agree at α₀) ≤ ℓ·|T|
  obtain ⟨α₀, hα₀mem, hcardmul⟩ := exists_mem_card_mul_le Aset
      (fun α => ((disagree u c).filter (fun i => gdiff u c i α = 0)).card) hAne hsum
  -- (4) t·#(agree at α₀) ≤ ℓ·|T|
  have hstep : t * ((disagree u c).filter (fun i => gdiff u c i α₀ = 0)).card
                ≤ ℓ * (disagree u c).card :=
    le_trans (Nat.mul_le_mul_right _ hclose) hcardmul
  -- (5) α₀ is close
  have hα₀close : hammingDist (comb u α₀) (comb c α₀) ≤ D := by
    have h := hα₀mem; rw [hA, mem_filter] at h; exact h.2
  -- (6) combine, multiplied through by t
  have hsplit := disagree_card_split u c α₀
  have key : t * hammingDist (comb u α₀) (comb c α₀)
      + t * ((disagree u c).filter (fun i => gdiff u c i α₀ = 0)).card
      = t * (disagree u c).card := by rw [← Nat.mul_add, hsplit]
  have h1 : t * hammingDist (comb u α₀) (comb c α₀) ≤ t * D := Nat.mul_le_mul_left _ hα₀close
  omega

/-- **The per-seed MCA distance bound (every `α`).** Under the same hypotheses, at *every*
field point the two curves are within `(t − ℓ)·dist ≤ t·D`, i.e. `dist ≤ D·t/(t−ℓ)`. -/
theorem all_seeds_close {ℓ t D : ℕ} (hlt : ℓ < t)
    (u c : Fin (ℓ + 1) → ι → A)
    (hclose : t ≤ (univ.filter
      (fun α : F => hammingDist (comb u α) (comb c α) ≤ D)).card) (β : F) :
    (t - ℓ) * hammingDist (comb u β) (comb c β) ≤ t * D := by
  have hmaster := disagree_spread_bound hlt u c hclose
  have hle : hammingDist (comb u β) (comb c β) ≤ (disagree u c).card := by
    rw [hammingDist_comb_eq]; exact Finset.card_filter_le _ _
  have h1 : (t - ℓ) * hammingDist (comb u β) (comb c β)
      ≤ (t - ℓ) * (disagree u c).card := Nat.mul_le_mul_left _ hle
  have h2 : (t - ℓ) * (disagree u c).card
      = t * (disagree u c).card - ℓ * (disagree u c).card := Nat.sub_mul t ℓ (disagree u c).card
  omega

end ProximityGap.GG25Lemma32

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.GG25Lemma32.disagree_spread_bound
#print axioms ProximityGap.GG25Lemma32.all_seeds_close

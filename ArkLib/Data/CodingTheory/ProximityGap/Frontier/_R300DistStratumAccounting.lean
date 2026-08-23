/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R299PatternStratification

/-!
# LANE B2 (#466, r=3 rung, route ii capstone): the DIST-stratum accounting — the
  calibrated open core localizes two-sidedly to the all-distinct-coset triples,
  with every other stratum priced UNCONDITIONALLY by counting

## The accounting discovery (this session, 2026-07-10)

Split `tripleConv J d` by whether the ordered triple `(i, d−j−i, j)` has all three
`H`-coset labels distinct (`H = {0,u,2u}`, `u = m/3`).  The non-distinct part is
COUNT-THIN: for fixed `(d, j)` the bad `i`-set is contained in two explicit
translate-triples plus three doubling-fibers — at most `6 + 3k₂` elements
(`k₂ = #{i : 2i = 0} = gcd(2,m) ≤ 2`).  Hence with only the classical envelope
`‖J‖² ≤ q` the ENTIRE non-distinct stratum satisfies

  `∑_d ‖nonDist(d)‖² ≤ (6+3k₂)²·m³·q³ ≤ 144·m³·q³`  — UNCONDITIONALLY,

no Hasse–Davenport, no cancellation: the `m²` loss of the R23 triangle-inequality
baseline is carried ENTIRELY by the all-distinct-coset triples.  This subsumes the
scale accounting of the R298 diagonal and the R299 SAME3/TWO classes at once
(their exact HD/mixed-conv structure remains the finer, sharper information).

## What this brick lands (all axiom-clean)

* `distStratum` / `nonDistStratum` — the exact decidable-pattern split of
  `tripleConv` (`tripleConv_eq_dist_add_nonDist`, unconditional);
* `nonDist_inner_subset` + `card` chain — the count-thinness, fully proven
  (translate-triples + `card_double_fiber_le_card_kernel`);
* `nonDistStratum_energy_le` — the unconditional `(6+3k₂)²·m³·B⁶` envelope;
* `DistStratumEnergyBound` — **THE MINIMAL NAMED OPEN PROP for the r=3 rung**:
  `∑_d ‖distStratum(d)‖² ≤ C·m³·q³`;
* `tripleConvEnergyBound_of_distStratum` / `distStratumEnergyBound_of_tripleConv`
  — the TWO-SIDED accounting: `TripleConvEnergyBound (2C_D + 288)` ⟸
  `DistStratumEnergyBound C_D` and conversely (`2C + 288`), given only `‖J‖² ≤ q`
  and `k₂ ≤ 2`;
* `distStratumEnergyBound_trivial` — instantiability: `C = m²` always (the
  baseline `m²` gap, now provably confined to DIST);
* **ladder rungs** `distStratum_eq_zero_m3` / `_m6` +
  `distStratumEnergyBound_rung_m3` / `_m6` — at `m = 3, 6` (`u ≤ 2` cosets) the
  DIST pattern is EMPTY by pigeonhole (kernel-checked by `decide`), so the open
  Prop holds with `C = 0` for EVERY coefficient sequence and every `q`: the Prop
  is instantiable and calibrated.

## The r=3 rung dependency graph after this brick

`TripleConvEnergyBound` (the §33 calibrated open core) ⟸ two-sidedly, with
absolute constants ⟸ `DistStratumEnergyBound` alone.  The HD inputs
(`HDCosetTripleCollapse`, `HDPairCollapse` — classical mathematics, a Mathlib
Gauss-sum gap) and the r=2-class input (`MixedConvEnergyBound`) price the finer
exact structure of the non-distinct strata but are NOT needed for the scale
accounting.  The open content of the rung = square-root cancellation among
all-distinct-coset Jacobi angle triples — Katz vertical-equidistribution
territory (route i; see the kb note for the precise monodromy statement needed).
CORE OPEN, ON-BGK.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R300DistStratumAccounting

open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R22SexticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput

variable {m : ℕ} [NeZero m]

/-- Membership in the order-3 subgroup `H = {0, u, 2u}` (as a difference test). -/
def inH (u x : ZMod m) : Prop := x = 0 ∨ x = u ∨ x = u + u

instance (u x : ZMod m) : Decidable (inH u x) :=
  inferInstanceAs (Decidable (x = 0 ∨ x = u ∨ x = u + u))

/-- All three coset labels of `(a, b, c)` distinct: no pairwise difference in `H`. -/
def allCosetsDistinct (u a b c : ZMod m) : Prop :=
  ¬ inH u (b - a) ∧ ¬ inH u (c - a) ∧ ¬ inH u (c - b)

instance (u a b c : ZMod m) : Decidable (allCosetsDistinct u a b c) :=
  inferInstanceAs (Decidable (¬ inH u (b - a) ∧ ¬ inH u (c - a) ∧ ¬ inH u (c - b)))

/-- **The DIST stratum**: the sub-sum of `tripleConv` over ordered triples
`(i, d−j−i, j)` with all three coset labels distinct. -/
noncomputable def distStratum (J : ZMod m → ℂ) (u d : ZMod m) : ℂ :=
  ∑ j ∈ Finset.univ \ {(0 : ZMod m)},
    ∑ i ∈ ((Finset.univ \ {(0 : ZMod m)}).filter (fun i => d - j - i ≠ 0)).filter
        (fun i => allCosetsDistinct u i (d - j - i) j),
      J i * J (d - j - i) * J j

/-- The complementary (non-distinct-pattern) stratum. -/
noncomputable def nonDistStratum (J : ZMod m → ℂ) (u d : ZMod m) : ℂ :=
  ∑ j ∈ Finset.univ \ {(0 : ZMod m)},
    ∑ i ∈ ((Finset.univ \ {(0 : ZMod m)}).filter (fun i => d - j - i ≠ 0)).filter
        (fun i => ¬ allCosetsDistinct u i (d - j - i) j),
      J i * J (d - j - i) * J j

/-- **The exact pattern split** (unconditional, pure algebra). -/
theorem tripleConv_eq_dist_add_nonDist (J : ZMod m → ℂ) (u d : ZMod m) :
    tripleConv J d = distStratum J u d + nonDistStratum J u d := by
  unfold distStratum nonDistStratum tripleConv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  unfold selfConv
  rw [Finset.sum_mul]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-! ### Count-thinness of the non-distinct stratum -/

/-- Translate-triple bad set (pair conditions not involving the doubled index). -/
def pairBad (u j d : ZMod m) : Finset (ZMod m) :=
  ({j, j - u, j - u - u} : Finset (ZMod m))
    ∪ ({d - 2 * j, d - 2 * j + u, d - 2 * j + u + u} : Finset (ZMod m))

/-- Doubling-fiber bad set (the `2i ∈ d − j − H` condition). -/
def doubleBad (u j d : ZMod m) : Finset (ZMod m) :=
  (Finset.univ.filter (fun i => 2 * i = d - j))
    ∪ ((Finset.univ.filter (fun i => 2 * i = d - j - u))
      ∪ (Finset.univ.filter (fun i => 2 * i = d - j - u - u)))

/-- A doubling fiber injects into the 2-torsion kernel. -/
theorem card_double_fiber_le_card_kernel (t : ZMod m) :
    (Finset.univ.filter (fun i : ZMod m => 2 * i = t)).card
      ≤ (Finset.univ.filter (fun i : ZMod m => 2 * i = 0)).card := by
  classical
  rcases (Finset.univ.filter (fun i : ZMod m => 2 * i = t)).eq_empty_or_nonempty with
    he | ⟨i₀, hi₀⟩
  · rw [he]
    exact Nat.zero_le _
  · have h2i₀ : 2 * i₀ = t := (Finset.mem_filter.mp hi₀).2
    apply Finset.card_le_card_of_injOn (fun i => i - i₀)
    · intro i hi
      have h2i : 2 * i = t := (Finset.mem_filter.mp hi).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [mul_sub, h2i, h2i₀, sub_self]
    · intro a _ b _ hab
      have : a - i₀ = b - i₀ := hab
      linear_combination this

/-- **The bad-index inclusion**: a non-distinct triple pins `i` into the two
translate-triples or a doubling fiber. -/
theorem nonDist_inner_subset (u j d : ZMod m) :
    (((Finset.univ \ {(0 : ZMod m)}).filter (fun i => d - j - i ≠ 0)).filter
        (fun i => ¬ allCosetsDistinct u i (d - j - i) j))
      ⊆ pairBad u j d ∪ doubleBad u j d := by
  intro i hi
  have hpred : ¬ allCosetsDistinct u i (d - j - i) j := (Finset.mem_filter.mp hi).2
  unfold allCosetsDistinct at hpred
  rw [Finset.mem_union]
  rcases not_and_or.mp hpred with hX | hYZ
  · -- `inH u ((d−j−i) − i)`: the doubling-fiber branch
    have hX' : inH u (d - j - i - i) := not_not.mp hX
    right
    simp only [doubleBad, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hX' with h | h | h
    · exact Or.inl (by linear_combination -h)
    · exact Or.inr (Or.inl (by linear_combination -h))
    · exact Or.inr (Or.inr (by linear_combination -h))
  · rcases not_and_or.mp hYZ with hY | hZ
    · -- `inH u (j − i)`: first translate triple
      have hY' : inH u (j - i) := not_not.mp hY
      left
      simp only [pairBad, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      rcases hY' with h | h | h
      · exact Or.inl (Or.inl (by linear_combination -h))
      · exact Or.inl (Or.inr (Or.inl (by linear_combination -h)))
      · exact Or.inl (Or.inr (Or.inr (by linear_combination -h)))
    · -- `inH u (j − (d−j−i))`: second translate triple
      have hZ' : inH u (j - (d - j - i)) := not_not.mp hZ
      left
      simp only [pairBad, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      rcases hZ' with h | h | h
      · exact Or.inr (Or.inl (by linear_combination h))
      · exact Or.inr (Or.inr (Or.inl (by linear_combination h)))
      · exact Or.inr (Or.inr (Or.inr (by linear_combination h)))

/-- Explicit three-element sets have at most three elements. -/
theorem card_triple_le (a b c : ZMod m) : ({a, b, c} : Finset (ZMod m)).card ≤ 3 := by
  classical
  calc ({a, b, c} : Finset (ZMod m)).card
      ≤ ({b, c} : Finset (ZMod m)).card + 1 := Finset.card_insert_le _ _
    _ ≤ (({c} : Finset (ZMod m)).card + 1) + 1 :=
        Nat.add_le_add_right (Finset.card_insert_le _ _) 1
    _ = 3 := by rw [Finset.card_singleton]

/-- **Count-thinness**: the bad `i`-set for fixed `(d,j)` has at most `6 + 3k₂`
elements, `k₂` the 2-torsion kernel size. -/
theorem card_nonDist_inner_le (u j d : ZMod m) {k₂ : ℕ}
    (hk₂ : (Finset.univ.filter (fun i : ZMod m => 2 * i = 0)).card ≤ k₂) :
    (((Finset.univ \ {(0 : ZMod m)}).filter (fun i => d - j - i ≠ 0)).filter
        (fun i => ¬ allCosetsDistinct u i (d - j - i) j)).card ≤ 6 + 3 * k₂ := by
  classical
  refine le_trans (Finset.card_le_card (nonDist_inner_subset u j d)) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  have hpair : (pairBad u j d).card ≤ 6 := by
    refine le_trans (Finset.card_union_le _ _) ?_
    have h1 := card_triple_le (m := m) j (j - u) (j - u - u)
    have h2 := card_triple_le (m := m) (d - 2 * j) (d - 2 * j + u) (d - 2 * j + u + u)
    omega
  have hdouble : (doubleBad u j d).card ≤ 3 * k₂ := by
    refine le_trans (Finset.card_union_le _ _) ?_
    have h2 : ((Finset.univ.filter (fun i : ZMod m => 2 * i = d - j - u)).card
        + (Finset.univ.filter (fun i : ZMod m => 2 * i = d - j - u - u)).card) ≤ 2 * k₂ := by
      have ha := le_trans (card_double_fiber_le_card_kernel (m := m) (d - j - u)) hk₂
      have hb := le_trans (card_double_fiber_le_card_kernel (m := m) (d - j - u - u)) hk₂
      omega
    have h1 := le_trans (card_double_fiber_le_card_kernel (m := m) (d - j)) hk₂
    refine le_trans (Nat.add_le_add h1 (le_trans (Finset.card_union_le _ _) h2)) ?_
    omega
  omega

/-- Generic norm bound for a triple-product sum over an index set of bounded size. -/
theorem norm_triple_sum_le {J : ZMod m → ℂ} {B : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ i : ZMod m, ‖J i‖ ≤ B) (S : Finset (ZMod m)) {n : ℕ} (hS : S.card ≤ n)
    (j d : ZMod m) :
    ‖∑ i ∈ S, J i * J (d - j - i) * J j‖ ≤ (n : ℝ) * B ^ 3 := by
  calc ‖∑ i ∈ S, J i * J (d - j - i) * J j‖
      ≤ ∑ i ∈ S, ‖J i * J (d - j - i) * J j‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ S, B ^ 3 := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [norm_mul, norm_mul]
        calc ‖J i‖ * ‖J (d - j - i)‖ * ‖J j‖
            ≤ B * B * B := by
              refine mul_le_mul (mul_le_mul (hJ i) (hJ (d - j - i))
                (norm_nonneg _) hB0) (hJ j) (norm_nonneg _) (by positivity)
          _ = B ^ 3 := by ring
    _ = (S.card : ℝ) * B ^ 3 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ) * B ^ 3 := by
        have : (S.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hS
        exact mul_le_mul_of_nonneg_right this (by positivity)

/-- **The unconditional non-distinct envelope**: `‖nonDist(d)‖ ≤ m·(6+3k₂)·B³`. -/
theorem norm_nonDistStratum_le {J : ZMod m → ℂ} {B : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ i : ZMod m, ‖J i‖ ≤ B) (u d : ZMod m) {k₂ : ℕ}
    (hk₂ : (Finset.univ.filter (fun i : ZMod m => 2 * i = 0)).card ≤ k₂) :
    ‖nonDistStratum J u d‖ ≤ (m : ℝ) * ((6 + 3 * k₂ : ℕ) : ℝ) * B ^ 3 := by
  unfold nonDistStratum
  calc ‖∑ j ∈ Finset.univ \ {(0 : ZMod m)}, ∑ i ∈ _, J i * J (d - j - i) * J j‖
      ≤ ∑ j ∈ Finset.univ \ {(0 : ZMod m)},
          ‖∑ i ∈ ((Finset.univ \ {(0 : ZMod m)}).filter (fun i => d - j - i ≠ 0)).filter
              (fun i => ¬ allCosetsDistinct u i (d - j - i) j),
            J i * J (d - j - i) * J j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.univ \ {(0 : ZMod m)}, ((6 + 3 * k₂ : ℕ) : ℝ) * B ^ 3 := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        exact norm_triple_sum_le hB0 hJ _ (card_nonDist_inner_le u j d hk₂) j d
    _ = ((Finset.univ \ {(0 : ZMod m)}).card : ℝ) * (((6 + 3 * k₂ : ℕ) : ℝ) * B ^ 3) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (m : ℝ) * (((6 + 3 * k₂ : ℕ) : ℝ) * B ^ 3) := by
        have hcard : ((Finset.univ \ {(0 : ZMod m)}).card : ℝ) ≤ (m : ℝ) := by
          have hle : (Finset.univ \ {(0 : ZMod m)}).card
              ≤ (Finset.univ : Finset (ZMod m)).card :=
            Finset.card_le_card (fun j _ => Finset.mem_univ j)
          simpa [ZMod.card] using (Nat.cast_le.mpr hle : _)
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (m : ℝ) * ((6 + 3 * k₂ : ℕ) : ℝ) * B ^ 3 := by ring

/-- **Unconditional non-distinct energy**: `∑_d ‖nonDist‖² ≤ (6+3k₂)²·m³·B⁶`. -/
theorem nonDistStratum_energy_le {J : ZMod m → ℂ} {B : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ i : ZMod m, ‖J i‖ ≤ B) (u : ZMod m) {k₂ : ℕ}
    (hk₂ : (Finset.univ.filter (fun i : ZMod m => 2 * i = 0)).card ≤ k₂) :
    ∑ d : ZMod m, ‖nonDistStratum J u d‖ ^ 2
      ≤ ((6 + 3 * k₂ : ℕ) : ℝ) ^ 2 * (m : ℝ) ^ 3 * B ^ 6 := by
  have hpt : ∀ d : ZMod m, ‖nonDistStratum J u d‖ ^ 2
      ≤ ((m : ℝ) * ((6 + 3 * k₂ : ℕ) : ℝ) * B ^ 3) ^ 2 := by
    intro d
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_nonDistStratum_le hB0 hJ u d hk₂) 2
  calc ∑ d : ZMod m, ‖nonDistStratum J u d‖ ^ 2
      ≤ ∑ _d : ZMod m, ((m : ℝ) * ((6 + 3 * k₂ : ℕ) : ℝ) * B ^ 3) ^ 2 :=
        Finset.sum_le_sum (fun d _ => hpt d)
    _ = ((Finset.univ : Finset (ZMod m)).card : ℝ)
        * ((m : ℝ) * ((6 + 3 * k₂ : ℕ) : ℝ) * B ^ 3) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((6 + 3 * k₂ : ℕ) : ℝ) ^ 2 * (m : ℝ) ^ 3 * B ^ 6 := by
        simp [ZMod.card]
        ring

/-! ### The minimal open Prop and the two-sided accounting -/

/-- **THE MINIMAL NAMED OPEN PROP for the r=3 rung**: Wick-scale energy of the
all-distinct-coset stratum.  Everything else in `TripleConvEnergyBound` is priced
unconditionally by counting (above).  Probe: this stratum carries the open mass
(O(0.1–0.5)·Wick, flat in `q`). -/
def DistStratumEnergyBound (J : ZMod m → ℂ) (u : ZMod m) (q : ℕ) (C : ℝ) : Prop :=
  ∑ d : ZMod m, ‖distStratum J u d‖ ^ 2 ≤ C * (m : ℝ) ^ 3 * (q : ℝ) ^ 3

private theorem sq_norm_add_le' (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  have h2 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

section Accounting

variable {J : ZMod m → ℂ} {u : ZMod m} {q : ℕ}

/-- From the classical square envelope `‖J‖² ≤ q` and `k₂ ≤ 2`:
`∑_d ‖nonDist‖² ≤ 144·m³·q³` unconditionally. -/
theorem nonDistStratum_energy_le_of_sq_bound
    (hJ : ∀ i : ZMod m, ‖J i‖ ^ 2 ≤ (q : ℝ))
    (hk₂ : (Finset.univ.filter (fun i : ZMod m => 2 * i = 0)).card ≤ 2) :
    ∑ d : ZMod m, ‖nonDistStratum J u d‖ ^ 2 ≤ 144 * (m : ℝ) ^ 3 * (q : ℝ) ^ 3 := by
  have hB0 : (0 : ℝ) ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hJroot : ∀ i : ZMod m, ‖J i‖ ≤ Real.sqrt (q : ℝ) := by
    intro i
    have h := Real.sqrt_le_sqrt (hJ i)
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  have hbase := nonDistStratum_energy_le hB0 hJroot u (k₂ := 2) hk₂
  have hsqrt : (Real.sqrt (q : ℝ)) ^ 6 = (q : ℝ) ^ 3 := by
    have hq0 : 0 ≤ (q : ℝ) := by positivity
    have hs2 : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := Real.sq_sqrt hq0
    calc (Real.sqrt (q : ℝ)) ^ 6 = ((Real.sqrt (q : ℝ)) ^ 2) ^ 3 := by ring
      _ = (q : ℝ) ^ 3 := by rw [hs2]
  calc ∑ d : ZMod m, ‖nonDistStratum J u d‖ ^ 2
      ≤ ((6 + 3 * 2 : ℕ) : ℝ) ^ 2 * (m : ℝ) ^ 3 * (Real.sqrt (q : ℝ)) ^ 6 := hbase
    _ = 144 * (m : ℝ) ^ 3 * (q : ℝ) ^ 3 := by
        rw [hsqrt]
        norm_num

/-- **FORWARD ACCOUNTING**: the DIST-stratum bound supplies the calibrated r=3
open core with constant `2·C_D + 288`, given only the classical coefficient
envelope.  The rung's dependency graph is now `DistStratumEnergyBound` ALONE. -/
theorem tripleConvEnergyBound_of_distStratum
    (hJ : ∀ i : ZMod m, ‖J i‖ ^ 2 ≤ (q : ℝ))
    (hk₂ : (Finset.univ.filter (fun i : ZMod m => 2 * i = 0)).card ≤ 2)
    {C_D : ℝ} (hD : DistStratumEnergyBound J u q C_D) :
    TripleConvEnergyBound J q (2 * C_D + 288) := by
  unfold TripleConvEnergyBound
  unfold DistStratumEnergyBound at hD
  have hnon := nonDistStratum_energy_le_of_sq_bound (u := u) hJ hk₂
  have hsplit : ∑ d : ZMod m, ‖tripleConv J d‖ ^ 2
      ≤ 2 * (∑ d : ZMod m, ‖distStratum J u d‖ ^ 2)
        + 2 * (∑ d : ZMod m, ‖nonDistStratum J u d‖ ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun d _ => ?_)
    rw [tripleConv_eq_dist_add_nonDist J u d]
    exact sq_norm_add_le' _ _
  nlinarith [hsplit, hnon, hD]

/-- **REVERSE ACCOUNTING**: conversely, the r=3 open core bounds the DIST stratum
with constant `2·C + 288` — the localization is two-sided. -/
theorem distStratumEnergyBound_of_tripleConvEnergyBound
    (hJ : ∀ i : ZMod m, ‖J i‖ ^ 2 ≤ (q : ℝ))
    (hk₂ : (Finset.univ.filter (fun i : ZMod m => 2 * i = 0)).card ≤ 2)
    {C : ℝ} (hT : TripleConvEnergyBound J q C) :
    DistStratumEnergyBound J u q (2 * C + 288) := by
  unfold DistStratumEnergyBound
  unfold TripleConvEnergyBound at hT
  have hnon := nonDistStratum_energy_le_of_sq_bound (u := u) hJ hk₂
  have hsplit : ∑ d : ZMod m, ‖distStratum J u d‖ ^ 2
      ≤ 2 * (∑ d : ZMod m, ‖tripleConv J d‖ ^ 2)
        + 2 * (∑ d : ZMod m, ‖nonDistStratum J u d‖ ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun d _ => ?_)
    have hEq : distStratum J u d = tripleConv J d + (- nonDistStratum J u d) := by
      have := tripleConv_eq_dist_add_nonDist J u d
      linear_combination -this
    rw [hEq]
    have := sq_norm_add_le' (tripleConv J d) (- nonDistStratum J u d)
    rwa [norm_neg] at this
  nlinarith [hsplit, hnon, hT]

/-- **Instantiability at the trivial calibration**: `C = m²` always works — the
R23 baseline `m²` gap is provably confined to the DIST stratum. -/
theorem distStratumEnergyBound_trivial
    (hJ : ∀ i : ZMod m, ‖J i‖ ^ 2 ≤ (q : ℝ)) :
    DistStratumEnergyBound J u q ((m : ℝ) ^ 2) := by
  unfold DistStratumEnergyBound
  have hB0 : (0 : ℝ) ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hJroot : ∀ i : ZMod m, ‖J i‖ ≤ Real.sqrt (q : ℝ) := by
    intro i
    have h := Real.sqrt_le_sqrt (hJ i)
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  have hsqrt : (Real.sqrt (q : ℝ)) ^ 6 = (q : ℝ) ^ 3 := by
    have hq0 : 0 ≤ (q : ℝ) := by positivity
    have hs2 : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := Real.sq_sqrt hq0
    calc (Real.sqrt (q : ℝ)) ^ 6 = ((Real.sqrt (q : ℝ)) ^ 2) ^ 3 := by ring
      _ = (q : ℝ) ^ 3 := by rw [hs2]
  have hpt : ∀ d : ZMod m, ‖distStratum J u d‖
      ≤ (m : ℝ) * ((m : ℕ) : ℝ) * (Real.sqrt (q : ℝ)) ^ 3 := by
    intro d
    unfold distStratum
    calc ‖∑ j ∈ Finset.univ \ {(0 : ZMod m)}, ∑ i ∈ _, J i * J (d - j - i) * J j‖
        ≤ ∑ j ∈ Finset.univ \ {(0 : ZMod m)},
            ‖∑ i ∈ ((Finset.univ \ {(0 : ZMod m)}).filter (fun i => d - j - i ≠ 0)).filter
                (fun i => allCosetsDistinct u i (d - j - i) j),
              J i * J (d - j - i) * J j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.univ \ {(0 : ZMod m)},
            ((m : ℕ) : ℝ) * (Real.sqrt (q : ℝ)) ^ 3 := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          refine norm_triple_sum_le hB0 hJroot _ ?_ j d
          calc (((Finset.univ \ {(0 : ZMod m)}).filter (fun i => d - j - i ≠ 0)).filter
                (fun i => allCosetsDistinct u i (d - j - i) j)).card
              ≤ (Finset.univ : Finset (ZMod m)).card :=
                Finset.card_le_card (fun i _ => Finset.mem_univ i)
            _ = m := ZMod.card m
      _ = ((Finset.univ \ {(0 : ZMod m)}).card : ℝ)
          * (((m : ℕ) : ℝ) * (Real.sqrt (q : ℝ)) ^ 3) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (m : ℝ) * (((m : ℕ) : ℝ) * (Real.sqrt (q : ℝ)) ^ 3) := by
          have hcard : ((Finset.univ \ {(0 : ZMod m)}).card : ℝ) ≤ (m : ℝ) := by
            have hle : (Finset.univ \ {(0 : ZMod m)}).card
                ≤ (Finset.univ : Finset (ZMod m)).card :=
              Finset.card_le_card (fun j _ => Finset.mem_univ j)
            simpa [ZMod.card] using (Nat.cast_le.mpr hle : _)
          exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (m : ℝ) * ((m : ℕ) : ℝ) * (Real.sqrt (q : ℝ)) ^ 3 := by ring
  calc ∑ d : ZMod m, ‖distStratum J u d‖ ^ 2
      ≤ ∑ _d : ZMod m, ((m : ℝ) * ((m : ℕ) : ℝ) * (Real.sqrt (q : ℝ)) ^ 3) ^ 2 := by
        refine Finset.sum_le_sum (fun d _ => ?_)
        exact pow_le_pow_left₀ (norm_nonneg _) (hpt d) 2
    _ = ((Finset.univ : Finset (ZMod m)).card : ℝ)
        * ((m : ℝ) * ((m : ℕ) : ℝ) * (Real.sqrt (q : ℝ)) ^ 3) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (m : ℝ) ^ 2 * (m : ℝ) ^ 3 * (Real.sqrt (q : ℝ)) ^ 6 := by
        simp [ZMod.card]
        ring
    _ = (m : ℝ) ^ 2 * (m : ℝ) ^ 3 * (q : ℝ) ^ 3 := by rw [hsqrt]

end Accounting

/-! ### Ladder rungs: the Prop discharges with `C = 0` when there are ≤ 2 cosets -/

/-- At `m = 3` (`u = 1`, a single coset) the DIST pattern is empty (kernel-checked). -/
theorem distStratum_eq_zero_m3 (J : ZMod 3 → ℂ) (d : ZMod 3) :
    distStratum J 1 d = 0 := by
  unfold distStratum
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [Finset.filter_false_of_mem, Finset.sum_empty]
  intro i _
  exact (by decide : ∀ d j i : ZMod 3, ¬ allCosetsDistinct 1 i (d - j - i) j) d j i

/-- At `m = 6` (`u = 2`, two cosets) the DIST pattern is empty by pigeonhole
(kernel-checked). -/
theorem distStratum_eq_zero_m6 (J : ZMod 6 → ℂ) (d : ZMod 6) :
    distStratum J 2 d = 0 := by
  unfold distStratum
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [Finset.filter_false_of_mem, Finset.sum_empty]
  intro i _
  exact (by decide : ∀ d j i : ZMod 6, ¬ allCosetsDistinct 2 i (d - j - i) j) d j i

/-- **Ladder rung m = 3**: the minimal open Prop holds with `C = 0` for every
coefficient sequence and every `q`. -/
theorem distStratumEnergyBound_rung_m3 (J : ZMod 3 → ℂ) (q : ℕ) :
    DistStratumEnergyBound J 1 q 0 := by
  unfold DistStratumEnergyBound
  simp [distStratum_eq_zero_m3]

/-- **Ladder rung m = 6**: likewise with `C = 0`. -/
theorem distStratumEnergyBound_rung_m6 (J : ZMod 6 → ℂ) (q : ℕ) :
    DistStratumEnergyBound J 2 q 0 := by
  unfold DistStratumEnergyBound
  simp [distStratum_eq_zero_m6]

end ArkLib.ProximityGap.Frontier.R300DistStratumAccounting

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.R300DistStratumAccounting in
#print axioms tripleConv_eq_dist_add_nonDist
open ArkLib.ProximityGap.Frontier.R300DistStratumAccounting in
#print axioms nonDist_inner_subset
open ArkLib.ProximityGap.Frontier.R300DistStratumAccounting in
#print axioms card_nonDist_inner_le
open ArkLib.ProximityGap.Frontier.R300DistStratumAccounting in
#print axioms nonDistStratum_energy_le
open ArkLib.ProximityGap.Frontier.R300DistStratumAccounting in
#print axioms tripleConvEnergyBound_of_distStratum
open ArkLib.ProximityGap.Frontier.R300DistStratumAccounting in
#print axioms distStratumEnergyBound_of_tripleConvEnergyBound
open ArkLib.ProximityGap.Frontier.R300DistStratumAccounting in
#print axioms distStratumEnergyBound_trivial
open ArkLib.ProximityGap.Frontier.R300DistStratumAccounting in
#print axioms distStratumEnergyBound_rung_m3
open ArkLib.ProximityGap.Frontier.R300DistStratumAccounting in
#print axioms distStratumEnergyBound_rung_m6

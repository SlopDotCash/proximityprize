/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G182DyadicKernelCeiling

/-!
# G206: the dyadic cross-orbit CLASS-COUNT CAP at depth `2` — at most `m = n/2` orbit
classes carry any depth-`2` mass, forcing a thinness floor on the cross-orbit tail

## Context: the sole open object at depth `2`

G88's orbit-class Parseval identity (`centeredShadowMass_orbitClassParseval`) writes the
DC-centered deep-wall numerator as a positive quadratic form in the orbit-class masses:

`n · centeredShadowMass = q·(n·S₀² + Σ_γ S_γ²) − n·n^(2r)`,

with `S₀ = repRF g n r 0` the kernel-class mass and `S_γ = orbitClassMass g n r γ` the
cross-orbit masses.  G182 closed the depth-`2` kernel side exactly (`S₀ = n`).  G88's wall
floor uses only the trivial `Σ_γ S_γ² ≥ 0`, leaving the cross-orbit tail `Σ_γ S_γ²` as the
sole remaining freedom at depth `2` (doctrine v3).

**This file bounds that tail from below by a thinness-forced constant.**  The mechanism is a
hard cap on the NUMBER of occupied cross-orbit classes.

## The class-count cap (the invariant)

At depth `2` an occupied class is `γ = c^n` for some representable nonzero value
`c = g^a + g^b`.  Factoring out the frame index,
`c = g^a·(1 + g^{b-a})`, and since `(g^a)^n = 1`, the class label collapses to

`γ = (1 + g^{b-a})^n = dClass g n d`,   `d := b - a ∈ Fin n`.

The kernel value `d = m` is excluded (`1 + g^m = 1 + (-1) = 0`, contributing to `S₀`, not a
cross class).  Crucially the **thinness involution** `d ↦ n - d` fixes the class:

`1 + g^{n-d} = g^{-d}·(g^d + 1)`  and  `(g^{-d})^n = 1`  ⇒  `dClass g n (n-d) = dClass g n d`.

On `Fin n \ {m}` this involution has the single fixed point `d = 0` and folds the remaining
`n - 2` indices into `(m - 1)` pairs, so the occupied classes are the image of just `m`
representatives `d ∈ {0, 1, …, m-1}`.  Hence

**`(occupiedDepth2Classes g n).card ≤ m`**  (`occupiedDepth2Classes_card_le_half`).

## Thinness essential

For an ODD-order subgroup `-1 ∉ ⟨g⟩`, the depth-`2` kernel is empty and there is no half-shift
`m` with `g^m = -1`; the `d ↦ n - d` folding and the kernel exclusion at `d = m` both use
`g^m = -1` and even order `n = 2m`.  The `≤ m` cap is a 2-power-subgroup fact.

## Consequence: the cross-orbit tail floor and a sharper wall floor

`Σ_γ S_γ = n^2 - S₀ = n² - n = n(n-1)` (`sum_orbitClassMass_eq` + `repRF_two_zero_eq`).  The
cap `card ≤ m = n/2` feeds directly into Cauchy–Schwarz `(Σ_γ S_γ)² ≤ card · Σ_γ S_γ²`, giving
the `p`-independent lower bound formalized here:

`Σ_γ S_γ² ≥ 2·n·(n - 1)²`   (`crossOrbitTail_two_floor`).

(The sharp integer-partition floor `n²(2n - 3)` — proved separately in G209 under the same
`card ≤ n/2` hypothesis, using the finer quantisation `S_γ = n·k_γ` — is about `1%` larger; it
is NOT re-derived in this file.  What THIS file adds is the structural cap on the CORE object
that discharges G209/G210's `ks.card ≤ n/2` premise.)  Substituted into G88's Parseval with
`S₀ = n`, the Cauchy–Schwarz floor upgrades the wall floor from the kernel-only
`q·n² − n⁴ ≤ centeredShadowMass` (G182) to

`q·(n² + 2(n-1)²) − n⁴ ≤ centeredShadowMass`   (`dyadic_wall_floor_two_with_tail`),

adding a strictly positive cross-orbit term `q·2(n-1)² > 0` on top of the kernel floor.
-/

namespace ArkLib.ProximityGap.Frontier.G206DyadicCrossOrbitClassCap

open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence
open ArkLib.ProximityGap.Frontier.G182DyadicKernelCeiling
open ArkLib.ProximityGap.Frontier.R365CenteredShadowMassWeld

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The class label attached to a difference index `d`: `(1 + g^d)^n`. -/
def dClass (g : F) (n d : ℕ) : F := (1 + g ^ d) ^ n

/-- The set of depth-`2` cross-orbit classes carrying positive mass. -/
noncomputable def occupiedDepth2Classes (g : F) (n : ℕ) : Finset F :=
  (orbitClassSet F n).filter (fun γ => 0 < orbitClassMass g n 2 γ)

/-- **Difference reduction.**  A representable nonzero value `g^a + g^b` has orbit-class label
`(1 + g^{b-a})^n`, i.e. `dClass g n (b - a)` at the difference index taken in `Fin n`.  Only the
difference `b - a` (mod `n`) matters. -/
theorem class_eq_dClass (g : F) (n : ℕ) (hord : orderOf g = n)
    (a b : Fin n) :
    (g ^ (a : ℕ) + g ^ (b : ℕ)) ^ n = dClass g n ((b + (n - a) : ℕ)) := by
  -- g^a + g^b = g^a · (1 + g^{b - a}) with b - a taken as (b + (n - a)) so the exponent is ℕ
  have hgn : g ^ n = 1 := by rw [← hord]; exact pow_orderOf_eq_one g
  have hfac : g ^ (a : ℕ) + g ^ (b : ℕ) = g ^ (a : ℕ) * (1 + g ^ ((b + (n - a) : ℕ))) := by
    have hexp : (a : ℕ) + (b + (n - a)) = n + (b : ℕ) := by omega
    have hmul : g ^ (a : ℕ) * g ^ ((b + (n - a) : ℕ)) = g ^ (b : ℕ) := by
      rw [← pow_add, hexp, pow_add, hgn, one_mul]
    rw [mul_add, mul_one, hmul]
  rw [hfac, mul_pow, dClass]
  have hgan : (g ^ (a : ℕ)) ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hgn, one_pow]
  rw [hgan, one_mul]

/-- **The thinness involution.**  `dClass g n (n - d) = dClass g n d`: the difference index `d`
and its negation `n - d` label the same orbit class, because `1 + g^{n-d} = g^{n-d}·(1 + g^d)`
and `(g^{n-d})^n = 1`. -/
theorem dClass_reflect (g : F) (n d : ℕ) (hord : orderOf g = n)
    (hd : d ≤ n) :
    dClass g n (n - d) = dClass g n d := by
  unfold dClass
  have hgn : g ^ n = 1 := by rw [← hord]; exact pow_orderOf_eq_one g
  -- 1 + g^{n-d} = g^{n-d} · (1 + g^d)  (since g^{n-d}·g^d = g^n = 1)
  have hprod : g ^ (n - d) * g ^ d = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hd, hgn]
  have hfac : 1 + g ^ (n - d) = g ^ (n - d) * (1 + g ^ d) := by
    rw [mul_add, mul_one, hprod]; ring
  rw [hfac, mul_pow]
  have hgndn : (g ^ (n - d)) ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hgn, one_pow]
  rw [hgndn, one_mul]

/-- **Occupied classes are labelled by `d ∈ {0, …, m-1}`.**  Every depth-`2` class with positive
mass is `dClass g n d` for some difference index `d < m`, using difference reduction, the
kernel exclusion at `d = m`, and the `d ↦ n - d` folding to land the representative below `m`. -/
theorem occupiedDepth2Classes_subset_image (g : F) (n m : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    occupiedDepth2Classes g n ⊆ (Finset.range m).image (dClass g n) := by
  have hn0 : 0 < n := by omega
  intro γ hγ
  simp only [occupiedDepth2Classes, Finset.mem_filter] at hγ
  obtain ⟨hγset, hγpos⟩ := hγ
  -- positive class mass ⇒ some representative c with repRF ≥ 1 ⇒ some (a,b) with g^a+g^b = c
  simp only [orbitClassSet, Finset.mem_image] at hγset
  obtain ⟨c, hcmem, rfl⟩ := hγset
  have hc0 : c ≠ 0 := by
    simp only [nonkernelValues, Finset.mem_filter] at hcmem; exact hcmem.2
  -- mass positive ⇒ repRF g n 2 c > 0 (mass = n · repRF c)
  have hmass : orbitClassMass g n 2 (c ^ n) = (n : ℝ) * (repRF g n 2 c : ℝ) :=
    orbitClassMass_eq_card_mul g n 2 hg0 hn0 hord hc0
  rw [hmass] at hγpos
  have hrep : 0 < repRF g n 2 c := by
    rcases Nat.eq_zero_or_pos (repRF g n 2 c) with h0 | hpos
    · rw [h0] at hγpos; simp at hγpos
    · exact hpos
  -- extract a tuple t : Fin 2 → Fin n with gsumR = c
  have hne : (Finset.univ.filter (fun t : Fin 2 → Fin n => gsumR g n 2 t = c)).Nonempty := by
    rw [← Finset.card_pos]; exact hrep
  obtain ⟨t, ht⟩ := hne
  simp only [Finset.mem_filter] at ht
  have htc : gsumR g n 2 t = c := ht.2
  -- gsumR at depth 2 = g^{t0} + g^{t1}
  have hgsum : g ^ ((t 0 : ℕ)) + g ^ ((t 1 : ℕ)) = c := by
    have : gsumR g n 2 t = g ^ ((t 0 : ℕ)) + g ^ ((t 1 : ℕ)) := by
      unfold gsumR
      rw [Fin.sum_univ_two]
    rw [← this]; exact htc
  -- apply difference reduction
  have hdc := class_eq_dClass g n hord (t 0) (t 1)
  rw [hgsum] at hdc
  -- so γ = c^n = dClass g n D  with D := t1 + (n - t0)
  set D : ℕ := ((t 1 : ℕ) + (n - (t 0 : ℕ))) with hDdef
  rw [hdc]
  -- reduce D mod n to d0 ∈ Fin n, then fold to below m via the involution
  rw [Finset.mem_image]
  -- dClass depends only on exponent mod n: dClass g n D = dClass g n (D % n)
  have hDmod : dClass g n D = dClass g n (D % n) := by
    unfold dClass
    have hpow : g ^ (D % n) = g ^ D := by
      conv_rhs => rw [← pow_mod_orderOf g D, hord]
    rw [hpow]
  set d0 : ℕ := D % n with hd0def
  have hd0lt : d0 < n := Nat.mod_lt _ hn0
  -- d0 ≠ m: if d0 = m then 1 + g^m = 0 ⇒ dClass = 0, but the class label c^n ≠ 0
  have hlabel_ne : dClass g n d0 ≠ 0 := by
    rw [← hDmod, ← hdc]
    exact pow_ne_zero _ hc0
  have hd0nem : d0 ≠ m := by
    intro h
    apply hlabel_ne
    unfold dClass
    rw [h, hg, add_neg_cancel, zero_pow hn0.ne']
  -- fold: choose representative d < m
  by_cases hd0lo : d0 < m
  · refine ⟨d0, Finset.mem_range.mpr hd0lo, ?_⟩
    rw [hDmod]
  · -- d0 > m (since ≠ m and < n = 2m), use n - d0 < m
    have hd0gt : m < d0 := by omega
    have hnd0 : n - d0 < m := by omega
    refine ⟨n - d0, Finset.mem_range.mpr hnd0, ?_⟩
    rw [hDmod, ← dClass_reflect g n d0 hord (le_of_lt hd0lt)]

/-- **HEADLINE — the dyadic cross-orbit class-count cap.**  At depth `2` the number of orbit
classes with positive mass is at most `m = n/2`.  This is thinness-essential: the folding
`d ↦ n - d` and the kernel exclusion `d = m` both require `g^m = -1` at even order `n = 2m`. -/
theorem occupiedDepth2Classes_card_le_half (g : F) (n m : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    (occupiedDepth2Classes g n).card ≤ m := by
  calc (occupiedDepth2Classes g n).card
      ≤ ((Finset.range m).image (dClass g n)).card :=
        Finset.card_le_card (occupiedDepth2Classes_subset_image g n m hg0 hord hm hn hg)
    _ ≤ (Finset.range m).card := Finset.card_image_le
    _ = m := Finset.card_range m

/-! ## Consequence: the cross-orbit tail floor and the sharpened wall floor -/

/-- The depth-`2` cross-orbit mass sums to `n(n-1)`, restricted to the occupied classes
(zero-mass classes contribute nothing).  Uses `S₀ = n` (G182). -/
theorem sum_occupied_orbitClassMass_two (g : F) (n m : ℕ) (hm : 0 < m) (hn : n = 2 * m)
    (hg : g ^ m = -1) (hord : orderOf g = n) :
    ∑ γ ∈ occupiedDepth2Classes g n, orbitClassMass g n 2 γ = (n : ℝ) ^ 2 - (n : ℝ) := by
  -- the full class sum equals n^2 - repRF 0 = n^2 - n; zero-mass classes drop out
  have hfull : ∑ γ ∈ orbitClassSet F n, orbitClassMass g n 2 γ
      = ((n : ℝ)) ^ 2 - (repRF g n 2 0 : ℝ) := sum_orbitClassMass_eq g n 2
  rw [repRF_two_zero_eq g n m hm hn hg hord] at hfull
  -- restrict to occupied: the complementary (zero-mass) terms are all 0
  have hsplit : ∑ γ ∈ orbitClassSet F n, orbitClassMass g n 2 γ
      = ∑ γ ∈ occupiedDepth2Classes g n, orbitClassMass g n 2 γ := by
    unfold occupiedDepth2Classes
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun γ hγ => ?_)
    by_cases hpos : 0 < orbitClassMass g n 2 γ
    · rw [if_pos hpos]
    · rw [if_neg hpos]
      -- mass is nonneg and not positive ⇒ zero
      have hnonneg : 0 ≤ orbitClassMass g n 2 γ := by
        unfold orbitClassMass
        exact Finset.sum_nonneg fun c _ => by positivity
      exact le_antisymm (le_of_not_gt hpos) hnonneg
  rw [← hsplit, hfull]

/-- **The cross-orbit tail floor.**  Combining the class-count cap `≤ m` with the exact total
cross mass `n(n-1)` via Cauchy–Schwarz, the depth-`2` cross-orbit tail `Σ_γ S_γ²` is bounded
below by the thinness-forced constant `2·n·(n-1)²` — strictly above the trivial `≥ 0` that
G88's wall floor uses.  (The sharp integer-partition floor `n²(2n-3)`, `~1%` above this, is
probe-verified tight; see `probe_oc_depth2_crossorbit_tail.py`.) -/
theorem crossOrbitTail_two_floor (g : F) (n m : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    (2 : ℝ) * (n : ℝ) * ((n : ℝ) - 1) ^ 2 ≤
      ∑ γ ∈ orbitClassSet F n, orbitClassMass g n 2 γ ^ 2 := by
  have hn0 : 0 < n := by omega
  -- restrict the square-sum to occupied classes (zero-mass terms vanish)
  have hsqsplit : ∑ γ ∈ orbitClassSet F n, orbitClassMass g n 2 γ ^ 2
      = ∑ γ ∈ occupiedDepth2Classes g n, orbitClassMass g n 2 γ ^ 2 := by
    unfold occupiedDepth2Classes
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    by_cases hpos : 0 < orbitClassMass g n 2 γ
    · rw [if_pos hpos]
    · rw [if_neg hpos]
      have hnonneg : 0 ≤ orbitClassMass g n 2 γ := by
        unfold orbitClassMass
        exact Finset.sum_nonneg fun c _ => by positivity
      have hz : orbitClassMass g n 2 γ = 0 := le_antisymm (le_of_not_gt hpos) hnonneg
      rw [hz]; ring
  rw [hsqsplit]
  -- Cauchy–Schwarz: (Σ S)² ≤ card · Σ S²
  have hCS := sq_sum_le_card_mul_sum_sq (s := occupiedDepth2Classes g n)
    (f := fun γ => orbitClassMass g n 2 γ)
  rw [sum_occupied_orbitClassMass_two g n m hm hn hg hord] at hCS
  -- card ≤ m and m = n/2, so card ≤ (n:ℝ)/2
  have hcard : ((occupiedDepth2Classes g n).card : ℝ) ≤ (n : ℝ) / 2 := by
    have hc := occupiedDepth2Classes_card_le_half g n m hg0 hord hm hn hg
    have : ((occupiedDepth2Classes g n).card : ℝ) ≤ (m : ℝ) := by exact_mod_cast hc
    have hmn : (m : ℝ) = (n : ℝ) / 2 := by
      have : (n : ℝ) = 2 * (m : ℝ) := by exact_mod_cast hn
      linarith
    linarith
  -- so ((n²-n))² ≤ (n/2) · Σ S²  ⇒  Σ S² ≥ 2(n²-n)²/n = 2n(n-1)²
  have hSsq : (0 : ℝ) ≤ ∑ γ ∈ occupiedDepth2Classes g n, orbitClassMass g n 2 γ ^ 2 :=
    Finset.sum_nonneg fun γ _ => sq_nonneg _
  have hlhs : ((n : ℝ) ^ 2 - (n : ℝ)) ^ 2 ≤
      ((n : ℝ) / 2) * ∑ γ ∈ occupiedDepth2Classes g n, orbitClassMass g n 2 γ ^ 2 := by
    calc ((n : ℝ) ^ 2 - (n : ℝ)) ^ 2
        ≤ ((occupiedDepth2Classes g n).card : ℝ) *
            ∑ γ ∈ occupiedDepth2Classes g n, orbitClassMass g n 2 γ ^ 2 := hCS
      _ ≤ ((n : ℝ) / 2) * ∑ γ ∈ occupiedDepth2Classes g n, orbitClassMass g n 2 γ ^ 2 :=
          mul_le_mul_of_nonneg_right hcard hSsq
  -- algebra: (n²-n)² = n²(n-1)², and ≤ (n/2)·T ⇒ 2n(n-1)² ≤ T
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hfactor : ((n : ℝ) ^ 2 - (n : ℝ)) ^ 2 = (n : ℝ) ^ 2 * ((n : ℝ) - 1) ^ 2 := by ring
  rw [hfactor] at hlhs
  -- from n²(n-1)² ≤ (n/2)·T, multiply through: T ≥ 2n(n-1)²
  nlinarith [hlhs, hnpos, sq_nonneg ((n : ℝ) - 1), hSsq]

/-- **Sharpened dyadic wall floor at depth `2`.**  Feeding `S₀ = n` (G182) and the cross-orbit
tail floor into G88's orbit-class Parseval identity yields a wall floor strictly above the
kernel-only floor of G182: the cross-orbit classes contribute an extra positive
`q·2(n-1)²` term. -/
theorem dyadic_wall_floor_two_with_tail (g : F) (n m : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    (Fintype.card F : ℝ) * ((n : ℝ) ^ 2 + 2 * ((n : ℝ) - 1) ^ 2) - (n : ℝ) ^ 4 ≤
      centeredShadowMass g n m 2 := by
  have hn0 : 0 < n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  -- Parseval: n·centeredShadowMass = q·(n·S₀² + Σ S_γ²) − n·n^4
  have hpar := centeredShadowMass_orbitClassParseval g n m 2 hg0 hord hm hn hg
  -- S₀ = n
  have hS0 : (repRF g n 2 0 : ℝ) = (n : ℝ) := by
    have := repRF_two_zero_eq g n m hm hn hg hord
    exact_mod_cast this
  rw [hS0] at hpar
  -- tail floor
  have htail := crossOrbitTail_two_floor g n m hg0 hord hm hn hg
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := Nat.cast_nonneg _
  -- n · centeredShadowMass ≥ q·(n·n² + 2n(n-1)²) − n·n^4  = n·[ q(n²+2(n-1)²) − n^4 ]
  -- normalise n^(2*2) = n^4 in the Parseval identity
  have hpow : (n : ℝ) ^ (2 * 2) = (n : ℝ) ^ 4 := by norm_num
  rw [hpow] at hpar
  -- q · Σ ≥ q · 2n(n-1)²  (scale the tail floor by the nonneg field size)
  have hqtail : (Fintype.card F : ℝ) * (2 * (n : ℝ) * ((n : ℝ) - 1) ^ 2)
      ≤ (Fintype.card F : ℝ) * ∑ γ ∈ orbitClassSet F n, orbitClassMass g n 2 γ ^ 2 :=
    mul_le_mul_of_nonneg_left htail hq
  have hkey : (n : ℝ) * ((Fintype.card F : ℝ) * ((n : ℝ) ^ 2 + 2 * ((n : ℝ) - 1) ^ 2)
        - (n : ℝ) ^ 4) ≤ (n : ℝ) * centeredShadowMass g n m 2 := by
    rw [hpar]
    nlinarith [hqtail, hnpos, hq]
  -- cancel the positive factor n
  exact le_of_mul_le_mul_left hkey hnpos

end ArkLib.ProximityGap.Frontier.G206DyadicCrossOrbitClassCap

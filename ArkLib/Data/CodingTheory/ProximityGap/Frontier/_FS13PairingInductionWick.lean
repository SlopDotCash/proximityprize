/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS12ZeroSumCountBijection
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# LANE FS13 (#466, Fable session 2026-07-09): THE PAIRING INDUCTION — the depth-generic
  char-0 Wick census `trivialCountG m r ≤ (2r−1)‼·(2m)^r`, closing the ledger's last input

On FS12's one-sided object `zeroSumCount m N` the classical Wick union bound is a clean
removal induction, formalized here:

* `coeff_sum_monomF` — the coefficient of `Σᵢ μ(cᵢ)` at a residue `res < m` is the signed
  occupancy `#{i : cᵢ = res} − #{i : cᵢ = res + m}`.
* `exists_partner` — in a zero-sum tuple every item has a cancelling `m`-shifted partner.
* **`zeroSumCount_step`** — `Z(N+2) ≤ (N+1)·2m·Z(N)`: remove the last item with a partner;
  the tuple is reconstructible from (partner position, last value, remainder)
  (`Fin.snoc`/`Fin.insertNth` surgery).
* **`zeroSumCount_le_wick`** — `Z(2r) ≤ (2r−1)‼·(2m)^r`, and via FS12
  **`trivialCountG_le_wick`** : `trivialCountG m r ≤ (2r−1)‼·(2m)^r`.

**What this completes:** the depth-generic ledger (FS1–FS3 + FS11 + FS12 + this brick) has
NO open census input at ANY depth — the char-0 half of the depth-`r` energy of `μ_n` is
Wick-bounded unconditionally, machine-checked, with no Lam–Leung import.  Composed with
FS11, `rEnergy(μ_n) r ≤ (2r−1)‼·n^r + wraparoundExcessG r`, and the FS1 T=1 ledger caps the
primes carrying any excess.

**Honest scope:** fixed depth `r`; the exceptional-prime budget grows like `n^{2r+1}`, so
the deep-`r` (`r ≈ ln q`) joint limit — the prize wall — remains untouched.

Issue #466, lane FS13.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.FS13PairingInductionWick

open ArkLib.ProximityGap.Frontier.FS4Depth3PatternDecomposition
open ArkLib.ProximityGap.Frontier.FS11GenericDepthDecomposition
open ArkLib.ProximityGap.Frontier.FS12ZeroSumCountBijection

open scoped Classical

/-- Folded-monomial coefficient at a low residue: the signed indicator. -/
theorem monomF_coeff_eq {m x res : ℕ} (hx : x < 2 * m) (hres : res < m) :
    (monomF m x).coeff res
      = (if x = res then (1 : ℤ) else 0) - (if x = res + m then (1 : ℤ) else 0) := by
  unfold monomF
  by_cases h : x < m
  · rw [if_pos h, coeff_X_pow]
    by_cases hxr : x = res
    · rw [if_pos hxr.symm, if_pos hxr, if_neg (by omega)]
      ring
    · rw [if_neg (fun hh => hxr hh.symm), if_neg hxr, if_neg (by omega)]
      ring
  · rw [if_neg h, coeff_neg, coeff_X_pow]
    by_cases hxr : x = res + m
    · rw [if_pos (by omega : res = x - m), if_neg (by omega), if_pos hxr]
      ring
    · rw [if_neg (by omega : ¬ res = x - m), if_neg (by omega), if_neg hxr]
      ring

/-- The coefficient of the one-sided sum at `res < m` is the signed occupancy count. -/
theorem coeff_sum_monomF {m N : ℕ} (c : Fin N → ℕ) (hc : ∀ i, c i < 2 * m)
    {res : ℕ} (hres : res < m) :
    (∑ i, monomF m (c i)).coeff res
      = ((univ.filter (fun i => c i = res)).card : ℤ)
        - ((univ.filter (fun i => c i = res + m)).card : ℤ) := by
  rw [Polynomial.finset_sum_coeff]
  have hpt : ∀ i : Fin N, (monomF m (c i)).coeff res
      = (if c i = res then (1 : ℤ) else 0) - (if c i = res + m then (1 : ℤ) else 0) :=
    fun i => monomF_coeff_eq (hc i) hres
  rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_sub_distrib]
  congr 1 <;>
    · rw [Finset.card_filter]
      push_cast
      rfl

/-- **Partner existence.**  In a zero-sum tuple, every item has an `m`-shifted partner at a
different index. -/
theorem exists_partner {m N : ℕ} (hm : 0 < m) (c : Fin N → ℕ) (hc : ∀ i, c i < 2 * m)
    (hzero : (∑ i, monomF m (c i)) = 0) (i0 : Fin N) :
    ∃ j, j ≠ i0 ∧ c j = mshift m (c i0) := by
  set v := c i0 with hv
  have hvlt : v < 2 * m := hc i0
  set res : ℕ := if v < m then v else v - m with hres_def
  have hres : res < m := by rw [hres_def]; split_ifs <;> omega
  have hcount := coeff_sum_monomF c hc hres
  rw [hzero, coeff_zero] at hcount
  have hcards : (univ.filter (fun i => c i = res)).card
      = (univ.filter (fun i => c i = res + m)).card := by omega
  by_cases h : v < m
  · have hvres : v = res := by rw [hres_def, if_pos h]
    have hmem : i0 ∈ univ.filter (fun i => c i = res) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← hv, hvres]⟩
    have hpos : 0 < (univ.filter (fun i => c i = res + m)).card := by
      rw [← hcards]
      exact Finset.card_pos.mpr ⟨i0, hmem⟩
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hj
    refine ⟨j, ?_, ?_⟩
    · intro hji
      rw [hji, ← hv] at hj
      omega
    · rw [hj.2, mshift, if_pos (show v < m from h)]
      omega
  · have hvres : v = res + m := by rw [hres_def, if_neg h]; omega
    have hmem : i0 ∈ univ.filter (fun i => c i = res + m) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← hv, hvres]⟩
    have hpos : 0 < (univ.filter (fun i => c i = res)).card := by
      rw [hcards]
      exact Finset.card_pos.mpr ⟨i0, hmem⟩
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hj
    refine ⟨j, ?_, ?_⟩
    · intro hji
      rw [hji, ← hv] at hj
      omega
    · rw [hj.2, mshift, if_neg (show ¬ v < m from h)]
      omega

section Step

variable {m N : ℕ}

/-- Total partner-index extractor (junk value off the zero-sum set). -/
noncomputable def partnerIdx (m : ℕ) {N : ℕ} (c : Fin (N + 2) → ℕ) : Fin (N + 2) :=
  if h : 0 < m ∧ (∀ i, c i < 2 * m) ∧ (∑ i, monomF m (c i)) = 0 then
    (exists_partner h.1 c h.2.1 h.2.2 (Fin.last (N + 1))).choose
  else 0

theorem partnerIdx_spec (hm : 0 < m) (c : Fin (N + 2) → ℕ) (hc : ∀ i, c i < 2 * m)
    (hz : (∑ i, monomF m (c i)) = 0) :
    partnerIdx m c ≠ Fin.last (N + 1)
      ∧ c (partnerIdx m c) = mshift m (c (Fin.last (N + 1))) := by
  unfold partnerIdx
  rw [dif_pos ⟨hm, hc, hz⟩]
  exact (exists_partner hm c hc hz (Fin.last (N + 1))).choose_spec

/-- Total below-last partner index. -/
noncomputable def partnerIdx' (m : ℕ) {N : ℕ} (c : Fin (N + 2) → ℕ) : Fin (N + 1) :=
  if h : partnerIdx m c ≠ Fin.last (N + 1) then (partnerIdx m c).castPred h else 0

theorem partnerIdx'_castSucc (hm : 0 < m) (c : Fin (N + 2) → ℕ) (hc : ∀ i, c i < 2 * m)
    (hz : (∑ i, monomF m (c i)) = 0) :
    Fin.castSucc (partnerIdx' m c) = partnerIdx m c := by
  obtain ⟨hne, -⟩ := partnerIdx_spec hm c hc hz
  unfold partnerIdx'
  rw [dif_pos hne]
  exact Fin.castSucc_castPred _ _

/-- The step map: (partner position, last value, remainder after removing the pair). -/
noncomputable def stepMap (m : ℕ) {N : ℕ} (c : Fin (N + 2) → ℕ) :
    Fin (N + 1) × ℕ × (Fin N → ℕ) :=
  (partnerIdx' m c, c (Fin.last (N + 1)),
    Fin.removeNth (partnerIdx' m c) (Fin.init c))

/-- Reconstruction: a zero-sum tuple is determined by its step-map image. -/
theorem stepMap_reconstruct (hm : 0 < m) (c : Fin (N + 2) → ℕ) (hc : ∀ i, c i < 2 * m)
    (hz : (∑ i, monomF m (c i)) = 0) :
    c = Fin.snoc
        (Fin.insertNth (partnerIdx' m c) (mshift m (c (Fin.last (N + 1))))
          (Fin.removeNth (partnerIdx' m c) (Fin.init c)))
        (c (Fin.last (N + 1))) := by
  obtain ⟨hne, hval⟩ := partnerIdx_spec hm c hc hz
  have hcs := partnerIdx'_castSucc hm c hc hz
  have hinit : Fin.init c (partnerIdx' m c) = mshift m (c (Fin.last (N + 1))) := by
    show c (Fin.castSucc (partnerIdx' m c)) = _
    rw [hcs, hval]
  calc c = Fin.snoc (Fin.init c) (c (Fin.last (N + 1))) := (Fin.snoc_init_self c).symm
    _ = _ := by
        congr 1
        rw [← hinit]
        exact (Fin.insertNth_self_removeNth (partnerIdx' m c) (Fin.init c)).symm

/-- The remainder of a zero-sum tuple is zero-sum. -/
theorem removeNth_zero_sum (hm : 0 < m) (c : Fin (N + 2) → ℕ) (hc : ∀ i, c i < 2 * m)
    (hz : (∑ i, monomF m (c i)) = 0) :
    (∑ i, monomF m (Fin.removeNth (partnerIdx' m c) (Fin.init c) i)) = 0 := by
  obtain ⟨hne, hval⟩ := partnerIdx_spec hm c hc hz
  have hcs := partnerIdx'_castSucc hm c hc hz
  set p : Fin (N + 1) := partnerIdx' m c with hp
  -- the composed function is removeNth of the composed function
  have hcomp : (fun i => monomF m (Fin.removeNth p (Fin.init c) i))
      = Fin.removeNth p (fun j => monomF m (Fin.init c j)) := rfl
  rw [hcomp]
  -- Σ removeNth = Σ over Fin (N+1) − value at p
  have hrem := Fin.add_sum_removeNth p (fun j => monomF m (Fin.init c j))
  -- Σ over Fin (N+1) of init = Σ over Fin (N+2) − last
  have hcast := Fin.sum_univ_castSucc (fun i : Fin (N + 2) => monomF m (c i))
  have hinitsum : (∑ j : Fin (N + 1), monomF m (Fin.init c j))
      = - monomF m (c (Fin.last (N + 1))) := by
    have heqi : (∑ j : Fin (N + 1), monomF m (Fin.init c j))
        = ∑ j : Fin (N + 1), monomF m (c (Fin.castSucc j)) := rfl
    rw [heqi]
    have hc0 := hcast
    rw [hz] at hc0
    linear_combination -hc0
  have hatp : monomF m (Fin.init c p) = - monomF m (c (Fin.last (N + 1))) := by
    have : Fin.init c p = mshift m (c (Fin.last (N + 1))) := by
      show c (Fin.castSucc p) = _
      rw [hp, hcs, hval]
    rw [this, monomF_mshift (hc _)]
  have hfin := hrem
  rw [hinitsum, hatp] at hfin
  linear_combination hfin

/-- The remainder stays in range. -/
theorem removeNth_mem_range (c : Fin (N + 2) → ℕ) (hc : ∀ i, c i < 2 * m) :
    ∀ i, Fin.removeNth (partnerIdx' m c) (Fin.init c) i < 2 * m := by
  intro i
  show c _ < 2 * m
  exact hc _

/-- **THE PAIRING STEP.**  `Z(N+2) ≤ (N+1)·2m·Z(N)`. -/
theorem zeroSumCount_step (m N : ℕ) (hm : 0 < m) :
    zeroSumCount m (N + 2) ≤ (N + 1) * (2 * m) * zeroSumCount m N := by
  unfold zeroSumCount
  have htarget :
      ((univ : Finset (Fin (N + 1))) ×ˢ range (2 * m)
        ×ˢ ((expTuples (2 * m) N).filter (fun c => (∑ i, monomF m (c i)) = 0))).card
      = (N + 1) * (2 * m)
          * ((expTuples (2 * m) N).filter (fun c => (∑ i, monomF m (c i)) = 0)).card := by
    rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_fin,
      Finset.card_range]
    ring
  rw [← htarget]
  refine Finset.card_le_card_of_injOn (stepMap m) ?_ ?_
  · -- maps into the target
    intro c hcS
    rw [Finset.mem_coe] at hcS
    rw [Finset.mem_coe]
    rw [Finset.mem_filter] at hcS
    obtain ⟨hmem, hz⟩ := hcS
    rw [expTuples, Fintype.mem_piFinset] at hmem
    have hc : ∀ i, c i < 2 * m := fun i => mem_range.mp (hmem i)
    rw [Finset.mem_product]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.mem_product]
    refine ⟨mem_range.mpr (hc _), ?_⟩
    rw [Finset.mem_filter]
    constructor
    · rw [expTuples, Fintype.mem_piFinset]
      intro i
      exact mem_range.mpr (removeNth_mem_range c hc i)
    · exact removeNth_zero_sum hm c hc hz
  · -- injective on the source
    intro c₁ hc₁S c₂ hc₂S heq
    rw [Finset.mem_coe, Finset.mem_filter] at hc₁S hc₂S
    obtain ⟨hmem₁, hz₁⟩ := hc₁S
    obtain ⟨hmem₂, hz₂⟩ := hc₂S
    rw [expTuples, Fintype.mem_piFinset] at hmem₁ hmem₂
    have hc₁ : ∀ i, c₁ i < 2 * m := fun i => mem_range.mp (hmem₁ i)
    have hc₂ : ∀ i, c₂ i < 2 * m := fun i => mem_range.mp (hmem₂ i)
    have h1 := stepMap_reconstruct hm c₁ hc₁ hz₁
    have h2 := stepMap_reconstruct hm c₂ hc₂ hz₂
    have hp : partnerIdx' m c₁ = partnerIdx' m c₂ := congrArg Prod.fst heq
    have hv : c₁ (Fin.last (N + 1)) = c₂ (Fin.last (N + 1)) :=
      congrArg (fun t => t.2.1) heq
    have hrem : Fin.removeNth (partnerIdx' m c₁) (Fin.init c₁)
        = Fin.removeNth (partnerIdx' m c₂) (Fin.init c₂) :=
      congrArg (fun t => t.2.2) heq
    rw [h1, h2, hrem, hp, hv]

end Step

/-- The empty tuple: `Z(0) = 1`. -/
theorem zeroSumCount_zero (m : ℕ) : zeroSumCount m 0 ≤ 1 := by
  unfold zeroSumCount
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [expTuples_card]
  norm_num

/-- **THE WICK CENSUS (one-sided form).**  `Z(2r) ≤ (2r−1)‼·(2m)^r`. -/
theorem zeroSumCount_le_wick (m r : ℕ) (hm : 0 < m) :
    zeroSumCount m (2 * r) ≤ Nat.doubleFactorial (2 * r - 1) * (2 * m) ^ r := by
  induction r with
  | zero =>
    simpa [Nat.doubleFactorial] using zeroSumCount_zero m
  | succ r ih =>
    have h2 : 2 * (r + 1) = 2 * r + 2 := by ring
    rw [h2]
    calc zeroSumCount m (2 * r + 2)
        ≤ (2 * r + 1) * (2 * m) * zeroSumCount m (2 * r) :=
          zeroSumCount_step m (2 * r) hm
      _ ≤ (2 * r + 1) * (2 * m)
            * (Nat.doubleFactorial (2 * r - 1) * (2 * m) ^ r) :=
          Nat.mul_le_mul_left _ ih
      _ = ((2 * r + 1) * Nat.doubleFactorial (2 * r - 1)) * (2 * m) ^ (r + 1) := by
          ring
      _ = Nat.doubleFactorial (2 * (r + 1) - 1) * (2 * m) ^ (r + 1) := by
          congr 1
          cases r with
          | zero => norm_num [Nat.doubleFactorial]
          | succ r' =>
            have hh : 2 * (r' + 1 + 1) - 1 = (2 * (r' + 1) - 1) + 2 := by omega
            rw [hh, Nat.doubleFactorial_add_two]
            first
            | rfl
            | (congr 1 <;> omega)

/-- **THE DEPTH-GENERIC WICK CENSUS.**  `trivialCountG m r ≤ (2r−1)‼·(2m)^r` — the char-0
half of the depth-`r` energy is Wick-bounded, at every depth, unconditionally. -/
theorem trivialCountG_le_wick (m r : ℕ) (hm : 0 < m) :
    trivialCountG m r ≤ Nat.doubleFactorial (2 * r - 1) * (2 * m) ^ r := by
  rw [trivialCountG_eq_zeroSumCount m r, show r + r = 2 * r by ring]
  exact zeroSumCount_le_wick m r hm

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound], no sorryAx)
#print axioms exists_partner
#print axioms zeroSumCount_step
#print axioms zeroSumCount_le_wick
#print axioms trivialCountG_le_wick

end ArkLib.ProximityGap.Frontier.FS13PairingInductionWick

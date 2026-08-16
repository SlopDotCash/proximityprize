/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Ring

/-!
# LANE B2 (#466 round 306): THE CHAR-0 SHADOW FLOOR — the r305 classification, formalized

The r305 probe theory: for `n = 2m` and `g` with `g^m = −1` (so `g` plays the role of a
primitive `n`-th root, `Φ_n = x^m + 1`), every triple `(a,b,c) ∈ (Fin n)³` has an exact
integer shadow vector `tripleVec ∈ (Fin m → ℤ)` (signed basis), and the field-level 3-sum
`g^a + g^b + g^c` FACTORS through the shadow: it equals the evaluation of `tripleVec` at `g`.

Hence the depth-3 energy `E₃ = Σ_c rep₃(c)²` is the ℓ² norm of the PUSHFORWARD of the
char-0 histogram `N₃(v) = #{triples with shadow v}` along the evaluation map — and pushing
forward can only merge classes, so:

* **`shadow_energy_le_depth3_energy`** :  `Σ_v N₃(v)² ≤ Σ_{c : F} rep₃(c)²` — the
  **unconditional char-0 floor**: for EVERY field (every prime, every β), the depth-3 energy
  is at least the char-0 shadow energy.  (At `n = 2^k` the shadow energy is the #464 closed
  form `15n³ − 45n² + 40n`; here it is the exact `Finset` sum, `F`-independent by
  construction.)

The difference `E₃ − Σ N₃²` is exactly the r305 "excess" = collision mass of shadow vectors
under evaluation — zero iff evaluation is injective on the shadow support (no wraparound),
which the r305 census showed holds for `p` beyond the largest class-norm divisor.  This
brick is the Lean-side foundation for consuming the census: the floor is proven here; the
collision term is what the good-prime lane must exclude.  Issue #466, round 306, LANE B2.
Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor

/-- The signed-basis shadow of a single root index `a ∈ Fin n`, `n = 2m`:
`a < m ↦ +e_a`, `a ≥ m ↦ −e_{a−m}` (the relation `ζ^{a} = −ζ^{a−m}` under `Φ_n = x^m+1`). -/
def vecOf (n m : ℕ) (a : Fin n) : Fin m → ℤ :=
  fun j => (if (a : ℕ) = (j : ℕ) then 1 else 0) - (if (a : ℕ) = (j : ℕ) + m then 1 else 0)

/-- The exact char-0 shadow of a triple of root indices. -/
def tripleVec (n m : ℕ) (t : Fin n × Fin n × Fin n) : Fin m → ℤ :=
  fun j => vecOf n m t.1 j + vecOf n m t.2.1 j + vecOf n m t.2.2 j

variable {F : Type*} [Field F]

/-- Evaluation of a shadow vector at `g`: `v ↦ Σ_j v_j · g^j`. -/
def evalVec (g : F) (m : ℕ) (v : Fin m → ℤ) : F :=
  ∑ j : Fin m, (v j : ℤ) • g ^ (j : ℕ)

/-- The field-level 3-sum of a triple of root indices. -/
def gsum (g : F) (n : ℕ) (t : Fin n × Fin n × Fin n) : F :=
  g ^ (t.1 : ℕ) + g ^ (t.2.1 : ℕ) + g ^ (t.2.2 : ℕ)

/-- **Single-root factorization**: under `g^m = −1`, the evaluation of the signed-basis
shadow of `a` is exactly `g^a`. -/
theorem evalVec_vecOf (g : F) (n m : ℕ) (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1)
    (a : Fin n) :
    evalVec g m (vecOf n m a) = g ^ (a : ℕ) := by
  unfold evalVec vecOf
  by_cases ha : (a : ℕ) < m
  · -- only the `j = ⟨a, ha⟩` term survives, with coefficient `+1`
    have hside : ∀ b ∈ (Finset.univ : Finset (Fin m)), b ≠ (⟨(a : ℕ), ha⟩ : Fin m) →
        (((if (a : ℕ) = (b : ℕ) then (1:ℤ) else 0)
          - (if (a : ℕ) = (b : ℕ) + m then 1 else 0)) : ℤ) • g ^ (b : ℕ) = 0 := by
      intro b _ hb
      have hb1 : ¬ ((a : ℕ) = (b : ℕ)) := by
        intro h
        exact hb (Fin.ext (by simp [← h]))
      have hb2 : ¬ ((a : ℕ) = (b : ℕ) + m) := by omega
      rw [if_neg hb1, if_neg hb2]
      simp
    rw [Finset.sum_eq_single_of_mem (⟨(a : ℕ), ha⟩ : Fin m) (Finset.mem_univ _) hside]
    have h1 : ((a : ℕ) = ((⟨(a : ℕ), ha⟩ : Fin m) : ℕ)) := rfl
    have h2 : ¬ ((a : ℕ) = ((⟨(a : ℕ), ha⟩ : Fin m) : ℕ) + m) := by
      omega
    rw [if_pos h1, if_neg h2]
    simp
  · -- only the `j = ⟨a − m, _⟩` term survives, with coefficient `−1`
    have haa : (a : ℕ) < n := a.2
    have ham : (a : ℕ) - m < m := by omega
    have hside : ∀ b ∈ (Finset.univ : Finset (Fin m)), b ≠ (⟨(a : ℕ) - m, ham⟩ : Fin m) →
        (((if (a : ℕ) = (b : ℕ) then (1:ℤ) else 0)
          - (if (a : ℕ) = (b : ℕ) + m then 1 else 0)) : ℤ) • g ^ (b : ℕ) = 0 := by
      intro b _ hb
      have hb1 : ¬ ((a : ℕ) = (b : ℕ)) := by omega
      have hb2 : ¬ ((a : ℕ) = (b : ℕ) + m) := by
        intro h
        refine hb (Fin.ext ?_)
        simp only [Fin.val_mk]
        omega
      rw [if_neg hb1, if_neg hb2]
      simp
    rw [Finset.sum_eq_single_of_mem (⟨(a : ℕ) - m, ham⟩ : Fin m) (Finset.mem_univ _) hside]
    have h1 : ¬ ((a : ℕ) = ((⟨(a : ℕ) - m, ham⟩ : Fin m) : ℕ)) := by
      omega
    have h2 : ((a : ℕ) = ((⟨(a : ℕ) - m, ham⟩ : Fin m) : ℕ) + m) := by
      simp only [Fin.val_mk]
      omega
    rw [if_neg h1, if_pos h2]
    have hpow : g ^ (a : ℕ) = g ^ ((a : ℕ) - m) * g ^ m := by
      rw [← pow_add, Nat.sub_add_cancel (by omega : m ≤ (a : ℕ))]
    simp only [zero_sub, neg_smul, one_smul]
    rw [hpow, hg]
    ring

/-- **The factorization**: the field-level 3-sum equals the evaluation of the shadow. -/
theorem gsum_eq_evalVec_tripleVec (g : F) (n m : ℕ) (hm : 0 < m) (hn : n = 2 * m)
    (hg : g ^ m = -1) (t : Fin n × Fin n × Fin n) :
    gsum g n t = evalVec g m (tripleVec n m t) := by
  unfold gsum tripleVec evalVec
  have hsplit : ∀ j : Fin m,
      ((vecOf n m t.1 j + vecOf n m t.2.1 j + vecOf n m t.2.2 j) : ℤ) • g ^ (j : ℕ)
      = (vecOf n m t.1 j : ℤ) • g ^ (j : ℕ) + (vecOf n m t.2.1 j : ℤ) • g ^ (j : ℕ)
        + (vecOf n m t.2.2 j : ℤ) • g ^ (j : ℕ) := by
    intro j
    rw [add_zsmul, add_zsmul]
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  rw [show (∑ j : Fin m, (vecOf n m t.1 j : ℤ) • g ^ (j : ℕ)) = evalVec g m (vecOf n m t.1)
      from rfl,
    show (∑ j : Fin m, (vecOf n m t.2.1 j : ℤ) • g ^ (j : ℕ)) = evalVec g m (vecOf n m t.2.1)
      from rfl,
    show (∑ j : Fin m, (vecOf n m t.2.2 j : ℤ) • g ^ (j : ℕ)) = evalVec g m (vecOf n m t.2.2)
      from rfl,
    evalVec_vecOf g n m hm hn hg, evalVec_vecOf g n m hm hn hg,
    evalVec_vecOf g n m hm hn hg]

/-- The set of shadow keys (distinct char-0 3-sum vectors). -/
def keys (n m : ℕ) : Finset (Fin m → ℤ) :=
  (Finset.univ : Finset (Fin n × Fin n × Fin n)).image (tripleVec n m)

/-- The char-0 histogram `N₃(v)` = number of triples with shadow `v`. -/
def N3 (n m : ℕ) (v : Fin m → ℤ) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n × Fin n)).filter
    (fun t => tripleVec n m t = v)).card

section Floor

variable [Fintype F] [DecidableEq F]

/-- The field-level depth-3 representation count at `c`. -/
def rep3F (g : F) (n : ℕ) (c : F) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n × Fin n)).filter (fun t => gsum g n t = c)).card

/-- The field-level fiber decomposes as the sum of `N₃` over shadow keys evaluating to `c`. -/
theorem rep3F_eq_sum_N3 (g : F) (n m : ℕ) (hm : 0 < m) (hn : n = 2 * m)
    (hg : g ^ m = -1) (c : F) :
    rep3F g n c = ∑ v ∈ (keys n m).filter (fun v => evalVec g m v = c), N3 n m v := by
  classical
  unfold rep3F
  rw [Finset.card_eq_sum_card_fiberwise
    (f := tripleVec n m) (t := (keys n m).filter (fun v => evalVec g m v = c))
    (fun t ht => ?_)]
  · refine Finset.sum_congr rfl (fun v hv => ?_)
    rw [Finset.mem_filter] at hv
    unfold N3
    congr 1
    rw [Finset.filter_filter]
    refine Finset.filter_congr (fun t _ => ?_)
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      exact ⟨by rw [gsum_eq_evalVec_tripleVec g n m hm hn hg, h, hv.2], h⟩
  · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    simp only [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_image_of_mem _ (Finset.mem_univ t), ?_⟩
    rw [← gsum_eq_evalVec_tripleVec g n m hm hn hg, ht]

/-- Fiberwise `Σ f² ≤ (Σ f)²` for `ℕ`-valued `f` (merging can only grow ℓ²). -/
theorem sum_sq_le_sq_sum {m : ℕ} (s : Finset (Fin m → ℤ)) (f : (Fin m → ℤ) → ℕ) :
    ∑ v ∈ s, (f v) ^ 2 ≤ (∑ v ∈ s, f v) ^ 2 := by
  calc ∑ v ∈ s, (f v) ^ 2 = ∑ v ∈ s, f v * f v := by
        refine Finset.sum_congr rfl (fun v _ => sq (f v))
    _ ≤ ∑ v ∈ s, f v * (∑ w ∈ s, f w) := by
        refine Finset.sum_le_sum (fun v hv => ?_)
        exact Nat.mul_le_mul_left _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv)
    _ = (∑ v ∈ s, f v) * (∑ w ∈ s, f w) := by rw [← Finset.sum_mul]
    _ = (∑ v ∈ s, f v) ^ 2 := (sq _).symm

/-- **THE CHAR-0 SHADOW FLOOR** (r305 formalized): for every field `F` and every `g` with
`g^m = −1`, the depth-3 energy dominates the char-0 shadow energy —
`Σ_v N₃(v)² ≤ Σ_{c : F} rep₃(c)²`.  The left side is `F`-independent; the difference is
exactly the r305 collision mass ("excess"). -/
theorem shadow_energy_le_depth3_energy (g : F) (n m : ℕ) (hm : 0 < m) (hn : n = 2 * m)
    (hg : g ^ m = -1) :
    ∑ v ∈ keys n m, (N3 n m v) ^ 2 ≤ ∑ c : F, (rep3F g n c) ^ 2 := by
  classical
  -- partition the keys by their evaluation
  have hpart : ∑ v ∈ keys n m, (N3 n m v) ^ 2
      = ∑ c : F, ∑ v ∈ (keys n m).filter (fun v => evalVec g m v = c), (N3 n m v) ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun v => evalVec g m v)
      (f := fun v => (N3 n m v) ^ 2)
      (fun v _ => Finset.mem_univ (evalVec g m v))]
  rw [hpart]
  refine Finset.sum_le_sum (fun c _ => ?_)
  rw [rep3F_eq_sum_N3 g n m hm hn hg c]
  exact sum_sq_le_sq_sum _ _

end Floor

end ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor.evalVec_vecOf
#print axioms ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor.gsum_eq_evalVec_tripleVec
#print axioms ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor.rep3F_eq_sum_N3
#print axioms ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor.shadow_energy_le_depth3_energy

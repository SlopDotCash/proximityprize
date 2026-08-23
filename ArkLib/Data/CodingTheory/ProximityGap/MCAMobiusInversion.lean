/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS
import ArkLib.Data.CodingTheory.ProximityGap.MCAEquivariance

/-!
# Möbius-inversion equivariance of the MCA event (#371, the σ-descent foundation)

The window adversary is Möbius-symmetric (probe record at two scales).  This file
proves the symmetry is structural: the MCA problem on an inversion-stable domain is
equivariant under `x ↦ −1/x` — via the **twisted** permutation action

  `(T u)(i) = (dom i)^{k−1} · u(σ i)`,

where `σ` is the index permutation realizing the inversion.  Plain precomposition
does NOT preserve the RS code (`P(−1/x)` is rational); the weight `x^{k−1}` repairs
it: `x^{k−1}·P(−1/x)` is the reversal-twist polynomial of degree `< k`.

* `mcaEvent_twisted_perm_mp` — the general engine: any weighted permutation with
  nonvanishing weights and code closure transports the MCA event (extends the
  in-tree untwisted engine `mcaEvent_comp_perm_iff`);
* `reversalTwist` / `reversalTwist_eval` — the polynomial closure;
* `rsCode_twist_mem` / `rsCode_twist_inv_mem` — RS closure both ways;
* `mcaEvent_rs_inversion` — the headline: the second PGL₂ generator.  Together with
  the in-tree rotation equivariance (`mcaEvent_rs_rotate`) this completes the
  Möbius symmetry of smooth-domain MCA — the formal ground for the σ-descent on
  the window residual `WindowRationalBounded`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.MCAMobius

open ProximityGap.SpikeFloor ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The twisted permutation engine -/

/-- The weighted-permutation action on words. -/
def twist (σ : Equiv.Perm ι) (m : ι → F) (u : ι → F) : ι → F :=
  fun i => m i * u (σ i)

/-- **The twisted-permutation engine**: a weighted permutation with nonvanishing
weights and code closure transports the MCA event at every scalar. -/
theorem mcaEvent_twisted_perm_mp (C : Submodule F (ι → F)) {δ : ℝ≥0}
    {u₀ u₁ : ι → F} {γ : F} (σ : Equiv.Perm ι) (m : ι → F) (hm : ∀ i, m i ≠ 0)
    (hT : ∀ w ∈ C, twist σ m w ∈ C)
    (hT' : ∀ w ∈ C, (fun j => (m (σ.symm j))⁻¹ * w (σ.symm j)) ∈ C) :
    mcaEvent (F := F) (C : Set (ι → F)) δ (twist σ m u₀) (twist σ m u₁) γ →
      mcaEvent (F := F) (C : Set (ι → F)) δ u₀ u₁ γ := by
  rintro ⟨S, hcard, ⟨w, hw, hag⟩, hno⟩
  refine ⟨S.image ⇑σ, ?_, ⟨fun j => (m (σ.symm j))⁻¹ * w (σ.symm j), hT' w hw, ?_⟩, ?_⟩
  · rw [Finset.card_image_of_injective S σ.injective]
    exact hcard
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have h : w i = twist σ m u₀ i + γ • twist σ m u₁ i := hag i hi
    simp only [twist, smul_eq_mul] at h
    have hmi := hm i
    show (m (σ.symm (σ i)))⁻¹ * w (σ.symm (σ i)) = u₀ (σ i) + γ • u₁ (σ i)
    rw [Equiv.symm_apply_apply, h, smul_eq_mul]
    field_simp
  · intro hpair
    apply hno
    obtain ⟨v₀, hv₀, v₁, hv₁, hagp⟩ := hpair
    refine ⟨twist σ m v₀, hT v₀ hv₀, twist σ m v₁, hT v₁ hv₁, fun i hi => ?_⟩
    have h := hagp (σ i) (Finset.mem_image_of_mem ⇑σ hi)
    exact ⟨by simp only [twist]; rw [h.1], by simp only [twist]; rw [h.2]⟩

/-! ## The reversal twist polynomial -/

/-- The reversal twist `P* = Σ_j (−1)^j p_j X^{k−1−j}` — the polynomial computing
`x^{k−1}·P(−1/x)`. -/
noncomputable def reversalTwist (k : ℕ) (P : F[X]) : F[X] :=
  ∑ j ∈ Finset.range k, C ((-1) ^ j * P.coeff j) * X ^ (k - 1 - j)

theorem reversalTwist_degree_lt (k : ℕ) (hk : 1 ≤ k) (P : F[X]) :
    (reversalTwist k P).degree < k := by
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe k)]
  intro j hj
  refine lt_of_le_of_lt (degree_mul_le _ _) ?_
  calc (C ((-1) ^ j * P.coeff j)).degree + (X ^ (k - 1 - j) : F[X]).degree
      ≤ 0 + ((k - 1 - j : ℕ) : WithBot ℕ) := add_le_add degree_C_le
        (by rw [degree_X_pow])
    _ < (k : WithBot ℕ) := by
        rw [zero_add]
        exact_mod_cast (by omega : k - 1 - j < k)

/-- The evaluation identity: `P*(x) = x^{k−1}·P(−x⁻¹)` for `x ≠ 0`, `deg P < k`. -/
theorem reversalTwist_eval (k : ℕ) (P : F[X]) (hP : P.degree < k)
    {x : F} (hx : x ≠ 0) :
    (reversalTwist k P).eval x = x ^ (k - 1) * P.eval (-x⁻¹) := by
  by_cases hP0 : P = 0
  · subst hP0
    simp [reversalTwist]
  have hPdeg : P.natDegree < k := (natDegree_lt_iff_degree_lt hP0).mpr hP
  rw [reversalTwist, eval_finset_sum, eval_eq_sum_range' hPdeg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k - 1 := by
    have := Finset.mem_range.mp hj
    omega
  rw [eval_mul, eval_C, eval_pow, eval_X]
  have hpowj : x ^ (k - 1 - j) = x ^ (k - 1) * (x⁻¹) ^ j := by
    have h3 : x ^ (k - 1 - j) * x ^ j = x ^ (k - 1) * (x⁻¹) ^ j * x ^ j := by
      rw [← pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hx, one_pow, mul_one]
      congr 1
      omega
    exact mul_right_cancel₀ (pow_ne_zero j hx) h3
  rw [hpowj, show (-x⁻¹ : F) = (-1) * x⁻¹ by ring, mul_pow]
  ring

/-! ## RS closure under the inversion twist -/

variable {n : ℕ} [NeZero n]

/-- Forward closure: the twist of a codeword is a codeword (the reversal twist). -/
theorem rsCode_twist_mem (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    (σ : Equiv.Perm (Fin n)) (hdom0 : ∀ i, dom i ≠ 0)
    (hσ : ∀ i, dom (σ i) = -(dom i)⁻¹)
    {u : Fin n → F} (hu : u ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    twist σ (fun i => (dom i) ^ (k - 1)) u
      ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
  obtain ⟨P, hPdeg, rfl⟩ := hu
  refine ⟨reversalTwist k P, reversalTwist_degree_lt k hk P, ?_⟩
  funext i
  show twist σ (fun i => (dom i) ^ (k - 1)) (fun i => P.eval (dom i)) i
    = (reversalTwist k P).eval (dom i)
  rw [twist]
  show (dom i) ^ (k-1) * P.eval (dom (σ i)) = (reversalTwist k P).eval (dom i)
  rw [reversalTwist_eval k P hPdeg (hdom0 i), hσ i]

/-- Backward closure: the inverse twist of a codeword is a codeword (a scalar
multiple of the reversal twist). -/
theorem rsCode_twist_inv_mem (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    (σ : Equiv.Perm (Fin n)) (hdom0 : ∀ i, dom i ≠ 0)
    (hσ : ∀ i, dom (σ i) = -(dom i)⁻¹)
    {u : Fin n → F} (hu : u ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    (fun j => ((fun i => (dom i) ^ (k - 1)) (σ.symm j))⁻¹ * u (σ.symm j))
      ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
  obtain ⟨P, hPdeg, rfl⟩ := hu
  -- dom (σ.symm j) = −(dom j)⁻¹  (the involution algebra)
  have hσsymm : ∀ j, dom (σ.symm j) = -(dom j)⁻¹ := by
    intro j
    have h := hσ (σ.symm j)
    rw [Equiv.apply_symm_apply] at h
    have hd := hdom0 (σ.symm j)
    -- h : dom j = −(dom (σ.symm j))⁻¹; solve for dom (σ.symm j)
    rw [h, inv_neg, inv_inv, neg_neg]
  refine ⟨((-1 : F) ^ (k - 1)) • reversalTwist k P,
    lt_of_le_of_lt (degree_smul_le _ _) (reversalTwist_degree_lt k hk P), ?_⟩
  funext j
  have hdj := hdom0 j
  have hdsj := hdom0 (σ.symm j)
  show (((dom (σ.symm j)) ^ (k - 1))⁻¹ * P.eval (dom (σ.symm j)))
    = (((-1 : F) ^ (k - 1)) • reversalTwist k P).eval (dom j)
  rw [eval_smul, smul_eq_mul, reversalTwist_eval k P hPdeg hdj, hσsymm j]
  have hinv : (((-(dom j)⁻¹ : F)) ^ (k - 1))⁻¹
      = ((-1 : F) ^ (k - 1)) * (dom j) ^ (k - 1) := by
    rw [show (-(dom j)⁻¹ : F) = (-1) * (dom j)⁻¹ by ring, mul_pow, mul_inv]
    congr 1
    · rw [← inv_pow, inv_neg, inv_one]
    · rw [← inv_pow, inv_inv]
  rw [hinv]
  ring

/-! ## The headline -/

open Classical in
/-- **Möbius-inversion equivariance of smooth-domain MCA** — the second PGL₂
generator: on an inversion-stable domain avoiding `0`, the twisted action
`(T u)(i) = (dom i)^{k−1}·u(σ i)` preserves the MCA event at every scalar. -/
theorem mcaEvent_rs_inversion (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    (σ : Equiv.Perm (Fin n)) (hdom0 : ∀ i, dom i ≠ 0)
    (hσ : ∀ i, dom (σ i) = -(dom i)⁻¹) (δ : ℝ≥0) (γ : F) (u₀ u₁ : Fin n → F) :
    mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (twist σ (fun i => (dom i) ^ (k - 1)) u₀)
        (twist σ (fun i => (dom i) ^ (k - 1)) u₁) γ →
      mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ :=
  mcaEvent_twisted_perm_mp (rsCode dom k) σ _
    (fun i => pow_ne_zero _ (hdom0 i))
    (fun w hw => rsCode_twist_mem dom hk σ hdom0 hσ hw)
    (fun w hw => rsCode_twist_inv_mem dom hk σ hdom0 hσ hw)

/-! ## The involution identity and the equivalence -/

/-- The index permutation realizing the inversion is an involution. -/
theorem sigma_sq (dom : Fin n ↪ F) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, dom (σ i) = -(dom i)⁻¹) (hdom0 : ∀ i, dom i ≠ 0) (i : Fin n) :
    σ (σ i) = i := by
  have h1 := hσ (σ i)
  rw [hσ i, inv_neg, inv_inv, neg_neg] at h1
  exact dom.injective h1

/-- **The twist is an involution up to the sign `(−1)^{k−1}`**: `T² = (−1)^{k−1}·id`.
For odd `k` it is a genuine involution and the stack space splits into
`T`-eigencomponents — the formal frame for the σ-average analysis of the window. -/
theorem twist_twist (dom : Fin n ↪ F) (k : ℕ) (σ : Equiv.Perm (Fin n))
    (hdom0 : ∀ i, dom i ≠ 0) (hσ : ∀ i, dom (σ i) = -(dom i)⁻¹) (u : Fin n → F) :
    twist σ (fun i => (dom i) ^ (k - 1)) (twist σ (fun i => (dom i) ^ (k - 1)) u)
      = ((-1 : F) ^ (k - 1)) • u := by
  funext i
  show (dom i) ^ (k - 1) * ((dom (σ i)) ^ (k - 1) * u (σ (σ i))) = _
  rw [sigma_sq dom σ hσ hdom0 i, hσ i]
  rw [show (-(dom i)⁻¹ : F) = (-1) * (dom i)⁻¹ by ring, mul_pow]
  have hd := hdom0 i
  rw [Pi.smul_apply, smul_eq_mul, inv_pow]
  have hcancel : (dom i) ^ (k - 1) * (((dom i) ^ (k - 1))⁻¹) = 1 :=
    mul_inv_cancel₀ (pow_ne_zero _ hd)
  calc (dom i) ^ (k-1) * ((-1 : F) ^ (k-1) * ((dom i) ^ (k-1))⁻¹ * u i)
      = ((-1 : F) ^ (k-1)) * ((dom i) ^ (k-1) * ((dom i) ^ (k-1))⁻¹) * u i := by ring
    _ = ((-1 : F) ^ (k-1)) * u i := by rw [hcancel, mul_one]

open Classical in
/-- **The equivalence form** of the inversion equivariance: the twisted action
preserves the MCA event in BOTH directions (via `T² = (−1)^{k−1}·id` and
whole-stack scaling invariance). -/
theorem mcaEvent_rs_inversion_iff (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    (σ : Equiv.Perm (Fin n)) (hdom0 : ∀ i, dom i ≠ 0)
    (hσ : ∀ i, dom (σ i) = -(dom i)⁻¹) (δ : ℝ≥0) (γ : F) (u₀ u₁ : Fin n → F) :
    mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (twist σ (fun i => (dom i) ^ (k - 1)) u₀)
        (twist σ (fun i => (dom i) ^ (k - 1)) u₁) γ ↔
      mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ := by
  constructor
  · exact mcaEvent_rs_inversion dom hk σ hdom0 hσ δ γ u₀ u₁
  · intro h
    -- apply the forward direction to the twisted stack: T²u = (−1)^{k−1}•u
    refine mcaEvent_rs_inversion dom hk σ hdom0 hσ δ γ
      (twist σ _ u₀) (twist σ _ u₁) ?_
    rw [twist_twist dom k σ hdom0 hσ, twist_twist dom k σ hdom0 hσ]
    have hsign : ((-1 : F) ^ (k - 1)) ≠ 0 :=
      pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    exact (ProximityGap.MCAEquivariance.mcaEvent_smul_both (rsCode dom k) hsign γ).mpr h

/-! ## The eigendecomposition (odd k, char ≠ 2) -/

/-- The T-eigencomponents of a word: `u± = (u ± Tu)/2`. -/
noncomputable def eigenPlus (dom : Fin n ↪ F) (k : ℕ) (σ : Equiv.Perm (Fin n))
    (u : Fin n → F) : Fin n → F :=
  (2 : F)⁻¹ • (u + twist σ (fun i => (dom i) ^ (k - 1)) u)

noncomputable def eigenMinus (dom : Fin n ↪ F) (k : ℕ) (σ : Equiv.Perm (Fin n))
    (u : Fin n → F) : Fin n → F :=
  (2 : F)⁻¹ • (u - twist σ (fun i => (dom i) ^ (k - 1)) u)

/-- The decomposition: `u = u⁺ + u⁻`. -/
theorem eigen_add (dom : Fin n ↪ F) (k : ℕ) (σ : Equiv.Perm (Fin n))
    (h2 : (2 : F) ≠ 0) (u : Fin n → F) :
    eigenPlus dom k σ u + eigenMinus dom k σ u = u := by
  funext i
  simp only [eigenPlus, eigenMinus, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul]
  field_simp
  ring

/-- Twist is additive. -/
theorem twist_add (σ : Equiv.Perm (Fin n)) (m : Fin n → F) (u v : Fin n → F) :
    twist σ m (u + v) = twist σ m u + twist σ m v := by
  funext i
  simp only [twist, Pi.add_apply]
  ring

/-- Twist commutes with scalar multiplication. -/
theorem twist_smul (σ : Equiv.Perm (Fin n)) (m : Fin n → F) (c : F) (u : Fin n → F) :
    twist σ m (c • u) = c • twist σ m u := by
  funext i
  simp only [twist, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The eigenproperty** (odd `k`): `T u⁺ = u⁺`. -/
theorem twist_eigenPlus (dom : Fin n ↪ F) {k : ℕ} (hkodd : (k - 1) % 2 = 0)
    (σ : Equiv.Perm (Fin n)) (hdom0 : ∀ i, dom i ≠ 0)
    (hσ : ∀ i, dom (σ i) = -(dom i)⁻¹) (u : Fin n → F) :
    twist σ (fun i => (dom i) ^ (k - 1)) (eigenPlus dom k σ u)
      = eigenPlus dom k σ u := by
  have hsign : ((-1 : F) ^ (k - 1)) = 1 :=
    Even.neg_one_pow (Nat.even_iff.mpr hkodd)
  rw [eigenPlus, twist_smul, twist_add, twist_twist dom k σ hdom0 hσ, hsign, one_smul,
    add_comm]

/-- **The eigenproperty** (odd `k`): `T u⁻ = −u⁻`. -/
theorem twist_eigenMinus (dom : Fin n ↪ F) {k : ℕ} (hkodd : (k - 1) % 2 = 0)
    (σ : Equiv.Perm (Fin n)) (hdom0 : ∀ i, dom i ≠ 0)
    (hσ : ∀ i, dom (σ i) = -(dom i)⁻¹) (u : Fin n → F) :
    twist σ (fun i => (dom i) ^ (k - 1)) (eigenMinus dom k σ u)
      = -(eigenMinus dom k σ u) := by
  have hsign : ((-1 : F) ^ (k - 1)) = 1 :=
    Even.neg_one_pow (Nat.even_iff.mpr hkodd)
  have hsub : ∀ u v : Fin n → F, twist σ (fun i => (dom i) ^ (k - 1)) (u - v)
      = twist σ (fun i => (dom i) ^ (k - 1)) u
        - twist σ (fun i => (dom i) ^ (k - 1)) v := by
    intro u v
    funext i
    simp only [twist, Pi.sub_apply]
    ring
  rw [eigenMinus, twist_smul, hsub, twist_twist dom k σ hdom0 hσ, hsign, one_smul]
  funext i
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-! ## The polynomial-level involution (the palindrome subcode foundation) -/

/-- **The reversal twist is an involution up to the sign**:
`(P*)* = (−1)^{k−1}·P` for `deg P < k` — purely by coefficient comparison. -/
theorem reversalTwist_reversalTwist (k : ℕ) (hk : 1 ≤ k) (P : F[X])
    (hP : P.degree < k) :
    reversalTwist k (reversalTwist k P) = ((-1 : F) ^ (k - 1)) • P := by
  have hcoeff : ∀ (Q : F[X]) (j : ℕ), j < k → (reversalTwist k Q).coeff j
      = (-1) ^ (k - 1 - j) * Q.coeff (k - 1 - j) := by
    intro Q j hj
    rw [reversalTwist, finset_sum_coeff]
    rw [Finset.sum_eq_single (k - 1 - j)]
    · rw [coeff_C_mul, coeff_X_pow, if_pos (by omega), mul_one]
    · intro b hb hbne
      have hbk := Finset.mem_range.mp hb
      rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  ext j
  by_cases hj : j < k
  · rw [hcoeff _ j hj, hcoeff P (k - 1 - j) (by omega)]
    have hjj : k - 1 - (k - 1 - j) = j := by omega
    rw [hjj, coeff_smul, smul_eq_mul, ← mul_assoc, ← pow_add]
    congr 2
    omega
  · have h1 : (reversalTwist k (reversalTwist k P)).coeff j = 0 := by
      refine coeff_eq_zero_of_degree_lt (lt_of_lt_of_le
        (reversalTwist_degree_lt k hk _) ?_)
      exact_mod_cast (by omega : k ≤ j)
    have h2 : P.coeff j = 0 := by
      refine coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hP ?_)
      exact_mod_cast (by omega : k ≤ j)
    rw [h1, coeff_smul, h2, smul_zero]

/-! ## T-fixed codewords ⟺ palindromes (the quotient-census bridge) -/

/-- The twist of an evaluation word is the evaluation of the reversal twist. -/
theorem twist_eval_eq (dom : Fin n ↪ F) {k : ℕ} (σ : Equiv.Perm (Fin n))
    (hdom0 : ∀ i, dom i ≠ 0) (hσ : ∀ i, dom (σ i) = -(dom i)⁻¹)
    {P : F[X]} (hPdeg : P.degree < k) :
    twist σ (fun i => (dom i) ^ (k - 1)) (fun i => P.eval (dom i))
      = fun i => (reversalTwist k P).eval (dom i) := by
  funext i
  show (dom i) ^ (k - 1) * P.eval (dom (σ i)) = (reversalTwist k P).eval (dom i)
  rw [reversalTwist_eval k P hPdeg (hdom0 i), hσ i]

/-- **T-fixed codewords are exactly the palindrome evaluations** (`k ≤ n`):
the quotient-census object of the invariant window pairs. -/
theorem twist_fixed_iff_palindrome (dom : Fin n ↪ F) {k : ℕ} (hkn : k ≤ n)
    (σ : Equiv.Perm (Fin n)) (hdom0 : ∀ i, dom i ≠ 0)
    (hσ : ∀ i, dom (σ i) = -(dom i)⁻¹)
    {P : F[X]} (hPdeg : P.degree < k) :
    twist σ (fun i => (dom i) ^ (k - 1)) (fun i => P.eval (dom i))
        = (fun i => P.eval (dom i))
      ↔ reversalTwist k P = P := by
  rw [twist_eval_eq dom σ hdom0 hσ hPdeg]
  constructor
  · intro h
    -- two degree-< k polynomials agreeing on n ≥ k distinct points are equal
    have hdiff : reversalTwist k P - P = 0 := by
      by_cases hk1 : 1 ≤ k
      · refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
          (f := reversalTwist k P - P)
          (s := (Finset.univ : Finset (Fin n)).image dom) ?_ ?_
        · have hcard : ((Finset.univ : Finset (Fin n)).image dom).card = n := by
            rw [Finset.card_image_of_injective _ dom.injective, Finset.card_univ,
              Fintype.card_fin]
          rw [hcard]
          calc (reversalTwist k P - P).degree
              ≤ max (reversalTwist k P).degree P.degree := degree_sub_le _ _
            _ < k := max_lt (reversalTwist_degree_lt k hk1 P) hPdeg
            _ ≤ (n : WithBot ℕ) := by exact_mod_cast hkn
        · intro x hx
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
          rw [eval_sub, sub_eq_zero]
          exact congrFun h i
      · -- k = 0: both sides are 0
        push Not at hk1
        interval_cases k
        have hP0 : P = 0 := by
          rw [← Polynomial.degree_eq_bot]
          have h0 : P.degree < (0 : ℕ) := hPdeg
          exact Nat.WithBot.lt_zero_iff.mp (by exact_mod_cast h0)
        rw [hP0, reversalTwist]
        simp
    have := sub_eq_zero.mp hdiff
    exact this
  · intro h
    rw [h]

end ProximityGap.MCAMobius

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.MCAMobius.mcaEvent_twisted_perm_mp
#print axioms ProximityGap.MCAMobius.reversalTwist_eval
#print axioms ProximityGap.MCAMobius.rsCode_twist_mem
#print axioms ProximityGap.MCAMobius.rsCode_twist_inv_mem
#print axioms ProximityGap.MCAMobius.mcaEvent_rs_inversion
#print axioms ProximityGap.MCAMobius.twist_twist
#print axioms ProximityGap.MCAMobius.mcaEvent_rs_inversion_iff
#print axioms ProximityGap.MCAMobius.eigen_add
#print axioms ProximityGap.MCAMobius.twist_eigenPlus
#print axioms ProximityGap.MCAMobius.twist_eigenMinus
#print axioms ProximityGap.MCAMobius.reversalTwist_reversalTwist
#print axioms ProximityGap.MCAMobius.twist_fixed_iff_palindrome

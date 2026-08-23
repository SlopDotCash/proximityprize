/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.ToyProblem.Metrics

/-!
# Issue #339 — `fenziSanso_upperBound_attack_concrete_residual` is TRUE:
the full-field winning set via the constraint degeneracy

This module **proves** the leaderboard's concrete attack residual by exhibiting a violating
instance over the genuine KoalaBear-sextic `[4,2]` Reed–Solomon code whose winning set is
**all of `F = F_{p^6}`** (`ncard = p^6 ≈ 2^186 ≥ 2^70`).

**The mechanism (honest disclosure).**  This is NOT the paper's list-decoding attack
(Fenzi–Sanso eprint 2025/2197 Lemma 4.4 — large lists do not exist at `δ = 3/10` for this
length-4 carrier).  It is a *constraint-degeneracy* exploit available in the in-tree
`relaxedRelation` model (Definition 6.3), whose encoding is existential with only
`∀ m, encode m ∈ C`:

* the instance: `f₁ = c₁ + bump`, `f₂ = c₂ + bump` at the last coordinate, with `c₁, c₂` the
  constant-`1` and identity codewords, `v = (1, 0) ≠ 0`, `μ₁ = μ₂ = 0`;
* **every `γ` wins**: the fold agrees with the codeword `c₁ + γ·c₂` on `{0,1,2}` (3 of 4
  coordinates, `(1 − 3/10)·4 = 2.8 ≤ 3`), realised by the rank-one encode
  `m ↦ m 1 • (c₁ + γ·c₂)` with message `(0,1)`, whose constraint
  `⟨(0,1), v⟩ = 0 = μ₁ + γ·μ₂` holds;
* **the instance violates the 2-row relation**: a common agreement set of size ≥ 3 contains
  two unbumped coordinates, forcing the close pair to `(c₁, c₂)` by affine interpolation;
  the zero constraints force `M i 0 = 0`, hence `c₁ = t₀ • E(0,1)` and `c₂ = t₁ • E(0,1)`
  are proportional — contradicting `c₁ 0 = 1, c₂ 0 = 0, c₂ 1 = 1`.

Via `fenziSanso_upperBound_attack_residual_of_concrete`, this discharges TWO of the three
#339 residuals.  The model-level finding is the honest content: the in-tree relaxed relation
is strictly more permissive than the paper's fixed-encoding `R_C` (single-row constraint
values are free at any nonzero close codeword under rank-one re-encoding, while zero
constraints on an independent close pair are unsatisfiable under any common encode), and the
leaderboard's 116-bit attack anchor is validated by that permissiveness — not by
list-decoding.
-/

namespace ArkLib

namespace KoalaBearAttack

open KoalaBear ToyProblem

/-- The constant-`1` codeword: message `(1, 0)`. -/
noncomputable def c₁ : Fin 4 → Sextic := rsEncoder ![1, 0]

/-- The identity codeword `j ↦ j`: message `(0, 1)`. -/
noncomputable def c₂ : Fin 4 → Sextic := rsEncoder ![0, 1]

@[simp] theorem c₁_apply (j : Fin 4) : c₁ j = 1 := by
  simp [c₁, rsEncoder, rsPoint]

@[simp] theorem c₂_apply (j : Fin 4) : c₂ j = (j.val : Sextic) := by
  simp [c₂, rsEncoder, rsPoint]

/-- The first attack word: `c₁` bumped by `1` at the last coordinate. -/
noncomputable def f₁ : Fin 4 → Sextic := fun j => c₁ j + if j = 3 then 1 else 0

/-- The second attack word: `c₂` bumped by `1` at the last coordinate. -/
noncomputable def f₂ : Fin 4 → Sextic := fun j => c₂ j + if j = 3 then 1 else 0

theorem f₁_apply_ne {j : Fin 4} (hj : j ≠ 3) : f₁ j = c₁ j := by simp [f₁, hj]

theorem f₂_apply_ne {j : Fin 4} (hj : j ≠ 3) : f₂ j = c₂ j := by simp [f₂, hj]

/-- The constraint vector `v = (1, 0)`. -/
noncomputable def v : Fin 2 → Sextic := ![1, 0]

/-! ## Small-point arithmetic: the evaluation points `0,1,2,3` are distinct in `Sextic` -/

/-- Distinct `Fin 4` points give distinct field points (characteristic `p > 4`). -/
theorem rsPoint_injective : Function.Injective rsPoint := by
  have hp : Fact (Nat.Prime fieldSize) := inferInstance
  intro a b hab
  have hchar : CharP Sextic fieldSize := inferInstance
  by_contra hne
  have hne' : a.val ≠ b.val := fun h => hne (Fin.ext h)
  -- WLOG via the two symmetric cases
  rcases Nat.lt_or_ge a.val b.val with hlt | hge
  · have hcast : ((b.val - a.val : ℕ) : Sextic) = 0 := by
      have hba : (a.val : Sextic) = (b.val : Sextic) := hab
      push_cast [Nat.cast_sub hlt.le]
      linear_combination -hba
    have hdvd := (CharP.cast_eq_zero_iff Sextic fieldSize _).mp hcast
    have hlt4 : b.val - a.val < fieldSize := by
      have := b.isLt
      have : b.val - a.val < 4 := by omega
      have h4 : 4 < fieldSize := by rw [fieldSize_eq]; norm_num
      omega
    have hpos : 0 < b.val - a.val := Nat.sub_pos_of_lt hlt
    exact absurd hdvd (Nat.not_dvd_of_pos_of_lt hpos hlt4)
  · have hlt : b.val < a.val := lt_of_le_of_ne hge (fun h => hne' h.symm)
    have hcast : ((a.val - b.val : ℕ) : Sextic) = 0 := by
      have hba : (a.val : Sextic) = (b.val : Sextic) := hab
      push_cast [Nat.cast_sub hlt.le]
      linear_combination hba
    have hdvd := (CharP.cast_eq_zero_iff Sextic fieldSize _).mp hcast
    have hlt4 : a.val - b.val < fieldSize := by
      have : a.val - b.val < 4 := by omega
      have h4 : 4 < fieldSize := by rw [fieldSize_eq]; norm_num
      omega
    have hpos : 0 < a.val - b.val := Nat.sub_pos_of_lt hlt
    exact absurd hdvd (Nat.not_dvd_of_pos_of_lt hpos hlt4)

/-- **Affine interpolation**: two codewords agreeing at two distinct points have equal
messages. -/
theorem message_eq_of_agree_two {m m' : Fin 2 → Sextic}
    {j₁ j₂ : Fin 4} (hj : j₁ ≠ j₂)
    (h₁ : rsEncoder m j₁ = rsEncoder m' j₁) (h₂ : rsEncoder m j₂ = rsEncoder m' j₂) :
    m = m' := by
  simp only [rsEncoder, LinearMap.coe_mk, AddHom.coe_mk] at h₁ h₂
  have hx : rsPoint j₁ - rsPoint j₂ ≠ 0 :=
    sub_ne_zero.mpr (fun h => hj (rsPoint_injective h))
  have hm1 : m 1 = m' 1 := by
    have hkey : (m 1 - m' 1) * (rsPoint j₁ - rsPoint j₂) = 0 := by
      linear_combination h₁ - h₂
    rcases mul_eq_zero.mp hkey with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hx
  have hm0 : m 0 = m' 0 := by linear_combination h₁ - (rsPoint j₁) * hm1
  funext i
  fin_cases i <;> assumption

/-! ## Every challenge wins -/

/-- The fold-target codeword at challenge `γ`: message `(1, γ)`. -/
noncomputable def wγ (γ : Sextic) : Fin 4 → Sextic := rsEncoder ![1, γ]

theorem wγ_apply (γ : Sextic) (j : Fin 4) : wγ γ j = c₁ j + γ * c₂ j := by
  simp [wγ, rsEncoder, c₁_apply, c₂_apply, rsPoint, mul_comm]

/-- The rank-one encode realising `wγ γ` with a zero-constraint message: `m ↦ m 1 • wγ γ`. -/
noncomputable def rankOneEncode (γ : Sextic) : (Fin 2 → Sextic) →ₗ[Sextic] (Fin 4 → Sextic) where
  toFun := fun m => m 1 • wγ γ
  map_add' := by intro m m'; simp [add_smul, Pi.add_apply]
  map_smul' := by intro c m; simp [smul_smul, Pi.smul_apply, smul_eq_mul]

/-- The rank-one encode lands in the code (the code is a subspace: scalar multiples of the
codeword `wγ γ` are encodings of the scaled message). -/
theorem rankOneEncode_mem (γ : Sextic) (m : Fin 2 → Sextic) :
    rankOneEncode γ m ∈ KoalaBear.rsCodeSet := by
  refine ⟨m 1 • ![1, γ], ?_⟩
  rw [map_smul]
  rfl

/-- **Every challenge wins.**  For every `γ`, the folded instance
`(v, 0 + γ·0, f₁ + γ·f₂)` is in the relaxed 1-row relation: the fold agrees with `wγ γ` on
`{0,1,2}` and the rank-one encode supplies the message `(0,1)` with constraint `0`. -/
theorem all_challenges_win (γ : Sextic) :
    γ ∈ winningSet KoalaBear.rsCodeSet (3 / 10) v 0 0 f₁ f₂ := by
  refine ⟨fun _ => wγ γ, ⟨fun _ => ![0, 1], ⟨rankOneEncode γ, rankOneEncode_mem γ, ?_⟩, ?_⟩,
    ({0, 1, 2} : Finset (Fin 4)), ?_, ?_⟩
  · -- the codeword is realised by the rank-one encode at message (0,1)
    intro i
    show wγ γ = rankOneEncode γ ![0, 1]
    show wγ γ = (![0, 1] : Fin 2 → Sextic) 1 • wγ γ
    norm_num
  · -- the constraint: ⟨(0,1), (1,0)⟩ = 0 = 0 + γ·0
    intro i
    show (0 : Sextic) * v 0 + (1 * v 1 + 0) = 0 + γ * 0
    simp [v]
  · -- |S| = 3 ≥ (1 − 3/10)·4 = 2.8
    have hcard : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by decide
    rw [hcard]
    push_cast
    norm_num
  · -- agreement off the bumped coordinate
    intro i j hj
    have hj3 : j ≠ 3 := by
      fin_cases j <;> simp_all <;> decide
    show f₁ j + γ * f₂ j = wγ γ j
    rw [f₁_apply_ne hj3, f₂_apply_ne hj3, wγ_apply]

/-! ## The instance violates the 2-row relation -/

/-- **The violation.**  No common encode can witness the 2-row relaxed relation at
`μ = (0,0)`: the common agreement set forces the close pair to `(c₁, c₂)`, and the zero
constraints force both messages into the second coordinate axis, making `c₁, c₂`
proportional — contradiction. -/
theorem instance_violates :
    ¬ relaxedRelation (ℓ := 2) KoalaBear.rsCodeSet (3 / 10) v ![0, 0] ![f₁, f₂] := by
  rintro ⟨Wstar, ⟨M, ⟨E, hEmem, hWeq⟩, hconstr⟩, S, hScard, hagree⟩
  -- |S| ≥ 3
  have hS3 : 3 ≤ S.card := by
    by_contra h
    push_neg at h
    interval_cases hc : S.card <;> simp_all <;> nlinarith [hScard]
  -- two distinct unbumped points in S
  have herase : 2 ≤ (S.erase 3).card := by
    have := Finset.pred_card_le_card_erase (s := S) (a := 3)
    omega
  obtain ⟨j₁, hj₁, j₂, hj₂, hjne⟩ := Finset.one_lt_card.mp (by omega : 1 < (S.erase 3).card)
  have hj₁S : j₁ ∈ S := Finset.mem_of_mem_erase hj₁
  have hj₂S : j₂ ∈ S := Finset.mem_of_mem_erase hj₂
  have hj₁3 : j₁ ≠ 3 := Finset.ne_of_mem_erase hj₁
  have hj₂3 : j₂ ≠ 3 := Finset.ne_of_mem_erase hj₂
  -- the rows' close codewords have messages, and are pinned to c₁, c₂
  obtain ⟨m₀, hm₀⟩ := hEmem (M 0)
  obtain ⟨m₁, hm₁⟩ := hEmem (M 1)
  have hW0 : Wstar 0 = rsEncoder m₀ := by rw [hWeq 0, ← hm₀]
  have hW1 : Wstar 1 = rsEncoder m₁ := by rw [hWeq 1, ← hm₁]
  -- agreement transported to the unbumped coordinates
  have hag : ∀ j ∈ S, j ≠ 3 →
      rsEncoder m₀ j = c₁ j ∧ rsEncoder m₁ j = c₂ j := by
    intro j hjS hj3
    constructor
    · have := hagree 0 j hjS
      simp only [Matrix.cons_val_zero] at this
      rw [← hW0, ← this, f₁_apply_ne hj3]
    · have hthis : f₂ j = Wstar 1 j := by simpa using hagree 1 j hjS
      rw [← hW1, ← hthis, f₂_apply_ne hj3]
  -- messages pinned by interpolation
  have hm₀eq : m₀ = ![1, 0] := by
    refine message_eq_of_agree_two hjne ?_ ?_
    · rw [(hag j₁ hj₁S hj₁3).1]; show c₁ j₁ = rsEncoder ![1, 0] j₁; rfl
    · rw [(hag j₂ hj₂S hj₂3).1]; show c₁ j₂ = rsEncoder ![1, 0] j₂; rfl
  have hm₁eq : m₁ = ![0, 1] := by
    refine message_eq_of_agree_two hjne ?_ ?_
    · rw [(hag j₁ hj₁S hj₁3).2]; show c₂ j₁ = rsEncoder ![0, 1] j₁; rfl
    · rw [(hag j₂ hj₂S hj₂3).2]; show c₂ j₂ = rsEncoder ![0, 1] j₂; rfl
  -- the constraints kill the first message coordinates
  have hc0 : M 0 0 = 0 := by
    have := hconstr 0
    simp only [Matrix.cons_val_zero, Fin.sum_univ_two, v, Matrix.cons_val_one,
      Matrix.head_cons] at this
    -- M 0 0 * 1 + M 0 1 * 0 = 0
    linear_combination this
  have hc1 : M 1 0 = 0 := by
    have := hconstr 1
    simp only [Matrix.cons_val_one, Matrix.head_cons, Fin.sum_univ_two, v,
      Matrix.cons_val_zero] at this
    linear_combination this
  -- hence both M-rows are multiples of (0,1): the encoded rows are proportional
  have hM0 : M 0 = M 0 1 • ![(0 : Sextic), 1] := by
    funext i; fin_cases i <;> simp [hc0]
  have hM1 : M 1 = M 1 1 • ![(0 : Sextic), 1] := by
    funext i; fin_cases i <;> simp [hc1]
  set w : Fin 4 → Sextic := E ![0, 1] with hw
  have hprop0 : rsEncoder m₀ = M 0 1 • w := by
    rw [hm₀]
    conv_lhs => rw [hM0]
    rw [map_smul, hw]
  have hprop1 : rsEncoder m₁ = M 1 1 • w := by
    rw [hm₁]
    conv_lhs => rw [hM1]
    rw [map_smul, hw]
  -- proportionality contradicts (c₁ 0, c₂ 0, c₂ 1) = (1, 0, 1)
  have h00 : (1 : Sextic) = M 0 1 * w 0 := by
    have := congrFun hprop0 0
    rw [hm₀eq] at this
    simpa [rsEncoder, rsPoint, Pi.smul_apply, smul_eq_mul] using this
  have h10 : (0 : Sextic) = M 1 1 * w 0 := by
    have := congrFun hprop1 0
    rw [hm₁eq] at this
    simpa [rsEncoder, rsPoint, Pi.smul_apply, smul_eq_mul] using this
  have h11 : (1 : Sextic) = M 1 1 * w 1 := by
    have := congrFun hprop1 1
    rw [hm₁eq] at this
    simpa [rsEncoder, rsPoint, Pi.smul_apply, smul_eq_mul] using this
  -- M 1 1 ≠ 0 from h11; then w 0 = 0 from h10; then h00 gives 1 = 0
  have hM11 : M 1 1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at h11
    exact one_ne_zero h11
  have hw0 : w 0 = 0 := by
    rcases mul_eq_zero.mp h10.symm with h | h
    · exact absurd h hM11
    · exact h
  rw [hw0, mul_zero] at h00
  exact one_ne_zero h00

/-! ## The instance, the full-field winning set, and the residual theorems -/

/-- The violating attack instance. -/
noncomputable def attackInstance : ViolatingInstance KoalaBear.rsCodeSet (3 / 10) 2 where
  v := v
  μ₁ := 0
  μ₂ := 0
  f₁ := f₁
  f₂ := f₂
  violates := instance_violates

/-- The attack instance's winning set is ALL of `F`. -/
theorem attackInstance_winningSet_eq_univ :
    winningSet KoalaBear.rsCodeSet (3 / 10) attackInstance.v attackInstance.μ₁
      attackInstance.μ₂ attackInstance.f₁ attackInstance.f₂ = Set.univ :=
  Set.eq_univ_of_forall all_challenges_win

/-- **`fenziSanso_upperBound_attack_concrete_residual` is TRUE**: the winning set has the
full field's cardinality `p^6 ≥ 2^116 ≥ 2^70`. -/
theorem fenziSanso_upperBound_attack_concrete_residual_holds :
    ToyProblem.fenziSanso_upperBound_attack_concrete_residual := by
  refine ⟨attackInstance, ?_⟩
  rw [attackInstance_winningSet_eq_univ, Set.ncard_univ, Nat.card_eq_fintype_card]
  calc (2 : ℕ) ^ 70 ≤ 2 ^ 116 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    _ ≤ Fintype.card KoalaBear.Sextic := KoalaBear.card_sextic_ge

/-- **`fenziSanso_upperBound_attack_residual` is TRUE** — the original 116-bit leaderboard
attack residual, via the in-tree bridge from the concrete winning-set proof (issue #339
closeout: residuals 2 and 3 of the filed list are both theorems). -/
theorem fenziSanso_upperBound_attack_residual_holds :
    ToyProblem.fenziSanso_upperBound_attack_residual :=
  ToyProblem.fenziSanso_upperBound_attack_residual_of_concrete
    fenziSanso_upperBound_attack_concrete_residual_holds

/-- The unconditional 116-bit attack anchor at the genuine KoalaBear-sextic carrier
(`SecurityUpperBound koalaIRSConcrete`), no residual hypothesis. -/
noncomputable def attackUpperBound : ToyProblem.SecurityUpperBound ToyProblem.koalaIRSConcrete :=
  ToyProblem.fenziSanso_upperBound_attack_concrete
    fenziSanso_upperBound_attack_concrete_residual_holds

end KoalaBearAttack

end ArkLib

/-! ## Axiom audit -/
#print axioms ArkLib.KoalaBearAttack.rsPoint_injective
#print axioms ArkLib.KoalaBearAttack.message_eq_of_agree_two
#print axioms ArkLib.KoalaBearAttack.all_challenges_win
#print axioms ArkLib.KoalaBearAttack.instance_violates
#print axioms ArkLib.KoalaBearAttack.fenziSanso_upperBound_attack_concrete_residual_holds
#print axioms ArkLib.KoalaBearAttack.fenziSanso_upperBound_attack_residual_holds
#print axioms ArkLib.KoalaBearAttack.attackUpperBound

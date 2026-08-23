/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Round 15 (Issue #232, Proximity Prize) — the PRIZE-SCALE TWO-SIDED BRACKET

Self-contained (Mathlib-only) assembly of the sharpest verified bracket on the list-decoding
threshold agreement `a*` for an MDS-type code at the prize parameters
`n = 2^20`, `k = 2^19` (rate `1/2`), `2^20 ≤ q ≤ 2^256`, prize list threshold `Lstar = 2^128`.

For a code `C ⊆ F^ι` (`|ι| = n`) we measure, for a received word `w`, the **list at agreement
`a`**: the number of codewords agreeing with `w` on at least `a` coordinates.  The two halves:

* **Johnson half (∀ words, genuine cap).**  If distinct codewords pairwise agree on at most
  `p = k - 1` coordinates (the MDS/distinct-low-degree-polynomial property), then a fully
  re-proved integer Johnson bound — coordinate double count + Cauchy–Schwarz
  (`sq_sum_le_card_mul_sum_sq`) — gives `L·(a² − np) ≤ n·(a − p)` for the list size `L` at any
  agreement `a`, in the subtraction-free form `L·a² + n·p ≤ n·a + L·n·p`
  (`johnson_core`).  At `aJ = 741455` (the least integer with `aJ² > n(k−1)`) this yields
  `L ≤ 2^128` for **every** word (`johnson_smallList`).

* **Capacity half (∃ word, genuine excess).**  A fully re-proved averaging argument: for every
  word `f`, the number of words agreeing with `f` on `≥ a` coordinates is at least
  `C(n,a)·(q−1)^(n−a)` (disjoint agreement-pattern slices, `ball_lower`); summing over the
  `≥ q^k` codewords and pigeonholing over all `q^n` words (`exists_big_list`) produces a word
  whose list at agreement `aC = 2^19 + 4063 = 528351` exceeds
  `q^k · C(n,aC) · (q−1)^(n−aC) / q^n`.  The round-14 central-binomial/Pascal-shift crossover
  (re-proved here, strengthened to absorb the honest `(q/(q−1))^(n−aC) ≤ (n−aC+1)` loss via the
  binomial-expansion bound `q^e ≤ (e+1)(q−1)^e`, `pow_le_succ_mul_pred_pow`) shows this exceeds
  `2^128`.

* **The bracket** (`prize_scale_bracket`): with `aC = 528351 < aJ = 741455`, every prize-scale
  MDS-type code of size `≥ q^k` has
  - list ≤ `2^128` at agreement `741455` for **all** words, and
  - list > `2^128` at agreement `528351` for **some** word.
  Hence the threshold agreement `a*` where the prize error `ε*·|F| = 2^128` is crossed lies in
  `[528351, 741455]`, i.e. the threshold distance satisfies
  `δ* ∈ [1 − 741455/2^20, 1 − 528351/2^20] ≈ [0.29289, 0.49613]` — Johnson `1−√ρ` from below,
  capacity-minus-a-constant `1−ρ−ρ/129` from above.

The code-level hypotheses (pairwise agreement `≤ k−1`, size `≥ q^k`) are exactly the two defining
Reed–Solomon facts; `bracket_hypotheses_satisfiable` exhibits a concrete witness
(`RS[𝔽_1048583, 2^20 points, degree < 2^19]`) so the bracket theorem is non-vacuous.

Everything is elementary ℕ/ℤ arithmetic over the standard foundation.
-/

open Finset

namespace R15Bracket

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Part 1: the Johnson side, re-proved from scratch.

`johnson_core` is the integer Johnson bound in subtraction-free form: if the `#s` sets
`A i ⊆ ι` (`i ∈ s`) each have `≥ a` elements and pairwise intersections `≤ p`, then
`#s · a² + n·p ≤ n·a + #s · n·p`, i.e. `#s · (a² − np) ≤ n(a − p)`. -/

theorem johnson_core {κ : Type*} [DecidableEq κ] (s : Finset κ) (A : κ → Finset ι)
    (a p : ℕ)
    (ha : ∀ i ∈ s, a ≤ #(A i))
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → #(A i ∩ A j) ≤ p)
    (hap : p ≤ a) :
    #s * a ^ 2 + Fintype.card ι * p ≤ Fintype.card ι * a + #s * (Fintype.card ι * p) := by
  set n := Fintype.card ι with hn
  set L := #s with hLdef
  -- the coordinate degree function
  set d : ι → ℕ := fun x => ∑ i ∈ s, if x ∈ A i then 1 else 0 with hd
  -- (A) first moment: ∑ₓ d x = ∑ᵢ #(A i)
  have sum_d : ∑ x, d x = ∑ i ∈ s, #(A i) := by
    simp only [hd]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_boole]
    simp [Finset.filter_univ_mem]
  -- (B) second moment: ∑ₓ (d x)² = ∑ᵢ ∑ⱼ #(A i ∩ A j)
  have sq_d : ∀ x, d x ^ 2 = ∑ i ∈ s, ∑ j ∈ s, (if x ∈ A i ∩ A j then 1 else 0) := by
    intro x
    simp only [hd]
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h1 : x ∈ A i <;> by_cases h2 : x ∈ A j <;>
      simp [h1, h2, Finset.mem_inter]
  have sum_d_sq : ∑ x, d x ^ 2 = ∑ i ∈ s, ∑ j ∈ s, #(A i ∩ A j) := by
    rw [Finset.sum_congr rfl fun x _ => sq_d x, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_boole, Finset.filter_univ_mem]
    exact Nat.cast_id _
  -- (C) the three working facts
  have f1 : L * a ≤ ∑ x, d x := by
    rw [sum_d, ← smul_eq_mul]
    exact Finset.card_nsmul_le_sum s _ a ha
  have f2 : (∑ x, d x) ^ 2 ≤ n * ∑ x, d x ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι)) (f := d)
    simpa [Finset.card_univ] using h
  have f3 : ∑ x, d x ^ 2 ≤ (∑ x, d x) + L * ((L - 1) * p) := by
    rw [sum_d_sq, sum_d]
    have step : ∀ i ∈ s, ∑ j ∈ s, #(A i ∩ A j) ≤ #(A i) + (L - 1) * p := by
      intro i hi
      rw [← Finset.add_sum_erase s _ hi, Finset.inter_self]
      refine Nat.add_le_add_left ?_ _
      calc ∑ j ∈ s.erase i, #(A i ∩ A j)
          ≤ #(s.erase i) • p := Finset.sum_le_card_nsmul _ _ _ (fun j hj =>
            hpair i hi j (Finset.mem_of_mem_erase hj) (Ne.symm (Finset.ne_of_mem_erase hj)))
        _ = (L - 1) * p := by rw [smul_eq_mul, Finset.card_erase_of_mem hi]
    calc ∑ i ∈ s, ∑ j ∈ s, #(A i ∩ A j)
        ≤ ∑ i ∈ s, (#(A i) + (L - 1) * p) := Finset.sum_le_sum step
      _ = (∑ i ∈ s, #(A i)) + L * ((L - 1) * p) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  -- (D) the case analysis
  rcases Nat.eq_zero_or_pos L with hL0 | hL1
  · simp only [hL0, Nat.zero_mul, Nat.zero_add, Nat.add_zero]
    exact Nat.mul_le_mul le_rfl hap
  rcases Nat.lt_or_ge (L * a) n with hsmall | hbig
  · -- degenerate regime L·a < n : termwise
    have h1 : L * a ^ 2 ≤ n * a := by
      calc L * a ^ 2 = (L * a) * a := by ring
        _ ≤ n * a := Nat.mul_le_mul hsmall.le le_rfl
    have h2 : n * p ≤ L * (n * p) := Nat.le_mul_of_pos_left _ hL1
    omega
  · -- main regime L·a ≥ n : Cauchy–Schwarz, in ℤ
    set S : ℕ := ∑ x, d x with hS
    set P : ℕ := ∑ x, d x ^ 2 with hP
    have hL1' : (1 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL1
    have f1' : (L : ℤ) * a ≤ (S : ℤ) := by exact_mod_cast f1
    have f2' : (S : ℤ) ^ 2 ≤ (n : ℤ) * P := by exact_mod_cast f2
    have f3' : (P : ℤ) ≤ (S : ℤ) + (L : ℤ) * (((L : ℤ) - 1) * p) := by
      have h := f3
      zify [hL1] at h
      exact h
    have hbig' : (n : ℤ) ≤ (L : ℤ) * a := by exact_mod_cast hbig
    have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    have hprod : (0 : ℤ) ≤ ((S : ℤ) - L * a) * ((S : ℤ) + L * a - n) := by
      apply mul_nonneg
      · linarith
      · linarith
    have key : (L : ℤ) * ((L : ℤ) * a ^ 2 + n * p) ≤ (L : ℤ) * ((n : ℤ) * a + L * (n * p)) := by
      nlinarith [hprod, f2', mul_le_mul_of_nonneg_left f3' hn0]
    have final : ((L : ℤ) * a ^ 2 + n * p) ≤ ((n : ℤ) * a + L * (n * p)) :=
      le_of_mul_le_mul_left key (by linarith)
    exact_mod_cast final

/-- **Johnson list cap.**  If moreover `a² > n·p` (the Johnson radius condition) and the cap
budget `n·a + Lstar·n·p ≤ n·p + Lstar·a²` (⇔ `n(a−p) ≤ Lstar(a²−np)`) holds, the family has at
most `Lstar` members. -/
theorem johnson_smallList {κ : Type*} [DecidableEq κ] (s : Finset κ) (A : κ → Finset ι)
    (a p Lstar : ℕ)
    (ha : ∀ i ∈ s, a ≤ #(A i))
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → #(A i ∩ A j) ≤ p)
    (hap : p ≤ a)
    (hgap : Fintype.card ι * p < a ^ 2)
    (hcap : Fintype.card ι * a + Lstar * (Fintype.card ι * p) ≤
      Fintype.card ι * p + Lstar * a ^ 2) :
    #s ≤ Lstar := by
  have core := johnson_core s A a p ha hpair hap
  by_contra hcon
  push_neg at hcon
  set n := Fintype.card ι with hn
  have hgap' : ((n : ℤ)) * p < (a : ℤ) ^ 2 := by exact_mod_cast hgap
  have core' : ((#s : ℤ)) * a ^ 2 + n * p ≤ (n : ℤ) * a + (#s : ℤ) * (n * p) := by
    exact_mod_cast core
  have hcap' : ((n : ℤ)) * a + (Lstar : ℤ) * (n * p) ≤ (n : ℤ) * p + (Lstar : ℤ) * a ^ 2 := by
    exact_mod_cast hcap
  have hcon' : (Lstar : ℤ) < (#s : ℤ) := by exact_mod_cast hcon
  nlinarith [mul_pos (show (0 : ℤ) < (a : ℤ) ^ 2 - n * p by linarith)
    (show (0 : ℤ) < (#s : ℤ) - Lstar by linarith), core', hcap']

/-! ## Part 2: the capacity side — agreement slices and the averaging pigeonhole. -/

variable {F : Type*} [Fintype F] [DecidableEq F]

/-- The agreement set of two words. -/
def agreeSet (u v : ι → F) : Finset ι := univ.filter fun x => u x = v x

/-- **Agreement-ball volume lower bound.**  For any word `f`, at least
`C(n,a)·(q−1)^(n−a)` words agree with `f` on at least `a` coordinates: one disjoint slice of
`(q−1)^(n−a)` words for each exact agreement pattern `T` of size `a`. -/
theorem ball_lower (f : ι → F) (a : ℕ) :
    (Fintype.card ι).choose a * (Fintype.card F - 1) ^ (Fintype.card ι - a) ≤
      #(univ.filter fun w : ι → F => a ≤ #(agreeSet w f)) := by
  set n := Fintype.card ι with hn
  set q := Fintype.card F with hq
  set S : Finset ι → Finset (ι → F) := fun T =>
    Fintype.piFinset (fun x => if x ∈ T then {f x} else univ.erase (f x)) with hSdef
  have hmem : ∀ T (w : ι → F), w ∈ S T ↔ ∀ x, (x ∈ T → w x = f x) ∧ (x ∉ T → w x ≠ f x) := by
    intro T w
    simp only [hSdef, Fintype.mem_piFinset]
    refine forall_congr' fun x => ?_
    by_cases hx : x ∈ T <;> simp [hx]
  have hagree : ∀ T (w : ι → F), w ∈ S T → agreeSet w f = T := by
    intro T w hw
    rw [hmem] at hw
    ext x
    simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hwx
      by_contra hxT
      exact (hw x).2 hxT hwx
    · intro hxT
      exact (hw x).1 hxT
  have hcard : ∀ T ∈ powersetCard a (univ : Finset ι), #(S T) = (q - 1) ^ (n - a) := by
    intro T hT
    have hTcard : #T = a := (Finset.mem_powersetCard.mp hT).2
    simp only [hSdef]
    rw [Fintype.card_piFinset]
    have hterm : ∀ x : ι,
        #(if x ∈ T then ({f x} : Finset F) else univ.erase (f x)) =
          if x ∈ T then 1 else q - 1 := by
      intro x
      by_cases hx : x ∈ T <;>
        simp [hx, Finset.card_erase_of_mem (Finset.mem_univ (f x)), Finset.card_univ, hq]
    rw [Finset.prod_congr rfl fun x _ => hterm x, Finset.prod_ite, Finset.prod_const_one,
      Finset.prod_const, one_mul]
    congr 1
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset ι)) (· ∈ T)
    have hmemT : #(univ.filter (· ∈ T)) = a := by
      rw [Finset.filter_univ_mem]; exact hTcard
    have huniv : #(univ : Finset ι) = n := Finset.card_univ
    omega
  have hdisj : ((powersetCard a (univ : Finset ι) : Finset (Finset ι)) :
      Set (Finset ι)).PairwiseDisjoint S := by
    intro T hT T' hT' hne
    refine Finset.disjoint_left.mpr fun w hw hw' => hne ?_
    rw [← hagree T w hw, ← hagree T' w hw']
  have hsub : (powersetCard a (univ : Finset ι)).biUnion S ⊆
      univ.filter fun w : ι → F => a ≤ #(agreeSet w f) := by
    intro w hw
    rw [Finset.mem_biUnion] at hw
    obtain ⟨T, hT, hwT⟩ := hw
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [hagree T w hwT, (Finset.mem_powersetCard.mp hT).2]⟩
  calc n.choose a * (q - 1) ^ (n - a)
      = ∑ _T ∈ powersetCard a (univ : Finset ι), (q - 1) ^ (n - a) := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, smul_eq_mul]
    _ = ∑ T ∈ powersetCard a (univ : Finset ι), #(S T) :=
        (Finset.sum_congr rfl fun T hT => (hcard T hT).symm)
    _ = #((powersetCard a (univ : Finset ι)).biUnion S) := (Finset.card_biUnion hdisj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- **Averaging pigeonhole.**  If `q^n · Lstar < #C · C(n,a)·(q−1)^(n−a)`, then SOME word has
more than `Lstar` codewords agreeing with it on `≥ a` coordinates. -/
theorem exists_big_list (C : Finset (ι → F)) (a Lstar : ℕ)
    (hbig : Fintype.card F ^ Fintype.card ι * Lstar <
      #C * ((Fintype.card ι).choose a * (Fintype.card F - 1) ^ (Fintype.card ι - a))) :
    ∃ w : ι → F, Lstar < #(C.filter fun f => a ≤ #(agreeSet w f)) := by
  by_contra hcon
  push_neg at hcon
  have swap : ∑ w : ι → F, #(C.filter fun f => a ≤ #(agreeSet w f))
      = ∑ f ∈ C, #(univ.filter fun w : ι → F => a ≤ #(agreeSet w f)) := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  have lower : #C * ((Fintype.card ι).choose a *
      (Fintype.card F - 1) ^ (Fintype.card ι - a)) ≤
      ∑ f ∈ C, #(univ.filter fun w : ι → F => a ≤ #(agreeSet w f)) := by
    rw [← smul_eq_mul]
    exact Finset.card_nsmul_le_sum C _ _ fun f _ => ball_lower f a
  have upper : ∑ w : ι → F, #(C.filter fun f => a ≤ #(agreeSet w f)) ≤
      Fintype.card F ^ Fintype.card ι * Lstar := by
    calc ∑ w : ι → F, #(C.filter fun f => a ≤ #(agreeSet w f))
        ≤ #(univ : Finset (ι → F)) • Lstar :=
          Finset.sum_le_card_nsmul _ _ _ fun w _ => hcon w
      _ = Fintype.card F ^ Fintype.card ι * Lstar := by
          rw [smul_eq_mul, Finset.card_univ, Fintype.card_fun]
  exact absurd hbig (not_lt.mpr (lower.trans (swap ▸ upper)))

/-! ## Part 3: the round-14 crossover arithmetic, restated and strengthened
(`Λ ≤ 2^147` instead of `2^128`, to absorb the `(e+1)`-factor from the honest
`(q−1)^e` ball volume). -/

theorem choose_le_succ_succ (n m : ℕ) : n.choose m ≤ (n + 1).choose (m + 1) := by
  rw [Nat.choose_succ_succ']
  exact Nat.le_add_right _ _

/-- The Pascal shift: `C(n, m) ≤ C(n + j, m + j)`. -/
theorem choose_le_add_add (n m j : ℕ) : n.choose m ≤ (n + j).choose (m + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc n.choose m ≤ (n + j).choose (m + j) := ih
      _ ≤ (n + j + 1).choose (m + j + 1) := choose_le_succ_succ _ _

/-- Central-binomial lower bound after a Pascal shift by `2t`:
`4^(m−t) ≤ 2(m−t) · C(2m, m+t)` for `t < m`. -/
theorem four_pow_le_shift_choose {m t : ℕ} (ht : t < m) :
    4 ^ (m - t) ≤ 2 * (m - t) * (2 * m).choose (m + t) := by
  have hpos : 0 < m - t := Nat.sub_pos_of_lt ht
  have hcb : 4 ^ (m - t) ≤ 2 * (m - t) * Nat.centralBinom (m - t) :=
    Nat.four_pow_le_two_mul_self_mul_centralBinom (m - t) hpos
  have hshift : Nat.centralBinom (m - t) ≤ (2 * m).choose (m + t) := by
    have h := choose_le_add_add (2 * (m - t)) (m - t) (2 * t)
    have e1 : 2 * (m - t) + 2 * t = 2 * m := by omega
    have e2 : m - t + 2 * t = m + t := by omega
    rw [e1, e2] at h
    exact h
  calc 4 ^ (m - t) ≤ 2 * (m - t) * Nat.centralBinom (m - t) := hcb
    _ ≤ 2 * (m - t) * (2 * m).choose (m + t) := Nat.mul_le_mul le_rfl hshift

/-- **Rate-1/2 crossover, strengthened.**  With `t < m ≤ 2^62`, `258t + 212 ≤ 2m`, prize field
`q ≤ 2^256`, and budget `Λ ≤ 2^147`: `Λ · q^t < C(2m, m+t)`. -/
theorem crossover_rate_half' {m t q Λ : ℕ}
    (ht : t < m) (hm : m ≤ 2 ^ 62) (hscale : 258 * t + 212 ≤ 2 * m)
    (hq : q ≤ 2 ^ 256) (hΛ : Λ ≤ 2 ^ 147) :
    Λ * q ^ t < (2 * m).choose (m + t) := by
  have hpos : 0 < 2 * (m - t) := by omega
  have h1 : Λ * q ^ t ≤ 2 ^ (147 + 256 * t) := by
    calc Λ * q ^ t ≤ 2 ^ 147 * (2 ^ 256) ^ t :=
          Nat.mul_le_mul hΛ (Nat.pow_le_pow_left hq t)
      _ = 2 ^ (147 + 256 * t) := by rw [← Nat.pow_mul, ← Nat.pow_add]
  have h2 : 2 * (m - t) * 2 ^ (147 + 256 * t) < 4 ^ (m - t) := by
    have hmt : 2 * (m - t) ≤ 2 ^ 63 := by
      calc 2 * (m - t) ≤ 2 * m := by omega
        _ ≤ 2 * 2 ^ 62 := by omega
        _ = 2 ^ 63 := by norm_num
    have hfour : (4 : ℕ) ^ (m - t) = 2 ^ (2 * (m - t)) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← Nat.pow_mul]
    rw [hfour]
    calc 2 * (m - t) * 2 ^ (147 + 256 * t)
        ≤ 2 ^ 63 * 2 ^ (147 + 256 * t) := Nat.mul_le_mul hmt le_rfl
      _ = 2 ^ (210 + 256 * t) := by rw [← Nat.pow_add]; congr 1; omega
      _ < 2 ^ (2 * (m - t)) := by
          apply Nat.pow_lt_pow_right (by norm_num)
          omega
  have h3 : 4 ^ (m - t) ≤ 2 * (m - t) * (2 * m).choose (m + t) :=
    four_pow_le_shift_choose ht
  have h4 : 2 * (m - t) * (Λ * q ^ t) < 2 * (m - t) * (2 * m).choose (m + t) := by
    calc 2 * (m - t) * (Λ * q ^ t)
        ≤ 2 * (m - t) * 2 ^ (147 + 256 * t) := Nat.mul_le_mul le_rfl h1
      _ < 4 ^ (m - t) := h2
      _ ≤ 2 * (m - t) * (2 * m).choose (m + t) := h3
  exact Nat.lt_of_mul_lt_mul_left h4

/-! ## Part 4: the honest `(q−1)`-correction: `q^e ≤ (e+1)·(q−1)^e` for `e ≤ q−1`. -/

theorem pow_le_succ_mul_pred_pow {q e : ℕ} (he : e ≤ q - 1) :
    q ^ e ≤ (e + 1) * (q - 1) ^ e := by
  rcases Nat.eq_zero_or_pos q with hq0 | hq1
  · have he0 : e = 0 := by omega
    subst he0
    simp
  set b := q - 1 with hb
  have hqb : q = b + 1 := by omega
  rw [hqb, add_pow]
  have hterm : ∀ m ∈ range (e + 1), b ^ m * 1 ^ (e - m) * (e.choose m) ≤ b ^ e := by
    intro m hm
    have hme : m ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [one_pow, mul_one]
    have h1 : e.choose m ≤ e ^ (e - m) := by
      rw [← Nat.choose_symm hme]
      exact Nat.choose_le_pow e (e - m)
    have h2 : (e : ℕ) ^ (e - m) ≤ b ^ (e - m) := Nat.pow_le_pow_left he (e - m)
    calc b ^ m * e.choose m ≤ b ^ m * b ^ (e - m) :=
          Nat.mul_le_mul le_rfl (h1.trans h2)
      _ = b ^ e := by rw [← pow_add]; congr 1; omega
  calc ∑ m ∈ range (e + 1), b ^ m * 1 ^ (e - m) * (e.choose m)
      ≤ ∑ _m ∈ range (e + 1), b ^ e := Finset.sum_le_sum hterm
    _ = (e + 1) * b ^ e := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-! ## Part 5: THE PRIZE-SCALE TWO-SIDED BRACKET. -/

/-- **The prize-scale two-sided bracket** at `n = 2^20`, rate `1/2` (`k = 2^19`),
`2^20 ≤ q = |F| ≤ 2^256`, prize threshold `Lstar = 2^128`, for any MDS-type code `C`
(pairwise agreement `≤ k−1`, size `≥ q^k` — the two Reed–Solomon facts):

* **Johnson half (∀ words):** at agreement `aJ = 741455` (`aJ/n ≈ 0.70711 ≈ √ρ`,
  `δ = 1 − aJ/n ≈ 0.29289 ≈ 1−√ρ`) the list never exceeds `2^128`;
* **capacity half (∃ word):** at agreement `aC = 528351` (`aC/n ≈ 0.50387`,
  `δ = 1 − aC/n ≈ 0.49613 ≈ 1 − ρ − ρ/129`) some word's list exceeds `2^128`;
* `aC < aJ`.

Hence the threshold agreement `a*` where the prize error is crossed satisfies
`a* ∈ [528351, 741455]`, i.e. `δ* ∈ [0.29289, 0.49613]`. -/
theorem prize_scale_bracket
    {F : Type*} [Fintype F] [DecidableEq F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hn : Fintype.card ι = 2 ^ 20)
    (hqlo : 2 ^ 20 ≤ Fintype.card F) (hqhi : Fintype.card F ≤ 2 ^ 256)
    (C : Finset (ι → F))
    (hsize : Fintype.card F ^ (2 ^ 19 : ℕ) ≤ #C)
    (hpairwise : ∀ f ∈ C, ∀ g ∈ C, f ≠ g → #(agreeSet f g) ≤ 2 ^ 19 - 1) :
    (∀ w : ι → F, #(C.filter fun f => 741455 ≤ #(agreeSet w f)) ≤ 2 ^ 128) ∧
    (∃ w : ι → F, 2 ^ 128 < #(C.filter fun f => 528351 ≤ #(agreeSet w f))) ∧
    (528351 : ℕ) < 741455 := by
  refine ⟨?johnson, ?capacity, by norm_num⟩
  case johnson =>
    intro w
    refine johnson_smallList (C.filter fun f => 741455 ≤ #(agreeSet w f))
      (fun f => agreeSet w f) 741455 (2 ^ 19 - 1) (2 ^ 128) ?_ ?_ ?_ ?_ ?_
    · intro f hf
      exact (Finset.mem_filter.mp hf).2
    · intro f hf g hg hfg
      have hsub : agreeSet w f ∩ agreeSet w g ⊆ agreeSet f g := by
        intro x hx
        rw [Finset.mem_inter] at hx
        obtain ⟨h1, h2⟩ := hx
        simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2 ⊢
        rw [← h1, ← h2]
      exact le_trans (Finset.card_le_card hsub)
        (hpairwise f (Finset.mem_filter.mp hf).1 g (Finset.mem_filter.mp hg).1 hfg)
    · norm_num
    · rw [hn]; norm_num
    · rw [hn]; norm_num
  case capacity =>
    set q := Fintype.card F with hqdef
    have hq2 : 2 ≤ q := le_trans (by norm_num) hqlo
    -- the (q−1) correction at e = n − aC = 520225
    have he_le : (520225 : ℕ) ≤ q - 1 := by omega
    have h1 : q ^ (520225 : ℕ) ≤ 520226 * (q - 1) ^ (520225 : ℕ) := by
      have h := pow_le_succ_mul_pred_pow (q := q) (e := 520225) he_le
      norm_num at h
      exact h
    -- the strengthened crossover at Λ = 520226·2^128 ≤ 2^147
    have h2 : 520226 * 2 ^ 128 * q ^ (4063 : ℕ) < (2 ^ 20 : ℕ).choose 528351 := by
      have h := crossover_rate_half' (m := 2 ^ 19) (t := 4063) (q := q)
        (Λ := 520226 * 2 ^ 128) (by norm_num) (by norm_num) (by norm_num) hqhi (by norm_num)
      have e1 : 2 * 2 ^ 19 = (2 ^ 20 : ℕ) := by norm_num
      have e2 : 2 ^ 19 + 4063 = (528351 : ℕ) := by norm_num
      rw [e1, e2] at h
      exact h
    have hqpos : 0 < q := by omega
    have hq1pos : 0 < q - 1 := by omega
    have hkey : 0 < q ^ (2 ^ 19 : ℕ) * (q - 1) ^ (520225 : ℕ) :=
      Nat.mul_pos (pow_pos hqpos _) (pow_pos hq1pos _)
    have hsplit : q ^ (2 ^ 20 : ℕ) = q ^ (2 ^ 19 : ℕ) * q ^ (4063 : ℕ) * q ^ (520225 : ℕ) := by
      rw [← pow_add, ← pow_add]
      norm_num
    have hbig : q ^ (2 ^ 20 : ℕ) * 2 ^ 128 <
        #C * ((2 ^ 20 : ℕ).choose 528351 * (q - 1) ^ (520225 : ℕ)) := by
      calc q ^ (2 ^ 20 : ℕ) * 2 ^ 128
          = q ^ (2 ^ 19 : ℕ) * q ^ (4063 : ℕ) * q ^ (520225 : ℕ) * 2 ^ 128 := by rw [hsplit]
        _ ≤ q ^ (2 ^ 19 : ℕ) * q ^ (4063 : ℕ) * (520226 * (q - 1) ^ (520225 : ℕ)) * 2 ^ 128 :=
            Nat.mul_le_mul (Nat.mul_le_mul le_rfl h1) le_rfl
        _ = q ^ (2 ^ 19 : ℕ) * (q - 1) ^ (520225 : ℕ) * (520226 * 2 ^ 128 * q ^ (4063 : ℕ)) := by
            ring
        _ < q ^ (2 ^ 19 : ℕ) * (q - 1) ^ (520225 : ℕ) * (2 ^ 20 : ℕ).choose 528351 :=
            mul_lt_mul_of_pos_left h2 hkey
        _ = q ^ (2 ^ 19 : ℕ) * ((2 ^ 20 : ℕ).choose 528351 * (q - 1) ^ (520225 : ℕ)) := by
            ring
        _ ≤ #C * ((2 ^ 20 : ℕ).choose 528351 * (q - 1) ^ (520225 : ℕ)) :=
            Nat.mul_le_mul hsize le_rfl
    refine exists_big_list C 528351 (2 ^ 128) ?_
    rw [hn]
    have hsub : (2 ^ 20 : ℕ) - 528351 = 520225 := by norm_num
    rw [hsub]
    exact hbig

/-! ## Part 6: non-vacuity — a concrete Reed–Solomon witness satisfying every hypothesis.

`RS[𝔽_p, 2^20 points, degree < 2^19]` over the least prime `p = 1048583 > 2^20`: the code
`codeW` has exactly `q^(2^19)` codewords (interpolation/injectivity) and distinct codewords
agree on at most `2^19 − 1` points (root counting), so `prize_scale_bracket` applies to it. -/

section Witness

/- The `constructorNameAsVariable` name-style linter (a purely cosmetic check) overflows its
recursion budget traversing the large `Fintype`-instance terms occurring in membership
hypotheses about `codeW`; it is disabled here. This has no bearing on proof correctness. -/
set_option linter.constructorNameAsVariable false

open Polynomial

/-- The least prime above `2^20 = 1048576`. -/
abbrev pW : ℕ := 1048583

instance factW : Fact (Nat.Prime pW) := ⟨by norm_num⟩

instance moduleInstance_ScaleBracketFull_1 : NeZero pW := ⟨by norm_num⟩

/-- The `2^20` evaluation points, embedded in `𝔽_p`. -/
def embW (x : Fin (2 ^ 20)) : ZMod pW := (x.val : ZMod pW)

theorem embW_inj : Function.Injective embW := by
  intro x y h
  have hx : (embW x).val = x.val :=
    ZMod.val_cast_of_lt (Nat.lt_of_lt_of_le x.isLt (by norm_num))
  have hy : (embW y).val = y.val :=
    ZMod.val_cast_of_lt (Nat.lt_of_lt_of_le y.isLt (by norm_num))
  exact Fin.ext (by rw [← hx, ← hy, h])

/-- The Reed–Solomon code: evaluations of polynomials of degree `< 2^19` (given by coefficient
vectors) at the `2^20` points. -/
def codeW : Finset (Fin (2 ^ 20) → ZMod pW) :=
  Finset.image (fun c : Fin (2 ^ 19) → ZMod pW => fun x => ∑ i, c i * embW x ^ (i : ℕ))
    Finset.univ

/-- The difference polynomial of two coefficient vectors. -/
noncomputable def diffPolyW (c c' : Fin (2 ^ 19) → ZMod pW) : Polynomial (ZMod pW) :=
  ∑ i : Fin (2 ^ 19), Polynomial.C (c i - c' i) * Polynomial.X ^ (i : ℕ)

theorem coeffW (c c' : Fin (2 ^ 19) → ZMod pW) (j : Fin (2 ^ 19)) :
    (diffPolyW c c').coeff (j : ℕ) = c j - c' j := by
  unfold diffPolyW
  rw [Polynomial.finset_sum_coeff]
  have hterm : ∀ i : Fin (2 ^ 19),
      (Polynomial.C (c i - c' i) * Polynomial.X ^ (i : ℕ)).coeff (j : ℕ)
        = if j = i then c i - c' i else 0 := by
    intro i
    rw [Polynomial.coeff_C_mul_X_pow]
    rcases eq_or_ne j i with rfl | hij
    · simp
    · have hne : (j : ℕ) ≠ (i : ℕ) := fun hc => hij (Fin.ext hc)
      simp [hne, hij]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_eq]
  simp

theorem evalW (c c' : Fin (2 ^ 19) → ZMod pW) (z : ZMod pW) :
    (diffPolyW c c').eval z =
      (∑ i, c i * z ^ (i : ℕ)) - ∑ i, c' i * z ^ (i : ℕ) := by
  unfold diffPolyW
  rw [Polynomial.eval_finset_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [sub_mul]

theorem degW (c c' : Fin (2 ^ 19) → ZMod pW) :
    (diffPolyW c c').natDegree ≤ 2 ^ 19 - 1 := by
  unfold diffPolyW
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  rw [Polynomial.natDegree_X_pow]
  have := i.isLt
  omega

/-- Root counting: a nonzero difference polynomial vanishes on at most `2^19 − 1` of the
evaluation points. -/
theorem rootsW {c c' : Fin (2 ^ 19) → ZMod pW} (h : diffPolyW c c' ≠ 0) :
    #(univ.filter fun x : Fin (2 ^ 20) => (diffPolyW c c').eval (embW x) = 0) ≤
      2 ^ 19 - 1 := by
  have hmaps : Set.MapsTo embW
      ↑(univ.filter fun x : Fin (2 ^ 20) => (diffPolyW c c').eval (embW x) = 0)
      ↑((diffPolyW c c').roots.toFinset) := by
    intro x hx
    have hx' := Finset.mem_coe.mp hx
    rw [Finset.mem_filter] at hx'
    refine Finset.mem_coe.mpr ?_
    rw [Multiset.mem_toFinset, Polynomial.mem_roots h]
    exact hx'.2
  calc #(univ.filter fun x : Fin (2 ^ 20) => (diffPolyW c c').eval (embW x) = 0)
      ≤ #((diffPolyW c c').roots.toFinset) :=
        Finset.card_le_card_of_injOn embW hmaps embW_inj.injOn
    _ ≤ Multiset.card (diffPolyW c c').roots := Multiset.toFinset_card_le _
    _ ≤ (diffPolyW c c').natDegree := Polynomial.card_roots' _
    _ ≤ 2 ^ 19 - 1 := degW c c'

/-- Counting functions `Fin k → G`, proved generically (so that no two differently-synthesized
`Fintype` instances on concrete types ever need a definitional-equality check). -/
theorem card_univ_fun (G : Type*) [Fintype G] [DecidableEq G] (k : ℕ) :
    #(univ : Finset (Fin k → G)) = Fintype.card G ^ k := by
  rw [← Fintype.piFinset_univ, Fintype.card_piFinset, Finset.prod_const, Finset.card_fin,
    Finset.card_univ]

/-- RS fact 1: the code has full size `q^k`. -/
theorem codeW_card : Fintype.card (ZMod pW) ^ (2 ^ 19 : ℕ) ≤ #codeW := by
  have hinj : Function.Injective
      (fun c : Fin (2 ^ 19) → ZMod pW => fun x : Fin (2 ^ 20) => ∑ i, c i * embW x ^ (i : ℕ)) := by
    intro c c' h
    by_contra hne
    have hP : diffPolyW c c' ≠ 0 := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
      intro h0
      apply hj
      have hc := coeffW c c' j
      rw [h0, Polynomial.coeff_zero] at hc
      exact sub_eq_zero.mp hc.symm
    have hall : (univ.filter fun x : Fin (2 ^ 20) =>
        (diffPolyW c c').eval (embW x) = 0) = univ := by
      rw [Finset.filter_eq_self]
      intro x _
      rw [evalW, sub_eq_zero]
      exact congrFun h x
    have hcard := rootsW hP
    rw [hall, Finset.card_univ, Fintype.card_fin] at hcard
    norm_num at hcard
  rw [codeW, Finset.card_image_of_injective _ hinj]
  exact (card_univ_fun (ZMod pW) (2 ^ 19)).ge

/-- RS fact 2: distinct codewords agree on at most `2^19 − 1` points. -/
theorem codeW_pairwise : ∀ f ∈ codeW, ∀ g ∈ codeW, f ≠ g →
    #(agreeSet f g) ≤ 2 ^ 19 - 1 := by
  intro f hf g hg hfg
  simp only [codeW, Finset.mem_image] at hf hg
  obtain ⟨c, -, rfl⟩ := hf
  obtain ⟨c', -, rfl⟩ := hg
  have hP : diffPolyW c c' ≠ 0 := by
    intro h0
    apply hfg
    funext x
    have he := evalW c c' (embW x)
    rw [h0, Polynomial.eval_zero] at he
    exact sub_eq_zero.mp he.symm
  have hsub : agreeSet (fun x => ∑ i, c i * embW x ^ (i : ℕ))
      (fun x => ∑ i, c' i * embW x ^ (i : ℕ)) ⊆
      univ.filter fun x : Fin (2 ^ 20) => (diffPolyW c c').eval (embW x) = 0 := by
    intro x hx
    simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [evalW, sub_eq_zero]
    exact hx
  exact le_trans (Finset.card_le_card hsub) (rootsW hP)

/-- **Non-vacuity of the bracket**: the concrete prize-scale Reed–Solomon code
`RS[𝔽_1048583, 2^20 points, degree < 2^19]` satisfies every hypothesis of
`prize_scale_bracket`, and therefore exhibits the verified two-sided bracket: list ≤ `2^128`
at agreement `741455` for ALL words, list > `2^128` at agreement `528351` for SOME word. -/
theorem prize_bracket_nonvacuous :
    (∀ w : Fin (2 ^ 20) → ZMod pW,
      #(codeW.filter fun f => 741455 ≤ #(agreeSet w f)) ≤ 2 ^ 128) ∧
    (∃ w : Fin (2 ^ 20) → ZMod pW,
      2 ^ 128 < #(codeW.filter fun f => 528351 ≤ #(agreeSet w f))) := by
  have h := prize_scale_bracket (F := ZMod pW) (ι := Fin (2 ^ 20))
    (by rw [Fintype.card_fin])
    (by rw [ZMod.card]; norm_num)
    (by rw [ZMod.card]; norm_num)
    codeW codeW_card codeW_pairwise
  exact ⟨h.1, h.2.1⟩

end Witness

end R15Bracket

#print axioms R15Bracket.johnson_core
#print axioms R15Bracket.johnson_smallList
#print axioms R15Bracket.ball_lower
#print axioms R15Bracket.exists_big_list
#print axioms R15Bracket.crossover_rate_half'
#print axioms R15Bracket.pow_le_succ_mul_pred_pow
#print axioms R15Bracket.prize_scale_bracket
#print axioms R15Bracket.codeW_card
#print axioms R15Bracket.codeW_pairwise
#print axioms R15Bracket.prize_bracket_nonvacuous

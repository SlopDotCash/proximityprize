/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The quotient (DEEP) construction — polynomial core, kernel-checked

The polynomial facts behind the per-prime lower-half closure (Theorem Q of
`QuotientPerPrimeInstantiation.md` / DISPROOF_LOG "the lower half closes";
[CS25], [BCHKS25 §6], [KKH ePrint 2026/782 Appendix A]):

* **Far side** (`farness_card_le`): on any evaluation set avoiding the `m`-fiber of `z`
  (`w := z^m`), a candidate codeword `c` of degree `< k` "agrees with `1/(x^m − w)`" — i.e.
  `c(x)·(x^m − w) = 1` — on at most `k + m − 1` points: agreement points are roots of the
  nonzero polynomial `c·(X^m − C w) − 1` of degree `≤ k − 1 + m`.

* **Bad-scalar side**: for the vanishing polynomial `v_S = Π_{a∈S}(X − C a)` of an `r`-subset
  `S` and its tail `p_S := X^r − v_S` (degree `≤ r − 1`, `tail_natDegree_le`), the deep quotient
  `q_S := (p_S(X^m) − p_S(w)) / (X^m − C w)` exists as a polynomial (`quotient_exists`), has
  degree `≤ (r−2)·m` when `r ≥ 1, m ≥ 1` (`quotient_natDegree_le` — i.e. `q_S` is a codeword of
  the dimension-`(r−1)m` code, and of the exact-rate code after the `r = ρs+1` shift), and at
  every point `x` of the `m`-power fiber over `S` satisfies the agreement identity
  `q_S(x)·(x^m − w) = x^{r·m} − p_S(w)` (`quotient_agree`) — exhibiting `λ_S = −p_S(w)` as a
  bad scalar of the line `(u₀, u₁) = (x^{rm}, 1)/(x^m − w)`.

Together with `ValueSpreadSecondMoment.exists_eval_image_spread` (the z-selection step), these
are the constructive content of the lower half. Remaining to a full in-tree `epsMCA` statement:
the smooth-domain fiber-count bookkeeping and the `MCALowerBound` wiring. Everything here is
elementary polynomial algebra over an arbitrary field.
-/

namespace ArkLib.ProximityGap.QuotientCore

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Far side of the deep quotient.** If every `x ∈ D` has `x^m ≠ w` (equivalently
`x^m − w ≠ 0`), then any polynomial `c` with `c.natDegree < k` (`1 ≤ k`, `1 ≤ m`) satisfies
`c(x)·(x^m − w) = 1` on at most `k + m − 1` points of `D`. -/
theorem farness_card_le {m : ℕ} (D : Finset F) (w : F)
    {k : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) (c : F[X]) (hc : c.natDegree < k) :
    (D.filter fun x => c.eval x * (x ^ m - w) = 1).card ≤ k + m - 1 := by
  classical
  set P : F[X] := c * (X ^ m - C w) - 1 with hP
  have hXmne : (X ^ m - C w : F[X]) ≠ 0 := by
    intro h0
    have hdeg := natDegree_X_pow_sub_C (n := m) (r := w)
    rw [h0] at hdeg
    simp only [natDegree_zero] at hdeg
    omega
  have hPne : P ≠ 0 := by
    intro h0
    have hunit : IsUnit (X ^ m - C w : F[X]) := by
      have h1 : c * (X ^ m - C w) = 1 := by
        have := sub_eq_zero.mp (hP ▸ h0)
        simpa using this
      exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact h1 : (X ^ m - C w : F[X]) * c = 1)
    have hdeg0 : (X ^ m - C w : F[X]).natDegree = 0 :=
      natDegree_eq_zero_of_isUnit hunit
    rw [natDegree_X_pow_sub_C] at hdeg0
    omega
  have hcard : (D.filter fun x => c.eval x * (x ^ m - w) = 1).card ≤ P.natDegree := by
    have hsub : (D.filter fun x => c.eval x * (x ^ m - w) = 1) ⊆ P.roots.toFinset := by
      intro x hx
      rcases Finset.mem_filter.mp hx with ⟨_, hagree⟩
      rw [Multiset.mem_toFinset, mem_roots hPne]
      simp only [hP, IsRoot, eval_sub, eval_mul, eval_one, eval_pow, eval_X, eval_C]
      rw [sub_eq_zero]
      simpa using hagree
    calc (D.filter fun x => c.eval x * (x ^ m - w) = 1).card
        ≤ P.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := P.card_roots'
  refine hcard.trans ?_
  have hXm : (X ^ m - C w : F[X]).natDegree ≤ m := by
    rw [natDegree_X_pow_sub_C]
  have hdegP : P.natDegree ≤ k - 1 + m := by
    rw [hP]
    refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
    refine natDegree_mul_le.trans ?_
    omega
  omega

omit [DecidableEq F] in
/-- The tail of the vanishing polynomial: `X^|S| − Π_{a∈S}(X − C a)` has degree `≤ |S| − 1`
(the monic leading terms cancel). -/
theorem tail_natDegree_le (S : Finset F) :
    ((X : F[X]) ^ S.card - ∏ a ∈ S, (X - C a)).natDegree ≤ S.card - 1 := by
  classical
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · rw [h0]
    have hS : S = ∅ := Finset.card_eq_zero.mp h0
    simp [hS]
  · have hprod_monic : (∏ a ∈ S, (X - C a) : F[X]).Monic :=
      monic_prod_of_monic _ _ fun a _ => monic_X_sub_C a
    have hprod_deg : (∏ a ∈ S, (X - C a) : F[X]).degree = S.card := by
      rw [degree_prod]
      simp [degree_X_sub_C]
    have hlt : ((X : F[X]) ^ S.card - ∏ a ∈ S, (X - C a)).degree < (S.card : WithBot ℕ) := by
      have := degree_sub_lt (p := (X : F[X]) ^ S.card) (q := ∏ a ∈ S, (X - C a))
        (by rw [degree_X_pow, hprod_deg]) (by exact pow_ne_zero _ X_ne_zero)
        (by rw [leadingCoeff_X_pow, Monic.leadingCoeff hprod_monic])
      rwa [degree_X_pow] at this
    have hle : ((X : F[X]) ^ S.card - ∏ a ∈ S, (X - C a)).natDegree < S.card := by
      rcases eq_or_ne ((X : F[X]) ^ S.card - ∏ a ∈ S, (X - C a)) 0 with hz | hz
      · rw [hz]; simpa using hpos
      · exact natDegree_lt_iff_degree_lt hz |>.mpr hlt
    omega

omit [DecidableEq F] in
/-- **Existence of the deep quotient.** For any polynomial `p` and any `w`,
`X^m − C w` divides `p.comp (X^m) − C (p.eval w)`. -/
theorem quotient_exists (p : F[X]) (w : F) (m : ℕ) :
    ((X : F[X]) ^ m - C w) ∣ (p.comp ((X : F[X]) ^ m) - C (p.eval w)) := by
  obtain ⟨g, hg⟩ : ((X : F[X]) - C w) ∣ (p - C (p.eval w)) := X_sub_C_dvd_sub_C_eval
  refine ⟨g.comp ((X : F[X]) ^ m), ?_⟩
  have := congrArg (fun q : F[X] => q.comp ((X : F[X]) ^ m)) hg
  simpa [sub_comp, mul_comp, X_comp, C_comp] using this

omit [DecidableEq F] in
/-- **Degree of the deep quotient.** If `p.natDegree ≤ r − 1` (`1 ≤ r`, `1 ≤ m`) and
`p.comp (X^m) − C (p.eval w) = (X^m − C w) * q`, then `q.natDegree ≤ (r − 2) * m`.
(For `r = 1` the quotient is the zero polynomial: degree `0 = (1−2)*m` in ℕ-subtraction.) -/
theorem quotient_natDegree_le {p q : F[X]} {w : F} {m r : ℕ}
    (hm : 1 ≤ m) (hr : 1 ≤ r) (hp : p.natDegree ≤ r - 1)
    (hq : p.comp ((X : F[X]) ^ m) - C (p.eval w) = ((X : F[X]) ^ m - C w) * q) :
    q.natDegree ≤ (r - 2) * m := by
  classical
  rcases eq_or_ne q 0 with h0 | h0
  · simp [h0]
  have hXmne : (X ^ m - C w : F[X]) ≠ 0 := by
    intro hz
    have hdeg := natDegree_X_pow_sub_C (n := m) (r := w)
    rw [hz] at hdeg
    simp only [natDegree_zero] at hdeg
    omega
  have hcomp : (p.comp ((X : F[X]) ^ m)).natDegree ≤ (r - 1) * m := by
    refine natDegree_comp_le.trans ?_
    rw [natDegree_X_pow]
    exact Nat.mul_le_mul_right _ hp
  have hlhs : (p.comp ((X : F[X]) ^ m) - C (p.eval w)).natDegree ≤ (r - 1) * m :=
    (natDegree_sub_le _ _).trans (max_le hcomp (by simp))
  have hmul : ((X ^ m - C w : F[X]) * q).natDegree = m + q.natDegree := by
    rw [natDegree_mul hXmne h0, natDegree_X_pow_sub_C]
  have hkey : m + q.natDegree ≤ (r - 1) * m := by
    rw [← hmul, ← hq]
    exact hlhs
  rcases Nat.lt_or_ge r 2 with h2 | h2
  · have hr1 : r = 1 := by omega
    subst hr1
    have hpconst : p.natDegree = 0 := by omega
    have hpc : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hpconst
    have hzero : p.comp ((X : F[X]) ^ m) - C (p.eval w) = 0 := by
      rw [hpc]
      simp
    rw [hzero] at hq
    exact absurd ((mul_eq_zero.mp hq.symm).resolve_left hXmne) h0
  · have hsplit : (r - 1) * m = (r - 2) * m + m := by
      have h : r - 1 = (r - 2) + 1 := by omega
      rw [h, Nat.add_mul, one_mul]
    omega

omit [DecidableEq F] in
/-- **The bad-scalar agreement identity.** With `v_S` the vanishing polynomial of `S`,
`p_S := X^|S| − v_S` its tail, and `q` the deep quotient of `p_S` at `w`: at every point `x`
whose `m`-th power lies in `S`,
`q(x)·(x^m − w) = x^{|S|·m} − p_S(w)`.
So along the line `λ ↦ (x^{|S|·m} + λ)/(x^m − w)`, the scalar `λ = −p_S(w)` agrees with the
*polynomial* `q` on the whole fiber of `S` — the bad-scalar event of the quotient construction. -/
theorem quotient_agree {S : Finset F} {q : F[X]} {w : F} {m : ℕ}
    (hq : ((X : F[X]) ^ S.card - ∏ a ∈ S, (X - C a)).comp ((X : F[X]) ^ m)
        - C ((((X : F[X]) ^ S.card - ∏ a ∈ S, (X - C a))).eval w)
        = ((X : F[X]) ^ m - C w) * q)
    {x : F} (hx : x ^ m ∈ S) :
    q.eval x * (x ^ m - w)
      = x ^ (S.card * m)
        - (((X : F[X]) ^ S.card - ∏ a ∈ S, (X - C a))).eval w := by
  classical
  have hvanish : (∏ a ∈ S, ((X : F[X]) - C a)).eval (x ^ m) = 0 := by
    rw [eval_prod]
    exact Finset.prod_eq_zero hx (by simp)
  have hev := congrArg (fun P : F[X] => P.eval x) hq
  simp only [eval_sub, eval_mul, eval_comp, eval_pow, eval_X, eval_C] at hev
  rw [hvanish, sub_zero] at hev
  simp only [eval_sub, eval_pow, eval_X]
  rw [pow_mul']
  rw [hev]
  ring

end ArkLib.ProximityGap.QuotientCore


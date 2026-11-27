/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AgreementBounds
import ArkLib.Research.ProximityGap.Frontier.ReservedFiberList

/-!
# Generalized Power-Fiber Rigidity for Arbitrary Rates and Higher Erasure Budgets

We generalize `FiveHeadFiberRigidity` in two orthogonal directions:

1. **Arbitrary rate `1/r` and arbitrary 2-fiber-connected hypergraph**
   (`polynomial_eq_of_fiber_two_connected` and `cyclic_words_eq_of_fiber_two_connected`):
   For any `r` power fibers `T₀, …, T_{r-1}` of size `≥ k`, up to `k` total erasures,
   and any `m` Reed–Solomon heads whose fiber-incidence hypergraph stays connected after
   deleting any single fiber `a : Fin r`, all `m` polynomials (and interleaved codewords)
   must coincide.

2. **Higher erasure budgets `|E| ≤ s * k` via base-`X^k` digit expansion and
   degree-`s` fiber polynomial rigidity** (`polynomial_eq_of_higher_erasure_rigidity` and
   `cyclic_words_eq_of_higher_erasure_rigidity`):
   Expanding `L * fᵢ = ∑_{u=0}^{s} X^{uk} B_{i,u}` with `deg B_{i,u} < k`, whenever
   two heads share `s` fibers avoiding `D x ^ k` (`x ∈ E`), the degree-`≤ s` univariate
   polynomial `Q_{i,x}(Y) = ∑_u B_{i,u}(D x) Y^u` agrees with `Q_{h,x}(Y)` on `s + 1`
   distinct points (`D x ^ k` and the `s` fiber labels), forcing `B_{i,u}(D x) = B_{h,u}(D x)`
   for every `u`. Whenever the `s`-shared-fiber graph stays connected after omitting any
   single fiber, all `m` polynomials coincide even under `s * k` total erasures!
-/

set_option autoImplicit false

namespace ProximityGap.GeneralizedFiberRigidity

open Polynomial Finset
open scoped BigOperators

private theorem eq_on_nodes {I F : Type*} [Field F] (D : I ↪ F) (S : Finset I)
    (P Q : F[X]) (hdeg : max P.natDegree Q.natDegree < S.card)
    (hag : ∀ i ∈ S, P.eval (D i) = Q.eval (D i)) : P = Q := by
  apply eq_of_natDegree_lt_card_of_eval_eq P Q
    (D.injective.comp (Subtype.val_injective (p := (· ∈ S))))
  · exact fun i => hag i.val i.property
  · simpa only [Fintype.card_coe] using hdeg

private theorem propagate_eq {m r s : ℕ} (edge : Fin m → Finset (Fin r)) (i0 : Fin m)
    (a : Fin r)
    (hconn : ∀ S : Finset (Fin m), i0 ∈ S →
      (∀ i ∈ S, ∀ j : Fin m, s ≤ ((edge i ∩ edge j).erase a).card → j ∈ S) → S = univ)
    {α : Type*} (v : Fin m → α)
    (hstep : ∀ i j : Fin m, s ≤ ((edge i ∩ edge j).erase a).card → v i = v j) :
    ∀ i : Fin m, v i = v i0 := by
  classical
  let S : Finset (Fin m) := univ.filter fun i => v i = v i0
  have hS0 : i0 ∈ S := mem_filter.mpr ⟨mem_univ _, rfl⟩
  have hclosed : ∀ i ∈ S, ∀ j : Fin m, s ≤ ((edge i ∩ edge j).erase a).card → j ∈ S := by
    intro i hi j hsh
    exact mem_filter.mpr ⟨mem_univ _, (hstep i j hsh).symm.trans (mem_filter.mp hi).2⟩
  have hall : S = univ := hconn S hS0 hclosed
  exact fun i => (mem_filter.mp (hall ▸ mem_univ i : i ∈ S)).2

/-- Theorem A: Arbitrary rate `1/r`, arbitrary head count `m`, up to `k` total erasures.
If deleting any single fiber leaves the shared-fiber graph on heads connected, then any
`m` degree-`< k` polynomials agreeing with a common center `u` on their punctured fiber
unions must all be equal. -/
theorem polynomial_eq_of_fiber_two_connected {I F : Type*} [Field F] (D : I ↪ F)
    {m r k : ℕ} (hr : 0 < r) (hk : 0 < k) (i0 : Fin m)
    (edge : Fin m → Finset (Fin r))
    (hconn : ∀ a : Fin r, ∀ S : Finset (Fin m), i0 ∈ S →
      (∀ i ∈ S, ∀ j : Fin m, 1 ≤ ((edge i ∩ edge j).erase a).card → j ∈ S) → S = univ)
    (z : Fin r ↪ F) (T : Fin r → Finset I) (sizes : ∀ j, k ≤ (T j).card)
    (powers : ∀ j x, x ∈ T j → D x ^ k = z j)
    (E : Finset I) (erase : E.card ≤ k) (f : Fin m → F[X]) (deg : ∀ i, (f i).natDegree < k)
    (u : I → F) (agree : ∀ i j, j ∈ edge i → ∀ x ∈ T j, x ∉ E → (f i).eval (D x) = u x) :
    ∀ i, f i = f i0 := by
  classical
  let L := Lagrange.nodal E D
  let A (i : Fin m) := (L * f i) %ₘ (X ^ k)
  let B (i : Fin m) := (L * f i) /ₘ (X ^ k)
  have split (i : Fin m) : A i + X ^ k * B i = L * f i := modByMonic_add_div _ _
  have xne : (X ^ k : F[X]) ≠ 1 := by
    intro h
    have bad := congrArg natDegree h
    simp only [natDegree_X_pow, natDegree_one] at bad
    omega
  have smallA (i : Fin m) : (A i).natDegree < k := by
    simpa only [A, natDegree_X_pow] using natDegree_modByMonic_lt (L * f i) (monic_X_pow k) xne
  have degreeL : L.natDegree = E.card := Lagrange.natDegree_nodal
  have smallB (i : Fin m) (he : 0 < E.card) : (B i).natDegree < E.card := by
    change ((L * f i) /ₘ (X ^ k)).natDegree < E.card
    rw [natDegree_divByMonic _ (monic_X_pow k), natDegree_X_pow]
    have bound := natDegree_mul_le (p := L) (q := f i)
    rw [degreeL] at bound
    have := deg i
    omega
  have emptyB (i : Fin m) (he : E = ∅) : B i = 0 := by
    apply (divByMonic_eq_zero_iff (monic_X_pow k)).mpr
    simp only [L, he, Lagrange.nodal, prod_empty, one_mul, degree_X_pow]
    exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr (deg i))
  have boundB (i : Fin m) : (B i).natDegree < k := by
    rcases E.eq_empty_or_nonempty with he | he
    · simpa only [emptyB i he, natDegree_zero] using hk
    · exact (smallB i he.card_pos).trans_le erase
  let G (i : Fin m) (j : Fin r) := A i + C (z j) * B i
  have dg (i : Fin m) (j : Fin r) : (G i j).natDegree < k :=
    (natDegree_add_le ..).trans_lt (max_lt (smallA i) ((natDegree_C_mul_le ..).trans_lt (boundB i)))
  have specialize (i : Fin m) (j : Fin r) (x : I) (hx : x ∈ T j) :
      (G i j).eval (D x) = (L * f i).eval (D x) := by
    rw [← split i]
    simp [G, powers j x hx]
  have shared (i h : Fin m) (j : Fin r) (hi : j ∈ edge i) (hh : j ∈ edge h) :
      G i j = G h j := by
    apply eq_on_nodes D (T j) _ _ ((max_lt (dg i j) (dg h j)).trans_le (sizes j))
    intro x hx
    rw [specialize i j x hx, specialize h j x hx, eval_mul, eval_mul]
    by_cases he : x ∈ E
    · have zero : L.eval (D x) = 0 := Lagrange.eval_nodal_at_node (v := D) he
      simp [zero]
    · rw [agree i j hi x hx he, agree h j hh x hx he]
  have Bnodes (x : I) (hx : x ∈ E) : ∀ i, (B i).eval (D x) = (B i0).eval (D x) := by
    obtain ⟨a, avoid⟩ : ∃ a : Fin r, ∀ j ≠ a, z j ≠ D x ^ k := by
      by_cases hit : ∃ j, z j = D x ^ k
      · obtain ⟨a, ha⟩ := hit
        exact ⟨a, fun j h eq => h (z.injective (eq.trans ha.symm))⟩
      · exact ⟨⟨0, hr⟩, fun j _ eq => hit ⟨j, eq⟩⟩
    have zero (i : Fin m) : (A i).eval (D x) + D x ^ k * (B i).eval (D x) = 0 := by
      have fact := congrArg (eval (D x)) (split i)
      simpa only [eval_add, eval_mul, eval_pow, eval_X, Lagrange.eval_nodal_at_node (v := D) hx,
        L, zero_mul] using fact
    apply propagate_eq edge i0 a (hconn a)
    intro i h hsh
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < ((edge i ∩ edge h).erase a).card)
    have hja : j ≠ a := (mem_erase.mp hj).1
    have hij : j ∈ edge i := (mem_inter.mp (mem_erase.mp hj).2).1
    have hhj : j ∈ edge h := (mem_inter.mp (mem_erase.mp hj).2).2
    have eqn := congrArg (eval (D x)) (shared i h j hij hhj)
    simp only [G, eval_add, eval_mul, eval_C] at eqn
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr (avoid j hja))
    linear_combination eqn - zero i + zero h
  have Beq (i : Fin m) : B i = B i0 := by
    rcases E.eq_empty_or_nonempty with he | he
    · rw [emptyB i he, emptyB i0 he]
    · exact eq_on_nodes D E _ _ (max_lt (smallB i he.card_pos) (smallB i0 he.card_pos))
        (fun x hx => Bnodes x hx i)
  have Aeq : ∀ i, A i = A i0 := by
    apply propagate_eq edge i0 ⟨0, hr⟩ (hconn ⟨0, hr⟩)
    intro i h hsh
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < ((edge i ∩ edge h).erase ⟨0, hr⟩).card)
    have hij : j ∈ edge i := (mem_inter.mp (mem_erase.mp hj).2).1
    have hhj : j ∈ edge h := (mem_inter.mp (mem_erase.mp hj).2).2
    have eqn := shared i h j hij hhj
    simpa only [G, Beq i, Beq h, add_left_inj] using eqn
  intro i
  apply mul_left_cancel₀ (Lagrange.nodal_ne_zero (s := E) (v := D))
  rw [← split i, ← split i0, Aeq i, Beq i]

/-- The `u`-th base-`X^k` digit of a polynomial `P`, collecting degrees `u*k + j` for `0 ≤ j < k`. -/
private noncomputable def powDigit {F : Type*} [Field F] (k : ℕ) (P : F[X]) (u : ℕ) : F[X] :=
  ∑ j ∈ Finset.range k, C (P.coeff (u * k + j)) * X ^ j

private theorem natDegree_powDigit_lt {F : Type*} [Field F] {k : ℕ} (hk : 0 < k)
    (P : F[X]) (u : ℕ) : (powDigit k P u).natDegree < k := by
  refine (natDegree_sum_le _ _).trans_lt ?_
  rw [Finset.fold_max_lt]
  refine ⟨hk, fun j hj => ?_⟩
  have hjk : j < k := mem_range.mp hj
  exact (natDegree_C_mul_le _ _).trans_lt (by simpa [natDegree_X_pow] using hjk)

/-- Base-`X^k` digit expansion of a polynomial `P` of degree `< (s + 1) * k`. -/
private theorem base_pow_expansion {F : Type*} [Field F] {k : ℕ} (hk : 0 < k)
    (s : ℕ) (P : F[X]) (hdeg : P.natDegree < (s + 1) * k) :
    ∑ u : Fin (s + 1), X ^ (u.val * k) * powDigit k P u.val = P := by
  ext n
  rw [finsetSum_coeff]
  have hterm (u : Fin (s + 1)) :
      (X ^ (u.val * k) * powDigit k P u.val).coeff n =
        if n / k = u.val then P.coeff n else 0 := by
    simp only [powDigit, Finset.mul_sum, finsetSum_coeff]
    have hinner (j : ℕ) :
        (X ^ (u.val * k) * (C (P.coeff (u.val * k + j)) * X ^ j)).coeff n =
          if u.val * k + j = n then P.coeff n else 0 := by
      rw [mul_left_comm, ← pow_add, coeff_C_mul, coeff_X_pow]
      by_cases h : u.val * k + j = n
      · subst h; simp
      · simp only [h, Ne.symm h, ite_false, mul_zero]
    simp_rw [hinner]
    by_cases hq : n / k = u.val
    · simp only [hq, ite_true]
      rw [Finset.sum_eq_single (n % k)]
      · have hdiv : u.val * k + n % k = n := by rw [← hq, mul_comm]; exact Nat.div_add_mod n k
        simp [hdiv]
      · intro j hj hjne
        have hjk : j < k := mem_range.mp hj
        have hne : u.val * k + j ≠ n := by
          intro heq
          have : n % k = j := by
            rw [← heq, Nat.mul_add_mod_self_right]
            exact Nat.mod_eq_of_lt hjk
          exact hjne this.symm
        simp [hne]
      · intro hnot
        exact False.elim (hnot (mem_range.mpr (Nat.mod_lt n hk)))
    · simp only [hq, ite_false]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hjk : j < k := mem_range.mp hj
      have hne : u.val * k + j ≠ n := by
        intro heq
        have : n / k = u.val := by
          rw [← heq, mul_comm u.val k, Nat.mul_add_div hk, Nat.div_eq_of_lt hjk, add_zero]
        exact hq this
      simp [hne]
  simp_rw [hterm]
  by_cases hn : n < (s + 1) * k
  · have hdiv_lt : n / k < s + 1 := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
    rw [Finset.sum_eq_single ⟨n / k, hdiv_lt⟩]
    · simp
    · intro u _ hne
      have : n / k ≠ u.val := fun h => hne (Fin.ext h.symm)
      simp [this]
    · intro hnot; exact False.elim (hnot (mem_univ _))
  · have hzero : P.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg (not_lt.mp hn))
    rw [hzero]
    refine Finset.sum_eq_zero fun u _ => ?_
    have hne : n / k ≠ u.val := by
      have hge : s + 1 ≤ n / k := by
        rw [Nat.le_div_iff_mul_le hk]
        exact not_lt.mp hn
      omega
    simp [hne]

/-- Theorem B: Higher erasure budget `|E| ≤ s * k` (`s ≥ 1`).
Whenever omitting any single fiber leaves the `s`-shared-fiber graph on the `m` heads
connected, all `m` degree-`< k` polynomials agreeing with a common center `u` on their
punctured fiber unions must coincide! -/
theorem polynomial_eq_of_higher_erasure_rigidity {I F : Type*} [Field F] (D : I ↪ F)
    {m r k s : ℕ} (hr : 0 < r) (hk : 0 < k) (hs : 1 ≤ s) (i0 : Fin m)
    (edge : Fin m → Finset (Fin r))
    (hconn : ∀ a : Fin r, ∀ S : Finset (Fin m), i0 ∈ S →
      (∀ i ∈ S, ∀ j : Fin m, s ≤ ((edge i ∩ edge j).erase a).card → j ∈ S) → S = univ)
    (z : Fin r ↪ F) (T : Fin r → Finset I) (sizes : ∀ j, k ≤ (T j).card)
    (powers : ∀ j x, x ∈ T j → D x ^ k = z j)
    (E : Finset I) (erase : E.card ≤ s * k) (f : Fin m → F[X]) (deg : ∀ i, (f i).natDegree < k)
    (u : I → F) (agree : ∀ i j, j ∈ edge i → ∀ x ∈ T j, x ∉ E → (f i).eval (D x) = u x) :
    ∀ i, f i = f i0 := by
  classical
  by_cases hsmall : E.card ≤ k
  · -- When `|E| ≤ k`, `s`-shared-fiber connectivity implies 1-shared-fiber connectivity,
    -- reducing directly to Theorem A.
    refine polynomial_eq_of_fiber_two_connected D hr hk i0 edge ?_ z T sizes powers E hsmall f deg u agree
    intro a S hS0 hclosed
    exact hconn a S hS0 fun i hi j hsh => hclosed i hi j (hs.trans hsh)
  · -- Main regime: `k < E.card ≤ s * k`.
    have hEge : k ≤ E.card := by omega
    let L := Lagrange.nodal E D
    have degreeL : L.natDegree = E.card := Lagrange.natDegree_nodal
    let B (i : Fin m) (u : Fin (s + 1)) : F[X] := powDigit k (L * f i) u.val
    have smallB (i : Fin m) (u : Fin (s + 1)) : (B i u).natDegree < k :=
      natDegree_powDigit_lt hk (L * f i) u.val
    have hLf_deg (i : Fin m) : (L * f i).natDegree < (s + 1) * k := by
      have bound := natDegree_mul_le (p := L) (q := f i)
      rw [degreeL] at bound
      have := deg i
      nlinarith
    have split (i : Fin m) :
        ∑ u : Fin (s + 1), X ^ (u.val * k) * B i u = L * f i :=
      base_pow_expansion hk s (L * f i) (hLf_deg i)
    let G (i : Fin m) (j : Fin r) : F[X] :=
      ∑ u : Fin (s + 1), C (z j ^ u.val) * B i u
    have dg (i : Fin m) (j : Fin r) : (G i j).natDegree < k := by
      refine (natDegree_sum_le _ _).trans_lt ?_
      rw [Finset.fold_max_lt]
      refine ⟨hk, fun u _ => ?_⟩
      exact (natDegree_C_mul_le _ _).trans_lt (smallB i u)
    have specialize (i : Fin m) (j : Fin r) (x : I) (hx : x ∈ T j) :
        (G i j).eval (D x) = (L * f i).eval (D x) := by
      rw [← split i]
      simp only [G, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [mul_comm u.val k, pow_mul, powers j x hx]
    have shared (i h : Fin m) (j : Fin r) (hi : j ∈ edge i) (hh : j ∈ edge h) :
        G i j = G h j := by
      apply eq_on_nodes D (T j) _ _ ((max_lt (dg i j) (dg h j)).trans_le (sizes j))
      intro x hx
      rw [specialize i j x hx, specialize h j x hx, eval_mul, eval_mul]
      by_cases he : x ∈ E
      · have zero : L.eval (D x) = 0 := Lagrange.eval_nodal_at_node (v := D) he
        simp [zero]
      · rw [agree i j hi x hx he, agree h j hh x hx he]
    -- Fix `x ∈ E`. Associate to each head `i` the degree-`≤ s` polynomial
    -- `Q i x (Y) = ∑ u, B_{i, u}(D x) * Y^u`.
    let Q (i : Fin m) (x : I) : F[X] :=
      ∑ u : Fin (s + 1), C ((B i u).eval (D x)) * X ^ u.val
    have hQdeg (i : Fin m) (x : I) : (Q i x).natDegree ≤ s := by
      refine (natDegree_sum_le _ _).trans ?_
      rw [Finset.fold_max_le]
      refine ⟨Nat.zero_le s, fun u _ => ?_⟩
      calc
        (C ((B i u).eval (D x)) * X ^ u.val).natDegree
          ≤ (X ^ u.val : F[X]).natDegree := natDegree_C_mul_le _ _
        _ = u.val := natDegree_X_pow u.val
        _ ≤ s := Nat.le_of_lt_succ u.isLt
    have hQeval_zero (i : Fin m) (x : I) (hx : x ∈ E) : (Q i x).eval (D x ^ k) = 0 := by
      have h1 : (Q i x).eval (D x ^ k) = (L * f i).eval (D x) := by
        rw [← split i]
        simp only [Q, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [← pow_mul, mul_comm k u.val, mul_comm]
      rw [h1, eval_mul, Lagrange.eval_nodal_at_node (v := D) hx, zero_mul]
    have hQeval_fiber (i : Fin m) (x : I) (j : Fin r) :
        (Q i x).eval (z j) = (G i j).eval (D x) := by
      simp only [Q, G, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
      refine Finset.sum_congr rfl fun u _ => mul_comm _ _
    have Qeq (x : I) (hx : x ∈ E) : ∀ i, Q i x = Q i0 x := by
      obtain ⟨a, avoid⟩ : ∃ a : Fin r, ∀ j ≠ a, z j ≠ D x ^ k := by
        by_cases hit : ∃ j, z j = D x ^ k
        · obtain ⟨a, ha⟩ := hit
          exact ⟨a, fun j h eq => h (z.injective (eq.trans ha.symm))⟩
        · exact ⟨⟨0, hr⟩, fun j _ eq => hit ⟨j, eq⟩⟩
      apply propagate_eq edge i0 a (hconn a)
      intro i h hsh
      let J := (edge i ∩ edge h).erase a
      let pts : Finset F := insert (D x ^ k) (J.image z)
      have hnotin : D x ^ k ∉ J.image z := by
        intro hmem
        rcases mem_image.mp hmem with ⟨j, hj, hjz⟩
        exact avoid j (mem_erase.mp hj).1 hjz
      have hptscard : s + 1 ≤ pts.card := by
        rw [card_insert_of_notMem hnotin, card_image_of_injective _ z.injective]
        exact Nat.succ_le_succ hsh
      apply eq_of_natDegree_lt_card_of_eval_eq (Q i x) (Q h x)
        (Subtype.val_injective (p := (· ∈ pts)))
      · intro ⟨y, hy⟩
        rcases mem_insert.mp hy with rfl | hyJ
        · rw [hQeval_zero i x hx, hQeval_zero h x hx]
        · rcases mem_image.mp hyJ with ⟨j, hj, rfl⟩
          have hij : j ∈ edge i := (mem_inter.mp (mem_erase.mp hj).2).1
          have hhj : j ∈ edge h := (mem_inter.mp (mem_erase.mp hj).2).2
          rw [hQeval_fiber i x j, hQeval_fiber h x j, shared i h j hij hhj]
      · simp only [Fintype.card_coe]
        exact (max_le (hQdeg i x) (hQdeg h x)).trans_lt (Nat.lt_of_succ_le hptscard)
    -- Extract equality of every digit `B i u` at every `x ∈ E`, hence globally since `deg B i u < k ≤ |E|`.
    have Beq (i : Fin m) (u : Fin (s + 1)) : B i u = B i0 u := by
      apply eq_on_nodes D E _ _ ((max_lt (smallB i u) (smallB i0 u)).trans_le hEge)
      intro x hx
      have hcoeff := congrArg (fun P : F[X] => P.coeff u.val) (Qeq x hx i)
      have hQcoeff (a : Fin m) : (Q a x).coeff u.val = (B a u).eval (D x) := by
        simp only [Q, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
        rw [Finset.sum_eq_single u]
        · simp
        · intro v _ hvu
          have : u.val ≠ v.val := fun h => hvu (Fin.ext h.symm)
          simp [this]
        · intro hu; exact False.elim (hu (mem_univ u))
      rw [hQcoeff i, hQcoeff i0] at hcoeff
      exact hcoeff
    intro i
    apply mul_left_cancel₀ (Lagrange.nodal_ne_zero (s := E) (v := D))
    rw [← split i, ← split i0]
    exact Finset.sum_congr rfl fun u _ => by rw [Beq i u]

/-- Cyclic-domain interleaved codeword corollary of Theorem B (`|E| ≤ s * k`),
valid for all rates `1/r`, all fields `F`, and arbitrary interleaving width `κ`. -/
theorem cyclic_words_eq_of_higher_erasure_rigidity {F κ : Type*} [Field F]
    {m r k s : ℕ} (hr : 0 < r) (hk : 0 < k) (hs : 1 ≤ s) (i0 : Fin m)
    (edge : Fin m → Finset (Fin r))
    (hconn : ∀ a : Fin r, ∀ S : Finset (Fin m), i0 ∈ S →
      (∀ i ∈ S, ∀ j : Fin m, s ≤ ((edge i ∩ edge j).erase a).card → j ∈ S) → S = univ)
    (g : Fˣ) (hg : orderOf g = k * r)
    (holes : Fin m → Finset (Fin r × Fin k))
    (htrim : (univ.biUnion holes).card ≤ s * k)
    (w : Fin m → Matrix (Fin r × Fin k) κ F)
    (words : ∀ i, w i ∈ Code.interleavedCodeSet (κ := κ)
      (ReedSolomon.code (ReservedFiberList.cyclicDomain g hg) k : Set ((Fin r × Fin k) → F)))
    (u : (Fin r × Fin k) → κ → F)
    (agree : ∀ i x, x.1 ∈ edge i → x ∉ holes i → w i x = u x) :
    ∀ i, w i = w i0 := by
  classical
  let : NeZero k := ⟨by omega⟩
  let D := ReservedFiberList.cyclicDomain g hg
  let T (j : Fin r) : Finset (Fin r × Fin k) := {j} ×ˢ univ
  let E := univ.biUnion holes
  have power (j : Fin r) (x : Fin r × Fin k) (hx : x ∈ T j) :
      D x ^ k = ReservedFiberList.cyclicLabels hk g hg j := by
    have first : x.1 = j := mem_singleton.mp (mem_product.mp hx).1
    simpa only [D, Fintype.card_fin, first] using ReservedFiberList.cyclicDomain_pow hk g hg x
  intro i
  funext x b
  have row (a : Fin m) := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp (words a b)
  choose f deg eval using row
  have all := polynomial_eq_of_higher_erasure_rigidity D hr hk hs i0 edge hconn
    (ReservedFiberList.cyclicLabels hk g hg) T (fun j => by simp [T]) power E htrim f deg
    (fun x => u x b) (by
      intro a j hj y hy outside
      have first : y.1 = j := mem_singleton.mp (mem_product.mp hy).1
      have keep : y ∉ holes a := fun hit => outside (mem_biUnion.mpr ⟨a, mem_univ _, hit⟩)
      exact (eval a y).trans (congrFun (agree a y (first ▸ hj) keep) b))
  calc w i x b = (f i).eval (D x) := (eval i x).symm
    _ = (f i0).eval (D x) := congrArg (Polynomial.eval (D x)) (all i)
    _ = w i0 x b := eval i0 x

end ProximityGap.GeneralizedFiberRigidity

#print axioms ProximityGap.GeneralizedFiberRigidity.polynomial_eq_of_fiber_two_connected
#print axioms ProximityGap.GeneralizedFiberRigidity.polynomial_eq_of_higher_erasure_rigidity
#print axioms ProximityGap.GeneralizedFiberRigidity.cyclic_words_eq_of_higher_erasure_rigidity

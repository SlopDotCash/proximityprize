/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

/-!
# Issue #232 — the sharp rank threshold for error-locator normal spaces (2026/858 Thm 26 + Rem 27)

The second-moment/Poisson-dispersion machinery of ePrint 2026/858 §7.2 (their
Theorem 26 / Corollary 28) rests on one algebraic dichotomy for the `2c` error-locator
normals `{Λ_{E₁}·X^r, Λ_{E₂}·X^r : r < c}` of two weight-`w` supports with intersection
size `j = |E₁ ∩ E₂|`:

* `j ≤ w − c` ⟹ the `2c` normals are **linearly independent** (their Theorem 26), giving
  exact pairwise independence of the membership indicators and `Var[M] ≈ E[M]`;
* `j > w − c` ⟹ the rank drops by exactly `ℓ = j − (w − c)` (their Remark 27) — shared
  cores produce genuine linear relations.

In polynomial language the span of the `2c` normals is
`{Λ_{E₁}·P + Λ_{E₂}·Q : deg P, deg Q < c}`, so the dichotomy is a *kernel* statement,
machine-checked here over any field:

* `normal_kernel_trivial` (= Theorem 26): if `c + j ≤ w₁` then
  `Λ_{E₁}·P + Λ_{E₂}·Q = 0` with `deg P, deg Q < c` forces `P = Q = 0`.
  The proof is *simpler than the paper's*: no gcd factoring — `A₁ = Λ_{E₁∖E₂}` divides
  `Λ_{E₁}·P = −Λ_{E₂}·Q` and is coprime to `Λ_{E₂}` outright (disjoint root sets), so
  `A₁ ∣ Q`, and `deg A₁ = w₁ − j ≥ c > deg Q` kills `Q`.
* `normal_kernel_nontrivial` (= Remark 27, sharpness): if `j > wᵢ − c` on both sides,
  the explicit relation `Λ_{E₁}·(−Λ_{E₂∖E₁}) + Λ_{E₂}·(Λ_{E₁∖E₂}) = 0` lives in the
  degree-`< c` window and is nontrivial — both products equal `Λ_{E₁ ∪ E₂}`.

**Why this matters for the open core:** their Conjecture 41 (the c ≥ 3 rank lemma,
≈ the prize's Grand List Challenge) is exactly a quantitative strengthening of this
mechanism — bounding how many supports can *simultaneously* be rank-deficient against a
fixed syndrome flat. The threshold formalized here is where the deficiency mechanism
turns on; any proof of Conjecture 41 must control precisely these shared-core relations.
-/

namespace NormalRank

open Polynomial Finset

variable {F : Type*} [Field F]

/-- The error-locator polynomial of a support `E ⊆ F` (also in `C2CoreBound.loc`;
duplicated here to keep this brick self-contained and Mathlib-only). -/
noncomputable def loc (E : Finset F) : F[X] := ∏ a ∈ E, (X - C a)

lemma loc_ne_zero (E : Finset F) : loc E ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun a _ => X_sub_C_ne_zero a

lemma loc_natDegree (E : Finset F) : (loc E).natDegree = E.card := by
  rw [loc, Polynomial.natDegree_prod _ _ fun a _ => X_sub_C_ne_zero a]
  simp

/-- Locators of disjoint supports are coprime (disjoint root sets). -/
lemma loc_isCoprime {S T : Finset F} (h : Disjoint S T) : IsCoprime (loc S) (loc T) := by
  rw [loc, loc]
  refine IsCoprime.prod_left fun a ha => IsCoprime.prod_right fun b hb => ?_
  have hab : a ≠ b := by
    intro hEq
    exact Finset.disjoint_left.mp h ha (hEq ▸ hb)
  exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hab).isUnit

/-- The locator factors through any sub-support split: `Λ_E = Λ_{E∖T} · Λ_{E∩T}`. -/
lemma loc_sdiff_mul_loc_inter [DecidableEq F] (E T : Finset F) :
    loc (E \ T) * loc (E ∩ T) = loc E := by
  rw [loc, loc, loc, ← Finset.prod_union (Finset.disjoint_sdiff_inter E T)]
  congr 1
  exact Finset.sdiff_union_inter E T

/-- **The trivial-kernel half of the sharp threshold** (2026/858 Theorem 26, kernel
form): if `c + |E₁ ∩ E₂| ≤ |E₁|`, then any degree-`< c` relation
`Λ_{E₁}·P + Λ_{E₂}·Q = 0` is trivial (no degree bound on `P` is even needed) — the `2c` error-locator normals are linearly
independent, giving the exact pairwise independence behind Poisson dispersion at every
codimension excess.

Proof (simpler than the paper's gcd route): `A₁ = Λ_{E₁∖E₂}` divides the left summand
and is coprime to `Λ_{E₂}` outright, so `A₁ ∣ Q`; but `deg A₁ = |E₁| − j ≥ c > deg Q`. -/
theorem normal_kernel_trivial [DecidableEq F] {E₁ E₂ : Finset F} {c : ℕ}
    (hth : c + (E₁ ∩ E₂).card ≤ E₁.card)
    {P Q : F[X]} (hQ : Q.natDegree < c)
    (hrel : loc E₁ * P + loc E₂ * Q = 0) :
    P = 0 ∧ Q = 0 := by
  have hQ0 : Q = 0 := by
    by_contra hQne
    -- A₁ := Λ_{E₁ \ E₂} divides Λ_{E₂} * Q
    have hdvd : loc (E₁ \ E₂) ∣ loc E₂ * Q := by
      have h1 : loc (E₁ \ E₂) ∣ loc E₁ * P :=
        Dvd.dvd.mul_right ⟨loc (E₁ ∩ E₂), (loc_sdiff_mul_loc_inter E₁ E₂).symm⟩ P
      have h2 : loc E₂ * Q = -(loc E₁ * P) := by linear_combination hrel
      rw [h2]
      exact h1.neg_right
    -- coprime to Λ_{E₂} (disjoint root sets), hence divides Q
    have hco : IsCoprime (loc (E₁ \ E₂)) (loc E₂) :=
      loc_isCoprime Finset.sdiff_disjoint
    have hdvdQ : loc (E₁ \ E₂) ∣ Q := hco.dvd_of_dvd_mul_left hdvd
    -- degree contradiction
    have hdeg := Polynomial.natDegree_le_of_dvd hdvdQ hQne
    rw [loc_natDegree] at hdeg
    have hcard : (E₁ \ E₂).card + (E₁ ∩ E₂).card = E₁.card :=
      Finset.card_sdiff_add_card_inter E₁ E₂
    omega
  refine ⟨?_, hQ0⟩
  rw [hQ0, mul_zero, add_zero, mul_eq_zero] at hrel
  exact hrel.resolve_left (loc_ne_zero E₁)

/-- **The sharpness half** (2026/858 Remark 27): past the threshold on both sides
(`|Eᵢ| < c + j`), the shared core produces an explicit nontrivial degree-`< c` relation:
`Λ_{E₁}·(−Λ_{E₂∖E₁}) + Λ_{E₂}·Λ_{E₁∖E₂} = 0` (both products are `Λ_{E₁ ∪ E₂}`).
The error-locator normal family genuinely drops rank — the deficiency mechanism that
Conjecture 41 (the open prize core) must control. -/
theorem normal_kernel_nontrivial [DecidableEq F] {E₁ E₂ : Finset F} {c : ℕ}
    (h₁ : E₁.card < c + (E₁ ∩ E₂).card) (h₂ : E₂.card < c + (E₁ ∩ E₂).card) :
    ∃ P Q : F[X], Q ≠ 0 ∧ P.natDegree < c ∧ Q.natDegree < c ∧
      loc E₁ * P + loc E₂ * Q = 0 := by
  refine ⟨-loc (E₂ \ E₁), loc (E₁ \ E₂), loc_ne_zero _, ?_, ?_, ?_⟩
  · rw [natDegree_neg, loc_natDegree]
    have := Finset.card_sdiff_add_card_inter E₂ E₁
    rw [Finset.inter_comm] at this
    omega
  · rw [loc_natDegree]
    have := Finset.card_sdiff_add_card_inter E₁ E₂
    omega
  · -- both cross-products equal Λ_{E₁ ∪ E₂}
    have key : loc E₁ * loc (E₂ \ E₁) = loc E₂ * loc (E₁ \ E₂) := by
      rw [loc, loc, loc, loc, ← Finset.prod_union Finset.disjoint_sdiff,
        ← Finset.prod_union Finset.disjoint_sdiff,
        Finset.union_sdiff_self_eq_union, Finset.union_sdiff_self_eq_union,
        Finset.union_comm]
    linear_combination -key

/-! ## The triple case of Conjecture 41: deficient triples are sunflowers

The open prize core (2026/858 Conjecture 41) is a *quantitative* rank statement at
`c ≥ 3` for many supports at once. The paper's evidence beyond pairs is empirical
("rank-deficient triples exist at c = 2 from n = 11; none found at c ≥ 3"; "k-wise
independence fails for common-core triples"). This section turns the k-wise landscape
into theorems:

* `common_core_triple_relation` — the empirical k-wise failure is a THEOREM: any three
  supports sharing a `(w−1)`-core admit an explicit relation with all three multipliers
  nonzero *constants* (so it lives in every window `c ≥ 1`).
* `triple_relation_vanishing` + `triple_kernel_trivial_of_spread` — **deficient triples
  are sunflowers**: in any nontrivial triple relation, `P_i` vanishes on
  `(E_j ∩ E_k) ∖ E_i`; hence if one pair is at the pairwise threshold and its private
  intersection `(E_j ∩ E_k) ∖ E_i` has `≥ c` points, the triple kernel is trivial.
  Contrapositive: a rank-deficient triple must concentrate every pairwise intersection
  to within `< c` of the triple core — the sunflower structure observed empirically at
  `c = 2` (translate families) is *forced*.
* `relation_core_reduction` — sunflower relations descend to the core-free family:
  Conjecture 41's triple case reduces to core-reduced supports.
-/

section Triple

lemma loc_eval_zero {E : Finset F} {x : F} (hx : x ∈ E) : (loc E).eval x = 0 := by
  rw [loc, eval_prod]
  exact Finset.prod_eq_zero hx (by simp)

lemma loc_eval_ne_zero {E : Finset F} {x : F} (hx : x ∉ E) : (loc E).eval x ≠ 0 := by
  rw [loc, eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun a ha => ?_
  simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
  exact fun hEq => hx (hEq ▸ ha)

variable [DecidableEq F]

/-- **The k-wise failure is a theorem** (any window `c ≥ 1`): three supports sharing a
common core admit an explicit relation with *constant* multipliers
`(x₂−x₃, x₃−x₁, x₁−x₂)` — all nonzero when the extension points are distinct. The
`2c`-pairwise independence of `normal_kernel_trivial` can never be promoted to 3-wise
without structural hypotheses. -/
theorem common_core_triple_relation (Cs : Finset F) {x₁ x₂ x₃ : F}
    (h₁ : x₁ ∉ Cs) (h₂ : x₂ ∉ Cs) (h₃ : x₃ ∉ Cs) :
    loc (insert x₁ Cs) * C (x₂ - x₃) + loc (insert x₂ Cs) * C (x₃ - x₁)
      + loc (insert x₃ Cs) * C (x₁ - x₂) = 0 := by
  rw [loc, loc, loc, Finset.prod_insert h₁, Finset.prod_insert h₂, Finset.prod_insert h₃]
  push_cast [C_sub]
  ring

omit [DecidableEq F] in
/-- **Sunflower vanishing**: in any triple relation, the multiplier of `E₁` vanishes on
the private pairwise intersection `(E₂ ∩ E₃) ∖ E₁`. -/
theorem triple_relation_vanishing {E₁ E₂ E₃ : Finset F} {P₁ P₂ P₃ : F[X]}
    (hrel : loc E₁ * P₁ + loc E₂ * P₂ + loc E₃ * P₃ = 0)
    {x : F} (hx₂ : x ∈ E₂) (hx₃ : x ∈ E₃) (hx₁ : x ∉ E₁) :
    P₁.eval x = 0 := by
  have h := congrArg (Polynomial.eval x) hrel
  simp only [eval_add, eval_mul, eval_zero] at h
  rw [loc_eval_zero hx₂, loc_eval_zero hx₃, zero_mul, zero_mul, add_zero, add_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (loc_eval_ne_zero hx₁)

/-- **Spread triples have trivial kernel — deficient triples are sunflowers.** If the
pair `(E₂, E₃)` is at the pairwise-independence threshold and its private intersection
`(E₂ ∩ E₃) ∖ E₁` carries at least `c` points, then the triple kernel is trivial.

Contrapositive (the structure theorem for Conjecture 41's triple case): any
rank-deficient triple must have `|(E_j ∩ E_k) ∖ E_i| < c` — the pairwise intersections
concentrate into the triple core, i.e. the family is sunflower-like. This is the
mechanism behind the paper's empirical c = 2 translate-family examples, now forced. -/
theorem triple_kernel_trivial_of_spread {E₁ E₂ E₃ : Finset F} {c : ℕ}
    (hth : c + (E₂ ∩ E₃).card ≤ E₂.card)
    (hbig : c ≤ ((E₂ ∩ E₃) \ E₁).card)
    {P₁ P₂ P₃ : F[X]} (h₁ : P₁.natDegree < c) (h₃ : P₃.natDegree < c)
    (hrel : loc E₁ * P₁ + loc E₂ * P₂ + loc E₃ * P₃ = 0) :
    P₁ = 0 ∧ P₂ = 0 ∧ P₃ = 0 := by
  have hP₁ : P₁ = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P₁ ((E₂ ∩ E₃) \ E₁)
    · intro x hx
      rw [Finset.mem_sdiff, Finset.mem_inter] at hx
      exact triple_relation_vanishing hrel hx.1.1 hx.1.2 hx.2
    · omega
  rw [hP₁, mul_zero, zero_add] at hrel
  obtain ⟨hP₂, hP₃⟩ := normal_kernel_trivial hth h₃ hrel
  exact ⟨hP₁, hP₂, hP₃⟩

/-- **Core reduction**: relations of a family with common core `T` are exactly the
relations of the core-free family — Conjecture 41's triple case reduces to core-reduced
supports. -/
theorem relation_core_reduction {T E₁ E₂ E₃ : Finset F}
    (h₁ : T ⊆ E₁) (h₂ : T ⊆ E₂) (h₃ : T ⊆ E₃) (P₁ P₂ P₃ : F[X]) :
    loc E₁ * P₁ + loc E₂ * P₂ + loc E₃ * P₃ = 0 ↔
      loc (E₁ \ T) * P₁ + loc (E₂ \ T) * P₂ + loc (E₃ \ T) * P₃ = 0 := by
  have hf : ∀ E : Finset F, T ⊆ E → loc E = loc T * loc (E \ T) := by
    intro E hTE
    rw [loc, loc, loc, ← Finset.prod_union Finset.disjoint_sdiff]
    congr 1
    exact (Finset.union_sdiff_of_subset hTE).symm
  rw [hf E₁ h₁, hf E₂ h₂, hf E₃ h₃]
  constructor
  · intro h
    have hT : loc T *
        (loc (E₁ \ T) * P₁ + loc (E₂ \ T) * P₂ + loc (E₃ \ T) * P₃) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp hT).resolve_left (loc_ne_zero T)
  · intro h
    linear_combination loc T * h

end Triple

/-! ## The cyclic (equal-symmetric-functions / PTE) deficiency mechanism

The probe suggested by `triple_kernel_trivial_of_spread` (search the core-reduced zone)
finds, empirically, that in the square case `w = 2c` the only deficiencies among spread
triples with a COMMON point are the trivial evaluation-syndrome collapses — but triples
with equal elementary symmetric functions `e₁, …, e_{w−c}` (Prouhet–Tarry–Escott style)
are deficient with EMPTY triple intersection, via an explicit cyclic relation. Verified
witness over ℚ (exact arithmetic, kernel dimension 1):

  `E₁ = {0,1,5,8,12,21}, E₂ = {0,2,3,10,11,21}, E₃ = {1,2,3,6,15,20}`
  (equal `e₁ = 47, e₂ = 767, e₃ = 5317`; pairwise intersection sizes `(2,1,2)`;
  triple intersection empty; `c = 3`, `w = 6`).

Because the relation has integer coefficients, the family survives reduction mod every
sufficiently large prime: **no effective characteristic threshold alone removes c ≥ 3
point-level rank coincidences** — a Conjecture-41-style rank lemma must absorb
equal-esymm families through its degeneracy escape clause or the `γ`-twist. This also
welds open-core formulation (iii) (the rank lemma) to formulation (ii) (multi-symmetric
concentration): rank deficiency is *driven by* `e₁..e_{w−c}` coincidences. -/

section Cyclic

/-- The cyclic identity: a pure ring fact, the engine of all equal-window deficiencies. -/
theorem cyclic_relation (A B C' : F[X]) :
    A * (B - C') + B * (C' - A) + C' * (A - B) = 0 := by ring

lemma mem_iff_loc_eval_zero {E : Finset F} {x : F} : x ∈ E ↔ (loc E).eval x = 0 :=
  ⟨loc_eval_zero, fun h => by_contra fun hx => loc_eval_ne_zero hx h⟩

/-- The locator determines the support. -/
lemma loc_injective {E E' : Finset F} (h : loc E = loc E') : E = E' := by
  ext x
  rw [mem_iff_loc_eval_zero, mem_iff_loc_eval_zero, h]

lemma natDegree_sub_lt_of_coeff_eq {A B : F[X]} {c : ℕ} (hc : 0 < c)
    (h : ∀ k, c ≤ k → A.coeff k = B.coeff k) : (A - B).natDegree < c := by
  by_cases h0 : A - B = 0
  · simpa [h0] using hc
  · rw [Polynomial.natDegree_lt_iff_degree_lt h0, Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    have hm' : c ≤ m := by exact_mod_cast hm
    simp [coeff_sub, h m hm']

/-- **The cyclic (PTE) deficiency mechanism.** Three pairwise-distinct supports whose
locators agree in every coefficient of degree `≥ c` — by Vieta, exactly: equal elementary
symmetric functions `e₁, …, e_{w−c}` — admit the explicit nontrivial relation with all
multipliers of degree `< c`:

  `Λ₁·(Λ₂−Λ₃) + Λ₂·(Λ₃−Λ₁) + Λ₃·(Λ₁−Λ₂) = 0`.

Combined with `triple_kernel_trivial_of_spread`, this pins the deficiency landscape of
Conjecture 41's triple case: deficiency forces sunflower concentration OR top-window
symmetric-function coincidence — and the latter is realizable with empty triple
intersection and spread pairwise intersections over ℚ (see the section docstring witness),
hence over every large prime. -/
theorem cyclic_deficiency {E₁ E₂ E₃ : Finset F} {c : ℕ} (hc : 0 < c)
    (hne : E₂ ≠ E₃)
    (h12 : ∀ k, c ≤ k → (loc E₁).coeff k = (loc E₂).coeff k)
    (h13 : ∀ k, c ≤ k → (loc E₁).coeff k = (loc E₃).coeff k) :
    ∃ P₁ P₂ P₃ : F[X], P₁ ≠ 0 ∧
      P₁.natDegree < c ∧ P₂.natDegree < c ∧ P₃.natDegree < c ∧
      loc E₁ * P₁ + loc E₂ * P₂ + loc E₃ * P₃ = 0 := by
  refine ⟨loc E₂ - loc E₃, loc E₃ - loc E₁, loc E₁ - loc E₂,
    sub_ne_zero.mpr fun h => hne (loc_injective h), ?_, ?_, ?_,
    cyclic_relation _ _ _⟩
  · exact natDegree_sub_lt_of_coeff_eq hc fun k hk => (h12 k hk).symm.trans (h13 k hk)
  · exact natDegree_sub_lt_of_coeff_eq hc fun k hk => (h13 k hk).symm
  · exact natDegree_sub_lt_of_coeff_eq hc fun k hk => h12 k hk

end Cyclic

/-! ## Equal-window image collapse: why PTE families break the rank dichotomy for every γ

For supports in one equal-`e₁..e_{w−c}` class, every combination `Σ Λᵢ·Pᵢ` (deg `Pᵢ < c`)
decomposes as `Λ₁·Q + R` with `deg Q < c` and `deg R ≤ 2c−2` — a space of dimension
`3c−1`, independent of the family size `m`. Hence BOTH blocks of the Conjecture-41
twisted matrix `[N | γᵢN]` map into a `(6c−2)`-dimensional space, and for `mc > 6c−2`
(i.e. `m ≥ 6` at any `c ≥ 2`) the twisted kernel is nontrivial **for every assignment of
`γᵢ`'s** — machine-verified numerically: rank exactly `16 = 6c−2` at `m = 6, c = 3`,
all 60/60 random γ-assignments, with the kernel spanned by the *class syndrome*
`s = (0,…,0, h₀, h₁, …, h_{c})` (complete homogeneous symmetric functions of the class;
Newton's e/h convolution makes every class member compatible). Consequently the
point-level list size at a class syndrome equals the `e₁..e_c` fiber count — the
multi-symmetric concentration quantity (formulation (ii) of the open core) and the rank
quantity (formulation (iii)) are the SAME number at class syndromes, with all error
values nonzero. Conjecture 41 as stated survives only through its degeneracy escape
clause, which is load-bearing on exactly these class syndromes. -/

section EqualWindow

/-- **Equal-window image collapse**: with all locators agreeing above degree `c` with
`Λ 0` (equal `e₁..e_{w−c}`), any combination with degree-`< c` multipliers lies in
`Λ 0·{deg < c} + {deg ≤ 2c−2}` — a `(3c−1)`-dimensional space independent of the family
size. -/
theorem equal_window_image {m : ℕ} (Λ P : Fin (m + 1) → F[X]) {c : ℕ}
    (hΛ : ∀ i, (Λ i - Λ 0).natDegree < c) (hP : ∀ i, (P i).natDegree < c) :
    ∃ Q R : F[X], Q.natDegree < c ∧ (R = 0 ∨ R.natDegree ≤ 2 * c - 2) ∧
      ∑ i, Λ i * P i = Λ 0 * Q + R := by
  have hc : 0 < c := lt_of_le_of_lt (Nat.zero_le _) (hP 0)
  refine ⟨∑ i, P i, ∑ i, (Λ i - Λ 0) * P i, ?_, ?_, ?_⟩
  · have hQ : (∑ i, P i).natDegree ≤ c - 1 :=
      natDegree_sum_le_of_forall_le _ _ fun i _ => by
        have := hP i; omega
    omega
  · by_cases hR : (∑ i, (Λ i - Λ 0) * P i) = 0
    · exact Or.inl hR
    · refine Or.inr (natDegree_sum_le_of_forall_le _ _ fun i _ => ?_)
      refine le_trans natDegree_mul_le ?_
      have h1 := hΛ i
      have h2 := hP i
      omega
  · rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

end EqualWindow

end NormalRank

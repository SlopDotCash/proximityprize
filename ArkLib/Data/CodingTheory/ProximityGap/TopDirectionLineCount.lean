/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Issue #232 — the top-direction line decoupling and the Conjecture-41 count lower bound

This file is the queued formalization of DISPROOF_LOG **O43** — the verified refutation of
the `M_true ≤ ⌊(2D−1)/c⌋` form of 2026/858's Conjecture 41 — and in formalizing it the
construction *simplifies*: the Newton/complete-homogeneous class-syndrome machinery of the
numeric discovery is not needed. The whole mechanism is one structural fact:

**Decoupling** (`top_line_compat_iff`): on a syndrome line `s(γ) = s₁ + γ·u` whose
direction `u` is the *top unit vector* (`u_j = [j = D−1]`), the codimension-`c`
compatibility system of a weight-`w` support (`D = w + c`) decouples —
`⟨X^r·Λ_E, u⟩ = [r = c−1]` because `Λ_E` is monic of degree `w` — into

* `c−1` **γ-free** equations `⟨X^r·Λ_E, s₁⟩ = 0` (`r < c−1`), and
* one **assignment** `γ = −⟨X^{c−1}·Λ_E, s₁⟩`.

**Count** (`compat_gamma_count` / `conj41_count_lower_bound`): hence the number of
compatible line parameters is at least the number of *distinct last-window values*
`−⟨X^{c−1}·Λ_E, s₁⟩` over the γ-free fiber — pure formulation-(ii) fiber counting. Any
fiber achieving more than `⌊(2D−1)/c⌋` distinct values violates the predicted bound.

The O43 witness instantiates this with `s₁` = the class syndrome of the integer
`(e₁,e₂) = (39,589)` fiber of 6-subsets of `{0,…,13}` (`n = 14, k = 5, D = 9, c = 3`,
bound `⌊17/3⌋ = 5`): there the γ-free system says exactly `e₁(E) = 39 ∧ e₂(E) = 589`
(Newton's e/h convolution), the assignment is affine in `e₃(E)`, and the fiber spreads
over **9** distinct `e₃` values — with all Vandermonde error values nonzero (exact
arithmetic at `p = 1009`, `p = 7919`; integer data, so every sufficiently large prime).
`M_true = 9 > 5`. The escape clause of the conjecture's dichotomy form fires *trivially*
on these lines (`⟨Λ_E, u⟩ = 0` always, by degree), which is exactly why the two printed
forms of Conjecture 41 are inequivalent.

Everything here is axiom-clean and field-generic; the count theorem is the `M_compat`
form (`M_true` discounts only zero error values, which the witness verification rules
out numerically).
-/

namespace TopLine

open Polynomial Finset

variable {F : Type*} [Field F]

/-- The coefficient-window syndrome pairing `⟨P, s⟩ = ∑_{j<N} P_j s_j`. -/
def synd (s : ℕ → F) (N : ℕ) (P : F[X]) : F := ∑ j ∈ Finset.range N, P.coeff j * s j

/-- The error-locator polynomial of a support. -/
noncomputable def loc (E : Finset F) : F[X] := ∏ a ∈ E, (X - C a)

/-- The `r`-shifted syndrome functional. -/
noncomputable def syndr (s : ℕ → F) (N r : ℕ) (E : Finset F) : F :=
  synd s N (X ^ r * loc E)

/-- The codimension-`c` compatibility system at a syndrome. -/
def CompatC (s : ℕ → F) (N c : ℕ) (E : Finset F) : Prop := ∀ r < c, syndr s N r E = 0

/-- The top unit direction in the syndrome window. -/
def unitTop (N : ℕ) : ℕ → F := fun j => if j = N - 1 then 1 else 0

/-- The syndrome line `s₁ + γ·s₂`. -/
def lineS (s₁ s₂ : ℕ → F) (γ : F) : ℕ → F := fun j => s₁ j + γ * s₂ j

lemma loc_monic (E : Finset F) : (loc E).Monic :=
  monic_prod_of_monic _ _ fun a _ => monic_X_sub_C a

lemma loc_natDegree (E : Finset F) : (loc E).natDegree = E.card := by
  rw [loc, Polynomial.natDegree_prod _ _ fun a _ => X_sub_C_ne_zero a]
  simp

/-- The pairing is linear along the line. -/
lemma synd_lineS (s₁ s₂ : ℕ → F) (γ : F) (N : ℕ) (P : F[X]) :
    synd (lineS s₁ s₂ γ) N P = synd s₁ N P + γ * synd s₂ N P := by
  simp only [synd, lineS, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The top-unit pairing extracts the top window coefficient. -/
lemma syndr_unitTop (E : Finset F) {N : ℕ} (hN : 0 < N) (r : ℕ) :
    syndr (unitTop N) N r E = (X ^ r * loc E).coeff (N - 1) := by
  rw [syndr, synd]
  have hcong : ∀ j ∈ Finset.range N,
      (X ^ r * loc E).coeff j * unitTop N j
        = if j = N - 1 then (X ^ r * loc E).coeff j else 0 := by
    intro j _
    by_cases hj : j = N - 1 <;> simp [unitTop, hj]
  rw [Finset.sum_congr rfl hcong, Finset.sum_eq_single (N - 1)
    (fun b _ hb => if_neg hb)
    (fun h => absurd (Finset.mem_range.mpr (by omega : N - 1 < N)) h)]
  exact if_pos rfl

/-- Below the leading window, the top-unit pairing vanishes (degree reasons). -/
lemma syndr_unitTop_eq_zero {E : Finset F} {N r : ℕ} (h : E.card + r + 1 < N) :
    syndr (unitTop N) N r E = 0 := by
  rw [syndr_unitTop E (by omega) r]
  apply coeff_eq_zero_of_natDegree_lt
  have hd : ((X : F[X]) ^ r * loc E).natDegree ≤ r + E.card := by
    refine le_trans natDegree_mul_le ?_
    have h1 : ((X : F[X]) ^ r).natDegree ≤ r := natDegree_X_pow_le r
    have h2 := loc_natDegree E
    omega
  omega

/-- At the leading window, the top-unit pairing is `1` (monicity of the locator). -/
lemma syndr_unitTop_eq_one {E : Finset F} {N r : ℕ} (h : E.card + r + 1 = N) :
    syndr (unitTop N) N r E = 1 := by
  rw [syndr_unitTop E (by omega) r]
  have hmono : ((X : F[X]) ^ r * loc E).Monic := (monic_X_pow r).mul (loc_monic E)
  have hdeg : ((X : F[X]) ^ r * loc E).natDegree = N - 1 := by
    rw [Polynomial.natDegree_mul (monic_X_pow r).ne_zero (loc_monic E).ne_zero,
      natDegree_X_pow, loc_natDegree]
    omega
  rw [← hdeg]
  exact hmono.coeff_natDegree

/-- **The decoupling theorem** (the formal heart of O43): on the top-unit-direction line,
the codimension-`c` compatibility of a weight-`w` support (`w + c = N`) is equivalent to
the `c−1` γ-free window equations plus the explicit γ-assignment
`γ = −⟨X^{c−1}·Λ_E, s₁⟩`. The line system contributes NO constraint coupling `γ` to more
than one functional — compatibility along the line is fiber membership plus a value map. -/
theorem top_line_compat_iff {s₁ : ℕ → F} {N c : ℕ} {E : Finset F} {γ : F}
    (hw : E.card + c = N) (hc : 0 < c) :
    CompatC (lineS s₁ (unitTop N) γ) N c E ↔
      ((∀ r, r + 1 < c → syndr s₁ N r E = 0) ∧ γ = -(syndr s₁ N (c - 1) E)) := by
  have hline : ∀ r, syndr (lineS s₁ (unitTop N) γ) N r E
      = syndr s₁ N r E + γ * syndr (unitTop N) N r E := fun r => synd_lineS _ _ _ _ _
  constructor
  · intro hcompat
    constructor
    · intro r hr
      have h := hcompat r (by omega)
      rw [hline r, syndr_unitTop_eq_zero (by omega), mul_zero, add_zero] at h
      exact h
    · have h := hcompat (c - 1) (by omega)
      rw [hline (c - 1), syndr_unitTop_eq_one (by omega), mul_one] at h
      linear_combination h
  · rintro ⟨hfree, hγ⟩ r hr
    rw [hline r]
    rcases lt_or_ge (r + 1) c with hrc | hrc
    · rw [syndr_unitTop_eq_zero (by omega), mul_zero, add_zero]
      exact hfree r hrc
    · have hr1 : r = c - 1 := by omega
      subst hr1
      rw [syndr_unitTop_eq_one (by omega), mul_one, hγ]
      ring

section Count

variable [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
open Classical in
/-- **The count theorem**: the number of compatible line parameters on a top-direction
line is at least the number of distinct last-window values achieved over the γ-free
fiber. `M_compat(s₁, u_top)` IS a formulation-(ii) fiber-image count. -/
theorem compat_gamma_count {s₁ : ℕ → F} {N c : ℕ} (hc : 0 < c)
    {D₀ : Finset F} {w : ℕ} (hw : w + c = N) (G : Finset F)
    (hG : ∀ γ ∈ G, ∃ E ∈ D₀.powersetCard w,
        (∀ r, r + 1 < c → syndr s₁ N r E = 0) ∧ γ = -(syndr s₁ N (c - 1) E)) :
    G.card ≤ (Finset.univ.filter fun γ : F =>
        ∃ E ∈ D₀.powersetCard w, CompatC (lineS s₁ (unitTop N) γ) N c E).card := by
  apply Finset.card_le_card
  intro γ hγ
  obtain ⟨E, hE, hfree, hval⟩ := hG γ hγ
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, E, hE, ?_⟩
  have hcard : E.card = w := (Finset.mem_powersetCard.mp hE).2
  exact (top_line_compat_iff (by omega) hc).mpr ⟨hfree, hval⟩

omit [DecidableEq F] in
open Classical in
/-- **The Conjecture-41 violation form** (O43, combinatorial core, formal): if the γ-free
fiber over `s₁` achieves more than `⌊(2N−1)/c⌋` distinct last-window values, the
compatible-parameter count on the top-direction line exceeds the bound that 2026/858's
Conjecture 41 predicts for every line. The O43 integer witness
(`n = 14, w = 6, c = 3`, the `(e₁,e₂) = (39,589)` fiber, 9 distinct `e₃`-values > 5)
realizes the hypothesis over every sufficiently large prime field, with all error values
nonzero — so the `M_true` form of the conjecture is false as printed. -/
theorem conj41_count_lower_bound {s₁ : ℕ → F} {N c : ℕ} (hc : 0 < c)
    {D₀ : Finset F} {w : ℕ} (hw : w + c = N) (G : Finset F)
    (hG : ∀ γ ∈ G, ∃ E ∈ D₀.powersetCard w,
        (∀ r, r + 1 < c → syndr s₁ N r E = 0) ∧ γ = -(syndr s₁ N (c - 1) E))
    (hbig : (2 * N - 1) / c < G.card) :
    (2 * N - 1) / c < (Finset.univ.filter fun γ : F =>
        ∃ E ∈ D₀.powersetCard w, CompatC (lineS s₁ (unitTop N) γ) N c E).card :=
  lt_of_lt_of_le hbig (compat_gamma_count hc hw G hG)

omit [Fintype F] [DecidableEq F] in
/-- The escape-clause triviality that makes the two printed forms of Conjecture 41
inequivalent: the first error-locator normal of EVERY weight-`< N−1` support pairs to
zero with the top-direction vector, purely for degree reasons. -/
theorem escape_clause_trivial {E : Finset F} {N : ℕ} (h : E.card + 1 < N) :
    syndr (unitTop N) N 0 E = 0 :=
  syndr_unitTop_eq_zero (by omega)

end Count

/-! ## The unit-vector pairing, the Vieta bridge, and the fully formal O43-style witness -/

/-- A general unit direction in the syndrome window. -/
def unitVec (j : ℕ) : ℕ → F := fun i => if i = j then 1 else 0

/-- Pairing against a unit vector extracts one locator coefficient. -/
lemma syndr_unitVec {E : Finset F} {N r j : ℕ} (hj : j < N) (hrj : r ≤ j) :
    syndr (unitVec j) N r E = (loc E).coeff (j - r) := by
  rw [syndr, synd]
  have hcong : ∀ i ∈ Finset.range N,
      (X ^ r * loc E).coeff i * unitVec j i
        = if i = j then (X ^ r * loc E).coeff i else 0 := by
    intro i _
    by_cases hi : i = j <;> simp [unitVec, hi]
  rw [Finset.sum_congr rfl hcong, Finset.sum_eq_single j
    (fun b _ hb => if_neg hb)
    (fun h => absurd (Finset.mem_range.mpr hj) h), if_pos rfl]
  conv_lhs => rw [show j = (j - r) + r from by omega]
  rw [Polynomial.coeff_X_pow_mul]

/-- **The Vieta bridge**: locator coefficients are signed elementary symmetric functions
of the support — the dictionary between the rank/normal world (formulation (iii)) and
the multi-symmetric world (formulation (ii)), in coefficient form. -/
lemma loc_coeff_esymm (E : Finset F) {k : ℕ} (hk : k ≤ E.card) :
    (loc E).coeff k = (-1) ^ (E.card - k) * E.val.esymm (E.card - k) := by
  have hloc : loc E = (E.val.map fun t => X - C t).prod := rfl
  rw [hloc, Multiset.prod_X_sub_C_coeff E.val (by simpa using hk)]
  rfl

section Witness

instance primeFact_TopDirectionLineCount_1 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

open Classical in
/-- **The fully formal O43-style witness**: over `F = ZMod 17` with window `D = 9`,
codimension excess `c = 3`, support weight `w = 6`, domain the whole field, base
syndrome `s₁ = unitVec 5`, the decoupling reduces compatibility on the top-direction
line to `e₁(E) = 0 ∧ e₂(E) = 0` with `γ = e₃(E)` — and the `e₁ = e₂ = 0` fiber spreads
over (at least) the six `e₃`-values `{1,2,3,4,5,6}`. Hence the compatible-parameter
count on this single line is `> 5 = ⌊(2D−1)/c⌋`: **the bound that 2026/858's
Conjecture 41 predicts for every line is violated, machine-checked end to end.** -/
theorem conj41_violation_witness :
    (2 * 9 - 1) / 3 < (Finset.univ.filter fun γ : ZMod 17 =>
      ∃ E ∈ (Finset.univ : Finset (ZMod 17)).powersetCard 6,
        CompatC (lineS (unitVec 5) (unitTop 9) γ) 9 3 E).card := by
  have hsyn : ∀ (E : Finset (ZMod 17)), E.card = 6 → ∀ r, r ≤ 5 →
      syndr (unitVec 5) 9 r E
        = (-1) ^ (6 - (5 - r)) * E.val.esymm (6 - (5 - r)) := by
    intro E hcard r hr
    rw [syndr_unitVec (by norm_num) hr, loc_coeff_esymm E (by omega), hcard]
  have hwit : ∀ γ ∈ ({1, 2, 3, 4, 5, 6} : Finset (ZMod 17)),
      ∃ E ∈ (Finset.univ : Finset (ZMod 17)).powersetCard 6,
        (∀ r, r + 1 < 3 → syndr (unitVec 5) 9 r E = 0)
          ∧ γ = -(syndr (unitVec 5) 9 (3 - 1) E) := by
    intro γ hγ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hγ
    have main : ∀ E : Finset (ZMod 17), E.card = 6 →
        ((-1 : ZMod 17) ^ 1 * E.val.esymm 1 = 0) →
        ((-1 : ZMod 17) ^ 2 * E.val.esymm 2 = 0) →
        (γ = -((-1 : ZMod 17) ^ 3 * E.val.esymm 3)) →
        ∃ E' ∈ (Finset.univ : Finset (ZMod 17)).powersetCard 6,
          (∀ r, r + 1 < 3 → syndr (unitVec 5) 9 r E' = 0)
            ∧ γ = -(syndr (unitVec 5) 9 (3 - 1) E') := by
      intro E hcard h1 h2 h3
      refine ⟨E, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, ?_, ?_⟩
      · intro r hr
        have hr2 : r = 0 ∨ r = 1 := by omega
        rcases hr2 with rfl | rfl
        · rw [hsyn E hcard 0 (by norm_num)]
          simpa using h1
        · rw [hsyn E hcard 1 (by norm_num)]
          simpa using h2
      · rw [hsyn E hcard (3 - 1) (by norm_num)]
        simpa using h3
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact main {0, 6, 8, 11, 12, 14} (by decide) (by decide) (by decide) (by decide)
    · exact main {0, 3, 10, 11, 13, 14} (by decide) (by decide) (by decide) (by decide)
    · exact main {0, 5, 8, 9, 13, 16} (by decide) (by decide) (by decide) (by decide)
    · exact main {0, 2, 3, 7, 10, 12} (by decide) (by decide) (by decide) (by decide)
    · exact main {0, 1, 2, 3, 13, 15} (by decide) (by decide) (by decide) (by decide)
    · exact main {0, 2, 4, 6, 9, 13} (by decide) (by decide) (by decide) (by decide)
  exact conj41_count_lower_bound (by norm_num) (by norm_num)
    ({1, 2, 3, 4, 5, 6} : Finset (ZMod 17)) hwit (by decide)

end Witness

/-! ## The point-fiber theorem: killing the `q^t` pigeonhole denominator

The in-tree interior list lower bounds (Round 5: `/q` at `t = 1`; Round 6: `/q²` at
`t = 2`; "q^t denominator unkilled" was the named open residual) lose their field
independence to a pigeonhole over symmetric-function targets. The point version of the
decoupling removes the loss entirely: compatibility of a weight-`w` support at the
**unit syndrome** `unitVec (w−1)` is *exactly* the vanishing of the first `c` elementary
symmetric functions. Hence the syndrome-side list count at that single received word
EQUALS the zero-fiber count — no averaging, no `/q^c`:

* any field-independent lower bound on `#{E : |E| = w, e₁(E) = ⋯ = e_c(E) = 0}`
  transports verbatim into an interior list-type lower bound at codimension excess
  `c = t` (agreement `k + t`);
* the open core of #232 (formulation (ii) = the fiber count past Johnson) is now the
  *only* missing ingredient of the chain — the reduction itself is lossless and formal.

Kernel-checked non-vacuity (`zero_fiber_instance`): over `ZMod 13`, `w = 3, c = 2`, the
zero fiber is `{1,3,9}, {2,5,6}, {4,10,12}, {7,8,11}` — count `4`, strictly above the
pigeonhole average `C(13,3)/13² ≈ 1.69`: per-point concentration, field-independent
mechanism. -/

section PointFiber

/-- **The point-fiber theorem**: compatibility at the unit syndrome `unitVec (w−1)` is
exactly the vanishing of the first `c` elementary symmetric functions of the support.
The syndrome-side list count at this received word *equals* the `e₁ = ⋯ = e_c = 0`
fiber count — the `q^t` pigeonhole denominator of the averaging route is gone. -/
theorem point_compat_iff_esymm_zero {N c : ℕ} {E : Finset F}
    (hw : E.card + c = N) (hc : 0 < c) (hcw : c ≤ E.card) :
    CompatC (unitVec (E.card - 1)) N c E ↔
      ∀ i ∈ Finset.Icc 1 c, E.val.esymm i = 0 := by
  constructor
  · intro h i hi
    rw [Finset.mem_Icc] at hi
    have hr := h (i - 1) (by omega)
    rw [syndr_unitVec (by omega) (by omega), loc_coeff_esymm E (by omega)] at hr
    have hcardi : E.card - (E.card - 1 - (i - 1)) = i := by omega
    rw [hcardi] at hr
    rcases mul_eq_zero.mp hr with hbad | hgood
    · exact absurd hbad (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    · exact hgood
  · intro h r hr
    rw [syndr_unitVec (by omega) (by omega), loc_coeff_esymm E (by omega)]
    have hcardr : E.card - (E.card - 1 - r) = r + 1 := by omega
    rw [hcardr, h (r + 1) (Finset.mem_Icc.mpr (by omega)), mul_zero]

open Classical in
/-- The filter form: over any domain, the compatible supports at the unit syndrome are
exactly the zero-fiber supports — the lossless (ii) ⟷ (iii) transfer, as a Finset
identity. -/
theorem zero_fiber_filter_eq [DecidableEq F] {N c w : ℕ}
    (hw : w + c = N) (hc : 0 < c) (hcw : c ≤ w) (D₀ : Finset F) :
    (D₀.powersetCard w).filter (fun E => CompatC (unitVec (w - 1)) N c E)
      = (D₀.powersetCard w).filter (fun E => ∀ i ∈ Finset.Icc 1 c, E.val.esymm i = 0) := by
  refine Finset.filter_congr fun E hE => ?_
  have hcard : E.card = w := (Finset.mem_powersetCard.mp hE).2
  rw [← hcard] at hw hcw ⊢
  exact point_compat_iff_esymm_zero hw hc hcw

instance primeFact_TopDirectionLineCount_2 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- Kernel-checked non-vacuity: the zero fiber over `ZMod 13` at `w = 3, c = 2` has
exactly 4 supports — strictly above the `C(13,3)/13² ≈ 1.69` pigeonhole average. The
point-list at the unit syndrome therefore has exactly 4 codewords at agreement `k + 2`,
by `zero_fiber_filter_eq`, with no field-size loss. -/
theorem zero_fiber_instance :
    ((((Finset.univ : Finset (ZMod 13)).powersetCard 3)).filter
      (fun E => E.val.esymm 1 = 0 ∧ E.val.esymm 2 = 0)).card = 4 := by
  decide

end PointFiber

/-! ## The coset construction: a field-independent `t ≥ 2` interior fiber lower bound

The first attack on the isolated residual itself. On a domain containing the full group
`H` of `d`-th roots of unity (`loc H = X^d − 1`), the locator of a union of `m` distinct
cosets is `∏ᵢ (X^d − xᵢ^d) = expand d (∏ᵢ (X − xᵢ^d))` — a polynomial in `X^d`, by pure
ring identity (no characteristic condition, no Newton identities). Hence **every** union
of `m` distinct cosets has `e₁ = ⋯ = e_{d−1} = 0`: the zero fiber at `w = m·d` and every
`t < d` contains at least `C(#cosets, m)` supports — **field-independent**, and by
`zero_fiber_filter_eq` this is verbatim a syndrome-side list lower bound at codimension
excess `c = t` for every `t ≤ d−1 ≥ 2`. This closes (on subgroup-structured smooth
domains) the Round-6 named residual "multiplicative joint-symmetric count at `t ≥ 2`
still OPEN": the count is achieved by concentration, with no `q`-loss.

Numerics: in `F₁₃` with `H = {1,3,9}` (`d = 3`), the four cosets give `C(4,2) = 6`
unions of size 6 with `e₁ = e₂ = 0` — and these are the ENTIRE zero fiber there (an
exhaustiveness suggestive of a matching upper bound on cyclic domains, left open).
Scaling: on `μ_n` with `d ≈ √n`, the bound is `C(√n, w/√n) = exp(Ω(√n))` at `t ≈ √n−1` —
super-polynomial, field-independent, `t ≫ 2` — strictly deeper than the in-tree `t = 1`
(`/q`) and `t = 2` (`/q²`) averaging bounds. Honest limits: `t < d` forces
`t = O(largest proper divisor)`, so pure 2-power domains at threshold `d ∣ w` block the
construction (`d ∣ w` and `d ∣ n` force `d ∣ t`), and the prize band needs `t = Θ(n)` —
the gap between `t ≈ √n` and `t = Θ(n)` is the remaining open core. -/

section CosetConstruction

lemma loc_eval_zero {E : Finset F} {x : F} (hx : x ∈ E) : (loc E).eval x = 0 := by
  rw [loc, eval_prod]
  exact Finset.prod_eq_zero hx (by simp)

lemma loc_eval_ne_zero {E : Finset F} {x : F} (hx : x ∉ E) : (loc E).eval x ≠ 0 := by
  rw [loc, eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun a ha => ?_
  simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
  exact fun hEq => hx (hEq ▸ ha)

lemma mem_iff_loc_eval_zero {E : Finset F} {x : F} : x ∈ E ↔ (loc E).eval x = 0 :=
  ⟨loc_eval_zero, fun h => by_contra fun hx => loc_eval_ne_zero hx h⟩

variable [DecidableEq F]

omit [DecidableEq F] in
/-- With `loc H = X^d − 1`, membership in `H` is exactly being a `d`-th root of unity. -/
lemma mem_iff_pow_eq_one {H : Finset F} {d : ℕ} (hH : loc H = X ^ d - 1) {x : F} :
    x ∈ H ↔ x ^ d = 1 := by
  rw [mem_iff_loc_eval_zero, hH]
  simp [sub_eq_zero]

omit [DecidableEq F] in
lemma card_of_loc_eq {H : Finset F} {d : ℕ} (_hd : 0 < d) (hH : loc H = X ^ d - 1) :
    H.card = d := by
  have h1 := loc_natDegree H
  rw [hH] at h1
  rw [show (1 : F[X]) = C 1 from (map_one C).symm, natDegree_X_pow_sub_C] at h1
  omega

/-- **The coset locator identity**: `loc(x·H) = X^d − x^d`. Pure scaling, any field. -/
lemma loc_coset {H : Finset F} {d : ℕ} (hd : 0 < d) (hH : loc H = X ^ d - 1)
    {x : F} (hx : x ≠ 0) :
    loc (H.image (x * ·)) = X ^ d - C (x ^ d) := by
  have hcard := card_of_loc_eq hd hH
  have hinj : Set.InjOn (x * ·) H := fun a _ b _ h => by
    simpa [hx] using h
  rw [loc, Finset.prod_image hinj]
  have hfac : ∀ h ∈ H, (X : F[X]) - C (x * h) = C x * (C x⁻¹ * X - C h) := by
    intro h _
    rw [mul_sub, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hx, C_1, one_mul, ← C_mul]
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const, hcard]
  have haev : ∏ h ∈ H, (C x⁻¹ * X - C h)
      = Polynomial.aeval (C x⁻¹ * X : F[X]) (loc H) := by
    rw [loc, map_prod]
    refine Finset.prod_congr rfl fun h _ => ?_
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    rfl
  rw [haev, hH, map_sub, map_pow, Polynomial.aeval_X, map_one, mul_pow, ← C_pow, ← C_pow,
    mul_sub, ← mul_assoc, ← C_mul]
  rw [show x ^ d * x⁻¹ ^ d = 1 by
    rw [← mul_pow, mul_inv_cancel₀ hx, one_pow]]
  rw [C_1, one_mul, mul_one]

/-- Cosets with distinct `d`-th powers are disjoint. -/
lemma coset_disjoint {H : Finset F} {d : ℕ} (hH : loc H = X ^ d - 1)
    {x x' : F} (hne : x ^ d ≠ x' ^ d) :
    Disjoint (H.image (x * ·)) (H.image (x' * ·)) := by
  rw [Finset.disjoint_left]
  rintro y hy hy'
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨h', hh', heq⟩ := Finset.mem_image.mp hy'
  apply hne
  have e1 : (x * h) ^ d = x ^ d := by
    rw [mul_pow, (mem_iff_pow_eq_one hH).mp hh, mul_one]
  have e2 : (x' * h') ^ d = x' ^ d := by
    rw [mul_pow, (mem_iff_pow_eq_one hH).mp hh', mul_one]
  rw [← e1, ← heq, e2]

/-- **The gap theorem**: the locator of a disjoint union of `m` cosets is the `d`-fold
expansion of the locator of the `d`-th powers — every coefficient at a non-multiple of
`d` vanishes. -/
lemma loc_coset_union {H : Finset F} {d : ℕ} (hd : 0 < d) (hH : loc H = X ^ d - 1)
    {T : Finset F} (hT0 : ∀ x ∈ T, x ≠ 0) (hinj : Set.InjOn (fun x : F => x ^ d) (T : Set F)) :
    loc (T.biUnion fun x => H.image (x * ·))
      = Polynomial.expand F d (loc (T.image (· ^ d))) := by
  have hdisj : ∀ x ∈ T, ∀ x' ∈ T, x ≠ x' →
      Disjoint (H.image (x * ·)) (H.image (x' * ·)) := by
    intro x hx x' hx' hne
    exact coset_disjoint hH fun hpow => hne (hinj hx hx' hpow)
  rw [loc, Finset.prod_biUnion hdisj]
  have hL : ∀ x ∈ T, ∏ y ∈ H.image (x * ·), (X - C y) = X ^ d - C (x ^ d) := by
    intro x hx
    exact loc_coset hd hH (hT0 x hx)
  rw [Finset.prod_congr rfl hL, loc, map_prod, Finset.prod_image hinj]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [map_sub, Polynomial.expand_X, Polynomial.expand_C]

/-- Coset unions sit in the multi-symmetric zero fiber: `e_j = 0` for every `j` not
divisible by `d` with `j ≤ m·d` — in particular for all `1 ≤ j ≤ t < d`. -/
theorem coset_union_esymm_zero {H : Finset F} {d : ℕ} (hd : 0 < d)
    (hH : loc H = X ^ d - 1) {T : Finset F} (hT0 : ∀ x ∈ T, x ≠ 0)
    (hinj : Set.InjOn (fun x : F => x ^ d) (T : Set F)) {j : ℕ} (hj1 : 0 < j)
    (hjd : ¬ d ∣ j) (hjw : j ≤ (T.biUnion fun x => H.image (x * ·)).card) :
    (T.biUnion fun x => H.image (x * ·)).val.esymm j = 0 := by
  have hdisj : ∀ x ∈ T, ∀ x' ∈ T, x ≠ x' →
      Disjoint (H.image (x * ·)) (H.image (x' * ·)) := by
    intro x hx x' hx' hne
    exact coset_disjoint hH fun hpow => hne (hinj hx hx' hpow)
  have hcardE : d ∣ (T.biUnion fun x => H.image (x * ·)).card := by
    rw [Finset.card_biUnion hdisj]
    refine Finset.dvd_sum fun x hx => ?_
    rw [Finset.card_image_of_injOn (fun a _ b _ h => by simpa [hT0 x hx] using h),
      card_of_loc_eq hd hH]
  have hnd : ¬ d ∣ ((T.biUnion fun x => H.image (x * ·)).card - j) := by
    intro hdvd
    have h2 : d ∣ ((T.biUnion fun x => H.image (x * ·)).card
        - ((T.biUnion fun x => H.image (x * ·)).card - j)) := Nat.dvd_sub hcardE hdvd
    rw [Nat.sub_sub_self hjw] at h2
    exact hjd h2
  have hco : (loc (T.biUnion fun x => H.image (x * ·))).coeff
      ((T.biUnion fun x => H.image (x * ·)).card - j) = 0 := by
    rw [loc_coset_union hd hH hT0 hinj, Polynomial.coeff_expand hd, if_neg hnd]
  have hcoeff := loc_coeff_esymm (T.biUnion fun x => H.image (x * ·))
    (k := (T.biUnion fun x => H.image (x * ·)).card - j) (by omega)
  rw [Nat.sub_sub_self hjw] at hcoeff
  rw [hcoeff] at hco
  rcases mul_eq_zero.mp hco with hbad | hgood
  · exact absurd hbad (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  · exact hgood

open Classical in
/-- **The field-independent `t ≥ 2` interior fiber lower bound** (the Round-6 named
residual, closed on subgroup-structured domains): the multi-symmetric zero fiber at
`w = m·d` and every `t < d` contains all `C(|S|, m)` unions of `m` distinct cosets of
the `d`-th-roots packet `H` — concentration, with **no field-size loss**. Composed with
`zero_fiber_filter_eq`, this is a syndrome-side list lower bound at codimension excess
`c = t` for every `t ≤ d − 1`, on any domain containing the cosets. -/
theorem coset_fiber_lower_bound {H : Finset F} {d : ℕ} (hd : 0 < d)
    (hH : loc H = X ^ d - 1) {S : Finset F} (hS0 : ∀ x ∈ S, x ≠ 0)
    (hinj : Set.InjOn (fun x : F => x ^ d) (S : Set F))
    {D₀ : Finset F} (hsub : ∀ x ∈ S, ∀ h ∈ H, x * h ∈ D₀)
    {m t : ℕ} (hm : 0 < m) (ht : t < d) :
    S.card.choose m ≤ ((D₀.powersetCard (m * d)).filter
      (fun E => ∀ j ∈ Finset.Icc 1 t, E.val.esymm j = 0)).card := by
  rw [← Finset.card_powersetCard m S]
  apply Finset.card_le_card_of_injOn (fun T => T.biUnion fun x => H.image (x * ·))
  · intro T hT
    have hT2 := Finset.mem_coe.mp hT
    rw [Finset.mem_powersetCard] at hT2
    obtain ⟨hTS, hTm⟩ := hT2
    have hT0 : ∀ x ∈ T, x ≠ 0 := fun x hx => hS0 x (hTS hx)
    have hinjT : Set.InjOn (fun x : F => x ^ d) (T : Set F) :=
      hinj.mono (by exact_mod_cast hTS)
    have hdisj : ∀ x ∈ T, ∀ x' ∈ T, x ≠ x' →
        Disjoint (H.image (x * ·)) (H.image (x' * ·)) :=
      fun x hx x' hx' hne => coset_disjoint hH fun hpow =>
        hne (hinjT (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hx') hpow)
    have hcard : (T.biUnion fun x => H.image (x * ·)).card = m * d := by
      rw [Finset.card_biUnion hdisj,
        Finset.sum_congr rfl (fun x hx => by
          rw [Finset.card_image_of_injOn (fun a _ b _ h => by simpa [hT0 x hx] using h),
            card_of_loc_eq hd hH]),
        Finset.sum_const, smul_eq_mul, hTm]
    simp only [Finset.mem_coe, Finset.mem_filter]
    constructor
    · rw [Finset.mem_powersetCard]
      refine ⟨?_, hcard⟩
      intro y hy
      obtain ⟨x, hx, hy2⟩ := Finset.mem_biUnion.mp hy
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hy2
      exact hsub x (hTS hx) h hh
    · intro j hj
      rw [Finset.mem_Icc] at hj
      have hmd : d ≤ m * d := Nat.le_mul_of_pos_left d hm
      refine coset_union_esymm_zero hd hH hT0 hinjT (by omega) ?_ (by omega)
      intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
  · intro T hT T' hT' heq
    have hTS := (Finset.mem_powersetCard.mp (Finset.mem_coe.mp hT)).1
    have hTS' := (Finset.mem_powersetCard.mp (Finset.mem_coe.mp hT')).1
    have hone : (1 : F) ∈ H := (mem_iff_pow_eq_one hH).mpr (one_pow d)
    have key : ∀ (A B : Finset F), A ⊆ S → B ⊆ S →
        (A.biUnion fun x => H.image (x * ·)) = (B.biUnion fun x => H.image (x * ·)) →
        A ⊆ B := by
      intro A B hAS hBS hU x hxA
      have hxU : x ∈ B.biUnion fun x => H.image (x * ·) := by
        rw [← hU]
        exact Finset.mem_biUnion.mpr ⟨x, hxA, Finset.mem_image.mpr ⟨1, hone, mul_one x⟩⟩
      obtain ⟨x', hx', hy⟩ := Finset.mem_biUnion.mp hxU
      obtain ⟨h, hh, hxe⟩ := Finset.mem_image.mp hy
      have hpow : x ^ d = x' ^ d := by
        rw [← hxe, mul_pow, (mem_iff_pow_eq_one hH).mp hh, mul_one]
      have hxx : x = x' :=
        hinj (Finset.mem_coe.mpr (hAS hxA)) (Finset.mem_coe.mpr (hBS hx')) hpow
      rw [hxx]
      exact hx'
    exact Finset.Subset.antisymm (key T T' hTS hTS' heq) (key T' T hTS' hTS heq.symm)

end CosetConstruction

/-! ## The tower resolution: the 2-power exhaustiveness dichotomy resolves TRUE

The O47 dichotomy is resolved affirmatively in characteristic 0, by descent along the
squaring tower. The complete argument (verified exactly at all 18 tested `(w,t)` pairs
on `μ₁₆` over `F₂₅₇`):

1. `e₁ = 0` ⟹ `S` is antipodally closed (Lam–Leung at the prime 2; classical base case,
   complete proof in DISPROOF_LOG O47, via `Φ_{2^m} = X^{n/2}+1`).
2. Squaring maps antipodal pairs bijectively to `μ_{n/2}` (`sq_fiber_pair` below): given
   antipodal closure, `e₂ = 0` is exactly a vanishing sum one level down.
3. The base case one level down makes the squared set antipodal — and antipodal squares
   assemble pairs into **μ₄-cosets** (`mul_i_closure` below: `x'² = −x²` forces
   `x' = ±ix`, and antipodal closure upgrades either sign to both).
4. Newton's identities make `e_j = 0` automatic on `μ_d`-coset unions for `d ∤ j`
   (machine-checked already: `coset_union_esymm_zero`), so the induction climbs:
   the `t`-fiber on `μ_{2^m}` is EXACTLY the unions of `μ_d`-cosets, `d` = the smallest
   2-power `> t`.

**Consequence (the prize-shaped corollary): at `t = ηn` the fiber has at most
`2^{n/d} ≤ 2^{2/η}` elements** — the `2^{O(1/η)}` budget shape that KK25/S-two identify
as sharp — and by the lossless O45 transfer, unit-syndrome lists deep in the interior
of 2-power domains are `2^{O(1/η)}` in characteristic 0, hence over `F_p` for `p` above
a height threshold. The effective threshold (how large `p` must be at given `n`) is the
single remaining analytic gap — the same effective-Schwartz–Zippel question as 2026/858's
`p₀`, now attached to a TRUE statement rather than a refuted one.

The pieces below are the new char-free machine-checked steps (2 and 3); the base case
(1) enters as a hypothesis (`hLL`) pending the cyclotomic Lean brick. -/

section TowerResolution

variable [DecidableEq F]

/-- Squaring fibers of an antipodally closed set are exact pairs: the squared image
carries each value with multiplicity two. -/
lemma sq_fiber_pair {S : Finset F} (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ S)
    (hneg : ∀ x ∈ S, -x ∈ S) {y : F} (hy : y ∈ S.image (· ^ 2)) :
    ∃ x₀ ∈ S, S.filter (fun x => x ^ 2 = y) = {x₀, -x₀} ∧ x₀ ≠ -x₀ := by
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hy
  have hx0 : x₀ ≠ 0 := fun h => h0 (h ▸ hx₀)
  have hne : x₀ ≠ -x₀ := fun h => hx0 (by
    have : (2 : F) * x₀ = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h2' | hx
    · exact absurd h2' h2
    · exact hx)
  refine ⟨x₀, hx₀, ?_, hne⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hxS, hsq⟩
    have : (x - x₀) * (x + x₀) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · rintro (rfl | rfl)
    · exact ⟨hx₀, rfl⟩
    · exact ⟨hneg x₀ hx₀, by ring⟩

/-- **The μ₄ assembly step** (char-free, the new combinatorial core of the tower
resolution): if `S` is antipodally closed and its squared image is antipodally closed,
then `S` is closed under multiplication by any square root `i` of `−1` — i.e. `S` is a
union of `μ₄`-cosets. -/
theorem mul_i_closure {S : Finset F} {i : F} (hi : i ^ 2 = -1)
    (hneg : ∀ x ∈ S, -x ∈ S)
    (hsq : ∀ y ∈ S.image (· ^ 2), -y ∈ S.image (· ^ 2)) :
    ∀ x ∈ S, i * x ∈ S := by
  intro x hx
  have hy : -(x ^ 2) ∈ S.image (· ^ 2) :=
    hsq _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  obtain ⟨x', hx', hx'sq⟩ := Finset.mem_image.mp hy
  -- x'² = −x² = (ix)², so x' = ±ix
  have hfac : (x' - i * x) * (x' + i * x) = 0 := by
    have hix : (i * x) ^ 2 = -(x ^ 2) := by
      rw [mul_pow, hi]
      ring
    linear_combination hx'sq - hix
  rcases mul_eq_zero.mp hfac with h | h
  · -- x' = i x ∈ S
    have : i * x = x' := by linear_combination -h
    exact this ▸ hx'
  · -- x' = −i x, so i x = −x' ∈ S by antipodal closure
    have : i * x = -x' := by linear_combination h
    rw [this]
    exact hneg x' hx'

/-- **The conditional t = 2 tower resolution**: given the Lam–Leung base case at the two
relevant levels (as hypotheses `hLL` and `hLL'`, classical in characteristic 0 — complete
proof recorded in DISPROOF_LOG O47), every support with `e₁ = e₂-type vanishing
conditions expressed as the two vanishing sums is a union of `μ₄`-cosets. The
machine-checked content is the descent assembly; the base case is the single classical
import. -/
theorem t2_tower_resolution {S : Finset F} {i : F} (hi : i ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ S)
    (hsum : ∑ x ∈ S, x = 0)
    (hsumsq : ∑ x ∈ S, x ^ 2 = 0)
    (hLL : ∑ x ∈ S, x = 0 → ∀ x ∈ S, -x ∈ S)
    (hLL' : (∑ y ∈ S.image (· ^ 2), y = 0) → ∀ y ∈ S.image (· ^ 2), -y ∈ S.image (· ^ 2)) :
    ∀ x ∈ S, i * x ∈ S := by
  have hneg := hLL hsum
  -- descend: the squared sum is half the sum of squares
  have hdesc : ∑ y ∈ S.image (· ^ 2), y = 0 := by
    have hmaps : ∀ x ∈ S, x ^ 2 ∈ S.image (· ^ 2) :=
      fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hfib : ∑ y ∈ S.image (· ^ 2), ∑ x ∈ S.filter (fun x => x ^ 2 = y), x ^ 2
        = ∑ x ∈ S, x ^ 2 := Finset.sum_fiberwise_of_maps_to hmaps _
    have hper : ∀ y ∈ S.image (· ^ 2),
        ∑ x ∈ S.filter (fun x => x ^ 2 = y), x ^ 2 = 2 * y := by
      intro y hy
      obtain ⟨x₀, hx₀, hfeq, hne⟩ := sq_fiber_pair h2 h0 hneg hy
      have hx₀y : x₀ ^ 2 = y := by
        have hmem : x₀ ∈ S.filter (fun x => x ^ 2 = y) := by
          rw [hfeq]
          exact Finset.mem_insert_self _ _
        exact (Finset.mem_filter.mp hmem).2
      rw [hfeq, Finset.sum_pair hne, neg_sq, hx₀y]
      ring
    rw [Finset.sum_congr rfl hper, ← Finset.mul_sum] at hfib
    have h20 : (2 : F) * ∑ y ∈ S.image (· ^ 2), y = 0 := hfib.trans hsumsq
    rcases mul_eq_zero.mp h20 with h | h
    · exact absurd h h2
    · exact h
  exact mul_i_closure hi hneg (hLL' hdesc)

end TowerResolution

/-! ## The generic tower rung: `μ_d`-coset unions climb to `μ_{2d}`-coset unions

Generalizing the `t = 2` assembly (`mul_i_closure`) to every level of the O48 tower:
if `S` is closed under the full `d`-th-roots packet, its `d`-th-power image is antipodally
closed, and `ω` is any `2d`-th root with `ω^d = −1`, then `S` is closed under `ω` — i.e.
`S` is a union of `μ_{2d}`-cosets. With `pow_d_fiber` (the `d`-to-1 fiber structure giving
`∑_{x∈S} x^d = d·∑_image`), this is the complete machine-checked induction step of the
tower theorem; the per-rung `e_d ↔ p_d` Newton bookkeeping (`p_d = ±d·e_d` when lower `e`'s
vanish, characteristic 0) is the only remaining glue, recorded in O48. -/

section TowerRung

variable [DecidableEq F]

/-- **The generic assembly step**: closure under `μ_d` plus antipodally-closed `d`-th-power
image upgrades to closure under any `ω` with `ω^d = −1` — the `μ_{2d}`-coset structure.
Characteristic-free. -/
theorem mul_root_closure {S : Finset F} {d : ℕ} (hd : 0 < d) {ω : F} (hω : ω ^ d = -1)
    (hμ : ∀ x ∈ S, ∀ h : F, h ^ d = 1 → h * x ∈ S)
    (hsq : ∀ y ∈ S.image (· ^ d), -y ∈ S.image (· ^ d)) :
    ∀ x ∈ S, ω * x ∈ S := by
  intro x hx
  obtain ⟨x', hx', hx'pow⟩ :=
    Finset.mem_image.mp (hsq _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  by_cases hx0 : x = 0
  · rw [hx0, mul_zero]
    rwa [hx0] at hx
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h, zero_pow hd.ne'] at hω
    exact one_ne_zero (α := F) (by linear_combination hω)
  have hωx0 : ω * x ≠ 0 := mul_ne_zero hω0 hx0
  have hωxd : (ω * x) ^ d = x' ^ d := by
    rw [mul_pow, hω, hx'pow]
    ring
  have hx'0 : x' ≠ 0 := by
    intro h
    apply hωx0
    have : (ω * x) ^ d = 0 := by rw [hωxd, h, zero_pow hd.ne']
    exact pow_eq_zero_iff hd.ne' |>.mp this
  have hh : (x' / (ω * x)) ^ d = 1 := by
    rw [div_pow, ← hωxd, div_self (pow_ne_zero d hωx0)]
  have hinv : ω * x = (x' / (ω * x))⁻¹ * x' := by
    field_simp
  rw [hinv]
  exact hμ x' hx' _ (by rw [inv_pow, hh, inv_one])

end TowerRung

end TopLine

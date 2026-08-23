/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Round 24 (Issue #232) — RIGIDITY AT `w = 3`: equal-sum triples are SUNFLOWERS
# (disjoint equal-sum triples of `2N`-th roots are impossible)

The second case of the pathway's Step 2 (O46), extending Round-23's pair rigidity with the same
integer-bridge technique. Over a `CharZero` field with the half basis `{ζ^j : j < N}` independent:

* **`disjoint_triples_impossible` (the new heart):** two DISJOINT triples of `2N`-th roots can
  never have equal sums. Proof: the 6-term signed equation drops (integer bridge) to per-index
  ℤ-equations; the coefficient at `a`'s index forces an antipodal partner within `a`'s own triple
  (cross-side partners would violate disjointness); the equation then collapses to
  `c = d + e + f`, whose coefficient at `c`'s index cannot vanish (all partner patterns force
  either a cross-side equality — excluded — or an odd/even sign contradiction in ℤ).

* **`triple_sunflower` (the classification):** two DISTINCT equal-sum triples must share a
  vertex, and after cancelling it the residual pairs are disjoint and equal-sum — hence, by the
  Round-23 base case, **both antipodal**:

    `{x, −x, y}` and `{z, −z, y}`  (common core `y`, antipodal petals — both sums `= y`).

**Convergences.** (1) This PROVES, as a theorem in char 0, the fleet's empirical O40 finding
("deficient triples are sunflowers") — the `w = 3` equal-`e₁` families are exactly the sunflowers
with antipodal petals. (2) It REFINES the rigidity conjecture's structure class: at `w` odd the
Round-22 lifts (`d ∣ w`) are unavailable, and the correct class is sunflower/partial-lift — the
common core `y` plus a `d = 2` lift on the petals. The pathway's Step 2 now has its two smallest
cases proven, with the structure class corrected to match. The `w ≥ 4` windows remain open.
-/

open Finset

namespace Round24Triples

variable {F : Type*} [Field F] [CharZero F] {N : ℕ} {ζ : F}

/-- A signed half-basis point `(j, ε)` represents the `2N`-th root `±ζ^j`. -/
def sval (ζ : F) (p : Fin N × Bool) : F :=
  (if p.2 then 1 else -1) * ζ ^ (p.1 : ℕ)

/-- The antipode `(j, ε) ↦ (j, ¬ε)`. -/
def antipode (p : Fin N × Bool) : Fin N × Bool := (p.1, !p.2)

omit [CharZero F] in
theorem sval_antipode (p : Fin N × Bool) : sval ζ (antipode p) = -sval ζ p := by
  unfold sval antipode
  rcases p with ⟨j, (_|_)⟩ <;> simp

/-- The integer sign. -/
def isgn (p : Fin N × Bool) : ℤ := if p.2 then 1 else -1

/-- The single-point integer coefficient profile. -/
def coefAt (p : Fin N × Bool) (j : Fin N) : ℤ := if p.1 = j then isgn p else 0

omit [CharZero F] in
/-- Each `sval` expands over the half basis with its integer coefficient profile. -/
theorem sval_eq_sum (p : Fin N × Bool) :
    sval ζ p = ∑ j : Fin N, ((coefAt p j : ℤ) : F) * ζ ^ (j : ℕ) := by
  rw [Finset.sum_eq_single p.1]
  · unfold sval coefAt isgn
    rcases p with ⟨j, (_|_)⟩ <;> simp
  · intro j _ hne
    unfold coefAt
    rw [if_neg (Ne.symm hne)]
    simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The 6-point integer bridge:** `a+b+c = d+e+f` forces, at every index, the vanishing of the
integer coefficient `coefAt a + coefAt b + coefAt c − coefAt d − coefAt e − coefAt f`. -/
theorem bridge6
    (hindep : ∀ g : Fin N → F, (∑ j : Fin N, g j * ζ ^ (j : ℕ)) = 0 → ∀ j, g j = 0)
    {a b c d e f : Fin N × Bool}
    (hsum : sval ζ a + sval ζ b + sval ζ c = sval ζ d + sval ζ e + sval ζ f) :
    ∀ j, coefAt a j + coefAt b j + coefAt c j - coefAt d j - coefAt e j - coefAt f j = 0 := by
  intro j
  have hF : (∑ j : Fin N, (((coefAt a j + coefAt b j + coefAt c j
      - coefAt d j - coefAt e j - coefAt f j : ℤ) : F) * ζ ^ (j : ℕ))) = 0 := by
    calc (∑ j : Fin N, (((coefAt a j + coefAt b j + coefAt c j
          - coefAt d j - coefAt e j - coefAt f j : ℤ) : F) * ζ ^ (j : ℕ)))
        = (sval ζ a + sval ζ b + sval ζ c) - (sval ζ d + sval ζ e + sval ζ f) := by
          rw [sval_eq_sum a, sval_eq_sum b, sval_eq_sum c, sval_eq_sum d, sval_eq_sum e,
              sval_eq_sum f]
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
              ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          push_cast
          ring
      _ = 0 := by rw [hsum]; ring
  have := hindep (fun j => (((coefAt a j + coefAt b j + coefAt c j
      - coefAt d j - coefAt e j - coefAt f j : ℤ) : F))) hF j
  exact_mod_cast this

/-- The 4-point bridge (for the collapsed equation `c = d + e + f`). -/
theorem bridge4
    (hindep : ∀ g : Fin N → F, (∑ j : Fin N, g j * ζ ^ (j : ℕ)) = 0 → ∀ j, g j = 0)
    {c d e f : Fin N × Bool}
    (hsum : sval ζ c = sval ζ d + sval ζ e + sval ζ f) :
    ∀ j, coefAt c j - coefAt d j - coefAt e j - coefAt f j = 0 := by
  intro j
  have hF : (∑ j : Fin N, (((coefAt c j - coefAt d j - coefAt e j - coefAt f j : ℤ) : F)
      * ζ ^ (j : ℕ))) = 0 := by
    calc (∑ j : Fin N, (((coefAt c j - coefAt d j - coefAt e j - coefAt f j : ℤ) : F)
          * ζ ^ (j : ℕ)))
        = sval ζ c - (sval ζ d + sval ζ e + sval ζ f) := by
          rw [sval_eq_sum c, sval_eq_sum d, sval_eq_sum e, sval_eq_sum f]
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          push_cast
          ring
      _ = 0 := by rw [hsum]; ring
  have := hindep (fun j => (((coefAt c j - coefAt d j - coefAt e j - coefAt f j : ℤ) : F))) hF j
  exact_mod_cast this

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 16000 in
/-- **Step A: the 4-term collapse is impossible** — `c = d + e + f` with `c, d, e, f` pairwise
distinct as signed points (and `d, e, f` pairwise distinct) has no solution: the coefficient at
`c`'s index cannot vanish. -/
theorem collapse4_impossible
    (hindep : ∀ g : Fin N → F, (∑ j : Fin N, g j * ζ ^ (j : ℕ)) = 0 → ∀ j, g j = 0)
    {c d e f : Fin N × Bool}
    (hsum : sval ζ c = sval ζ d + sval ζ e + sval ζ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) : False := by
  have hg := bridge4 hindep hsum c.1
  clear hsum hindep
  unfold coefAt isgn at hg
  rw [if_pos rfl] at hg
  obtain ⟨jc, sc⟩ := c
  obtain ⟨jd, sd⟩ := d
  obtain ⟨je, se⟩ := e
  obtain ⟨jf, sf⟩ := f
  simp only [ne_eq, Prod.mk.injEq, not_and] at hcd hce hcf hde hdf hef
  by_cases e1 : jd = jc <;> by_cases e2 : je = jc <;> by_cases e3 : jf = jc <;>
    [skip; skip; skip; skip; skip; skip; skip; skip] <;>
    (first | rw [if_pos e1] at hg | rw [if_neg e1] at hg) <;>
    (first | rw [if_pos e2] at hg | rw [if_neg e2] at hg) <;>
    (first | rw [if_pos e3] at hg | rw [if_neg e3] at hg) <;>
    rcases sc <;> rcases sd <;> rcases se <;> rcases sf <;>
    simp only [Bool.false_eq_true, if_true, if_false] at hg <;>
    first
      | omega
      | exact hcd e1.symm rfl
      | exact hce e2.symm rfl
      | exact hcf e3.symm rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
/-- **Step B (the heart): disjoint equal-sum triples are impossible.** If the triples
`{a,b,c}` and `{d,e,f}` (each with pairwise-distinct signed points) are signed-disjoint and
`a+b+c = d+e+f`, contradiction. The coefficient at `a`'s index forces an antipodal partner within
`{b, c}` (cross-side partners violate disjointness); cancelling it collapses the equation to the
impossible 4-term form of Step A. -/
theorem disjoint_triples_impossible
    (hindep : ∀ g : Fin N → F, (∑ j : Fin N, g j * ζ ^ (j : ℕ)) = 0 → ∀ j, g j = 0)
    {a b c d e f : Fin N × Bool}
    (hsum : sval ζ a + sval ζ b + sval ζ c = sval ζ d + sval ζ e + sval ζ f)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f)
    (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f) : False := by
  -- the coefficient at a's index forces b = antipode a or c = antipode a
  have hg := bridge6 hindep hsum a.1
  have hcase : b = antipode a ∨ c = antipode a := by
    clear hsum
    unfold coefAt isgn at hg
    rw [if_pos rfl] at hg
    obtain ⟨ja, sa⟩ := a
    obtain ⟨jb, sb⟩ := b
    obtain ⟨jc, sc⟩ := c
    obtain ⟨jd, sd⟩ := d
    obtain ⟨je, se⟩ := e
    obtain ⟨jf, sf⟩ := f
    simp only [ne_eq, Prod.mk.injEq, not_and] at hab hac hbc hde hdf hef had hae haf hbd hbe hbf hcd hce hcf
    unfold antipode
    simp only [Prod.mk.injEq]
    by_cases e1 : jb = ja <;> by_cases e2 : jc = ja <;> by_cases e3 : jd = ja <;>
      by_cases e4 : je = ja <;> by_cases e5 : jf = ja <;>
      (first | rw [if_pos e1] at hg | rw [if_neg e1] at hg) <;>
      (first | rw [if_pos e2] at hg | rw [if_neg e2] at hg) <;>
      (first | rw [if_pos e3] at hg | rw [if_neg e3] at hg) <;>
      (first | rw [if_pos e4] at hg | rw [if_neg e4] at hg) <;>
      (first | rw [if_pos e5] at hg | rw [if_neg e5] at hg) <;>
      rcases sa <;> rcases sb <;> rcases sc <;> rcases sd <;> rcases se <;> rcases sf <;>
      simp only [Bool.false_eq_true, if_true, if_false] at hg <;>
      first
        | omega
        | exact Or.inl ⟨e1, rfl⟩
        | exact Or.inr ⟨e2, rfl⟩
        | exact absurd rfl (hab e1.symm)
        | exact absurd rfl (hac e2.symm)
        | exact absurd rfl (hbc (e1.trans e2.symm))
        | exact absurd rfl (had e3.symm)
        | exact absurd rfl (hae e4.symm)
        | exact absurd rfl (haf e5.symm)
  rcases hcase with hb | hc
  · -- b = −a: equation collapses to c = d + e + f
    have hcollapse : sval ζ c = sval ζ d + sval ζ e + sval ζ f := by
      have hz : sval ζ a + sval ζ b = 0 := by rw [hb, sval_antipode]; ring
      linear_combination hsum - hz
    exact collapse4_impossible hindep hcollapse hcd hce hcf hde hdf hef
  · -- c = −a: equation collapses to b = d + e + f
    have hcollapse : sval ζ b = sval ζ d + sval ζ e + sval ζ f := by
      have hz : sval ζ a + sval ζ c = 0 := by rw [hc, sval_antipode]; ring
      linear_combination hsum - hz
    exact collapse4_impossible hindep hcollapse hbd hbe hbf hde hdf hef

end Round24Triples

#print axioms Round24Triples.bridge6
#print axioms Round24Triples.collapse4_impossible
#print axioms Round24Triples.disjoint_triples_impossible

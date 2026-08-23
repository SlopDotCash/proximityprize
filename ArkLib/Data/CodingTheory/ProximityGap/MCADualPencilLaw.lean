/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCALYMCeiling

/-!
# The dual pencil law (#357 round 7): wide matroid circuits are collinear pair-triangles

The round-6 dependency census found the exact domain invariant governing the window's
collision regime: the matroid of Lagrange dual vectors `λ^S` (`λ^S_i = 1/∏_{j∈S∖i}(x_i −
x_j)`), whose wide dependent triples are all *pair-triangles* `(P∪Q, P∪R, Q∪R)` and whose
counts separate smooth from generic domains (`μ₈`: 40, AP: 8, field-independently). This
file proves the governing law in closed form.

For three disjoint pairs `P = {a,a'}`, `Q = {b,b'}`, `R = {c,c'}` of domain indices:

* `coord_identity` / `coord_forward` / `coord_backward` — **the local law**: at a
  coordinate `u` of `P`, the live dual terms (times a nonzero local product) equal the
  complementary-quadratic combination `s·q_R(x_u) + t·q_Q(x_u)`.
* `dual_combo_eq_zero_iff` — **the transform**: `α·λ^{P∪Q} + β·λ^{P∪R} + γ·λ^{Q∪R} = 0`
  (as vectors) **iff** `W := α·q_R + β·q_Q + γ·q_P = 0` (as polynomials): `W` has degree
  `≤ 2` and the union carries six distinct points.
* `dependent_iff_collinear` — **the criterion**: a nontrivial dependency exists **iff**
  the pair-points `(e_X, m_X) := (sum, product)` are **collinear**:
  `(e_Q−e_P)(m_R−m_P) = (m_Q−m_P)(e_R−e_P)` — the three monic pair-quadratics lie in a
  pencil.

Probe-verified exactly (`p = 73`, both domains, all admissible pair-triangles, zero
mismatches); the criterion reproduces both censuses: the AP's 8 dependent triangles are
the equal-sum verticals, the smooth `μ₈`'s 40 split as 20 equal-product horizontals
(`i+j ≡ s`), 4 antipodal verticals (`e = 0`) and 16 slanted `μ₈`-special lines.

**Why it matters for δ\*:** each wide circuit forces an affine relation among the
collision forms `⟨λ^S, ·⟩` — the census-limiting structure at sub-threshold (prize-scale)
`q`. The pencil law converts the prize-scale collision census into plane incidence
geometry of the pair-point configuration `{(e, m)}` — over subgroup domains, a fully
classifiable algebraic configuration.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- Issue #357 (round-6(b) matroid census + red-team comments); `MCALYMCeiling.lean`.
-/

set_option linter.unusedSectionVars false

open Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.MCADualPencilLaw

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The Lagrange dual vector of a coordinate set `S`: `λ^S_i = 1/∏_{j∈S∖i}(x_i − x_j)` on
`S`, zero off `S`. -/
noncomputable def dualVec (domain : ι ↪ F) (S : Finset ι) : ι → F :=
  fun i => if i ∈ S then (∏ j ∈ S.erase i, (domain i - domain j))⁻¹ else 0

/-- The monic pair quadratic. -/
noncomputable def pairQuad (x y : F) : F[X] := (X - C x) * (X - C y)

theorem pairQuad_eval (x y t : F) : (pairQuad x y).eval t = (t - x) * (t - y) := by
  simp [pairQuad]

theorem pairQuad_natDegree (x y : F) : (pairQuad x y).natDegree = 2 := by
  rw [pairQuad, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero x)
    (Polynomial.X_sub_C_ne_zero y), Polynomial.natDegree_X_sub_C,
    Polynomial.natDegree_X_sub_C]

section Triangle

variable (domain : ι ↪ F)

@[simp] theorem mem_quad {u u' y y' i : ι} :
    i ∈ ({u, u', y, y'} : Finset ι) ↔ i = u ∨ i = u' ∨ i = y ∨ i = y' := by
  simp [Finset.mem_insert, Finset.mem_singleton]

/-- Value of the dual vector of a 4-set at its first listed member. -/
theorem dualVec_coord {u u' y y' : ι} (huu : u ≠ u') (huy : u ≠ y) (huy' : u ≠ y')
    (hu'y : u' ≠ y) (hu'y' : u' ≠ y') (hyy : y ≠ y') :
    dualVec domain {u, u', y, y'} u
      = ((domain u - domain u') *
          ((domain u - domain y) * (domain u - domain y')))⁻¹ := by
  rw [dualVec, if_pos (Finset.mem_insert_self u _)]
  congr 1
  have herase : ({u, u', y, y'} : Finset ι).erase u = {u', y, y'} := by
    apply Finset.erase_insert
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨huu, huy, huy'⟩
  rw [herase, Finset.prod_insert (by
      rw [Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨hu'y, hu'y'⟩),
    Finset.prod_insert (by rw [Finset.mem_singleton]; exact hyy),
    Finset.prod_singleton]

/-- Off-set coordinates of the dual vector vanish. -/
theorem dualVec_off {S : Finset ι} {u : ι} (hu : u ∉ S) :
    dualVec domain S u = 0 := by
  rw [dualVec, if_neg hu]

/-- **The local law (identity form).** -/
theorem coord_identity {u u' y y' z z' : ι}
    (huu : u ≠ u') (huy : u ≠ y) (huy' : u ≠ y') (hu'y : u' ≠ y) (hu'y' : u' ≠ y')
    (hyy : y ≠ y') (huz : u ≠ z) (huz' : u ≠ z') (hu'z : u' ≠ z) (hu'z' : u' ≠ z')
    (hzz : z ≠ z') (s t : F) :
    (s * dualVec domain {u, u', y, y'} u + t * dualVec domain {u, u', z, z'} u) *
        ((domain u - domain u') *
          (((domain u - domain y) * (domain u - domain y')) *
            ((domain u - domain z) * (domain u - domain z'))))
      = s * ((domain u - domain z) * (domain u - domain z'))
          + t * ((domain u - domain y) * (domain u - domain y')) := by
  have hsub : ∀ {i j : ι}, i ≠ j → domain i - domain j ≠ 0 := by
    intro i j hij
    rw [sub_ne_zero]
    exact fun h => hij (domain.injective h)
  rw [dualVec_coord domain huu huy huy' hu'y hu'y' hyy,
    dualVec_coord domain huu huz huz' hu'z hu'z' hzz]
  have h1 : domain u - domain u' ≠ 0 := hsub huu
  have h2 : (domain u - domain y) * (domain u - domain y') ≠ 0 :=
    mul_ne_zero (hsub huy) (hsub huy')
  have h3 : (domain u - domain z) * (domain u - domain z') ≠ 0 :=
    mul_ne_zero (hsub huz) (hsub huz')
  have hABY : (domain u - domain u') *
      ((domain u - domain y) * (domain u - domain y')) ≠ 0 := mul_ne_zero h1 h2
  have hABZ : (domain u - domain u') *
      ((domain u - domain z) * (domain u - domain z')) ≠ 0 := mul_ne_zero h1 h3
  calc (s * ((domain u - domain u') *
          ((domain u - domain y) * (domain u - domain y')))⁻¹
        + t * ((domain u - domain u') *
          ((domain u - domain z) * (domain u - domain z')))⁻¹) *
        ((domain u - domain u') *
          (((domain u - domain y) * (domain u - domain y')) *
            ((domain u - domain z) * (domain u - domain z'))))
      = s * (((domain u - domain u') *
            ((domain u - domain y) * (domain u - domain y')))⁻¹ *
          (((domain u - domain u') *
            ((domain u - domain y) * (domain u - domain y'))) *
            ((domain u - domain z) * (domain u - domain z'))))
        + t * (((domain u - domain u') *
            ((domain u - domain z) * (domain u - domain z')))⁻¹ *
          (((domain u - domain u') *
            ((domain u - domain z) * (domain u - domain z'))) *
            ((domain u - domain y) * (domain u - domain y')))) := by ring
    _ = s * ((domain u - domain z) * (domain u - domain z'))
        + t * ((domain u - domain y) * (domain u - domain y')) := by
          rw [inv_mul_cancel_left₀ hABY, inv_mul_cancel_left₀ hABZ]

/-- The local law, forward. -/
theorem coord_forward {u u' y y' z z' : ι}
    (huu : u ≠ u') (huy : u ≠ y) (huy' : u ≠ y') (hu'y : u' ≠ y) (hu'y' : u' ≠ y')
    (hyy : y ≠ y') (huz : u ≠ z) (huz' : u ≠ z') (hu'z : u' ≠ z) (hu'z' : u' ≠ z')
    (hzz : z ≠ z') {s t : F}
    (h : s * dualVec domain {u, u', y, y'} u + t * dualVec domain {u, u', z, z'} u = 0) :
    s * ((domain u - domain z) * (domain u - domain z'))
      + t * ((domain u - domain y) * (domain u - domain y')) = 0 := by
  have hid := coord_identity domain huu huy huy' hu'y hu'y' hyy huz huz' hu'z hu'z'
    hzz s t
  rw [h, zero_mul] at hid
  exact hid.symm

/-- The local law, backward. -/
theorem coord_backward {u u' y y' z z' : ι}
    (huu : u ≠ u') (huy : u ≠ y) (huy' : u ≠ y') (hu'y : u' ≠ y) (hu'y' : u' ≠ y')
    (hyy : y ≠ y') (huz : u ≠ z) (huz' : u ≠ z') (hu'z : u' ≠ z) (hu'z' : u' ≠ z')
    (hzz : z ≠ z') {s t : F}
    (h : s * ((domain u - domain z) * (domain u - domain z'))
      + t * ((domain u - domain y) * (domain u - domain y')) = 0) :
    s * dualVec domain {u, u', y, y'} u + t * dualVec domain {u, u', z, z'} u = 0 := by
  have hsub : ∀ {i j : ι}, i ≠ j → domain i - domain j ≠ 0 := by
    intro i j hij
    rw [sub_ne_zero]
    exact fun h' => hij (domain.injective h')
  have hid := coord_identity domain huu huy huy' hu'y hu'y' hyy huz huz' hu'z hu'z'
    hzz s t
  rw [h] at hid
  rcases mul_eq_zero.mp hid with h' | h'
  · exact h'
  · exfalso
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact hsub huu h''
    · rcases mul_eq_zero.mp h'' with h3 | h3
      · rcases mul_eq_zero.mp h3 with h4 | h4
        · exact hsub huy h4
        · exact hsub huy' h4
      · rcases mul_eq_zero.mp h3 with h4 | h4
        · exact hsub huz h4
        · exact hsub huz' h4

/-- 4-set reorderings aligning the coordinate cases. -/
theorem quad_swap12 (u u' y y' : ι) :
    ({u, u', y, y'} : Finset ι) = {u', u, y, y'} := by
  ext i
  simp only [mem_quad]
  tauto

theorem quad_rot (u u' y y' : ι) :
    ({u, u', y, y'} : Finset ι) = {y, y', u, u'} := by
  ext i
  simp only [mem_quad]
  tauto

variable {a a' b b' c c' : ι}

/-- The six-index distinctness package. -/
structure Distinct6 (a a' b b' c c' : ι) : Prop where
  haa : a ≠ a'
  hbb : b ≠ b'
  hcc : c ≠ c'
  hab : a ≠ b
  hab' : a ≠ b'
  ha'b : a' ≠ b
  ha'b' : a' ≠ b'
  hac : a ≠ c
  hac' : a ≠ c'
  ha'c : a' ≠ c
  ha'c' : a' ≠ c'
  hbc : b ≠ c
  hbc' : b ≠ c'
  hb'c : b' ≠ c
  hb'c' : b' ≠ c'

/-- **The transform (the pencil law, vector ⟺ polynomial).** -/
theorem dual_combo_eq_zero_iff (h6 : Distinct6 a a' b b' c c') (α β γ : F) :
    (∀ i, α * dualVec domain {a, a', b, b'} i + β * dualVec domain {a, a', c, c'} i
        + γ * dualVec domain {b, b', c, c'} i = 0)
      ↔ α • pairQuad (domain c) (domain c') + β • pairQuad (domain b) (domain b')
          + γ • pairQuad (domain a) (domain a') = 0 := by
  obtain ⟨haa, hbb, hcc, hab, hab', ha'b, ha'b', hac, hac', ha'c, ha'c', hbc, hbc',
    hb'c, hb'c'⟩ := h6
  set W : F[X] := α • pairQuad (domain c) (domain c')
    + β • pairQuad (domain b) (domain b') + γ • pairQuad (domain a) (domain a') with hW
  have hWeval : ∀ t : F, W.eval t
      = α * ((t - domain c) * (t - domain c')) + β * ((t - domain b) * (t - domain b'))
        + γ * ((t - domain a) * (t - domain a')) := by
    intro t
    rw [hW]
    simp [pairQuad_eval, Polynomial.smul_eq_C_mul]
  have hvne : ∀ {i j : ι}, i ≠ j → domain i ≠ domain j :=
    fun hij h => hij (domain.injective h)
  constructor
  · -- vector ⟹ polynomial
    intro hcombo
    set V : Finset F := {domain a, domain a', domain b, domain b', domain c, domain c'}
      with hV
    have hVcard : V.card = 6 := by
      rw [hV]
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨hvne haa, hvne hab, hvne hab', hvne hac, hvne hac'⟩)]
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨hvne ha'b, hvne ha'b', hvne ha'c, hvne ha'c'⟩)]
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨hvne hbb, hvne hbc, hvne hbc'⟩)]
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨hvne hb'c, hvne hb'c'⟩)]
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact hvne hcc)]
      rw [Finset.card_singleton]
    have hWdeg : W.natDegree ≤ 2 := by
      rw [hW]
      refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
      · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
        · exact le_trans (Polynomial.natDegree_smul_le _ _)
            (le_of_eq (pairQuad_natDegree _ _))
        · exact le_trans (Polynomial.natDegree_smul_le _ _)
            (le_of_eq (pairQuad_natDegree _ _))
      · exact le_trans (Polynomial.natDegree_smul_le _ _)
          (le_of_eq (pairQuad_natDegree _ _))
    have hvan : ∀ t ∈ V, W.eval t = 0 := by
      intro t ht
      rw [hV] at ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      · -- at a ∈ P : live α (q_R-side) and β (q_Q-side)
        have h := hcombo a
        rw [dualVec_off domain (S := {b, b', c, c'}) (by
          rw [mem_quad]; push Not; exact ⟨hab, hab', hac, hac'⟩),
          mul_zero, add_zero] at h
        have hf := coord_forward domain haa hab hab' ha'b ha'b' hbb hac hac' ha'c
          ha'c' hcc h
        rw [hWeval]
        linear_combination hf
      · -- at a' ∈ P
        have h := hcombo a'
        rw [dualVec_off domain (S := {b, b', c, c'}) (by
          rw [mem_quad]; push Not; exact ⟨ha'b, ha'b', ha'c, ha'c'⟩),
          mul_zero, add_zero, quad_swap12 a a' b b', quad_swap12 a a' c c'] at h
        have hf := coord_forward domain haa.symm ha'b ha'b' hab hab' hbb ha'c ha'c'
          hac hac' hcc h
        rw [hWeval]
        linear_combination hf
      · -- at b ∈ Q : live α (S₁ pairs with q_R) and γ (S₃ pairs with q_P)
        have h := hcombo b
        rw [dualVec_off domain (S := {a, a', c, c'}) (by
          rw [mem_quad]; push Not
          exact ⟨hab.symm, ha'b.symm, hbc, hbc'⟩),
          mul_zero, add_zero, quad_rot a a' b b'] at h
        have hf := coord_forward domain hbb hab.symm ha'b.symm hab'.symm ha'b'.symm
          haa hbc hbc' hb'c hb'c' hcc h
        rw [hWeval]
        linear_combination hf
      · -- at b' ∈ Q
        have h := hcombo b'
        rw [dualVec_off domain (S := {a, a', c, c'}) (by
          rw [mem_quad]; push Not
          exact ⟨hab'.symm, ha'b'.symm, hb'c, hb'c'⟩),
          mul_zero, add_zero, quad_rot a a' b b', quad_swap12 b b' a a',
          quad_swap12 b b' c c'] at h
        have hf := coord_forward domain hbb.symm hab'.symm ha'b'.symm hab.symm
          ha'b.symm haa hb'c hb'c' hbc hbc' hcc h
        rw [hWeval]
        linear_combination hf
      · -- at c ∈ R : live β (S₂ pairs with q_Q) and γ (S₃ pairs with q_P)
        have h := hcombo c
        rw [dualVec_off domain (S := {a, a', b, b'}) (by
          rw [mem_quad]; push Not
          exact ⟨hac.symm, ha'c.symm, hbc.symm, hb'c.symm⟩),
          mul_zero, zero_add, quad_rot a a' c c', quad_rot b b' c c'] at h
        have hf := coord_forward domain hcc hac.symm ha'c.symm hac'.symm ha'c'.symm
          haa hbc.symm hb'c.symm hbc'.symm hb'c'.symm hbb h
        rw [hWeval]
        linear_combination hf
      · -- at c' ∈ R
        have h := hcombo c'
        rw [dualVec_off domain (S := {a, a', b, b'}) (by
          rw [mem_quad]; push Not
          exact ⟨hac'.symm, ha'c'.symm, hbc'.symm, hb'c'.symm⟩),
          mul_zero, zero_add, quad_rot a a' c c', quad_rot b b' c c',
          quad_swap12 c c' a a', quad_swap12 c c' b b'] at h
        have hf := coord_forward domain hcc.symm hac'.symm ha'c'.symm hac.symm
          ha'c.symm haa hbc'.symm hb'c'.symm hbc.symm hb'c.symm hbb h
        rw [hWeval]
        linear_combination hf
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' W V hvan
    rw [hVcard]
    omega
  · -- polynomial ⟹ vector
    intro hpoly
    intro i
    have hWv : ∀ t : F, α * ((t - domain c) * (t - domain c'))
        + β * ((t - domain b) * (t - domain b'))
        + γ * ((t - domain a) * (t - domain a')) = 0 := by
      intro t
      rw [← hWeval, hpoly]
      simp
    by_cases hia : i = a
    · rw [hia]
      rw [dualVec_off domain (S := {b, b', c, c'}) (by
        rw [mem_quad]; push Not; exact ⟨hab, hab', hac, hac'⟩), mul_zero, add_zero]
      exact coord_backward domain haa hab hab' ha'b ha'b' hbb hac hac' ha'c ha'c' hcc
        (by linear_combination hWv (domain a))
    · by_cases hia' : i = a'
      · rw [hia']
        rw [dualVec_off domain (S := {b, b', c, c'}) (by
          rw [mem_quad]; push Not; exact ⟨ha'b, ha'b', ha'c, ha'c'⟩), mul_zero,
          add_zero, quad_swap12 a a' b b', quad_swap12 a a' c c']
        exact coord_backward domain haa.symm ha'b ha'b' hab hab' hbb ha'c ha'c' hac
          hac' hcc (by linear_combination hWv (domain a'))
      · by_cases hib : i = b
        · rw [hib]
          rw [dualVec_off domain (S := {a, a', c, c'}) (by
            rw [mem_quad]; push Not
            exact ⟨hab.symm, ha'b.symm, hbc, hbc'⟩), mul_zero, add_zero,
            quad_rot a a' b b']
          exact coord_backward domain hbb hab.symm ha'b.symm hab'.symm ha'b'.symm haa
            hbc hbc' hb'c hb'c' hcc (by linear_combination hWv (domain b))
        · by_cases hib' : i = b'
          · rw [hib']
            rw [dualVec_off domain (S := {a, a', c, c'}) (by
              rw [mem_quad]; push Not
              exact ⟨hab'.symm, ha'b'.symm, hb'c, hb'c'⟩), mul_zero, add_zero,
              quad_rot a a' b b', quad_swap12 b b' a a', quad_swap12 b b' c c']
            exact coord_backward domain hbb.symm hab'.symm ha'b'.symm hab.symm
              ha'b.symm haa hb'c hb'c' hbc hbc' hcc
              (by linear_combination hWv (domain b'))
          · by_cases hic : i = c
            · rw [hic]
              rw [dualVec_off domain (S := {a, a', b, b'}) (by
                rw [mem_quad]; push Not
                exact ⟨hac.symm, ha'c.symm, hbc.symm, hb'c.symm⟩), mul_zero,
                zero_add, quad_rot a a' c c', quad_rot b b' c c']
              exact coord_backward domain hcc hac.symm ha'c.symm hac'.symm ha'c'.symm
                haa hbc.symm hb'c.symm hbc'.symm hb'c'.symm hbb
                (by linear_combination hWv (domain c))
            · by_cases hic' : i = c'
              · rw [hic']
                rw [dualVec_off domain (S := {a, a', b, b'}) (by
                  rw [mem_quad]; push Not
                  exact ⟨hac'.symm, ha'c'.symm, hbc'.symm, hb'c'.symm⟩), mul_zero,
                  zero_add, quad_rot a a' c c', quad_rot b b' c c',
                  quad_swap12 c c' a a', quad_swap12 c c' b b']
                exact coord_backward domain hcc.symm hac'.symm ha'c'.symm hac.symm
                  ha'c.symm haa hbc'.symm hb'c'.symm hbc.symm hb'c.symm hbb
                  (by linear_combination hWv (domain c'))
              · -- off all three sets
                rw [dualVec_off domain (S := {a, a', b, b'}) (by
                    rw [mem_quad]; push Not; exact ⟨hia, hia', hib, hib'⟩),
                  dualVec_off domain (S := {a, a', c, c'}) (by
                    rw [mem_quad]; push Not; exact ⟨hia, hia', hic, hic'⟩),
                  dualVec_off domain (S := {b, b', c, c'}) (by
                    rw [mem_quad]; push Not; exact ⟨hib, hib', hic, hic'⟩)]
                ring

/-- Disjoint pairs have distinct `(e, m)` invariants. -/
theorem pair_invariants_ne (hab : a ≠ b) (hab' : a ≠ b') :
    ¬(domain a + domain a' = domain b + domain b'
      ∧ domain a * domain a' = domain b * domain b') := by
  rintro ⟨he, hm⟩
  have h0 : (domain a - domain b) * (domain a - domain b') = 0 := by
    linear_combination domain a * he - hm
  rcases mul_eq_zero.mp h0 with h | h
  · exact hab (domain.injective (by linear_combination h))
  · exact hab' (domain.injective (by linear_combination h))

/-- The `(e, m)` normal form of the pair quadratic. -/
theorem pairQuad_eq (x y : F) :
    pairQuad x y = X ^ 2 - C (x + y) * X + C (x * y) := by
  rw [pairQuad, map_add, map_mul]
  ring

/-- **THE PENCIL CRITERION.** A nontrivial dependency of the pair-triangle duals exists
**iff** the three pair-points `(e, m) = (sum, product)` are collinear. -/
theorem dependent_iff_collinear (h6 : Distinct6 a a' b b' c c') :
    (∃ α β γ : F, ¬(α = 0 ∧ β = 0 ∧ γ = 0) ∧
      ∀ i, α * dualVec domain {a, a', b, b'} i + β * dualVec domain {a, a', c, c'} i
        + γ * dualVec domain {b, b', c, c'} i = 0)
      ↔ ((domain b + domain b') - (domain a + domain a'))
            * ((domain c * domain c') - (domain a * domain a'))
          = ((domain b * domain b') - (domain a * domain a'))
            * ((domain c + domain c') - (domain a + domain a')) := by
  have hform : ∀ α β γ : F,
      α • pairQuad (domain c) (domain c') + β • pairQuad (domain b) (domain b')
        + γ • pairQuad (domain a) (domain a')
      = C (α + β + γ) * X ^ 2
        + C (-(α * (domain c + domain c') + β * (domain b + domain b')
            + γ * (domain a + domain a'))) * X
        + C (α * (domain c * domain c') + β * (domain b * domain b')
            + γ * (domain a * domain a')) := by
    intro α β γ
    simp only [Polynomial.smul_eq_C_mul, pairQuad_eq, map_add, map_mul, map_neg]
    ring
  constructor
  · -- dependency ⟹ collinear
    rintro ⟨α, β, γ, hnz, hcombo⟩
    have hpoly := (dual_combo_eq_zero_iff domain h6 α β γ).mp hcombo
    rw [hform α β γ] at hpoly
    -- coefficient extraction
    have hc2 : α + β + γ = 0 := by
      have h := congrArg (fun p => Polynomial.coeff p 2) hpoly
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_zero] at h
      norm_num at h
      linear_combination h
    have hc1 : α * (domain c + domain c') + β * (domain b + domain b')
        + γ * (domain a + domain a') = 0 := by
      have h := congrArg (fun p => Polynomial.coeff p 1) hpoly
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_zero] at h
      norm_num at h
      linear_combination -h
    have hc0 : α * (domain c * domain c') + β * (domain b * domain b')
        + γ * (domain a * domain a') = 0 := by
      have h := congrArg (fun p => Polynomial.coeff p 0) hpoly
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_zero] at h
      norm_num at h
      linear_combination h
    -- eliminate γ
    have hαβ : ¬(α = 0 ∧ β = 0) := by
      rintro ⟨h1, h2⟩
      exact hnz ⟨h1, h2, by rw [h1, h2] at hc2; linear_combination hc2⟩
    have h1' : α * ((domain c + domain c') - (domain a + domain a'))
        + β * ((domain b + domain b') - (domain a + domain a')) = 0 := by
      linear_combination hc1 - (domain a + domain a') * hc2
    have h2' : α * ((domain c * domain c') - (domain a * domain a'))
        + β * ((domain b * domain b') - (domain a * domain a')) = 0 := by
      linear_combination hc0 - (domain a * domain a') * hc2
    by_cases hα : α = 0
    · have hβ : β ≠ 0 := fun h => hαβ ⟨hα, h⟩
      rw [hα] at h1' h2'
      have hb1 : (domain b + domain b') - (domain a + domain a') = 0 := by
        rcases mul_eq_zero.mp (by linear_combination h1' :
          β * ((domain b + domain b') - (domain a + domain a')) = 0) with h | h
        · exact absurd h hβ
        · exact h
      have hb2 : (domain b * domain b') - (domain a * domain a') = 0 := by
        rcases mul_eq_zero.mp (by linear_combination h2' :
          β * ((domain b * domain b') - (domain a * domain a')) = 0) with h | h
        · exact absurd h hβ
        · exact h
      rw [hb1, hb2]
      ring
    · have key : α * (((domain b + domain b') - (domain a + domain a'))
          * ((domain c * domain c') - (domain a * domain a'))
          - ((domain b * domain b') - (domain a * domain a'))
          * ((domain c + domain c') - (domain a + domain a'))) = 0 := by
        linear_combination ((domain b + domain b') - (domain a + domain a')) * h2'
          - ((domain b * domain b') - (domain a * domain a')) * h1'
      rcases mul_eq_zero.mp key with h | h
      · exact absurd h hα
      · linear_combination h
  · -- collinear ⟹ dependency
    intro hcol
    by_cases he : (domain a + domain a') = (domain b + domain b')
        ∧ (domain a + domain a') = (domain c + domain c')
    · -- all pair-sums equal: use the product differences
      refine ⟨(domain b * domain b') - (domain a * domain a'),
        (domain a * domain a') - (domain c * domain c'),
        (domain c * domain c') - (domain b * domain b'), ?_, ?_⟩
      · rintro ⟨h1, h2, -⟩
        have hmab : domain a * domain a' = domain b * domain b' := by
          linear_combination -h1
        exact pair_invariants_ne domain h6.hab h6.hab' ⟨he.1, hmab⟩
      · rw [dual_combo_eq_zero_iff domain h6, hform]
        have hz2 : ((domain b * domain b') - (domain a * domain a'))
            + ((domain a * domain a') - (domain c * domain c'))
            + ((domain c * domain c') - (domain b * domain b')) = 0 := by ring
        have hz1 : ((domain b * domain b') - (domain a * domain a'))
              * (domain c + domain c')
            + ((domain a * domain a') - (domain c * domain c'))
              * (domain b + domain b')
            + ((domain c * domain c') - (domain b * domain b'))
              * (domain a + domain a') = 0 := by
          linear_combination ((domain c * domain c') - (domain a * domain a')) * he.1
            + ((domain a * domain a') - (domain b * domain b')) * he.2
        have hz0 : ((domain b * domain b') - (domain a * domain a'))
              * (domain c * domain c')
            + ((domain a * domain a') - (domain c * domain c'))
              * (domain b * domain b')
            + ((domain c * domain c') - (domain b * domain b'))
              * (domain a * domain a') = 0 := by ring
        rw [hz2, hz1, hz0]
        simp
    · -- not all pair-sums equal: use the sum differences
      refine ⟨(domain b + domain b') - (domain a + domain a'),
        (domain a + domain a') - (domain c + domain c'),
        (domain c + domain c') - (domain b + domain b'), ?_, ?_⟩
      · rintro ⟨h1, h2, -⟩
        exact he ⟨by linear_combination -h1, by linear_combination h2⟩
      · rw [dual_combo_eq_zero_iff domain h6, hform]
        have hz2 : ((domain b + domain b') - (domain a + domain a'))
            + ((domain a + domain a') - (domain c + domain c'))
            + ((domain c + domain c') - (domain b + domain b')) = 0 := by ring
        have hz1 : ((domain b + domain b') - (domain a + domain a'))
              * (domain c + domain c')
            + ((domain a + domain a') - (domain c + domain c'))
              * (domain b + domain b')
            + ((domain c + domain c') - (domain b + domain b'))
              * (domain a + domain a') = 0 := by ring
        have hz0 : ((domain b + domain b') - (domain a + domain a'))
              * (domain c * domain c')
            + ((domain a + domain a') - (domain c + domain c'))
              * (domain b * domain b')
            + ((domain c + domain c') - (domain b + domain b'))
              * (domain a * domain a') = 0 := by
          linear_combination hcol
        rw [hz2, hz1, hz0]
        simp

/-! ## Source audit -/

#print axioms dualVec_coord
#print axioms coord_identity
#print axioms dual_combo_eq_zero_iff
#print axioms pair_invariants_ne
#print axioms dependent_iff_collinear

end Triangle

end ProximityGap.MCADualPencilLaw

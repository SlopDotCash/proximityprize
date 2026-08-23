/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandMultiplicity

/-!
# The sheared-subplane supply floor (#389): every subfield obstructs, at every band

Companion to `FrobeniusSubfieldBlowup.lean` (the prime-subfield secant family: charter
floor at the single tuned band `2+m+1 = p`, over `AffClosed` domains) and to
`AffinePlaneSharpness.lean` (the abstract set-system pole at `t² = s·n`).  This file
closes the two gaps those leave:

1. **Composite subfields.**  The blowup needs only SOME finite subfield `K ⊆ F`,
   `r = |K|` any prime power — not the prime subfield.  In characteristic 2 the
   Frobenius-secant mechanism is vacuous (`t = p = 2` cannot fill a `(2+m+1)`-core),
   while here `K = 𝔽_{2^j}` gives `t = 2^j` at every `j`: **binary-tower fields (the
   char-2 production setting) carry the sub-Johnson supply explosion whenever the
   evaluation domain contains a sheared `K`-plane.**
2. **Every band at once.**  The floor holds for ALL `m` with `2+m+1 ≤ r`
   simultaneously (each line contributes `C(r, 2+m+1)` cores), not at one tuned band.

The ambient field is an arbitrary extension of `K`, so `q/n` is unbounded: largeness
of the field alone cannot rescue the supply statement.

The construction (`k = 2`, lines).  Let `K ⊆ F` be a finite subfield, `r = |K|`, and
`λ ∈ F \ K`.  Shear the affine plane `K × K` into `F` by `(a, b) ↦ a + λ·b`:

* the map is injective (else `λ = (a' − a)/(b − b') ∈ K`), giving a domain of
  `n = r²` distinct points;
* the word is the second coordinate, `w(a + λ·b) = b`;
* every `K`-line maps onto the agreement set of an honest degree-`< 2` codeword:
  `{b = s·a + c}` becomes `y = (s·x + c)/(1 + λ·s)` (note `1 + λ·s ≠ 0` since
  `λ ∉ K`), and the vertical `{a = a₀}` becomes `y = (x − a₀)/λ`.

So the word `w` carries the full affine plane `AG(2, r)`: `r² + r` codewords each
agreeing with `w` on exactly `r = √n` points, pairwise sharing at most one point —
the projective-plane extremal configuration, as Reed–Solomon agreement geometry.
Each line contributes `C(r, m+3)` explainable cores and distinct lines contribute
disjoint core families, hence:

* `subplane_supply_floor` — **any `B` with `ExplainableCoreSupply dom 2 m B`
  satisfies `(r² + r)·C(r, 2+m+1) ≤ B`.**

Consequences for the issue (logged as the addendum to the 2026-06-13 Frobenius entry
in `DISPROOF_LOG.md`):
* at band `m` the floor is `(r²+r)·C(r, 2+m+1) ≈ n^{(m+3)/2}` — superpolynomial in
  `n` at every fixed band depth, against every landed `O(n)`-shaped target;
* the word satisfies every hypothesis used by the landed combinatorial routes
  (pairwise `≤ 1` intersections, sizes `√n`, sub-Johnson `t² = n < 2(k−1)·n`);
* what it does NOT survive: prime fields (no proper subfield) and domains without
  affine `K`-plane substructure (e.g., conjecturally, `μ_n`) — the wall's remaining
  open content is exactly the absence of additive subfield structure in the domain.

Probe: `scripts/probes/probe_subplane_supply.py` (exact at `F₉/K=F₃`, `F₂₇/K=F₃`,
`F₁₆/K=F₄`: agreement histogram `{0, 1, r}` only; rich-line count exactly `r(r+1)`).
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

section Subplane

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

variable (K : Subfield F) [Fintype K] (lam : F)

/-- The sheared planar point of a pair `(a, b) ∈ K × K`: the field element `a + λ·b`. -/
def subplanePt (p : K × K) : F := (p.1 : F) + lam * (p.2 : F)

omit [Fintype F] [Fintype K] in
/-- For `λ ∉ K` the shear is injective: `a + λ·b = a' + λ·b'` with `b ≠ b'` would
solve `λ = (a' − a)/(b − b') ∈ K`. -/
theorem subplanePt_injective (hlam : lam ∉ K) :
    Function.Injective (subplanePt K lam) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [subplanePt] at h
  by_cases hbb : b = b'
  · subst hbb
    have ha : (a : F) = (a' : F) := by
      have h' : (a : F) + lam * (b : F) = (a' : F) + lam * (b : F) := h
      exact add_right_cancel h'
    rw [Subtype.coe_injective ha]
  · exfalso
    apply hlam
    have hbF : (b : F) ≠ (b' : F) := fun hc => hbb (Subtype.coe_injective hc)
    have hb : ((b : F) - (b' : F)) ≠ 0 := sub_ne_zero.mpr hbF
    have hl : lam = (((a' - a) / (b - b') : K) : F) := by
      push_cast
      rw [eq_div_iff hb]
      linear_combination h
    rw [hl]
    exact SetLike.coe_mem _

instance instNeZeroSubplaneCard {K : Subfield F} [Fintype K] :
    NeZero (Fintype.card (K × K)) :=
  ⟨by
    haveI : Nonempty (K × K) := ⟨(0, 0)⟩
    exact Fintype.card_ne_zero⟩

/-- The subplane evaluation domain: an enumeration of the `r²` sheared points. -/
noncomputable def subplaneDom (hlam : lam ∉ K) : Fin (Fintype.card (K × K)) ↪ F :=
  ⟨fun i => subplanePt K lam ((Fintype.equivFin (K × K)).symm i),
    (subplanePt_injective K lam hlam).comp (Equiv.injective _)⟩

/-- The subplane word: the second (unsheared) coordinate of each domain point. -/
noncomputable def subplaneWord (i : Fin (Fintype.card (K × K))) : F :=
  ((((Fintype.equivFin (K × K)).symm i)).2 : F)

/-- Index type for the `r² + r` lines of `AG(2, K)`: non-vertical `(slope, intercept)`
pairs plus vertical lines. -/
abbrev LineIdx (K : Subfield F) [Fintype K] : Type := (K × K) ⊕ K

/-- The incidence predicate of `AG(2, K)`. -/
def onLine : LineIdx K → K × K → Prop
  | Sum.inl sc => fun p => p.2 = sc.1 * p.1 + sc.2
  | Sum.inr a₀ => fun p => p.1 = a₀

omit [Fintype F] [Fintype K] in
/-- `1 + λ·s ≠ 0` for `s ∈ K`, since `λ ∉ K`. -/
theorem one_add_lam_mul_ne_zero (hlam : lam ∉ K) (s : K) :
    (1 : F) + lam * (s : F) ≠ 0 := by
  intro h
  by_cases hs : s = 0
  · subst hs
    rw [ZeroMemClass.coe_zero, mul_zero, add_zero] at h
    exact one_ne_zero h
  · apply hlam
    have hsF : (s : F) ≠ 0 := fun hc => hs (by exact_mod_cast hc)
    have hl : lam = ((-1 / s : K) : F) := by
      push_cast
      rw [eq_div_iff hsF]
      linear_combination h
    rw [hl]
    exact SetLike.coe_mem _

omit [Fintype F] [DecidableEq F] [Fintype K] in
/-- `λ ≠ 0`, since `0 ∈ K`. -/
theorem lam_ne_zero (hlam : lam ∉ K) : lam ≠ 0 := fun h => hlam (h ▸ K.zero_mem)

/-- The degree-`< 2` polynomial whose graph contains the sheared image of a `K`-line. -/
noncomputable def linePoly : LineIdx K → Polynomial F
  | Sum.inl sc => Polynomial.C ((sc.1 : F) / (1 + lam * (sc.1 : F))) * Polynomial.X
      + Polynomial.C ((sc.2 : F) / (1 + lam * (sc.1 : F)))
  | Sum.inr a₀ => Polynomial.C lam⁻¹ * Polynomial.X + Polynomial.C (-(a₀ : F) / lam)

omit [Fintype F] in
/-- **The agreement law**: the line polynomial of `j` matches the word at a sheared
point exactly when the pair lies on the `K`-line `j`. -/
theorem linePoly_eval_eq_iff (hlam : lam ∉ K) (j : LineIdx K) (p : K × K) :
    (linePoly K lam j).eval (subplanePt K lam p) = (p.2 : F) ↔ onLine K j p := by
  obtain ⟨a, b⟩ := p
  cases j with
  | inl sc =>
    obtain ⟨s, c⟩ := sc
    have hden := one_add_lam_mul_ne_zero K lam hlam s
    simp only [linePoly, onLine, subplanePt, eval_add, eval_mul, eval_C, eval_X]
    rw [div_mul_eq_mul_div, ← add_div, div_eq_iff hden]
    constructor
    · intro h
      have hF : (b : F) = (s : F) * (a : F) + (c : F) := by linear_combination -h
      exact Subtype.coe_injective (by push_cast; exact hF)
    · intro h
      have hF : (b : F) = (s : F) * (a : F) + (c : F) := by exact_mod_cast h
      linear_combination -hF
  | inr a₀ =>
    have hl0 := lam_ne_zero K lam hlam
    simp only [linePoly, onLine, subplanePt, eval_add, eval_mul, eval_C, eval_X]
    rw [inv_mul_eq_div, ← add_div, div_eq_iff hl0]
    constructor
    · intro h
      have hF : (a : F) = (a₀ : F) := by linear_combination h
      exact Subtype.coe_injective hF
    · intro h
      have hF : (a : F) = (a₀ : F) := by exact_mod_cast h
      linear_combination hF

open Classical in
/-- The agreement index set of line `j`: domain indices whose pair lies on the line. -/
noncomputable def agreeIdx (j : LineIdx K) : Finset (Fin (Fintype.card (K × K))) :=
  Finset.univ.filter (fun i => onLine K j ((Fintype.equivFin (K × K)).symm i))

omit [Fintype F] [DecidableEq F] in
theorem mem_agreeIdx {j : LineIdx K} {i : Fin (Fintype.card (K × K))} :
    i ∈ agreeIdx K j ↔ onLine K j ((Fintype.equivFin (K × K)).symm i) := by
  simp [agreeIdx]

omit [Fintype F] in
/-- Each `K`-line carries exactly `|K|` domain points. -/
theorem card_agreeIdx (j : LineIdx K) : (agreeIdx K j).card = Fintype.card K := by
  classical
  have himg : agreeIdx K j
      = (Finset.univ.filter (fun p : K × K => onLine K j p)).image
          (Fintype.equivFin (K × K)) := by
    ext i
    simp only [mem_agreeIdx, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro h
      exact ⟨(Fintype.equivFin (K × K)).symm i, h, Equiv.apply_symm_apply _ _⟩
    · rintro ⟨p, hp, rfl⟩
      simpa using hp
  rw [himg, Finset.card_image_of_injective _ (Equiv.injective _)]
  cases j with
  | inl sc =>
    obtain ⟨s, c⟩ := sc
    have himg2 : (Finset.univ.filter (fun p : K × K => onLine K (Sum.inl (s, c)) p))
        = Finset.univ.image (fun a : K => (a, s * a + c)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, onLine]
      constructor
      · intro h
        exact ⟨a, by rw [h]⟩
      · rintro ⟨a', ha'⟩
        injection ha' with h1 h2
        subst h1
        exact h2.symm
    rw [himg2, Finset.card_image_of_injective _ (fun x y hxy => congrArg Prod.fst hxy)]
    exact Finset.card_univ
  | inr a₀ =>
    have himg2 : (Finset.univ.filter (fun p : K × K => onLine K (Sum.inr a₀) p))
        = Finset.univ.image (fun b : K => (a₀, b)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, onLine]
      constructor
      · intro h
        exact ⟨b, by rw [h]⟩
      · rintro ⟨b', hb'⟩
        injection hb' with h1 h2
        exact h1.symm
    rw [himg2, Finset.card_image_of_injective _ (fun x y hxy => congrArg Prod.snd hxy)]
    exact Finset.card_univ

omit [Fintype F] in
/-- Two distinct `K`-lines share at most one point of the plane. -/
theorem onLine_unique {j j' : LineIdx K} (hjj : j ≠ j') {p p' : K × K}
    (h1 : onLine K j p) (h2 : onLine K j' p) (h3 : onLine K j p') (h4 : onLine K j' p') :
    p = p' := by
  obtain ⟨a, b⟩ := p
  obtain ⟨a', b'⟩ := p'
  cases j with
  | inl sc =>
    obtain ⟨s, c⟩ := sc
    cases j' with
    | inl sc' =>
      obtain ⟨s', c'⟩ := sc'
      simp only [onLine] at h1 h2 h3 h4
      by_cases hss : s = s'
      · subst hss
        exact absurd (by rw [show c = c' from by linear_combination h2 - h1]) hjj
      · have hs : s - s' ≠ 0 := sub_ne_zero.mpr hss
        have ha : a = a' := by
          have key : (s - s') * a = (s - s') * a' := by
            linear_combination h2 - h1 + h3 - h4
          exact mul_left_cancel₀ hs key
        subst ha
        have hb : b = b' := by linear_combination h1 - h3
        rw [hb]
    | inr a₀' =>
      simp only [onLine] at h1 h2 h3 h4
      have ha : a = a' := h2.trans h4.symm
      subst ha
      have hb : b = b' := by linear_combination h1 - h3
      rw [hb]
  | inr a₀ =>
    cases j' with
    | inl sc' =>
      obtain ⟨s', c'⟩ := sc'
      simp only [onLine] at h1 h2 h3 h4
      have ha : a = a' := h1.trans h3.symm
      subst ha
      have hb : b = b' := by linear_combination h2 - h4
      rw [hb]
    | inr a₀' =>
      simp only [onLine] at h1 h2 h3 h4
      exact absurd (by rw [show a₀ = a₀' from h1.symm.trans h2]) hjj

omit [Fintype F] in
/-- Distinct lines share at most one domain index. -/
theorem agreeIdx_inter_card_le_one {j j' : LineIdx K} (hjj : j ≠ j') :
    ((agreeIdx K j) ∩ (agreeIdx K j')).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro i hi i' hi'
  rw [Finset.mem_inter, mem_agreeIdx, mem_agreeIdx] at hi hi'
  have hpp := onLine_unique K hjj hi.1 hi.2 hi'.1 hi'.2
  exact (Fintype.equivFin (K × K)).symm.injective hpp

omit [Fintype F] in
/-- The line polynomial evaluates to a codeword of `rsCode dom 2`. -/
theorem linePoly_mem (hlam : lam ∉ K) (j : LineIdx K) :
    (fun i => (linePoly K lam j).eval (subplaneDom K lam hlam i))
      ∈ (rsCode (subplaneDom K lam hlam) 2 :
          Submodule F (Fin (Fintype.card (K × K)) → F)) := by
  refine ⟨linePoly K lam j, ?_, rfl⟩
  have hle : (linePoly K lam j).degree ≤ 1 := by
    cases j with
    | inl sc => exact degree_linear_le
    | inr a₀ => exact degree_linear_le
  exact lt_of_le_of_lt hle (by exact_mod_cast Nat.one_lt_two)

open Classical in
omit [Fintype F] in
/-- **The sheared-subplane supply floor.**  Any admissible per-word core supply `B`
for `rsCode dom 2` on the subplane domain dominates the affine-plane count
`(r² + r)·C(r, 2+m+1)`: the word `w(a + λ·b) = b` carries `r² + r` codewords of
agreement exactly `r` with pairwise intersections `≤ 1`, whose `(2+m+1)`-cores are
all explainable and pairwise distinct across lines. -/
theorem subplane_supply_floor (hlam : lam ∉ K) {m B : ℕ}
    (hB : ExplainableCoreSupply (subplaneDom K lam hlam) 2 m B) :
    (Fintype.card K * Fintype.card K + Fintype.card K)
      * (Fintype.card K).choose (2 + m + 1) ≤ B := by
  have hword := hB (subplaneWord K)
  refine le_trans ?_ hword
  have hdisj : ∀ j ∈ (Finset.univ : Finset (LineIdx K)),
      ∀ j' ∈ (Finset.univ : Finset (LineIdx K)), j ≠ j' →
      Disjoint ((agreeIdx K j).powersetCard (2 + m + 1))
        ((agreeIdx K j').powersetCard (2 + m + 1)) := by
    intro j _ j' _ hjj
    rw [Finset.disjoint_left]
    intro T hT hT'
    rw [Finset.mem_powersetCard] at hT hT'
    have hsub : T ⊆ (agreeIdx K j) ∩ (agreeIdx K j') := Finset.subset_inter hT.1 hT'.1
    have hcard := Finset.card_le_card hsub
    have hle1 := agreeIdx_inter_card_le_one K hjj
    have hTcard := hT.2
    omega
  calc (Fintype.card K * Fintype.card K + Fintype.card K)
        * (Fintype.card K).choose (2 + m + 1)
      = ∑ _j : LineIdx K, (Fintype.card K).choose (2 + m + 1) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        congr 1
        simp [Fintype.card_sum, Fintype.card_prod]
    _ = ∑ j : LineIdx K, ((agreeIdx K j).powersetCard (2 + m + 1)).card := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.card_powersetCard, card_agreeIdx]
    _ = ((Finset.univ : Finset (LineIdx K)).biUnion
          (fun j => (agreeIdx K j).powersetCard (2 + m + 1))).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ _ := by
        apply Finset.card_le_card
        intro T hT
        rw [Finset.mem_biUnion] at hT
        obtain ⟨j, _, hTj⟩ := hT
        rw [Finset.mem_powersetCard] at hTj
        rw [Finset.mem_filter, Finset.mem_powersetCard]
        refine ⟨⟨Finset.subset_univ _, hTj.2⟩, ?_⟩
        refine ⟨fun i => (linePoly K lam j).eval (subplaneDom K lam hlam i),
          linePoly_mem K lam hlam j, ?_⟩
        intro i hiT
        have hi := hTj.1 hiT
        rw [mem_agreeIdx] at hi
        exact (linePoly_eval_eq_iff K lam hlam j _).mpr hi

end Subplane

end ProximityGap.Ownership

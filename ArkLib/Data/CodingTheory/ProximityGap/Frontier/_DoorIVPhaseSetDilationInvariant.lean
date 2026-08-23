/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Door IV (Lane 1, the brief's verbatim small-ball target): the worst-b phase set `{b·x : x∈μ_n}` has
# DILATION-INVARIANT additive structure — the worst `b` cannot tune it, so any small-ball / Halász
# lever is b-independent and reproduces the (dead) EVT/Plancherel ceiling, never beats the wall

This file records the axiom-clean kernel behind the probe
`scripts/probes/probe_dooriv_phaseset_additive_smallball.py`.

## Why this matters (the brief's literal Lane-1 question)

The brief asks verbatim: "how spread is `{b·x^m mod p}`? Any Littlewood–Offord / Halász-type
small-ball bound for this phase set that does NOT route through multiplicative energy?" This is the
ADDITIVE structure of the x-side phase-residue set `S_b = {b·x : x ∈ μ_n} ⊆ 𝔽_p` (distinct from the
b-side worst-set `ae2bc7e0b` and the complex-alignment participation `78d1df596`).

`S_b = b · μ_n` is a multiplicative DILATE of the subgroup. Its additive energy
`E⁺(S) = #{(a,b,c,d) ∈ S⁴ : a + b = c + d}` is the natural small-ball / Halász input. The probe
(PROPER `μ_n`, p≈n⁴≫n³, EXACT bignum, never n=q−1) found:

  * `E⁺(μ_n)/n²` is FLAT at a small constant (2.81, 2.91, 2.95 for n=16,32,64) — does NOT grow with
    `n`: the phase set is additively SPREAD (Sidon-like up to a constant), NOT additively structured.
  * sumset doubling `|S+S|/n ≈ n/2` (8.06, 16.03, 32.02) = the Sidon signature `|S+S| ≈ |S|²/2`.
  * the arc small-ball `ρ*` DECAYS (0.75 → 0.25 → 0.078): the residues spread, no concentration.
  * the worst-b sum sits at the EVT/Plancherel ceiling `M/√(n·log(p/n)) ≈ 1.2–1.36`.

So the Halász/small-ball bound derived from `E⁺` reproduces `|η_b| ≲ √(n·log)` = the SAME EVT ceiling
— it does NOT beat the wall and does NOT avoid the moment route. And crucially: `E⁺(b·μ_n)` does NOT
depend on `b` (dilation-invariance), so the WORST `b` cannot tune the additive structure to do better.
The additive energy of a multiplicative subgroup IS a multiplicative-energy object. Mapped wall, not
a non-moment lever.

## The formalizable kernel (this file): dilation-invariance of additive energy

The exact structural fact making the small-ball lever b-blind: for a unit `λ` (here `λ = b`),
multiplication-by-`λ` is a bijection of `𝔽_p` that preserves the additive-quadruple relation
`a + b = c + d ⟺ λ·a + λ·b = λ·c + λ·d`. Hence `E⁺(λ • S) = E⁺(S)`. We model `E⁺` as the cardinality
of the quadruple solution set inside `S⁴` and prove the dilate has the SAME count via the
mul-by-`λ⁻¹` bijection on the index `Finset`. Consequence: any bound on `|η_b|` factoring through
`E⁺(S_b)` is `b`-independent — the worst `b` inherits the typical (EVT) ceiling.
-/

set_option linter.style.longLine false


namespace ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant

open Finset

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- The additive-quadruple solution set of a finite set `S ⊆ F`:
`{(a,b,c,d) ∈ S⁴ : a + b = c + d}`, whose cardinality is the additive energy `E⁺(S)`. -/
def addQuadruples (S : Finset F) : Finset (F × F × F × F) :=
  (S ×ˢ S ×ˢ S ×ˢ S).filter (fun q => q.1 + q.2.1 = q.2.2.1 + q.2.2.2)

/-- Additive energy `E⁺(S) = #{(a,b,c,d) ∈ S⁴ : a+b=c+d}`. -/
def addEnergy (S : Finset F) : ℕ := (addQuadruples S).card


/-- Additive sumset `S + S`, used by the small-ball/doubling probe. -/
def addSumset (S : Finset F) : Finset F :=
  (S ×ˢ S).image (fun p => p.1 + p.2)

/-- Dilation commutes exactly with the additive sumset: `(λS)+(λS)=λ(S+S)`. -/
theorem addSumset_smul_eq_image (S : Finset F) (lam : F) :
    addSumset (S.image (fun x => lam * x)) = (addSumset S).image (fun x => lam * x) := by
  classical
  ext y
  simp [addSumset, mul_add]
  aesop

/-- Nonzero dilation preserves additive doubling cardinality.  Thus the observed `|bS+bS|/|S|`
small-ball input is also worst-frequency-blind: changing `b` cannot improve or worsen the sumset
size of the phase residue set. -/
theorem addSumset_card_smul_eq (S : Finset F) {lam : F} (hlam : lam ≠ 0) :
    (addSumset (S.image (fun x => lam * x))).card = (addSumset S).card := by
  classical
  rw [addSumset_smul_eq_image]
  exact Finset.card_image_of_injOn (s := addSumset S) (f := fun x => lam * x) (by
    intro x _ y _ hxy
    exact mul_left_cancel₀ hlam hxy)

/-- Two nonzero frequency dilates have the same additive sumset cardinal.  This is the exact formal
counterpart of the probe verdict: additive-doubling/arc-small-ball data of `{b*x^m}` is a property
of the subgroup, not of the adversarial worst `b`. -/
theorem addSumset_card_phaseSet_indep_of_scalar
    (S : Finset F) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    (addSumset (S.image (fun x => b₁ * x))).card =
      (addSumset (S.image (fun x => b₂ * x))).card := by
  rw [addSumset_card_smul_eq S hb₁, addSumset_card_smul_eq S hb₂]


/-- Additive difference set `S - S`, the pair-spacing support seen by pair-collision and
Littlewood-Offord small-ball arguments. -/
def addDiffset (S : Finset F) : Finset F :=
  (S ×ˢ S).image (fun p => p.1 - p.2)

/-- Dilation commutes exactly with the additive difference set: `λS - λS = λ(S - S)`. -/
theorem addDiffset_smul_eq_image (S : Finset F) (lam : F) :
    addDiffset (S.image (fun x => lam * x)) = (addDiffset S).image (fun x => lam * x) := by
  classical
  ext y
  simp [addDiffset, mul_sub]
  aesop

/-- Nonzero dilation preserves additive difference-set cardinality.  Thus pair-spacing support of
`{b*x^m}` is also independent of the adversarial frequency. -/
theorem addDiffset_card_smul_eq (S : Finset F) {lam : F} (hlam : lam ≠ 0) :
    (addDiffset (S.image (fun x => lam * x))).card = (addDiffset S).card := by
  classical
  rw [addDiffset_smul_eq_image]
  exact Finset.card_image_of_injOn (s := addDiffset S) (f := fun x => lam * x) (by
    intro x _ y _ hxy
    exact mul_left_cancel₀ hlam hxy)

/-- Two nonzero frequency dilates have the same additive difference-set cardinal.  This rules out a
worst-b selector based purely on pair-spacing support or difference-set expansion. -/
theorem addDiffset_card_phaseSet_indep_of_scalar
    (S : Finset F) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    (addDiffset (S.image (fun x => b₁ * x))).card =
      (addDiffset (S.image (fun x => b₂ * x))).card := by
  rw [addDiffset_card_smul_eq S hb₁, addDiffset_card_smul_eq S hb₂]


/-- Pair-sum representation count at target `t`: `#{(a,b) in S^2 : a+b=t}`. -/
def addPairSumCount (S : Finset F) (t : F) : ℕ :=
  ((S ×ˢ S).filter (fun p => p.1 + p.2 = t)).card

/-- Nonzero dilation preserves each pair-sum fiber, after dilating the target.  This is the exact
multiplicity-level version of sumset-cardinality invariance: not only the support `S+S`, but every
representation count is transported by `t ↦ λt`. -/
theorem addPairSumCount_smul_eq (S : Finset F) {lam t : F} (hlam : lam ≠ 0) :
    addPairSumCount (S.image (fun x => lam * x)) (lam * t) = addPairSumCount S t := by
  classical
  unfold addPairSumCount
  have hcdiv : ∀ z : F, lam⁻¹ * (lam * z) = z := fun z => by
    rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  have hcmul : ∀ z : F, lam * (lam⁻¹ * z) = z := fun z => by
    rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
  refine Finset.card_nbij'
    (fun p => (lam⁻¹ * p.1, lam⁻¹ * p.2))
    (fun p => (lam * p.1, lam * p.2))
    ?_ ?_ ?_ ?_
  · intro p hp
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_image] at hp ⊢
    obtain ⟨⟨hp₁, hp₂⟩, hsum⟩ := hp
    obtain ⟨a, ha, hpa⟩ := hp₁
    obtain ⟨b, hb, hpb⟩ := hp₂
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa [← hpa, hcdiv] using ha
    · simpa [← hpb, hcdiv] using hb
    · apply mul_left_cancel₀ hlam
      simpa [mul_add, ← hpa, ← hpb, hcmul] using hsum
  · intro p hp
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_image] at hp ⊢
    obtain ⟨⟨hp₁, hp₂⟩, hsum⟩ := hp
    refine ⟨⟨⟨p.1, hp₁, rfl⟩, ⟨p.2, hp₂, rfl⟩⟩, ?_⟩
    rw [← mul_add, hsum]
  · intro p _
    simp [hcmul]
  · intro p _
    simp [hcdiv]

/-- The pair-sum multiplicity profile of two nonzero frequency dilates is identical after the obvious
rescaling of targets.  Pure pair-count/Halasz inputs therefore cannot distinguish the worst `b`. -/
theorem addPairSumCount_phaseSet_indep_of_scalar
    (S : Finset F) {b₁ b₂ t : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    addPairSumCount (S.image (fun x => b₁ * x)) (b₁ * t) =
      addPairSumCount (S.image (fun x => b₂ * x)) (b₂ * t) := by
  rw [addPairSumCount_smul_eq S hb₁, addPairSumCount_smul_eq S hb₂]



/-- Pair-difference representation count at target `t`: `#{(a,b) in S^2 : a-b=t}`.  This is the
multiplicity-level pair-spacing profile behind difference-set small-ball inputs. -/
def addPairDiffCount (S : Finset F) (t : F) : ℕ :=
  ((S ×ˢ S).filter (fun p => p.1 - p.2 = t)).card

/-- Nonzero dilation preserves each pair-difference fiber, after dilating the target.  Thus not only
the support `S-S`, but every pair-spacing multiplicity is transported by `t ↦ λt`. -/
theorem addPairDiffCount_smul_eq (S : Finset F) {lam t : F} (hlam : lam ≠ 0) :
    addPairDiffCount (S.image (fun x => lam * x)) (lam * t) = addPairDiffCount S t := by
  classical
  unfold addPairDiffCount
  have hcdiv : ∀ z : F, lam⁻¹ * (lam * z) = z := fun z => by
    rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  have hcmul : ∀ z : F, lam * (lam⁻¹ * z) = z := fun z => by
    rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
  refine Finset.card_nbij'
    (fun p => (lam⁻¹ * p.1, lam⁻¹ * p.2))
    (fun p => (lam * p.1, lam * p.2))
    ?_ ?_ ?_ ?_
  · intro p hp
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_image] at hp ⊢
    obtain ⟨⟨hp₁, hp₂⟩, hdiff⟩ := hp
    obtain ⟨a, ha, hpa⟩ := hp₁
    obtain ⟨b, hb, hpb⟩ := hp₂
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa [← hpa, hcdiv] using ha
    · simpa [← hpb, hcdiv] using hb
    · apply mul_left_cancel₀ hlam
      simpa [mul_sub, ← hpa, ← hpb, hcmul] using hdiff
  · intro p hp
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_image] at hp ⊢
    obtain ⟨⟨hp₁, hp₂⟩, hdiff⟩ := hp
    refine ⟨⟨⟨p.1, hp₁, rfl⟩, ⟨p.2, hp₂, rfl⟩⟩, ?_⟩
    rw [← mul_sub, hdiff]
  · intro p _
    simp [hcmul]
  · intro p _
    simp [hcdiv]

/-- The pair-difference multiplicity profile of two nonzero frequency dilates is identical after the
obvious target rescaling.  Pure spacing-multiplicity / autocorrelation inputs therefore cannot select
or distinguish the worst `b`. -/
theorem addPairDiffCount_phaseSet_indep_of_scalar
    (S : Finset F) {b₁ b₂ t : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    addPairDiffCount (S.image (fun x => b₁ * x)) (b₁ * t) =
      addPairDiffCount (S.image (fun x => b₂ * x)) (b₂ * t) := by
  rw [addPairDiffCount_smul_eq S hb₁, addPairDiffCount_smul_eq S hb₂]



/-- Three-sum representation count at target `t`: `#{(a,b,c) in S^3 : a+b+c=t}`.
This is the next small-ball fiber after pair-sum multiplicities; it probes whether a 3-fold
Littlewood-Offord/Halász input can distinguish the adversarial frequency. -/
def addTripleSumCount (S : Finset F) (t : F) : ℕ :=
  ((S ×ˢ S ×ˢ S).filter (fun p => p.1 + p.2.1 + p.2.2 = t)).card

/-- Nonzero dilation preserves every three-sum fiber after dilating the target.  Thus the 3-fold
small-ball multiplicity profile of `{b*x^m}` is transported by `t ↦ b*t`; it is not a selector for
worst `b`. -/
theorem addTripleSumCount_smul_eq (S : Finset F) {lam t : F} (hlam : lam ≠ 0) :
    addTripleSumCount (S.image (fun x => lam * x)) (lam * t) = addTripleSumCount S t := by
  classical
  unfold addTripleSumCount
  have hcdiv : ∀ z : F, lam⁻¹ * (lam * z) = z := fun z => by
    rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  have hcmul : ∀ z : F, lam * (lam⁻¹ * z) = z := fun z => by
    rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
  refine Finset.card_nbij'
    (fun p => (lam⁻¹ * p.1, lam⁻¹ * p.2.1, lam⁻¹ * p.2.2))
    (fun p => (lam * p.1, lam * p.2.1, lam * p.2.2))
    ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c⟩ hp
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_image] at hp ⊢
    obtain ⟨⟨ha, hb, hc⟩, hsum⟩ := hp
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    obtain ⟨c', hc', rfl⟩ := hc
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simpa [hcdiv] using ha'
    · simpa [hcdiv] using hb'
    · simpa [hcdiv] using hc'
    · have hbase : a' + b' + c' = t := by
        apply mul_left_cancel₀ hlam
        calc
          lam * (a' + b' + c') = lam * a' + lam * b' + lam * c' := by ring
          _ = lam * t := hsum
      simpa [hcdiv] using hbase
  · rintro ⟨a, b, c⟩ hp
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_image] at hp ⊢
    obtain ⟨⟨ha, hb, hc⟩, hsum⟩ := hp
    refine ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, ⟨c, hc, rfl⟩⟩, ?_⟩
    rw [← hsum]
    ring
  · rintro ⟨a, b, c⟩ _
    simp [hcmul]
  · rintro ⟨a, b, c⟩ _
    simp [hcdiv]

/-- The three-sum multiplicity profile of two nonzero frequency dilates is identical after the
obvious target rescaling.  Pure 3-fold small-ball/Halász inputs therefore cannot distinguish or
select the worst `b`. -/
theorem addTripleSumCount_phaseSet_indep_of_scalar
    (S : Finset F) {b₁ b₂ t : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    addTripleSumCount (S.image (fun x => b₁ * x)) (b₁ * t) =
      addTripleSumCount (S.image (fun x => b₂ * x)) (b₂ * t) := by
  rw [addTripleSumCount_smul_eq S hb₁, addTripleSumCount_smul_eq S hb₂]


/-- Three-term arithmetic-progression count in `S`: triples `(a,b,c) ∈ S^3` with `a+c=2b`.
This is a basic homogeneous additive-linear pattern count, adjacent to small-ball/additive-structure
inputs but not tied to a target fiber. -/
def addThreeAPCount (S : Finset F) : ℕ :=
  ((S ×ˢ S ×ˢ S).filter (fun p => p.1 + p.2.2 = (2 : F) * p.2.1)).card

/-- Nonzero dilation preserves the three-term AP count.  Homogeneous additive-linear pattern counts
of the phase set are therefore frequency-blind: `bS` has exactly as many 3APs as `S`. -/
theorem addThreeAPCount_smul_eq (S : Finset F) {lam : F} (hlam : lam ≠ 0) :
    addThreeAPCount (S.image (fun x => lam * x)) = addThreeAPCount S := by
  classical
  unfold addThreeAPCount
  have hcdiv : ∀ z : F, lam⁻¹ * (lam * z) = z := fun z => by
    rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  have hcmul : ∀ z : F, lam * (lam⁻¹ * z) = z := fun z => by
    rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
  refine Finset.card_nbij'
    (fun p => (lam⁻¹ * p.1, lam⁻¹ * p.2.1, lam⁻¹ * p.2.2))
    (fun p => (lam * p.1, lam * p.2.1, lam * p.2.2))
    ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c⟩ hp
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_image] at hp ⊢
    obtain ⟨⟨ha, hb, hc⟩, hap⟩ := hp
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    obtain ⟨c', hc', rfl⟩ := hc
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simpa [hcdiv] using ha'
    · simpa [hcdiv] using hb'
    · simpa [hcdiv] using hc'
    · have hbase : a' + c' = (2 : F) * b' := by
        apply mul_left_cancel₀ hlam
        calc
          lam * (a' + c') = lam * a' + lam * c' := by rw [mul_add]
          _ = (2 : F) * (lam * b') := hap
          _ = lam * ((2 : F) * b') := by ring
      simpa [hcdiv] using hbase
  · rintro ⟨a, b, c⟩ hp
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_image] at hp ⊢
    obtain ⟨⟨ha, hb, hc⟩, hap⟩ := hp
    refine ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, ⟨c, hc, rfl⟩⟩, ?_⟩
    rw [← mul_add, hap]
    ring
  · rintro ⟨a, b, c⟩ _
    simp [hcmul]
  · rintro ⟨a, b, c⟩ _
    simp [hcdiv]

/-- Two nonzero frequency dilates have the same three-term AP count.  A door-(iv) anti-concentration
argument cannot select the worst frequency using this homogeneous additive-pattern statistic. -/
theorem addThreeAPCount_phaseSet_indep_of_scalar
    (S : Finset F) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    addThreeAPCount (S.image (fun x => b₁ * x)) =
      addThreeAPCount (S.image (fun x => b₂ * x)) := by
  rw [addThreeAPCount_smul_eq S hb₁, addThreeAPCount_smul_eq S hb₂]



/-- General finite linear-pattern/fiber count on `S^k`: the number of functions `v : Fin k → F`
whose coordinates all lie in `S` and whose weighted additive linear form is the target `t`.
This packages the one-off pair-sum, pair-difference, three-sum, and homogeneous AP counts into the
actual Littlewood-Offord/Halász template: a fixed linear equation in finitely many phase residues. -/
def addLinearPatternCount {k : ℕ} (S : Finset F) (coeff : Fin k → F) (t : F) : ℕ :=
  ((Finset.univ : Finset (Fin k → F)).filter
    (fun v => (∀ i : Fin k, v i ∈ S) ∧ (∑ i : Fin k, coeff i * v i) = t)).card

/-- Nonzero dilation preserves every fixed additive-linear pattern fiber after dilating the target.
Equivalently, multiplication by `λ` transports the solution set for `S` and target `t` bijectively
onto the solution set for `λS` and target `λt`.  Thus any small-ball / Halász input that only counts
solutions to a fixed linear equation in the phase set `{b*x^m}` is frequency-blind, not a selector for
the adversarial worst `b`. -/
theorem addLinearPatternCount_smul_eq {k : ℕ} (S : Finset F) (coeff : Fin k → F)
    {lam t : F} (hlam : lam ≠ 0) :
    addLinearPatternCount (S.image (fun x => lam * x)) coeff (lam * t) =
      addLinearPatternCount S coeff t := by
  classical
  unfold addLinearPatternCount
  have hcdiv : ∀ z : F, lam⁻¹ * (lam * z) = z := fun z => by
    rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  have hcmul : ∀ z : F, lam * (lam⁻¹ * z) = z := fun z => by
    rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
  refine Finset.card_nbij'
    (fun v i => lam⁻¹ * v i)
    (fun v i => lam * v i)
    ?_ ?_ ?_ ?_
  · intro v hv
    simp only [coe_filter, mem_univ, true_and] at hv ⊢
    obtain ⟨hmem, hlin⟩ := hv
    refine ⟨?_, ?_⟩
    · intro i
      obtain ⟨x, hx, hvx⟩ := Finset.mem_image.mp (hmem i)
      simpa [← hvx, hcdiv] using hx
    · have hscaled : lam * (∑ i : Fin k, coeff i * (lam⁻¹ * v i)) = lam * t := by
        calc
          lam * (∑ i : Fin k, coeff i * (lam⁻¹ * v i))
              = ∑ i : Fin k, coeff i * v i := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i _
                field_simp [hlam]
          _ = lam * t := hlin
      exact mul_left_cancel₀ hlam hscaled
  · intro v hv
    simp only [coe_filter, mem_univ, true_and] at hv ⊢
    obtain ⟨hmem, hlin⟩ := hv
    refine ⟨?_, ?_⟩
    · intro i
      exact Finset.mem_image.mpr ⟨v i, hmem i, rfl⟩
    · calc
        ∑ i : Fin k, coeff i * (lam * v i)
            = lam * (∑ i : Fin k, coeff i * v i) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = lam * t := by rw [hlin]
  · intro v _
    ext i
    simp [hcmul]
  · intro v _
    ext i
    simp [hcdiv]

/-- Two nonzero frequency dilates have identical fixed additive-linear pattern profiles after the
obvious target rescaling.  This is the broad b-blindness constraint behind the finite
Littlewood-Offord/Halász linear-pattern family: such data lives on the undilated subgroup and cannot
single out the worst frequency. -/
theorem addLinearPatternCount_phaseSet_indep_of_scalar {k : ℕ}
    (S : Finset F) (coeff : Fin k → F) {b₁ b₂ t : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    addLinearPatternCount (S.image (fun x => b₁ * x)) coeff (b₁ * t) =
      addLinearPatternCount (S.image (fun x => b₂ * x)) coeff (b₂ * t) := by
  rw [addLinearPatternCount_smul_eq S coeff hb₁, addLinearPatternCount_smul_eq S coeff hb₂]



/-- The set/range of target-fiber multiplicities for a fixed additive-linear pattern.  This records
which fiber sizes occur after forgetting target labels: it contains every possible count of a fiber
`∑ coeff_i v_i = t` with `v_i ∈ S`.  In particular, its maximum is the usual finite Littlewood-Offord
small-ball multiplicity for this linear form.  It intentionally does not record how many targets have
each size. -/
def addLinearPatternFiberCounts {k : ℕ} (S : Finset F) (coeff : Fin k → F) : Finset ℕ :=
  (Finset.univ : Finset F).image (fun t => addLinearPatternCount S coeff t)

/-- Nonzero dilation preserves the range of target-fiber counts of a fixed additive-linear pattern.
The labels of targets are merely permuted by `t ↦ λt`; therefore the max-over-target small-ball
multiplicity, and any statistic depending only on which fiber sizes occur, is frequency-blind. -/
theorem addLinearPatternFiberCounts_smul_eq {k : ℕ} (S : Finset F) (coeff : Fin k → F)
    {lam : F} (hlam : lam ≠ 0) :
    addLinearPatternFiberCounts (S.image (fun x => lam * x)) coeff =
      addLinearPatternFiberCounts S coeff := by
  classical
  ext N
  constructor
  · intro hN
    simp only [addLinearPatternFiberCounts, mem_image, mem_univ, true_and] at hN ⊢
    obtain ⟨t, ht⟩ := hN
    refine ⟨lam⁻¹ * t, ?_⟩
    have htarg : lam * (lam⁻¹ * t) = t := by
      rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
    have hcount := (addLinearPatternCount_smul_eq S coeff (t := lam⁻¹ * t) hlam).symm
    simpa [htarg, ht] using hcount
  · intro hN
    simp only [addLinearPatternFiberCounts, mem_image, mem_univ, true_and] at hN ⊢
    obtain ⟨t, ht⟩ := hN
    refine ⟨lam * t, ?_⟩
    rw [← ht]
    exact addLinearPatternCount_smul_eq S coeff hlam

/-- Two nonzero frequency dilates have the same range of linear-pattern fiber sizes.  Thus a lever
using only the maximum fiber size, or any statistic depending only on the set of occurring fiber
sizes, cannot select the adversarial worst frequency. -/
theorem addLinearPatternFiberCounts_phaseSet_indep_of_scalar {k : ℕ}
    (S : Finset F) (coeff : Fin k → F) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    addLinearPatternFiberCounts (S.image (fun x => b₁ * x)) coeff =
      addLinearPatternFiberCounts (S.image (fun x => b₂ * x)) coeff := by
  rw [addLinearPatternFiberCounts_smul_eq S coeff hb₁,
    addLinearPatternFiberCounts_smul_eq S coeff hb₂]


/-- The maximum target-fiber multiplicity of a fixed additive-linear pattern over all targets.  This
is the canonical small-ball/Halász statistic: the largest number of `S`-valued `k`-tuples landing in
one fiber of the linear form `∑ coeff_i v_i`. -/
def addLinearPatternMaxFiber {k : ℕ} (S : Finset F) (coeff : Fin k → F) : ℕ :=
  (addLinearPatternFiberCounts S coeff).max' (by
    classical
    simp [addLinearPatternFiberCounts])

/-- Nonzero dilation preserves the maximum target-fiber multiplicity of a fixed additive-linear
pattern.  This packages the most common Littlewood-Offord/Halász small-ball input directly: taking
`max_t` over fibers does not recover any dependence on the adversarial frequency `b`; dilation merely
renames the target attaining the maximum. -/
theorem addLinearPatternMaxFiber_smul_eq {k : ℕ} (S : Finset F) (coeff : Fin k → F)
    {lam : F} (hlam : lam ≠ 0) :
    addLinearPatternMaxFiber (S.image (fun x => lam * x)) coeff =
      addLinearPatternMaxFiber S coeff := by
  classical
  apply le_antisymm
  · rw [addLinearPatternMaxFiber, Finset.max'_le_iff]
    intro y hy
    rw [addLinearPatternMaxFiber]
    apply Finset.le_max'
    simpa [addLinearPatternFiberCounts_smul_eq S coeff hlam] using hy
  · rw [addLinearPatternMaxFiber, Finset.max'_le_iff]
    intro y hy
    rw [addLinearPatternMaxFiber]
    apply Finset.le_max'
    simpa [← addLinearPatternFiberCounts_smul_eq S coeff hlam] using hy

/-- Two nonzero frequency dilates have the same maximum linear-pattern fiber.  Thus a worst-frequency
anti-concentration attempt based on the usual `max_t` small-ball statistic is exactly `b`-blind. -/
theorem addLinearPatternMaxFiber_phaseSet_indep_of_scalar {k : ℕ}
    (S : Finset F) (coeff : Fin k → F) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    addLinearPatternMaxFiber (S.image (fun x => b₁ * x)) coeff =
      addLinearPatternMaxFiber (S.image (fun x => b₂ * x)) coeff := by
  rw [addLinearPatternMaxFiber_smul_eq S coeff hb₁,
    addLinearPatternMaxFiber_smul_eq S coeff hb₂]



/-- **No strict scalar improvement for max-fiber small-ball bounds.**  If the additive-linear
small-ball maximum for one nonzero frequency dilate is above a proposed threshold `C`, then no other
nonzero frequency dilate can satisfy the bound `≤ C`.  Thus a Door-IV anti-concentration proof based
only on the usual max-over-target Littlewood-Offord/Halász statistic cannot improve by choosing a
better scalar `b`; the statistic is exactly scalar-blind. -/
theorem not_addLinearPatternMaxFiber_scalar_improvement {k : ℕ}
    (S : Finset F) (coeff : Fin k → F) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) {C : ℕ}
    (hbad : C < addLinearPatternMaxFiber (S.image (fun x => b₁ * x)) coeff) :
    ¬ addLinearPatternMaxFiber (S.image (fun x => b₂ * x)) coeff ≤ C := by
  intro hgood
  have heq := addLinearPatternMaxFiber_phaseSet_indep_of_scalar
    (S := S) (coeff := coeff) hb₁ hb₂
  exact not_lt_of_ge hgood (by simpa [heq] using hbad)

/-- Histogram bin for target-fiber multiplicities of a fixed additive-linear pattern: the number of
field targets `t` whose fiber has size exactly `N`.  Unlike `addLinearPatternFiberCounts`, this records
how often each fiber size occurs. -/
def addLinearPatternFiberMultiplicity {k : ℕ} (S : Finset F) (coeff : Fin k → F) (N : ℕ) : ℕ :=
  ((Finset.univ : Finset F).filter (fun t => addLinearPatternCount S coeff t = N)).card

/-- Nonzero dilation preserves the full histogram of target-fiber sizes for a fixed additive-linear
pattern.  The target relabeling `t ↦ λt` is a bijection, so not only the max/range but also the number
of targets attaining each fiber size is independent of the frequency. -/
theorem addLinearPatternFiberMultiplicity_smul_eq {k : ℕ} (S : Finset F) (coeff : Fin k → F)
    (N : ℕ) {lam : F} (hlam : lam ≠ 0) :
    addLinearPatternFiberMultiplicity (S.image (fun x => lam * x)) coeff N =
      addLinearPatternFiberMultiplicity S coeff N := by
  classical
  unfold addLinearPatternFiberMultiplicity
  have hcdiv : ∀ z : F, lam⁻¹ * (lam * z) = z := fun z => by
    rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  have hcmul : ∀ z : F, lam * (lam⁻¹ * z) = z := fun z => by
    rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
  refine Finset.card_nbij'
    (fun t => lam⁻¹ * t)
    (fun t => lam * t)
    ?_ ?_ ?_ ?_
  · intro t ht
    have htN : addLinearPatternCount (S.image (fun x => lam * x)) coeff t = N := by
      simpa using ht
    have hcount := (addLinearPatternCount_smul_eq S coeff (t := lam⁻¹ * t) hlam).symm
    have htN' : addLinearPatternCount (S.image (fun x => lam * x)) coeff (lam * (lam⁻¹ * t)) = N := by
      simpa [hcmul] using htN
    simpa using hcount.trans htN'
  · intro t ht
    have htN : addLinearPatternCount S coeff t = N := by
      simpa using ht
    have hcount := addLinearPatternCount_smul_eq S coeff (t := t) hlam
    simpa using hcount.trans htN
  · intro t _
    exact hcmul t
  · intro t _
    exact hcdiv t

/-- Two nonzero frequency dilates have the same full linear-pattern fiber histogram.  Therefore a
Littlewood-Offord/Halász lever using the distribution of fixed linear-form fiber sizes, rather than
just the maximum or support, still cannot select the adversarial worst frequency. -/
theorem addLinearPatternFiberMultiplicity_phaseSet_indep_of_scalar {k : ℕ}
    (S : Finset F) (coeff : Fin k → F) (N : ℕ) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    addLinearPatternFiberMultiplicity (S.image (fun x => b₁ * x)) coeff N =
      addLinearPatternFiberMultiplicity (S.image (fun x => b₂ * x)) coeff N := by
  rw [addLinearPatternFiberMultiplicity_smul_eq S coeff N hb₁,
    addLinearPatternFiberMultiplicity_smul_eq S coeff N hb₂]

/-- **No strict scalar improvement for full fiber-histogram small-ball bounds.**  If one nonzero
frequency dilate has more than `C` targets whose additive-linear fiber size is exactly `N`, then no
other nonzero dilate can satisfy the histogram bound `≤ C` at that same fiber size.  Passing from the
maximum fiber to the whole Littlewood-Offord/Halász fiber histogram still cannot select or improve the
adversarial `b`; dilation only relabels the targets. -/
theorem not_addLinearPatternFiberMultiplicity_scalar_improvement {k : ℕ}
    (S : Finset F) (coeff : Fin k → F) (N : ℕ) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) {C : ℕ}
    (hbad : C < addLinearPatternFiberMultiplicity (S.image (fun x => b₁ * x)) coeff N) :
    ¬ addLinearPatternFiberMultiplicity (S.image (fun x => b₂ * x)) coeff N ≤ C := by
  intro hgood
  have heq := addLinearPatternFiberMultiplicity_phaseSet_indep_of_scalar
    (S := S) (coeff := coeff) (N := N) hb₁ hb₂
  exact not_lt_of_ge hgood (by simpa [heq] using hbad)

/-- Dilation by a NONZERO scalar `λ` is an additive-energy-preserving bijection on the quadruple
solution set: `(a,b,c,d) ↦ (λa,λb,λc,λd)` maps `addQuadruples S` bijectively onto
`addQuadruples (λ • S)`, because `a+b=c+d ⟺ λa+λb=λc+λd` for `λ ≠ 0`. Hence the additive energy is
dilation-invariant. -/
theorem addEnergy_smul_eq (S : Finset F) {lam : F} (hlam : lam ≠ 0) :
    addEnergy (S.image (fun x => lam * x)) = addEnergy S := by
  classical
  unfold addEnergy addQuadruples
  -- s = quadruples of (λ•S); t = quadruples of S. i divides by λ, j multiplies by λ.
  have hcdiv : ∀ z : F, lam⁻¹ * (lam * z) = z := fun z => by
    rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  have hcmul : ∀ z : F, lam * (lam⁻¹ * z) = z := fun z => by
    rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
  refine Finset.card_nbij'
    (fun q => (lam⁻¹ * q.1, lam⁻¹ * q.2.1, lam⁻¹ * q.2.2.1, lam⁻¹ * q.2.2.2))
    (fun q => (lam * q.1, lam * q.2.1, lam * q.2.2.1, lam * q.2.2.2))
    ?_ ?_ ?_ ?_
  · -- i : (λ•S)-quads → S-quads
    rintro ⟨a, b, c, d⟩ hq
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_image] at hq ⊢
    obtain ⟨⟨⟨a', ha', rfl⟩, ⟨b', hb', rfl⟩, ⟨c', hc', rfl⟩, ⟨d', hd', rfl⟩⟩, heq⟩ := hq
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa [hcdiv] using ha'
    · simpa [hcdiv] using hb'
    · simpa [hcdiv] using hc'
    · simpa [hcdiv] using hd'
    · rw [hcdiv, hcdiv, hcdiv, hcdiv]
      have h2 := mul_left_cancel₀ hlam (by linear_combination heq :
        lam * (a' + b') = lam * (c' + d'))
      linear_combination h2
  · -- j : S-quads → (λ•S)-quads
    rintro ⟨a, b, c, d⟩ hq
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_image] at hq ⊢
    obtain ⟨⟨ha, hb, hc, hd⟩, heq⟩ := hq
    refine ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, ⟨c, hc, rfl⟩, ⟨d, hd, rfl⟩⟩, ?_⟩
    linear_combination lam * heq
  · -- left inverse on s
    rintro ⟨a, b, c, d⟩ _
    simp only [Prod.mk.injEq]
    exact ⟨hcmul a, hcmul b, hcmul c, hcmul d⟩
  · -- right inverse on t
    rintro ⟨a, b, c, d⟩ _
    simp only [Prod.mk.injEq]
    exact ⟨hcdiv a, hcdiv b, hcdiv c, hcdiv d⟩

/-- Consequence for the small-ball lever: since `E⁺(b • S) = E⁺(S)` for every nonzero `b`, any
`|η_b|`-bound that factors through the additive energy of the phase set `S_b = b • μ_n` takes the
SAME value at the worst `b` as at a typical `b`. The worst `b` cannot tune the additive structure;
the small-ball / Halász lever is b-independent and reproduces the typical (EVT/Plancherel) ceiling.
We state it as: a uniform additive-energy `E⁺(S_b) = K` certificate is the SAME for all nonzero
dilates, so a bound `f (E⁺ (b • S))` is constant in `b`. -/
theorem addEnergy_phaseSet_indep_of_scalar
    (S : Finset F) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    addEnergy (S.image (fun x => b₁ * x)) = addEnergy (S.image (fun x => b₂ * x)) := by
  rw [addEnergy_smul_eq S hb₁, addEnergy_smul_eq S hb₂]

/-- **No strict scalar improvement for additive-energy bounds.**  If one nonzero frequency dilate has
additive energy above a proposed threshold `C`, then every other nonzero frequency dilate has the same
energy and therefore cannot satisfy `E⁺ ≤ C`.  Thus an additive-energy/Halász lever cannot become a
worst-frequency anti-concentration theorem by optimizing over `b`; the scalar only relabels the phase
set. -/
theorem not_addEnergy_scalar_improvement
    (S : Finset F) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) {C : ℕ}
    (hbad : C < addEnergy (S.image (fun x => b₁ * x))) :
    ¬ addEnergy (S.image (fun x => b₂ * x)) ≤ C := by
  intro hgood
  have heq := addEnergy_phaseSet_indep_of_scalar (S := S) hb₁ hb₂
  exact not_lt_of_ge hgood (by simpa [heq] using hbad)

/-- The higher-order additive-energy solution set `E_k(S)`: the set of `2k`-tuples
`(a : Fin k → S, c : Fin k → S)` with balanced sums `∑ a_i = ∑ c_i`.  Its cardinality is the
`k`-th additive energy `E_k(S) = #{(a,c) ∈ S^{2k} : ∑ a_i = ∑ c_i}`, the canonical input to a
higher-order (`L^{2k}`-moment / Gowers / higher-Halász) small-ball bound.  The `k = 2` case is the
classical additive energy `addEnergy`. -/
def addEnergyKTuples {k : ℕ} (S : Finset F) :
    Finset ((Fin k → F) × (Fin k → F)) :=
  ((Finset.univ : Finset ((Fin k → F) × (Fin k → F))).filter
    (fun q => (∀ i, q.1 i ∈ S) ∧ (∀ i, q.2 i ∈ S) ∧
      (∑ i, q.1 i) = (∑ i, q.2 i)))

/-- `k`-th additive energy `E_k(S) = #{(a,c) ∈ S^{2k} : ∑ a_i = ∑ c_i}`.  Generalizes `addEnergy`
(the `k = 2` case) and is the natural input to a higher-order Halász/Gowers small-ball lever — the
"go higher-order" escape from the saturated `E⁺` bound. -/
def addEnergyK {k : ℕ} (S : Finset F) : ℕ := (addEnergyKTuples (k := k) S).card

/-- **Higher-order additive energy is dilation-invariant.**  For nonzero `λ`, the coordinatewise
multiply-by-`λ` map is a bijection of the `E_k` solution set: it preserves membership in `S` (after
dilating `S`) and the balanced-sum relation `∑ a_i = ∑ c_i ⟺ ∑ λa_i = ∑ λc_i`.  Hence
`E_k(λ • S) = E_k(S)` for every order `k`.  This closes the "go higher-order" escape b-blindly: no
finite-order additive-energy lever can depend on the adversarial frequency. -/
theorem addEnergyK_smul_eq {k : ℕ} (S : Finset F) {lam : F} (hlam : lam ≠ 0) :
    addEnergyK (k := k) (S.image (fun x => lam * x)) = addEnergyK (k := k) S := by
  classical
  unfold addEnergyK addEnergyKTuples
  have hcdiv : ∀ z : F, lam⁻¹ * (lam * z) = z := fun z => by
    rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  have hcmul : ∀ z : F, lam * (lam⁻¹ * z) = z := fun z => by
    rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
  refine Finset.card_nbij'
    (fun q => (fun i => lam⁻¹ * q.1 i, fun i => lam⁻¹ * q.2 i))
    (fun q => (fun i => lam * q.1 i, fun i => lam * q.2 i))
    ?_ ?_ ?_ ?_
  · rintro ⟨a, c⟩ hq
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hq ⊢
    obtain ⟨ha, hc, hsum⟩ := hq
    refine ⟨?_, ?_, ?_⟩
    · intro i
      obtain ⟨x, hx, hax⟩ := Finset.mem_image.mp (ha i)
      simpa [← hax, hcdiv] using hx
    · intro i
      obtain ⟨x, hx, hcx⟩ := Finset.mem_image.mp (hc i)
      simpa [← hcx, hcdiv] using hx
    · apply mul_left_cancel₀ hlam
      have hL : lam * (∑ i, lam⁻¹ * a i) = ∑ i, a i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => hcmul (a i))
      have hR : lam * (∑ i, lam⁻¹ * c i) = ∑ i, c i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => hcmul (c i))
      rw [hL, hR, hsum]
  · rintro ⟨a, c⟩ hq
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hq ⊢
    obtain ⟨ha, hc, hsum⟩ := hq
    refine ⟨?_, ?_, ?_⟩
    · intro i; exact Finset.mem_image.mpr ⟨a i, ha i, rfl⟩
    · intro i; exact Finset.mem_image.mpr ⟨c i, hc i, rfl⟩
    · rw [← Finset.mul_sum, ← Finset.mul_sum, hsum]
  · rintro ⟨a, c⟩ _
    simp only [Prod.mk.injEq]
    constructor <;> · funext i; simp [hcmul]
  · rintro ⟨a, c⟩ _
    simp only [Prod.mk.injEq]
    constructor <;> · funext i; simp [hcdiv]

/-- Two nonzero frequency dilates have the same `k`-th additive energy.  Thus a higher-order
additive-energy / Gowers small-ball lever on `{b·x^m}` is exactly `b`-blind at every order, just like
the classical `E⁺` case: the worst frequency cannot tune any finite-order energy. -/
theorem addEnergyK_phaseSet_indep_of_scalar {k : ℕ}
    (S : Finset F) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    addEnergyK (k := k) (S.image (fun x => b₁ * x)) =
      addEnergyK (k := k) (S.image (fun x => b₂ * x)) := by
  rw [addEnergyK_smul_eq (k := k) S hb₁, addEnergyK_smul_eq (k := k) S hb₂]

/-- **No strict scalar improvement for higher-order additive-energy bounds.**  If one nonzero
frequency dilate has `k`-th additive energy above a proposed threshold `C`, then every other nonzero
dilate has the same energy and cannot satisfy `E_k ≤ C`.  Therefore the "go higher-order" escape —
replacing the classical energy by a higher-moment/Gowers energy — still cannot become a worst-frequency
anti-concentration theorem by optimizing over `b`; the scalar only relabels the phase set at every
order. -/
theorem not_addEnergyK_scalar_improvement {k : ℕ}
    (S : Finset F) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) {C : ℕ}
    (hbad : C < addEnergyK (k := k) (S.image (fun x => b₁ * x))) :
    ¬ addEnergyK (k := k) (S.image (fun x => b₂ * x)) ≤ C := by
  intro hgood
  have heq := addEnergyK_phaseSet_indep_of_scalar (k := k) (S := S) hb₁ hb₂
  exact not_lt_of_ge hgood (by simpa [heq] using hbad)

/-- Target-fiber of the higher-order balanced sum: for an order `k`, the set of `k`-tuples
`(a : Fin k → S)` whose sum hits a fixed target `t`.  Its cardinality is the `L^{2k}`-small-ball /
higher-Halász multiplicity at `t`; maximizing over `t` gives the higher-order analogue of
`addLinearPatternMaxFiber`. -/
def addKSumCount {k : ℕ} (S : Finset F) (t : F) : ℕ :=
  ((Finset.univ : Finset (Fin k → F)).filter
    (fun v => (∀ i, v i ∈ S) ∧ (∑ i, v i) = t)).card

/-- Nonzero dilation transports every higher-order sum fiber by `t ↦ λt`.  This is the higher-order
analogue of `addLinearPatternCount_smul_eq` for the homogeneous all-ones linear form on `k`
coordinates. -/
theorem addKSumCount_smul_eq {k : ℕ} (S : Finset F) {lam t : F} (hlam : lam ≠ 0) :
    addKSumCount (k := k) (S.image (fun x => lam * x)) (lam * t) = addKSumCount (k := k) S t := by
  classical
  unfold addKSumCount
  have hcdiv : ∀ z : F, lam⁻¹ * (lam * z) = z := fun z => by
    rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  have hcmul : ∀ z : F, lam * (lam⁻¹ * z) = z := fun z => by
    rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
  refine Finset.card_nbij'
    (fun v i => lam⁻¹ * v i)
    (fun v i => lam * v i)
    ?_ ?_ ?_ ?_
  · intro v hv
    simp only [coe_filter, mem_univ, true_and] at hv ⊢
    obtain ⟨hmem, hsum⟩ := hv
    refine ⟨?_, ?_⟩
    · intro i
      obtain ⟨x, hx, hvx⟩ := Finset.mem_image.mp (hmem i)
      simpa [← hvx, hcdiv] using hx
    · apply mul_left_cancel₀ hlam
      have hL : lam * (∑ i, lam⁻¹ * v i) = ∑ i, v i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => hcmul (v i))
      rw [hL, hsum]
  · intro v hv
    simp only [coe_filter, mem_univ, true_and] at hv ⊢
    obtain ⟨hmem, hsum⟩ := hv
    refine ⟨?_, ?_⟩
    · intro i; exact Finset.mem_image.mpr ⟨v i, hmem i, rfl⟩
    · rw [← Finset.mul_sum, hsum]
  · intro v _; funext i; simp [hcmul]
  · intro v _; funext i; simp [hcdiv]

/-- The set of higher-order sum-fiber sizes (forgetting target labels).  Its maximum is the
`L^{2k}` higher-order small-ball multiplicity. -/
def addKSumFiberCounts {k : ℕ} (S : Finset F) : Finset ℕ :=
  (Finset.univ : Finset F).image (fun t => addKSumCount (k := k) S t)

/-- Nonzero dilation preserves the range of higher-order sum-fiber sizes: `t ↦ λt` merely permutes
target labels. -/
theorem addKSumFiberCounts_smul_eq {k : ℕ} (S : Finset F) {lam : F} (hlam : lam ≠ 0) :
    addKSumFiberCounts (k := k) (S.image (fun x => lam * x)) = addKSumFiberCounts (k := k) S := by
  classical
  ext N
  constructor
  · intro hN
    simp only [addKSumFiberCounts, mem_image, mem_univ, true_and] at hN ⊢
    obtain ⟨t, ht⟩ := hN
    refine ⟨lam⁻¹ * t, ?_⟩
    have htarg : lam * (lam⁻¹ * t) = t := by
      rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
    have hcount := (addKSumCount_smul_eq (k := k) S (t := lam⁻¹ * t) hlam).symm
    simpa [htarg, ht] using hcount
  · intro hN
    simp only [addKSumFiberCounts, mem_image, mem_univ, true_and] at hN ⊢
    obtain ⟨t, ht⟩ := hN
    refine ⟨lam * t, ?_⟩
    rw [← ht]
    exact addKSumCount_smul_eq (k := k) S hlam

/-- The higher-order `L^{2k}` small-ball multiplicity: the maximum over targets of the `k`-fold
sum-fiber size.  This is the higher-order analogue of `addLinearPatternMaxFiber`. -/
def addKSumMaxFiber {k : ℕ} (S : Finset F) : ℕ :=
  (addKSumFiberCounts (k := k) S).max' (by
    classical
    simp [addKSumFiberCounts])

/-- Nonzero dilation preserves the higher-order `L^{2k}` small-ball multiplicity.  The worst
frequency cannot tune the max-over-target higher-order fiber; dilation only relabels the target
attaining the maximum. -/
theorem addKSumMaxFiber_smul_eq {k : ℕ} (S : Finset F) {lam : F} (hlam : lam ≠ 0) :
    addKSumMaxFiber (k := k) (S.image (fun x => lam * x)) = addKSumMaxFiber (k := k) S := by
  classical
  apply le_antisymm
  · rw [addKSumMaxFiber, Finset.max'_le_iff]
    intro y hy
    rw [addKSumMaxFiber]
    apply Finset.le_max'
    simpa [addKSumFiberCounts_smul_eq (k := k) S hlam] using hy
  · rw [addKSumMaxFiber, Finset.max'_le_iff]
    intro y hy
    rw [addKSumMaxFiber]
    apply Finset.le_max'
    simpa [← addKSumFiberCounts_smul_eq (k := k) S hlam] using hy

/-- Two nonzero frequency dilates have the same higher-order `L^{2k}` small-ball multiplicity.  A
higher-order Halász max-fiber anti-concentration attempt is therefore exactly `b`-blind at every
order. -/
theorem addKSumMaxFiber_phaseSet_indep_of_scalar {k : ℕ}
    (S : Finset F) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    addKSumMaxFiber (k := k) (S.image (fun x => b₁ * x)) =
      addKSumMaxFiber (k := k) (S.image (fun x => b₂ * x)) := by
  rw [addKSumMaxFiber_smul_eq (k := k) S hb₁, addKSumMaxFiber_smul_eq (k := k) S hb₂]

/-- **No strict scalar improvement for the higher-order `L^{2k}` small-ball multiplicity.**  If one
nonzero frequency dilate has higher-order max-fiber above a proposed threshold `C`, then no other
nonzero dilate can satisfy `≤ C`.  Passing to the higher-order small-ball constant still cannot improve
the adversarial frequency. -/
theorem not_addKSumMaxFiber_scalar_improvement {k : ℕ}
    (S : Finset F) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) {C : ℕ}
    (hbad : C < addKSumMaxFiber (k := k) (S.image (fun x => b₁ * x))) :
    ¬ addKSumMaxFiber (k := k) (S.image (fun x => b₂ * x)) ≤ C := by
  intro hgood
  have heq := addKSumMaxFiber_phaseSet_indep_of_scalar (k := k) (S := S) hb₁ hb₂
  exact not_lt_of_ge hgood (by simpa [heq] using hbad)

/-! ## The multi-dimensional small-ball lever: a SYSTEM of additive-linear forms is b-blind

A genuine Halász / Littlewood–Offord anti-concentration lever for the phase set is `m`-dimensional:
it measures the JOINT fiber `{v ∈ S^k : A·v = t}` of a SYSTEM of `m` additive-linear forms
(`A : Fin m → Fin k → F`, vector target `t : Fin m → F`), not a single scalar form. The single-form
`addLinearPatternCount` does NOT subsume this multi-dimensional case. We close the entire
multi-dimensional additive small-ball class in one statement: every such joint count is dilation
invariant (after rescaling the vector target), hence b-blind on the worst-frequency phase set.
This matches the probe `scripts/probes/probe_dooriv_multiform_smallball_blind.py` (PROPER 2-power
`μ_n`, p≫n³, structured primes, `m=2,k=3`, multiple nonzero dilates × targets, never n=q−1), which
found the joint system count invariant under every nonzero dilation. -/

/-- The joint solution set of a SYSTEM of `m` additive-linear forms `A : Fin m → Fin k → F` over a
finite set `S`, at vector target `t : Fin m → F`: the tuples `v : Fin k → F` with all coordinates in
`S` simultaneously satisfying `∑ⱼ A r j · v j = t r` for every row `r`. Its cardinality is the
`m`-dimensional Littlewood–Offord / Halász small-ball count for the system. -/
def addSystemPatternCount {m k : ℕ} (S : Finset F) (A : Fin m → Fin k → F) (t : Fin m → F) : ℕ :=
  ((Finset.univ : Finset (Fin k → F)).filter
    (fun v => (∀ i : Fin k, v i ∈ S) ∧ (∀ r : Fin m, (∑ j : Fin k, A r j * v j) = t r))).card

/-- **A SYSTEM of additive-linear forms is dilation-invariant** (after rescaling the vector target).
Multiplication by a nonzero `λ` transports the joint solution set for `S` and target `t` bijectively
onto the one for `λS` and target `λt`, simultaneously across all `m` rows. Hence the multi-dimensional
Halász / Littlewood–Offord small-ball count of the phase set is frequency-blind. -/
theorem addSystemPatternCount_smul_eq {m k : ℕ} (S : Finset F) (A : Fin m → Fin k → F)
    {lam : F} (t : Fin m → F) (hlam : lam ≠ 0) :
    addSystemPatternCount (S.image (fun x => lam * x)) A (fun r => lam * t r) =
      addSystemPatternCount S A t := by
  classical
  unfold addSystemPatternCount
  have hcdiv : ∀ z : F, lam⁻¹ * (lam * z) = z := fun z => by
    rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  have hcmul : ∀ z : F, lam * (lam⁻¹ * z) = z := fun z => by
    rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
  refine Finset.card_nbij'
    (fun v i => lam⁻¹ * v i)
    (fun v i => lam * v i)
    ?_ ?_ ?_ ?_
  · intro v hv
    simp only [coe_filter, mem_univ, true_and] at hv ⊢
    obtain ⟨hmem, hlin⟩ := hv
    refine ⟨?_, ?_⟩
    · intro i
      obtain ⟨x, hx, hvx⟩ := Finset.mem_image.mp (hmem i)
      simpa [← hvx, hcdiv] using hx
    · intro r
      have hscaled : lam * (∑ j : Fin k, A r j * (lam⁻¹ * v j)) = lam * t r := by
        calc
          lam * (∑ j : Fin k, A r j * (lam⁻¹ * v j))
              = ∑ j : Fin k, A r j * v j := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                field_simp [hlam]
          _ = lam * t r := hlin r
      exact mul_left_cancel₀ hlam hscaled
  · intro v hv
    simp only [coe_filter, mem_univ, true_and] at hv ⊢
    obtain ⟨hmem, hlin⟩ := hv
    refine ⟨?_, ?_⟩
    · intro i
      exact Finset.mem_image.mpr ⟨v i, hmem i, rfl⟩
    · intro r
      calc
        ∑ j : Fin k, A r j * (lam * v j)
            = lam * (∑ j : Fin k, A r j * v j) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = lam * t r := by rw [hlin r]
  · intro v _
    ext i
    simp [hcmul]
  · intro v _
    ext i
    simp [hcdiv]

/-- **Two nonzero frequency dilates have identical joint system small-ball profiles** (after the
vector-target rescaling). The entire multi-dimensional additive small-ball / Halász family lives on
the undilated subgroup and cannot single out the adversarial worst frequency. This subsumes the
single-form `addLinearPatternCount_phaseSet_indep_of_scalar` (take `m = 1`). -/
theorem addSystemPatternCount_phaseSet_indep_of_scalar {m k : ℕ}
    (S : Finset F) (A : Fin m → Fin k → F) (t : Fin m → F) {b₁ b₂ : F}
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    addSystemPatternCount (S.image (fun x => b₁ * x)) A (fun r => b₁ * t r) =
      addSystemPatternCount (S.image (fun x => b₂ * x)) A (fun r => b₂ * t r) := by
  rw [addSystemPatternCount_smul_eq S A t hb₁, addSystemPatternCount_smul_eq S A t hb₂]

/-- The range of joint-system target-fiber multiplicities over all vector targets.  This is the
multi-form, multi-target small-ball profile: it forgets target labels and keeps exactly which fiber
sizes occur for the system `∀ r, ∑ j A r j * v j = t r`. -/
def addSystemPatternFiberCounts {m k : ℕ}
    (S : Finset F) (A : Fin m → Fin k → F) : Finset ℕ :=
  (Finset.univ : Finset (Fin m → F)).image (fun t => addSystemPatternCount S A t)

/-- Nonzero dilation preserves the full range of joint-system fiber sizes.  The vector target labels
are merely permuted by `t ↦ λ • t`; hence even taking an arbitrary vector-target histogram/range does
not recover any dependence on the adversarial frequency. -/
theorem addSystemPatternFiberCounts_smul_eq {m k : ℕ}
    (S : Finset F) (A : Fin m → Fin k → F) {lam : F} (hlam : lam ≠ 0) :
    addSystemPatternFiberCounts (S.image (fun x => lam * x)) A =
      addSystemPatternFiberCounts S A := by
  classical
  ext N
  constructor
  · intro hN
    simp only [addSystemPatternFiberCounts, mem_image, mem_univ, true_and] at hN ⊢
    obtain ⟨t, ht⟩ := hN
    refine ⟨fun r => lam⁻¹ * t r, ?_⟩
    rw [← ht]
    have hcount := (addSystemPatternCount_smul_eq S A (fun r => lam⁻¹ * t r) hlam).symm
    simpa [← mul_assoc, mul_inv_cancel₀ hlam] using hcount
  · intro hN
    simp only [addSystemPatternFiberCounts, mem_image, mem_univ, true_and] at hN ⊢
    obtain ⟨t, ht⟩ := hN
    refine ⟨fun r => lam * t r, ?_⟩
    rw [← ht]
    exact addSystemPatternCount_smul_eq S A t hlam

/-- Two nonzero frequency dilates have the same joint-system small-ball fiber-size range.  This is the
histogram/range form of multi-dimensional Halász blindness, independent of which vector target is
chosen after dilation. -/
theorem addSystemPatternFiberCounts_phaseSet_indep_of_scalar {m k : ℕ}
    (S : Finset F) (A : Fin m → Fin k → F) {b₁ b₂ : F}
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    addSystemPatternFiberCounts (S.image (fun x => b₁ * x)) A =
      addSystemPatternFiberCounts (S.image (fun x => b₂ * x)) A := by
  rw [addSystemPatternFiberCounts_smul_eq S A hb₁,
    addSystemPatternFiberCounts_smul_eq S A hb₂]

/-- The maximum joint-system target-fiber multiplicity over all vector targets.  This is the usual
multi-dimensional small-ball/Halász statistic obtained from a system of additive linear forms. -/
def addSystemPatternMaxFiber {m k : ℕ}
    (S : Finset F) (A : Fin m → Fin k → F) : ℕ :=
  (addSystemPatternFiberCounts S A).max' (by
    classical
    simp [addSystemPatternFiberCounts])

/-- Nonzero dilation preserves the maximum joint-system small-ball multiplicity.  Taking `max_t` over
all vector targets only renames the maximizer by scalar multiplication; it does not create a worst-`b`
anti-concentration lever. -/
theorem addSystemPatternMaxFiber_smul_eq {m k : ℕ}
    (S : Finset F) (A : Fin m → Fin k → F) {lam : F} (hlam : lam ≠ 0) :
    addSystemPatternMaxFiber (S.image (fun x => lam * x)) A =
      addSystemPatternMaxFiber S A := by
  classical
  apply le_antisymm
  · rw [addSystemPatternMaxFiber, Finset.max'_le_iff]
    intro y hy
    rw [addSystemPatternMaxFiber]
    apply Finset.le_max'
    simpa [addSystemPatternFiberCounts_smul_eq S A hlam] using hy
  · rw [addSystemPatternMaxFiber, Finset.max'_le_iff]
    intro y hy
    rw [addSystemPatternMaxFiber]
    apply Finset.le_max'
    simpa [← addSystemPatternFiberCounts_smul_eq S A hlam] using hy

/-- Two nonzero frequency dilates have the same maximum joint-system small-ball fiber.  Thus the
strongest target-optimized multi-dimensional additive small-ball statistic is still scalar-blind. -/
theorem addSystemPatternMaxFiber_phaseSet_indep_of_scalar {m k : ℕ}
    (S : Finset F) (A : Fin m → Fin k → F) {b₁ b₂ : F}
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    addSystemPatternMaxFiber (S.image (fun x => b₁ * x)) A =
      addSystemPatternMaxFiber (S.image (fun x => b₂ * x)) A := by
  rw [addSystemPatternMaxFiber_smul_eq S A hb₁,
    addSystemPatternMaxFiber_smul_eq S A hb₂]

/-- Histogram bin for joint-system target-fiber multiplicities: the number of vector targets whose
fiber has size exactly `N`.  This records the full multi-dimensional small-ball histogram, not merely
its support or maximum. -/
def addSystemPatternFiberMultiplicity {m k : ℕ}
    (S : Finset F) (A : Fin m → Fin k → F) (N : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin m → F)).filter (fun t => addSystemPatternCount S A t = N)).card

/-- Nonzero dilation preserves the full histogram of joint-system fiber sizes.  The map
`t ↦ λ • t` is a bijection on vector targets, so every histogram bin is unchanged. -/
theorem addSystemPatternFiberMultiplicity_smul_eq {m k : ℕ}
    (S : Finset F) (A : Fin m → Fin k → F) (N : ℕ) {lam : F} (hlam : lam ≠ 0) :
    addSystemPatternFiberMultiplicity (S.image (fun x => lam * x)) A N =
      addSystemPatternFiberMultiplicity S A N := by
  classical
  unfold addSystemPatternFiberMultiplicity
  refine Finset.card_nbij'
    (fun t r => lam⁻¹ * t r)
    (fun t r => lam * t r)
    ?_ ?_ ?_ ?_
  · intro t ht
    have htN : addSystemPatternCount (S.image (fun x => lam * x)) A t = N := by
      simpa using ht
    have hcount := (addSystemPatternCount_smul_eq S A (fun r => lam⁻¹ * t r) hlam).symm
    have htarget : (fun r => lam * (lam⁻¹ * t r)) = t := by
      ext r
      rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
    have hcount' : addSystemPatternCount (S.image (fun x => lam * x)) A t =
        addSystemPatternCount S A (fun r => lam⁻¹ * t r) := by
      simpa [htarget] using hcount.symm
    simpa using hcount'.symm.trans htN
  · intro t ht
    have htN : addSystemPatternCount S A t = N := by
      simpa using ht
    have hcount := addSystemPatternCount_smul_eq S A t hlam
    simpa using hcount.trans htN
  · intro t _
    ext r
    simp [hlam]
  · intro t _
    ext r
    simp [hlam]

/-- Two nonzero frequency dilates have the same full joint-system fiber histogram.  Thus even
histogram-sensitive multi-dimensional small-ball inputs are scalar-blind. -/
theorem addSystemPatternFiberMultiplicity_phaseSet_indep_of_scalar {m k : ℕ}
    (S : Finset F) (A : Fin m → Fin k → F) (N : ℕ) {b₁ b₂ : F}
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    addSystemPatternFiberMultiplicity (S.image (fun x => b₁ * x)) A N =
      addSystemPatternFiberMultiplicity (S.image (fun x => b₂ * x)) A N := by
  rw [addSystemPatternFiberMultiplicity_smul_eq S A N hb₁,
    addSystemPatternFiberMultiplicity_smul_eq S A N hb₂]

/-- **No strict scalar improvement for the multi-dimensional small-ball count.** If one nonzero
frequency dilate makes the joint system fiber exceed a proposed threshold `C`, no other nonzero
dilate can satisfy `≤ C` at the rescaled target. The adversarial worst `b` cannot tune the
multi-dimensional Halász small-ball lever to beat the typical value: it is genuinely frequency-blind.
This is the multi-form analogue of `not_addLinearPatternMaxFiber_scalar_improvement`, and locks the
full `m`-dimensional additive small-ball class as a dead door-(iv) lever. -/
theorem not_addSystemPatternCount_scalar_improvement {m k : ℕ}
    (S : Finset F) (A : Fin m → Fin k → F) (t : Fin m → F) {b₁ b₂ : F}
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) {C : ℕ}
    (hbad : C < addSystemPatternCount (S.image (fun x => b₁ * x)) A (fun r => b₁ * t r)) :
    ¬ addSystemPatternCount (S.image (fun x => b₂ * x)) A (fun r => b₂ * t r) ≤ C := by
  intro hgood
  have heq := addSystemPatternCount_phaseSet_indep_of_scalar (S := S) A t hb₁ hb₂
  exact not_lt_of_ge hgood (by simpa [heq] using hbad)

/-- **No strict scalar improvement for target-optimized multi-dimensional small-ball bounds.** If the
max-over-vector-target joint fiber for one nonzero frequency is above `C`, then every other nonzero
frequency has the same maximum and cannot satisfy `≤ C`. This packages the actual Halász/LO
small-ball use case where the target is chosen adversarially after the system is fixed. -/
theorem not_addSystemPatternMaxFiber_scalar_improvement {m k : ℕ}
    (S : Finset F) (A : Fin m → Fin k → F) {b₁ b₂ : F}
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) {C : ℕ}
    (hbad : C < addSystemPatternMaxFiber (S.image (fun x => b₁ * x)) A) :
    ¬ addSystemPatternMaxFiber (S.image (fun x => b₂ * x)) A ≤ C := by
  intro hgood
  have heq := addSystemPatternMaxFiber_phaseSet_indep_of_scalar (S := S) A hb₁ hb₂
  exact not_lt_of_ge hgood (by simpa [heq] using hbad)

/-- **No strict scalar improvement for full joint-system fiber-histogram bounds.** If one nonzero
frequency has more than `C` vector targets with fiber size exactly `N`, no other nonzero frequency can
satisfy the histogram-bin bound `≤ C`. Dilation only relabels vector targets. -/
theorem not_addSystemPatternFiberMultiplicity_scalar_improvement {m k : ℕ}
    (S : Finset F) (A : Fin m → Fin k → F) (N : ℕ) {b₁ b₂ : F}
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) {C : ℕ}
    (hbad : C < addSystemPatternFiberMultiplicity (S.image (fun x => b₁ * x)) A N) :
    ¬ addSystemPatternFiberMultiplicity (S.image (fun x => b₂ * x)) A N ≤ C := by
  intro hgood
  have heq := addSystemPatternFiberMultiplicity_phaseSet_indep_of_scalar (S := S) A N hb₁ hb₂
  exact not_lt_of_ge hgood (by simpa [heq] using hbad)

end ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant

#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addSumset_smul_eq_image
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addSumset_card_smul_eq
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addSumset_card_phaseSet_indep_of_scalar
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addDiffset_smul_eq_image
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addDiffset_card_smul_eq
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addDiffset_card_phaseSet_indep_of_scalar
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addPairSumCount_smul_eq
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addPairSumCount_phaseSet_indep_of_scalar
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addPairDiffCount_smul_eq
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addPairDiffCount_phaseSet_indep_of_scalar
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addTripleSumCount_smul_eq
#print axioms
  ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addTripleSumCount_phaseSet_indep_of_scalar
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addThreeAPCount_smul_eq
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addThreeAPCount_phaseSet_indep_of_scalar
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addLinearPatternCount_smul_eq
#print axioms
  ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addLinearPatternCount_phaseSet_indep_of_scalar
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addLinearPatternFiberCounts_smul_eq
#print axioms
  ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addLinearPatternFiberCounts_phaseSet_indep_of_scalar
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addLinearPatternMaxFiber_smul_eq
#print axioms
  ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addLinearPatternMaxFiber_phaseSet_indep_of_scalar
#print axioms
  ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.not_addLinearPatternMaxFiber_scalar_improvement
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addLinearPatternFiberMultiplicity_smul_eq
#print axioms
  ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addLinearPatternFiberMultiplicity_phaseSet_indep_of_scalar
#print axioms
  ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.not_addLinearPatternFiberMultiplicity_scalar_improvement
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addEnergy_smul_eq
#print axioms
  ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addEnergy_phaseSet_indep_of_scalar
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.not_addEnergy_scalar_improvement
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addEnergyK_smul_eq
#print axioms
  ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addEnergyK_phaseSet_indep_of_scalar
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.not_addEnergyK_scalar_improvement
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addKSumCount_smul_eq
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addKSumFiberCounts_smul_eq
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addKSumMaxFiber_smul_eq
#print axioms
  ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addKSumMaxFiber_phaseSet_indep_of_scalar
#print axioms
  ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.not_addKSumMaxFiber_scalar_improvement
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addSystemPatternCount_smul_eq
#print axioms
  ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addSystemPatternCount_phaseSet_indep_of_scalar
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addSystemPatternFiberCounts_smul_eq
#print axioms
  ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addSystemPatternFiberCounts_phaseSet_indep_of_scalar
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addSystemPatternMaxFiber_smul_eq
#print axioms
  ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addSystemPatternMaxFiber_phaseSet_indep_of_scalar
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addSystemPatternFiberMultiplicity_smul_eq
#print axioms
  ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addSystemPatternFiberMultiplicity_phaseSet_indep_of_scalar
#print axioms
  ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.not_addSystemPatternCount_scalar_improvement
#print axioms
  ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.not_addSystemPatternMaxFiber_scalar_improvement
#print axioms
  ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.not_addSystemPatternFiberMultiplicity_scalar_improvement

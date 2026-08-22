/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R366CenteredRelationAnomaly
import Mathlib.Algebra.Order.Chebyshev

/-!
# G88: cross-orbit first incidence — the orbit-class Parseval decomposition of the deep wall

Issue #505 (fork `lalalune/ArkLib`), DIRECT route.  After R382 (within-orbit rigidity: the
triangle inequality on a rotation block is an equality), R384/R385/G76 (generator averaging and
higher distinct-generator moments carry no slack), OC-EQUI (unweighted embedding coverage is
all-or-nothing), and G75/G77/G80 (raw-sign, Fourier-gauge, and signed-l1 formulations all pin to
the wall), the surviving uncontrolled object was the CROSS-ORBIT signed interaction: how the
single-embedding first-incidence weighted relation mass distributes across genuinely distinct
relation orbits.

This file proves that this interaction is completely rigid, in two layers.

## Layer 1 — pair-level: the cross-orbit collision trichotomy

Take the rotation frames `{g^j · c}` and `{g^k · c'}` of two field values at an exact-order
generator `g` (`orderOf g = n`).  `frameCollisionCount g n c c'` counts colliding frame pairs.
We prove it is QUANTIZED:

* both values in the evaluation kernel: `n^2` (total coherence);
* both nonzero and in the same `n`-th-power class `c^n = c'^n` (equivalently, the same
  `⟨g⟩`-coset): exactly `n` — a FIRST incidence forces exactly `n` incidences, never more,
  never fewer (`frameCollisionCount_eq_of_incident`);
* genuinely distinct classes: exactly `0` — full cross-orbit orthogonality.

For the signed (DC-centered, R367-normalized) pair mass `crossFrameSigned` this gives the exact
values `n^2·(q-1)`, `n·(q-n)`, `-n^2`; in particular at production scale `q > n` a single first
incidence across distinct non-kernel orbits already makes the pair's signed mass strictly
POSITIVE: no signed cancellation is available from same-class cross-orbit interactions, and
cross-class interactions carry no collision mass at all — only the flat DC term.

## Layer 2 — global: the orbit-class Parseval identity at production depth

Let `R(c) = repRF g n r c` be the depth-`r` representation mass (the production weights), let
`S₀ = R(0)` be the kernel-class mass and, for each class label `γ ∈ orbitClassSet`,
let `S_γ = orbitClassMass` be the total mass of the class fiber.  We prove the EXACT identity

```text
n · centeredShadowMass = q · ( n·S₀² + Σ_γ S_γ² ) − n · n^(2r).
```

The DC-subtracted deep-wall numerator is a POSITIVE-SEMIDEFINITE quadratic form in the orbit-class
masses (minus the DC constant): a sum of squares over genuinely distinct relation orbit classes,
with NO cross-class terms.  Inputs: rotation invariance of the representation profile
(`repRF_mul_left`, proven at tuple level), the `n`-element class fibers, and constancy of `R` on
each fiber.  Corollaries:

* `kernel_sq_le_centeredShadowMass` — dropping the class squares: the kernel mass alone forces
  `q·S₀² − n^(2r) ≤ centeredShadowMass`; no cross-orbit cancellation can go below the kernel term;
* `centeredShadowMass_le_kernel_concentration` — Cauchy–Schwarz: total concentration in ONE class
  is extremal, `n·centeredShadowMass ≤ q·(n·S₀² + (n^r − S₀)²) − n·n^(2r)`; the entire cross-orbit
  freedom is bracketed by functions of the single kernel-class mass `S₀`;
* `equidistribution_minimizes_centeredShadowMass` — Chebyshev: equidistribution of first-incidence
  mass across the classes is the minimizing configuration;
* `relationAnomaly_orbitClassParseval` — the same identity for R366's `relationAnomaly`;
* `dcEnergyBound_iff_orbitClassParseval_le` — the production wall `DCEnergyBound` is EXACTLY a
  bound on the orbit-class quadratic form: the #505 formulation is quantitatively identical to
  the BGK/Paley wall, now in cross-orbit coordinates.

Finally `weighted_crossFrame_eq_centeredShadowMass` welds the two layers: the `repRF`-weighted
sum of the pair-level signed frame masses over ALL value pairs is exactly
`n^2 · centeredShadowMass`.

## Honest scope

These are exact identities and two-sided brackets, not a proof of `DCEnergyBound`: the size of
the kernel mass `S₀ = repRF g n r 0` and of the realized class masses remains the open
arithmetic content (the wall).  What is new: cross-orbit interaction carries no sign degrees of
freedom (orthogonality + positivity), so any future bound on the centered mass reduces to
bounding the `ℓ²`-profile `(S₀, (S_γ)_γ)` — and conversely no cross-orbit reshuffling argument
can beat the kernel floor.  CORE remains OPEN / ON-BGK.

Issue #505.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence

open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.R365CenteredShadowMassWeld
open ArkLib.ProximityGap.Frontier.R366CenteredRelationAnomaly

/-! ## The orbit-class combinatorics of the value field -/

/-- All nonzero values of the coefficient field. -/
def nonkernelValues (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset F :=
  Finset.univ.filter (fun c => c ≠ 0)

/-- Labels of the genuinely distinct nonzero rotation-orbit classes: the `n`-th powers.  Two
nonzero values are in the same `⟨g⟩`-rotation class iff they have the same label
(`exists_pow_mul_of_class_eq`). -/
def orbitClassSet (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) : Finset F :=
  (nonkernelValues F).image (fun c => c ^ n)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The fiber of nonzero values in the class labelled `γ`. -/
def orbitClassFiber (n : ℕ) (γ : F) : Finset F :=
  (nonkernelValues F).filter (fun c => c ^ n = γ)

theorem mem_orbitClassFiber_iff {n : ℕ} {γ x : F} :
    x ∈ orbitClassFiber n γ ↔ x ≠ 0 ∧ x ^ n = γ := by
  simp [orbitClassFiber, nonkernelValues]

/-! ## Exponent arithmetic at an exact-order generator -/

/-- Power comparison at a nonzero field element is exponent congruence mod the order. -/
theorem pow_eq_pow_iff_modEq_orderOf (g : F) (hg0 : g ≠ 0) {a b : ℕ} :
    g ^ a = g ^ b ↔ a ≡ b [MOD orderOf g] := by
  constructor
  · intro h
    rcases le_total a b with hab | hab
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
      have hk : g ^ k = 1 := by
        have h1 : g ^ a * g ^ k = g ^ a * 1 := by
          rw [mul_one, ← pow_add]
          exact h.symm
        exact mul_left_cancel₀ (pow_ne_zero a hg0) h1
      exact (Nat.modEq_iff_dvd' (Nat.le_add_right a k)).mpr
        (by simpa using orderOf_dvd_of_pow_eq_one hk)
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
      have hk : g ^ k = 1 := by
        have h1 : g ^ b * g ^ k = g ^ b * 1 := by
          rw [mul_one, ← pow_add]
          exact h
        exact mul_left_cancel₀ (pow_ne_zero b hg0) h1
      exact ((Nat.modEq_iff_dvd' (Nat.le_add_right b k)).mpr
        (by simpa using orderOf_dvd_of_pow_eq_one hk)).symm
  · intro h
    calc g ^ a = g ^ (a % orderOf g) := (pow_mod_orderOf g a).symm
      _ = g ^ (b % orderOf g) := by rw [show a % orderOf g = b % orderOf g from h]
      _ = g ^ b := pow_mod_orderOf g b

/-- Exponents below the order are determined by the power. -/
theorem pow_val_inj (g : F) (n : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    {a b : ℕ} (ha : a < n) (hb : b < n) (h : g ^ a = g ^ b) : a = b := by
  have hmod := (pow_eq_pow_iff_modEq_orderOf g hg0).mp h
  rwa [Nat.ModEq, hord, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod

/-- Multiplying by a power of `g` preserves the class label. -/
theorem pow_mul_class (g : F) (n : ℕ) (hord : orderOf g = n) (s : ℕ) (c : F) :
    (g ^ s * c) ^ n = c ^ n := by
  have hgn : g ^ n = 1 := by rw [← hord]; exact pow_orderOf_eq_one g
  rw [mul_pow, ← pow_mul, mul_comm s n, pow_mul, hgn, one_pow, one_mul]

/-- **Class labels detect the rotation coset**: two nonzero values share an `n`-th power iff one
is a `⟨g⟩`-rotate of the other.  (Since `orderOf g = n`, the `n` powers of `g` exhaust the
`n`-th roots of unity of the field.) -/
theorem exists_pow_mul_of_class_eq (g : F) (n : ℕ) (hn : 0 < n) (hord : orderOf g = n)
    {c c' : F} (hc' : c' ≠ 0) (hclass : c ^ n = c' ^ n) :
    ∃ s < n, c = g ^ s * c' := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hprim : IsPrimitiveRoot g n := by
    rw [← hord]
    exact IsPrimitiveRoot.orderOf g
  have hξ : (c * c'⁻¹) ^ n = 1 := by
    rw [mul_pow, hclass, inv_pow, mul_inv_cancel₀ (pow_ne_zero n hc')]
  obtain ⟨s, hs, hgs⟩ := hprim.eq_pow_of_pow_eq_one hξ
  refine ⟨s, hs, ?_⟩
  rw [hgs, inv_mul_cancel_right₀ hc']

/-! ## Rotation invariance of the production representation profile

The depth-`r` representation count `repRF` is invariant under multiplying the target value by
`g`: rotating the value corresponds to the index shift `t ↦ finRotate ∘ t` on `r`-tuples of
root indices.  This is the field-value avatar of the shadow-level `rotZ` invariances
(R371/R372), proven here directly at tuple level so it needs only `orderOf g = n`. -/

/-- One cyclic index step multiplies the root power by `g`. -/
theorem pow_finRotate_val (g : F) (n : ℕ) (hn : 0 < n) (hord : orderOf g = n) (a : Fin n) :
    g ^ ((finRotate n a : Fin n) : ℕ) = g * g ^ ((a : ℕ)) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  by_cases h : a = Fin.last n'
  · subst h
    rw [finRotate_last]
    have hcycle : g * g ^ ((Fin.last n' : ℕ)) = 1 := by
      rw [Fin.val_last, ← pow_succ', ← hord]
      exact pow_orderOf_eq_one g
    rw [hcycle]
    simp
  · rw [coe_finRotate_of_ne_last h, pow_succ']

/-- Shifting every index of a tuple multiplies its `r`-fold power sum by `g`. -/
theorem gsumR_comp_finRotate (g : F) (n r : ℕ) (hn : 0 < n) (hord : orderOf g = n)
    (t : Fin r → Fin n) :
    gsumR g n r (fun i => finRotate n (t i)) = g * gsumR g n r t := by
  unfold gsumR
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => pow_finRotate_val g n hn hord (t i))

/-- **Rotation invariance of the representation profile** (within-orbit rigidity at the
field-value level): `repRF (g·c) = repRF c`. -/
theorem repRF_mul_left (g : F) (n r : ℕ) (hg0 : g ≠ 0) (hn : 0 < n)
    (hord : orderOf g = n) (c : F) :
    repRF g n r (g * c) = repRF g n r c := by
  classical
  unfold repRF
  symm
  refine Finset.card_bij' (fun t _ => fun i => finRotate n (t i))
    (fun t _ => fun i => (finRotate n).symm (t i)) ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_filter] at ht ⊢
    exact ⟨Finset.mem_univ _, by rw [gsumR_comp_finRotate g n r hn hord t, ht.2]⟩
  · intro t ht
    rw [Finset.mem_filter] at ht ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have h1 : gsumR g n r (fun i => finRotate n ((finRotate n).symm (t i))) =
        g * gsumR g n r (fun i => (finRotate n).symm (t i)) :=
      gsumR_comp_finRotate g n r hn hord _
    simp only [Equiv.apply_symm_apply] at h1
    apply mul_left_cancel₀ hg0
    rw [← h1]
    exact ht.2
  · intro t _
    funext i
    exact (finRotate n).symm_apply_apply (t i)
  · intro t _
    funext i
    exact (finRotate n).apply_symm_apply (t i)

/-- Rotation invariance for every power of `g`. -/
theorem repRF_pow_mul (g : F) (n r : ℕ) (hg0 : g ≠ 0) (hn : 0 < n)
    (hord : orderOf g = n) (s : ℕ) (c : F) :
    repRF g n r (g ^ s * c) = repRF g n r c := by
  induction s with
  | zero => rw [pow_zero, one_mul]
  | succ k ih =>
      rw [pow_succ', mul_assoc, repRF_mul_left g n r hg0 hn hord, ih]

/-! ## Class fibers: `n` elements each, constant representation mass -/

/-- The class fiber of a nonzero value is its exact `⟨g⟩`-rotation coset. -/
theorem orbitClassFiber_eq_image (g : F) (n : ℕ) (hg0 : g ≠ 0) (hn : 0 < n)
    (hord : orderOf g = n) {c : F} (hc : c ≠ 0) :
    orbitClassFiber n (c ^ n) = (Finset.range n).image (fun s => g ^ s * c) := by
  ext x
  rw [mem_orbitClassFiber_iff, Finset.mem_image]
  constructor
  · rintro ⟨hx0, hxc⟩
    obtain ⟨s, hs, rfl⟩ := exists_pow_mul_of_class_eq g n hn hord hc hxc
    exact ⟨s, Finset.mem_range.mpr hs, rfl⟩
  · rintro ⟨s, _, rfl⟩
    exact ⟨mul_ne_zero (pow_ne_zero s hg0) hc, pow_mul_class g n hord s c⟩

/-- Every nonzero class fiber has exactly `n` elements. -/
theorem card_orbitClassFiber (g : F) (n : ℕ) (hg0 : g ≠ 0) (hn : 0 < n)
    (hord : orderOf g = n) {c : F} (hc : c ≠ 0) :
    (orbitClassFiber n (c ^ n)).card = n := by
  rw [orbitClassFiber_eq_image g n hg0 hn hord hc]
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  exact pow_val_inj g n hg0 hord ha hb (mul_right_cancel₀ hc hab)

/-- The representation mass is constant on every class fiber. -/
theorem repRF_constant_on_orbitClassFiber (g : F) (n r : ℕ) (hg0 : g ≠ 0) (hn : 0 < n)
    (hord : orderOf g = n) {c₀ : F} (hc₀ : c₀ ≠ 0) {c : F}
    (hc : c ∈ orbitClassFiber n (c₀ ^ n)) :
    repRF g n r c = repRF g n r c₀ := by
  obtain ⟨hcne, hclass⟩ := mem_orbitClassFiber_iff.mp hc
  obtain ⟨s, _, rfl⟩ := exists_pow_mul_of_class_eq g n hn hord hc₀ hclass
  exact repRF_pow_mul g n r hg0 hn hord s c₀

/-! ## Layer 1: the cross-orbit collision trichotomy -/

/-- Number of colliding rotation-frame pairs between the `g`-frames of two field values. -/
def frameCollisionCount (g : F) (n : ℕ) (c c' : F) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun p => g ^ ((p.1 : ℕ)) * c = g ^ ((p.2 : ℕ)) * c')).card

/-- Kernel–kernel frames are totally coherent: all `n^2` pairs collide. -/
theorem frameCollisionCount_kernel_kernel (g : F) (n : ℕ) :
    frameCollisionCount g n 0 0 = n ^ 2 := by
  unfold frameCollisionCount
  rw [Finset.filter_true_of_mem (fun p _ => by rw [mul_zero, mul_zero]), Finset.card_univ]
  simp [sq]

/-- A kernel frame never collides with a nonzero frame. -/
theorem frameCollisionCount_kernel_left (g : F) (n : ℕ) (hg0 : g ≠ 0)
    {c' : F} (hc' : c' ≠ 0) :
    frameCollisionCount g n 0 c' = 0 := by
  unfold frameCollisionCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _
  rw [mul_zero]
  exact fun h => (mul_ne_zero (pow_ne_zero _ hg0) hc') h.symm

/-- A nonzero frame never collides with a kernel frame. -/
theorem frameCollisionCount_kernel_right (g : F) (n : ℕ) (hg0 : g ≠ 0)
    {c : F} (hc : c ≠ 0) :
    frameCollisionCount g n c 0 = 0 := by
  unfold frameCollisionCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _
  rw [mul_zero]
  exact mul_ne_zero (pow_ne_zero _ hg0) hc

/-- **Cross-orbit orthogonality**: frames of genuinely distinct classes never collide. -/
theorem frameCollisionCount_cross_class (g : F) (n : ℕ) (hord : orderOf g = n)
    {c c' : F} (hclass : c ^ n ≠ c' ^ n) :
    frameCollisionCount g n c c' = 0 := by
  unfold frameCollisionCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _ heq
  apply hclass
  have hgn : g ^ n = 1 := by rw [← hord]; exact pow_orderOf_eq_one g
  have h1 : (g ^ ((p.1 : ℕ)) * c) ^ n = (g ^ ((p.2 : ℕ)) * c') ^ n := by rw [heq]
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm ((p.1 : ℕ)) n,
    mul_comm ((p.2 : ℕ)) n, pow_mul, pow_mul, hgn, one_pow, one_pow, one_mul, one_mul] at h1
  exact h1

/-- **Same-class collision quantization**: nonzero frames in one class collide in EXACTLY `n`
pairs — one per relative rotation offset. -/
theorem frameCollisionCount_same_class (g : F) (n : ℕ) (hg0 : g ≠ 0) (hn : 0 < n)
    (hord : orderOf g = n) {c c' : F} (hc' : c' ≠ 0) (hclass : c ^ n = c' ^ n) :
    frameCollisionCount g n c c' = n := by
  obtain ⟨s, hs, rfl⟩ := exists_pow_mul_of_class_eq g n hn hord hc' hclass
  unfold frameCollisionCount
  conv_rhs => rw [← Fintype.card_fin n, ← Finset.card_univ]
  refine Finset.card_bij (fun p _ => p.1) (fun p _ => Finset.mem_univ _) ?_ ?_
  · intro p hp p' hp' hfst
    have hfst' : p.1 = p'.1 := hfst
    rw [Finset.mem_filter] at hp hp'
    have h1 := hp.2
    have h2 := hp'.2
    rw [← hfst'] at h2
    have h3 : g ^ ((p.2 : ℕ)) * c' = g ^ ((p'.2 : ℕ)) * c' := h1.symm.trans h2
    have h4 : g ^ ((p.2 : ℕ)) = g ^ ((p'.2 : ℕ)) := mul_right_cancel₀ hc' h3
    have h5 : ((p.2 : ℕ)) = ((p'.2 : ℕ)) := pow_val_inj g n hg0 hord p.2.isLt p'.2.isLt h4
    exact Prod.ext hfst' (Fin.ext h5)
  · intro b _
    refine ⟨(b, ⟨((b : ℕ) + s) % n, Nat.mod_lt _ hn⟩), ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show g ^ ((b : ℕ)) * (g ^ s * c') = g ^ (((b : ℕ) + s) % n) * c'
    have hmod : g ^ (((b : ℕ) + s) % n) = g ^ ((b : ℕ) + s) := by
      have hpm := pow_mod_orderOf g ((b : ℕ) + s)
      rwa [hord] at hpm
    rw [hmod, ← mul_assoc, ← pow_add]

/-- **First incidence forces exact quantization**: if two nonzero frames collide at all, they
are in the same class and collide in exactly `n` pairs. -/
theorem frameCollisionCount_eq_of_incident (g : F) (n : ℕ) (hg0 : g ≠ 0) (hn : 0 < n)
    (hord : orderOf g = n) {c c' : F} (hc' : c' ≠ 0)
    (hpos : 0 < frameCollisionCount g n c c') :
    c ^ n = c' ^ n ∧ frameCollisionCount g n c c' = n := by
  by_cases hclass : c ^ n = c' ^ n
  · exact ⟨hclass, frameCollisionCount_same_class g n hg0 hn hord hc' hclass⟩
  · rw [frameCollisionCount_cross_class g n hord hclass] at hpos
    exact absurd hpos (lt_irrefl 0)

/-- **The collision trichotomy**: every cross-frame collision count is `0`, `n`, or `n^2`. -/
theorem frameCollisionCount_trichotomy (g : F) (n : ℕ) (hg0 : g ≠ 0) (hn : 0 < n)
    (hord : orderOf g = n) (c c' : F) :
    frameCollisionCount g n c c' = 0 ∨ frameCollisionCount g n c c' = n ∨
      frameCollisionCount g n c c' = n ^ 2 := by
  by_cases hc : c = 0
  · by_cases hc' : c' = 0
    · subst hc; subst hc'
      exact Or.inr (Or.inr (frameCollisionCount_kernel_kernel g n))
    · subst hc
      exact Or.inl (frameCollisionCount_kernel_left g n hg0 hc')
  · by_cases hc' : c' = 0
    · subst hc'
      exact Or.inl (frameCollisionCount_kernel_right g n hg0 hc)
    · by_cases hclass : c ^ n = c' ^ n
      · exact Or.inr (Or.inl (frameCollisionCount_same_class g n hg0 hn hord hc' hclass))
      · exact Or.inl (frameCollisionCount_cross_class g n hord hclass)

/-- The signed (R367-normalized) cross-frame pair mass between two rotation frames. -/
noncomputable def crossFrameSigned (g : F) (n : ℕ) (c c' : F) : ℝ :=
  ∑ p : Fin n × Fin n,
    ((Fintype.card F : ℝ) *
      (if g ^ ((p.1 : ℕ)) * c = g ^ ((p.2 : ℕ)) * c' then 1 else 0) - 1)

/-- The signed cross-frame mass in closed form. -/
theorem crossFrameSigned_eq (g : F) (n : ℕ) (c c' : F) :
    crossFrameSigned g n c c' =
      (Fintype.card F : ℝ) * (frameCollisionCount g n c c' : ℝ) - ((n : ℝ)) ^ 2 := by
  unfold crossFrameSigned frameCollisionCount
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const,
    Finset.card_univ]
  simp only [Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  ring

/-- Genuinely distinct classes interact ONLY through the flat DC term. -/
theorem crossFrameSigned_cross_orbit (g : F) (n : ℕ) (hord : orderOf g = n)
    {c c' : F} (hclass : c ^ n ≠ c' ^ n) :
    crossFrameSigned g n c c' = -((n : ℝ)) ^ 2 := by
  rw [crossFrameSigned_eq, frameCollisionCount_cross_class g n hord hclass]
  simp

/-- A same-class pair of nonzero frames carries the exact signed mass `n(q - n)`. -/
theorem crossFrameSigned_first_incidence (g : F) (n : ℕ) (hg0 : g ≠ 0) (hn : 0 < n)
    (hord : orderOf g = n) {c c' : F} (hc' : c' ≠ 0) (hclass : c ^ n = c' ^ n) :
    crossFrameSigned g n c c' = (n : ℝ) * ((Fintype.card F : ℝ) - (n : ℝ)) := by
  rw [crossFrameSigned_eq, frameCollisionCount_same_class g n hg0 hn hord hc' hclass]
  ring

/-- **First-incidence positivity**: at production scale (`q > n`) a single first incidence
across distinct non-kernel orbits makes the signed pair mass strictly positive — same-class
cross-orbit interaction offers NO signed cancellation. -/
theorem crossFrameSigned_pos_of_first_incidence (g : F) (n : ℕ) (hg0 : g ≠ 0) (hn : 0 < n)
    (hord : orderOf g = n) {c c' : F} (hc' : c' ≠ 0) (hclass : c ^ n = c' ^ n)
    (hbig : (n : ℝ) < (Fintype.card F : ℝ)) :
    0 < crossFrameSigned g n c c' := by
  rw [crossFrameSigned_first_incidence g n hg0 hn hord hc' hclass]
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact mul_pos hn0 (by linarith)

/-! ## Layer 2: the orbit-class Parseval identity at production depth -/

/-- Total representation mass of one orbit class (production weights `repRF`). -/
noncomputable def orbitClassMass (g : F) (n r : ℕ) (γ : F) : ℝ :=
  ∑ c ∈ orbitClassFiber n γ, (repRF g n r c : ℝ)

/-- The class mass is `n` times the common representative mass. -/
theorem orbitClassMass_eq_card_mul (g : F) (n r : ℕ) (hg0 : g ≠ 0) (hn : 0 < n)
    (hord : orderOf g = n) {c₀ : F} (hc₀ : c₀ ≠ 0) :
    orbitClassMass g n r (c₀ ^ n) = (n : ℝ) * (repRF g n r c₀ : ℝ) := by
  unfold orbitClassMass
  rw [Finset.sum_congr rfl (fun c hc => by
    rw [repRF_constant_on_orbitClassFiber g n r hg0 hn hord hc₀ hc])]
  rw [Finset.sum_const, card_orbitClassFiber g n hg0 hn hord hc₀, nsmul_eq_mul]

/-- Per-class Parseval collapse: `n · Σ_fiber R(c)² = S_γ²`. -/
theorem mul_sum_sq_orbitClassFiber (g : F) (n r : ℕ) (hg0 : g ≠ 0) (hn : 0 < n)
    (hord : orderOf g = n) {c₀ : F} (hc₀ : c₀ ≠ 0) :
    (n : ℝ) * ∑ c ∈ orbitClassFiber n (c₀ ^ n), ((repRF g n r c : ℝ)) ^ 2 =
      orbitClassMass g n r (c₀ ^ n) ^ 2 := by
  have hsum : ∑ c ∈ orbitClassFiber n (c₀ ^ n), ((repRF g n r c : ℝ)) ^ 2 =
      (n : ℝ) * ((repRF g n r c₀ : ℝ)) ^ 2 := by
    rw [Finset.sum_congr rfl (fun c hc => by
      rw [repRF_constant_on_orbitClassFiber g n r hg0 hn hord hc₀ hc])]
    rw [Finset.sum_const, card_orbitClassFiber g n hg0 hn hord hc₀, nsmul_eq_mul]
  rw [hsum, orbitClassMass_eq_card_mul g n r hg0 hn hord hc₀]
  ring

/-- **Global Parseval collapse over the non-kernel spectrum**: the `ℓ²`-mass of the
representation profile is exactly the class-mass square sum, with NO cross-class terms. -/
theorem mul_sum_nonkernel_sq_eq_sum_orbitClassMass_sq (g : F) (n r : ℕ)
    (hg0 : g ≠ 0) (hn : 0 < n) (hord : orderOf g = n) :
    (n : ℝ) * ∑ c ∈ nonkernelValues F, ((repRF g n r c : ℝ)) ^ 2 =
      ∑ γ ∈ orbitClassSet F n, orbitClassMass g n r γ ^ 2 := by
  have hfib :
      ∑ γ ∈ orbitClassSet F n, ∑ c ∈ (nonkernelValues F).filter (fun c => c ^ n = γ),
          ((repRF g n r c : ℝ)) ^ 2 =
        ∑ c ∈ nonkernelValues F, ((repRF g n r c : ℝ)) ^ 2 :=
    Finset.sum_fiberwise_of_maps_to
      (fun c hc => Finset.mem_image_of_mem _ hc) _
  rw [← hfib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun γ hγ => ?_)
  simp only [orbitClassSet] at hγ
  obtain ⟨c₀, hc₀mem, rfl⟩ := Finset.mem_image.mp hγ
  have hc₀ : c₀ ≠ 0 := by
    simp only [nonkernelValues, Finset.mem_filter] at hc₀mem
    exact hc₀mem.2
  exact mul_sum_sq_orbitClassFiber g n r hg0 hn hord hc₀

/-- The total representation mass is the tuple count `n^r`. -/
theorem sum_repRF_eq_pow (g : F) (n r : ℕ) :
    ∑ c : F, repRF g n r c = n ^ r := by
  classical
  unfold repRF
  rw [← Finset.card_eq_sum_card_fiberwise
    (f := gsumR g n r) (s := Finset.univ) (t := Finset.univ)
    (fun t _ => Finset.mem_univ _)]
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

theorem nonkernelValues_eq_erase :
    nonkernelValues F = Finset.univ.erase 0 := by
  simp [nonkernelValues, Finset.filter_ne']

/-- Splitting an all-values sum into the kernel value and the non-kernel spectrum. -/
theorem sum_split_kernel (f : F → ℝ) :
    ∑ c : F, f c = f 0 + ∑ c ∈ nonkernelValues F, f c := by
  rw [nonkernelValues_eq_erase]
  exact (Finset.add_sum_erase Finset.univ f (Finset.mem_univ 0)).symm

/-- The non-kernel representation mass. -/
theorem sum_nonkernel_repRF_eq (g : F) (n r : ℕ) :
    ∑ c ∈ nonkernelValues F, (repRF g n r c : ℝ) =
      ((n : ℝ)) ^ r - (repRF g n r 0 : ℝ) := by
  have htot : ∑ c : F, (repRF g n r c : ℝ) = ((n : ℝ)) ^ r := by
    have hcast := congrArg (Nat.cast : ℕ → ℝ) (sum_repRF_eq_pow g n r)
    push_cast at hcast
    exact hcast
  have hsplit := sum_split_kernel (F := F) (fun c => (repRF g n r c : ℝ))
  rw [hsplit] at htot
  linarith

/-- Total class mass = total non-kernel mass. -/
theorem sum_orbitClassMass_eq (g : F) (n r : ℕ) :
    ∑ γ ∈ orbitClassSet F n, orbitClassMass g n r γ =
      ((n : ℝ)) ^ r - (repRF g n r 0 : ℝ) := by
  have hfib : ∑ γ ∈ orbitClassSet F n, orbitClassMass g n r γ =
      ∑ c ∈ nonkernelValues F, (repRF g n r c : ℝ) := by
    unfold orbitClassMass orbitClassFiber orbitClassSet
    exact Finset.sum_fiberwise_of_maps_to
      (fun c hc => Finset.mem_image_of_mem _ hc) _
  rw [hfib, sum_nonkernel_repRF_eq]

/-- **HEADLINE: the orbit-class Parseval identity.**  At production depth `r`, the DC-centered
deep-wall numerator is an exact positive-semidefinite quadratic form in the orbit-class masses:

`n · centeredShadowMass = q · (n·S₀² + Σ_γ S_γ²) − n · n^(2r)`.

Cross-orbit first-incidence structure enters ONLY through the per-class squares: genuinely
distinct relation orbit classes contribute no cross terms. -/
theorem centeredShadowMass_orbitClassParseval
    (g : F) (n m r : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    (n : ℝ) * centeredShadowMass g n m r =
      (Fintype.card F : ℝ) *
          ((n : ℝ) * (repRF g n r 0 : ℝ) ^ 2 +
            ∑ γ ∈ orbitClassSet F n, orbitClassMass g n r γ ^ 2) -
        (n : ℝ) * (n : ℝ) ^ (2 * r) := by
  have hn0 : 0 < n := by omega
  have hR312 := congrArg (Nat.cast : ℕ → ℝ)
    (depthR_energy_eq_shadowEnergy_add_collisionMass g n m r hm hn hg)
  push_cast at hR312
  have hsplit := sum_split_kernel (F := F) (fun c => ((repRF g n r c : ℝ)) ^ 2)
  have hparse := mul_sum_nonkernel_sq_eq_sum_orbitClassMass_sq g n r hg0 hn0 hord
  unfold centeredShadowMass
  rw [← hR312, hsplit, ← hparse]
  ring

/-- **Kernel floor**: no distribution of first-incidence mass across genuinely distinct orbits
can push the centered mass below the kernel-class term. -/
theorem kernel_sq_le_centeredShadowMass
    (g : F) (n m r : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    (Fintype.card F : ℝ) * (repRF g n r 0 : ℝ) ^ 2 - (n : ℝ) ^ (2 * r) ≤
      centeredShadowMass g n m r := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hpar := centeredShadowMass_orbitClassParseval g n m r hg0 hord hm hn hg
  have hS : (0 : ℝ) ≤ ∑ γ ∈ orbitClassSet F n, orbitClassMass g n r γ ^ 2 :=
    Finset.sum_nonneg fun γ _ => sq_nonneg _
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := Nat.cast_nonneg _
  have hmul : (n : ℝ) * ((Fintype.card F : ℝ) * (repRF g n r 0 : ℝ) ^ 2 -
      (n : ℝ) ^ (2 * r)) ≤ (n : ℝ) * centeredShadowMass g n m r := by
    rw [hpar]
    nlinarith [mul_nonneg hq hS]
  exact le_of_mul_le_mul_left hmul hn0

/-- **Concentration ceiling** (Cauchy–Schwarz over classes): total concentration of the
non-kernel mass in a single orbit class is extremal; the centered mass is bounded by a function
of the kernel-class mass alone. -/
theorem centeredShadowMass_le_kernel_concentration
    (g : F) (n m r : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    (n : ℝ) * centeredShadowMass g n m r ≤
      (Fintype.card F : ℝ) *
          ((n : ℝ) * (repRF g n r 0 : ℝ) ^ 2 +
            (((n : ℝ)) ^ r - (repRF g n r 0 : ℝ)) ^ 2) -
        (n : ℝ) * (n : ℝ) ^ (2 * r) := by
  have hpar := centeredShadowMass_orbitClassParseval g n m r hg0 hord hm hn hg
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := Nat.cast_nonneg _
  have hmassnn : ∀ γ ∈ orbitClassSet F n, 0 ≤ orbitClassMass g n r γ :=
    fun γ _ => Finset.sum_nonneg fun c _ => Nat.cast_nonneg _
  have hCS : ∑ γ ∈ orbitClassSet F n, orbitClassMass g n r γ ^ 2 ≤
      (∑ γ ∈ orbitClassSet F n, orbitClassMass g n r γ) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg hmassnn
  rw [sum_orbitClassMass_eq g n r] at hCS
  nlinarith [mul_le_mul_of_nonneg_left hCS hq]

/-- **Equidistribution floor** (Chebyshev over classes): spreading the non-kernel mass evenly
across the genuinely distinct orbit classes is the MINIMIZING configuration of the centered
mass. -/
theorem equidistribution_minimizes_centeredShadowMass
    (g : F) (n m r : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    (Fintype.card F : ℝ) *
        (((orbitClassSet F n).card : ℝ) * ((n : ℝ) * (repRF g n r 0 : ℝ) ^ 2) +
          (((n : ℝ)) ^ r - (repRF g n r 0 : ℝ)) ^ 2) -
      ((orbitClassSet F n).card : ℝ) * ((n : ℝ) * (n : ℝ) ^ (2 * r)) ≤
    ((orbitClassSet F n).card : ℝ) * ((n : ℝ) * centeredShadowMass g n m r) := by
  have hpar := centeredShadowMass_orbitClassParseval g n m r hg0 hord hm hn hg
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := Nat.cast_nonneg _
  have hCheb := sq_sum_le_card_mul_sum_sq
    (s := orbitClassSet F n) (f := orbitClassMass g n r)
  rw [sum_orbitClassMass_eq g n r] at hCheb
  have hcardpar : ((orbitClassSet F n).card : ℝ) *
      ((n : ℝ) * centeredShadowMass g n m r) =
      ((orbitClassSet F n).card : ℝ) *
        ((Fintype.card F : ℝ) *
            ((n : ℝ) * (repRF g n r 0 : ℝ) ^ 2 +
              ∑ γ ∈ orbitClassSet F n, orbitClassMass g n r γ ^ 2) -
          (n : ℝ) * (n : ℝ) ^ (2 * r)) := by
    rw [hpar]
  nlinarith [hcardpar, mul_le_mul_of_nonneg_left hCheb hq]

/-- The orbit-class Parseval identity for R366's `relationAnomaly`. -/
theorem relationAnomaly_orbitClassParseval
    (g : F) (n m r : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    (n : ℝ) * relationAnomaly g n m r =
      (Fintype.card F : ℝ) *
          ((n : ℝ) * (repRF g n r 0 : ℝ) ^ 2 +
            ∑ γ ∈ orbitClassSet F n, orbitClassMass g n r γ ^ 2) -
        (n : ℝ) * (n : ℝ) ^ (2 * r) -
        (n : ℝ) * (((Fintype.card F : ℝ) - 1) * (shadowEnergy n m r : ℝ)) := by
  have hpar := centeredShadowMass_orbitClassParseval g n m r hg0 hord hm hn hg
  have h366 := centeredShadowMass_eq_floor_add_relationAnomaly g n m r
  linear_combination hpar - (n : ℝ) * h366

/-- **The production wall in cross-orbit coordinates**: `DCEnergyBound` is EXACTLY a bound on
the orbit-class quadratic form.  The #505 cross-orbit formulation is quantitatively identical
to the BGK/Paley wall — no weaker sufficient condition hides in the orbit decomposition. -/
theorem dcEnergyBound_iff_orbitClassParseval_le
    (g : F) (n m r : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    DCEnergyBound (powerRootSet g n) r ↔
      (Fintype.card F : ℝ) *
          ((n : ℝ) * (repRF g n r 0 : ℝ) ^ 2 +
            ∑ γ ∈ orbitClassSet F n, orbitClassMass g n r γ ^ 2) ≤
        (n : ℝ) * ((Fintype.card F : ℝ) *
            ((Nat.doubleFactorial (2 * r - 1) : ℝ) *
              ((powerRootSet g n).card : ℝ) ^ r)) +
          (n : ℝ) * (n : ℝ) ^ (2 * r) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hpar := centeredShadowMass_orbitClassParseval g n m r hg0 hord hm hn hg
  rw [dcEnergyBound_iff_centeredShadowMass_le g n m r hg0 hord hm hn hg]
  constructor
  · intro h
    have h2 := mul_le_mul_of_nonneg_left h hn0.le
    linarith [hpar]
  · intro h
    have h2 : (n : ℝ) * centeredShadowMass g n m r ≤
        (n : ℝ) * ((Fintype.card F : ℝ) *
          ((Nat.doubleFactorial (2 * r - 1) : ℝ) *
            ((powerRootSet g n).card : ℝ) ^ r)) := by
      linarith [hpar]
    exact le_of_mul_le_mul_left h2 hn0

/-! ## The weld: frame-level pair masses reproduce the production centered mass -/

/-- For a fixed frame offset, the `repRF`-weighted collision indicator collapses to the
`ℓ²`-mass of the representation profile — the frame average sees no offset dependence. -/
theorem sum_sum_weighted_indicator (g : F) (n r : ℕ) (hg0 : g ≠ 0) (hn0 : 0 < n)
    (hord : orderOf g = n) (j k : Fin n) :
    (∑ c : F, ∑ c' : F, (repRF g n r c : ℝ) * (repRF g n r c' : ℝ) *
        (if g ^ ((j : ℕ)) * c = g ^ ((k : ℕ)) * c' then 1 else 0)) =
      ∑ u : F, ((repRF g n r u : ℝ)) ^ 2 := by
  have hgn : g ^ n = 1 := by rw [← hord]; exact pow_orderOf_eq_one g
  have hjle : (j : ℕ) ≤ n := le_of_lt j.isLt
  have hcond : ∀ c c' : F,
      (g ^ ((j : ℕ)) * c = g ^ ((k : ℕ)) * c') ↔
        c = g ^ ((n - (j : ℕ)) + (k : ℕ)) * c' := by
    intro c c'
    constructor
    · intro h
      have h2 : g ^ (n - (j : ℕ)) * (g ^ ((j : ℕ)) * c) =
          g ^ (n - (j : ℕ)) * (g ^ ((k : ℕ)) * c') := by rw [h]
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hjle, hgn, one_mul,
        ← mul_assoc, ← pow_add] at h2
      exact h2
    · intro h
      rw [h, ← mul_assoc, ← pow_add,
        show (j : ℕ) + ((n - (j : ℕ)) + (k : ℕ)) = n + (k : ℕ) by omega,
        pow_add, hgn, one_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c' _ => ?_)
  calc
    ∑ c : F, (repRF g n r c : ℝ) * (repRF g n r c' : ℝ) *
        (if g ^ ((j : ℕ)) * c = g ^ ((k : ℕ)) * c' then 1 else 0) =
      ∑ c : F, (if c = g ^ ((n - (j : ℕ)) + (k : ℕ)) * c' then
          (repRF g n r c : ℝ) * (repRF g n r c' : ℝ) else 0) := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        by_cases h : g ^ ((j : ℕ)) * c = g ^ ((k : ℕ)) * c'
        · rw [if_pos h, if_pos ((hcond c c').mp h), mul_one]
        · rw [if_neg h, if_neg (fun hc => h ((hcond c c').mpr hc)), mul_zero]
    _ = (repRF g n r (g ^ ((n - (j : ℕ)) + (k : ℕ)) * c') : ℝ) *
          (repRF g n r c' : ℝ) := by
        rw [Finset.sum_ite_eq' Finset.univ]
        simp
    _ = ((repRF g n r c' : ℝ)) ^ 2 := by
        rw [repRF_pow_mul g n r hg0 hn0 hord]
        ring

/-- **The weld.**  The `repRF`-weighted total of the pair-level signed frame masses over ALL
value pairs is exactly `n^2` times the production centered mass: the Layer-1 trichotomy is the
complete pair-local mechanism behind the Layer-2 Parseval identity. -/
theorem weighted_crossFrame_eq_centeredShadowMass
    (g : F) (n m r : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    (∑ c : F, ∑ c' : F, (repRF g n r c : ℝ) * (repRF g n r c' : ℝ) *
        crossFrameSigned g n c c') =
      (n : ℝ) ^ 2 * centeredShadowMass g n m r := by
  have hn0 : 0 < n := by omega
  have hR312 := congrArg (Nat.cast : ℕ → ℝ)
    (depthR_energy_eq_shadowEnergy_add_collisionMass g n m r hm hn hg)
  push_cast at hR312
  have hRtot : ∑ c : F, (repRF g n r c : ℝ) = ((n : ℝ)) ^ r := by
    have hcast := congrArg (Nat.cast : ℕ → ℝ) (sum_repRF_eq_pow g n r)
    push_cast at hcast
    exact hcast
  have hprod : ∑ c : F, ∑ c' : F, (repRF g n r c : ℝ) * (repRF g n r c' : ℝ) =
      (((n : ℝ)) ^ r) ^ 2 := by
    rw [← Finset.sum_mul_sum, hRtot]
    ring
  have hper : ∀ p : Fin n × Fin n,
      (∑ c : F, ∑ c' : F, (repRF g n r c : ℝ) * (repRF g n r c' : ℝ) *
        ((Fintype.card F : ℝ) *
          (if g ^ ((p.1 : ℕ)) * c = g ^ ((p.2 : ℕ)) * c' then 1 else 0) - 1)) =
      (Fintype.card F : ℝ) * (∑ u : F, ((repRF g n r u : ℝ)) ^ 2) -
        (((n : ℝ)) ^ r) ^ 2 := by
    intro p
    have hkey := sum_sum_weighted_indicator g n r hg0 hn0 hord p.1 p.2
    have hpull : ∑ c : F, ∑ c' : F, (Fintype.card F : ℝ) *
          ((repRF g n r c : ℝ) * (repRF g n r c' : ℝ) *
            (if g ^ ((p.1 : ℕ)) * c = g ^ ((p.2 : ℕ)) * c' then 1 else 0)) =
        (Fintype.card F : ℝ) * ∑ c : F, ∑ c' : F,
          (repRF g n r c : ℝ) * (repRF g n r c' : ℝ) *
            (if g ^ ((p.1 : ℕ)) * c = g ^ ((p.2 : ℕ)) * c' then 1 else 0) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun c _ => by rw [Finset.mul_sum])
    calc
      (∑ c : F, ∑ c' : F, (repRF g n r c : ℝ) * (repRF g n r c' : ℝ) *
          ((Fintype.card F : ℝ) *
            (if g ^ ((p.1 : ℕ)) * c = g ^ ((p.2 : ℕ)) * c' then 1 else 0) - 1)) =
        ∑ c : F, ((∑ c' : F, (Fintype.card F : ℝ) *
            ((repRF g n r c : ℝ) * (repRF g n r c' : ℝ) *
              (if g ^ ((p.1 : ℕ)) * c = g ^ ((p.2 : ℕ)) * c' then 1 else 0))) -
          ∑ c' : F, (repRF g n r c : ℝ) * (repRF g n r c' : ℝ)) := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun c' _ => by ring)
      _ = (∑ c : F, ∑ c' : F, (Fintype.card F : ℝ) *
            ((repRF g n r c : ℝ) * (repRF g n r c' : ℝ) *
              (if g ^ ((p.1 : ℕ)) * c = g ^ ((p.2 : ℕ)) * c' then 1 else 0))) -
          ∑ c : F, ∑ c' : F, (repRF g n r c : ℝ) * (repRF g n r c' : ℝ) := by
          rw [Finset.sum_sub_distrib]
      _ = (Fintype.card F : ℝ) * (∑ u : F, ((repRF g n r u : ℝ)) ^ 2) -
            (((n : ℝ)) ^ r) ^ 2 := by
          rw [hpull, hkey, hprod]
  calc
    (∑ c : F, ∑ c' : F, (repRF g n r c : ℝ) * (repRF g n r c' : ℝ) *
        crossFrameSigned g n c c') =
      ∑ c : F, ∑ c' : F, ∑ p : Fin n × Fin n,
        (repRF g n r c : ℝ) * (repRF g n r c' : ℝ) *
          ((Fintype.card F : ℝ) *
            (if g ^ ((p.1 : ℕ)) * c = g ^ ((p.2 : ℕ)) * c' then 1 else 0) - 1) := by
        refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun c' _ => ?_))
        unfold crossFrameSigned
        rw [Finset.mul_sum]
    _ = ∑ c : F, ∑ p : Fin n × Fin n, ∑ c' : F,
        (repRF g n r c : ℝ) * (repRF g n r c' : ℝ) *
          ((Fintype.card F : ℝ) *
            (if g ^ ((p.1 : ℕ)) * c = g ^ ((p.2 : ℕ)) * c' then 1 else 0) - 1) :=
        Finset.sum_congr rfl (fun c _ => Finset.sum_comm)
    _ = ∑ p : Fin n × Fin n, ∑ c : F, ∑ c' : F,
        (repRF g n r c : ℝ) * (repRF g n r c' : ℝ) *
          ((Fintype.card F : ℝ) *
            (if g ^ ((p.1 : ℕ)) * c = g ^ ((p.2 : ℕ)) * c' then 1 else 0) - 1) :=
        Finset.sum_comm
    _ = ∑ _p : Fin n × Fin n,
        ((Fintype.card F : ℝ) * (∑ u : F, ((repRF g n r u : ℝ)) ^ 2) -
          (((n : ℝ)) ^ r) ^ 2) :=
        Finset.sum_congr rfl (fun p _ => hper p)
    _ = (n : ℝ) ^ 2 * ((Fintype.card F : ℝ) * (∑ u : F, ((repRF g n r u : ℝ)) ^ 2) -
          (((n : ℝ)) ^ r) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ]
        simp only [Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ = (n : ℝ) ^ 2 * centeredShadowMass g n m r := by
        unfold centeredShadowMass
        rw [← hR312]
        ring

end ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.pow_eq_pow_iff_modEq_orderOf
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.pow_val_inj
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.pow_mul_class
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.exists_pow_mul_of_class_eq
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.pow_finRotate_val
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.gsumR_comp_finRotate
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.repRF_mul_left
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.repRF_pow_mul
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.orbitClassFiber_eq_image
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.card_orbitClassFiber
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.repRF_constant_on_orbitClassFiber
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.frameCollisionCount_kernel_kernel
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.frameCollisionCount_kernel_left
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.frameCollisionCount_kernel_right
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.frameCollisionCount_cross_class
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.frameCollisionCount_same_class
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.frameCollisionCount_eq_of_incident
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.frameCollisionCount_trichotomy
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.crossFrameSigned_eq
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.crossFrameSigned_cross_orbit
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.crossFrameSigned_first_incidence
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.crossFrameSigned_pos_of_first_incidence
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.orbitClassMass_eq_card_mul
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.mul_sum_sq_orbitClassFiber
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.mul_sum_nonkernel_sq_eq_sum_orbitClassMass_sq
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.sum_repRF_eq_pow
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.sum_nonkernel_repRF_eq
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.sum_orbitClassMass_eq
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.centeredShadowMass_orbitClassParseval
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.kernel_sq_le_centeredShadowMass
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.centeredShadowMass_le_kernel_concentration
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.equidistribution_minimizes_centeredShadowMass
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.relationAnomaly_orbitClassParseval
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.dcEnergyBound_iff_orbitClassParseval_le
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.sum_sum_weighted_indicator
#print axioms
  ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence.weighted_crossFrame_eq_centeredShadowMass

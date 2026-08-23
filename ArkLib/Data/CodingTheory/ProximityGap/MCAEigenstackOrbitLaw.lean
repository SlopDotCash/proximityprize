/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAEquivariance
import ArkLib.Data.CodingTheory.ProximityGap.DeltaStarExactPinF5

/-!
# The eigenstack orbit law (#357 S3, layer 2 on the equivariance engine)

`MCAEquivariance.lean` provides the per-`γ`/probability-level symmetry laws of `mcaEvent`
(codeword translation, stack scaling, direction scaling ↔ `γ`-multiplication, shift ↔
`γ`-translation, code-preserving domain permutations) and the orbit-section reduction for
`epsMCA`. This file proves the **structure theorem those symmetries imply for individual
stacks**, and the counting law the exact-`ε_mca` probes measured:

* `mcaEvent_eigenstack_iff` — **the eigenstack orbit law.** If `C` is stable under a domain
  permutation `σ` and the stack is a *`σ`-eigenstack* — `u₀ ∘ σ = a•u₀ + b•u₁`,
  `u₁ ∘ σ = c•u₁` with `a, c ≠ 0` — then the bad-scalar set is invariant under the affine
  reparametrization `T(γ) = a⁻¹b + γ·(a⁻¹c)`.
* `orderOf_le_card_of_mul_mem` / `orderOf_dvd_card_of_mul_mem` — orbit arithmetic for
  multiplicatively invariant scalar `Finset`s: a nonzero member forces the whole orbit
  (`ord(α) ≤ card`), and avoidance of `0` forces exact divisibility (`ord(α) ∣ card`).
* `orderOf_le_badScalarSet_card_of_eigenstack` / `orderOf_dvd_badScalarSet_card_of_eigenstack`
  — the combination: for a multiplicative eigenstack the bad-scalar count is
  `ε + (#orbits)·ord(a⁻¹c)` with `ε ∈ {0,1}` — **field-independent orbit arithmetic**.

This is the mechanism behind the probes' "flat numerator": at the `(13,12,6)` plateau rung
the worst-case bad-scalar count is exactly `12 = n` at `p = 13, 37, 61` because the
maximizer is a rotation eigenstack whose bad set is **one full order-12 orbit** (probe
`probe_s3_eigenstack_orbit_law.py`, pre-registered and exact: the entire profile
`1, 2, 3, 12, 13` is orbit arithmetic — fixed point, antipodal pair (σ⁶), ω-triple (σ⁴),
one order-12 orbit, orbit + fixed point). The [KKH26] near-capacity bad line is *also* an
eigenstack (eigenratio `g^{−m}` of order `s`) — the ceiling construction and the toy-scale
plateau maximizers are one object class.

## Demo

At `C = RS[F₅, F₅*, 2]` (`DeltaStarExactPinF5`), the stack `(x³, x²)` is a rotation
eigenstack with `T(γ) = 3γ` of order `4`; **one** explicit badness certificate at `γ = 1`
plus the orbit law reproduce the sharp bound `ε_mca(C, 1/4) ≥ 4/5` that
`DeltaStarExactPinF5` obtained from four hand-built certificates
(`DemoF5.epsMCA_C542_quarter_ge_via_orbit`).

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  ePrint 2026/680. (Definition 4.3.)
* [KKH26] Krachun, Kazanin, Haböck. ePrint 2026/782.
* Issue #357, hypothesis S3 of the 2026-06-11 nine-hypothesis campaign; #334 item A5.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.MCAEigenstack

open scoped NNReal ProbabilityTheory ENNReal
open ProximityGap Code ProximityGap.MCAEquivariance

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## The bad-scalar set (`Finset`-level counting API) -/

open Classical in
/-- The set of bad scalars of a stack at radius `δ` (the numerator of the stack's `epsMCA`
term). -/
noncomputable def badScalarSet (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) : Finset F :=
  Finset.univ.filter (fun γ => mcaEvent (F := F) C δ u₀ u₁ γ)

open Classical in
theorem mem_badScalarSet {C : Set (ι → A)} {δ : ℝ≥0} {u₀ u₁ : ι → A} {γ : F} :
    γ ∈ badScalarSet (F := F) C δ u₀ u₁ ↔ mcaEvent (F := F) C δ u₀ u₁ γ := by
  simp [badScalarSet]

open Classical in
/-- The probability of the bad event is the bad-scalar count over `|F|`. -/
theorem prob_mcaEvent_eq_badScalarSet_card (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) C δ u₀ u₁ γ]
      = ((badScalarSet (F := F) C δ u₀ u₁).card : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
  rw [prob_uniform_eq_card_filter_div_card]
  rfl

/-! ## The eigenstack orbit law -/

/-- **The eigenstack affine-reparametrization law.** If `C` is stable under the domain
permutation `σ` (both directions) and `(u₀, u₁)` is a `σ`-eigenstack —
`u₀ ∘ σ = a • u₀ + b • u₁` and `u₁ ∘ σ = c • u₁` with `a, c ≠ 0` — then badness at
`T(γ) = a⁻¹·b + γ·(a⁻¹·c)` is equivalent to badness at `γ`: the bad-scalar set is invariant
under the affine map `T`. -/
theorem mcaEvent_eigenstack_iff (C : Submodule F (ι → A)) (δ : ℝ≥0) (σ : Equiv.Perm ι)
    (hσ : ∀ w ∈ C, w ∘ ⇑σ ∈ C) (hσ' : ∀ w ∈ C, w ∘ ⇑σ⁻¹ ∈ C)
    {u₀ u₁ : ι → A} {a b c : F} (ha : a ≠ 0) (hc : c ≠ 0)
    (h₀ : u₀ ∘ σ = a • u₀ + b • u₁) (h₁ : u₁ ∘ σ = c • u₁) (γ : F) :
    mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ (a⁻¹ * b + γ * (a⁻¹ * c)) ↔
      mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ := by
  have key₀ : a • (u₀ + (a⁻¹ * b) • u₁) = u₀ ∘ σ := by
    rw [h₀, smul_add, smul_smul, mul_inv_cancel_left₀ ha]
  have key₁ : a • ((a⁻¹ * c) • u₁) = u₁ ∘ σ := by
    rw [h₁, smul_smul, mul_inv_cancel_left₀ ha]
  have hac : a⁻¹ * c ≠ 0 := mul_ne_zero (inv_ne_zero ha) hc
  calc mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ (a⁻¹ * b + γ * (a⁻¹ * c))
      ↔ mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ + (a⁻¹ * b) • u₁) u₁ (γ * (a⁻¹ * c)) :=
        (mcaEvent_shift C (a⁻¹ * b) (γ * (a⁻¹ * c))).symm
    _ ↔ mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ + (a⁻¹ * b) • u₁) ((a⁻¹ * c) • u₁) γ :=
        (mcaEvent_smul_right C hac γ).symm
    _ ↔ mcaEvent (F := F) (C : Set (ι → A)) δ
          (a • (u₀ + (a⁻¹ * b) • u₁)) (a • ((a⁻¹ * c) • u₁)) γ :=
        (mcaEvent_smul_both C ha γ).symm
    _ ↔ mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ ∘ ⇑σ) (u₁ ∘ ⇑σ) γ := by
        rw [key₀, key₁]
    _ ↔ mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ :=
        mcaEvent_comp_perm_iff C σ hσ hσ'

/-! ## Orbit arithmetic over the scalar field -/

/-- **Orbit injection.** A finite scalar set invariant under multiplication by a unit `α`
and containing a nonzero element has at least `ord(α)` elements: the whole multiplicative
orbit of that element is inside. -/
theorem orderOf_le_card_of_mul_mem {α : Fˣ} {S : Finset F}
    (hinv : ∀ γ ∈ S, (α : F) * γ ∈ S) {γ₀ : F} (h₀ : γ₀ ∈ S) (hne : γ₀ ≠ 0) :
    orderOf α ≤ S.card := by
  classical
  have hmem : ∀ j : ℕ, ((α : F) ^ j) * γ₀ ∈ S := by
    intro j
    induction j with
    | zero => simpa using h₀
    | succ j ih =>
      have := hinv _ ih
      rwa [← mul_assoc, ← pow_succ'] at this
  have hinj : Set.InjOn (fun j : ℕ => ((α : F) ^ j) * γ₀)
      (Set.Iio (orderOf α)) := by
    intro i hi j hj hij
    have hcancel : ((α : F)) ^ i = ((α : F)) ^ j :=
      mul_right_cancel₀ hne hij
    have hu : (α ^ i : Fˣ) = α ^ j := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
      exact hcancel
    exact pow_injOn_Iio_orderOf hi hj hu
  calc orderOf α
      = ((Finset.range (orderOf α)).image (fun j => ((α : F) ^ j) * γ₀)).card := by
        rw [Finset.card_image_of_injOn (by rwa [Finset.coe_range])]
        rw [Finset.card_range]
    _ ≤ S.card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
        exact hmem j

/-- **Orbit divisibility.** A finite scalar set invariant under multiplication by a unit `α`
and avoiding `0` has cardinality divisible by `ord(α)`: it is a disjoint union of full
multiplicative orbits. -/
theorem orderOf_dvd_card_of_mul_mem {α : Fˣ} (S : Finset F) :
    (∀ γ ∈ S, (α : F) * γ ∈ S) → (0 : F) ∉ S → orderOf α ∣ S.card := by
  classical
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro hinv h0
    rcases S.eq_empty_or_nonempty with rfl | ⟨γ₀, hγ₀⟩
    · simp
    · have hne : γ₀ ≠ 0 := fun h => h0 (h ▸ hγ₀)
      have hd1 : 1 ≤ orderOf α := orderOf_pos α
      have hmem : ∀ j : ℕ, ((α : F) ^ j) * γ₀ ∈ S := by
        intro j
        induction j with
        | zero => simpa using hγ₀
        | succ j ihj =>
          have := hinv _ ihj
          rwa [← mul_assoc, ← pow_succ'] at this
      set d := orderOf α with hd
      set O : Finset F := (Finset.range d).image (fun j => ((α : F) ^ j) * γ₀) with hO
      have hOsub : O ⊆ S := by
        intro x hx
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
        exact hmem j
      have hinj : Set.InjOn (fun j : ℕ => ((α : F) ^ j) * γ₀) (Set.Iio d) := by
        intro i hi j hj hij
        have hcancel : ((α : F)) ^ i = ((α : F)) ^ j := mul_right_cancel₀ hne hij
        have hu : (α ^ i : Fˣ) = α ^ j := by
          apply Units.ext
          rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
          exact hcancel
        exact pow_injOn_Iio_orderOf hi hj hu
      have hOcard : O.card = d := by
        rw [hO, Finset.card_image_of_injOn (by rwa [Finset.coe_range]),
          Finset.card_range]
      have hONe : O.Nonempty := ⟨γ₀, by
        rw [hO]
        exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hd1, by simp⟩⟩
      have hpow_d : ((α : F)) ^ d = 1 := by
        have := pow_orderOf_eq_one α
        calc ((α : F)) ^ d = ((α ^ d : Fˣ) : F) := by
              rw [Units.val_pow_eq_pow_val]
          _ = ((1 : Fˣ) : F) := by rw [hd, this]
          _ = 1 := Units.val_one
      have hinv' : ∀ γ ∈ S \ O, (α : F) * γ ∈ S \ O := by
        intro γ hγ
        rw [Finset.mem_sdiff] at hγ ⊢
        refine ⟨hinv _ hγ.1, fun hmemO => hγ.2 ?_⟩
        obtain ⟨j, hj, hjeq⟩ := Finset.mem_image.mp hmemO
        rw [Finset.mem_range] at hj
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · -- α γ = γ₀ ⟹ γ = α^{d-1} γ₀
          simp only [pow_zero, one_mul] at hjeq
          have : γ = ((α : F) ^ (d - 1)) * γ₀ := by
            have hαne : (α : F) ≠ 0 := Units.ne_zero α
            apply mul_left_cancel₀ hαne
            rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hd1, hpow_d, one_mul]
            exact hjeq.symm
          rw [this, hO]
          exact Finset.mem_image.mpr ⟨d - 1, Finset.mem_range.mpr (by omega), rfl⟩
        · -- α γ = α^j γ₀ ⟹ γ = α^{j-1} γ₀
          have : γ = ((α : F) ^ (j - 1)) * γ₀ := by
            have hαne : (α : F) ≠ 0 := Units.ne_zero α
            apply mul_left_cancel₀ hαne
            rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hjpos]
            exact hjeq.symm
          rw [this, hO]
          exact Finset.mem_image.mpr ⟨j - 1, Finset.mem_range.mpr (by omega), rfl⟩
      have h0' : (0 : F) ∉ S \ O := fun h => h0 (Finset.mem_sdiff.mp h).1
      have hss : S \ O ⊂ S := Finset.sdiff_ssubset hOsub hONe
      have hdvd' := ih (S \ O) hss hinv' h0'
      have hcards : S.card = (S \ O).card + d := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hOsub, hOcard]
        have hle := Finset.card_le_card hOsub
        rw [hOcard] at hle
        omega
      rw [hcards]
      exact Nat.dvd_add hdvd' dvd_rfl

/-! ## The orbit law for eigenstack bad sets -/

/-- **Lower propagation.** For a `σ`-stable submodule code and a multiplicative
`σ`-eigenstack (`u₀ ∘ σ = a • u₀`, `u₁ ∘ σ = c • u₁`, `a, c ≠ 0`), one bad nonzero scalar
forces at least `ord(a⁻¹c)` bad scalars: the entire multiplicative orbit is bad. This is
the mechanism behind the probes' field-independent "flat numerator". -/
theorem orderOf_le_badScalarSet_card_of_eigenstack
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (σ : Equiv.Perm ι)
    (hσ : ∀ w ∈ C, w ∘ ⇑σ ∈ C) (hσ' : ∀ w ∈ C, w ∘ ⇑σ⁻¹ ∈ C)
    {u₀ u₁ : ι → A} {a c : F} (ha : a ≠ 0) (hc : c ≠ 0)
    (h₀ : u₀ ∘ σ = a • u₀) (h₁ : u₁ ∘ σ = c • u₁)
    {γ₀ : F} (hbad : mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ₀) (hne : γ₀ ≠ 0) :
    orderOf (Units.mk0 (a⁻¹ * c) (mul_ne_zero (inv_ne_zero ha) hc))
      ≤ (badScalarSet (F := F) (C : Set (ι → A)) δ u₀ u₁).card := by
  classical
  have h₀' : u₀ ∘ σ = a • u₀ + (0 : F) • u₁ := by rw [zero_smul, add_zero, h₀]
  refine orderOf_le_card_of_mul_mem (fun γ hγ => ?_) (mem_badScalarSet.mpr hbad) hne
  rw [mem_badScalarSet] at hγ ⊢
  have := (mcaEvent_eigenstack_iff C δ σ hσ hσ' ha hc h₀' h₁ γ).mpr hγ
  have harith : a⁻¹ * 0 + γ * (a⁻¹ * c) = (Units.mk0 (a⁻¹ * c)
      (mul_ne_zero (inv_ne_zero ha) hc) : F) * γ := by
    rw [Units.val_mk0]
    ring
  rwa [harith] at this

/-- **Divisibility.** Under the same hypotheses, if the scalar `0` is not bad, the
bad-scalar count is exactly divisible by `ord(a⁻¹c)`: the bad set is a disjoint union of
full multiplicative orbits. Together with the lower-propagation form this gives the orbit
arithmetic `count = ε + (#orbits)·ord(a⁻¹c)` measured by the exact probes. -/
theorem orderOf_dvd_badScalarSet_card_of_eigenstack
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (σ : Equiv.Perm ι)
    (hσ : ∀ w ∈ C, w ∘ ⇑σ ∈ C) (hσ' : ∀ w ∈ C, w ∘ ⇑σ⁻¹ ∈ C)
    {u₀ u₁ : ι → A} {a c : F} (ha : a ≠ 0) (hc : c ≠ 0)
    (h₀ : u₀ ∘ σ = a • u₀) (h₁ : u₁ ∘ σ = c • u₁)
    (h0bad : ¬ mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ (0 : F)) :
    orderOf (Units.mk0 (a⁻¹ * c) (mul_ne_zero (inv_ne_zero ha) hc))
      ∣ (badScalarSet (F := F) (C : Set (ι → A)) δ u₀ u₁).card := by
  classical
  have h₀' : u₀ ∘ σ = a • u₀ + (0 : F) • u₁ := by rw [zero_smul, add_zero, h₀]
  refine orderOf_dvd_card_of_mul_mem _ (fun γ hγ => ?_) ?_
  · rw [mem_badScalarSet] at hγ ⊢
    have := (mcaEvent_eigenstack_iff C δ σ hσ hσ' ha hc h₀' h₁ γ).mpr hγ
    have harith : a⁻¹ * 0 + γ * (a⁻¹ * c) = (Units.mk0 (a⁻¹ * c)
        (mul_ne_zero (inv_ne_zero ha) hc) : F) * γ := by
      rw [Units.val_mk0]
      ring
    rwa [harith] at this
  · exact fun h => h0bad (mem_badScalarSet.mp h)

/-! ## Demo: the engine at `RS[F₅, F₅*, 2]`

One explicit certificate + the orbit law reproduce the sharp lower bound that
`DeltaStarExactPinF5` assembled from four certificates. -/

namespace DemoF5

open ProximityGap.DeltaStarExactPin

/-- The domain rotation of `F₅* = (1, 2, 4, 3)` (multiplication by the generator `2`),
as the index cycle `i ↦ i + 1` on `Fin 4`. -/
def rot : Equiv.Perm (Fin 4) where
  toFun i := i + 1
  invFun i := i - 1
  left_inv := by decide
  right_inv := by decide

theorem dom_rot : ∀ i, dom (rot i) = 2 * dom i := by decide

theorem dom_rot_inv : ∀ i, dom (rot⁻¹ i) = 3 * dom i := by decide

/-- `C542` is stable under the domain rotation (forward direction). -/
theorem C542_rot_mem : ∀ w ∈ C542, w ∘ ⇑rot ∈ C542 := by
  rintro w ⟨A, B, rfl⟩
  refine ⟨A, 2 * B, ?_⟩
  funext i
  show lineEval A B (rot i) = lineEval A (2 * B) i
  simp only [lineEval, dom_rot i]
  ring

/-- `C542` is stable under the inverse rotation. -/
theorem C542_rot_inv_mem : ∀ w ∈ C542, w ∘ ⇑rot⁻¹ ∈ C542 := by
  rintro w ⟨A, B, rfl⟩
  refine ⟨A, 3 * B, ?_⟩
  funext i
  show lineEval A B (rot⁻¹ i) = lineEval A (3 * B) i
  simp only [lineEval, dom_rot_inv i]
  ring

/-- First demo row: the pure frequency `x³` on the domain `(1,2,4,3)`. -/
def w₀ : Fin 4 → F5 := ![1, 3, 4, 2]

/-- Second demo row: the pure frequency `x²` on the domain `(1,2,4,3)`. -/
def w₁ : Fin 4 → F5 := ![1, 4, 1, 4]

/-- `(w₀, w₁)` is a rotation-eigenstack: `w₀ ∘ rot = 3 • w₀`. -/
theorem w₀_eigen : w₀ ∘ ⇑rot = (3 : F5) • w₀ := by decide

/-- `w₁ ∘ rot = 4 • w₁`. -/
theorem w₁_eigen : w₁ ∘ ⇑rot = (4 : F5) • w₁ := by decide

/-- The single explicit badness certificate: `γ = 1` is bad for `(w₀, w₁)` at `δ = 1/4`
(witness set `{1,2,3}`, interpolating codeword `4 + 4·X`, second row not explainable). -/
theorem mcaEvent_demo_g1 :
    mcaEvent (F := F5) (C542 : Set (Fin 4 → F5)) (1/4) w₀ w₁ (1 : F5) := by
  refine ⟨{1, 2, 3}, card_cond (by decide), ⟨lineEval 4 4, lineEval_mem 4 4, by decide⟩, ?_⟩
  exact not_pairJointAgreesOn_of_row1 (by decide)

/-- **The orbit law in action:** the order of `3⁻¹ * 4 = 3` in `F₅ˣ` is `4`, so the single
certificate propagates to at least `4` bad scalars. -/
theorem badScalarSet_demo_ge_four :
    4 ≤ (badScalarSet (F := F5) (C542 : Set (Fin 4 → F5)) (1/4) w₀ w₁).card := by
  have h := orderOf_le_badScalarSet_card_of_eigenstack C542 (1/4) rot
    C542_rot_mem C542_rot_inv_mem
    (a := 3) (c := 4) (by decide) (by decide) w₀_eigen w₁_eigen
    mcaEvent_demo_g1 (by decide)
  have hord : orderOf (Units.mk0 ((3 : F5)⁻¹ * 4)
      (mul_ne_zero (inv_ne_zero (by decide)) (by decide))) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro m hm hm0
    rcases m with _ | _ | _ | _ | m
    · omega
    · decide
    · decide
    · decide
    · omega
  rwa [hord] at h

open Classical in
/-- **The R1 lower bound, re-derived by symmetry:** `ε_mca(C542, 1/4) ≥ 4/5` from one
certificate plus the orbit law (versus the four explicit certificates of
`DeltaStarExactPinF5.epsMCA_C542_quarter_ge`). -/
theorem epsMCA_C542_quarter_ge_via_orbit :
    (4 : ℝ≥0∞) / 5 ≤ epsMCA (F := F5) (A := F5) (C542 : Set (Fin 4 → F5)) (1/4) := by
  have hle := badScalarSet_demo_ge_four
  have hbound := mcaEvent_prob_le_epsMCA (F := F5) (A := F5)
    (C542 : Set (Fin 4 → F5)) (1/4) ![w₀, w₁]
  rw [show (![w₀, w₁] : WordStack F5 (Fin 2) (Fin 4)) 0 = w₀ from rfl,
    show (![w₀, w₁] : WordStack F5 (Fin 2) (Fin 4)) 1 = w₁ from rfl,
    prob_mcaEvent_eq_badScalarSet_card] at hbound
  refine le_trans ?_ hbound
  have hF : ((Fintype.card F5 : ℝ≥0) : ℝ≥0∞) = 5 := by
    rw [show Fintype.card F5 = 5 from by simp [ZMod.card]]
    norm_num
  rw [hF]
  gcongr
  exact_mod_cast hle

end DemoF5

/-! ## Source audit -/

#print axioms mcaEvent_eigenstack_iff
#print axioms orderOf_le_card_of_mul_mem
#print axioms orderOf_dvd_card_of_mul_mem
#print axioms orderOf_le_badScalarSet_card_of_eigenstack
#print axioms orderOf_dvd_badScalarSet_card_of_eigenstack
#print axioms DemoF5.epsMCA_C542_quarter_ge_via_orbit

end ProximityGap.MCAEigenstack

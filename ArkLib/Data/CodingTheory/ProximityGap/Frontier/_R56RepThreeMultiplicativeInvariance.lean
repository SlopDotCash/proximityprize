/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R55Depth3VarianceReformulation

/-!
# LANE B2 (#466 round 56): THE MULTIPLICATIVE SYMMETRY OF THE REPRESENTATION FUNCTION

Round 55 recast the depth-3 target as the ℓ²-flatness deficit of `rep3 G`.  This brick exploits
the one piece of structure that is special to `G = μ_n` and absent from a generic set: `G` is a
**multiplicative subgroup**, so the additive representation function inherits a multiplicative
symmetry.

  **`rep3_smul`** :  for `a ∈ G`, `rep3 G (a * c) = rep3 G c`.

Proof: `x ↦ a⁻¹ x` is a bijection of `G` (subgroup closure), and it carries the triples summing
to `a·c` onto the triples summing to `c`.

**Consequence (the sharpened lens).**  `rep3 G` is constant on each multiplicative coset `a·H`
of `G`.  So the flatness deficit `∑_c (q·rep3 G c − |G|³)²` — the DC-subtracted energy (round 55)
— is really a sum over the `(q−1)/|G|` **cosets** (the Gauss-period orbits), each contributing
`|G|` equal terms, plus the `c = 0` point:

  `∑_c (q·rep3(c) − |G|³)² = (deficit at 0) + |G| · ∑_{cosets O} (q·rep3(O) − |G|³)²`.

i.e. the depth-3 flatness problem has only `(q−1)/|G|` genuine degrees of freedom (the distinct
Gauss periods), NOT `q`.  This is exactly the reduction to the Gauss-period index set
`𝔽_q^* / G` that the character-sum picture also sees (each nontrivial `η_b` depends only on the
coset of `b`), now made explicit on the additive side.

`rep3_orbit_const` packages the coset-constancy.  This does not break the wall (the per-coset
values are still governed by Paley/BGK), but it is the correct structural normalization of the
round-55 variance and a genuinely `μ_n`-specific fact.  Issue #466, round 56.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance

open ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation
open ArkLib.ProximityGap.Frontier.R53Depth3ExcessHeadroom

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Natural supremum / upper-levelset bridge.**  For a finite nonempty index set and a
natural-valued weight, proving the supremum is strictly below a natural threshold is exactly the
same as proving the upper levelset `{i | T ≤ w i}` has cardinality zero.  This is the counting
socket used by the R56 high-`rep3` exclusions. -/
theorem nat_sup_lt_iff_upper_levelset_card_zero {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (w : ι → ℕ) (T : ℕ) :
    s.sup w < T ↔ (s.filter (fun i => T ≤ w i)).card = 0 := by
  classical
  constructor
  · intro hsup
    by_contra hne
    rcases Finset.card_pos.mp (Nat.pos_of_ne_zero hne) with ⟨i, hi⟩
    have hi_mem : i ∈ s := (Finset.mem_filter.mp hi).1
    have hT_le : T ≤ w i := (Finset.mem_filter.mp hi).2
    have hwi_le : w i ≤ s.sup w := Finset.le_sup hi_mem
    omega
  · intro hzero
    by_contra hnot
    have hT_le_sup : T ≤ s.sup w := Nat.le_of_not_gt hnot
    obtain ⟨i, hi_mem, hsup_eq⟩ := Finset.exists_mem_eq_sup s hs w
    have hT_le_i : T ≤ w i := by
      simpa [hsup_eq] using hT_le_sup
    have hi_filter : i ∈ s.filter (fun i => T ≤ w i) :=
      Finset.mem_filter.mpr ⟨hi_mem, hT_le_i⟩
    have hpos : 0 < (s.filter (fun i => T ≤ w i)).card :=
      Finset.card_pos.mpr ⟨i, hi_filter⟩
    omega

/-- **Natural supremum / successor-levelset bridge.**  For a finite nonempty index set and a
natural-valued weight, a supremum bound `≤ T` is equivalent to emptiness of the successor
upper-levelset `{i | T + 1 ≤ w i}`.  This is the exact shape needed when a real bound is
rounded down by `Nat.floor`. -/
theorem nat_sup_le_iff_succ_upper_levelset_card_zero {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (w : ι → ℕ) (T : ℕ) :
    s.sup w ≤ T ↔ (s.filter (fun i => T + 1 ≤ w i)).card = 0 := by
  have hbridge := nat_sup_lt_iff_upper_levelset_card_zero s hs w (T + 1)
  rw [← hbridge]
  constructor <;> omega

/-- **Pointwise successor-levelset bridge.**  If the successor upper-levelset
`{i | T + 1 ≤ w i}` is empty, every element of `s` has weight at most `T`.  This is the
pointwise counterpart of `nat_sup_le_iff_succ_upper_levelset_card_zero`. -/
theorem le_of_succ_upper_levelset_card_zero {ι : Type*}
    (s : Finset ι) (w : ι → ℕ) (T : ℕ)
    (hzero : (s.filter (fun i => T + 1 ≤ w i)).card = 0)
    {i : ι} (hi : i ∈ s) :
    w i ≤ T := by
  classical
  by_contra hnot
  have hsucc : T + 1 ≤ w i := Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot)
  have hi_filter : i ∈ s.filter (fun i => T + 1 ≤ w i) :=
    Finset.mem_filter.mpr ⟨hi, hsucc⟩
  have hpos : 0 < (s.filter (fun i => T + 1 ≤ w i)).card :=
    Finset.card_pos.mpr ⟨i, hi_filter⟩
  omega

/-- **Multiplicative invariance of the 3-fold representation function.**  If `G` is closed under
multiplication and inverses and avoids `0` (a multiplicative subgroup), then for `a ∈ G` and any
target `c`, `rep3 G (a * c) = rep3 G c`. -/
theorem rep3_smul (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {a : F} (ha : a ∈ G) (c : F) :
    rep3 G (a * c) = rep3 G c := by
  classical
  have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
  have hainv : a⁻¹ ∈ G := hinv ha
  -- the multiplication-by-`a` bijection of `G`
  have hmemA : ∀ x : F, a * x ∈ G ↔ x ∈ G := by
    intro x
    constructor
    · intro hx
      have : a⁻¹ * (a * x) ∈ G := hmul hainv hx
      rwa [← mul_assoc, inv_mul_cancel₀ ha0, one_mul] at this
    · intro hx; exact hmul ha hx
  -- reindexing helper: `x ↦ a·x` permutes `G`, so `∑_{y∈G} f(a·y) = ∑_{y∈G} f y`
  have hreindex : ∀ f : F → ℕ, ∑ y ∈ G, f (a * y) = ∑ y ∈ G, f y := by
    intro f
    refine Finset.sum_nbij' (i := fun y => a * y) (j := fun y => a⁻¹ * y)
      (fun y hy => (hmemA y).mpr hy) (fun y hy => hmul hainv hy)
      (fun y _ => inv_mul_cancel_left₀ ha0 y)
      (fun y _ => mul_inv_cancel_left₀ ha0 y)
      (fun y _ => rfl)
  unfold rep3
  -- reindex the three `G`-sums of the `a·c`-target energy by `yᵢ ↦ a·yᵢ`
  rw [← hreindex (fun y₁ => ∑ y₂ ∈ G, ∑ y₃ ∈ G, if y₁ + y₂ + y₃ = a * c then 1 else 0)]
  refine Finset.sum_congr rfl (fun y₁ _ => ?_)
  rw [← hreindex (fun y₂ => ∑ y₃ ∈ G, if a * y₁ + y₂ + y₃ = a * c then 1 else 0)]
  refine Finset.sum_congr rfl (fun y₂ _ => ?_)
  rw [← hreindex (fun y₃ => if a * y₁ + a * y₂ + y₃ = a * c then 1 else 0)]
  refine Finset.sum_congr rfl (fun y₃ _ => ?_)
  -- pointwise: `a·y₁ + a·y₂ + a·y₃ = a·c  ↔  y₁ + y₂ + y₃ = c`
  rw [show a * y₁ + a * y₂ + a * y₃ = a * (y₁ + y₂ + y₃) by ring]
  simp only [mul_right_inj' ha0]

/-- **Coset-constancy.**  `rep3 G` is constant on each multiplicative coset of `G`: if
`a, a' ∈ G` then `rep3 G (a * c) = rep3 G (a' * c)`. -/
theorem rep3_orbit_const (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {a a' : F} (ha : a ∈ G) (ha' : a' ∈ G) (c : F) :
    rep3 G (a * c) = rep3 G (a' * c) := by
  rw [rep3_smul G hmul hinv h0 ha c, rep3_smul G hmul hinv h0 ha' c]

/-- **The round-55 variance summand is multiplicatively invariant.**  The whole flatness
defect term attached to `c` is constant along every multiplicative `G`-orbit. -/
theorem rep3_varianceSummand_smul (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {a : F} (ha : a ∈ G) (c : F) :
    ((Fintype.card F : ℝ) * (rep3 G (a * c) : ℝ) - (G.card : ℝ) ^ 3) ^ 2
      = ((Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3) ^ 2 := by
  rw [rep3_smul G hmul hinv h0 ha c]

/-- **Coset-constancy of the round-55 variance summand.**  This is the additive-side mirror of
Gauss-period coset reduction: after excluding `0`, the depth-3 flatness budget is constant on
each multiplicative coset of `G`. -/
theorem rep3_varianceSummand_orbit_const (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {a a' : F} (ha : a ∈ G) (ha' : a' ∈ G) (c : F) :
    ((Fintype.card F : ℝ) * (rep3 G (a * c) : ℝ) - (G.card : ℝ) ^ 3) ^ 2
      = ((Fintype.card F : ℝ) * (rep3 G (a' * c) : ℝ) - (G.card : ℝ) ^ 3) ^ 2 := by
  rw [rep3_smul G hmul hinv h0 ha c, rep3_smul G hmul hinv h0 ha' c]

/-- **Raw orbit contribution.**  Summing `rep3` over one multiplicative `G`-orbit just
multiplies the representative value by `|G|`. -/
theorem rep3_orbit_sum_eq_card_mul (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) (c : F) :
    ∑ x ∈ G, rep3 G (x * c) = G.card * rep3 G c := by
  classical
  calc ∑ x ∈ G, rep3 G (x * c)
      = ∑ _x ∈ G, rep3 G c := by
        refine Finset.sum_congr rfl (fun x hx => ?_)
        exact rep3_smul G hmul hinv h0 hx c
    _ = G.card * rep3 G c := by
        simp [Finset.sum_const]

/-- **Variance orbit contribution.**  The R55 flatness/variance budget over a multiplicative
`G`-orbit is `|G|` times the representative summand.  This is the machine-checked form of the
round-56 coset normalization. -/
theorem rep3_varianceSummand_orbit_sum_eq_card_mul (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) (c : F) :
    ∑ x ∈ G,
        ((Fintype.card F : ℝ) * (rep3 G (x * c) : ℝ) - (G.card : ℝ) ^ 3) ^ 2
      = (G.card : ℝ)
        * ((Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3) ^ 2 := by
  classical
  calc ∑ x ∈ G,
        ((Fintype.card F : ℝ) * (rep3 G (x * c) : ℝ) - (G.card : ℝ) ^ 3) ^ 2
      = ∑ _x ∈ G,
        ((Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3) ^ 2 := by
        refine Finset.sum_congr rfl (fun x hx => ?_)
        exact rep3_varianceSummand_smul G hmul hinv h0 hx c
    _ = (G.card : ℝ)
        * ((Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **Orbit share of the total variance.**  For nonzero `c`, the multiplicative `G`-orbit
through `c` injects into the full field, so its constant variance contribution is bounded by the
total R55 variance.  This is the first explicit `1 / |G|` quotient-normalized consequence of the
round-56 symmetry. -/
theorem rep3_varianceSummand_orbit_le_total (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) {c : F} (hc : c ≠ 0) :
    (G.card : ℝ)
        * ((Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3) ^ 2
      ≤ ∑ z : F, ((Fintype.card F : ℝ) * (rep3 G z : ℝ) - (G.card : ℝ) ^ 3) ^ 2 := by
  classical
  let f : F → ℝ :=
    fun z => ((Fintype.card F : ℝ) * (rep3 G z : ℝ) - (G.card : ℝ) ^ 3) ^ 2
  have hinj : ∀ ⦃x₁⦄, x₁ ∈ G → ∀ ⦃x₂⦄, x₂ ∈ G → x₁ * c = x₂ * c → x₁ = x₂ := by
    intro x₁ _ x₂ _ h
    exact mul_right_cancel₀ hc h
  have himage : ∑ z ∈ G.image (fun x => x * c), f z = ∑ x ∈ G, f (x * c) := by
    rw [Finset.sum_image]
    exact hinj
  have hsubset : G.image (fun x => x * c) ⊆ (Finset.univ : Finset F) := by
    intro z hz
    simp
  have hmass : ∑ z ∈ G.image (fun x => x * c), f z ≤ ∑ z : F, f z :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun z _ _ => by
      dsimp [f]
      positivity)
  have horbit := rep3_varianceSummand_orbit_sum_eq_card_mul G hmul hinv h0 c
  dsimp [f] at himage hmass
  rw [himage, horbit] at hmass
  exact hmass

/-- **Variance-flatness gives a quotient-normalized pointwise orbit budget.**  Under the R55
flatness target, every nonzero multiplicative orbit has representative variance at most
`15 q² |G|²` after dividing the total budget by its `|G|` equal points. -/
theorem rep3_varianceSummand_le_of_variance (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hvar : ∑ z : F,
        ((Fintype.card F : ℝ) * (rep3 G z : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3)
    {c : F} (hc : c ≠ 0) :
    ((Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3) ^ 2
      ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 2 := by
  have hshare := rep3_varianceSummand_orbit_le_total G hmul hinv h0 hc
  have hbudget : (G.card : ℝ)
        * ((Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3) ^ 2
      ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3 :=
    le_trans hshare hvar
  have hnpos : (0 : ℝ) < (G.card : ℝ) := by exact_mod_cast hGpos
  have htarget_mul : (G.card : ℝ)
        * (15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 2)
      = 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3 := by
    ring
  exact le_of_mul_le_mul_left (by rwa [htarget_mul]) hnpos

/-- **Deviation form of the quotient-normalized orbit budget.**  The same `1 / |G|` gain,
stated directly as a bound on the additive-convolution discrepancy
`q * rep3 G c - |G|³`. -/
theorem abs_rep3_deviation_le_of_variance (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hvar : ∑ z : F,
        ((Fintype.card F : ℝ) * (rep3 G z : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3)
    {c : F} (hc : c ≠ 0) :
    |(Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3|
      ≤ Real.sqrt 15 * (Fintype.card F : ℝ) * (G.card : ℝ) := by
  set D : ℝ := (Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3
  have hsq : D ^ 2 ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 2 := by
    simpa [D] using rep3_varianceSummand_le_of_variance G hmul hinv h0 hGpos hvar hc
  have htarget_nonneg : 0 ≤ Real.sqrt 15 * (Fintype.card F : ℝ) * (G.card : ℝ) := by
    positivity
  have hsqrt : Real.sqrt (D ^ 2)
      ≤ Real.sqrt ((Real.sqrt 15 * (Fintype.card F : ℝ) * (G.card : ℝ)) ^ 2) := by
    apply Real.sqrt_le_sqrt
    calc D ^ 2
        ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 2 := hsq
      _ = (Real.sqrt 15 * (Fintype.card F : ℝ) * (G.card : ℝ)) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)]
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq htarget_nonneg] at hsqrt

/-- **Concrete quadratic-excess deviation bound.**  The round-52/53 regime (`E = C |G|²`,
`C ≤ 44`, `|G| ≥ 40`) feeds the quotient-normalized R56 discrepancy estimate directly. -/
theorem abs_rep3_deviation_le_of_quadraticExcess {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) {C : ℝ}
    (hexc : Depth3ExcessBounded G (C * (G.card : ℝ) ^ 2))
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ))
    {c : F} (hc : c ≠ 0) :
    |(Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3|
      ≤ Real.sqrt 15 * (Fintype.card F : ℝ) * (G.card : ℝ) := by
  have hGposR : (0 : ℝ) < (G.card : ℝ) := by linarith
  have hGpos : 0 < G.card := by exact_mod_cast hGposR
  exact abs_rep3_deviation_le_of_variance G hmul hinv h0 hGpos
    (variance_bound_of_quadraticExcess hψ G hexc hC hn) hc

/-- **Centered pointwise flatness from variance.**  Dividing the R56 discrepancy estimate by
`q = |F|` converts it into the natural statement that every nonzero target has `rep3 G c`
within `sqrt 15 * |G|` of the random-model value `|G|³ / q`. -/
theorem abs_rep3_centered_le_of_variance (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hvar : ∑ z : F,
        ((Fintype.card F : ℝ) * (rep3 G z : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3)
    {c : F} (hc : c ≠ 0) :
    |(rep3 G c : ℝ) - (G.card : ℝ) ^ 3 / (Fintype.card F : ℝ)|
      ≤ Real.sqrt 15 * (G.card : ℝ) := by
  have hdev := abs_rep3_deviation_le_of_variance G hmul hinv h0 hGpos hvar hc
  have hqpos : 0 < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos
  set centered : ℝ :=
    (rep3 G c : ℝ) - (G.card : ℝ) ^ 3 / (Fintype.card F : ℝ)
  have hrewrite : (Fintype.card F : ℝ) * centered
      = (Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3 := by
    dsimp [centered]
    field_simp [ne_of_gt hqpos]
  have hcentered_dev : |(Fintype.card F : ℝ) * centered|
      ≤ Real.sqrt 15 * (Fintype.card F : ℝ) * (G.card : ℝ) := by
    rwa [hrewrite]
  have hmul_abs : (Fintype.card F : ℝ) * |centered|
      ≤ Real.sqrt 15 * (Fintype.card F : ℝ) * (G.card : ℝ) := by
    simpa [abs_mul, abs_of_pos hqpos, mul_assoc] using hcentered_dev
  have htarget_mul : (Fintype.card F : ℝ) * (Real.sqrt 15 * (G.card : ℝ))
      = Real.sqrt 15 * (Fintype.card F : ℝ) * (G.card : ℝ) := by
    ring
  have hres : |centered| ≤ Real.sqrt 15 * (G.card : ℝ) :=
    le_of_mul_le_mul_left (by rwa [htarget_mul]) hqpos
  simpa [centered] using hres

/-- **Concrete centered pointwise flatness.**  Under the round-52/53 quadratic-excess regime,
every nonzero target has `rep3 G c = |G|³ / |F| + O(|G|)` with the explicit constant
`sqrt 15`. -/
theorem abs_rep3_centered_le_of_quadraticExcess {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) {C : ℝ}
    (hexc : Depth3ExcessBounded G (C * (G.card : ℝ) ^ 2))
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ))
    {c : F} (hc : c ≠ 0) :
    |(rep3 G c : ℝ) - (G.card : ℝ) ^ 3 / (Fintype.card F : ℝ)|
      ≤ Real.sqrt 15 * (G.card : ℝ) := by
  have hGposR : (0 : ℝ) < (G.card : ℝ) := by linarith
  have hGpos : 0 < G.card := by exact_mod_cast hGposR
  exact abs_rep3_centered_le_of_variance G hmul hinv h0 hGpos
    (variance_bound_of_quadraticExcess hψ G hexc hC hn) hc

/-- **Pointwise upper envelope from variance.**  The centered flatness bound gives an immediate
nonzero-target upper bound for `rep3 G c`: random-model mean plus the R56 orbit-normalized
fluctuation. -/
theorem rep3_le_mean_add_sqrt15_card_of_variance (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hvar : ∑ z : F,
        ((Fintype.card F : ℝ) * (rep3 G z : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3)
    {c : F} (hc : c ≠ 0) :
    (rep3 G c : ℝ)
      ≤ (G.card : ℝ) ^ 3 / (Fintype.card F : ℝ)
        + Real.sqrt 15 * (G.card : ℝ) := by
  have hcenter := abs_rep3_centered_le_of_variance G hmul hinv h0 hGpos hvar hc
  have hle_abs :
      (rep3 G c : ℝ) - (G.card : ℝ) ^ 3 / (Fintype.card F : ℝ)
        ≤ |(rep3 G c : ℝ) - (G.card : ℝ) ^ 3 / (Fintype.card F : ℝ)| :=
    le_abs_self _
  linarith

/-- **Concrete pointwise upper envelope.**  In the round-52/53 quadratic-excess regime, every
nonzero target has at most the random-model number of representations plus `sqrt 15 * |G|`. -/
theorem rep3_le_mean_add_sqrt15_card_of_quadraticExcess {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) {C : ℝ}
    (hexc : Depth3ExcessBounded G (C * (G.card : ℝ) ^ 2))
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ))
    {c : F} (hc : c ≠ 0) :
    (rep3 G c : ℝ)
      ≤ (G.card : ℝ) ^ 3 / (Fintype.card F : ℝ)
        + Real.sqrt 15 * (G.card : ℝ) := by
  have hGposR : (0 : ℝ) < (G.card : ℝ) := by linarith
  have hGpos : 0 < G.card := by exact_mod_cast hGposR
  exact rep3_le_mean_add_sqrt15_card_of_variance G hmul hinv h0 hGpos
    (variance_bound_of_quadraticExcess hψ G hexc hC hn) hc

/-- **Pointwise lower envelope from variance.**  The centered flatness bound also gives the
matching lower side of the nonzero-target interval around the random-model mean. -/
theorem mean_sub_sqrt15_card_le_rep3_of_variance (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hvar : ∑ z : F,
        ((Fintype.card F : ℝ) * (rep3 G z : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3)
    {c : F} (hc : c ≠ 0) :
    (G.card : ℝ) ^ 3 / (Fintype.card F : ℝ)
        - Real.sqrt 15 * (G.card : ℝ)
      ≤ (rep3 G c : ℝ) := by
  have hcenter := abs_rep3_centered_le_of_variance G hmul hinv h0 hGpos hvar hc
  have hneg_abs :
      -|(rep3 G c : ℝ) - (G.card : ℝ) ^ 3 / (Fintype.card F : ℝ)|
        ≤ (rep3 G c : ℝ) - (G.card : ℝ) ^ 3 / (Fintype.card F : ℝ) :=
    neg_abs_le _
  linarith

/-- **Concrete pointwise lower envelope.**  The round-52/53 quadratic-excess regime places every
nonzero `rep3 G c` at least the random-model mean minus `sqrt 15 * |G|`. -/
theorem mean_sub_sqrt15_card_le_rep3_of_quadraticExcess {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) {C : ℝ}
    (hexc : Depth3ExcessBounded G (C * (G.card : ℝ) ^ 2))
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ))
    {c : F} (hc : c ≠ 0) :
    (G.card : ℝ) ^ 3 / (Fintype.card F : ℝ)
        - Real.sqrt 15 * (G.card : ℝ)
      ≤ (rep3 G c : ℝ) := by
  have hGposR : (0 : ℝ) < (G.card : ℝ) := by linarith
  have hGpos : 0 < G.card := by exact_mod_cast hGposR
  exact mean_sub_sqrt15_card_le_rep3_of_variance G hmul hinv h0 hGpos
    (variance_bound_of_quadraticExcess hψ G hexc hC hn) hc

/-- **Pointwise interval from variance.**  Under the R55 variance hypothesis, every nonzero
representation count lies in the explicit interval
`|G|³ / |F| ± sqrt 15 * |G|`. -/
theorem rep3_mem_mean_sqrt15_interval_of_variance (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hvar : ∑ z : F,
        ((Fintype.card F : ℝ) * (rep3 G z : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3)
    {c : F} (hc : c ≠ 0) :
    (G.card : ℝ) ^ 3 / (Fintype.card F : ℝ)
        - Real.sqrt 15 * (G.card : ℝ)
      ≤ (rep3 G c : ℝ)
      ∧ (rep3 G c : ℝ)
        ≤ (G.card : ℝ) ^ 3 / (Fintype.card F : ℝ)
          + Real.sqrt 15 * (G.card : ℝ) := by
  exact ⟨mean_sub_sqrt15_card_le_rep3_of_variance G hmul hinv h0 hGpos hvar hc,
    rep3_le_mean_add_sqrt15_card_of_variance G hmul hinv h0 hGpos hvar hc⟩

/-- **Concrete pointwise interval.**  The round-52/53 quadratic-excess regime gives the same
two-sided nonzero-target interval around the random-model mean. -/
theorem rep3_mem_mean_sqrt15_interval_of_quadraticExcess {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) {C : ℝ}
    (hexc : Depth3ExcessBounded G (C * (G.card : ℝ) ^ 2))
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ))
    {c : F} (hc : c ≠ 0) :
    (G.card : ℝ) ^ 3 / (Fintype.card F : ℝ)
        - Real.sqrt 15 * (G.card : ℝ)
      ≤ (rep3 G c : ℝ)
      ∧ (rep3 G c : ℝ)
        ≤ (G.card : ℝ) ^ 3 / (Fintype.card F : ℝ)
          + Real.sqrt 15 * (G.card : ℝ) := by
  have hGposR : (0 : ℝ) < (G.card : ℝ) := by linarith
  have hGpos : 0 < G.card := by exact_mod_cast hGposR
  exact rep3_mem_mean_sqrt15_interval_of_variance G hmul hinv h0 hGpos
    (variance_bound_of_quadraticExcess hψ G hexc hC hn) hc

set_option linter.unusedDecidableInType false in
/-- **Quadratic-field-size mean collapse.**  If `|F| ≥ |G|²`, the random-model term
`|G|³ / |F|` is at most `|G|`.  This is the thin-regime simplifier used to turn the R56 interval
into a purely linear-in-`|G|` envelope. -/
lemma rep3_mean_le_card_of_card_sq_le_field_card (G : Finset F)
    (hGpos : 0 < G.card)
    (hfield : G.card ^ 2 ≤ Fintype.card F) :
    (G.card : ℝ) ^ 3 / (Fintype.card F : ℝ) ≤ (G.card : ℝ) := by
  have hnpos : 0 < (G.card : ℝ) := by exact_mod_cast hGpos
  have hqpos : 0 < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hfieldR : (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ) := by
    exact_mod_cast hfield
  have hratio : (G.card : ℝ) ^ 2 / (Fintype.card F : ℝ) ≤ 1 := by
    exact (div_le_iff₀ hqpos).mpr (by simpa using hfieldR)
  calc (G.card : ℝ) ^ 3 / (Fintype.card F : ℝ)
      = (G.card : ℝ) * ((G.card : ℝ) ^ 2 / (Fintype.card F : ℝ)) := by
        ring
    _ ≤ (G.card : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left hratio (le_of_lt hnpos)
    _ = (G.card : ℝ) := by ring

/-- **Linear pointwise upper envelope in the thin regime.**  When `|F| ≥ |G|²`, the R56
nonzero-target upper bound simplifies to `(1 + sqrt 15) * |G|`. -/
theorem rep3_le_one_add_sqrt15_card_of_variance (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hfield : G.card ^ 2 ≤ Fintype.card F)
    (hvar : ∑ z : F,
        ((Fintype.card F : ℝ) * (rep3 G z : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3)
    {c : F} (hc : c ≠ 0) :
    (rep3 G c : ℝ) ≤ (1 + Real.sqrt 15) * (G.card : ℝ) := by
  have hupper := rep3_le_mean_add_sqrt15_card_of_variance G hmul hinv h0 hGpos hvar hc
  have hmean := rep3_mean_le_card_of_card_sq_le_field_card G hGpos hfield
  calc (rep3 G c : ℝ)
      ≤ (G.card : ℝ) ^ 3 / (Fintype.card F : ℝ)
          + Real.sqrt 15 * (G.card : ℝ) := hupper
    _ ≤ (G.card : ℝ) + Real.sqrt 15 * (G.card : ℝ) := by
        linarith
    _ = (1 + Real.sqrt 15) * (G.card : ℝ) := by ring

/-- **Concrete linear pointwise upper envelope in the thin regime.**  In the round-52/53
quadratic-excess regime and under `|F| ≥ |G|²`, each nonzero target has at most
`(1 + sqrt 15) * |G|` representations. -/
theorem rep3_le_one_add_sqrt15_card_of_quadraticExcess {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) {C : ℝ}
    (hexc : Depth3ExcessBounded G (C * (G.card : ℝ) ^ 2))
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ))
    (hfield : G.card ^ 2 ≤ Fintype.card F)
    {c : F} (hc : c ≠ 0) :
    (rep3 G c : ℝ) ≤ (1 + Real.sqrt 15) * (G.card : ℝ) := by
  have hGposR : (0 : ℝ) < (G.card : ℝ) := by linarith
  have hGpos : 0 < G.card := by exact_mod_cast hGposR
  exact rep3_le_one_add_sqrt15_card_of_variance G hmul hinv h0 hGpos hfield
    (variance_bound_of_quadraticExcess hψ G hexc hC hn) hc

/-- **No nonzero high-`rep3` targets in the thin regime.**  Under the R56 variance hypothesis
and `|F| ≥ |G|²`, the nonzero targets whose 3-fold representation count reaches any threshold
strictly above `(1 + sqrt 15) * |G|` form the empty set. -/
theorem no_nonzero_rep3_levelset_above_linear_of_variance (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hfield : G.card ^ 2 ≤ Fintype.card F)
    (hvar : ∑ z : F,
        ((Fintype.card F : ℝ) * (rep3 G z : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3)
    {tau : ℝ} (htau : (1 + Real.sqrt 15) * (G.card : ℝ) < tau) :
    ((Finset.univ.erase (0 : F)).filter (fun c => tau ≤ (rep3 G c : ℝ))) = ∅ := by
  classical
  by_contra hne
  set S := (Finset.univ.erase (0 : F)).filter (fun c => tau ≤ (rep3 G c : ℝ)) with hSdef
  have hnemp : S.Nonempty := by
    rw [hSdef]
    exact Finset.nonempty_iff_ne_empty.mpr hne
  rcases hnemp with ⟨c, hcS⟩
  have hcS' : c ∈ (Finset.univ.erase (0 : F)).filter
      (fun c => tau ≤ (rep3 G c : ℝ)) := by
    simpa [S] using hcS
  have hc_ne : c ≠ 0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hcS').1).1
  have htau_le : tau ≤ (rep3 G c : ℝ) := (Finset.mem_filter.mp hcS').2
  have hrep := rep3_le_one_add_sqrt15_card_of_variance G hmul hinv h0 hGpos hfield hvar hc_ne
  linarith

/-- **Concrete no-high-`rep3` levelset in the thin regime.**  The round-52/53
quadratic-excess atom, together with `|F| ≥ |G|²`, forbids nonzero targets with
`rep3` count above `(1 + sqrt 15) * |G|`. -/
theorem no_nonzero_rep3_levelset_above_linear_of_quadraticExcess
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) {C : ℝ}
    (hexc : Depth3ExcessBounded G (C * (G.card : ℝ) ^ 2))
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ))
    (hfield : G.card ^ 2 ≤ Fintype.card F)
    {tau : ℝ} (htau : (1 + Real.sqrt 15) * (G.card : ℝ) < tau) :
    ((Finset.univ.erase (0 : F)).filter (fun c => tau ≤ (rep3 G c : ℝ))) = ∅ := by
  have hGposR : (0 : ℝ) < (G.card : ℝ) := by linarith
  have hGpos : 0 < G.card := by exact_mod_cast hGposR
  exact no_nonzero_rep3_levelset_above_linear_of_variance G hmul hinv h0 hGpos hfield
    (variance_bound_of_quadraticExcess hψ G hexc hC hn) htau

/-- **Cardinality form of the high-`rep3` exclusion.**  This is the counting-friendly version of
`no_nonzero_rep3_levelset_above_linear_of_variance`: the nonzero high-representation levelset has
cardinality zero. -/
theorem nonzero_rep3_levelset_card_eq_zero_above_linear_of_variance (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hfield : G.card ^ 2 ≤ Fintype.card F)
    (hvar : ∑ z : F,
        ((Fintype.card F : ℝ) * (rep3 G z : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3)
    {tau : ℝ} (htau : (1 + Real.sqrt 15) * (G.card : ℝ) < tau) :
    (((Finset.univ.erase (0 : F)).filter (fun c => tau ≤ (rep3 G c : ℝ))).card : ℕ) = 0 := by
  rw [no_nonzero_rep3_levelset_above_linear_of_variance G hmul hinv h0 hGpos hfield hvar htau]
  rfl

/-- **Concrete cardinality form of the high-`rep3` exclusion.**  In the round-52/53
quadratic-excess regime and the thin field range, the nonzero high-representation levelset has
cardinality zero. -/
theorem nonzero_rep3_levelset_card_eq_zero_above_linear_of_quadraticExcess
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) {C : ℝ}
    (hexc : Depth3ExcessBounded G (C * (G.card : ℝ) ^ 2))
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ))
    (hfield : G.card ^ 2 ≤ Fintype.card F)
    {tau : ℝ} (htau : (1 + Real.sqrt 15) * (G.card : ℝ) < tau) :
    (((Finset.univ.erase (0 : F)).filter (fun c => tau ≤ (rep3 G c : ℝ))).card : ℕ) = 0 := by
  rw [no_nonzero_rep3_levelset_above_linear_of_quadraticExcess
    hψ G hmul hinv h0 hexc hC hn hfield htau]
  rfl

/-- **Positive-slack cardinal exclusion.**  A threshold of
`(1 + sqrt 15) * |G| + eps`, with `eps > 0`, has empty nonzero `rep3` levelset under the
variance and thin-field hypotheses. -/
theorem nonzero_rep3_levelset_card_eq_zero_of_linear_add_pos_of_variance (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hfield : G.card ^ 2 ≤ Fintype.card F)
    (hvar : ∑ z : F,
        ((Fintype.card F : ℝ) * (rep3 G z : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3)
    {eps : ℝ} (heps : 0 < eps) :
    (((Finset.univ.erase (0 : F)).filter
      (fun c => (1 + Real.sqrt 15) * (G.card : ℝ) + eps ≤ (rep3 G c : ℝ))).card : ℕ)
        = 0 := by
  exact nonzero_rep3_levelset_card_eq_zero_above_linear_of_variance G hmul hinv h0 hGpos hfield
    hvar (by linarith)

/-- **Concrete positive-slack cardinal exclusion.**  In the round-52/53 quadratic-excess regime,
any positive additive slack above `(1 + sqrt 15) * |G|` gives an empty nonzero `rep3` levelset. -/
theorem nonzero_rep3_levelset_card_eq_zero_of_linear_add_pos_of_quadraticExcess
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) {C : ℝ}
    (hexc : Depth3ExcessBounded G (C * (G.card : ℝ) ^ 2))
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ))
    (hfield : G.card ^ 2 ≤ Fintype.card F)
    {eps : ℝ} (heps : 0 < eps) :
    (((Finset.univ.erase (0 : F)).filter
      (fun c => (1 + Real.sqrt 15) * (G.card : ℝ) + eps ≤ (rep3 G c : ℝ))).card : ℕ)
        = 0 := by
  exact nonzero_rep3_levelset_card_eq_zero_above_linear_of_quadraticExcess
    hψ G hmul hinv h0 hexc hC hn hfield (by linarith)

/-- **Natural-threshold high-`rep3` exclusion.**  Under the variance and thin-field hypotheses,
any natural threshold strictly above `(1 + sqrt 15) * |G|` has no nonzero elements with
`T ≤ rep3 G c`.  This is the integer-threshold form used by downstream counting arguments. -/
theorem nonzero_rep3_nat_levelset_card_eq_zero_above_linear_of_variance (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hfield : G.card ^ 2 ≤ Fintype.card F)
    (hvar : ∑ z : F,
        ((Fintype.card F : ℝ) * (rep3 G z : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3)
    {T : ℕ} (hT : (1 + Real.sqrt 15) * (G.card : ℝ) < (T : ℝ)) :
    (((Finset.univ.erase (0 : F)).filter (fun c => T ≤ rep3 G c)).card : ℕ) = 0 := by
  classical
  by_contra hne
  rcases Finset.card_pos.mp (Nat.pos_of_ne_zero hne) with ⟨c, hc⟩
  have hc_mem := (Finset.mem_filter.mp hc).1
  have hc_ne : c ≠ 0 := by
    exact Finset.mem_erase.mp hc_mem |>.1
  have hT_le_nat : T ≤ rep3 G c := (Finset.mem_filter.mp hc).2
  have hT_le : (T : ℝ) ≤ (rep3 G c : ℝ) := by
    exact_mod_cast hT_le_nat
  have hrep := rep3_le_one_add_sqrt15_card_of_variance G hmul hinv h0 hGpos hfield hvar hc_ne
  linarith

/-- **Concrete natural-threshold high-`rep3` exclusion.**  In the round-52/53 quadratic-excess
regime and the thin-field range, any natural threshold strictly above
`(1 + sqrt 15) * |G|` has an empty nonzero `rep3` levelset. -/
theorem nonzero_rep3_nat_levelset_card_eq_zero_above_linear_of_quadraticExcess
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) {C : ℝ}
    (hexc : Depth3ExcessBounded G (C * (G.card : ℝ) ^ 2))
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ))
    (hfield : G.card ^ 2 ≤ Fintype.card F)
    {T : ℕ} (hT : (1 + Real.sqrt 15) * (G.card : ℝ) < (T : ℝ)) :
    (((Finset.univ.erase (0 : F)).filter (fun c => T ≤ rep3 G c)).card : ℕ) = 0 := by
  have hGposR : 0 < (G.card : ℝ) := by linarith
  have hGpos : 0 < G.card := by exact_mod_cast hGposR
  exact nonzero_rep3_nat_levelset_card_eq_zero_above_linear_of_variance G hmul hinv h0
    hGpos hfield
    (variance_bound_of_quadraticExcess hψ G hexc hC hn) hT

/-- **Natural-threshold supremum exclusion.**  Under the variance and thin-field hypotheses, if a
natural threshold lies strictly above `(1 + sqrt 15) * |G|`, then the nonzero `rep3` supremum is
strictly below that threshold. -/
theorem nonzero_rep3_sup_lt_nat_threshold_of_variance (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hfield : G.card ^ 2 ≤ Fintype.card F)
    (hvar : ∑ z : F,
        ((Fintype.card F : ℝ) * (rep3 G z : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3)
    {T : ℕ} (hT : (1 + Real.sqrt 15) * (G.card : ℝ) < (T : ℝ)) :
    (Finset.univ.erase (0 : F)).sup (fun c => rep3 G c) < T := by
  classical
  have hne : (Finset.univ.erase (0 : F)).Nonempty := by
    exact ⟨1, Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_univ 1⟩⟩
  have hzero := nonzero_rep3_nat_levelset_card_eq_zero_above_linear_of_variance G hmul hinv h0
    hGpos hfield hvar hT
  exact (nat_sup_lt_iff_upper_levelset_card_zero (Finset.univ.erase (0 : F)) hne
    (fun c => rep3 G c) T).mpr hzero

/-- **Concrete natural-threshold supremum exclusion.**  In the round-52/53 quadratic-excess
regime, if a natural threshold lies strictly above `(1 + sqrt 15) * |G|`, then the nonzero `rep3`
supremum is strictly below that threshold. -/
theorem nonzero_rep3_sup_lt_nat_threshold_of_quadraticExcess
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) {C : ℝ}
    (hexc : Depth3ExcessBounded G (C * (G.card : ℝ) ^ 2))
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ))
    (hfield : G.card ^ 2 ≤ Fintype.card F)
    {T : ℕ} (hT : (1 + Real.sqrt 15) * (G.card : ℝ) < (T : ℝ)) :
    (Finset.univ.erase (0 : F)).sup (fun c => rep3 G c) < T := by
  classical
  have hne : (Finset.univ.erase (0 : F)).Nonempty := by
    exact ⟨1, Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_univ 1⟩⟩
  have hzero := nonzero_rep3_nat_levelset_card_eq_zero_above_linear_of_quadraticExcess
    hψ G hmul hinv h0 hexc hC hn hfield hT
  exact (nat_sup_lt_iff_upper_levelset_card_zero (Finset.univ.erase (0 : F)) hne
    (fun c => rep3 G c) T).mpr hzero

/-- **Canonical floor-threshold high-`rep3` exclusion.**  The first natural number strictly above
`(1 + sqrt 15) * |G|` has an empty nonzero `rep3` levelset under the variance and thin-field
hypotheses.  This removes the floor/cast side-condition from downstream integer-counting uses. -/
theorem nonzero_rep3_floor_levelset_card_eq_zero_of_variance (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hfield : G.card ^ 2 ≤ Fintype.card F)
    (hvar : ∑ z : F,
        ((Fintype.card F : ℝ) * (rep3 G z : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3) :
    (((Finset.univ.erase (0 : F)).filter
      (fun c =>
        Nat.floor ((1 + Real.sqrt 15) * (G.card : ℝ)) + 1 ≤ rep3 G c)).card : ℕ)
        = 0 := by
  have hT : (1 + Real.sqrt 15) * (G.card : ℝ)
      < ((Nat.floor ((1 + Real.sqrt 15) * (G.card : ℝ)) + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one ((1 + Real.sqrt 15) * (G.card : ℝ)))
  exact nonzero_rep3_nat_levelset_card_eq_zero_above_linear_of_variance G hmul hinv h0
    hGpos hfield hvar hT

/-- **Concrete canonical floor-threshold exclusion.**  In the round-52/53 quadratic-excess
regime, the nonzero levelset above
`floor ((1 + sqrt 15) * |G|) + 1` is empty. -/
theorem nonzero_rep3_floor_levelset_card_eq_zero_of_quadraticExcess
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) {C : ℝ}
    (hexc : Depth3ExcessBounded G (C * (G.card : ℝ) ^ 2))
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ))
    (hfield : G.card ^ 2 ≤ Fintype.card F) :
    (((Finset.univ.erase (0 : F)).filter
      (fun c =>
        Nat.floor ((1 + Real.sqrt 15) * (G.card : ℝ)) + 1 ≤ rep3 G c)).card : ℕ)
        = 0 := by
  have hT : (1 + Real.sqrt 15) * (G.card : ℝ)
      < ((Nat.floor ((1 + Real.sqrt 15) * (G.card : ℝ)) + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one ((1 + Real.sqrt 15) * (G.card : ℝ)))
  exact nonzero_rep3_nat_levelset_card_eq_zero_above_linear_of_quadraticExcess
    hψ G hmul hinv h0 hexc hC hn hfield hT

/-- **Pointwise integer high-`rep3` bound.**  Under the variance and thin-field hypotheses, every
nonzero representative has `rep3` at most the canonical integer floor
`floor ((1 + sqrt 15) * |G|)`. -/
theorem rep3_le_floor_linear_of_variance (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hfield : G.card ^ 2 ≤ Fintype.card F)
    (hvar : ∑ z : F,
        ((Fintype.card F : ℝ) * (rep3 G z : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3)
    {c : F} (hc : c ≠ 0) :
    rep3 G c ≤ Nat.floor ((1 + Real.sqrt 15) * (G.card : ℝ)) := by
  classical
  have hc_mem : c ∈ Finset.univ.erase (0 : F) := by
    exact Finset.mem_erase.mpr ⟨hc, Finset.mem_univ c⟩
  have hzero := nonzero_rep3_floor_levelset_card_eq_zero_of_variance G hmul hinv h0 hGpos
    hfield hvar
  exact le_of_succ_upper_levelset_card_zero (Finset.univ.erase (0 : F)) (fun c => rep3 G c)
    (Nat.floor ((1 + Real.sqrt 15) * (G.card : ℝ))) hzero hc_mem

/-- **Concrete pointwise integer high-`rep3` bound.**  In the round-52/53 quadratic-excess
regime, every nonzero representative has `rep3` at most
`floor ((1 + sqrt 15) * |G|)`. -/
theorem rep3_le_floor_linear_of_quadraticExcess
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) {C : ℝ}
    (hexc : Depth3ExcessBounded G (C * (G.card : ℝ) ^ 2))
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ))
    (hfield : G.card ^ 2 ≤ Fintype.card F)
    {c : F} (hc : c ≠ 0) :
    rep3 G c ≤ Nat.floor ((1 + Real.sqrt 15) * (G.card : ℝ)) := by
  classical
  have hc_mem : c ∈ Finset.univ.erase (0 : F) := by
    exact Finset.mem_erase.mpr ⟨hc, Finset.mem_univ c⟩
  have hzero := nonzero_rep3_floor_levelset_card_eq_zero_of_quadraticExcess
    hψ G hmul hinv h0 hexc hC hn hfield
  exact le_of_succ_upper_levelset_card_zero (Finset.univ.erase (0 : F)) (fun c => rep3 G c)
    (Nat.floor ((1 + Real.sqrt 15) * (G.card : ℝ))) hzero hc_mem

/-- **Pointwise real high-`rep3` bound.**  Under the variance and thin-field hypotheses, every
nonzero representative has `rep3`, cast to `ℝ`, at most `(1 + sqrt 15) * |G|`. -/
theorem rep3_real_le_linear_of_variance (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hfield : G.card ^ 2 ≤ Fintype.card F)
    (hvar : ∑ z : F,
        ((Fintype.card F : ℝ) * (rep3 G z : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3)
    {c : F} (hc : c ≠ 0) :
    (rep3 G c : ℝ) ≤ (1 + Real.sqrt 15) * (G.card : ℝ) := by
  have hfloor := rep3_le_floor_linear_of_variance G hmul hinv h0 hGpos hfield hvar hc
  have hfloorR : (rep3 G c : ℝ)
      ≤ (Nat.floor ((1 + Real.sqrt 15) * (G.card : ℝ)) : ℝ) := by
    exact_mod_cast hfloor
  have hnonneg : 0 ≤ (1 + Real.sqrt 15) * (G.card : ℝ) := by positivity
  exact le_trans hfloorR (Nat.floor_le hnonneg)

/-- **Concrete pointwise real high-`rep3` bound.**  In the round-52/53 quadratic-excess regime,
every nonzero representative has `rep3`, cast to `ℝ`, at most `(1 + sqrt 15) * |G|`. -/
theorem rep3_real_le_linear_of_quadraticExcess
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) {C : ℝ}
    (hexc : Depth3ExcessBounded G (C * (G.card : ℝ) ^ 2))
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ))
    (hfield : G.card ^ 2 ≤ Fintype.card F)
    {c : F} (hc : c ≠ 0) :
    (rep3 G c : ℝ) ≤ (1 + Real.sqrt 15) * (G.card : ℝ) := by
  have hfloor := rep3_le_floor_linear_of_quadraticExcess hψ G hmul hinv h0 hexc hC hn
    hfield hc
  have hfloorR : (rep3 G c : ℝ)
      ≤ (Nat.floor ((1 + Real.sqrt 15) * (G.card : ℝ)) : ℝ) := by
    exact_mod_cast hfloor
  have hnonneg : 0 ≤ (1 + Real.sqrt 15) * (G.card : ℝ) := by positivity
  exact le_trans hfloorR (Nat.floor_le hnonneg)

/-- **Worst nonzero integer high-`rep3` bound.**  The finite supremum of `rep3` over nonzero field
elements is at most the canonical floor threshold under the variance and thin-field hypotheses. -/
theorem nonzero_rep3_sup_le_floor_linear_of_variance (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hfield : G.card ^ 2 ≤ Fintype.card F)
    (hvar : ∑ z : F,
        ((Fintype.card F : ℝ) * (rep3 G z : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3) :
    (Finset.univ.erase (0 : F)).sup (fun c => rep3 G c)
      ≤ Nat.floor ((1 + Real.sqrt 15) * (G.card : ℝ)) := by
  classical
  have hne : (Finset.univ.erase (0 : F)).Nonempty := by
    exact ⟨1, Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_univ 1⟩⟩
  have hzero := nonzero_rep3_floor_levelset_card_eq_zero_of_variance G hmul hinv h0 hGpos
    hfield hvar
  exact (nat_sup_le_iff_succ_upper_levelset_card_zero (Finset.univ.erase (0 : F)) hne
    (fun c => rep3 G c) (Nat.floor ((1 + Real.sqrt 15) * (G.card : ℝ)))).mpr hzero

/-- **Concrete worst nonzero integer high-`rep3` bound.**  In the round-52/53 quadratic-excess
regime, the finite supremum of `rep3` over nonzero field elements is at most
`floor ((1 + sqrt 15) * |G|)`. -/
theorem nonzero_rep3_sup_le_floor_linear_of_quadraticExcess
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) {C : ℝ}
    (hexc : Depth3ExcessBounded G (C * (G.card : ℝ) ^ 2))
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ))
    (hfield : G.card ^ 2 ≤ Fintype.card F) :
    (Finset.univ.erase (0 : F)).sup (fun c => rep3 G c)
      ≤ Nat.floor ((1 + Real.sqrt 15) * (G.card : ℝ)) := by
  classical
  have hne : (Finset.univ.erase (0 : F)).Nonempty := by
    exact ⟨1, Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_univ 1⟩⟩
  have hzero := nonzero_rep3_floor_levelset_card_eq_zero_of_quadraticExcess
    hψ G hmul hinv h0 hexc hC hn hfield
  exact (nat_sup_le_iff_succ_upper_levelset_card_zero (Finset.univ.erase (0 : F)) hne
    (fun c => rep3 G c) (Nat.floor ((1 + Real.sqrt 15) * (G.card : ℝ)))).mpr hzero

/-- **Worst nonzero real high-`rep3` bound.**  The finite supremum of `rep3` over nonzero field
elements, cast to `ℝ`, is at most `(1 + sqrt 15) * |G|` under the variance and thin-field
hypotheses. -/
theorem nonzero_rep3_sup_real_le_linear_of_variance (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hfield : G.card ^ 2 ≤ Fintype.card F)
    (hvar : ∑ z : F,
        ((Fintype.card F : ℝ) * (rep3 G z : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3) :
    (((Finset.univ.erase (0 : F)).sup (fun c => rep3 G c) : ℕ) : ℝ)
      ≤ (1 + Real.sqrt 15) * (G.card : ℝ) := by
  have hsup := nonzero_rep3_sup_le_floor_linear_of_variance G hmul hinv h0 hGpos hfield hvar
  have hsupR : (((Finset.univ.erase (0 : F)).sup (fun c => rep3 G c) : ℕ) : ℝ)
      ≤ (Nat.floor ((1 + Real.sqrt 15) * (G.card : ℝ)) : ℝ) := by
    exact_mod_cast hsup
  have hnonneg : 0 ≤ (1 + Real.sqrt 15) * (G.card : ℝ) := by positivity
  exact le_trans hsupR (Nat.floor_le hnonneg)

/-- **Concrete worst nonzero real high-`rep3` bound.**  In the round-52/53 quadratic-excess
regime, the finite supremum of `rep3` over nonzero field elements, cast to `ℝ`, is at most
`(1 + sqrt 15) * |G|`. -/
theorem nonzero_rep3_sup_real_le_linear_of_quadraticExcess
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) {C : ℝ}
    (hexc : Depth3ExcessBounded G (C * (G.card : ℝ) ^ 2))
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ))
    (hfield : G.card ^ 2 ≤ Fintype.card F) :
    (((Finset.univ.erase (0 : F)).sup (fun c => rep3 G c) : ℕ) : ℝ)
      ≤ (1 + Real.sqrt 15) * (G.card : ℝ) := by
  have hsup := nonzero_rep3_sup_le_floor_linear_of_quadraticExcess
    hψ G hmul hinv h0 hexc hC hn hfield
  have hsupR : (((Finset.univ.erase (0 : F)).sup (fun c => rep3 G c) : ℕ) : ℝ)
      ≤ (Nat.floor ((1 + Real.sqrt 15) * (G.card : ℝ)) : ℝ) := by
    exact_mod_cast hsup
  have hnonneg : 0 ≤ (1 + Real.sqrt 15) * (G.card : ℝ) := by positivity
  exact le_trans hsupR (Nat.floor_le hnonneg)

/-- **Positive-slack worst nonzero real high-`rep3` bound.**  Under the variance and thin-field
hypotheses, the nonzero `rep3` supremum is strictly below any positive additive slack above
`(1 + sqrt 15) * |G|`. -/
theorem nonzero_rep3_sup_real_lt_linear_add_pos_of_variance (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (hGpos : 0 < G.card)
    (hfield : G.card ^ 2 ≤ Fintype.card F)
    (hvar : ∑ z : F,
        ((Fintype.card F : ℝ) * (rep3 G z : ℝ) - (G.card : ℝ) ^ 3) ^ 2
          ≤ 15 * (Fintype.card F : ℝ) ^ 2 * (G.card : ℝ) ^ 3)
    {eps : ℝ} (heps : 0 < eps) :
    (((Finset.univ.erase (0 : F)).sup (fun c => rep3 G c) : ℕ) : ℝ)
      < (1 + Real.sqrt 15) * (G.card : ℝ) + eps := by
  have hsup := nonzero_rep3_sup_real_le_linear_of_variance G hmul hinv h0 hGpos hfield hvar
  linarith

/-- **Concrete positive-slack worst nonzero real high-`rep3` bound.**  In the round-52/53
quadratic-excess regime, the nonzero `rep3` supremum is strictly below any positive additive
slack above `(1 + sqrt 15) * |G|`. -/
theorem nonzero_rep3_sup_real_lt_linear_add_pos_of_quadraticExcess
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G) {C : ℝ}
    (hexc : Depth3ExcessBounded G (C * (G.card : ℝ) ^ 2))
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ))
    (hfield : G.card ^ 2 ≤ Fintype.card F)
    {eps : ℝ} (heps : 0 < eps) :
    (((Finset.univ.erase (0 : F)).sup (fun c => rep3 G c) : ℕ) : ℝ)
      < (1 + Real.sqrt 15) * (G.card : ℝ) + eps := by
  have hsup := nonzero_rep3_sup_real_le_linear_of_quadraticExcess
    hψ G hmul hinv h0 hexc hC hn hfield
  linarith

end ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.nat_sup_lt_iff_upper_levelset_card_zero
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.nat_sup_le_iff_succ_upper_levelset_card_zero
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.le_of_succ_upper_levelset_card_zero
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.rep3_smul
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.rep3_orbit_const
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.rep3_varianceSummand_smul
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.rep3_varianceSummand_orbit_const
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.rep3_orbit_sum_eq_card_mul
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.rep3_varianceSummand_orbit_sum_eq_card_mul
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.rep3_varianceSummand_orbit_le_total
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.rep3_varianceSummand_le_of_variance
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.abs_rep3_deviation_le_of_variance
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.abs_rep3_deviation_le_of_quadraticExcess
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.abs_rep3_centered_le_of_variance
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.abs_rep3_centered_le_of_quadraticExcess
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.rep3_le_mean_add_sqrt15_card_of_variance
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.rep3_le_mean_add_sqrt15_card_of_quadraticExcess
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.mean_sub_sqrt15_card_le_rep3_of_variance
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.mean_sub_sqrt15_card_le_rep3_of_quadraticExcess
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.rep3_mem_mean_sqrt15_interval_of_variance
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.rep3_mem_mean_sqrt15_interval_of_quadraticExcess
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.rep3_mean_le_card_of_card_sq_le_field_card
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.rep3_le_one_add_sqrt15_card_of_variance
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.rep3_le_one_add_sqrt15_card_of_quadraticExcess
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.no_nonzero_rep3_levelset_above_linear_of_variance
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.no_nonzero_rep3_levelset_above_linear_of_quadraticExcess
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.nonzero_rep3_levelset_card_eq_zero_above_linear_of_variance
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.nonzero_rep3_levelset_card_eq_zero_above_linear_of_quadraticExcess
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.nonzero_rep3_levelset_card_eq_zero_of_linear_add_pos_of_variance
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.nonzero_rep3_levelset_card_eq_zero_of_linear_add_pos_of_quadraticExcess
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.nonzero_rep3_nat_levelset_card_eq_zero_above_linear_of_variance
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.nonzero_rep3_nat_levelset_card_eq_zero_above_linear_of_quadraticExcess
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.nonzero_rep3_sup_lt_nat_threshold_of_variance
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.nonzero_rep3_sup_lt_nat_threshold_of_quadraticExcess
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.nonzero_rep3_floor_levelset_card_eq_zero_of_variance
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.nonzero_rep3_floor_levelset_card_eq_zero_of_quadraticExcess
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.rep3_le_floor_linear_of_variance
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.rep3_le_floor_linear_of_quadraticExcess
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.rep3_real_le_linear_of_variance
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.rep3_real_le_linear_of_quadraticExcess
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.nonzero_rep3_sup_le_floor_linear_of_variance
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.nonzero_rep3_sup_le_floor_linear_of_quadraticExcess
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.nonzero_rep3_sup_real_le_linear_of_variance
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.nonzero_rep3_sup_real_le_linear_of_quadraticExcess
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.nonzero_rep3_sup_real_lt_linear_add_pos_of_variance
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance.nonzero_rep3_sup_real_lt_linear_add_pos_of_quadraticExcess

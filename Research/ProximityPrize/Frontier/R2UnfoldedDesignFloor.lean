/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.SubspaceDesign

/-!
# The R2 (CZ25 subspace-design) route has a structural floor on UNFOLDED codes (#407)

**Claim being assessed.** The R2 list-recovery chain (`ProximityGap.exists_determining_tuple`,
`SeparationSurvivalCount.card_surv_ge`, the CZ25 capacity reduction `CZ25DimensionCount`) takes
as input that the `δ`-close codewords span a subspace `H ≤ C` of dimension `≤ r`, and that the
code is a `τ`-subspace-design (`IsSubspaceDesign s τ C`) with a small `τ` (the capacity radius
is `1 − τ(r₀) − η`, `r₀ = ⌊1/η⌋`). The prize target is *explicit smooth (UNFOLDED) Reed–Solomon*,
i.e. a code over the scalar alphabet `F` — in the in-tree encoding `s = 1`.

**The obstruction (this file, proven).** For `s = 1` the subspace-design parameter is forced to
satisfy `τ(r) ≥ (m − 1)/m` for **every** `m`-dimensional subspace `A ≤ C` with `m ≤ r` — it does
**not** decay to the rate `ρ`. The mechanism is the "free vanishing of one scalar coordinate":
each coordinate map `eval_i : A → F` is a *single linear functional* (`range ≤ Fin 1 → F`,
`finrank ≤ 1`), so by rank–nullity `dim(A ⊓ ker eval_i) ≥ dim A − 1` at **every** coordinate `i`.
Summing over all `n` coordinates,

  `∑_i dim(A ⊓ ker eval_i) ≥ (m − 1)·n`,

and the design inequality `∑_i dim A_i ≤ m·τ(r)·n` forces `τ(r) ≥ (m − 1)/m`.

`unfolded_subspaceDesign_tau_ge` is this floor. `unfolded_subspaceDesign_tau_ge_half`
specialises it to `m = 2`: any unfolded subspace-design with a 2-dimensional subcode has
`τ(r) ≥ 1/2` for all `r ≥ 2`.

**Consequence for the prize (numeric in `scripts/probes/probe_r2_unfolded_floor.py`).** The CZ25
capacity radius is `1 − τ(r₀) − η` with `r₀ = ⌊1/η⌋`. On unfolded RS, using an `r₀`-dimensional
subcode (every RS code of dimension `k ≥ r₀` has one), this is `≤ 1 − (r₀−1)/r₀ − η = 1/r₀ − η`,
which is `< 1/r₀ − 1/(r₀+1) = 1/(r₀(r₀+1)) ≤ 1/2` (using `η > 1/(r₀+1)`), *independent of `ρ`*. The
supremum over all `η` of this certified radius is `< 1/2` (attained only at `r₀ = 1`), and `< 1/6`
for `r₀ ≥ 2`. Since capacity is `1 − ρ ≥ 1/2` for every prize rate `ρ ∈ {1/2,1/4,1/8,1/16}`, the
unfolded-R2 radius is **strictly below capacity (the window upper edge) in every prize rate**; it is
moreover below the window *lower* edge `1 − √ρ` for `ρ ∈ {1/8, 1/16}` (for `ρ ∈ {1/2, 1/4}` the
radius `< 1/2` is below capacity but not below the lower edge). The radius form is proven as
`unfolded_cz25_radius_lt_half`. So the R2 route, instantiated on the prize code, certifies a radius
far below the prize window: it requires **folding** (`s ≫ 1`) to give a `τ(r) ≈ ρ` profile, exactly
as GK16 / GG25 prove it (`frs_is_subspaceDesign_gk16`, valid only on `r ∈ [s]`, where
`dim(A ⊓ ker eval_i) ≥ dim A − s` permits the small profile). This is not a formalization gap but a
structural fact about the route: the missing input `CZ25CoordFiberCap` for *unfolded* RS would
require `τ(r₀) ≈ ρ` at `r₀ ≥ 2`, which this floor refutes.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open CodingTheory

variable {ι : Type} [Fintype ι] [Nonempty ι] {F : Type} [Field F]

/-- **Free-vanishing of one scalar coordinate (the `s = 1` mechanism).** For an `m`-dimensional
subspace `A` of the unfolded ambient space `ι → Fin 1 → F`, every coordinate map `eval_i` is a
single linear functional on `A` (range inside `Fin 1 → F`, of dimension `≤ 1`), so by
rank–nullity `dim(A ⊓ ker eval_i) ≥ dim A − 1`. -/
theorem finrank_inf_ker_ge_sub_one_unfolded
    (A : Submodule F (ι → Fin 1 → F)) (i : ι) :
    Module.finrank F A - 1 ≤
      Module.finrank F (↥(A ⊓ (LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin 1 → F) i)) :
        Submodule F (ι → Fin 1 → F))) := by
  classical
  haveI : FiniteDimensional F (ι → Fin 1 → F) := inferInstance
  -- Restrict the `i`-th projection to `A`.
  set f : (ι → Fin 1 → F) →ₗ[F] (Fin 1 → F) :=
    LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin 1 → F) i with hf
  set g : A →ₗ[F] (Fin 1 → F) := f.domRestrict A with hg
  -- `(ker g).map A.subtype = A ⊓ ker f`.
  have hkermap : (LinearMap.ker g).map A.subtype
      = A ⊓ (LinearMap.ker f) := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.coe_subtype, Submodule.mem_inf,
      hg, LinearMap.domRestrict_apply]
    constructor
    · rintro ⟨⟨y, hy⟩, hker, rfl⟩
      exact ⟨hy, hker⟩
    · rintro ⟨hxA, hxker⟩
      exact ⟨⟨x, hxA⟩, hxker, rfl⟩
  -- `finrank (ker g) = finrank (A ⊓ ker f)` (subtype is injective).
  have hfinrank_eq : Module.finrank F (LinearMap.ker g)
      = Module.finrank F (↥(A ⊓ (LinearMap.ker f))) := by
    rw [← hkermap, Submodule.finrank_map_subtype_eq]
  -- rank–nullity: `finrank (range g) + finrank (ker g) = finrank A`.
  have hrn : Module.finrank F (LinearMap.range g) + Module.finrank F (LinearMap.ker g)
      = Module.finrank F A := LinearMap.finrank_range_add_finrank_ker g
  -- `finrank (range g) ≤ finrank (Fin 1 → F) = 1`.
  have hrange_le : Module.finrank F (LinearMap.range g) ≤ 1 := by
    refine le_trans (Submodule.finrank_le _) ?_
    simp
  -- Combine.
  rw [hfinrank_eq] at hrn
  omega

/-- **The unfolded subspace-design floor `τ(r) ≥ (m − 1)/m`.** For an unfolded (`s = 1`) code
`C : Submodule F (ι → Fin 1 → F)` that is a `τ`-subspace-design, and **any** `m`-dimensional
subspace `A ≤ C` with `m ≤ r`, the design parameter is bounded below by `(m − 1)/m`:

  `τ(r) ≥ (m − 1) / m`.

This is the structural obstruction to the R2 (CZ25 subspace-design) route on unfolded RS: unlike
folded RS (where GK16 gives `τ(r) ≈ ρ` on `r ∈ [s]`), an unfolded code's design parameter cannot
fall below `(m−1)/m`, so the CZ25 capacity radius `1 − τ(r₀) − η` stays below `1/2` for `r₀ ≥ 2`.
The "free vanishing of one scalar coordinate" (`finrank_inf_ker_ge_sub_one_unfolded`) makes the
per-coordinate vanishing mass at least `m − 1` everywhere. -/
theorem unfolded_subspaceDesign_tau_ge
    {τ : ℕ → ℝ} {C : Submodule F (ι → Fin 1 → F)} (h : IsSubspaceDesign 1 τ C)
    {r m : ℕ} (hm : 1 ≤ m) {A : Submodule F (ι → Fin 1 → F)}
    (hAC : A ≤ C) (hrank : Module.finrank F A = m) (hmr : m ≤ r) :
    ((m : ℝ) - 1) / m ≤ τ r := by
  classical
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  -- design inequality at `A` (cleared of the `/n`).
  have hdesign := h r A hAC (hrank ▸ hmr)
  rw [div_le_iff₀ hn] at hdesign
  -- per-coordinate lower bound `m - 1 ≤ dim A_i`, summed.
  have hper : ∀ i : ι, ((m : ℝ) - 1) ≤
      (Module.finrank F (↥(A ⊓ (LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin 1 → F) i)) :
        Submodule F (ι → Fin 1 → F))) : ℝ) := by
    intro i
    have h1 := finrank_inf_ker_ge_sub_one_unfolded A i
    rw [hrank] at h1
    have : ((m - 1 : ℕ) : ℝ) ≤
        (Module.finrank F (↥(A ⊓ (LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin 1 → F) i)))) : ℝ) := by
      exact_mod_cast h1
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub hm]; simp
    rwa [hcast] at this
  have hsum_lb : ((m : ℝ) - 1) * Fintype.card ι ≤
      ∑ i : ι, (Module.finrank F (↥(A ⊓ (LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin 1 → F) i)) :
        Submodule F (ι → Fin 1 → F))) : ℝ) := by
    calc ((m : ℝ) - 1) * Fintype.card ι
        = ∑ _i : ι, ((m : ℝ) - 1) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ i : ι, (Module.finrank F (↥(A ⊓ (LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin 1 → F) i)) :
            Submodule F (ι → Fin 1 → F))) : ℝ) :=
          Finset.sum_le_sum (fun i _ => hper i)
  -- combine: `(m-1)·n ≤ ∑ dim A_i ≤ (finrank A · τ r)·n = (m·τ r)·n`, cancel `n`, divide by `m`.
  have hcomb : ((m : ℝ) - 1) * Fintype.card ι ≤ ((m : ℝ) * τ r) * Fintype.card ι := by
    calc ((m : ℝ) - 1) * Fintype.card ι
        ≤ ∑ i : ι, (Module.finrank F (↥(A ⊓ (LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin 1 → F) i)) :
            Submodule F (ι → Fin 1 → F))) : ℝ) := hsum_lb
      _ ≤ (Module.finrank F A * τ r) * Fintype.card ι := hdesign
      _ = ((m : ℝ) * τ r) * Fintype.card ι := by rw [hrank]
  have hcancel : ((m : ℝ) - 1) ≤ (m : ℝ) * τ r :=
    le_of_mul_le_mul_right hcomb hn
  rw [div_le_iff₀ hmpos]
  linarith [hcancel]

/-- **Specialisation: any unfolded subspace-design with a 2-dimensional subcode has
`τ(r) ≥ 1/2` for `r ≥ 2`.** This is the first place the unfolded floor exceeds the rate `ρ`
(for `ρ < 1/2`): the CZ25 route cannot use any dimension-`≥ 2` span without paying `τ ≥ 1/2`,
capping its certified radius below `1/2`. -/
theorem unfolded_subspaceDesign_tau_ge_half
    {τ : ℕ → ℝ} {C : Submodule F (ι → Fin 1 → F)} (h : IsSubspaceDesign 1 τ C)
    {r : ℕ} (hr : 2 ≤ r) {A : Submodule F (ι → Fin 1 → F)}
    (hAC : A ≤ C) (hrank : Module.finrank F A = 2) :
    (1 : ℝ) / 2 ≤ τ r := by
  have := unfolded_subspaceDesign_tau_ge h (m := 2) (by norm_num) hAC hrank hr
  norm_num at this ⊢
  linarith [this]

/-- **The CZ25 radius collapse on unfolded RS (the obstruction in radius form).**

The CZ25 / R2 capacity radius certified by a `τ`-subspace-design is `δ = 1 − τ(r₀) − η` with
`r₀ = ⌊1/η⌋`.  For an *unfolded* (`s = 1`) code `C` that carries a 2-dimensional subcode `A`
(every RS code of dimension `k ≥ 2` does), and on the regime `r₀ ≥ 2` (i.e. `η ≤ 1/2`), the floor
`unfolded_subspaceDesign_tau_ge_half` forces `τ(r₀) ≥ 1/2`, so the *whole* certified radius is

  `1 − τ(r₀) − η ≤ 1/2 − η < 1/2`,

**independent of the rate `ρ`**.  Since the prize window is the interior of `(1 − √ρ, 1 − ρ)`
and `1/2 ≤ 1 − ρ` for every prize rate `ρ ∈ {1/2, 1/4, 1/8, 1/16}` (capacity `≥ 1/2`), this
radius is **strictly below capacity** for all prize rates: the R2 route on unfolded RS provably
cannot certify a list-decoding radius reaching the prize window's upper portion.  This is the
machine-checked radius form of the structural obstruction — it requires *folding* (`s ≫ 1`,
where `dim(A ⊓ ker eval_i) ≥ dim A − s` permits `τ(r) ≈ ρ` on `r ∈ [s]`, per GK16/GG25). -/
theorem unfolded_cz25_radius_lt_half
    {τ : ℕ → ℝ} {C : Submodule F (ι → Fin 1 → F)} (h : IsSubspaceDesign 1 τ C)
    {η : ℝ} (hη : 0 < η) (hr₀ : 2 ≤ Nat.floor (1 / η))
    {A : Submodule F (ι → Fin 1 → F)} (hAC : A ≤ C)
    (hrank : Module.finrank F A = 2) :
    1 - τ (Nat.floor (1 / η)) - η < 1 / 2 := by
  have hτ : (1 : ℝ) / 2 ≤ τ (Nat.floor (1 / η)) :=
    unfolded_subspaceDesign_tau_ge_half h hr₀ hAC hrank
  linarith [hτ, hη]

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.finrank_inf_ker_ge_sub_one_unfolded
#print axioms ProximityGap.unfolded_subspaceDesign_tau_ge
#print axioms ProximityGap.unfolded_subspaceDesign_tau_ge_half
#print axioms ProximityGap.unfolded_cz25_radius_lt_half

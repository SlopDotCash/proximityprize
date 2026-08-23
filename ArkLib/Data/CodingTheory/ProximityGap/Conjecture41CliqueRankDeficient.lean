/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Conjecture41CliqueKernelStructure
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Round 20 (Issue #232) — the clique constraint system is RANK-DEFICIENT by ≥ `|W| = w+1`,
# over EVERY field

Assembling the two axiom-clean facts of
`Conjecture41CliqueKernelStructure.lean` (namespace `Round20CliqueKernel`):

* `clique_kernel_mem` — for **every** weight `b : F → F`, the twisted evaluation pencil
  `(s₁, s₂) = (−∑ γ·b·ev_β, ∑ b·ev_β)` satisfies **every** clique kernel condition
  `⟨Λ_{E_α}X^r, s₁⟩ + γ(α)·⟨Λ_{E_α}X^r, s₂⟩ = 0`, over every field.
* `evalSyndrome_family_injective` — the map `b ↦ ∑ b·ev_β` is injective on `W`.

into ONE headline statement: the solution space (kernel) of the clique constraint conditions
contains, for every field and twist, a subspace of dimension **at least `W.card = w+1`**.

The mechanism: parameterise pencils by weights `b : ↥W → F` via the linear map

  `Φ : (↥W → F) →ₗ[F] (Fin D → F) × (Fin D → F)`,
  `b ↦ (fun j => −∑ β∈W, γ β · b β · ev_β j,  fun j => ∑ β∈W, b β · ev_β j)`.

* `Φ` is **injective** (its second component is, by `evalSyndrome_family_injective`), so its range
  is a subspace of dimension exactly `W.card` (`finrank (↥W → F) = W.card`).
* `Φ` lands **entirely inside** the clique kernel solution space (by `clique_kernel_mem`).

Hence `finrank F (cliqueKernelSpace …) ≥ W.card`. This is the **field-independent rank deficiency**:
the deficiency is structural over `ℚ` and over every `𝔽ₚ` alike — there is **no special prime `p₀`**
where the clique configuration becomes full rank. The exact kernel dimension (the conjectural
`(w+1) + (w−1)(c−1) − …`) is genuinely open and is **NOT** claimed here; only the floor `≥ w+1` is.
-/

open Polynomial Finset

namespace Round20CliqueKernel

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. Linearity of the pairing in the syndrome argument -/

omit [DecidableEq F] in
/-- The pairing `⟨P, ·⟩` is additive in the syndrome argument. -/
theorem pairing_add (D : ℕ) (P : F[X]) (s t : Fin D → F) :
    pairing D P (s + t) = pairing D P s + pairing D P t := by
  unfold pairing
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => by simp [Pi.add_apply]; ring)

omit [DecidableEq F] in
/-- The pairing `⟨P, ·⟩` is homogeneous in the syndrome argument. -/
theorem pairing_smul (D : ℕ) (P : F[X]) (c : F) (s : Fin D → F) :
    pairing D P (c • s) = c * pairing D P s := by
  unfold pairing
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by simp [Pi.smul_apply, smul_eq_mul]; ring)

omit [DecidableEq F] in
/-- The pairing `⟨P, ·⟩` sends `0` to `0`. -/
theorem pairing_zero (D : ℕ) (P : F[X]) : pairing D P (0 : Fin D → F) = 0 := by
  unfold pairing
  simp

/-! ## 2. The clique kernel conditions as a submodule of pencils -/

/-- A pencil `(s₁, s₂) ∈ F^D × F^D` satisfies the clique kernel condition at vertex `α` and
codimension index `r` (degree-fit `r` so the normal lives below `D`):
`⟨Λ_{E_α}X^r, s₁⟩ + γ(α)·⟨Λ_{E_α}X^r, s₂⟩ = 0`. -/
def cliqueKernelCond (D : ℕ) (W : Finset F) (γ : F → F) (α : F) (r : ℕ)
    (p : (Fin D → F) × (Fin D → F)) : Prop :=
  pairing D (normalPoly W α r) p.1 + γ α * pairing D (normalPoly W α r) p.2 = 0

/-- The clique kernel solution space: the set of pencils satisfying **every** clique kernel
condition (all `α ∈ W`, all degree-fitting `r`). It is a `Submodule` because `pairing` is linear
in the syndrome argument. -/
def cliqueKernelSpace (D : ℕ) (W : Finset F) (γ : F → F) :
    Submodule F ((Fin D → F) × (Fin D → F)) where
  carrier := {p | ∀ α ∈ W, ∀ r : ℕ, W.card - 1 + r < D → cliqueKernelCond D W γ α r p}
  add_mem' := by
    rintro p q hp hq α hα r hr
    have h1 := hp α hα r hr
    have h2 := hq α hα r hr
    simp only [cliqueKernelCond, Prod.fst_add, Prod.snd_add, pairing_add] at *
    have : pairing D (normalPoly W α r) p.1 + pairing D (normalPoly W α r) q.1
        + γ α * (pairing D (normalPoly W α r) p.2 + pairing D (normalPoly W α r) q.2)
        = (pairing D (normalPoly W α r) p.1 + γ α * pairing D (normalPoly W α r) p.2)
          + (pairing D (normalPoly W α r) q.1 + γ α * pairing D (normalPoly W α r) q.2) := by
      ring
    rw [this, h1, h2, add_zero]
  zero_mem' := by
    intro α hα r hr
    simp [cliqueKernelCond, pairing_zero]
  smul_mem' := by
    rintro c p hp α hα r hr
    have hc := hp α hα r hr
    simp only [cliqueKernelCond, Prod.smul_fst, Prod.smul_snd, pairing_smul] at *
    rw [show c * pairing D (normalPoly W α r) p.1 + γ α * (c * pairing D (normalPoly W α r) p.2)
        = c * (pairing D (normalPoly W α r) p.1 + γ α * pairing D (normalPoly W α r) p.2) by ring,
      hc, mul_zero]

/-! ## 2. The weight-parameterised pencil as a linear map -/

/-- The pencil map on raw weights `b : F → F`: `s₁` component (the negated, `γ`-twisted sum). -/
noncomputable def pencilFst (D : ℕ) (W : Finset F) (γ : F → F) (b : F → F) : Fin D → F :=
  fun j => -∑ β ∈ W, γ β * b β * evalSyndrome D β j

/-- The pencil map on raw weights `b : F → F`: `s₂` component (the plain evaluation sum). -/
noncomputable def pencilSnd (D : ℕ) (W : Finset F) (b : F → F) : Fin D → F :=
  fun j => ∑ β ∈ W, b β * evalSyndrome D β j

/-- The weight-parameterised pencil linear map
`Φ : (↥W → F) →ₗ[F] (Fin D → F) × (Fin D → F)`, where the weight is supported on `W`
(extended by `0` off `W` via `Finset.attach`). -/
noncomputable def pencilMap (D : ℕ) (W : Finset F) (γ : F → F) :
    (↥W → F) →ₗ[F] (Fin D → F) × (Fin D → F) where
  toFun b :=
    (pencilFst D W γ (fun β => if h : β ∈ W then b ⟨β, h⟩ else 0),
     pencilSnd D W (fun β => if h : β ∈ W then b ⟨β, h⟩ else 0))
  map_add' b₁ b₂ := by
    classical
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
    · simp only [pencilFst, Prod.fst_add, Pi.add_apply,← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun β hβ => ?_)
      simp only [dif_pos hβ]
      ring
    · simp only [pencilSnd, Prod.snd_add, Pi.add_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun β hβ => ?_)
      simp only [dif_pos hβ]
      ring
  map_smul' c b := by
    classical
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
    · simp only [pencilFst, RingHom.id_apply, Prod.smul_fst, Pi.smul_apply, smul_eq_mul,
        mul_neg, Finset.mul_sum]
      refine congrArg Neg.neg (Finset.sum_congr rfl (fun β hβ => ?_))
      simp only [dif_pos hβ]
      ring
    · simp only [pencilSnd, RingHom.id_apply, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl (fun β hβ => ?_)
      simp only [dif_pos hβ]
      ring

/-! ## 3. `pencilMap` is injective and lands in the kernel space -/

/-- `pencilMap` is **injective** — its `s₂` component is, by `evalSyndrome_family_injective`. -/
theorem pencilMap_injective (W : Finset F) (γ : F → F) {D : ℕ} (hD : W.card - 1 < D) :
    Function.Injective (pencilMap D W γ) := by
  classical
  rw [← LinearMap.ker_eq_bot]
  rw [Submodule.eq_bot_iff]
  intro b hb
  rw [LinearMap.mem_ker] at hb
  -- the second component vanishes
  have hb2 : pencilSnd D W (fun β => if h : β ∈ W then b ⟨β, h⟩ else 0) = 0 := by
    have h := congrArg Prod.snd hb
    simp only [pencilMap, LinearMap.coe_mk, AddHom.coe_mk, Prod.snd_zero] at h
    exact h
  have hzero := evalSyndrome_family_injective W hD
    (fun β => if h : β ∈ W then b ⟨β, h⟩ else 0) (by
      simpa only [pencilSnd] using hb2)
  -- read off b α = 0 for every α ∈ W
  ext α
  have := hzero α.1 α.2
  simpa only [dif_pos α.2] using this

/-- `pencilMap` lands **entirely inside** the clique kernel solution space — by
`clique_kernel_mem` (every pencil satisfies every clique kernel condition). -/
theorem pencilMap_range_le (W : Finset F) (γ : F → F) {D : ℕ} :
    LinearMap.range (pencilMap D W γ) ≤ cliqueKernelSpace D W γ := by
  classical
  rw [LinearMap.range_le_iff_comap, eq_top_iff]
  intro b _ α hα r hr
  -- unfold the membership condition and apply clique_kernel_mem
  have hkey := clique_kernel_mem W γ (fun β => if h : β ∈ W then b ⟨β, h⟩ else 0) hα hr
  simp only [cliqueKernelCond, pencilMap, LinearMap.coe_mk, AddHom.coe_mk]
  exact hkey

/-! ## 4. THE HEADLINE: rank deficiency by ≥ `|W| = w+1`, field-independently -/

/-- **THE CLIQUE CONSTRAINT SYSTEM IS RANK-DEFICIENT BY AT LEAST `|W| = w+1`, OVER EVERY FIELD.**

For any vertex set `W`, twist `γ : F → F`, and ambient dimension `D > |W|−1`, the clique kernel
solution space `cliqueKernelSpace D W γ` (the pencils satisfying every clique kernel condition) has

  `finrank F (cliqueKernelSpace D W γ) ≥ W.card`.

Proof: the weight-parameterised pencil map `pencilMap D W γ : (↥W → F) →ₗ (Fin D → F)²` is injective
(`pencilMap_injective`, from `evalSyndrome_family_injective`) and its range lies inside the solution
space (`pencilMap_range_le`, from `clique_kernel_mem`); so the solution space contains a subspace of
dimension `finrank (↥W → F) = W.card`.

This bound holds over **every** field — `ℚ`, every `𝔽ₚ` — with the **same** floor `W.card`: the
rank deficiency is structural, not arithmetic. There is **no special prime `p₀`** restoring full
rank, and no codimension `c` (= the range of `r`) at which the clique configuration is
rank-saturated. The exact kernel dimension remains open; this is the verified floor `≥ w+1`. -/
theorem cliqueKernelSpace_finrank_ge (W : Finset F) (γ : F → F) {D : ℕ} (hD : W.card - 1 < D) :
    W.card ≤ Module.finrank F (cliqueKernelSpace D W γ) := by
  classical
  -- the range of pencilMap is a subspace of the solution space, of dimension exactly W.card
  have hinj := pencilMap_injective W γ hD
  have hle := pencilMap_range_le (D := D) W γ
  -- finrank of the range = finrank of the domain (injective lin map)
  have hrange : Module.finrank F (LinearMap.range (pencilMap D W γ)) = W.card := by
    rw [LinearMap.finrank_range_of_inj hinj]
    rw [Module.finrank_pi]
    simp [Fintype.card_coe]
  -- monotonicity of finrank along the submodule inclusion (ambient is finite-dim)
  calc W.card = Module.finrank F (LinearMap.range (pencilMap D W γ)) := hrange.symm
    _ ≤ Module.finrank F (cliqueKernelSpace D W γ) :=
        Submodule.finrank_mono hle

end Round20CliqueKernel

#print axioms Round20CliqueKernel.cliqueKernelSpace_finrank_ge

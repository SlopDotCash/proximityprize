/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Folded
import ArkLib.Data.CodingTheory.ProximityGap.GK16Claim16Transport
import ArkLib.Data.CodingTheory.ProximityGap.GK16DegreeBudget
import ArkLib.ToMathlib.GK16Claim16Witness
import ArkLib.Data.CodingTheory.ProximityGap.GK16Lemma12

/-!
# Encoder-isomorphism transport for the FRS subspace-design budget (GK16 §4)

This file discharges the **encoder-isomorphism transport** half of GK16 Claim 16 / Theorem
2.18: it carries the abstract adapted-recombination engine
(`ArkLib.FRS.GK16.exists_adapted_recombination`) across the FRS encoder
`E := frsEvalOnPoints domain s ω` to produce, for any subspace `A ≤ frsCode` with
`finrank A ≤ s` and an **injective** encoder, the per-coordinate multiplicity lower bound

  `dim (A ⊓ ker(eval_i)) ≤ rootMultiplicity (domain i) (foldedWronskian P ω)`

for a realizing polynomial family `P` of degrees `< k`.  Summed and chained with the
verified degree-budget spine, this yields the GK16 §4 budget
`∑_i dim A_i ≤ (dim A)·(k-1)` on the `finrank A ≤ s` range — exactly the range used in the
`r ∈ [s]` branch of the subspace-design profile.

## Key construction

For `A ≤ frsCode = (degreeLT F k).map E`, with `E` injective, the **pullback**
`U := A.comap E ⊓ degreeLT F k` is a polynomial subspace with `U.map E = A` and (via the
injective-image equiv) `finrank U = finrank A`.  A basis `bU` of `U` gives the realizing
family `P j := (bU j : F[X])` (independent, degrees `< k`).  Per coordinate `i`, the
orbit-vanishing subspace `W_i ≤ U` (polynomials killed by `proj i ∘ E`) has
`finrank W_i = finrank (A ⊓ ker (proj i))` (the iso restricts), and the adapted
recombination of `bU` to `W_i` feeds the proven Claim-16 engine.

The side condition `finrank A ≤ s` is genuine: the Claim-16 engine's orbit-vanishing
hypothesis ranges over the `finrank A` dilation rows `ω^b`, which must be among the `s`
folds (`b < finrank A ≤ s`).

Everything here is `sorry`/axiom-clean.
-/

set_option linter.unusedSectionVars false

open Polynomial Module

namespace ReedSolomon.Folded

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

/-- The FRS evaluation map composed with the `i`-th coordinate projection, as a single
`F`-linear map `F[X] →ₗ[F] (Fin s → F)`. A polynomial lies in its kernel iff it vanishes
on the whole `s`-fold orbit `{domain i · ω^j : j < s}`. -/
noncomputable def evalAtCoord (domain : ι ↪ F) (s : ℕ) (ω : F) (i : ι) :
    Polynomial F →ₗ[F] (Fin s → F) :=
  (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i).comp
    (frsEvalOnPoints domain s ω)

@[simp] lemma evalAtCoord_apply (domain : ι ↪ F) (s : ℕ) (ω : F) (i : ι)
    (p : Polynomial F) (j : Fin s) :
    evalAtCoord domain s ω i p j = p.eval (domain i * ω ^ (j : ℕ)) := rfl

/-- The **polynomial pullback** of a subspace `A` of the folded RS code: the degree-`< k`
polynomials whose encoding lies in `A`. -/
noncomputable def frsPullback (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (A : Submodule F (ι → Fin s → F)) : Submodule F (Polynomial F) :=
  A.comap (frsEvalOnPoints domain s ω) ⊓ Polynomial.degreeLT F k

variable {domain : ι ↪ F} {k s : ℕ} {ω : F}

/-- Every pullback polynomial has degree `< k`, hence `natDegree ≤ k - 1`. -/
lemma natDegree_le_of_mem_frsPullback {A : Submodule F (ι → Fin s → F)}
    {p : Polynomial F} (hp : p ∈ frsPullback domain k s ω A) :
    p.natDegree ≤ k - 1 := by
  have hdeg : p.degree < (k : WithBot ℕ) :=
    (Polynomial.mem_degreeLT).mp hp.2
  rcases eq_or_ne p 0 with hp0 | hp0
  · simp [hp0]
  · have hnd : (p.natDegree : WithBot ℕ) < (k : WithBot ℕ) := by
      rwa [Polynomial.degree_eq_natDegree hp0] at hdeg
    have : p.natDegree < k := by exact_mod_cast hnd
    omega

/-- **Pullback maps onto `A`.** When the encoder is injective and `A ≤ frsCode`, the
pullback `U := A.comap E ⊓ degreeLT F k` satisfies `U.map E = A`. -/
lemma frsPullback_map_eq {A : Submodule F (ι → Fin s → F)}
    (hA : A ≤ frsCode domain k s ω) :
    (frsPullback domain k s ω A).map (frsEvalOnPoints domain s ω) = A := by
  apply le_antisymm
  · -- image ⊆ A: members come from `A.comap E`.
    rintro _ ⟨p, hp, rfl⟩
    exact hp.1
  · -- A ⊆ image: every `a ∈ A ≤ frsCode` is `E p` with `p ∈ degreeLT`, and then `p ∈ U`.
    intro a ha
    obtain ⟨p, hp_deg, rfl⟩ := hA ha
    exact ⟨p, ⟨ha, hp_deg⟩, rfl⟩

/-- **Pullback preserves dimension.** `finrank (frsPullback …) = finrank A`. -/
lemma finrank_frsPullback_eq {A : Submodule F (ι → Fin s → F)}
    (hEinj : Function.Injective (frsEvalOnPoints domain s ω))
    (hA : A ≤ frsCode domain k s ω) :
    Module.finrank F (frsPullback domain k s ω A) = Module.finrank F A := by
  have e := Submodule.equivMapOfInjective (frsEvalOnPoints domain s ω) hEinj
    (frsPullback domain k s ω A)
  rw [e.finrank_eq, frsPullback_map_eq hA]

/-- The pullback inherits the `finrank ≤ s` range needed by the GK16 adapted
recombination engine. -/
lemma finrank_frsPullback_le {A : Submodule F (ι → Fin s → F)}
    (hEinj : Function.Injective (frsEvalOnPoints domain s ω))
    (hA : A ≤ frsCode domain k s ω)
    (hAs : Module.finrank F A ≤ s) :
    Module.finrank F (frsPullback domain k s ω A) ≤ s := by
  rw [finrank_frsPullback_eq hEinj hA]
  exact hAs

/-- The **orbit-vanishing subspace** inside the pullback: pullback polynomials that vanish
on the entire `s`-fold orbit of `domain i`. -/
noncomputable def frsVanish (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (A : Submodule F (ι → Fin s → F)) (i : ι) : Submodule F (Polynomial F) :=
  frsPullback domain k s ω A ⊓ LinearMap.ker (evalAtCoord domain s ω i)

/-- **Orbit-vanishing maps onto the per-coordinate vanishing subspace.**
`(frsVanish … i).map E = A ⊓ ker(proj i)`. -/
lemma frsVanish_map_eq {A : Submodule F (ι → Fin s → F)}
    (hA : A ≤ frsCode domain k s ω) (i : ι) :
    (frsVanish domain k s ω A i).map (frsEvalOnPoints domain s ω) =
      A ⊓ LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) := by
  apply le_antisymm
  · -- image ⊆ A ⊓ ker(proj i)
    rintro _ ⟨p, ⟨hpU, hpV⟩, rfl⟩
    refine Submodule.mem_inf.mpr ⟨hpU.1, ?_⟩
    -- `E p ∈ ker(proj i)` since `evalAtCoord i p = 0`.
    apply LinearMap.mem_ker.mpr
    simp only [LinearMap.proj_apply]
    have hz : evalAtCoord domain s ω i p = 0 := (LinearMap.mem_ker).mp hpV
    funext j
    have := congrFun hz j
    simpa [evalAtCoord_apply] using this
  · -- A ⊓ ker(proj i) ⊆ image
    intro a ha_mem
    obtain ⟨ha, hker⟩ := Submodule.mem_inf.mp ha_mem
    obtain ⟨p, hp_deg, rfl⟩ := hA ha
    refine ⟨p, ⟨⟨ha, hp_deg⟩, ?_⟩, rfl⟩
    -- `p ∈ ker(evalAtCoord i)` since `E p i = 0`.
    apply LinearMap.mem_ker.mpr
    have hi : frsEvalOnPoints domain s ω p i = 0 := by
      have hk := (LinearMap.mem_ker).mp hker
      rwa [LinearMap.proj_apply] at hk
    funext j
    have := congrFun hi j
    simpa [evalAtCoord_apply] using this

/-- **Orbit-vanishing preserves dimension.**
`finrank (frsVanish … i) = finrank (A ⊓ ker(proj i))`. -/
lemma finrank_frsVanish_eq {A : Submodule F (ι → Fin s → F)}
    (hEinj : Function.Injective (frsEvalOnPoints domain s ω))
    (hA : A ≤ frsCode domain k s ω) (i : ι) :
    Module.finrank F (frsVanish domain k s ω A i) =
      Module.finrank F (↥(A ⊓ LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) := by
  have e := Submodule.equivMapOfInjective (frsEvalOnPoints domain s ω) hEinj
    (frsVanish domain k s ω A i)
  rw [e.finrank_eq, frsVanish_map_eq hA i]

/-- The orbit-vanishing pullback lies in the `finrank ≤ s` range whenever the
original FRS subspace does. -/
lemma finrank_frsVanish_le {A : Submodule F (ι → Fin s → F)}
    (hEinj : Function.Injective (frsEvalOnPoints domain s ω))
    (hA : A ≤ frsCode domain k s ω)
    (hAs : Module.finrank F A ≤ s) (i : ι) :
    Module.finrank F (frsVanish domain k s ω A i) ≤ s := by
  rw [finrank_frsVanish_eq hEinj hA i]
  exact le_trans (Submodule.finrank_mono (inf_le_left :
    A ⊓ LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) ≤ A)) hAs

/-- **Encoder-transport, single-subspace GK16 §4 budget.** For a subspace `A ≤ frsCode`
with an injective encoder and `finrank A ≤ s`, and a folding element `ω` satisfying the
degree-separation admissibility `hω_sep`, the per-coordinate vanishing dimensions sum to at
most `(finrank A)·(k-1)`:

  `∑_i dim (A ⊓ ker(eval_i)) ≤ (finrank A)·(k - 1)`.

This is the GK16 §4 budget specialised to the design-relevant range `finrank A ≤ s`. It is
obtained by transporting `A` to its polynomial pullback `U` (a degree-`< k` space of the
same dimension), realizing a basis as a linearly-independent family `P` of degrees `< k`,
and — per coordinate — feeding the proven Claim-16 engine an *adapted recombination* of `P`
to the orbit-vanishing subspace (`exists_adapted_recombination`), giving
`dim A_i ≤ rootMultiplicity (domain i) (foldedWronskian P ω)`.  Summing and chaining with
the verified spine `sum_rootMultiplicity_foldedWronskian_le` closes it. -/
theorem frs_degreeBudget_of_finrank_le
    (A : Submodule F (ι → Fin s → F))
    (hEinj : Function.Injective (frsEvalOnPoints domain s ω))
    (hA : A ≤ frsCode domain k s ω)
    (hAs : Module.finrank F A ≤ s)
    (hω_sep : ∀ Q : Fin (Module.finrank F A) → Polynomial F, (∀ j, Q j ≠ 0) →
        Function.Injective (fun j => (Q j).natDegree) →
        Function.Injective (fun j => ω ^ (Q j).natDegree)) :
    (∑ i : ι, Module.finrank F (↥(A ⊓
        (LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
        Submodule F (ι → Fin s → F))))
      ≤ Module.finrank F A * (k - 1) := by
  classical
  set n := Module.finrank F A with hn
  set U := frsPullback domain k s ω A with hU
  -- `U ≤ degreeLT F k` is finite-dimensional (so is `↥U`).
  haveI : FiniteDimensional F (Polynomial.degreeLT F k) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv F k).symm
  haveI : FiniteDimensional F U :=
    Submodule.finiteDimensional_of_le (S₂ := Polynomial.degreeLT F k) inf_le_right
  -- A basis of the pullback, indexed by `Fin n`.
  have hUrank : Module.finrank F U = n := finrank_frsPullback_eq hEinj hA
  let bU : Basis (Fin n) F U := by
    rw [← hUrank]; exact Module.finBasis F U
  -- The realizing polynomial family.
  let P : Fin n → Polynomial F := fun j => (bU j : Polynomial F)
  have hP_deg : ∀ j, (P j).natDegree ≤ k - 1 := fun j =>
    natDegree_le_of_mem_frsPullback (bU j).2
  -- `P` is linearly independent (image of a basis under the injective subtype).
  have hP_indep : LinearIndependent F P := by
    have hbi : LinearIndependent F (fun j => bU j) := bU.linearIndependent
    exact hbi.map' U.subtype (Submodule.ker_subtype U)
  -- The folded Wronskian is nonzero (Lemma 12, hard direction).
  have hL_ne : ArkLib.FRS.GK16.foldedWronskian P ω ≠ 0 :=
    ArkLib.FRS.GK16.foldedWronskian_ne_zero_of_linearIndependent P ω hP_indep hω_sep
  -- Per coordinate: `dim A_i ≤ rootMultiplicity (domain i) (foldedWronskian P ω)`.
  have hclaim16 : ∀ i : ι,
      Module.finrank F (↥(A ⊓ (LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
          Submodule F (ι → Fin s → F)))
      ≤ Polynomial.rootMultiplicity (domain i)
          (ArkLib.FRS.GK16.foldedWronskian P ω) := by
    intro i
    -- The orbit-vanishing subspace `Wi ≤ U`, viewed inside `↥U`.
    have hWi_le : frsVanish domain k s ω A i ≤ U := inf_le_left
    set d := Module.finrank F (↥(A ⊓ (LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)))) with hd
    have hWcomap_rank :
        Module.finrank F ((frsVanish domain k s ω A i).comap U.subtype) = d := by
      rw [(Submodule.comapSubtypeEquivOfLe hWi_le).finrank_eq, hd]
      exact finrank_frsVanish_eq hEinj hA i
    -- The adapted recombination of `bU` to the orbit-vanishing subspace.
    obtain ⟨Q, c, T, hc_det, hQ_rec, hT_card, hT_mem⟩ :=
      ArkLib.FRS.GK16.exists_adapted_recombination bU
        ((frsVanish domain k s ω A i).comap U.subtype) hWcomap_rank
    -- Push the recombination down to polynomials via the subtype.
    let Qpoly : Fin n → Polynomial F := fun l => (Q l : Polynomial F)
    have hQpoly_rec : ∀ l, Qpoly l = ∑ m, c l m • P m := by
      intro l
      have hcoe := congrArg (fun u : U => (u : Polynomial F)) (hQ_rec l)
      simpa [Qpoly, P, Submodule.coe_sum, Submodule.coe_smul] using hcoe
    -- Members of `T` vanish on the whole `Fin n`-orbit (since `n ≤ s`).
    have hvanish : ∀ l ∈ T, ∀ b : Fin n,
        (Qpoly l).eval (domain i * ω ^ (b : ℕ)) = 0 := by
      intro l hl b
      -- `Q l ∈ comap subtype (frsVanish i)`, so `(Q l : F[X]) ∈ frsVanish i ≤ ker eval`.
      have hmem : (Q l : Polynomial F) ∈ frsVanish domain k s ω A i :=
        (Submodule.mem_comap).mp (hT_mem l hl)
      have hker : evalAtCoord domain s ω i (Q l : Polynomial F) = 0 :=
        (LinearMap.mem_ker).mp hmem.2
      have hbs : (b : ℕ) < s := lt_of_lt_of_le b.2 hAs
      have hcg := congrFun hker ⟨(b : ℕ), hbs⟩
      simpa [Qpoly, evalAtCoord_apply] using hcg
    -- Apply the proven Claim-16 engine; `T.card = d`.
    have hbound := ArkLib.FRS.GK16.claim16_rootMultiplicity_ge
      P Qpoly ω (domain i) c hc_det hQpoly_rec hL_ne T hvanish
    rwa [hT_card] at hbound
  -- Chain the per-coordinate bounds with the verified degree-budget spine.
  calc (∑ i : ι, Module.finrank F (↥(A ⊓ (LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
          Submodule F (ι → Fin s → F))))
      ≤ ∑ i : ι, Polynomial.rootMultiplicity (domain i)
          (ArkLib.FRS.GK16.foldedWronskian P ω) :=
        Finset.sum_le_sum (fun i _ => hclaim16 i)
    _ = ∑ a ∈ (Finset.univ.image domain),
          Polynomial.rootMultiplicity a (ArkLib.FRS.GK16.foldedWronskian P ω) := by
        rw [Finset.sum_image (fun i _ j _ h => domain.injective h)]
    _ ≤ n * (k - 1) :=
        ArkLib.FRS.GK16.sum_rootMultiplicity_foldedWronskian_le P ω hP_deg hL_ne _

end ReedSolomon.Folded

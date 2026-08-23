/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BKR06Pigeonhole
import ArkLib.Data.CodingTheory.ListDecoding.SubspacePolyGeneralSupport
import ArkLib.ToMathlib.LinearizedPigeonhole

/-!
# BKR06 Lemma 3.5 — the **tight** subspace-polynomial pigeonhole family

The tight form of `BKR06.bkr06_pigeonhole_family_card`.  Because subspace polynomials are
**q-power-supported** (`isQPowSupported_subspacePoly'`, the linearized-support theorem), the
top-coefficient pattern above the cutoff `q^u` lives in only the `v − u` linearized slots
`q^{u+1},…,q^v` (not a generic width-`w` window).  Feeding the `q^{v(m−v)}` graph family
(`card_dimv_subspaces_ge`) into the **tight** linearized pigeonhole `exists_qpow_pattern_fiber`
gives a sub-family of size `> N` whenever `(#K)^{v−u}·N < q^{v(m−v)}`, on which all pairwise
subspace-polynomial differences vanish above `q^u`.  This is the slot economy behind BKR06's
`q^{(u+1)m − v²}` list-size count (the `hexp` exponent), now with the *tight* `(#K)^{v−u}` count.
-/

open Polynomial BigOperators ArkLib.LinearizedKernel

namespace BKR06

universe u

variable {K : Type u} [Field K] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Fintype F] [Algebra F K]

noncomputable local instance fintypeSubmoduleK (W : Submodule F K) : Fintype W := Fintype.ofFinite W

/-- **BKR06 Lemma 3.5, tight (linearized) form.** A sub-family of `> N` distinct dimension-`v`
subspaces whose subspace-polynomial differences all vanish above `q^u`, available whenever
`(#K)^{v−u}·N < q^{v(m−v)}` — the tight `(#K)^{v−u}` pattern count from q-power support. -/
theorem bkr06_tight_pigeonhole_family
    (v u N : ℕ) (hv : v ≤ Module.finrank F K)
    (hbig : (Fintype.card K) ^ (v - u) * N
        < (Fintype.card F) ^ (v * (Module.finrank F K - v))) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (𝓛 : ι → Submodule F K)
      (_ : ∀ i, Fintype (𝓛 i)),
      N < Fintype.card ι ∧
      (∀ i, Module.finrank F (𝓛 i) = v) ∧
      Function.Injective (fun i => subspacePoly (subFinset (𝓛 i))) ∧
      (∀ i j n, Fintype.card F ^ u < n →
        (subspacePoly (subFinset (𝓛 i)) - subspacePoly (subFinset (𝓛 j))).coeff n = 0) := by
  classical
  obtain ⟨S, hScard, hSdim⟩ := card_dimv_subspaces_ge (F := F) (K := K) v hv
  let g : {W : Submodule F K // W ∈ S} → K[X] := fun W => subspacePoly (subFinset W.val)
  have hg_inj : Function.Injective g := fun W₁ W₂ hW => by
    by_contra hne
    exact subspacePoly_ne_of_ne W₁.val W₂.val (fun h => hne (Subtype.ext h)) hW
  have hg_deg : ∀ W : {W : Submodule F K // W ∈ S}, (g W).natDegree ≤ (Fintype.card F) ^ v := by
    intro W
    have hdim : Module.finrank F W.val = v := hSdim W.val W.2
    show (subspacePoly (subFinset W.val)).natDegree ≤ (Fintype.card F) ^ v
    rw [subspacePoly_natDegree_eq_pow_finrank, hdim]
  have hg_supp : ∀ W : {W : Submodule F K // W ∈ S}, IsQPowSupported (F := F) (g W) :=
    fun W => isQPowSupported_subspacePoly' W.val
  have hScard' : (Fintype.card F) ^ (v * (Module.finrank F K - v))
      ≤ Fintype.card {W : Submodule F K // W ∈ S} := by
    rw [Fintype.card_coe]; exact hScard
  have hbig' : (Fintype.card K) ^ (v - u) * N
      < Fintype.card {W : Submodule F K // W ∈ S} := lt_of_lt_of_le hbig hScard'
  obtain ⟨T, hTcard, hTsmall⟩ := exists_qpow_pattern_fiber g u v N hg_supp hg_deg hbig'
  refine ⟨{t : {W : Submodule F K // W ∈ S} // t ∈ T}, inferInstance, inferInstance,
    fun t => t.val.val, fun _ => inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_coe]; exact hTcard
  · intro t; exact hSdim _ t.val.2
  · intro t₁ t₂ ht
    exact Subtype.ext (hg_inj ht)
  · intro t₁ t₂ n hn
    exact hTsmall t₁.val t₁.2 t₂.val t₂.2 n hn

end BKR06

-- Axiom audit.
#print axioms BKR06.bkr06_tight_pigeonhole_family

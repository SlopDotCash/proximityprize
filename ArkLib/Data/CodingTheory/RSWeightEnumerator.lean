/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.RSVanishingDim
import Mathlib.FieldTheory.Finiteness

/-!
# Reed–Solomon (MDS) support counts — toward the weight enumerator `A_d`

The MDS weight enumerator of `RS[deg]` is assembled by inclusion–exclusion from the *support
counts*: how many degree-`<deg` codewords vanish on a given coordinate set `S` (equivalently, are
supported on its complement).  Over a finite field, that count is `q^{deg − |S|}` — the cardinality
of the vanishing subspace whose dimension is `deg − |S|` (`finrank_ker_evalOnS`).  This is the
entropy-free combinatorial core feeding the CS25 second-moment bound (#82): the pairwise / weight
distribution `∑_d A_d · …` builds on these counts.
-/

namespace ArkLib.CS25

open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- **MDS support count.**  Over a finite field `F` with `q = |F|`, the number of degree-`<deg`
polynomials vanishing on a coordinate set `S` with `|S| ≤ deg` is `q^{deg − |S|}` — the cardinality
of the vanishing subspace `ker (evalOnS α deg S)`, whose dimension is `deg − |S|`
(`finrank_ker_evalOnS`).  The inclusion–exclusion building block of the RS/MDS weight enumerator. -/
theorem natCard_ker_evalOnS (α : ι ↪ F) (deg : ℕ) (S : Finset ι) (hS : S.card ≤ deg) :
    Nat.card (LinearMap.ker (evalOnS α deg S)) = (Fintype.card F) ^ (deg - S.card) := by
  haveI : FiniteDimensional F (Polynomial.degreeLT F deg) :=
    FiniteDimensional.of_injective (Polynomial.degreeLTEquiv F deg).toLinearMap
      (Polynomial.degreeLTEquiv F deg).injective
  haveI : Fintype (Polynomial.degreeLT F deg) :=
    Fintype.ofEquiv (Fin deg → F) (Polynomial.degreeLTEquiv F deg).symm.toEquiv
  haveI : Fintype (LinearMap.ker (evalOnS α deg S)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F),
    finrank_ker_evalOnS α deg S hS]

/-- **MDS support count, general `S`.**  Drops the `|S| ≤ deg` hypothesis: when `|S| > deg` the
vanishing subspace collapses to `⊥` (a degree-`<deg` polynomial cannot vanish on more than `deg−1`
nodes), and `q^{deg−|S|} = q^0 = 1` matches by `ℕ`-subtraction.  This is the form the inclusion–
exclusion for `A_d` needs (zero-sets `T` range up to size `n`). -/
theorem natCard_ker_evalOnS_general (α : ι ↪ F) (deg : ℕ) (S : Finset ι) :
    Nat.card (LinearMap.ker (evalOnS α deg S)) = (Fintype.card F) ^ (deg - S.card) := by
  by_cases hS : S.card ≤ deg
  · exact natCard_ker_evalOnS α deg S hS
  · push_neg at hS
    haveI : FiniteDimensional F (Polynomial.degreeLT F deg) :=
      FiniteDimensional.of_injective (Polynomial.degreeLTEquiv F deg).toLinearMap
        (Polynomial.degreeLTEquiv F deg).injective
    rw [Nat.sub_eq_zero_of_le hS.le, pow_zero]
    obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_eq (le_of_lt hS)
    have hbot' : LinearMap.ker (evalOnS α deg S') = ⊥ := by
      have hf := finrank_ker_evalOnS α deg S' (by omega : S'.card ≤ deg)
      rw [hS'card, Nat.sub_self] at hf
      exact Submodule.finrank_eq_zero.mp hf
    have hle : LinearMap.ker (evalOnS α deg S) ≤ LinearMap.ker (evalOnS α deg S') := by
      intro p hp
      rw [LinearMap.mem_ker] at hp ⊢
      ext i
      have hmem : (i : ι) ∈ S := hS'sub i.2
      have := congrFun hp ⟨(i : ι), hmem⟩
      simpa [evalOnS] using this
    have hbot : LinearMap.ker (evalOnS α deg S) = ⊥ := by
      rw [eq_bot_iff, ← hbot']; exact hle
    rw [hbot]; simp

/-- **Support-⊆ sum.**  Summing the support count over all `d`-element coordinate sets `T` (a
codeword of weight `d` is supported on some such `T`, i.e. vanishes on `Tᶜ`):

  `∑_{|T|=d} #{p vanishing on Tᶜ} = C(n, d) · q^{deg − (n − d)}`.

There are `C(n,d)` sets `T`, each contributing the constant `q^{deg − |Tᶜ|} = q^{deg − (n − d)}`
(`natCard_ker_evalOnS_general`).  This is the right-hand side of the MDS weight-enumerator upper
bound `A_d ≤ C(n,d)·q^{d−(n−deg)}` (every weight-`d` codeword is counted in its own support term). -/
theorem supportSubsetSum_eq (α : ι ↪ F) (deg d : ℕ) :
    ∑ T ∈ (Finset.univ : Finset ι).powersetCard d,
        Nat.card (LinearMap.ker (evalOnS α deg Tᶜ))
      = (Fintype.card ι).choose d * (Fintype.card F) ^ (deg - (Fintype.card ι - d)) := by
  have hconst : ∀ T ∈ (Finset.univ : Finset ι).powersetCard d,
      Nat.card (LinearMap.ker (evalOnS α deg Tᶜ))
        = (Fintype.card F) ^ (deg - (Fintype.card ι - d)) := by
    intro T hT
    rw [Finset.mem_powersetCard] at hT
    rw [natCard_ker_evalOnS_general, Finset.card_compl, hT.2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    smul_eq_mul]

/-- The **evaluation support** of a degree-`<deg` polynomial: the coordinates where it does not
vanish (the Hamming support of the corresponding RS codeword). -/
noncomputable def evalSupport (α : ι ↪ F) {deg : ℕ} (p : Polynomial.degreeLT F deg) : Finset ι :=
  Finset.univ.filter (fun i => (p : F[X]).eval (α i) ≠ 0)

omit [Fintype F] in
/-- **Support ↔ vanishing.**  A degree-`<deg` polynomial lies in the vanishing subspace on `Tᶜ`
exactly when its evaluation support is contained in `T` — both say `p` vanishes off `T`.  This
identifies the support-`⊆ T` codewords with `ker (evalOnS α deg Tᶜ)`, bridging the support counts
to the actual weight distribution. -/
theorem mem_ker_evalOnS_compl_iff (α : ι ↪ F) (deg : ℕ) (T : Finset ι)
    (p : Polynomial.degreeLT F deg) :
    p ∈ LinearMap.ker (evalOnS α deg Tᶜ) ↔ evalSupport α p ⊆ T := by
  rw [LinearMap.mem_ker, funext_iff]
  constructor
  · intro h i hi
    rw [evalSupport, Finset.mem_filter] at hi
    by_contra hiT
    exact hi.2 (h ⟨i, Finset.mem_compl.mpr hiT⟩)
  · intro h j
    by_contra hj
    have hmem : (j : ι) ∈ evalSupport α p := by
      rw [evalSupport, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hj⟩
    exact (Finset.mem_compl.mp j.2) (h hmem)

omit [DecidableEq ι] in
/-- **MDS weight-enumerator upper bound `A_d ≤ C(n,d)·q^{d−(n−deg)}`.**  The number of
degree-`<deg` polynomials whose evaluation has Hamming weight exactly `d` is at most the
support-⊆ sum: every such polynomial is supported on (hence counted in) the term for its own
`d`-element support set.  Combined with `supportSubsetSum_eq`, this is the classical MDS
weight-distribution upper bound feeding the CS25 second moment (#82). -/
theorem card_evalWeight_le (α : ι ↪ F) (deg : ℕ)
    [Fintype (Polynomial.degreeLT F deg)] (d : ℕ) :
    (Finset.univ.filter
        (fun p : Polynomial.degreeLT F deg => (evalSupport α p).card = d)).card
      ≤ (Fintype.card ι).choose d * (Fintype.card F) ^ (deg - (Fintype.card ι - d)) := by
  classical
  let W : Finset (Polynomial.degreeLT F deg) :=
    Finset.univ.filter (fun p : Polynomial.degreeLT F deg => (evalSupport α p).card = d)
  let U : Finset (Polynomial.degreeLT F deg) :=
    ((Finset.univ : Finset ι).powersetCard d).biUnion
      (fun T =>
        Finset.univ.filter (fun p : Polynomial.degreeLT F deg =>
          p ∈ LinearMap.ker (evalOnS α deg Tᶜ)))
  have hcover : W ⊆ U := by
    intro p hp
    dsimp [W] at hp
    rw [Finset.mem_filter] at hp
    dsimp [U]
    refine Finset.mem_biUnion.mpr ⟨evalSupport α p, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hp.2⟩
    · rw [Finset.mem_filter, mem_ker_evalOnS_compl_iff]
      exact ⟨Finset.mem_univ _, Finset.Subset.refl _⟩
  have hsum_eq :
      (∑ T ∈ (Finset.univ : Finset ι).powersetCard d,
          (Finset.univ.filter (fun p : Polynomial.degreeLT F deg =>
            p ∈ LinearMap.ker (evalOnS α deg Tᶜ))).card)
        = ∑ T ∈ (Finset.univ : Finset ι).powersetCard d,
          Nat.card (LinearMap.ker (evalOnS α deg Tᶜ)) := by
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc
    (Finset.univ.filter
        (fun p : Polynomial.degreeLT F deg => (evalSupport α p).card = d)).card
        = W.card := rfl
    _ ≤ U.card := Finset.card_le_card hcover
    _ ≤ ∑ T ∈ (Finset.univ : Finset ι).powersetCard d,
          (Finset.univ.filter (fun p : Polynomial.degreeLT F deg =>
            p ∈ LinearMap.ker (evalOnS α deg Tᶜ))).card := by
      dsimp [U]
      exact Finset.card_biUnion_le
    _ = ∑ T ∈ (Finset.univ : Finset ι).powersetCard d,
          Nat.card (LinearMap.ker (evalOnS α deg Tᶜ)) := hsum_eq
    _ = (Fintype.card ι).choose d * (Fintype.card F) ^ (deg - (Fintype.card ι - d)) :=
      supportSubsetSum_eq α deg d

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.natCard_ker_evalOnS
#print axioms ArkLib.CS25.natCard_ker_evalOnS_general
#print axioms ArkLib.CS25.supportSubsetSum_eq
#print axioms ArkLib.CS25.mem_ker_evalOnS_compl_iff
#print axioms ArkLib.CS25.card_evalWeight_le

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#466, lane L5)
-/
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Additive/Binius domain dissolution, part II: the dilated spectrum and `S^⊥`
# (#466, lane L5 — companion to `_AdditiveDomainDissolution.lean`)

The companion file proves the fixed-character dichotomy (`∑_{x∈S} ψ x ∈ {0, |S|}`), the
coset blindness, and `E(S) = |S|³`.  This file pins the two remaining pieces of the lane:

* **The full far-direction spectrum collapses** (`dilated_sum_dichotomy`): the
  multiplicative-domain wall object is the FAMILY `η_b = ∑_{x∈μ_n} ψ(b·x)` over all
  directions `b`, with `M = max_{b≠0} |η_b|` at an unknown scale.  For an additive
  subgroup/`F₂`-subspace `s` of a ring, EVERY dilated sum `∑_{x∈s} ψ(b·x)` is `|s|` or `0` —
  the spectrum `{η_b}_b` of an additive domain is a two-point set, for every `b` at once.
* **Exactly WHERE the `|s|`-spikes sit** (`dilated_sum_eq_card_iff_mem_dualDirections`):
  the spike set is precisely the **annihilator subgroup**
  `s^⊥ := dualDirections s ψ = {b | x ↦ ψ(b·x) is trivial on s}` — constructed here as an
  honest `AddSubgroup` of the ambient ring.  For the canonical trace character of
  `F_{2^k}` this is the trace-dual `F₂`-subspace of `s`.

## HONEST CAVEAT (same as the companion file — do NOT over-claim)

This does NOT resolve any Binius/additive-RS proximity or soundness question.  It proves
the *relocation*: all magnitude information in the far-direction spectrum degenerates, and
the surviving discriminating object is the coset geometry of `dualDirections s ψ` (which
dilations/offsets of a folded additive-NTT domain land in `s^⊥`, i.e. the dual-code
weight/coset structure across the NTT subspace flag).  That subspace-lattice problem — and
beyond-Johnson mutual correlated agreement for additive-NTT RS in general — remains OPEN.
Nothing here transfers back to the multiplicative prize core (#466 §2).

Everything below is axiom-clean (`propext, Classical.choice, Quot.sound`; no `sorryAx`).
Parseval cross-check: `∑_b |η_b|² = |F|·|s|` forces `#spikes = |F|/|s|` when the pairing is
nondegenerate — consistent with the spikes being exactly `s^⊥` (trace pairing:
`|s^⊥| = |F|/|s|`).  kb note: `docs/kb/deltastar-466-additive-domain-dissolution.md`.
-/

namespace ArkLib.ProximityGap.AdditiveDomainDissolution

open Finset

section Dilated

variable {F : Type*} [CommRing F] {R : Type*} [CommRing R]
variable {S : Type*} [SetLike S F] [AddSubgroupClass S F]

/-- The dilated character `x ↦ ψ(b·x)` restricted to the subgroup `s`, as an additive
character of `↥s`. -/
def dilatedRestrict (ψ : AddChar F R) (b : F) (s : S) : AddChar s R :=
  (ψ.mulShift b).compAddMonoidHom (AddSubgroupClass.subtype s)

@[simp] lemma dilatedRestrict_apply (ψ : AddChar F R) (b : F) (s : S) (x : s) :
    dilatedRestrict ψ b s x = ψ (b * (x : F)) := rfl

/-- The dilated restriction is trivial iff `ψ(b·x) = 1` for all `x ∈ s`. -/
lemma dilatedRestrict_eq_one_iff (ψ : AddChar F R) (b : F) (s : S) :
    dilatedRestrict ψ b s = 1 ↔ ∀ x ∈ s, ψ (b * x) = 1 := by
  constructor
  · intro h x hx
    have := DFunLike.congr_fun h (⟨x, hx⟩ : s)
    simpa using this
  · intro h
    ext x
    simpa using h x x.2

/-- **`M(S)` collapse, every direction at once.**  For an additive subgroup (in particular
an `F₂`-subspace) `s` of a ring `F` and ANY dilation direction `b`, the dilated character
sum `η_b(s) = ∑_{x∈s} ψ(b·x)` is `|s|` or `0`.  The additive-domain analogue of the
far-direction spectrum `{η_b(μ_n)}_b` — whose maximum `M` is the multiplicative
Johnson→capacity wall — is the trivial two-point set. -/
theorem dilated_sum_dichotomy [IsDomain R] (ψ : AddChar F R) (b : F) (s : S) [Fintype s] :
    ∑ x : s, ψ (b * (x : F)) = (Fintype.card s : R) ∨ ∑ x : s, ψ (b * (x : F)) = 0 := by
  by_cases h : dilatedRestrict ψ b s = 1
  · exact Or.inl (AddChar.sum_eq_card_of_eq_one h)
  · exact Or.inr (AddChar.sum_eq_zero_of_ne_one h)

/-- The **annihilator / dual-direction subgroup** `s^⊥ = {b | x ↦ ψ(b·x) trivial on s}`,
as an `AddSubgroup` of the ambient ring.  Under the canonical trace character of `F_{2^k}`
this is the trace-dual `F₂`-subspace.  This coset geometry — not any character-sum
magnitude — is where the far-direction analysis of additive-RS domains relocates. -/
def dualDirections {M : Type*} [Monoid M] (s : S) (ψ : AddChar F M) : AddSubgroup F where
  carrier := {b : F | ∀ x ∈ s, ψ (b * x) = 1}
  zero_mem' := fun x _ => by rw [zero_mul, AddChar.map_zero_eq_one]
  add_mem' := fun {a b} ha hb x hx => by
    rw [add_mul, AddChar.map_add_eq_mul, ha x hx, hb x hx, one_mul]
  neg_mem' := fun {a} ha x hx => by
    have key : ψ (-a * x) * ψ (a * x) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    rwa [ha x hx, mul_one] at key

@[simp] lemma mem_dualDirections {M : Type*} [Monoid M] {s : S} {ψ : AddChar F M} {b : F} :
    b ∈ dualDirections s ψ ↔ ∀ x ∈ s, ψ (b * x) = 1 :=
  Iff.rfl

/-- **Exact spike localization (the relocated hardness, stated precisely).**  Over a
characteristic-zero domain target (e.g. `ℂ`), the dilated sum attains the value `|s|`
EXACTLY on the annihilator `s^⊥ = dualDirections s ψ`; everywhere else it is `0`
(`dilated_sum_dichotomy`).  So the entire far-direction content of an additive evaluation
domain is the indicator of `s^⊥`: what remains open for additive-RS proximity is the coset
geometry of `s^⊥` across the NTT subspace flag — a combinatorial question NOT settled here. -/
theorem dilated_sum_eq_card_iff_mem_dualDirections [IsDomain R] [CharZero R]
    (ψ : AddChar F R) (b : F) (s : S) [Fintype s] :
    ∑ x : s, ψ (b * (x : F)) = (Fintype.card s : R) ↔ b ∈ dualDirections s ψ := by
  haveI : Nonempty s := ⟨⟨0, zero_mem s⟩⟩
  by_cases hb : b ∈ dualDirections s ψ
  · simp only [hb, iff_true]
    exact AddChar.sum_eq_card_of_eq_one ((dilatedRestrict_eq_one_iff ψ b s).2 hb)
  · simp only [hb, iff_false]
    have hne : dilatedRestrict ψ b s ≠ 1 := fun h1 =>
      hb ((dilatedRestrict_eq_one_iff ψ b s).1 h1)
    have hz : ∑ x : s, ψ (b * (x : F)) = 0 := AddChar.sum_eq_zero_of_ne_one hne
    rw [hz]
    exact fun hc => Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := s)) hc.symm

/-- Contrapositive packaging: off the annihilator `s^⊥`, the dilated sum vanishes
identically — there is no intermediate scale for ANY direction. -/
theorem dilated_sum_eq_zero_of_not_mem_dualDirections [IsDomain R] (ψ : AddChar F R)
    (b : F) (s : S) [Fintype s] (hb : b ∉ dualDirections s ψ) :
    ∑ x : s, ψ (b * (x : F)) = 0 :=
  AddChar.sum_eq_zero_of_ne_one fun h1 => hb ((dilatedRestrict_eq_one_iff ψ b s).1 h1)

/-- The `AddSubgroup` instantiation of the dilated dichotomy. -/
theorem addSubgroup_dilated_sum_dichotomy [IsDomain R] (ψ : AddChar F R) (b : F)
    (s : AddSubgroup F) [Fintype s] :
    ∑ x : s, ψ (b * (x : F)) = (Fintype.card s : R) ∨ ∑ x : s, ψ (b * (x : F)) = 0 :=
  dilated_sum_dichotomy ψ b s

/-- The Binius instantiation shape: the dilated dichotomy for a **linear subspace**
`V : Submodule K F` (take `K = ZMod 2`, `F = F_{2^k}`, `R = ℂ`, `ψ = trace character`:
every far-direction "eigenvalue" of an additive-NTT evaluation domain is `0` or `|V|`). -/
theorem submodule_dilated_sum_dichotomy [IsDomain R] {K : Type*} [Ring K] [Module K F]
    (ψ : AddChar F R) (b : F) (V : Submodule K F) [Fintype V] :
    ∑ x : V, ψ (b * (x : F)) = (Fintype.card V : R) ∨ ∑ x : V, ψ (b * (x : F)) = 0 :=
  dilated_sum_dichotomy ψ b V

end Dilated

end ArkLib.ProximityGap.AdditiveDomainDissolution

-- Honesty contract: every claim above must be axiom-clean
-- (expected: subset of [propext, Classical.choice, Quot.sound], 0 sorryAx).
#print axioms ArkLib.ProximityGap.AdditiveDomainDissolution.dilated_sum_dichotomy
#print axioms ArkLib.ProximityGap.AdditiveDomainDissolution.dualDirections
#print axioms ArkLib.ProximityGap.AdditiveDomainDissolution.mem_dualDirections
#print axioms ArkLib.ProximityGap.AdditiveDomainDissolution.dilated_sum_eq_card_iff_mem_dualDirections
#print axioms ArkLib.ProximityGap.AdditiveDomainDissolution.dilated_sum_eq_zero_of_not_mem_dualDirections
#print axioms ArkLib.ProximityGap.AdditiveDomainDissolution.addSubgroup_dilated_sum_dichotomy
#print axioms ArkLib.ProximityGap.AdditiveDomainDissolution.submodule_dilated_sum_dichotomy

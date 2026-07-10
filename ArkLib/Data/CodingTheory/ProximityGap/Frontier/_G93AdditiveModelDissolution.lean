/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466, lane G93)
-/
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Complex.Basic

/-!
# G93: the additive-model production theorem — exact index count, double annihilator,
# coset faithfulness, and the production-shaped sup-norm closure (#466, dossier §6 Tier-3)

**Context.** The production wall of the Proximity Prize (#334/#466) is the sup-norm bound
`M(μ_n) = max_{b≠0} |Σ_{x∈μ_n} e_p(bx)| ≤ C·√(n·log(p/n))` for the smooth
multiplicative
subgroup `μ_n ⊂ F_p^×` — open, ON-BGK.  The dossier's Tier-3 "function-field model theorem"
lane asks for the exact production-shaped statement proved *in a model* where square-root
cancellation is unconditional.  `_FunctionFieldModelSubfieldDegeneracy.lean` (lane W4) showed
the multiplicative `F_q[t]` transplant is degenerate or verbatim-open, and
`_AdditiveDomainDissolution{,Dual}.lean` (lane L5) proved the two-branch spectrum
`η_b(S) ∈ {0, |S|}` for additive (Binius / additive-NTT) domains `S`, localizing the spikes
on the annihilator `S^⊥`.  **This file completes the lane with the four statements those
files did not prove:**

1. **Exact spike count / index law** (`card_annihilator_mul_card`, `card_annihilator`):
   for a *primitive* character `ψ` on a finite commutative ring `F` and any additive
   subgroup (`F₂`-subspace) `s`, `|s^⊥| · |s| = |F|` exactly — so the spike set has exactly
   index-many elements, `|s^⊥| = |F|/|s| = m` (the model analogue of the prize index
   `m = (p−1)/n = 2^128`).  The L5 kb note recorded this only as an *unformalized Parseval
   cross-check*; here it is a theorem, proved by double-counting `Σ_b η_b = |F|` against the
   two-branch spectrum (`AddChar.sum_mulShift` + orthogonality — **no Weil input anywhere**).
2. **Double annihilator** (`annihilator_annihilator`): `s^⊥⊥ = s` for `ψ` primitive — by the
   index law applied twice plus `s ≤ s^⊥⊥`.  This is the biduality that makes "the hardness
   relocates to `S^⊥`" a *lossless* relocation rather than a slogan.
3. **Coset faithfulness — the relocation, made exact**
   (`sub_mem_iff_annihilator_phase_eq`): `y − y' ∈ S ⟺ ∀ b ∈ S^⊥, ψ(by) = ψ(by')`.
   Combined with coset blindness (L5: every coset sum vanishes off `S^⊥`), this pins
   *exactly* what ambient character analysis retains about an additive domain: the
   `S^⊥`-phase vector of a point is a **complete invariant of its `S`-coset**, and nothing
   off `S^⊥` carries any information.  The far-direction analysis of additive-RS proximity
   therefore lives on the coset geometry of `S^⊥` — no more and no less.
4. **The production-shaped model theorem** (`model_production_bound`, with exact form
   `model_offSpike_norm_eq_zero` and the necessity theorem
   `naive_model_sup_attains_card`): on the corrected frequency set (all `b ∉ S^⊥`),
   `‖Σ_{x∈S} ψ(bx)‖ ≤ √(|S| · log(|F|/|S|))` holds **unconditionally, C = 1** — indeed
   the left side is identically `0`, so the Johnson→capacity character-sum gap *vanishes* in
   the additive model.  And the excision of `S^⊥` is *necessary*: for any proper `S` the
   naive sup over all `b ≠ 0` equals `|S|` exactly (a nonzero spike always exists, since
   `|S^⊥| = |F|/|S| ≥ 2`) — the naive transplant of the prize law is maximally FALSE.

## Honest scope (do NOT over-claim)

* **This is a model theorem, NOT the `F_p` prize.**  Nothing here constrains `M(μ_n)`,
  `E(μ_n)`, or δ* for multiplicative smooth domains; the open core (#466 §2) is untouched.
  The value is cartographic: the exact production-shaped statement — sup-norm, `√(n log m)`
  scale, worst-case over a frequency set — is *provable, elementarily and unconditionally*,
  the moment the domain is an additive subgroup, because the far-direction spectrum is
  `|S|·1_{S^⊥}`.  What `F_p` lacks is precisely this: `μ_n` is multiplicatively closed but
  additively unstructured, so its Fourier transform has full support at unknown scale.  The
  feature blocking the transfer is not the *thinness* (the model reproduces the exact prize
  index `m`) but the *additive closure* of the domain.
* **The relocation caveat, quantified.**  The gap does not disappear — it relocates:
  theorems 1–3 show the surviving object is the coset geometry of the exactly-index-sized
  dual `S^⊥` (for Binius: the trace-dual flag structure).  Agreement on proper subsets of
  `S` (the actual proximity object) is invisible to ambient characters, and the
  beyond-Johnson MCA question for additive-NTT RS remains **open**.  A tool losing its grip
  is not the problem disappearing.
* Part 0 re-derives the L5 two-branch spectrum locally (self-contained, Mathlib-only
  imports) because the companion frontier files are not part of the built substrate; the
  new mathematics is Parts 1–4.  Companions: `_AdditiveDomainDissolution.lean`,
  `_AdditiveDomainDissolutionDual.lean`, `_FunctionFieldModelSubfieldDegeneracy.lean`;
  kb note `docs/kb/deltastar-466-additive-domain-dissolution.md`.
* `isPrizeClosure := false`.  Everything below is axiom-clean
  (`propext, Classical.choice, Quot.sound`; no `sorry`, no `axiom`, no `native_decide`).
-/

namespace ArkLib.ProximityGap.G93AdditiveModelDissolution

open Finset

variable {F : Type*} [CommRing F]

/-! ## Part 0: the annihilator and the two-branch spectrum (self-contained substrate)

The dual-direction subgroup `s^⊥` and the dichotomy `η_b(s) ∈ {0, |s|}` — re-derived
locally from `AddChar` orthogonality (cf. lane L5); everything downstream consumes these. -/

section Annihilator

variable {M : Type*} [Monoid M]

/-- The **annihilator** `s^⊥ = {b | x ↦ ψ(b·x) is trivial on s}` of a `SetLike` domain
`s ⊆ F` with respect to an additive character `ψ`, as an `AddSubgroup` of the ambient ring.
For the trace character of `F_{2^k}` and an `F₂`-subspace `s`, this is the trace-dual
subspace. -/
def annihilator {S : Type*} [SetLike S F] (s : S) (ψ : AddChar F M) : AddSubgroup F where
  carrier := {b : F | ∀ x ∈ s, ψ (b * x) = 1}
  zero_mem' := fun x _ => by rw [zero_mul, AddChar.map_zero_eq_one]
  add_mem' := fun {a b} ha hb x hx => by
    rw [add_mul, AddChar.map_add_eq_mul, ha x hx, hb x hx, one_mul]
  neg_mem' := fun {a} ha x hx => by
    have key : ψ (-a * x) * ψ (a * x) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    rwa [ha x hx, mul_one] at key

@[simp] lemma mem_annihilator {S : Type*} [SetLike S F] {s : S} {ψ : AddChar F M} {b : F} :
    b ∈ annihilator s ψ ↔ ∀ x ∈ s, ψ (b * x) = 1 :=
  Iff.rfl

end Annihilator

section Dichotomy

variable {R : Type*} [CommRing R]
variable {S : Type*} [SetLike S F] [AddSubgroupClass S F]

omit [AddSubgroupClass S F] in
/-- Spike branch: on the annihilator the character sum is exactly `|s|`. -/
theorem charSum_eq_card_of_mem_annihilator {s : S} [Fintype s] {ψ : AddChar F R} {b : F}
    (hb : b ∈ annihilator s ψ) :
    ∑ x : s, ψ (b * (x : F)) = (Fintype.card s : R) := by
  have h1 : ∀ x : s, ψ (b * (x : F)) = 1 := fun x => hb (x : F) x.2
  simp [h1]

/-- Vanishing branch: off the annihilator the character sum is exactly `0`
(orthogonality on the subgroup — the entire "model Weil bound", with `0` in place of
`√`-cancellation). -/
theorem charSum_eq_zero_of_not_mem_annihilator [IsDomain R] {s : S} [Fintype s]
    {ψ : AddChar F R} {b : F} (hb : b ∉ annihilator s ψ) :
    ∑ x : s, ψ (b * (x : F)) = 0 := by
  have hne : (ψ.mulShift b).compAddMonoidHom (AddSubgroupClass.subtype s) ≠ 1 := by
    intro h1
    refine hb fun x hx => ?_
    have := DFunLike.congr_fun h1 (⟨x, hx⟩ : s)
    simpa using this
  simpa using AddChar.sum_eq_zero_of_ne_one hne

/-- The two-branch spectrum in indicator form: `η_b(s) = |s| · 1_{s^⊥}(b)`. -/
theorem charSum_eq_ite [IsDomain R] {s : S} [Fintype s] {ψ : AddChar F R} (b : F)
    [Decidable (b ∈ annihilator s ψ)] :
    ∑ x : s, ψ (b * (x : F))
      = if b ∈ annihilator s ψ then (Fintype.card s : R) else 0 := by
  split_ifs with h
  · exact charSum_eq_card_of_mem_annihilator h
  · exact charSum_eq_zero_of_not_mem_annihilator h

end Dichotomy

/-! ## Part 1: the exact spike count — `|s^⊥| · |s| = |F|`

Double-counting `Σ_{b∈F} η_b(s)`: column-wise it is `|F|` (only `x = 0` survives, by
`AddChar.sum_mulShift` for a primitive `ψ`); row-wise it is `|s^⊥|·|s|` (two-branch
spectrum).  The spike set is exactly index-sized: the model reproduces the prize index
`m = |F|/|s|` as the cardinality of the relocated hardness locus. -/

section Count

variable [Fintype F] [DecidableEq F]
variable {R : Type*} [CommRing R] [IsDomain R]
variable {S : Type*} [SetLike S F] [AddSubgroupClass S F]

/-- Column count: for primitive `ψ`, `Σ_{b∈F} η_b(s) = |F|` (no conjugation needed —
first moment, not Parseval). -/
theorem sum_charSum (ψ : AddChar F R) (hψ : ψ.IsPrimitive) (s : S) [Fintype s] :
    ∑ b : F, ∑ x : s, ψ (b * (x : F)) = (Fintype.card F : R) := by
  classical
  rw [Finset.sum_comm]
  calc ∑ x : s, ∑ b : F, ψ (b * (x : F))
      = ∑ x : s, ((if (x : F) = 0 then Fintype.card F else 0 : ℕ) : R) :=
        Finset.sum_congr rfl fun x _ => AddChar.sum_mulShift (x : F) hψ
    _ = (Fintype.card F : R) := by
        rw [Fintype.sum_eq_single (0 : s) (fun x hx0 => by
          rw [if_neg fun hc => hx0 (ZeroMemClass.coe_eq_zero.mp hc), Nat.cast_zero])]
        simp

/-- **The exact spike count (index law).**  For a primitive character `ψ` on a finite
commutative ring `F` and any additive subgroup / `F₂`-subspace `s`:
`|s^⊥| · |s| = |F|` — the spike set of the far-direction spectrum has exactly index-many
elements.  Purely elementary (orthogonality + `sum_mulShift`); the L5 lane recorded this
only as an unformalized Parseval cross-check. -/
theorem card_annihilator_mul_card [CharZero R] (ψ : AddChar F R) (hψ : ψ.IsPrimitive)
    (s : S) [Fintype s] :
    Nat.card (annihilator s ψ) * Nat.card s = Nat.card F := by
  classical
  have hII : ∑ b : F, ∑ x : s, ψ (b * (x : F))
      = ((Nat.card (annihilator s ψ) : R) * (Nat.card s : R)) := by
    calc ∑ b : F, ∑ x : s, ψ (b * (x : F))
        = ∑ b : F, if b ∈ annihilator s ψ then (Fintype.card s : R) else 0 :=
          Finset.sum_congr rfl fun b _ => charSum_eq_ite b
      _ = ((Finset.univ.filter (fun b : F => b ∈ annihilator s ψ)).card : R)
            * (Fintype.card s : R) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
            nsmul_eq_mul]
      _ = ((Nat.card (annihilator s ψ) : R) * (Nat.card s : R)) := by
          congr 2
          · rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
          · rw [Nat.card_eq_fintype_card]
  have h := (sum_charSum ψ hψ s).symm.trans hII
  have hnat : ((Nat.card F : ℕ) : R)
      = ((Nat.card (annihilator s ψ) * Nat.card s : ℕ) : R) := by
    rw [Nat.card_eq_fintype_card (α := F)]
    push_cast
    exact h
  exact_mod_cast hnat.symm

/-- The spike set is exactly the **index**: `|s^⊥| = |F| / |s| = m`, the model analogue of
the prize index `m = (p−1)/n`. -/
theorem card_annihilator [CharZero R] (ψ : AddChar F R) (hψ : ψ.IsPrimitive)
    (s : S) [Fintype s] :
    Nat.card (annihilator s ψ) = Nat.card F / Nat.card s := by
  haveI : Nonempty s := ⟨⟨0, zero_mem s⟩⟩
  have hpos : 0 < Nat.card s := Nat.card_pos
  have h : Nat.card F = Nat.card s * Nat.card (annihilator s ψ) := by
    rw [mul_comm]
    exact (card_annihilator_mul_card ψ hψ s).symm
  exact (Nat.div_eq_of_eq_mul_right hpos h).symm

end Count

/-! ## Part 2: the double annihilator — the relocation is lossless -/

section Biduality

variable {M : Type*} [Monoid M]

/-- `S ≤ S^⊥⊥`, for any character (uses only commutativity of `F`). -/
theorem le_annihilator_annihilator (ψ : AddChar F M) (S' : AddSubgroup F) :
    S' ≤ annihilator (annihilator S' ψ) ψ := fun x hx b hb => by
  rw [mul_comm]
  exact hb x hx

end Biduality

section BidualityCount

variable [Fintype F] [DecidableEq F]
variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-- **Double annihilator: `S^⊥⊥ = S`** for a primitive character on a finite commutative
ring.  The index law applied twice forces `|S^⊥⊥| = |S|`, and `S ≤ S^⊥⊥` upgrades to
equality.  Consequence: passing from `S` to the coset geometry of `S^⊥` loses no
information — the relocation of the additive-domain hardness is exact, not an upper
bound. -/
theorem annihilator_annihilator (ψ : AddChar F R) (hψ : ψ.IsPrimitive)
    (S' : AddSubgroup F) [Fintype S'] :
    annihilator (annihilator S' ψ) ψ = S' := by
  classical
  haveI : Fintype (annihilator S' ψ) := Fintype.ofFinite _
  have h1 := card_annihilator_mul_card ψ hψ S'
  have h2 := card_annihilator_mul_card ψ hψ (annihilator S' ψ)
  have hpos : 0 < Nat.card (annihilator S' ψ) := Nat.card_pos
  have hEq : Nat.card (annihilator (annihilator S' ψ) ψ) = Nat.card S' := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h2, mul_comm]
    exact h1.symm
  exact (AddSubgroup.eq_of_le_of_card_ge (le_annihilator_annihilator ψ S') hEq.le).symm

/-! ## Part 3: coset faithfulness — where the hardness relocates, exactly -/

/-- **Coset faithfulness (the relocation theorem).**  For a primitive character `ψ`:
`y − y' ∈ S ⟺ the S^⊥-phase vectors of y and y' agree`.  Together with coset blindness
(L5: all coset sums vanish off `S^⊥`), this is the exact accounting of the ambient
character content of an additive domain: the phase vector `(ψ(b·y))_{b∈S^⊥}` is a
COMPLETE invariant of the `S`-coset of `y`, and directions off `S^⊥` carry nothing.  Any
far-direction analysis of additive-RS proximity is therefore *equivalent* to a question
about the coset geometry of the index-sized dual `S^⊥` — which remains OPEN; nothing here
bounds it. -/
theorem sub_mem_iff_annihilator_phase_eq (ψ : AddChar F R) (hψ : ψ.IsPrimitive)
    (S' : AddSubgroup F) [Fintype S'] (y y' : F) :
    y - y' ∈ S' ↔ ∀ b ∈ annihilator S' ψ, ψ (b * y) = ψ (b * y') := by
  constructor
  · intro h b hb
    have h1 : ψ (b * (y - y')) = 1 := hb _ h
    have hy : b * y = b * y' + b * (y - y') := by ring
    rw [hy, AddChar.map_add_eq_mul, h1, mul_one]
  · intro h
    have hmem : y - y' ∈ annihilator (annihilator S' ψ) ψ := by
      intro b hb
      have hu : IsUnit (ψ (b * y')) := ψ.val_isUnit _
      have hkey : ψ (b * (y - y')) * ψ (b * y') = 1 * ψ (b * y') := by
        rw [← AddChar.map_add_eq_mul, one_mul]
        have hsplit : b * (y - y') + b * y' = b * y := by ring
        rw [hsplit]
        exact h b hb
      have h1 : ψ (b * (y - y')) = 1 := hu.mul_right_cancel hkey
      rwa [mul_comm] at h1
    rwa [annihilator_annihilator ψ hψ S'] at hmem

/-! ## Part 4: the production-shaped model theorem, and why the excision is necessary -/

variable {S : Type*} [SetLike S F] [AddSubgroupClass S F]

/-- **Necessity of excising `S^⊥` (the honest flip side).**  For any PROPER additive
subgroup `s` and primitive `ψ`, some NONZERO direction spikes: `∃ b ≠ 0` with
`η_b(s) = |s|` exactly.  So the naive transplant of the prize law
(`max_{b≠0} |η_b| = o(|s|)`) is maximally FALSE on additive domains — the correct model
frequency set is `F ∖ S^⊥`, and by the index law the excised set has exactly `|F|/|s|`
elements.  (Additive-subgroup counterpart of the W4 subfield countermodel.) -/
theorem exists_nonzero_spike (ψ : AddChar F R) (hψ : ψ.IsPrimitive) (s : S) [Fintype s]
    (hproper : Nat.card s < Nat.card F) :
    ∃ b : F, b ≠ 0 ∧ ∑ x : s, ψ (b * (x : F)) = (Fintype.card s : R) := by
  classical
  have h1 := card_annihilator_mul_card ψ hψ s
  have hne : ∃ b ∈ annihilator s ψ, b ≠ 0 := by
    by_contra hall
    push Not at hall
    have hbot : annihilator s ψ = ⊥ := (AddSubgroup.eq_bot_iff_forall _).2 hall
    rw [hbot, AddSubgroup.card_bot, one_mul] at h1
    omega
  obtain ⟨b, hbmem, hb0⟩ := hne
  exact ⟨b, hb0, charSum_eq_card_of_mem_annihilator hbmem⟩

end BidualityCount

section Model

variable {S : Type*} [SetLike S F] [AddSubgroupClass S F]

/-- Exact form of the model theorem: off the annihilator, the far-direction character sum
vanishes in norm — not merely `≲ √(n log m)` but `= 0`. -/
theorem model_offSpike_norm_eq_zero (ψ : AddChar F ℂ) (s : S) [Fintype s] {b : F}
    (hb : b ∉ annihilator s ψ) :
    ‖∑ x : s, ψ (b * (x : F))‖ = 0 := by
  rw [charSum_eq_zero_of_not_mem_annihilator hb, norm_zero]

/-- **THE PRODUCTION-SHAPED MODEL THEOREM.**  In the additive model — `s` an additive
subgroup / `F₂`-subspace of a finite commutative ring `F` (Binius: `F = F_{2^k}`,
`ψ` = trace character), frequency set corrected to exclude the annihilator — the exact
production-shaped sup-norm law holds **unconditionally, with constant `C = 1`**:

`‖Σ_{x∈s} ψ(b·x)‖ ≤ √(|s| · log(|F|/|s|))`  for every `b ∉ s^⊥`,

the verbatim shape of the open prize core `M(μ_n) ≤ C·√(n·log(p/n))` (#466 §2), with the
model index `m = |F|/|s|` in place of `p/n`.  The proof consumes NO Weil bound and no
analysis at all: the left side is identically zero (`model_offSpike_norm_eq_zero`) — in
the additive model the Johnson→capacity character-sum gap does not merely close to
√-scale, it VANISHES.  Honest reading: this pins the blocking feature of `F_p` as the
additive non-closure of `μ_n` (not its thinness — the model index is unconstrained), and
by `naive_model_sup_attains_card` the excision of the index-sized `s^⊥` is necessary,
which is exactly where the model hardness relocates. -/
theorem model_production_bound (ψ : AddChar F ℂ) (s : S) [Fintype s] {b : F}
    (hb : b ∉ annihilator s ψ) :
    ‖∑ x : s, ψ (b * (x : F))‖
      ≤ Real.sqrt ((Nat.card s : ℝ) * Real.log ((Nat.card F : ℝ) / (Nat.card s : ℝ))) := by
  rw [model_offSpike_norm_eq_zero ψ s hb]
  exact Real.sqrt_nonneg _

/-- The naive model sup (over ALL `b ≠ 0`) attains `|s|` on every proper subgroup:
without the `s^⊥`-excision the production-shaped law is false at the worst possible
scale.  Norm packaging of `exists_nonzero_spike` over `ℂ`. -/
theorem naive_model_sup_attains_card [Fintype F] [DecidableEq F] (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (s : S) [Fintype s] (hproper : Nat.card s < Nat.card F) :
    ∃ b : F, b ≠ 0 ∧ ‖∑ x : s, ψ (b * (x : F))‖ = (Fintype.card s : ℝ) := by
  obtain ⟨b, hb0, hb⟩ := exists_nonzero_spike (R := ℂ) ψ hψ s hproper
  refine ⟨b, hb0, ?_⟩
  rw [hb]
  simp

end Model

/-! ## Part 5: Binius / `F₂`-subspace instantiations

The main theorems are stated for any `SetLike` + `AddSubgroupClass`, so `Submodule K F`
(Binius: `K = ZMod 2`, `F = F_{2^k}`) instantiates directly; the `AddSubgroup`-specific
statements (biduality, coset faithfulness) transfer through `Submodule.toAddSubgroup`. -/

section Binius

variable [Fintype F] [DecidableEq F]
variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
variable {K : Type*} [CommRing K] [Module K F]

omit [Fintype F] [DecidableEq F] in
/-- The annihilator does not see the `K`-linear structure: computing it on
`V.toAddSubgroup` or on `V` is the same subgroup. -/
lemma annihilator_toAddSubgroup {M : Type*} [Monoid M] (ψ : AddChar F M)
    (V : Submodule K F) :
    annihilator V.toAddSubgroup ψ = annihilator V ψ := by
  ext b
  exact ⟨fun h x hx => h x hx, fun h x hx => h x hx⟩

/-- Binius index law: `|V^⊥| · |V| = |F|` for an `F₂`-subspace evaluation domain. -/
theorem binius_card_annihilator_mul_card (ψ : AddChar F R) (hψ : ψ.IsPrimitive)
    (V : Submodule K F) [Fintype V] :
    Nat.card (annihilator V ψ) * Nat.card V = Nat.card F :=
  card_annihilator_mul_card ψ hψ V

/-- Binius double annihilator: `V^⊥⊥ = V` (as additive subgroups). -/
theorem binius_annihilator_annihilator (ψ : AddChar F R) (hψ : ψ.IsPrimitive)
    (V : Submodule K F) [Fintype V] :
    annihilator (annihilator V ψ) ψ = V.toAddSubgroup := by
  haveI : Fintype V.toAddSubgroup := Fintype.ofFinite _
  rw [← annihilator_toAddSubgroup ψ V]
  exact annihilator_annihilator ψ hψ V.toAddSubgroup

/-- Binius coset faithfulness: membership of `y − y'` in the subspace is equivalent to
agreement of the `V^⊥`-phase vectors. -/
theorem binius_sub_mem_iff_phase_eq (ψ : AddChar F R) (hψ : ψ.IsPrimitive)
    (V : Submodule K F) [Fintype V] (y y' : F) :
    y - y' ∈ V ↔ ∀ b ∈ annihilator V ψ, ψ (b * y) = ψ (b * y') := by
  haveI : Fintype V.toAddSubgroup := Fintype.ofFinite _
  have h := sub_mem_iff_annihilator_phase_eq ψ hψ V.toAddSubgroup y y'
  rwa [annihilator_toAddSubgroup ψ V, Submodule.mem_toAddSubgroup] at h

end Binius

/-! ## Part 6: the finite-field form (primitivity for free) -/

section FieldModel

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq Fq]
variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
variable {S : Type*} [SetLike S Fq] [AddSubgroupClass S Fq]

/-- Over a finite FIELD every nontrivial character is primitive, so the index law needs
only `ψ ≠ 1` — the natural hypothesis for the `F_{2^k}` trace character. -/
theorem field_card_annihilator_mul_card (ψ : AddChar Fq R) (hψ : ψ ≠ 1)
    (s : S) [Fintype s] :
    Nat.card (annihilator s ψ) * Nat.card s = Nat.card Fq :=
  card_annihilator_mul_card ψ (AddChar.IsPrimitive.of_ne_one hψ) s

/-- Field form of the exact index count: `|s^⊥| = |F_q| / |s|`. -/
theorem field_card_annihilator (ψ : AddChar Fq R) (hψ : ψ ≠ 1) (s : S) [Fintype s] :
    Nat.card (annihilator s ψ) = Nat.card Fq / Nat.card s :=
  card_annihilator ψ (AddChar.IsPrimitive.of_ne_one hψ) s

end FieldModel

end ArkLib.ProximityGap.G93AdditiveModelDissolution

/-! ## Axiom audit

Honesty contract: every declaration below must depend on axioms that are a subset of
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no custom axioms, no
`native_decide`. -/

#print axioms ArkLib.ProximityGap.G93AdditiveModelDissolution.annihilator
#print axioms ArkLib.ProximityGap.G93AdditiveModelDissolution.charSum_eq_card_of_mem_annihilator
#print axioms ArkLib.ProximityGap.G93AdditiveModelDissolution.charSum_eq_zero_of_not_mem_annihilator
#print axioms ArkLib.ProximityGap.G93AdditiveModelDissolution.charSum_eq_ite
#print axioms ArkLib.ProximityGap.G93AdditiveModelDissolution.sum_charSum
#print axioms ArkLib.ProximityGap.G93AdditiveModelDissolution.card_annihilator_mul_card
#print axioms ArkLib.ProximityGap.G93AdditiveModelDissolution.card_annihilator
#print axioms ArkLib.ProximityGap.G93AdditiveModelDissolution.le_annihilator_annihilator
#print axioms ArkLib.ProximityGap.G93AdditiveModelDissolution.annihilator_annihilator
#print axioms ArkLib.ProximityGap.G93AdditiveModelDissolution.sub_mem_iff_annihilator_phase_eq
#print axioms ArkLib.ProximityGap.G93AdditiveModelDissolution.exists_nonzero_spike
#print axioms ArkLib.ProximityGap.G93AdditiveModelDissolution.model_offSpike_norm_eq_zero
#print axioms ArkLib.ProximityGap.G93AdditiveModelDissolution.model_production_bound
#print axioms ArkLib.ProximityGap.G93AdditiveModelDissolution.naive_model_sup_attains_card
#print axioms ArkLib.ProximityGap.G93AdditiveModelDissolution.annihilator_toAddSubgroup
#print axioms ArkLib.ProximityGap.G93AdditiveModelDissolution.binius_card_annihilator_mul_card
#print axioms ArkLib.ProximityGap.G93AdditiveModelDissolution.binius_annihilator_annihilator
#print axioms ArkLib.ProximityGap.G93AdditiveModelDissolution.binius_sub_mem_iff_phase_eq
#print axioms ArkLib.ProximityGap.G93AdditiveModelDissolution.field_card_annihilator_mul_card
#print axioms ArkLib.ProximityGap.G93AdditiveModelDissolution.field_card_annihilator

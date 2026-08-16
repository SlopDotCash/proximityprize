/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.CensusLowerBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapeRateHalfBracket

/-!
# G87: mcaEvent → syndrome-functional bridge — the G86 rank-collapse dichotomy applies
  to the concrete rate-half gate wall hypothesis (#466 / #507)

`Frontier/_G86RankCollapseDichotomy.lean` proved the abstract planting dichotomy: any
family of `r` witnesses, each contributing `m` constraint functionals annihilating a
common nonzero syndrome vector, satisfies EITHER `r·m + 1 ≤ dim V` OR its functionals
carry an explicit nontrivial linear dependence (syzygy).  Its docstring honestly flagged
the gap: *"the bridge from this abstract model to the concrete `mcaEvent` count is the
probe's exact reduction, not a Lean theorem."*  This file closes that gap.

## What is constructed

Fix a linear code `C : Submodule F (ι → F)` with `n = |ι|`, `k = dim C`, and an
agreement threshold `t`.  For a stack `(u₀, u₁)` and a scalar `γ` that is *bad via
`(S, c)`* (`|S| = t`, `c ∈ C`, `c` agrees with the line `u₀ + γ·u₁` on `S`):

* **Syndrome pair space** (`SyndromePair`): `V = ((ι→F)⧸C) × ((ι→F)⧸C)`, of dimension
  exactly `2(n−k)` (`finrank_syndromePair`).  This is the abstract-presentation form of
  the probe's `F^{2(n−k)}`: the dichotomy needs ONLY the kernel (= codeword-pair space)
  and the dimension count, NOT the Vandermonde structure of a concrete GRS parity-check
  matrix.  We therefore work with the canonical quotient presentation rather than
  explicit Vandermonde parity rows — this is the "abstract-H" simplification flagged as
  fully honest in the task brief: any parity-check presentation `H` with
  `ker H = C ⊕ C` is linearly isomorphic to this quotient, so nothing is lost.
* **Witness functionals** (`exists_rowFunctionals`): each witness `(S, c)` yields
  `t − k` linearly independent functionals `ℓⱼ` on `F^ι` that (a) annihilate `C` and
  (b) kill the line `u₀ + γ·u₁` — the abstract form of the `t − k` GRS parity rows on
  `S` built by `make_planted` in
  `scripts/probes/probe_rate_half_predecessor_count_largefield.py`.  They are obtained
  as duals of the quotient `(S → F) ⧸ res_S(C)`, whose dimension is `≥ t − k` because
  `dim res_S(C) ≤ k`.
* **Bridge functionals** (`exists_bridge_functionals`): folding the `γᵢ`-weights in,
  each of `r` bad scalars contributes `t − k` functionals
  `φ(i,j) = ℓ̄ᵢⱼ ∘ fst + γᵢ · (ℓ̄ᵢⱼ ∘ snd)` on the syndrome pair space, all of which
  vanish on the stack's syndrome pair, with each per-witness block `j ↦ φ(i,j)`
  linearly independent (so the construction is not vacuous).

## Main results

* `syndrome_dichotomy` — **the bridge theorem**: for any stack that is not a codeword
  pair and any `r` scalars each bad-via-witness at threshold `t`, the constructed
  functionals are `Plantable` in G86's sense (the syndrome pair is the annihilated
  nonzero vector), hence G86's dichotomy applies verbatim: EITHER
  `r·(t−k) + 1 ≤ 2(n−k)`, OR the concrete witness functionals admit an explicit
  nontrivial syzygy.
* `mcaEvent_witness` / `mcaEvent_not_both_mem` — witness extraction: the ABF26
  `mcaEvent` at radius `δ` yields a bad-via-`(S,c)` witness at any threshold
  `t ≤ (1−δ)·n` (take any `t`-subset of the event's witness set), and automatically
  rules out the degenerate codeword-pair stack (a codeword pair joint-agrees with
  itself, contradicting the event's `¬ pairJointAgreesOn` clause).
* `wall_syzygy_of_sixtyFour_bad_scalars` — **consumer corollary at the production
  shape** (`n = 2^30`, `k ≤ 2^29`, `t = 2^30 − 31·2^24 + 1`, so `t − k ≥ 2^24 + 1` and
  `2(n−k) ≥ 2^30`): for the first certified prize field and the exact code and radius
  of the gate hypothesis
  `firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count`, ANY stack
  with `≥ 64` bad scalars (each firing `mcaEvent` at the predecessor radius) forces an
  explicit nontrivial syzygy among its witness functionals; equivalently
  (`wall_not_linearIndependent_of_sixtyFour_bad_scalars`) the witness functionals of
  `64` bad scalars can NEVER be linearly independent.  The arithmetic:
  `64·(2^24+1) + 1 = 2^30 + 65 > 2^30` kills the generic disjunct.

## Honest scope

This makes G86 bite on the concrete gate: the wall hypothesis (`≤ 2^30` bad scalars
per stack — budget far above `64`) can now only fail through **syzygy configurations**:
stacks whose bad-scalar witness functionals are forced into a nontrivial linear
dependence, in blocks of at most `63` independent witnesses.  What this file does NOT
do: it does not exclude syzygy configurations (that is the remaining mathematical
content between here and the literal gate hypothesis), it does not bound the *number*
of bad scalars unconditionally, and it uses the code's dimension only through the
one-sided bound `finrank ≤ 2^29` (proved here via the degree-`< 2^29` polynomial
parametrization; the opposite Vandermonde inequality is never needed — a smaller code
only shrinks the generic budget further).  CORE remains OPEN.

Honesty: no `sorry`, no `axiom`, no `native_decide`; `#print axioms` at the bottom.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000


namespace ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge

open Module Submodule
open scoped NNReal

/-! ## G86 core, restated

The abstract dichotomy from `Frontier/_G86RankCollapseDichotomy.lean` (statements
byte-identical up to namespace).  Restated locally because that file landed after the
shared olean cache was last built; the proofs are the same few lines of Mathlib linear
algebra, and `#print axioms` below re-audits them. -/

section G86Core

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {r m : ℕ}

/-- Restatement of `G86RankCollapseDichotomy.Plantable`: some **nonzero** syndrome
vector is annihilated by every constraint functional. -/
def Plantable (φ : Fin r × Fin m → Module.Dual F V) : Prop :=
  ∃ v : V, v ≠ 0 ∧ ∀ p : Fin r × Fin m, φ p v = 0

/-- Restatement of `G86RankCollapseDichotomy.plantable_linearIndependent_cap`. -/
theorem plantable_linearIndependent_cap {φ : Fin r × Fin m → Module.Dual F V}
    (hp : Plantable φ) (h : LinearIndependent F φ) : r * m + 1 ≤ finrank F V := by
  obtain ⟨v, hv, hann⟩ := hp
  set W : Subspace F (Module.Dual F V) := (F ∙ v).dualAnnihilator with hW
  have hmem : ∀ p : Fin r × Fin m, φ p ∈ W := by
    intro p
    rw [hW, Submodule.mem_dualAnnihilator]
    intro w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    simp [hann p]
  set ψ : Fin r × Fin m → W := fun p => ⟨φ p, hmem p⟩ with hψ
  have hψli : LinearIndependent F ψ := by
    refine LinearIndependent.of_comp W.subtype ?_
    have : (W.subtype ∘ ψ) = φ := by funext p; simp [hψ]
    rwa [this]
  have hcard : r * m ≤ finrank F W := by
    have := hψli.fintype_card_le_finrank
    simpa [Fintype.card_prod, Fintype.card_fin] using this
  have hsplit : finrank F (F ∙ v) + finrank F W = finrank F V :=
    Subspace.finrank_add_finrank_dualAnnihilator_eq (F ∙ v)
  have hone : finrank F (F ∙ v) = 1 := finrank_span_singleton hv
  omega

/-- Restatement of `G86RankCollapseDichotomy.plantable_dichotomy`: generic cap OR
explicit syzygy. -/
theorem plantable_dichotomy {φ : Fin r × Fin m → Module.Dual F V} (hp : Plantable φ) :
    r * m + 1 ≤ finrank F V ∨
      ∃ c : Fin r × Fin m → F,
        (∑ p : Fin r × Fin m, c p • φ p = 0) ∧ ∃ p : Fin r × Fin m, c p ≠ 0 := by
  by_cases h : LinearIndependent F φ
  · exact Or.inl (plantable_linearIndependent_cap hp h)
  · exact Or.inr (Fintype.not_linearIndependent_iff.mp h)

end G86Core

/-! ## The concrete syndrome pair space -/

section SyndromeSpace

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The concrete syndrome pair space of a linear code `C ≤ F^ι`: the product of two
copies of the syndrome quotient `F^ι ⧸ C`.  Its dimension is exactly `2(n−k)`; its
"zero" fiber is exactly the codeword-pair space, matching the probe's reduction. -/
abbrev SyndromePair (C : Submodule F (ι → F)) : Type _ :=
  ((ι → F) ⧸ C) × ((ι → F) ⧸ C)

/-- The syndrome pair of a stack `(u₀, u₁)`. -/
def syndromePair (C : Submodule F (ι → F)) (u₀ u₁ : ι → F) : SyndromePair C :=
  (C.mkQ u₀, C.mkQ u₁)

/-- The code dimension is bounded by the block length. -/
theorem finrank_code_le (C : Submodule F (ι → F)) :
    finrank F C ≤ Fintype.card ι := by
  have h := Submodule.finrank_le C
  simpa [Module.finrank_pi] using h

/-- The syndrome pair space has dimension exactly `2(n − k)`. -/
theorem finrank_syndromePair (C : Submodule F (ι → F)) :
    finrank F (SyndromePair C) = 2 * (Fintype.card ι - finrank F C) := by
  have hq : finrank F ((ι → F) ⧸ C) + finrank F C = finrank F (ι → F) :=
    Submodule.finrank_quotient_add_finrank C
  have hpi : finrank F (ι → F) = Fintype.card ι := Module.finrank_pi F
  have hle := finrank_code_le C
  have hprod : finrank F (SyndromePair C) =
      finrank F ((ι → F) ⧸ C) + finrank F ((ι → F) ⧸ C) :=
    Module.finrank_prod
  omega

/-- The syndrome pair of a stack vanishes iff the stack is a codeword pair. -/
theorem syndromePair_eq_zero_iff (C : Submodule F (ι → F)) (u₀ u₁ : ι → F) :
    syndromePair C u₀ u₁ = 0 ↔ u₀ ∈ C ∧ u₁ ∈ C := by
  simp [syndromePair, Prod.ext_iff, Submodule.Quotient.mk_eq_zero]

/-! ## Witness functionals: the `t − k` parity rows of one bad scalar -/

/-- **Functional construction (one witness).**  If a codeword `c ∈ C` agrees with the
line `u₀ + γ·u₁` on a `t`-set `S`, there are `t − k` linearly independent functionals
on `F^ι` that annihilate `C` and kill the line.  These are the abstract GRS parity rows
on `S`: duals of the quotient `(S → F) ⧸ res_S(C)`, which has dimension
`t − dim res_S(C) ≥ t − k`. -/
theorem exists_rowFunctionals (C : Submodule F (ι → F)) {S : Finset ι} {t : ℕ}
    (hS : S.card = t) {u₀ u₁ : ι → F} {γ : F}
    (hagree : ∃ c ∈ C, ∀ x ∈ S, c x = u₀ x + γ * u₁ x) :
    ∃ ℓ : Fin (t - finrank F C) → Module.Dual F (ι → F),
      LinearIndependent F ℓ ∧
      (∀ j, ∀ x ∈ C, ℓ j x = 0) ∧
      (∀ j, ℓ j (u₀ + γ • u₁) = 0) := by
  classical
  obtain ⟨c, hcC, hc⟩ := hagree
  -- restriction to `S`, and the syndrome quotient on `S`
  set res : (ι → F) →ₗ[F] ((↥S : Type _) → F) :=
    LinearMap.funLeft F F (fun s : ↥S => (s : ι)) with hres
  set M : Submodule F ((↥S : Type _) → F) := C.map res with hM
  set π : (ι → F) →ₗ[F] (((↥S : Type _) → F) ⧸ M) := M.mkQ.comp res with hπ
  have hπsurj : Function.Surjective π := by
    have h1 : Function.Surjective res :=
      LinearMap.funLeft_surjective_of_injective F F _ Subtype.val_injective
    exact (Submodule.mkQ_surjective M).comp h1
  -- dimension count: `dim (dual of the quotient) = t − dim M ≥ t − k`
  have hdimS : finrank F ((↥S : Type _) → F) = t := by
    simp [Fintype.card_coe, hS]
  have hqM : finrank F (((↥S : Type _) → F) ⧸ M) + finrank F M =
      finrank F ((↥S : Type _) → F) :=
    Submodule.finrank_quotient_add_finrank M
  have hMle : finrank F M ≤ finrank F C := Submodule.finrank_map_le res C
  have hdual : finrank F (Module.Dual F (((↥S : Type _) → F) ⧸ M)) =
      finrank F (((↥S : Type _) → F) ⧸ M) :=
    Subspace.dual_finrank_eq
  have hbudget : t - finrank F C ≤
      finrank F (Module.Dual F (((↥S : Type _) → F) ⧸ M)) := by omega
  -- pick `t − k` independent duals of the quotient
  set b := Module.finBasis F (Module.Dual F (((↥S : Type _) → F) ⧸ M)) with hb
  set lam : Fin (t - finrank F C) → Module.Dual F (((↥S : Type _) → F) ⧸ M) :=
    fun j => b (Fin.castLE hbudget j) with hlam
  have hlamli : LinearIndependent F lam :=
    b.linearIndependent.comp _ (Fin.castLE_injective hbudget)
  refine ⟨fun j => (lam j).comp π, ?_, ?_, ?_⟩
  · -- independence: `π` is surjective, so composing with it preserves independence
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have hlamzero : ∑ j, a j • lam j = 0 := by
      apply LinearMap.ext
      intro q
      obtain ⟨v, rfl⟩ := hπsurj q
      have := congrArg (fun f => f v) ha
      simpa [LinearMap.sum_apply, LinearMap.smul_apply] using this
    exact Fintype.linearIndependent_iff.mp hlamli a hlamzero
  · -- annihilation of the code
    intro j x hx
    have : π x = 0 := by
      simp only [hπ, LinearMap.comp_apply, Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero M).mpr (Submodule.mem_map_of_mem hx)
    simp [LinearMap.comp_apply, this]
  · -- the line vanishes: on `S` it equals `c`, and `c` is a codeword
    intro j
    have hresline : res (u₀ + γ • u₁) = res c := by
      funext s
      have := hc (s : ι) s.2
      simp [hres, LinearMap.funLeft_apply, this]
    have : π (u₀ + γ • u₁) = 0 := by
      simp only [hπ, LinearMap.comp_apply, hresline, Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero M).mpr (Submodule.mem_map_of_mem hcC)
    simp [LinearMap.comp_apply, this]

/-! ## Bridge functionals: `r` witnesses on the syndrome pair space -/

/-- **Functional construction (all witnesses).**  `r` bad scalars, each with a
threshold-`t` witness, yield `r·(t−k)` functionals on the syndrome pair space that all
vanish on the stack's syndrome pair, with each per-witness block linearly independent.
`φ(i,j) = ℓ̄ᵢⱼ ∘ fst + γᵢ · (ℓ̄ᵢⱼ ∘ snd)` — the `γᵢ`-weighted parity rows of the probe. -/
theorem exists_bridge_functionals (C : Submodule F (ι → F)) {r t : ℕ}
    {u₀ u₁ : ι → F} (γ : Fin r → F)
    (hwit : ∀ i, ∃ S : Finset ι, S.card = t ∧
      ∃ c ∈ C, ∀ x ∈ S, c x = u₀ x + γ i * u₁ x) :
    ∃ φ : Fin r × Fin (t - finrank F C) → Module.Dual F (SyndromePair C),
      (∀ p, φ p (syndromePair C u₀ u₁) = 0) ∧
      (∀ i, LinearIndependent F fun j => φ (i, j)) := by
  classical
  -- extract the row functionals of each witness
  have hrows : ∀ i, ∃ ℓ : Fin (t - finrank F C) → Module.Dual F (ι → F),
      LinearIndependent F ℓ ∧ (∀ j, ∀ x ∈ C, ℓ j x = 0) ∧
      (∀ j, ℓ j (u₀ + γ i • u₁) = 0) := by
    intro i
    obtain ⟨S, hS, hagree⟩ := hwit i
    exact exists_rowFunctionals C hS hagree
  choose ℓ hℓli hℓann hℓline using hrows
  -- descend to the syndrome quotient
  have hker : ∀ i j, C ≤ LinearMap.ker (ℓ i j) := fun i j x hx =>
    LinearMap.mem_ker.mpr (hℓann i j x hx)
  set lbar : Fin r → Fin (t - finrank F C) → Module.Dual F ((ι → F) ⧸ C) :=
    fun i j => C.liftQ (ℓ i j) (hker i j) with hlbar
  have hlbar_mk : ∀ i j (v : ι → F), lbar i j (C.mkQ v) = ℓ i j v := by
    intro i j v
    simp [hlbar, Submodule.mkQ_apply, Submodule.liftQ_apply]
  -- fold in the γ-weights on the pair space
  refine ⟨fun p =>
    (lbar p.1 p.2).comp (LinearMap.fst F _ _) +
      γ p.1 • (lbar p.1 p.2).comp (LinearMap.snd F _ _), ?_, ?_⟩
  · -- annihilation of the syndrome pair
    rintro ⟨i, j⟩
    have h1 : lbar i j (C.mkQ u₀) + γ i * lbar i j (C.mkQ u₁) = 0 := by
      rw [hlbar_mk, hlbar_mk]
      have := hℓline i j
      rw [map_add, map_smul] at this
      simpa [smul_eq_mul] using this
    simpa [syndromePair, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, smul_eq_mul] using h1
  · -- per-witness independence, by evaluating at pairs `(mkQ v, 0)`
    intro i
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have hzero : ∑ j, a j • ℓ i j = 0 := by
      apply LinearMap.ext
      intro v
      have := congrArg (fun f => f ((C.mkQ v, 0) : SyndromePair C)) ha
      simpa [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply,
        LinearMap.comp_apply, hlbar_mk] using this
    exact Fintype.linearIndependent_iff.mp (hℓli i) a hzero

/-! ## The bridge theorem: G86 applies verbatim -/

/-- **G87 bridge theorem.**  For any stack `(u₀, u₁)` that is not a codeword pair and
any `r` scalars each bad-via-witness at agreement threshold `t`, the constructed
witness functionals are `Plantable` (the annihilated nonzero vector is the syndrome
pair itself), so the G86 rank-collapse dichotomy applies verbatim: EITHER the generic
budget `r·(t−k) + 1 ≤ 2(n−k)` holds, OR the witness functionals admit an explicit
nontrivial syzygy. -/
theorem syndrome_dichotomy (C : Submodule F (ι → F)) {r t : ℕ}
    {u₀ u₁ : ι → F} (γ : Fin r → F)
    (hstack : u₀ ∉ C ∨ u₁ ∉ C)
    (hwit : ∀ i, ∃ S : Finset ι, S.card = t ∧
      ∃ c ∈ C, ∀ x ∈ S, c x = u₀ x + γ i * u₁ x) :
    ∃ φ : Fin r × Fin (t - finrank F C) → Module.Dual F (SyndromePair C),
      (∀ p, φ p (syndromePair C u₀ u₁) = 0) ∧
      (∀ i, LinearIndependent F fun j => φ (i, j)) ∧
      (r * (t - finrank F C) + 1 ≤ 2 * (Fintype.card ι - finrank F C) ∨
        ∃ cc : Fin r × Fin (t - finrank F C) → F,
          (∑ p, cc p • φ p = 0) ∧ ∃ p, cc p ≠ 0) := by
  obtain ⟨φ, hann, hblock⟩ := exists_bridge_functionals C γ hwit
  refine ⟨φ, hann, hblock, ?_⟩
  have hplant : Plantable φ := by
    refine ⟨syndromePair C u₀ u₁, ?_, hann⟩
    intro h0
    obtain ⟨h₀, h₁⟩ := (syndromePair_eq_zero_iff C u₀ u₁).mp h0
    rcases hstack with h | h
    · exact h h₀
    · exact h h₁
  have := plantable_dichotomy hplant
  rwa [finrank_syndromePair C] at this

end SyndromeSpace

/-! ## Witness extraction from the ABF26 `mcaEvent` -/

section McaEvent

open _root_.ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Witness extraction.**  The ABF26 `mcaEvent` at radius `δ` yields a bad-via-`(S,c)`
witness at any threshold `t ≤ (1−δ)·n`: take any `t`-subset of the event's witness set. -/
theorem mcaEvent_witness {Cset : Set (ι → F)} {δ : ℝ≥0} {u₀ u₁ : ι → F} {γ : F}
    (h : mcaEvent Cset δ u₀ u₁ γ) {t : ℕ}
    (ht : (t : ℝ≥0) ≤ (1 - δ) * (Fintype.card ι : ℝ≥0)) :
    ∃ S : Finset ι, S.card = t ∧ ∃ c ∈ Cset, ∀ x ∈ S, c x = u₀ x + γ * u₁ x := by
  obtain ⟨S₀, hS₀, ⟨w, hwC, hw⟩, -⟩ := h
  have hle : t ≤ S₀.card := by
    have : (t : ℝ≥0) ≤ (S₀.card : ℝ≥0) := le_trans ht hS₀
    exact_mod_cast this
  obtain ⟨S, hsub, hcard⟩ := Finset.exists_subset_card_eq hle
  exact ⟨S, hcard, w, hwC, fun x hx => by simpa [smul_eq_mul] using hw x (hsub hx)⟩

/-- **Degenerate case is impossible.**  A codeword-pair stack joint-agrees with itself
on every witness set, so it can never fire `mcaEvent`: any bad scalar certifies that
the stack is not a codeword pair (i.e. the syndrome pair is nonzero). -/
theorem mcaEvent_not_both_mem (C : Submodule F (ι → F)) {δ : ℝ≥0}
    {u₀ u₁ : ι → F} {γ : F} (h : mcaEvent (C : Set (ι → F)) δ u₀ u₁ γ) :
    u₀ ∉ C ∨ u₁ ∉ C := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨S, -, -, hno⟩ := h
  exact hno ⟨u₀, hcon.1, u₁, hcon.2, fun i _ => ⟨rfl, rfl⟩⟩

end McaEvent

/-! ## Consumer corollary at the production shape -/

section Wall

open _root_.ProximityGap _root_.ProximityGap.CensusLowerBound
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket

local instance localInstance_G87McaEventSyndromeBridge_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_G87McaEventSyndromeBridge_2 : NeZero P := ⟨prime_P.ne_zero⟩

/-- The gate code, presented as a `Submodule`: evaluations of polynomials of degree
`< 2^29` on the smooth domain `i ↦ g^i`, `n = 2^30`. -/
noncomputable def wallCode : Submodule (ZMod P) (Fin (2 ^ 30) → ZMod P) :=
  ProximityGap.CensusLowerBound.evalCode (fun i : Fin (2 ^ 30) => g ^ (i : ℕ)) (2 ^ 29)

/-- The submodule presentation carries exactly the gate hypothesis' code
(`KKH26.evalCode g (2^30) (2^29 − 1)`, the code of
`firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count`). -/
theorem wallCode_coe :
    (wallCode : Set (Fin (2 ^ 30) → ZMod P)) =
      ArkLib.ProximityGap.KKH26.evalCode g (2 ^ 30) (2 ^ 29 - 1) := rfl

/-- One-sided dimension bound: the wall code is parametrized by polynomials of degree
`< 2^29`, so its dimension is at most `2^29`.  (The reverse Vandermonde inequality is
never needed: a smaller code only shrinks the generic planting budget further.) -/
theorem finrank_wallCode_le : Module.finrank (ZMod P) wallCode ≤ 2 ^ 29 := by
  classical
  set E : Polynomial (ZMod P) →ₗ[ZMod P] (Fin (2 ^ 30) → ZMod P) :=
    LinearMap.pi (fun i : Fin (2 ^ 30) => Polynomial.leval (g ^ (i : ℕ))) with hE
  have hsub : wallCode ≤ (Polynomial.degreeLT (ZMod P) (2 ^ 29)).map E := by
    rintro f ⟨q, hq, hf⟩
    have hqm : q ∈ Polynomial.degreeLT (ZMod P) (2 ^ 29) := by
      rw [Polynomial.mem_degreeLT]
      refine lt_of_le_of_lt (Polynomial.degree_le_natDegree) ?_
      exact_mod_cast Nat.lt_of_le_of_lt hq (by norm_num)
    refine Submodule.mem_map.mpr ⟨q, hqm, ?_⟩
    funext i
    simp [hE, LinearMap.pi_apply, Polynomial.leval_apply, hf i]
  have h1 : Module.finrank (ZMod P) wallCode ≤
      Module.finrank (ZMod P) ((Polynomial.degreeLT (ZMod P) (2 ^ 29)).map E) :=
    Submodule.finrank_mono hsub
  have h2 : Module.finrank (ZMod P) ((Polynomial.degreeLT (ZMod P) (2 ^ 29)).map E) ≤
      Module.finrank (ZMod P) (Polynomial.degreeLT (ZMod P) (2 ^ 29)) :=
    Submodule.finrank_map_le E _
  have h3 : Module.finrank (ZMod P) (Polynomial.degreeLT (ZMod P) (2 ^ 29)) = 2 ^ 29 := by
    rw [(Polynomial.degreeLTEquiv (ZMod P) (2 ^ 29)).finrank_eq]
    simp
  omega

/-- The wall threshold: at the gate radius (`predecessorRadius (2^30) (31·2^24)`), the
`mcaEvent` witness set has at least `t = 2^30 − 31·2^24 + 1 = 553648129` points. -/
theorem wall_threshold :
    ((553648129 : ℕ) : ℝ≥0) ≤
      (1 - predecessorRadius (2 ^ 30) (31 * 2 ^ 24)) *
        (Fintype.card (Fin (2 ^ 30)) : ℝ≥0) := by
  rw [Fintype.card_fin, predecessorRadius, tsub_mul, one_mul,
    div_mul_cancel₀ _ (by norm_num : ((2 ^ 30 : ℕ) : ℝ≥0) ≠ 0),
    le_tsub_iff_right (Nat.cast_le.mpr (by norm_num : (31 * 2 ^ 24 - 1 : ℕ) ≤ 2 ^ 30))]
  exact_mod_cast (by norm_num : (553648129 + (31 * 2 ^ 24 - 1) : ℕ) ≤ 2 ^ 30)

/-- **Consumer corollary at the production shape (the honest provable form).**
For the first certified prize field, the exact code, and the exact predecessor radius
of the gate hypothesis
`firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count`: any stack
with `r ≥ 64` bad scalars (each firing `mcaEvent`) yields witness functionals on the
`≥ 2^30`-dimensional syndrome pair space that (a) all vanish on the stack's syndrome
pair, (b) are linearly independent within each witness block, and (c) globally admit an
**explicit nontrivial syzygy** — because the generic disjunct of the G86 dichotomy is
numerically impossible: `64·(t−k) + 1 ≥ 64·(2^24+1) + 1 = 2^30 + 65 > 2(n−k)` for every
`k ≤ 2^29`.  Equivalently, the wall hypothesis (budget `2^30`) can only fail through
syzygy configurations: independent-block planting is capped at `63` scalars. -/
theorem wall_syzygy_of_sixtyFour_bad_scalars
    {r : ℕ} (hr : 64 ≤ r) (u₀ u₁ : Fin (2 ^ 30) → ZMod P) (γ : Fin r → ZMod P)
    (hbad : ∀ i, mcaEvent
      (ArkLib.ProximityGap.KKH26.evalCode g (2 ^ 30) (2 ^ 29 - 1))
      (predecessorRadius (2 ^ 30) (31 * 2 ^ 24)) u₀ u₁ (γ i)) :
    ∃ φ : Fin r × Fin (553648129 - Module.finrank (ZMod P) wallCode) →
        Module.Dual (ZMod P) (SyndromePair wallCode),
      (∀ p, φ p (syndromePair wallCode u₀ u₁) = 0) ∧
      (∀ i, LinearIndependent (ZMod P) fun j => φ (i, j)) ∧
      ∃ cc : Fin r × Fin (553648129 - Module.finrank (ZMod P) wallCode) → ZMod P,
        (∑ p, cc p • φ p = 0) ∧ ∃ p, cc p ≠ 0 := by
  have hbad' : ∀ i, mcaEvent (wallCode : Set (Fin (2 ^ 30) → ZMod P))
      (predecessorRadius (2 ^ 30) (31 * 2 ^ 24)) u₀ u₁ (γ i) := by
    intro i; rw [wallCode_coe]; exact hbad i
  have hwit : ∀ i, ∃ S : Finset (Fin (2 ^ 30)), S.card = 553648129 ∧
      ∃ c ∈ wallCode, ∀ x ∈ S, c x = u₀ x + γ i * u₁ x :=
    fun i => mcaEvent_witness (hbad' i) wall_threshold
  have hstack : u₀ ∉ wallCode ∨ u₁ ∉ wallCode :=
    mcaEvent_not_both_mem wallCode (hbad' ⟨0, by omega⟩)
  obtain ⟨φ, hann, hblock, hdich⟩ := syndrome_dichotomy wallCode γ hstack hwit
  refine ⟨φ, hann, hblock, ?_⟩
  rcases hdich with hcap | hsyz
  · -- the generic cap is numerically impossible at the production shape
    exfalso
    have hkle : Module.finrank (ZMod P) wallCode ≤ 536870912 :=
      le_trans finrank_wallCode_le (by norm_num)
    have hcard : Fintype.card (Fin (2 ^ 30)) = 1073741824 := by
      rw [Fintype.card_fin]; norm_num
    generalize hK : Module.finrank (ZMod P) ↥wallCode = K at hcap hkle
    generalize hN : Fintype.card (Fin (2 ^ 30)) = N at hcap hcard
    have h64 : 64 * (553648129 - K) ≤ r * (553648129 - K) :=
      Nat.mul_le_mul_right _ hr
    have hcap' := le_trans (Nat.add_le_add_right h64 1) hcap
    omega
  · exact hsyz

/-- Equivalent impossibility form: the witness functionals of `64` bad scalars at the
gate shape can **never** be linearly independent (their count over-spends the syndrome
budget: independent planting is capped at `63`). -/
theorem wall_not_linearIndependent_of_sixtyFour_bad_scalars
    {r : ℕ} (hr : 64 ≤ r) (u₀ u₁ : Fin (2 ^ 30) → ZMod P) (γ : Fin r → ZMod P)
    (hbad : ∀ i, mcaEvent
      (ArkLib.ProximityGap.KKH26.evalCode g (2 ^ 30) (2 ^ 29 - 1))
      (predecessorRadius (2 ^ 30) (31 * 2 ^ 24)) u₀ u₁ (γ i)) :
    ∃ φ : Fin r × Fin (553648129 - Module.finrank (ZMod P) wallCode) →
        Module.Dual (ZMod P) (SyndromePair wallCode),
      (∀ p, φ p (syndromePair wallCode u₀ u₁) = 0) ∧
      (∀ i, LinearIndependent (ZMod P) fun j => φ (i, j)) ∧
      ¬ LinearIndependent (ZMod P) φ := by
  obtain ⟨φ, hann, hblock, cc, hcc, hne⟩ :=
    wall_syzygy_of_sixtyFour_bad_scalars hr u₀ u₁ γ hbad
  exact ⟨φ, hann, hblock, Fintype.not_linearIndependent_iff.mpr ⟨cc, hcc, hne⟩⟩

end Wall

end ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge

-- Honesty audit:
#print axioms ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge.plantable_dichotomy
#print axioms ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge.finrank_syndromePair
#print axioms ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge.exists_rowFunctionals
#print axioms ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge.exists_bridge_functionals
#print axioms ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge.syndrome_dichotomy
#print axioms ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge.mcaEvent_witness
#print axioms ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge.mcaEvent_not_both_mem
#print axioms ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge.wallCode_coe
#print axioms ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge.finrank_wallCode_le
#print axioms ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge.wall_threshold
#print axioms ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge.wall_syzygy_of_sixtyFour_bad_scalars
#print axioms ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge.wall_not_linearIndependent_of_sixtyFour_bad_scalars

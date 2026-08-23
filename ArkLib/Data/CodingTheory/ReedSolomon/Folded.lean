/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Folded Reed-Solomon codes (ABF26 §2.4)

ABF26 Definitions 2.14 and 2.15: the folded Reed-Solomon code `FRS[F, L, k, s, ω]`
and the `(L, s)`-admissibility condition on the folding element `ω`.

## Main definitions

- `ReedSolomon.Folded.Admissible` — ABF26 Definition 2.14.
- `ReedSolomon.Folded.frsEvalOnPoints` — F-linear FRS evaluation map.
- `ReedSolomon.Folded.frsCode` — ABF26 Definition 2.15 [GR08].

## Main lemmas

- `ReedSolomon.Folded.mem_frsCode_iff` / `mem_frsCode_iff_flipped` — paper-style
  membership characterisation.
- `ReedSolomon.Folded.dim_frsCode` — `Module.finrank F (frsCode …) = k` under FRS
  encoder injectivity.
- `ReedSolomon.Folded.mem_frsCode_one_iff_mem_rsCode` /
  `frsCode_one_map_eq_rsCode` — sanity checks for `s = 1` collapse to plain RS.

## References

- [ABF26] Arnon-Boneh-Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. §2.4 Definitions 2.14, 2.15.
- [GR08] Guruswami-Rudra. (Original FRS paper.)
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ReedSolomon
namespace Folded

/-- **ABF26 Definition 2.14 (strengthened).** An element `ω : F` is `(L, s)`-admissible
if **every evaluation point appears only once across all folds**, i.e. the map
`(α, i) ↦ α · ω^i : L × Fin s → F` is injective.

Split into two conjuncts to keep the predicate `simp`-friendly:

  - **inter-orbit:** for distinct `α ≠ β ∈ L`, `α · ω^i ≠ β` for every `i < s`.
  - **intra-orbit:** for every `α ∈ L`, `α · ω^i ≠ α` for every `0 < i < s` —
    equivalently, `ω` has multiplicative order at least `s` on the non-zero
    orbit of `α`.

**Deviation from the paper's literal text.** Definition 2.14 of ABF26 states only the
*inter-orbit* clause (it quantifies over unordered pairs `{α, β} ∈ (L choose 2)`, hence
distinct `α ≠ β`). Its literal reading therefore does *not* forbid `ω^j = 1` for some
`0 < j < s`, which would collapse a fold's `s`-tuple to a repeated-entry vector and
silently weaken the FRS distance argument downstream (T2.18, T4.14). We add the
*intra-orbit* conjunct so that `Admissible` is exactly the GR08 injectivity condition
the paper's results actually rely on. This is a deliberate strengthening, not a verbatim
transcription. -/
def Admissible {F : Type} [Field F] [DecidableEq F]
    (L : Finset F) (s : ℕ) (ω : F) : Prop :=
  (∀ α ∈ L, ∀ β ∈ L, α ≠ β → ∀ i : ℕ, i < s → α * ω ^ i ≠ β) ∧
  (∀ α ∈ L, ∀ i : ℕ, 0 < i → i < s → α * ω ^ i ≠ α)

/-- The FRS evaluation map as an `F`-linear map from polynomials to `ι → Fin s → F`,
mirroring `ReedSolomon.evalOnPoints` (which is the `s = 1` special case). -/
def frsEvalOnPoints {ι : Type} [Fintype ι]
    {F : Type} [CommSemiring F]
    (domain : ι ↪ F) (s : ℕ) (ω : F) : Polynomial F →ₗ[F] (ι → Fin s → F) where
  toFun p := fun x j ↦ p.eval (domain x * ω ^ (j : ℕ))
  map_add' p q := by ext; simp
  map_smul' c p := by ext; simp

/-- **ABF26 Definition 2.15 [GR08].** The folded Reed-Solomon code:

  `FRS[F, L, k, s, ω] := { f : L → F^s | ∃ f̂ ∈ F^{<k}[X],`
  `                          ∀ x ∈ L, f(x) = (f̂(x), f̂(x·ω), ..., f̂(x·ω^{s-1})) }`

The fold packages `s` consecutive evaluations of a single underlying polynomial into a
length-`s` vector at each evaluation point. We do not bake the `Admissible` hypothesis
into the definition itself — admissibility is left as a side condition for downstream
statements about distance / list decoding. Note that `FRS[F, L, k, 1, ω] = RS[F, L, k]`
for any `ω`.

**Submodule structure.** Defined as `(Polynomial.degreeLT F k).map (frsEvalOnPoints …)`,
exactly mirroring `ReedSolomon.code`. This makes `frsCode` a `Submodule F (ι → Fin s → F)`
directly — `F`-linear by construction — so downstream theorems (e.g. T2.18, T4.14)
consume it as a `ModuleCode ι F (Fin s → F)` without an existential wrap. -/
noncomputable def frsCode {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F) : Submodule F (ι → Fin s → F) :=
  (Polynomial.degreeLT F k).map (frsEvalOnPoints domain s ω)

/-- **Membership of `frsCode` in paper-style form.** A vector `f : ι → Fin s → F` is
in `frsCode domain k s ω` iff there is a polynomial of degree `< k` whose folded
evaluations match `f`. This is the original paper-shaped membership predicate, kept
as a `simp`-able iff lemma. -/
lemma mem_frsCode_iff {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F) (f : ι → Fin s → F) :
    f ∈ frsCode domain k s ω ↔
      ∃ p ∈ Polynomial.degreeLT F k,
        ∀ x : ι, ∀ j : Fin s, f x j = p.eval (domain x * ω ^ (j : ℕ)) := by
  simp only [frsCode, Submodule.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p, hp, ?_⟩
    intro x j
    rfl
  · rintro ⟨p, hp, hf⟩
    refine ⟨p, hp, ?_⟩
    ext x j
    exact (hf x j).symm

/-- **Dimension of `frsCode`.** When the FRS encoder is injective on `degreeLT F k` — i.e.
when `(L, s)`-admissibility plus enough evaluation points (`k ≤ s · |L|`) rule out
non-trivial polynomial vanishing on the folded orbit — the dimension equals `k`.

The hypothesis `h_encoder_inj` packages exactly this injectivity. The "natural" RS case
is `h_encoder_inj := Polynomial.degreeLT_eval_inj` (or equivalent); we leave it as a
hypothesis so this lemma is reusable across regimes. -/
lemma dim_frsCode {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (h_encoder_inj : Function.Injective (frsEvalOnPoints domain s ω)) :
    Module.finrank F (frsCode domain k s ω) = k := by
  unfold frsCode
  rw [(Submodule.equivMapOfInjective _ h_encoder_inj _).finrank_eq.symm]
  exact (Polynomial.degreeLTEquiv F k).finrank_eq.trans (by simp)

/-- Mirror of `mem_frsCode_iff` with the equation oriented `encoder = f` rather than
`f = encoder` — useful for `rw` / `simp` from the encoder side. -/
lemma mem_frsCode_iff_flipped {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F) (f : ι → Fin s → F) :
    f ∈ frsCode domain k s ω ↔
      ∃ p ∈ Polynomial.degreeLT F k,
        ∀ x : ι, ∀ j : Fin s, p.eval (domain x * ω ^ (j : ℕ)) = f x j := by
  rw [mem_frsCode_iff]
  refine exists_congr fun p ↦ and_congr_right fun _ ↦ ?_
  exact ⟨fun h x j ↦ (h x j).symm, fun h x j ↦ (h x j).symm⟩

/-- **Sanity check: `FRS[F, L, k, 1, ω] ≃ RS[F, L, k]`.** With `s = 1` there is exactly
one fold and `Fin 1 → F ≃ F`, so the folded RS code collapses to the standard
Reed-Solomon code. Stated as an iff between memberships to avoid the cross-type
equality issue (the LHS lives in `ι → Fin 1 → F`, the RHS in `ι → F`). -/
lemma mem_frsCode_one_iff_mem_rsCode {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k : ℕ) (ω : F) (f : ι → Fin 1 → F) :
    f ∈ frsCode domain k 1 ω ↔
      (fun i ↦ f i 0) ∈ ReedSolomon.code domain k := by
  simp only [mem_frsCode_iff, ReedSolomon.code, Submodule.mem_map, ReedSolomon.evalOnPoints]
  constructor
  · rintro ⟨p, hp, hf⟩
    refine ⟨p, hp, ?_⟩
    ext i
    simpa using (hf i 0).symm
  · rintro ⟨p, hp, hp_eval⟩
    refine ⟨p, hp, ?_⟩
    intro i j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    have := congrFun hp_eval i
    simpa using this.symm

/-- **Submodule-level form of the `s = 1` collapse.** Under the natural F-linear
isomorphism `flat : (ι → Fin 1 → F) ≃ₗ[F] (ι → F)` (componentwise via
`LinearEquiv.funUnique`), the image of `frsCode domain k 1 ω` is exactly
`ReedSolomon.code domain k`. This is the structural form of `mem_frsCode_one_iff_mem_rsCode`:
the two codes correspond under the canonical "drop the trivial fold" isomorphism. -/
lemma frsCode_one_map_eq_rsCode {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k : ℕ) (ω : F) :
    (frsCode domain k 1 ω).map
        (LinearEquiv.piCongrRight (fun _ : ι ↦ LinearEquiv.funUnique (Fin 1) F F) :
            (ι → Fin 1 → F) ≃ₗ[F] (ι → F)).toLinearMap =
      ReedSolomon.code domain k := by
  ext g
  simp only [Submodule.mem_map, LinearEquiv.coe_toLinearMap]
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [mem_frsCode_one_iff_mem_rsCode] at hf
    convert hf using 1
  · intro hg
    refine ⟨fun i _ ↦ g i, ?_, ?_⟩
    · rw [mem_frsCode_one_iff_mem_rsCode]
      convert hg using 1
    · ext i
      simp [LinearEquiv.piCongrRight, LinearEquiv.funUnique]

end Folded
end ReedSolomon

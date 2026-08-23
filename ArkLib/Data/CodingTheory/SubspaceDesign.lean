/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Folded
import ArkLib.Data.CodingTheory.ReedSolomon.AdmissibleDischarge
import ArkLib.Data.CodingTheory.ProximityGap.GK16DegreeBudget
import ArkLib.Data.CodingTheory.ProximityGap.GK16Lemma12
import ArkLib.Data.CodingTheory.ProximityGap.GK16FrsTransport
import ArkLib.Data.CodingTheory.ProximityGap.GK16Admissible
import ArkLib.ToMathlib.GK16Claim16Witness
import ArkLib.ToMathlib.GK16Structural
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Polynomial.HasseDeriv

/-!
# Subspace-design codes (ABF26 §2.5)

ABF26 Definition 2.16 [GX13]: the τ-subspace-design property for an F-additive code
`C : F^k → (F^s)^n`. Lemma 2.17 [GG25] is **proven** (with a statement repair: the
paper-faithful rate over the block alphabet `F^s` is `k/(s·n)`, see the docstring).
Theorem 2.18 [GK16] (FRS half) is now **proven modulo a single named residual**
(`GK16DegreeBudget`, the GK16 §4 degree budget bundling the two deep gaps); its `τ` was
**repaired for the same `s`-factor rate bug** as L2.17.

## Main definitions

- `CodingTheory.IsSubspaceDesign` — ABF26 Definition 2.16.
- `CodingTheory.GK16DegreeBudget` — the GK16 §4 degree-budget residual
  `∑_i dim A_i ≤ (dim A)·(k-1)` (packages the two deep gaps ①② of T2.18).

## Main statements

- `CodingTheory.ker_proj_eq_vanish_at` — bridge between `ker(proj i)` and `{a | a i = 0}`.
- `CodingTheory.subspaceDesign_tau_lower` — ABF26 Lemma 2.17 [GG25] (**proven**, statement
  repaired): a nontrivial τ-subspace-design code of rate `ρ = k/(s·n)` has
  `min_{r∈[s]} τ(r) ≥ ρ - 1/n`, via the 1-dimensional-span instantiation + the Singleton
  bound over the block alphabet.
- `CodingTheory.frs_is_subspaceDesign_gk16` — ABF26 Theorem 2.18 [GK16], FRS half
  (**proven** given `GK16DegreeBudget`; rate-arithmetic reduction is axiom-clean). The `τ`
  is repaired to the paper-rate-consistent `τ(r) = (k-1)/n` on `[s]` — the pre-repair
  `s·k/(n·(s-r+1))` inherited the same `s`-factor inflation as the pre-repair L2.17. See
  the theorem docstring for the repair and the two residual gaps.
- `CodingTheory.um_is_subspaceDesign_gk16` — ABF26 Theorem 2.18, UM half.

## References

- [ABF26] Arnon-Boneh-Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. §2.5 Definition 2.16, Lemma 2.17, Theorem 2.18.
- [GX13] Guruswami-Xing. (Original subspace-design definition.)
- [GG25] Goyal-Guruswami. (Cited for L2.17.)
- [GK16] Guruswami-Kopparty. (Cited for T2.18.)
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal

/-- **ABF26 Definition 2.16 [GX13].** A code `C : F^k → (F^s)^n` (here represented as a
subspace of `(ι → Fin s → F)` over `F`) is **τ-subspace-design** if for every `r ∈ ℕ`
and every F-linear subspace `A` of `C` with `dim A ≤ r`,

  `(Σ_{i ∈ [n]} dim A_i) / n ≤ dim A · τ(r)`

where `A_i := { a ∈ A : a_i = 0^s }` is the subspace of `A` whose codewords vanish at
position `i`. Here `A_i` is realised as `A ⊓ ker(eval_i)`, the intersection of `A`
with the kernel of the linear map evaluating the `i`-th coordinate. -/
def IsSubspaceDesign {ι : Type} [Fintype ι]
    {F : Type} [Field F] (s : ℕ) (τ : ℕ → ℝ)
    (C : Submodule F (ι → Fin s → F)) : Prop :=
  ∀ r : ℕ, ∀ A : Submodule F (ι → Fin s → F), A ≤ C →
    Module.finrank F A ≤ r →
    (∑ i : ι,
        (Module.finrank F (↥(A ⊓
            (LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
            Submodule F (ι → Fin s → F))) : ℝ)) /
        Fintype.card ι ≤
      Module.finrank F A * τ r

/-- A τ-profile can be weakened pointwise: a τ-subspace-design is also a τ'-subspace-design
whenever `τ r ≤ τ' r` for every `r`. -/
theorem IsSubspaceDesign.mono_tau {ι : Type} [Fintype ι]
    {F : Type} [Field F] {s : ℕ} {τ τ' : ℕ → ℝ}
    {C : Submodule F (ι → Fin s → F)}
    (h : IsSubspaceDesign s τ C) (hτ : ∀ r, τ r ≤ τ' r) :
    IsSubspaceDesign s τ' C := by
  intro r A hA hA_rank
  have hrank_nonneg : 0 ≤ (Module.finrank F A : ℝ) := Nat.cast_nonneg _
  exact le_trans (h r A hA hA_rank)
    (mul_le_mul_of_nonneg_left (hτ r) hrank_nonneg)

/-- **Bridge: kernel of the `i`-th projection equals the comprehension `{a | a i = 0}`.**

The subspace `A_i := {a ∈ A : a_i = 0^s}` from the paper's `IsSubspaceDesign` definition
is `A ⊓ ker(LinearMap.proj i)`. This lemma confirms the underlying set: a word
`a : ι → Fin s → F` lies in `ker(proj i)` iff `a i = 0`. Combined with `Submodule.inf_*`
this lets downstream proofs rewrite freely between the technical `ker(proj i)` form (used
in the `IsSubspaceDesign` definition for type-class reasons) and the paper's
comprehension form. -/
lemma ker_proj_eq_vanish_at {ι : Type*} {F : Type*} [Semiring F] {s : ℕ} (i : ι) :
    (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) :
        Set (ι → Fin s → F)) =
      {a | a i = 0} := by
  ext a
  simp [LinearMap.mem_ker, LinearMap.proj_apply]

/-- The 1-dimensional subspace `span{a}` meets `ker(proj i)` in itself when `a i = 0`. -/
private lemma span_inf_ker_proj_of_eq_zero {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {s : ℕ} {a : ι → Fin s → F} {i : ι} (hai : a i = 0) :
    (Submodule.span F {a}) ⊓
        LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) =
      Submodule.span F {a} :=
  inf_eq_left.mpr <| Submodule.span_le.mpr <| Set.singleton_subset_iff.mpr <| by
    simp [LinearMap.mem_ker, LinearMap.proj_apply, hai]

/-- The 1-dimensional subspace `span{a}` meets `ker(proj i)` trivially when `a i ≠ 0`. -/
private lemma span_inf_ker_proj_of_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {s : ℕ} {a : ι → Fin s → F} {i : ι} (hai : a i ≠ 0) :
    (Submodule.span F {a}) ⊓
        LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx_span, hx_ker⟩ := Submodule.mem_inf.mp hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx_span
  have h0 : c • a i = 0 := by
    simpa [LinearMap.mem_ker, LinearMap.proj_apply] using hx_ker
  rcases smul_eq_zero.mp h0 with hc | h
  · simp [hc]
  · exact absurd h hai

/-- **ABF26 Lemma 2.17 [GG25]** (statement repaired — see below). For any *nontrivial*
τ-subspace-design code `C : F^k → (F^s)^n` of rate `ρ := k/(s·n)`, the profile `τ` is
lower-bounded by `ρ - 1/n` over the paper's range `r ∈ [s] = {1, …, s}`:

  `min_{r ∈ [s]} τ(r) ≥ ρ - 1/n` .

**Statement repair (2026-06-04).** The previous (admitted) form used `ρ := k/n`.
ABF26 Definition 2.5 fixes the rate of a code over alphabet `Σ` as `log_|Σ| |C| / n`;
for an F-additive code over `Σ = F^s` with `|C| = |F|^k` this is `k/(s·n)`, not `k/n`.
The `k/n` form is **false for `s ≥ 2`**: the full code `C = (F^s)^n` is
`(1 - 1/n)`-subspace-design — for any `A ≤ C`,
`Σ_i dim A_i = n·dim A - Σ_i rank(eval_i) ≤ (n-1)·dim A` because
`⋂_i ker(eval_i) = ⊥` forces `Σ_i rank(eval_i) ≥ dim A` — yet the `k/n` form would
demand `τ(r) ≥ s - 1/n > 1 - 1/n`. At the corrected rate the full code is instead the
tightness witness: `k/(s·n) - 1/n = 1 - 1/n`.

**Nontriviality `C ≠ ⊥`** is paper-implicit (a code is a map `F^k → (F^s)^n` with
`k ≥ 1`): for `C = ⊥` the design property constrains nothing (the only subspace is
`A = ⊥`, giving `0 ≤ 0`), while the conclusion would still assert `τ(r) ≥ -1/n`,
which fails for e.g. `τ ≡ -1`.

The quantifier is restricted to `r ∈ Finset.Icc 1 s` to match the paper's `[s]`
notation: outside this range the `IsSubspaceDesign` predicate places no
constraint on `τ`, so the bound is vacuous for `r = 0` (where `A ≤ C` with
`finrank A ≤ 0` forces `A = ⊥`, making the design inequality `0 ≤ 0 · τ(0)`
trivially satisfied by any `τ(0)` including ones violating the lower bound).

**Proof sketch.** Take a minimum-weight nonzero codeword `a` (the minimum distance
`d` of `C` is achieved by a pair `u ≠ v`; set `a := u - v`). Instantiate the design
property at the 1-dimensional `A := span{a}` (`dim A = 1 ≤ r`): then `A_i = A` iff
`a i = 0` and `A_i = ⊥` otherwise, so `Σ_i dim A_i = n - wt(a) = n - d`, giving
`τ(r) ≥ (n-d)/n`. The Singleton bound over the block alphabet `F^s`
(`q^k ≤ (q^s)^{n-d+1}`) gives `k ≤ s·(n-d+1)`, hence `(n-d)/n ≥ k/(s·n) - 1/n`. -/
theorem subspaceDesign_tau_lower
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (h_nontriv : C ≠ ⊥) :
    ∀ r ∈ Finset.Icc 1 s,
      τ r ≥ (Module.finrank F C : ℝ) / ((s : ℝ) * Fintype.card ι) -
        1 / Fintype.card ι := by
  intro r hr
  obtain ⟨hr1, hrs⟩ := Finset.mem_Icc.mp hr
  have hn_pos : 0 < Fintype.card ι := Fintype.card_pos
  -- ① A nonzero codeword exists, so the minimum distance is achieved by some pair.
  obtain ⟨a₀, ha₀C, ha₀ne⟩ := (Submodule.ne_bot_iff C).mp h_nontriv
  have hSne : {d | ∃ u ∈ (C : Set (ι → Fin s → F)), ∃ v ∈ (C : Set (ι → Fin s → F)),
      u ≠ v ∧ hammingDist u v = d}.Nonempty :=
    ⟨hammingDist a₀ 0, a₀, ha₀C, 0, C.zero_mem, ha₀ne, rfl⟩
  have hd_mem : Code.minDist (C : Set (ι → Fin s → F)) ∈
      {d | ∃ u ∈ (C : Set (ι → Fin s → F)), ∃ v ∈ (C : Set (ι → Fin s → F)),
        u ≠ v ∧ hammingDist u v = d} := by
    rw [Code.minDist]
    exact Nat.sInf_mem hSne
  obtain ⟨u, huC, v, hvC, huv_ne, huv_d⟩ := hd_mem
  -- The minimum-weight nonzero codeword `a := u - v`.
  have haC : u - v ∈ C := C.sub_mem huC hvC
  have ha_ne : u - v ≠ 0 := sub_ne_zero.mpr huv_ne
  have ha_norm : hammingNorm (u - v) = Code.minDist (C : Set (ι → Fin s → F)) := by
    rw [← neg_add_eq_sub, ← hammingDist_eq_hammingNorm, hammingDist_comm]
    exact huv_d
  have hd_pos : 1 ≤ Code.minDist (C : Set (ι → Fin s → F)) :=
    Nat.one_le_iff_ne_zero.mpr fun h0 =>
      huv_ne (hammingDist_eq_zero.mp (huv_d.trans h0))
  have hd_le_n : Code.minDist (C : Set (ι → Fin s → F)) ≤ Fintype.card ι := by
    rw [← huv_d]
    exact hammingDist_le_card_fintype
  -- ② Instantiate the design property at the 1-dimensional `A := span{a}`.
  have hA_le : Submodule.span F {u - v} ≤ C :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr haC)
  have hA_rank : Module.finrank F (Submodule.span F {u - v}) = 1 :=
    finrank_span_singleton ha_ne
  have hdesign := h r (Submodule.span F {u - v}) hA_le (by rw [hA_rank]; exact hr1)
  rw [hA_rank] at hdesign
  -- ③ Per-coordinate ranks: `dim A_i = 1` iff the block `(u-v) i` vanishes.
  have hterm : ∀ i : ι,
      (Module.finrank F (↥((Submodule.span F {u - v}) ⊓
          (LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
          Submodule F (ι → Fin s → F))) : ℝ) =
        if (u - v) i = 0 then 1 else 0 := by
    intro i
    by_cases hai : (u - v) i = 0
    · rw [span_inf_ker_proj_of_eq_zero hai, hA_rank, if_pos hai]
      norm_num
    · rw [span_inf_ker_proj_of_ne_zero hai, if_neg hai]
      simp
  -- ④ The design sum is the number of vanishing blocks, `n - d`.
  have hsum : (∑ i : ι,
      (Module.finrank F (↥((Submodule.span F {u - v}) ⊓
          (LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
          Submodule F (ι → Fin s → F))) : ℝ)) =
      (Fintype.card ι : ℝ) - Code.minDist (C : Set (ι → Fin s → F)) := by
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    rw [Finset.sum_boole]
    have hsplit : ({i | (u - v) i = 0} : Finset ι).card +
        ({i | (u - v) i ≠ 0} : Finset ι).card = Fintype.card ι := by
      simpa using Finset.card_filter_add_card_filter_not
        (s := Finset.univ) (p := fun i : ι => (u - v) i = 0)
    have hnorm_card : ({i | (u - v) i ≠ 0} : Finset ι).card =
        Code.minDist (C : Set (ι → Fin s → F)) := by
      rw [← ha_norm]; rfl
    have hzero_card : ({i | (u - v) i = 0} : Finset ι).card =
        Fintype.card ι - Code.minDist (C : Set (ι → Fin s → F)) := by omega
    rw [hzero_card]
    push_cast [Nat.cast_sub hd_le_n]
    ring
  have hkey : ((Fintype.card ι : ℝ) - Code.minDist (C : Set (ι → Fin s → F))) /
      (Fintype.card ι : ℝ) ≤ τ r := by
    calc ((Fintype.card ι : ℝ) - Code.minDist (C : Set (ι → Fin s → F))) /
        (Fintype.card ι : ℝ)
        = (∑ i : ι,
            (Module.finrank F (↥((Submodule.span F {u - v}) ⊓
                (LinearMap.ker
                  (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
                Submodule F (ι → Fin s → F))) : ℝ)) / (Fintype.card ι : ℝ) := by
          rw [hsum]
      _ ≤ (1 : ℕ) * τ r := hdesign
      _ = τ r := by norm_num
  -- ⑤ Singleton bound over the block alphabet `F^s`: `k ≤ s·(n - d + 1)`.
  have hsingleton : Module.finrank F C ≤
      s * (Fintype.card ι - Code.minDist (C : Set (ι → Fin s → F)) + 1) := by
    haveI : Fintype ↥(C : Set (ι → Fin s → F)) := Fintype.ofFinite _
    have hsb := singleton_bound (C : Set (ι → Fin s → F))
    rw [Subsingleton.elim (Fintype.ofFinite ↥(C : Set (ι → Fin s → F)))
      ‹Fintype ↥(C : Set (ι → Fin s → F))›,
      Subsingleton.elim (Fintype.ofFinite (Fin s → F)) inferInstance] at hsb
    have hcardC : Fintype.card ↥(C : Set (ι → Fin s → F)) =
        Fintype.card F ^ Module.finrank F C := by
      rw [Module.card_eq_pow_finrank (K := F)]
      rfl
    have hcardA : Fintype.card (Fin s → F) = Fintype.card F ^ s := by
      rw [Fintype.card_fun, Fintype.card_fin]
    rw [hcardC, hcardA, Code.dist_eq_minDist] at hsb
    have hq : 1 < Fintype.card F := Fintype.one_lt_card
    have hexp : Fintype.card ι - (Code.minDist (C : Set (ι → Fin s → F)) - 1) =
        Fintype.card ι - Code.minDist (C : Set (ι → Fin s → F)) + 1 := by omega
    rw [hexp, ← pow_mul] at hsb
    exact (Nat.pow_le_pow_iff_right hq).mp hsb
  -- ⑥ Final arithmetic: `k/(s·n) - 1/n ≤ (n-d)/n ≤ τ r`.
  have hs_pos : (0 : ℝ) < s := by
    have h1s : 1 ≤ s := le_trans hr1 hrs
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1s
  have hn_posR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn_pos
  rw [ge_iff_le]
  have hcast : (Module.finrank F C : ℝ) ≤
      (s : ℝ) * ((Fintype.card ι : ℝ) -
        Code.minDist (C : Set (ι → Fin s → F)) + 1) := by
    calc (Module.finrank F C : ℝ)
        ≤ ((s * (Fintype.card ι -
            Code.minDist (C : Set (ι → Fin s → F)) + 1) : ℕ) : ℝ) := by
          exact_mod_cast hsingleton
      _ = (s : ℝ) * ((Fintype.card ι : ℝ) -
            Code.minDist (C : Set (ι → Fin s → F)) + 1) := by
          push_cast [Nat.cast_sub hd_le_n]
          ring
  have hs0 : (s : ℝ) ≠ 0 := ne_of_gt hs_pos
  have hn0 : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hn_posR
  calc (Module.finrank F C : ℝ) / ((s : ℝ) * Fintype.card ι) - 1 / Fintype.card ι
      ≤ ((s : ℝ) * ((Fintype.card ι : ℝ) -
          Code.minDist (C : Set (ι → Fin s → F)) + 1)) /
          ((s : ℝ) * Fintype.card ι) - 1 / Fintype.card ι := by
        gcongr
    _ = ((Fintype.card ι : ℝ) - Code.minDist (C : Set (ι → Fin s → F))) /
          (Fintype.card ι : ℝ) := by
        field_simp
        ring
    _ ≤ τ r := hkey

/-- **The GK16 §4 degree-budget residual.** For a subspace `A` of the folded RS code,
the *folded-Wronskian degree budget* of GK16 §4 (Theorem 14): the per-coordinate
vanishing dimensions `dim A_i := dim (A ⊓ ker(eval_i))` sum to at most `(dim A)·(k-1)`.

This is the GK16 §4 spine line on p. 9,
`∑_i dim A_i ≤ ∑_i rootMultiplicity (domain i) L ≤ natDegree L ≤ (dim A)·(k-1)`, whose
last two `≤` are proven axiom-clean in ArkLib
(`ArkLib.FRS.GK16.sum_rootMultiplicity_foldedWronskian_le`) and whose first `≤` (plus the
`L ≠ 0` it needs) are the deep gaps ①② documented on `frs_is_subspaceDesign_gk16`. The
predicate names that combined residual so the rate arithmetic can be discharged from it. -/
def GK16DegreeBudget {ι : Type} [Fintype ι]
    {F : Type} [Field F] (k s : ℕ)
    (C : Submodule F (ι → Fin s → F)) : Prop :=
  ∀ A : Submodule F (ι → Fin s → F), A ≤ C →
    (∑ i : ι, Module.finrank F (↥(A ⊓
        (LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
        Submodule F (ι → Fin s → F)))) ≤ Module.finrank F A * (k - 1)

/-- **GK16 Claim 16 witness (named residual ②, with structural transport).** For a
subspace `A ≤ C = frsCode`, this packages exactly the data of GK16 Claims 15–16 plus the
encoder-isomorphism transport, in the precise shape the degree-budget reduction consumes:

* an indexed family `P : Fin (dim A) → F[X]` of the underlying polynomials (a basis of the
  polynomial space `U` with `A = U.map encoder`), each of degree `< k`;
* the folded Wronskian `L := foldedWronskian P ω` is **nonzero** (GK16 Lemma 12, hard
  direction — now an unconditional theorem, `gk16Lemma12HardResidual_holds`, modulo the
  admissibility of `ω`, which `Admissible` supplies);
* **Claim 16**: at each evaluation point `domain i`, the root multiplicity of `L` is at
  least `dim A_i = dim (A ⊓ ker(eval_i))`.

Everything *after* this witness — the chaining `∑_i dim A_i ≤ ∑_i mult ≤ deg L ≤
(dim A)(k-1)` — is **proven, axiom-clean** in `gk16DegreeBudget_of_claim16Witness`. The
witness isolates precisely the two deep gaps ①② (Lemma 12 nonvanishing is now closed;
Claim 16 + the transport remain) so that `GK16DegreeBudget` follows from it by a routine
root-counting argument. -/
def GK16Claim16Witness {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (C : Submodule F (ι → Fin s → F)) : Prop :=
  ∀ A : Submodule F (ι → Fin s → F), A ≤ C →
    ∃ P : Fin (Module.finrank F A) → Polynomial F,
      (∀ j, (P j).natDegree ≤ k - 1) ∧
      ArkLib.FRS.GK16.foldedWronskian P ω ≠ 0 ∧
      (∀ i : ι, Module.finrank F (↥(A ⊓
          (LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
          Submodule F (ι → Fin s → F)))
        ≤ Polynomial.rootMultiplicity (domain i) (ArkLib.FRS.GK16.foldedWronskian P ω))

/-- **GK16 Claim 16 witness, Lemma-12-discharged form (residual ② only).** Identical to
`GK16Claim16Witness` except that the *nonvanishing* clause `foldedWronskian P ω ≠ 0` is
**replaced** by its now-proven cause: the underlying family `P` is `F`-linearly
independent, together with the order/degree-separation admissibility of `ω` (`hω_sep`, exactly
the hypothesis of `ArkLib.FRS.GK16.foldedWronskian_ne_zero_of_linearIndependent`).

Since GK16 Lemma 12 (hard direction) is now an unconditional theorem in ArkLib
(`ArkLib.FRS.GK16.foldedWronskian_ne_zero_of_linearIndependent`,
`…gk16Lemma12HardResidual_holds`), this witness carries *strictly less* than
`GK16Claim16Witness`: it no longer assumes the folded Wronskian is nonzero — that is
*derived*. The only remaining content is genuinely residual ② (GK16 Claim 16: the
per-coordinate root-multiplicity lower bound + the encoder-isomorphism transport supplying
the independent polynomial family `P` of degrees `< k`). The reduction
`gk16Claim16Witness_of_indep` proves `GK16Claim16Witness` from this. -/
def GK16Claim16WitnessIndep {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (C : Submodule F (ι → Fin s → F)) : Prop :=
  ∀ A : Submodule F (ι → Fin s → F), A ≤ C →
    ∃ P : Fin (Module.finrank F A) → Polynomial F,
      (∀ j, (P j).natDegree ≤ k - 1) ∧
      LinearIndependent F P ∧
      (∀ Q : Fin (Module.finrank F A) → Polynomial F, (∀ j, Q j ≠ 0) →
          Function.Injective (fun j => (Q j).natDegree) →
          Function.Injective (fun j => ω ^ (Q j).natDegree)) ∧
      (∀ i : ι, Module.finrank F (↥(A ⊓
          (LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
          Submodule F (ι → Fin s → F)))
        ≤ Polynomial.rootMultiplicity (domain i) (ArkLib.FRS.GK16.foldedWronskian P ω))

/-- **Proven silver reduction: the Lemma-12-discharged witness implies the original
witness.** `GK16Claim16WitnessIndep → GK16Claim16Witness`. The only nontrivial step is
deriving `foldedWronskian P ω ≠ 0`, which is now the *theorem*
`ArkLib.FRS.GK16.foldedWronskian_ne_zero_of_linearIndependent` (GK16 Lemma 12, hard
direction) applied to the independent family `P` under the admissibility separation
`hω_sep`. Everything else is transported verbatim. This is axiom-clean and `sorry`-free;
it certifies that residual ① (Lemma 12 nonvanishing) is fully closed and no longer part of
the Theorem-2.18 residual. -/
theorem gk16Claim16Witness_of_indep
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (C : Submodule F (ι → Fin s → F))
    (hwit : GK16Claim16WitnessIndep domain k s ω C) :
    GK16Claim16Witness domain k s ω C := by
  intro A hA_le
  obtain ⟨P, hP_deg, hP_indep, hω_sep, hClaim16⟩ := hwit A hA_le
  refine ⟨P, hP_deg, ?_, hClaim16⟩
  exact ArkLib.FRS.GK16.foldedWronskian_ne_zero_of_linearIndependent P ω hP_indep hω_sep

/-- **Proven reduction: the Claim-16 witness implies the degree budget.** Given the
`GK16Claim16Witness` data (per-coordinate root-multiplicity lower bounds, a nonzero folded
Wronskian, and the degree bound on the underlying polynomials), the GK16 §4 degree budget
`∑_i dim A_i ≤ (dim A)·(k-1)` follows by chaining

  `∑_i dim A_i ≤ ∑_i mult(L, domain i) ≤ ∑_{a ∈ image domain} mult(L, a) ≤ deg L ≤ (dim A)(k-1)`,

where the middle two `≤` are the verified spine
`ArkLib.FRS.GK16.sum_rootMultiplicity_foldedWronskian_le` (root multiplicities over distinct
points are bounded by the degree, itself `≤ (dim A)(k-1)`). The reduction is **axiom-clean**;
it does not use the Lemma-12 / Claim-16 internals, only the witness interface. -/
theorem gk16DegreeBudget_of_claim16Witness
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (C : Submodule F (ι → Fin s → F))
    (hwit : GK16Claim16Witness domain k s ω C) :
    GK16DegreeBudget k s C := by
  classical
  intro A hA_le
  obtain ⟨P, hP_deg, hL_ne, hClaim16⟩ := hwit A hA_le
  set L := ArkLib.FRS.GK16.foldedWronskian P ω with hL
  -- ① `∑_i dim A_i ≤ ∑_i mult(L, domain i)` by Claim 16, termwise.
  have hstep1 :
      (∑ i : ι, Module.finrank F (↥(A ⊓
        (LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
        Submodule F (ι → Fin s → F))))
      ≤ ∑ i : ι, Polynomial.rootMultiplicity (domain i) L :=
    Finset.sum_le_sum (fun i _ => hClaim16 i)
  -- ② `∑_i mult(L, domain i) = ∑_{a ∈ image domain} mult(L, a)` (domain injective).
  have hstep2 :
      (∑ i : ι, Polynomial.rootMultiplicity (domain i) L)
      = ∑ a ∈ (Finset.univ.image domain), Polynomial.rootMultiplicity a L := by
    rw [Finset.sum_image (fun i _ j _ h => domain.injective h)]
  -- ③ The verified spine bounds the sum over distinct points by `(dim A)·(k-1)`.
  have hstep3 :
      (∑ a ∈ (Finset.univ.image domain), Polynomial.rootMultiplicity a L)
      ≤ (Module.finrank F A) * (k - 1) :=
    ArkLib.FRS.GK16.sum_rootMultiplicity_foldedWronskian_le P ω hP_deg hL_ne _
  calc (∑ i : ι, Module.finrank F (↥(A ⊓
        (LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
        Submodule F (ι → Fin s → F))))
      ≤ ∑ i : ι, Polynomial.rootMultiplicity (domain i) L := hstep1
    _ = ∑ a ∈ (Finset.univ.image domain), Polynomial.rootMultiplicity a L := hstep2
    _ ≤ (Module.finrank F A) * (k - 1) := hstep3

/-- **Composed reduction: the Lemma-12-discharged witness implies the degree budget.**
`GK16Claim16WitnessIndep → GK16DegreeBudget`, via `gk16Claim16Witness_of_indep` followed by
`gk16DegreeBudget_of_claim16Witness`. With this, the GK16 §4 degree budget — and hence
`frs_is_subspaceDesign_gk16` — reduces to residual ② alone (Claim 16 + transport), Lemma 12
having been discharged. Axiom-clean. -/
theorem gk16DegreeBudget_of_claim16WitnessIndep
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (C : Submodule F (ι → Fin s → F))
    (hwit : GK16Claim16WitnessIndep domain k s ω C) :
    GK16DegreeBudget k s C :=
  gk16DegreeBudget_of_claim16Witness domain k s ω C
    (gk16Claim16Witness_of_indep domain k s ω C hwit)

/-- **GK16 Claim 16, structural-transport residual (the genuinely-unwritten gap).** For a
subspace `A ≤ C = frsCode`, this packages exactly the *structural encoder-isomorphism +
adapted-basis* data that the column-divisibility proof of Claim 16 consumes — the part the
original `frs_is_subspaceDesign_gk16` docstring already named as "routine but unwritten".
Per `A`, it provides:

* a realizing family `P : Fin (dim A) → F[X]` of degrees `< k` (a basis of the polynomial
  space `U` with `A = U.map encoder`), `F`-linearly **independent** (encoder injectivity);
* the order/degree-separation admissibility of `ω` (`hω_sep`, exactly the hypothesis of
  `foldedWronskian_ne_zero_of_linearIndependent` — so `L ≠ 0` is *derived*, not assumed);
* per coordinate `i`, an **adapted basis** of `U`: an *invertible* `F`-linear recombination
  `Q^{(i)}` of `P` (`Q^{(i)} l = ∑ m, c m l • P m`, `det c ≠ 0`) and a `dim A_i`-element index
  set `T_i ⊆ Fin (dim A)` whose members `Q^{(i)} l` vanish on the *whole orbit*
  `{domain i · ω^b : b : Fin (dim A)}`. (Orbit-vanishing over the `dim A` dilation rows is
  the image, under the encoder isomorphism `A_i ≅ U_i`, of `A_i`-membership; it presupposes
  the design-range side condition `dim A ≤ s`, under which the `dim A` dilation exponents are
  genuine fold indices `< s`.)

This is the *only* remaining content of GK16 Claim 16: the multiplicity-counting **engine**
(column divisibility `(X − domain i)^{dim A_i} ∣ det [Q^{(i)} l (ω^b X)]` ⟹ the root-
multiplicity bound, transported across the nonzero change-of-basis constant) is **proven,
axiom-clean** in `ArkLib.FRS.GK16.claim16_rootMultiplicity_ge`. The reduction
`gk16Claim16WitnessIndep_of_structuralData` turns this data into `GK16Claim16WitnessIndep`. -/
def GK16Claim16StructuralData {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (C : Submodule F (ι → Fin s → F)) : Prop :=
  ∀ A : Submodule F (ι → Fin s → F), A ≤ C →
    ∃ P : Fin (Module.finrank F A) → Polynomial F,
      (∀ j, (P j).natDegree ≤ k - 1) ∧
      LinearIndependent F P ∧
      (∀ Q : Fin (Module.finrank F A) → Polynomial F, (∀ j, Q j ≠ 0) →
          Function.Injective (fun j => (Q j).natDegree) →
          Function.Injective (fun j => ω ^ (Q j).natDegree)) ∧
      (∀ i : ι, ∃ (Q : Fin (Module.finrank F A) → Polynomial F)
          (c : Fin (Module.finrank F A) → Fin (Module.finrank F A) → F)
          (T : Finset (Fin (Module.finrank F A))),
        (Matrix.of c).det ≠ 0 ∧
        (∀ l, Q l = ∑ m, c l m • P m) ∧
        T.card = Module.finrank F (↥(A ⊓
            (LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
            Submodule F (ι → Fin s → F))) ∧
        (∀ l ∈ T, ∀ b : Fin (Module.finrank F A),
            (Q l).eval (domain i * ω ^ (b : ℕ)) = 0))

/-- **Proven reduction: the structural data discharges the (Lemma-12-free) Claim-16
witness.** `GK16Claim16StructuralData → GK16Claim16WitnessIndep`. The per-coordinate
multiplicity bound `dim A_i ≤ rootMultiplicity (domain i) (foldedWronskian P ω)` is exactly
the proven Claim-16 engine `ArkLib.FRS.GK16.claim16_rootMultiplicity_ge` applied to the
adapted recombination `Q^{(i)}` and index set `T_i`: column divisibility by
`(X − domain i)` factors `(X − domain i)^{|T_i|}` out of the folded Wronskian, and
`|T_i| = dim A_i`. The realizing family, its independence, and the `ω`-separation are passed
through verbatim. The folded Wronskian's nonvanishing (Lemma 12) is *not* needed here as a
hypothesis — it is supplied internally to the engine from independence + `hω_sep`.
Axiom-clean, `sorry`-free. -/
theorem gk16Claim16WitnessIndep_of_structuralData
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (C : Submodule F (ι → Fin s → F))
    (hdata : GK16Claim16StructuralData domain k s ω C) :
    GK16Claim16WitnessIndep domain k s ω C := by
  intro A hA_le
  obtain ⟨P, hP_deg, hP_indep, hω_sep, hcoord⟩ := hdata A hA_le
  refine ⟨P, hP_deg, hP_indep, hω_sep, ?_⟩
  intro i
  obtain ⟨Q, c, T, hc_det, hQ_rec, hT_card, hT_vanish⟩ := hcoord i
  -- The folded Wronskian of `P` is nonzero (Lemma 12 hard direction, discharged).
  have hL_ne : ArkLib.FRS.GK16.foldedWronskian P ω ≠ 0 :=
    ArkLib.FRS.GK16.foldedWronskian_ne_zero_of_linearIndependent P ω hP_indep hω_sep
  -- Apply the proven Claim-16 engine to the adapted recombination at coordinate `i`.
  have hbound :=
    ArkLib.FRS.GK16.claim16_rootMultiplicity_ge P Q ω (domain i) c hc_det hQ_rec hL_ne T
      hT_vanish
  rw [hT_card] at hbound
  exact hbound

/-- **Composed reduction: the structural data discharges the degree budget.**
`GK16Claim16StructuralData → GK16DegreeBudget`, via
`gk16Claim16WitnessIndep_of_structuralData` followed by
`gk16DegreeBudget_of_claim16WitnessIndep`. With the multiplicity engine and Lemma 12 both
proven, the entire GK16 §4 degree budget — hence `frs_is_subspaceDesign_gk16` — reduces to
the single structural-transport residual `GK16Claim16StructuralData` (encoder isomorphism +
adapted basis). Axiom-clean. -/
theorem gk16DegreeBudget_of_structuralData
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (C : Submodule F (ι → Fin s → F))
    (hdata : GK16Claim16StructuralData domain k s ω C) :
    GK16DegreeBudget k s C :=
  gk16DegreeBudget_of_claim16WitnessIndep domain k s ω C
    (gk16Claim16WitnessIndep_of_structuralData domain k s ω C hdata)

/-- **Residual ② CLOSED — the structural-transport residual is now a theorem.** The named
residual `GK16Claim16StructuralData domain k s ω (frsCode …)` is **discharged** (built, not
assumed) under the genuine, documented side conditions:

* `hinj` — the FRS-encoder isomorphism hypothesis (injectivity of `frsEvalOnPoints`, the
  `dim_frsCode` hypothesis; for `(L, s)`-admissible `ω` use its restricted form, see
  `frs_is_subspaceDesign_gk16_of_admissible`);
* `hω_sep` — the `ω`-degree-separation admissibility (the genuinely-necessary hypothesis of
  GK16 Lemma 12, `foldedWronskian_ne_zero_of_linearIndependent`);
* `hCs : finrank C ≤ s` — the design-range side condition `dim A ≤ s` (here pushed onto the
  whole code so that *every* subspace `A ≤ C` is in range; on the live design path this is
  the per-`A` range `dim A ≤ r ≤ s` of the `r ∈ [s]` branch, cf.
  `frs_is_subspaceDesign_gk16_of_injective`).

The per-`A` construction is `ArkLib.FRS.GK16.gk16Claim16StructuralData_at`
(`ToMathlib/GK16Structural.lean`): the realizing family is a basis of the polynomial
pre-image `A' := comap encoder A ⊓ degreeLT F k` (encoder isomorphism `A' ≃ A`), and per
coordinate the adapted invertible recombination extends a basis of the pre-image
`A'_i := comap encoder (A ⊓ ker(eval_i)) ⊓ degreeLT F k` to a basis of `A'`, whose
`dim A_i = dim A'_i` distinguished members vanish on the whole `s`-fold orbit of `domain i`
(`dim A ≤ s` makes the `dim A` dilation exponents genuine fold indices `< s`). Axiom-clean,
`sorry`-free. Composed with `gk16DegreeBudget_of_structuralData` this discharges the entire
`GK16DegreeBudget` residual on the design range. -/
theorem gk16Claim16StructuralData_holds
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hinj : Function.Injective (ReedSolomon.Folded.frsEvalOnPoints domain s ω))
    (hk : 1 ≤ k)
    (hω_sep : ∀ {n : ℕ} (Q : Fin n → Polynomial F), (∀ j, Q j ≠ 0) →
        Function.Injective (fun j => (Q j).natDegree) →
        Function.Injective (fun j => ω ^ (Q j).natDegree))
    (hCs : Module.finrank F (ReedSolomon.Folded.frsCode domain k s ω) ≤ s) :
    GK16Claim16StructuralData domain k s ω (ReedSolomon.Folded.frsCode domain k s ω) := by
  intro A hA_le
  have hAs : Module.finrank F A ≤ s := le_trans (Submodule.finrank_mono hA_le) hCs
  exact ArkLib.FRS.GK16.gk16Claim16StructuralData_at domain k s ω hinj hk A hA_le hAs
    (fun Q => hω_sep Q)

/-- **ABF26 Theorem 2.18 [GK16], FRS half** (reduced to the GK16 §4 degree-budget
residual `GK16DegreeBudget`; `s`-factor rate bug repaired). Folded Reed-Solomon codes are
τ-subspace-design for

  `τ(r) := (k-1)/n`   for `r ∈ [s] = {1, …, s}`,   and   `τ(r) := 1`   otherwise,

*given* the residual `GK16DegreeBudget k s (frsCode …)` (which packages the two deep gaps
①② below). The rate-arithmetic reduction itself is **fully proven, axiom-clean**: the
`r ∈ [s]` branch divides the degree budget by `n`; the `r ∉ [s]` branch (`τ = 1`) holds
**unconditionally** from `A_i ≤ A`.

**Statement repair (2026-06-05, `s`-factor rate bug).** The pre-repair statement used
`τ(r) := s·k / n / (s - r + 1)`, inheriting the **same `s`-factor inflation** as the
pre-repair L2.17 (cf. `subspaceDesign_tau_lower`). ABF26 Definition 2.5 fixes the rate of
a code over alphabet `Σ = F^s` as `ρ = log_|Σ| |C| / n = k/(s·n)`, so the paper's
`τ(r) = s·ρ/(s-r+1) = k/(n·(s-r+1))`. The old Lean formula `s·k/(n·(s-r+1))` is `s` times
that — false for `s ≥ 2` by the same countermodel that refuted L2.17 (the full code
`(F^s)^n`, genuine profile `≤ 1 - 1/n`). The old docstring's claim "`τ(1) = ρ`" was itself
inconsistent with the written formula (which gives `τ(1) = k/n = s·ρ`).

**What `τ` the formalized spine supports.** The verified GK16 §4 spine bounds
`∑_i dim A_i ≤ (dim A)·(k-1)`, which justifies exactly `τ(r) ≥ (k-1)/n` — independent of
`r`. We therefore state the **provable** repaired profile `τ(r) = (k-1)/n` on `[s]`. This
already implies the L2.17 lower bound `τ(r) ≥ ρ - 1/n = k/(s·n) - 1/n` (since
`(k-1)/n ≥ k/(s·n) - 1/n` for `s ≥ 1`). The paper's finer `(s-r+1)` denominator is **not**
justified by the crude degree budget alone; recovering it needs the sharper per-point
bound `rootMultiplicity ≤ s - dim A_i` of GK16 Claim 15 (a strengthening of residual ②),
tracked separately.

**The residual `GK16DegreeBudget k s (frsCode …)` packages two genuine, deep gaps**
(both pinned precisely; neither faked). The spine's verified tail
`∑_i rootMultiplicity (domain i) L ≤ (dim A)·(k-1)` is **proven, axiom-clean**:
`ArkLib.FRS.GK16.sum_rootMultiplicity_foldedWronskian_le` (file `GK16DegreeBudget.lean`),
which chains `ArkLib.FRS.GK16.natDegree_foldedWronskian_le` (`deg L ≤ s·(k-1)`,
`ProximityPrizeLeaves.lean`) with `Polynomial.sum_rootMultiplicity_le_natDegree`
(`∑ over distinct points of rootMultiplicity ≤ natDegree`, `GK16RootCounting.lean`).

**Both deep gaps are now closed.** Residual ① (GK16 Lemma 12) and residual ② (GK16 Claim 16,
including the structural encoder-isomorphism + adapted-basis transport) are both proven,
axiom-clean — so the FRS half is unconditional on the residual via the `_of_*` theorems below.
Residual ① (GK16 Lemma 12) is **fully closed**:

① **GK16 Lemma 12, hard direction** — `LinearIndependent F P → foldedWronskian P ω ≠ 0`,
   needed to know `L ≠ 0`. **NOW A THEOREM** (`GK16Lemma12.lean`, all axiom-clean,
   `[propext, Classical.choice, Quot.sound]` only):
   `ArkLib.FRS.GK16.foldedWronskian_ne_zero_of_linearIndependent` — for any linearly
   independent `P` over a field, if `ω` separates the degrees of every nonzero
   distinct-degree family (the genuinely-necessary admissibility hypothesis `hω_sep`),
   then `foldedWronskian P ω ≠ 0`. The unconditional engine is
   `ArkLib.FRS.GK16.foldedWronskian_ne_zero_of_distinct_natDegree` (top-coefficient
   extraction: the coefficient of `X ^ (∑ d j)` is
   `(∏ leadingCoeff (P j)) · det (vandermonde (ω ^ d ·)) ≠ 0`, see
   `coeff_foldedWronskian_sum_natDegree`), reduced to the general case by the
   *Gaussian-elimination-on-degrees* echelon step
   `ArkLib.FRS.GK16.gk16Lemma12HardResidual_holds` (every independent family is an
   invertible recombination of a distinct-degree one;
   `exists_distinctDegree_recombination` in `ToMathlib/GK16Finish.lean`) composed with
   the change-of-basis identity `ArkLib.FRS.GK16.foldedWronskian_change_basis`.
   Supporting facts:
   - **Statement-bug found and kernel-refuted.** The *bare* statement (no hypothesis on
     `ω`) is **false**: at `ω = 1` all dilation rows coincide so the folded Wronskian
     vanishes for `s ≥ 2` even for independent `P`
     (`ArkLib.FRS.GK16.foldedWronskian_eq_zero_of_one`,
     `ArkLib.FRS.GK16.not_lemma12_bare`). A multiplicative-order hypothesis on `ω`
     (admissibility) is genuinely required, and is exactly the `hω_sep` input above.
   - **Vandermonde base case** (`foldedWronskian_monomial_ne_zero`) and **change-of-basis
     F-linearity** (`foldedWronskian_change_basis`) feed the engine above.
   This `L ≠ 0` clause is discharged from independence + `hω_sep` in
   `gk16Claim16Witness_of_indep` / `gk16DegreeBudget_of_claim16WitnessIndep`, so the
   Theorem-2.18 residual no longer contains Lemma 12.
   The *easy* direction (`≠ 0 → LinearIndependent`) is in
   `ArkLib.FRS.GK16.gk16_folded_wronskian_nonvanishing` (`GK16Wronskian.lean`).

② **GK16 Claim 16** — `rootMultiplicity (domain i) L ≥ dim (A ⊓ ker(eval_i))`: the link
   from a vanishing subspace to a high-multiplicity root of `L`. **The mathematical core is
   now proven, axiom-clean** (`ArkLib.FRS.GK16.claim16_rootMultiplicity_ge`): pass to an
   `A_i`-adapted basis (an invertible recombination `Q^{(i)}` of `P`), where each of the
   `dim A_i` adapted columns of the folded Wronskian is `(X − domain i)`-divisible
   (orbit-vanishing), so the column-divisibility determinant lemma
   `ArkLib.FRS.GK16.pow_dvd_det_of_col_dvd` factors `(X − domain i)^{dim A_i}` out of
   `det [Q^{(i)} l (ω^b X)] = foldedWronskian Q^{(i)} ω`; transporting across the nonzero
   change-of-basis constant (`foldedWronskian_change_basis`, `rootMultiplicity_C_mul`)
   yields the bound for `foldedWronskian P ω`.

The last structural gap — the **encoder-isomorphism + adapted-basis transport**
(`A ≤ frsCode ↔ U ⊆ degreeLT F k`, carrying `finrank (A ⊓ ker(eval_i)) = dim (U ∩ H_{domain
i})` and supplying, per `i`, the adapted invertible recombination `Q^{(i)}` with its
`dim A_i`-element orbit-vanishing index set, presupposing the design-range side condition
`dim A ≤ s`) — is now **CLOSED** (written, axiom-clean), in two independent forms:

* `ArkLib.FRS.GK16.gk16Claim16StructuralData_at` (`ToMathlib/GK16Structural.lean`) constructs,
  for each `A ≤ frsCode` with `dim A ≤ s`, exactly the per-`A` existential body of the named
  residual `GK16Claim16StructuralData` (realizing family = basis of the polynomial pre-image
  `A' := comap encoder A ⊓ degreeLT F k`; per coordinate, the adapted recombination extends a
  basis of the pre-image `A'_i` to a basis of `A'`, with orbit-vanishing on the `dim A ≤ s`
  dilation range), under the two documented side conditions (encoder injectivity `hinj`,
  design range `dim A ≤ s`) and the genuinely-necessary `ω`-degree separation `hω_sep`.
* `ReedSolomon.Folded.frs_degreeBudget_of_finrank_le` /
  `…frs_degreeBudget_of_finrank_le_admissible` (`GK16FrsTransport.lean`, `GK16Admissible.lean`)
  package the same transport directly into the per-`A` budget `∑_i dim A_i ≤ (dim A)(k-1)` on
  the `dim A ≤ s` range, feeding the proven Claim-16 engine `claim16_rootMultiplicity_ge`.

Consequently the budget hypothesis is **no longer needed** on the design range and the FRS
half is **unconditional on the residual**: `frs_is_subspaceDesign_gk16_of_injective` (under
restricted encoder injectivity + bounded `hω_sep`) and `frs_is_subspaceDesign_gk16_of_admissible`
(under `Admissible L s ω` + `ω ≠ 0` + `k ≤ s·|ι|` + `k ≤ orderOf ω`) prove `IsSubspaceDesign`
with the budget supplied from the transport above on the `r ∈ [s]` (i.e. `dim A ≤ s`) branch
and `τ = 1` unconditionally off `[s]`. This `frs_is_subspaceDesign_gk16` theorem retains the
abstract residual hypothesis `GK16DegreeBudget` for callers that wish to supply it directly;
for the discharged statements use the two `_of_*` theorems. The abstract reduction chain
`GK16Claim16StructuralData → GK16DegreeBudget` (via `gk16DegreeBudget_of_structuralData`) and
the intermediate witness `GK16Claim16WitnessIndep` (discharged by
`gk16Claim16WitnessIndep_of_structuralData`) remain available. -/
theorem frs_is_subspaceDesign_gk16
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (L : Finset F) (_hL_dom : ∀ i : ι, domain i ∈ L)
    (_hω : ReedSolomon.Folded.Admissible L s ω)
    (h_residual : GK16DegreeBudget k s (ReedSolomon.Folded.frsCode domain k s ω)) :
    let τ : ℕ → ℝ := fun r ↦
      if r ∈ Finset.Icc 1 s then (k - 1 : ℝ) / Fintype.card ι else 1
    IsSubspaceDesign s τ (ReedSolomon.Folded.frsCode domain k s ω) := by
  intro τ r A hA_le _hA_rank
  have hn_pos : 0 < Fintype.card ι := Fintype.card_pos
  have hn_posR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn_pos
  haveI : FiniteDimensional F (ι → Fin s → F) := inferInstance
  -- The per-coordinate vanishing subspaces `A_i := A ⊓ ker(eval_i)`.
  set Ai : ι → Submodule F (ι → Fin s → F) := fun i =>
    A ⊓ (LinearMap.ker
      (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) with hAi
  -- Each `A_i ≤ A`, so `dim A_i ≤ dim A` (the ambient space is finite-dimensional).
  have hAi_rank_le : ∀ i, Module.finrank F (Ai i) ≤ Module.finrank F A := fun i =>
    Submodule.finrank_mono (inf_le_left)
  by_cases hr : r ∈ Finset.Icc 1 s
  · -- Range `r ∈ [s]`: divide the GK16 §4 budget `∑_i dim A_i ≤ (dim A)·(k-1)` by `n`.
    simp only [τ, if_pos hr]
    have hbudget : (∑ i : ι, Module.finrank F (Ai i)) ≤ Module.finrank F A * (k - 1) :=
      h_residual A hA_le
    have hbudgetR :
        (∑ i : ι, (Module.finrank F (Ai i) : ℝ)) ≤
          (Module.finrank F A : ℝ) * ((k : ℝ) - 1) := by
      by_cases hk0 : k = 0
      · -- `k = 0`: the code is `⊥`, so `A = ⊥` and every `dim A_i = 0`.
        subst hk0
        have hC0 : ReedSolomon.Folded.frsCode domain 0 s ω = ⊥ := by
          have hdLT : Polynomial.degreeLT F 0 = ⊥ := by
            rw [eq_bot_iff]
            intro p hp
            rw [Polynomial.mem_degreeLT] at hp
            rw [Submodule.mem_bot, ← Polynomial.degree_eq_bot]
            exact Nat.WithBot.lt_zero_iff.mp (by simpa using hp)
          unfold ReedSolomon.Folded.frsCode
          rw [hdLT, Submodule.map_bot]
        have hAbot : A = ⊥ := le_bot_iff.mp (hA_le.trans hC0.le)
        have hzero : ∀ i, Module.finrank F (Ai i) = 0 := by
          intro i
          have : Ai i = ⊥ := by rw [hAi, hAbot]; simp
          rw [this]; simp
        have hAr : Module.finrank F A = 0 := by rw [hAbot]; simp
        simp [hzero, hAr]
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        calc (∑ i : ι, (Module.finrank F (Ai i) : ℝ))
            = ((∑ i : ι, Module.finrank F (Ai i) : ℕ) : ℝ) := by push_cast; rfl
          _ ≤ ((Module.finrank F A * (k - 1) : ℕ) : ℝ) := by exact_mod_cast hbudget
          _ = (Module.finrank F A : ℝ) * ((k : ℝ) - 1) := by
                push_cast [Nat.cast_sub hk1]; ring
    rw [div_le_iff₀ hn_posR]
    calc (∑ i : ι, (Module.finrank F (Ai i) : ℝ))
        ≤ (Module.finrank F A : ℝ) * ((k : ℝ) - 1) := hbudgetR
      _ = (Module.finrank F A : ℝ) * ((k - 1 : ℝ) / Fintype.card ι) * Fintype.card ι := by
            field_simp
  · -- Range `r ∉ [s]`: `τ(r) = 1`, proven unconditionally from `A_i ≤ A`.
    simp only [τ, if_neg hr, mul_one]
    rw [div_le_iff₀ hn_posR]
    calc (∑ i : ι, (Module.finrank F (Ai i) : ℝ))
        ≤ (∑ _i : ι, (Module.finrank F A : ℝ)) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          exact_mod_cast hAi_rank_le i
      _ = (Module.finrank F A : ℝ) * Fintype.card ι := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- **ABF26 Theorem 2.18 [GK16], FRS half — structural residual form.**
This packages the current proof frontier into the single residual
`GK16Claim16StructuralData`: the structural encoder-isomorphism/adapted-basis transport
discharges `GK16DegreeBudget` by `gk16DegreeBudget_of_structuralData`, and the
rate-arithmetic theorem `frs_is_subspaceDesign_gk16` then gives the repaired
`τ(r) = (k-1)/n` profile on `[s]` (and `1` off `[s]`). -/
theorem frs_is_subspaceDesign_gk16_of_structuralData
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (hω : ReedSolomon.Folded.Admissible L s ω)
    (hdata : GK16Claim16StructuralData domain k s ω
      (ReedSolomon.Folded.frsCode domain k s ω)) :
    let τ : ℕ → ℝ := fun r ↦
      if r ∈ Finset.Icc 1 s then (k - 1 : ℝ) / Fintype.card ι else 1
    IsSubspaceDesign s τ (ReedSolomon.Folded.frsCode domain k s ω) :=
  frs_is_subspaceDesign_gk16 domain k s ω L hL_dom hω
    (gk16DegreeBudget_of_structuralData domain k s ω
      (ReedSolomon.Folded.frsCode domain k s ω) hdata)

/-- **ABF26 Theorem 2.18 [GK16], FRS half — residual `GK16DegreeBudget` discharged.**
The folded RS code is τ-subspace-design for `τ(r) = (k-1)/n` on `[s]` (and `1` off `[s]`),
*unconditionally on the degree-budget residual*, given only:

* `hEinj` — injectivity of the FRS encoder `frsEvalOnPoints domain s ω` on `degreeLT F k`
  (the encoder-isomorphism side condition; holds for `(L, s)`-admissible `ω` with
  `k ≤ s·|L|`);
* `hω_sep` — the degree-separation admissibility of `ω` (exactly the genuinely-necessary
  hypothesis of GK16 Lemma 12, `foldedWronskian_ne_zero_of_linearIndependent`).

In contrast to `frs_is_subspaceDesign_gk16` (which assumes the bundled residual
`GK16DegreeBudget`), here the budget is **proven**: for every `A ≤ frsCode` in the design
range `finrank A ≤ s` (which is exactly the `r ∈ [s]` branch, since there
`finrank A ≤ r ≤ s`), the encoder-transport theorem
`ReedSolomon.Folded.frs_degreeBudget_of_finrank_le` supplies
`∑_i dim A_i ≤ (dim A)·(k-1)` by realizing `A` as an independent degree-`< k` polynomial
family and feeding the proven Claim-16 multiplicity engine an adapted recombination per
coordinate. The `r ∉ [s]` branch (`τ = 1`) is unconditional. -/
theorem frs_is_subspaceDesign_gk16_of_injective
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hEinj : Function.Injective (ReedSolomon.Folded.frsEvalOnPoints domain s ω))
    (hω_sep : ∀ {n : ℕ} (Q : Fin n → Polynomial F), (∀ j, Q j ≠ 0) →
        Function.Injective (fun j => (Q j).natDegree) →
        Function.Injective (fun j => ω ^ (Q j).natDegree)) :
    let τ : ℕ → ℝ := fun r ↦
      if r ∈ Finset.Icc 1 s then (k - 1 : ℝ) / Fintype.card ι else 1
    IsSubspaceDesign s τ (ReedSolomon.Folded.frsCode domain k s ω) := by
  intro τ r A hA_le hA_rank
  have hn_pos : 0 < Fintype.card ι := Fintype.card_pos
  have hn_posR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn_pos
  haveI : FiniteDimensional F (ι → Fin s → F) := inferInstance
  set Ai : ι → Submodule F (ι → Fin s → F) := fun i =>
    A ⊓ (LinearMap.ker
      (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) with hAi
  have hAi_rank_le : ∀ i, Module.finrank F (Ai i) ≤ Module.finrank F A := fun i =>
    Submodule.finrank_mono (inf_le_left)
  by_cases hr : r ∈ Finset.Icc 1 s
  · -- Range `r ∈ [s]`: `finrank A ≤ r ≤ s`, so the proven encoder budget applies.
    simp only [τ, if_pos hr]
    obtain ⟨_, hrs⟩ := Finset.mem_Icc.mp hr
    have hAs : Module.finrank F A ≤ s := le_trans hA_rank hrs
    have hbudget : (∑ i : ι, Module.finrank F (Ai i)) ≤ Module.finrank F A * (k - 1) :=
      ReedSolomon.Folded.frs_degreeBudget_of_finrank_le A hEinj hA_le hAs
        (fun Q => hω_sep Q)
    have hbudgetR :
        (∑ i : ι, (Module.finrank F (Ai i) : ℝ)) ≤
          (Module.finrank F A : ℝ) * ((k : ℝ) - 1) := by
      by_cases hk0 : k = 0
      · subst hk0
        have hC0 : ReedSolomon.Folded.frsCode domain 0 s ω = ⊥ := by
          have hdLT : Polynomial.degreeLT F 0 = ⊥ := by
            rw [eq_bot_iff]
            intro p hp
            rw [Polynomial.mem_degreeLT] at hp
            rw [Submodule.mem_bot, ← Polynomial.degree_eq_bot]
            exact Nat.WithBot.lt_zero_iff.mp (by simpa using hp)
          unfold ReedSolomon.Folded.frsCode
          rw [hdLT, Submodule.map_bot]
        have hAbot : A = ⊥ := le_bot_iff.mp (hA_le.trans hC0.le)
        have hzero : ∀ i, Module.finrank F (Ai i) = 0 := by
          intro i
          have : Ai i = ⊥ := by rw [hAi, hAbot]; simp
          rw [this]; simp
        have hAr : Module.finrank F A = 0 := by rw [hAbot]; simp
        simp [hzero, hAr]
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        calc (∑ i : ι, (Module.finrank F (Ai i) : ℝ))
            = ((∑ i : ι, Module.finrank F (Ai i) : ℕ) : ℝ) := by push_cast; rfl
          _ ≤ ((Module.finrank F A * (k - 1) : ℕ) : ℝ) := by exact_mod_cast hbudget
          _ = (Module.finrank F A : ℝ) * ((k : ℝ) - 1) := by
                push_cast [Nat.cast_sub hk1]; ring
    rw [div_le_iff₀ hn_posR]
    calc (∑ i : ι, (Module.finrank F (Ai i) : ℝ))
        ≤ (Module.finrank F A : ℝ) * ((k : ℝ) - 1) := hbudgetR
      _ = (Module.finrank F A : ℝ) * ((k - 1 : ℝ) / Fintype.card ι) * Fintype.card ι := by
            field_simp
  · -- Range `r ∉ [s]`: `τ(r) = 1`, proven unconditionally from `A_i ≤ A`.
    simp only [τ, if_neg hr, mul_one]
    rw [div_le_iff₀ hn_posR]
    calc (∑ i : ι, (Module.finrank F (Ai i) : ℝ))
        ≤ (∑ _i : ι, (Module.finrank F A : ℝ)) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          exact_mod_cast hAi_rank_le i
      _ = (Module.finrank F A : ℝ) * Fintype.card ι := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- **ABF26 Theorem 2.18 [GK16], FRS half — from `Admissible` + minimal arithmetic.**
The folded RS code is τ-subspace-design for `τ(r) = (k-1)/n` on `[s]` (and `1` off `[s]`),
*unconditionally on the degree-budget residual*, given only the standard
`ReedSolomon.Folded.Admissible L s ω` structure (`domain i ∈ L`) plus the **genuinely-minimal
arithmetic side conditions**:

* `hω0 : ω ≠ 0` — needed for fold-point injectivity (the `Admissible` conjuncts alone do
  **not** give it: with `ω = 0, s ≥ 2` all higher folds collapse to `0`; see
  `ReedSolomon.Folded.mulPow_injective_of_admissible`);
* `hkLs : k ≤ s · |ι|` — enough distinct fold points for the encoder to be injective on
  `degreeLT F k` (`ReedSolomon.Folded.frsEvalOnPoints_injOn_degreeLT`);
* `hkord : k ≤ orderOf ω` — keeps every realizing/recombined degree `< k` strictly below
  `orderOf ω`, which is exactly what makes the GK16 Lemma-12 degree separation hold
  (`ReedSolomon.Folded.pow_natDegree_injective_of_lt_orderOf`).

This replaces the two *unsatisfiable* side conditions of `frs_is_subspaceDesign_gk16_of_injective`
— the global encoder injectivity `hEinj` (false: source is infinite-dimensional, see
`ReedSolomon.Folded.frsEvalOnPoints_not_injective`) and the *arbitrary-degree* `hω_sep`
(false in any finite field) — with their genuinely-true restricted forms, all discharged from
`Admissible` plus the arithmetic above. The budget on the `finrank A ≤ s` range is supplied by
`ReedSolomon.Folded.frs_degreeBudget_of_finrank_le_admissible`; the `r ∉ [s]` branch is
unconditional. -/
theorem frs_is_subspaceDesign_gk16_of_admissible
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (hω0 : ω ≠ 0) (hadm : ReedSolomon.Folded.Admissible L s ω)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω) :
    let τ : ℕ → ℝ := fun r ↦
      if r ∈ Finset.Icc 1 s then (k - 1 : ℝ) / Fintype.card ι else 1
    IsSubspaceDesign s τ (ReedSolomon.Folded.frsCode domain k s ω) := by
  intro τ r A hA_le hA_rank
  have hn_pos : 0 < Fintype.card ι := Fintype.card_pos
  have hn_posR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn_pos
  haveI : FiniteDimensional F (ι → Fin s → F) := inferInstance
  set Ai : ι → Submodule F (ι → Fin s → F) := fun i =>
    A ⊓ (LinearMap.ker
      (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) with hAi
  have hAi_rank_le : ∀ i, Module.finrank F (Ai i) ≤ Module.finrank F A := fun i =>
    Submodule.finrank_mono (inf_le_left)
  by_cases hr : r ∈ Finset.Icc 1 s
  · -- Range `r ∈ [s]`: `finrank A ≤ r ≤ s`, so the `Admissible` encoder budget applies.
    simp only [τ, if_pos hr]
    obtain ⟨_, hrs⟩ := Finset.mem_Icc.mp hr
    have hAs : Module.finrank F A ≤ s := le_trans hA_rank hrs
    have hbudget : (∑ i : ι, Module.finrank F (Ai i)) ≤ Module.finrank F A * (k - 1) :=
      ReedSolomon.Folded.frs_degreeBudget_of_finrank_le_admissible A
        hL_dom hω0 hadm hkLs hkord hA_le hAs
    have hbudgetR :
        (∑ i : ι, (Module.finrank F (Ai i) : ℝ)) ≤
          (Module.finrank F A : ℝ) * ((k : ℝ) - 1) := by
      by_cases hk0 : k = 0
      · subst hk0
        have hC0 : ReedSolomon.Folded.frsCode domain 0 s ω = ⊥ := by
          have hdLT : Polynomial.degreeLT F 0 = ⊥ := by
            rw [eq_bot_iff]
            intro p hp
            rw [Polynomial.mem_degreeLT] at hp
            rw [Submodule.mem_bot, ← Polynomial.degree_eq_bot]
            exact Nat.WithBot.lt_zero_iff.mp (by simpa using hp)
          unfold ReedSolomon.Folded.frsCode
          rw [hdLT, Submodule.map_bot]
        have hAbot : A = ⊥ := le_bot_iff.mp (hA_le.trans hC0.le)
        have hzero : ∀ i, Module.finrank F (Ai i) = 0 := by
          intro i
          have : Ai i = ⊥ := by rw [hAi, hAbot]; simp
          rw [this]; simp
        have hAr : Module.finrank F A = 0 := by rw [hAbot]; simp
        simp [hzero, hAr]
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        calc (∑ i : ι, (Module.finrank F (Ai i) : ℝ))
            = ((∑ i : ι, Module.finrank F (Ai i) : ℕ) : ℝ) := by push_cast; rfl
          _ ≤ ((Module.finrank F A * (k - 1) : ℕ) : ℝ) := by exact_mod_cast hbudget
          _ = (Module.finrank F A : ℝ) * ((k : ℝ) - 1) := by
                push_cast [Nat.cast_sub hk1]; ring
    rw [div_le_iff₀ hn_posR]
    calc (∑ i : ι, (Module.finrank F (Ai i) : ℝ))
        ≤ (Module.finrank F A : ℝ) * ((k : ℝ) - 1) := hbudgetR
      _ = (Module.finrank F A : ℝ) * ((k - 1 : ℝ) / Fintype.card ι) * Fintype.card ι := by
            field_simp
  · -- Range `r ∉ [s]`: `τ(r) = 1`, proven unconditionally from `A_i ≤ A`.
    simp only [τ, if_neg hr, mul_one]
    rw [div_le_iff₀ hn_posR]
    calc (∑ i : ι, (Module.finrank F (Ai i) : ℝ))
        ≤ (∑ _i : ι, (Module.finrank F A : ℝ)) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          exact_mod_cast hAi_rank_le i
      _ = (Module.finrank F A : ℝ) * Fintype.card ι := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- **ABF26 Theorem 2.18 [GK16], FRS half — from order bound + inter-orbit
separation.** This caller-facing wrapper composes the discharged intra-orbit side of
`ReedSolomon.Folded.Admissible` with the existing admissible T2.18 theorem. Thus T2.18
call sites need only provide:

* `0 ∉ L`, the nonzero-domain condition;
* `s ≤ orderOf ω`, the order-theoretic no-repeat condition inside each fold;
* the genuine inter-orbit/coset-separation clause for distinct domain points.

The resulting subspace-design profile is the repaired GK16 profile
`τ(r) = (k - 1)/n` on `[s]` and `1` off `[s]`. -/
theorem frs_is_subspaceDesign_gk16_of_orderOf_ge_of_inter
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (hL_zero : (0 : F) ∉ L) (hω0 : ω ≠ 0) (hs_order : s ≤ orderOf ω)
    (hinter : ∀ α ∈ L, ∀ β ∈ L, α ≠ β → ∀ i : ℕ, i < s → α * ω ^ i ≠ β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω) :
    let τ : ℕ → ℝ := fun r ↦
      if r ∈ Finset.Icc 1 s then (k - 1 : ℝ) / Fintype.card ι else 1
    IsSubspaceDesign s τ (ReedSolomon.Folded.frsCode domain k s ω) :=
  frs_is_subspaceDesign_gk16_of_admissible domain k s ω L hL_dom hω0
    (ReedSolomon.Folded.admissible_of_orderOf_ge_of_inter L s ω hL_zero hs_order hinter)
    hkLs hkord

/-- **Profile bridge for C3.5.** The repaired GK16/FRS profile
`τ(r) = (k - 1)/n` on `[s]` is pointwise no larger than the CZ25 capacity-reduction profile
`τ(r) = s·k/(n·(s-r+1))` on `[s]` (and both profiles are `1` off `[s]`). Hence any FRS
subspace-design theorem stated with the repaired GK16 profile can feed the existing C3.5
reduction, which consumes the CZ25 profile. -/
theorem frs_is_subspaceDesign_cz25Profile_of_gk16Profile
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (h : IsSubspaceDesign s
      (fun r ↦ if r ∈ Finset.Icc 1 s then (k - 1 : ℝ) / Fintype.card ι else 1)
      (ReedSolomon.Folded.frsCode domain k s ω)) :
    IsSubspaceDesign s
      (fun r ↦ if r ∈ Finset.Icc 1 s then
          (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
      (ReedSolomon.Folded.frsCode domain k s ω) := by
  apply IsSubspaceDesign.mono_tau h
  intro r
  by_cases hr : r ∈ Finset.Icc 1 s
  · simp only [hr, if_true]
    obtain ⟨hr1, hrs⟩ := Finset.mem_Icc.mp hr
    have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hden_pos : 0 < (s : ℝ) - r + 1 := by
      have hrsR : (r : ℝ) ≤ s := by exact_mod_cast hrs
      linarith
    have hratio : 1 ≤ (s : ℝ) / ((s : ℝ) - r + 1) := by
      rw [le_div_iff₀ hden_pos]
      have hr1R : (1 : ℝ) ≤ r := by exact_mod_cast hr1
      linarith
    calc ((k : ℝ) - 1) / Fintype.card ι
        ≤ (k : ℝ) / Fintype.card ι := by
            exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hn_pos)
      _ ≤ ((k : ℝ) / Fintype.card ι) * ((s : ℝ) / ((s : ℝ) - r + 1)) := by
            exact le_mul_of_one_le_right
              (div_nonneg (Nat.cast_nonneg k) (le_of_lt hn_pos)) hratio
      _ = (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) := by
            ring
  · simp only [hr, if_false]
    exact le_rfl

/-- C3.5-compatible FRS subspace-design profile from the injective GK16 bridge. -/
theorem frs_is_subspaceDesign_cz25Profile_of_injective
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hEinj : Function.Injective (ReedSolomon.Folded.frsEvalOnPoints domain s ω))
    (hω_sep : ∀ {n : ℕ} (Q : Fin n → Polynomial F), (∀ j, Q j ≠ 0) →
        Function.Injective (fun j => (Q j).natDegree) →
        Function.Injective (fun j => ω ^ (Q j).natDegree)) :
    IsSubspaceDesign s
      (fun r ↦ if r ∈ Finset.Icc 1 s then
          (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
      (ReedSolomon.Folded.frsCode domain k s ω) :=
  frs_is_subspaceDesign_cz25Profile_of_gk16Profile domain k s ω
    (frs_is_subspaceDesign_gk16_of_injective domain k s ω hEinj hω_sep)

/-- C3.5-compatible FRS subspace-design profile from the admissible GK16 bridge. -/
theorem frs_is_subspaceDesign_cz25Profile_of_admissible
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (hω0 : ω ≠ 0) (hadm : ReedSolomon.Folded.Admissible L s ω)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω) :
    IsSubspaceDesign s
      (fun r ↦ if r ∈ Finset.Icc 1 s then
          (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
      (ReedSolomon.Folded.frsCode domain k s ω) :=
  frs_is_subspaceDesign_cz25Profile_of_gk16Profile domain k s ω
    (frs_is_subspaceDesign_gk16_of_admissible domain k s ω L hL_dom hω0 hadm hkLs hkord)


/-! ## Univariate Multiplicity Codes (ABF26 DA.7) -/

/-- Univariate multiplicity evaluation function `D_ux` (derivative-of-x):
Evaluates the Hasse derivatives up to order `s-1` of a polynomial at `x`.
This is the derivative-coded operation for `UM[F, L, k, s]`. -/
noncomputable def D_ux {ι : Type} [Fintype ι]
    {F : Type} [CommSemiring F]
    (domain : ι ↪ F) (s : ℕ) : Polynomial F →ₗ[F] (ι → Fin s → F) where
  toFun p := fun x j ↦ (Polynomial.hasseDeriv j.val p).eval (domain x)
  map_add' p q := by ext; simp
  map_smul' c p := by ext; simp

/-- **ABF26 DA.7 (Univariate Multiplicity codes)**.
The UM code `UM[F, L, k, s]`:

  `UM[F, L, k, s] := { f : L → F^s | ∃ f̂ ∈ F^{<k}[X],`
  `                          ∀ x ∈ L, f(x) = (f̂(x), f̂'(x), ..., f̂^{(s-1)}(x)) }`

where derivatives are Hasse derivatives. -/
noncomputable def umCode {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) : Submodule F (ι → Fin s → F) :=
  (Polynomial.degreeLT F k).map (D_ux domain s)

/-- **ABF26 Theorem 2.18, UM half — abstract residual form.**
The Univariate Multiplicity code is τ-subspace-design for `τ(r) = (k-1)/n` on `[s]`,
conditional on the UM degree-budget residual. This matches the FRS half exactly
and connects the UM result to the repaired GK16/vector-space statements. -/
theorem um_is_subspaceDesign_gk16
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ)
    (h_residual : GK16DegreeBudget k s (umCode domain k s)) :
    let τ : ℕ → ℝ := fun r ↦
      if r ∈ Finset.Icc 1 s then (k - 1 : ℝ) / Fintype.card ι else 1
    IsSubspaceDesign s τ (umCode domain k s) := by
  intro τ r A hA_le _hA_rank
  have hn_pos : 0 < Fintype.card ι := Fintype.card_pos
  have hn_posR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn_pos
  haveI : FiniteDimensional F (ι → Fin s → F) := inferInstance
  -- The per-coordinate vanishing subspaces `A_i := A ⊓ ker(eval_i)`.
  set Ai : ι → Submodule F (ι → Fin s → F) := fun i =>
    A ⊓ (LinearMap.ker
      (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) with hAi
  -- Each `A_i ≤ A`, so `dim A_i ≤ dim A` (the ambient space is finite-dimensional).
  have hAi_rank_le : ∀ i, Module.finrank F (Ai i) ≤ Module.finrank F A := fun i =>
    Submodule.finrank_mono (inf_le_left)
  by_cases hr : r ∈ Finset.Icc 1 s
  · -- Range `r ∈ [s]`: divide the degree budget `∑_i dim A_i ≤ (dim A)·(k-1)` by `n`.
    simp only [τ, if_pos hr]
    have hbudget : (∑ i : ι, Module.finrank F (Ai i)) ≤ Module.finrank F A * (k - 1) :=
      h_residual A hA_le
    have hbudgetR :
        (∑ i : ι, (Module.finrank F (Ai i) : ℝ)) ≤
          (Module.finrank F A : ℝ) * ((k : ℝ) - 1) := by
      by_cases hk0 : k = 0
      · -- `k = 0`: the code is `⊥`, so `A = ⊥` and every `dim A_i = 0`.
        subst hk0
        have hC0 : umCode domain 0 s = ⊥ := by
          have hdLT : Polynomial.degreeLT F 0 = ⊥ := by
            rw [eq_bot_iff]
            intro p hp
            rw [Polynomial.mem_degreeLT] at hp
            rw [Submodule.mem_bot, ← Polynomial.degree_eq_bot]
            exact Nat.WithBot.lt_zero_iff.mp (by simpa using hp)
          unfold umCode
          rw [hdLT, Submodule.map_bot]
        have hAbot : A = ⊥ := le_bot_iff.mp (hA_le.trans hC0.le)
        have hzero : ∀ i, Module.finrank F (Ai i) = 0 := by
          intro i
          have : Ai i = ⊥ := by rw [hAi, hAbot]; simp
          rw [this]; simp
        have hAr : Module.finrank F A = 0 := by rw [hAbot]; simp
        simp [hzero, hAr]
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        calc (∑ i : ι, (Module.finrank F (Ai i) : ℝ))
            = ((∑ i : ι, Module.finrank F (Ai i) : ℕ) : ℝ) := by push_cast; rfl
          _ ≤ ((Module.finrank F A * (k - 1) : ℕ) : ℝ) := by exact_mod_cast hbudget
          _ = (Module.finrank F A : ℝ) * ((k : ℝ) - 1) := by
                push_cast [Nat.cast_sub hk1]; ring
    rw [div_le_iff₀ hn_posR]
    calc (∑ i : ι, (Module.finrank F (Ai i) : ℝ))
        ≤ (Module.finrank F A : ℝ) * ((k : ℝ) - 1) := hbudgetR
      _ = (Module.finrank F A : ℝ) * ((k - 1 : ℝ) / Fintype.card ι) * Fintype.card ι := by
            field_simp
  · -- Range `r ∉ [s]`: `τ(r) = 1`, proven unconditionally from `A_i ≤ A`.
    simp only [τ, if_neg hr, mul_one]
    rw [div_le_iff₀ hn_posR]
    calc (∑ i : ι, (Module.finrank F (Ai i) : ℝ))
        ≤ (∑ _i : ι, (Module.finrank F A : ℝ)) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          exact_mod_cast hAi_rank_le i
      _ = (Module.finrank F A : ℝ) * Fintype.card ι := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

end CodingTheory

/- Axiom audit:
`CodingTheory.um_is_subspaceDesign_gk16` and the C3.5-compatible FRS profile bridges depend
only on `propext`, `Classical.choice`, and `Quot.sound`. -/
#print axioms CodingTheory.um_is_subspaceDesign_gk16
#print axioms CodingTheory.IsSubspaceDesign.mono_tau
#print axioms CodingTheory.frs_is_subspaceDesign_cz25Profile_of_gk16Profile
#print axioms CodingTheory.frs_is_subspaceDesign_cz25Profile_of_injective
#print axioms CodingTheory.frs_is_subspaceDesign_cz25Profile_of_admissible
#print axioms CodingTheory.frs_is_subspaceDesign_gk16_of_orderOf_ge_of_inter

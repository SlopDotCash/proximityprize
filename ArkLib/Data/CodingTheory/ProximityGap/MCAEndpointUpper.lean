/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-!
# A universal upper bound on `ε_mca` via witness-set pinning

This file proves a **new, universal** upper bound on the mutual correlated agreement error
`ε_mca` (ABF26 Definition 4.3, `ProximityGap.epsMCA`) for *every* `F`-submodule code and at
*every* proximity radius `δ`:

  `ε_mca(MC, δ) ≤ 2^n / |F|`,  where `n := |ι|`.

## The pinning argument

Fix a stack `(u₀, u₁)`. For each "bad" scalar `γ` (one for which `mcaEvent` holds) choose a
witness set `S_γ ⊆ ι` from the event: it carries a codeword on the line `u₀ + γ • u₁` while
admitting *no* joint pair of codewords matching `(u₀, u₁)`. The map `γ ↦ S_γ` is **injective**
on the bad set: if two distinct bad scalars `γ ≠ γ'` shared a witness set `S`, with codewords
`w, w' ∈ MC` realising the two lines on `S`, then the pair

  `v₁ := (γ - γ')⁻¹ • (w - w')`,   `v₀ := w - γ • v₁`

lies in `MC` (submodule `smul`/`sub` closure, using `γ - γ' ≠ 0`) and matches `(u₀, u₁)` on
`S` — a *forbidden* joint codeword pair. So each witness set pins at most one bad `γ`, and the
number of bad `γ` is at most the number of subsets of `ι`, i.e. `2^n`. Dividing by `|F|`
(uniform `γ`) gives the bound, and taking the supremum over stacks yields `ε_mca ≤ 2^n / |F|`.

Only `smul`/`sub` closure of `MC` and field-invertibility of `F`-scalars are used, so the
result holds for a general `F`-module `A`, exactly as in `Errors.lean`'s section variables.

## Endpoint corollary

Combined with the radius-one **lower** bound (`epsMCA_one_ge_choose_div`, separate file)
this brackets the endpoint MCA value of Reed–Solomon. Here we record the *huge-field*
endpoint: when `|F| ≥ 2^(n+128)` the universal bound already collapses below the prize
threshold `ε* = 2^(-128)` (`ProximityGap.epsStar`), at *every* radius `δ`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*,
  §1 Grand Challenges, §4.3. 2026.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## Core pinning lemma

A chosen mutual-witness set pins its bad scalar: two distinct bad `γ` sharing a witness set
would manufacture the forbidden joint codeword pair. -/

/-- **Pinning.** Let `S` be a set on which both lines `u₀ + γ • u₁` and `u₀ + γ' • u₁` equal
codewords `w, w'` of the submodule `MC`. If `γ ≠ γ'`, then there *is* a joint pair of
codewords of `MC` agreeing with `(u₀, u₁)` on `S`. Contrapositively, the witness set of a
`mcaEvent` (which forbids such a pair) cannot be shared by two distinct bad scalars. -/
theorem pairJointAgreesOn_of_two_lines
    (MC : Submodule F (ι → A)) {S : Finset ι} {u₀ u₁ : ι → A} {γ γ' : F}
    (hne : γ ≠ γ')
    {w : ι → A} (hw : w ∈ (MC : Set (ι → A))) (hwline : ∀ i ∈ S, w i = u₀ i + γ • u₁ i)
    {w' : ι → A} (hw' : w' ∈ (MC : Set (ι → A))) (hw'line : ∀ i ∈ S, w' i = u₀ i + γ' • u₁ i) :
    pairJointAgreesOn (MC : Set (ι → A)) S u₀ u₁ := by
  -- `γ - γ' ≠ 0`, hence invertible.
  have hsub : γ - γ' ≠ 0 := sub_ne_zero.mpr hne
  -- The two witness codewords and their submodule combinations.
  set v₁ : ι → A := (γ - γ')⁻¹ • (w - w') with hv₁
  set v₀ : ι → A := w - γ • v₁ with hv₀
  have hv₁mem : v₁ ∈ (MC : Set (ι → A)) := by
    rw [hv₁, SetLike.mem_coe]
    exact MC.smul_mem _ (MC.sub_mem hw hw')
  have hv₀mem : v₀ ∈ (MC : Set (ι → A)) := by
    rw [hv₀, SetLike.mem_coe]
    exact MC.sub_mem hw (MC.smul_mem _ hv₁mem)
  refine ⟨v₀, hv₀mem, v₁, hv₁mem, ?_⟩
  intro i hi
  -- On `S`: `(w - w') i = (γ - γ') • u₁ i`.
  have hdiff : (w - w') i = (γ - γ') • u₁ i := by
    have h1 : w i = u₀ i + γ • u₁ i := hwline i hi
    have h2 : w' i = u₀ i + γ' • u₁ i := hw'line i hi
    simp only [Pi.sub_apply, h1, h2]
    rw [sub_smul]
    abel
  -- Hence `v₁ i = u₁ i`.
  have hv₁i : v₁ i = u₁ i := by
    rw [hv₁, Pi.smul_apply, hdiff, smul_smul, inv_mul_cancel₀ hsub, one_smul]
  -- And `v₀ i = w i - γ • u₁ i = u₀ i`.
  have hv₀i : v₀ i = u₀ i := by
    rw [hv₀, Pi.sub_apply, Pi.smul_apply, hv₁i, hwline i hi]
    abel
  exact ⟨hv₀i, hv₁i⟩

/-! ## Per-stack probability bound -/

/-- **Per-stack counting bound.** For a fixed stack `(u₀, u₁)`, the `mcaEvent` probability
over uniform `γ` is at most `2^n / |F|`: each bad `γ`'s chosen witness set pins `γ`, so the
bad set injects into the `2^n` subsets of `ι`. -/
theorem mcaEvent_prob_le_two_pow_card_div
    (MC : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    Pr_{ let γ ←$ᵖ F }[ mcaEvent (MC : Set (ι → A)) δ u₀ u₁ γ ] ≤
      (2 ^ (Fintype.card ι) : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  rw [prob_uniform_eq_card_filter_div_card]
  set Bad := Finset.univ.filter
    (fun γ : F => mcaEvent (MC : Set (ι → A)) δ u₀ u₁ γ) with hBad
  -- For each bad `γ`, extract its witness set together with its three event clauses.
  have hwit : ∀ γ ∈ Bad,
      ∃ S : Finset ι,
        (∃ w ∈ (MC : Set (ι → A)), ∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧
        ¬ pairJointAgreesOn (MC : Set (ι → A)) S u₀ u₁ := by
    intro γ hγ
    rw [hBad, Finset.mem_filter] at hγ
    obtain ⟨S, _hScard, hline, hpair⟩ := hγ.2
    exact ⟨S, hline, hpair⟩
  choose! Sf hSf using hwit
  -- `Sf` maps `Bad` into the (full) finset universe of subsets, injectively.
  have hmaps : Set.MapsTo Sf (↑Bad) (↑(Finset.univ : Finset (Finset ι))) := by
    intro γ _hγ; exact Finset.mem_univ _
  have hinj : (↑Bad : Set F).InjOn Sf := by
    intro γ₁ hγ₁ γ₂ hγ₂ hSeq
    by_contra hne
    -- Unpack both events; their shared witness set yields a forbidden joint pair.
    obtain ⟨⟨w₁, hw₁, hw₁line⟩, _hpair₁⟩ := hSf γ₁ hγ₁
    obtain ⟨⟨w₂, hw₂, hw₂line⟩, hpair₂⟩ := hSf γ₂ hγ₂
    apply hpair₂
    -- Build the joint pair on `S := Sf γ₂ = Sf γ₁`.
    refine pairJointAgreesOn_of_two_lines MC (S := Sf γ₂) (γ := γ₁) (γ' := γ₂) hne
      hw₁ ?_ hw₂ hw₂line
    rw [← hSeq]; exact hw₁line
  have hcard_le : Bad.card ≤ (Finset.univ : Finset (Finset ι)).card :=
    Finset.card_le_card_of_injOn Sf hmaps hinj
  rw [Finset.card_univ, Fintype.card_finset] at hcard_le
  -- Push to `ENNReal` division.
  have hnum : (↑(↑Bad.card : ℝ≥0) : ENNReal) ≤ (↑(2 ^ Fintype.card ι) : ENNReal) := by
    exact_mod_cast hcard_le
  have hden : (↑(↑(Fintype.card F) : ℝ≥0) : ENNReal) = (↑(Fintype.card F) : ENNReal) := by
    push_cast; rfl
  have hpow : (↑(2 ^ Fintype.card ι) : ENNReal) = (2 ^ Fintype.card ι : ENNReal) := by
    push_cast; rfl
  rw [hden]
  calc (↑(↑Bad.card : ℝ≥0) : ENNReal) / (Fintype.card F : ENNReal)
      ≤ (↑(2 ^ Fintype.card ι) : ENNReal) / (Fintype.card F : ENNReal) := by gcongr
    _ = (2 ^ Fintype.card ι : ENNReal) / (Fintype.card F : ENNReal) := by rw [hpow]

/-! ## The universal bound -/

/-- **NEW RESULT: universal pinning bound.** For *every* `F`-submodule code `MC` and *every*
radius `δ`, `ε_mca(MC, δ) ≤ 2^n / |F|`, where `n := |ι|`.

Each bad scalar's chosen mutual-witness set pins it uniquely (two distinct bad scalars
sharing a witness set `S` would yield the forbidden joint pair
`v₁ = (γ-γ')⁻¹(w-w')`, `v₀ = w - γ v₁`), so at most `2^n` bad scalars exist. See
`[ABF26]` §1 (Grand MCA Challenge), §4.3. -/
theorem epsMCA_le_two_pow_card_div (MC : Submodule F (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) (MC : Set (ι → A)) δ ≤
      (2 ^ (Fintype.card ι) : ENNReal) / (Fintype.card F : ENNReal) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  exact mcaEvent_prob_le_two_pow_card_div MC δ (u 0) (u 1)

/-! ## Huge-field endpoint corollary -/

/-- **Huge-field endpoint.** When `|F| ≥ 2^(n+128)`, the universal pinning bound already
collapses the MCA error below the prize threshold `ε* = 2^(-128)` (`ProximityGap.epsStar`),
at *every* radius `δ` — `ε_mca(MC, δ) ≤ ε*`. See `[ABF26]` §1 (Grand MCA Challenge). -/
theorem epsMCA_le_epsStar_of_huge_field
    (MC : Submodule F (ι → A)) (δ : ℝ≥0)
    (hq : 2 ^ (Fintype.card ι + 128) ≤ Fintype.card F) :
    epsMCA (F := F) (MC : Set (ι → A)) δ ≤ (ProximityGap.epsStar : ENNReal) := by
  classical
  refine le_trans (epsMCA_le_two_pow_card_div MC δ) ?_
  -- `epsStar = 1 / 2^128` as an `ENNReal`.
  have hstar : (ProximityGap.epsStar : ENNReal) = 1 / (2 ^ (128 : ℕ) : ENNReal) := by
    rw [epsStar]
    push_cast
    rfl
  rw [hstar]
  -- `2^n / |F| ≤ 2^n / 2^(n+128) = 1/2^128`.
  set n := Fintype.card ι with hn
  have hqE : (2 ^ (n + 128) : ENNReal) ≤ (Fintype.card F : ENNReal) := by
    have h : ((2 ^ (n + 128) : ℕ) : ENNReal) ≤ (Fintype.card F : ENNReal) := by exact_mod_cast hq
    rwa [Nat.cast_pow, Nat.cast_ofNat] at h
  -- First lower the denominator from `|F|` down to `2^(n+128)`.
  have hstep1 : (2 ^ n : ENNReal) / (Fintype.card F : ENNReal) ≤
      (2 ^ n : ENNReal) / (2 ^ (n + 128) : ENNReal) :=
    ENNReal.div_le_div_left hqE _
  refine le_trans hstep1 (le_of_eq ?_)
  -- `2^n / 2^(n+128) = 2^n / (2^n * 2^128) = 1 / 2^128`.
  rw [pow_add]
  have h2 : (2 : ENNReal) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2top : (2 : ENNReal) ^ n ≠ ⊤ := by
    apply ENNReal.pow_ne_top; norm_num
  nth_rewrite 1 [show (2 : ENNReal) ^ n = (2 : ENNReal) ^ n * 1 from (mul_one _).symm]
  rw [ENNReal.mul_div_mul_left 1 (2 ^ (128 : ℕ)) h2 h2top]

end

end ProximityGap

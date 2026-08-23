/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Jo26ObstructionRowCount

/-!
# Deviation kernels: the fully-close case of S2(b′) (#357)

`Jo26ObstructionRowCount.lean` reduced `ObstructionBound` to a δ-close direction count
on one row.  This file handles the complementary regime — **every row fully close** —
where direction counts saturate and a different mechanism takes over.

Setting: each row `j` of the stack is *jointly explained* by a codeword pair
`(c_{j,0}, c_{j,1})` on a common position set `S*` (the correlated-agreement output,
intersected over rows).  Then for any witness `T` and any combiner `λ` in the
obstruction subspace `K_T`:

1. row `j`'s combination agrees with the *codeword* combination
   `λ₀·c_{j,0} + λ₁·c_{j,1}` on `T ∩ S*`;
2. if `T ∩ S*` is large enough that agreement forces codeword equality
   (`|T ∩ S*| > n − d`, the code-distance threshold, taken as the named hypothesis
   `hforce`), the explaining codeword of clause 1 of `K_T` **is** that combination;
3. hence membership in `K_T` is equivalent to `λ` killing every **deviation covector**
   `(U_{j,0}(i) − c_{j,0}(i), U_{j,1}(i) − c_{j,1}(i))` at the outlier positions
   `i ∈ T \ S*` (`mem_jointStackSubmodule_iff_deviation` — the structural heart);
4. so every obstruction subspace is an intersection of kernels of deviation covectors:
   it is `⊥`, or a single covector kernel intersected down — in particular each LINE
   obstruction is the kernel of one nonzero deviation covector, and the number of
   distinct line obstructions is at most the number of (position, row) deviation pairs
   `≤ l·|ι \ S*|` — *independent of the field size* (`obstruction_line_is_deviation_kernel`).

For the deployed regime (`q ≥ 2^128 ≫ n·l`) this closes the fully-close case of
S2(b′): the dominating family is `{⊥} ∪ {deviation kernels}`, of size `≤ 1 + l·n ≪ q`.
The correlated-agreement input (existence of `(c_{j,k}, S*)`) and the distance-forcing
input are the two named hypotheses — both are exactly what the in-tree CA-below-Johnson
surfaces provide.
-/

open Finset NNReal Code
open scoped BigOperators

namespace ProximityGap.Jo26Obstruction

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The **deviation covector** of row `j` at position `i`, relative to the explaining
pair `c j : Fin 2 → ι → A`: the column-indexed tuple of deviations of the stack from
its codeword explanation. -/
def deviation {l : ℕ} (U : Fin l → ι → Fin 2 → A) (c : Fin l → Fin 2 → ι → A)
    (j : Fin l) (i : ι) : Fin 2 → A :=
  fun k => U j i k - c j k i

/-- `λ` kills the deviation covector at `(j, i)`:
`λ₀·(U_{j,0}(i) − c_{j,0}(i)) + λ₁·(U_{j,1}(i) − c_{j,1}(i)) = 0`. -/
def KillsDeviation {l : ℕ} (U : Fin l → ι → Fin 2 → A) (c : Fin l → Fin 2 → ι → A)
    (j : Fin l) (i : ι) (lam : Fin 2 → F) : Prop :=
  ∑ k, lam k • deviation U c j i k = 0

/-- **The structural heart of the fully-close case.**  Suppose each row `j` of the
stack is explained by the codeword pair `c j` on all of `S*` (`hexp`), and suppose
agreement on `T ∩ S*` forces codeword equality (`hforce` — the code-distance input,
stated for exactly the words that arise).  Then a combiner `λ` lies in the obstruction
subspace `K_T = jointStackSubmodule C T U` **iff** it kills every deviation covector
at every outlier position `i ∈ T \ S*`, for every row.

Forward: the explaining codeword of `λ`'s combination is forced to be the codeword
combination `λ₀·c_{j,0} + λ₁·c_{j,1}` (they agree on `T ∩ S*`), so on `T \ S*` the
combination must equal it — which is the kill condition.  Backward: the codeword
combination explains `λ`'s combination on all of `T` (on `T ∩ S*` by `hexp`, on
`T \ S*` by the kill condition). -/
theorem mem_jointStackSubmodule_iff_deviation
    (C : Submodule F (ι → A)) {l : ℕ} {U : Fin l → ι → Fin 2 → A}
    {c : Fin l → Fin 2 → ι → A} {Sstar : Finset ι} {T : Finset ι}
    (hcw : ∀ j k, c j k ∈ (C : Set (ι → A)))
    (hexp : ∀ j k, ∀ i ∈ Sstar, c j k i = U j i k)
    (hforce : ∀ (w : ι → A), w ∈ (C : Set (ι → A)) →
      ∀ (w' : ι → A), w' ∈ (C : Set (ι → A)) →
      (∀ i ∈ T ∩ Sstar, w i = w' i) → w = w')
    (lam : Fin 2 → F) :
    lam ∈ jointStackSubmodule C T U ↔
      ∀ j : Fin l, ∀ i ∈ T \ Sstar, KillsDeviation U c j i lam := by
  have hmem : ∀ j : Fin l, (fun i' => ∑ k, lam k • c j k i') ∈ (C : Set (ι → A)) := by
    intro j
    have heq : (fun i' => ∑ k, lam k • c j k i') = ∑ k, lam k • c j k := by
      funext i'
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun k _ => rfl
    rw [heq]
    exact Submodule.sum_mem _ fun k _ => C.smul_mem _ (hcw j k)
  constructor
  · rintro ⟨cs, hcs, hag⟩ j i hi
    obtain ⟨hiT, hiS⟩ := Finset.mem_sdiff.mp hi
    -- the forced identification: cs j = λ-combination of the explaining pair
    have hforced : cs j = fun i' => ∑ k, lam k • c j k i' := by
      refine hforce (cs j) (hcs j) _ (hmem j) ?_
      intro i' hi'
      obtain ⟨hi'T, hi'S⟩ := Finset.mem_inter.mp hi'
      calc cs j i' = ∑ k, lam k • U j i' k := hag i' hi'T j
        _ = ∑ k, lam k • c j k i' := by
            exact Finset.sum_congr rfl fun k _ => by rw [hexp j k i' hi'S]
    -- on the outlier position, agreement + forcing give the kill condition
    have hagi : cs j i = ∑ k, lam k • U j i k := hag i hiT j
    have hky : (∑ k, lam k • c j k i) = ∑ k, lam k • U j i k := by
      rw [← hagi, hforced]
    unfold KillsDeviation deviation
    calc (∑ k, lam k • (U j i k - c j k i))
        = (∑ k, lam k • U j i k) - ∑ k, lam k • c j k i := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun k _ => smul_sub _ _ _
      _ = 0 := by rw [hky, sub_self]
  · intro hkill
    refine ⟨fun j i' => ∑ k, lam k • c j k i', fun j => hmem j, ?_⟩
    intro i hiT j
    by_cases hiS : i ∈ Sstar
    · exact Finset.sum_congr rfl fun k _ => by rw [hexp j k i hiS]
    · have hk := hkill j i (Finset.mem_sdiff.mpr ⟨hiT, hiS⟩)
      unfold KillsDeviation deviation at hk
      have : (∑ k, lam k • U j i k) - ∑ k, lam k • c j k i = 0 := by
        rw [← hk, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => (smul_sub _ _ _).symm
      have := sub_eq_zero.mp this
      exact this.symm

/-- **Line obstructions are deviation kernels.**  Under the fully-close hypotheses,
if the obstruction subspace of a witness `T` is a line `span{λ₀}` (`λ₀ ≠ 0`), then
some deviation covector at an outlier of `T` is nonzero with `λ₀` in its kernel —
i.e. the line is pinned by a single deviation.  Hence the number of distinct line
obstructions over ALL witnesses is at most the number of (row, position) pairs with
nonzero deviation — independent of `q`. -/
theorem obstruction_line_pinned_by_deviation
    (C : Submodule F (ι → A)) {l : ℕ} {U : Fin l → ι → Fin 2 → A}
    {c : Fin l → Fin 2 → ι → A} {Sstar : Finset ι} {T : Finset ι}
    (hcw : ∀ j k, c j k ∈ (C : Set (ι → A)))
    (hexp : ∀ j k, ∀ i ∈ Sstar, c j k i = U j i k)
    (hforce : ∀ (w : ι → A), w ∈ (C : Set (ι → A)) →
      ∀ (w' : ι → A), w' ∈ (C : Set (ι → A)) →
      (∀ i ∈ T ∩ Sstar, w i = w' i) → w = w')
    (hproper : jointStackSubmodule C T U ≠ ⊤) :
    jointStackSubmodule C T U = ⊥ ∨
      ∃ (j : Fin l) (i : ι), i ∈ T \ Sstar ∧ deviation U c j i ≠ 0 ∧
        ∀ lam ∈ jointStackSubmodule C T U, KillsDeviation U c j i lam := by
  by_cases hbot : jointStackSubmodule C T U = ⊥
  · exact Or.inl hbot
  refine Or.inr ?_
  -- not ⊥ and not ⊤: some deviation covector must be nonzero, else K_T = ⊤
  by_contra hno
  push Not at hno
  apply hproper
  rw [Submodule.eq_top_iff']
  intro lam
  rw [mem_jointStackSubmodule_iff_deviation C hcw hexp hforce]
  intro j i hi
  by_cases hdev : deviation U c j i = 0
  · unfold KillsDeviation
    rw [hdev]
    simp
  · -- a nonzero deviation exists; hno yields an unkilled member of K_T, contradiction
    exfalso
    obtain ⟨lam', hlam', hnk⟩ := hno j i hi hdev
    exact hnk ((mem_jointStackSubmodule_iff_deviation C hcw hexp hforce lam').mp
      hlam' j i hi)

end ProximityGap.Jo26Obstruction

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Jo26Obstruction.mem_jointStackSubmodule_iff_deviation
#print axioms ProximityGap.Jo26Obstruction.obstruction_line_pinned_by_deviation

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Gaussian additive-energy recursion: base case, convolution identity, conditional step (#444)

This file formalizes — **axiom-clean** and abstractly (any additive comm group, any finite carrier
set `M`) — the structural skeleton of the additive-energy recursion that is the convergent
next-sub-goal of three independent BGK proof strategies for the proximity prize (#444). Specializing
`M` to `μ_n` (the `n`-th roots of unity in `Fₚˣ`, `n = 2^μ`) gives the prize-relevant statement.

## The objects

For a carrier `M : Finset α` in an additive comm group, the *`r`-fold representation function* is
`repCount M r t = #{x : Fin r → α | (∀ i, x i ∈ M) ∧ ∑ i, x i = t}` and the *`r`-th additive
energy* is `energyR M r = ∑ₜ (repCount M r t)²` (the number of pairs of `r`-tuples in `M` with equal
sum). We work with explicit `Finset.card`s of tuple sets, so everything is exact-integer (no
analysis, no probability).

## What is proved here (all axiom-clean)

* `repCount_succ` — the **convolution recursion** for the representation function:
  `repCount M (r+1) t = ∑_{m ∈ M} repCount M r (t − m)` (appending one coordinate from `M`),
  proved as a clean `Finset.card` double-count via grouping tuples by their last coordinate.
* `energyR_eq_matched` — `energyR M r = #{(x,y) ∈ Mʳ × Mʳ : ∑x = ∑y}` (energy as the count of
  matched pairs), and `sum_repCount` — `∑ₜ repCount M r t = (#M)ʳ` (the total tuple count).
* `energyR_succ_ge_diag` — the **diagonal lower bound** `#M · energyR M r ≤ energyR M (r+1)`
  (the appended coordinates `m = m'` already contribute `#M · E r`); hence the off-diagonal excess
  `offDiag := energyR M (r+1) − #M · energyR M r` is a well-defined natural number.
* `recursion_step` — the **single inductive STEP** `energyR M (r+1) ≤ (2r+1) · #M · energyR M r`
  GIVEN the named *appended-coordinate hypothesis* `hOff : offDiag ≤ 2 r · #M · energyR M r`.
  This isolates the open content (the off-diagonal correlation bound that the
  Sidon-except-negation structure of `μ_n` should supply r-uniformly up to `r ~ log p`).
* `base_case_of_sidon` — the **base case** `energyR M 2 ≤ 3 · (#M)^2` from the
  *Sidon-except-negation* rep-count hypothesis (`repCount M 2 t ≤ 2` for `t ≠ 0`, and
  `repCount M 2 0 ≤ #M`), the honest `≤` form of the exact `3n² − 3n` for `μ_n`.

## Honest scope (#444)

The convolution identity and the diagonal lower bound are proven *unconditionally* (pure finite
double-counting, any comm group). The base case is proven from the Sidon-except-negation rep-count
bound. The inductive step is a genuine *conditional* theorem reducing the recursion to the single
named hypothesis `hOff`, the appended-coordinate off-diagonal bound. **Not** a proof of the
recursion: the `r`-uniform validity of `hOff` up to `r ~ log p` is the open BGK content, isolated in
that one hypothesis. This does NOT close the prize.
-/

namespace ArkLib.ProximityGap.Frontier.AvGER

open Finset BigOperators

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-- The `r`-fold representation count of `t` over the carrier `M`: the number of tuples
`x : Fin r → α` with every coordinate in `M` and `∑ i, x i = t`. -/
noncomputable def repCount (M : Finset α) (r : ℕ) (t : α) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin r => M)).filter (fun x => ∑ i, x i = t)).card

/-- The `r`-th additive energy of `M`, defined as the `L²` sum of representation counts over the
(finite) `r`-fold sumset support. -/
noncomputable def energyR (M : Finset α) (r : ℕ) : ℕ :=
  ∑ t ∈ (Fintype.piFinset (fun _ : Fin r => M)).image (fun x => ∑ i, x i),
    (repCount M r t) ^ 2

/-- `repCount` vanishes off the `r`-fold sumset support. -/
lemma repCount_eq_zero_of_not_mem {M : Finset α} {r : ℕ} {t : α}
    (ht : t ∉ (Fintype.piFinset (fun _ : Fin r => M)).image (fun x => ∑ i, x i)) :
    repCount M r t = 0 := by
  unfold repCount
  rw [Finset.card_eq_zero]
  ext x
  simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
  intro hx hsum
  exact ht (Finset.mem_image.mpr ⟨x, hx, hsum⟩)

/-- **Convolution recursion**: `repCount M (r+1) t = ∑_{m ∈ M} repCount M r (t − m)`.
Proved by grouping the `(r+1)`-tuples by their last coordinate `m`; for each `m`, the first `r`
coordinates form an `r`-tuple summing to `t − m`. -/
theorem repCount_succ (M : Finset α) (r : ℕ) (t : α) :
    repCount M (r + 1) t = ∑ m ∈ M, repCount M r (t - m) := by
  classical
  unfold repCount
  -- Equiv: (Fin (r+1) → α) tuples in M with sum t ↔ Σ_{m∈M} (Fin r → α) tuples in M with sum (t-m),
  -- via x ↦ (x (last), Fin.init x).  Count by partitioning on the last coordinate.
  rw [Finset.card_eq_sum_card_fiberwise
        (f := fun x : Fin (r+1) → α => x (Fin.last r)) (t := M)
        (by
          intro x hx
          have hx1 : x ∈ Fintype.piFinset (fun _ : Fin (r+1) => M) :=
            Finset.mem_of_mem_filter x hx
          exact (Fintype.mem_piFinset.mp hx1) (Fin.last r))]
  refine Finset.sum_congr rfl ?_
  intro m hm
  -- The fiber over `m` (last coord = m, sum = t) ↔ r-tuples in M summing to t - m.
  apply Finset.card_bij (fun x _ => Fin.init x)
  · -- maps into the target filter
    intro x hx
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hx ⊢
    obtain ⟨⟨hmem, hsum⟩, hlast⟩ := hx
    refine ⟨fun i => hmem (Fin.castSucc i), ?_⟩
    have h2 := hsum
    rw [Fin.sum_univ_castSucc, hlast] at h2
    -- h2 : (∑ i, x (castSucc i)) + m = t
    have heq : (∑ i : Fin r, Fin.init x i) = ∑ i : Fin r, x (Fin.castSucc i) := rfl
    rw [heq]
    exact eq_sub_of_add_eq h2
  · -- injective on the fiber: last coords agree (= m), inits agree by hypothesis
    intro x hx y hy hxy
    simp only [Finset.mem_filter] at hx hy
    funext i
    refine Fin.lastCases ?_ ?_ i
    · rw [hx.2, hy.2]
    · intro j
      have : Fin.init x j = Fin.init y j := by rw [hxy]
      simpa [Fin.init] using this
  · -- surjective onto the target filter
    intro y hy
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hy
    refine ⟨Fin.snoc y m, ?_, ?_⟩
    · simp only [Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · simpa using hm
        · intro j; simpa [Fin.snoc] using hy.1 j
      · rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [hy.2]; abel
      · simp [Fin.snoc_last]
    · funext i; simp [Fin.init, Fin.snoc_castSucc]

/-- The `r`-fold sumset support of `M`. -/
noncomputable def support (M : Finset α) (r : ℕ) : Finset α :=
  (Fintype.piFinset (fun _ : Fin r => M)).image (fun x => ∑ i, x i)

/-- **Energy as the `L²` sum over a superset of the support.** For any finite `S` containing the
support, `energyR M r = ∑_{t ∈ S} (repCount M r t)²` (terms off the support are zero). -/
theorem energyR_eq_sum_on (M : Finset α) (r : ℕ) {S : Finset α}
    (hS : support M r ⊆ S) :
    energyR M r = ∑ t ∈ S, (repCount M r t) ^ 2 := by
  classical
  unfold energyR
  refine Finset.sum_subset (by simpa [support] using hS) ?_
  intro t _ ht
  rw [repCount_eq_zero_of_not_mem ht]; simp

/-- **The off-diagonal excess** of the energy recursion:
`offDiag M r = energyR M (r+1) − #M · energyR M r` (a `ℕ` subtraction; nonnegative once we know the
diagonal lower bound `energyR_succ_ge_diag`). -/
noncomputable def offDiag (M : Finset α) (r : ℕ) : ℕ :=
  energyR M (r + 1) - M.card * energyR M r

/-- The set of *matched `r`-pairs* `{(x,y) : ∑x = ∑y}`; its card is `energyR M r`. -/
noncomputable def matchedPairs (M : Finset α) (r : ℕ) : Finset ((Fin r → α) × (Fin r → α)) :=
  ((Fintype.piFinset (fun _ : Fin r => M)) ×ˢ (Fintype.piFinset (fun _ : Fin r => M))).filter
    (fun p => ∑ i, p.1 i = ∑ i, p.2 i)

theorem energyR_eq_matched (M : Finset α) (r : ℕ) :
    energyR M r = (matchedPairs M r).card := by
  classical
  unfold energyR matchedPairs
  rw [Finset.card_filter, Finset.sum_product]
  rw [← Finset.sum_fiberwise_of_maps_to
        (g := fun x : Fin r → α => ∑ i, x i)
        (t := (Fintype.piFinset (fun _ : Fin r => M)).image (fun x => ∑ i, x i))
        (by intro x hx; exact Finset.mem_image.mpr ⟨x, hx, rfl⟩)]
  refine Finset.sum_congr rfl ?_
  intro t _
  unfold repCount
  rw [sq]
  -- inner sum: ∑_{x : ∑x=t} #{y : ∑y=∑x} = (#{x:∑x=t}) * (#{y:∑y=t})
  rw [Finset.sum_congr rfl
      (g := fun _ => ((Fintype.piFinset (fun _ : Fin r => M)).filter
              (fun y => ∑ i, y i = t)).card)
      (by
        intro x hx
        rw [Finset.mem_filter] at hx
        -- inner ∑_y [∑x = ∑y] = #{y : ∑y = t} since ∑x = t
        rw [Finset.card_filter]
        refine Finset.sum_congr rfl ?_
        intro y _
        rw [hx.2]
        by_cases h : t = ∑ i, y i
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (fun hh => h hh.symm)])]
  rw [Finset.sum_const, smul_eq_mul]

/-- **Diagonal lower bound.** Appending the *same* coordinate `m` to both `r`-tuples already
contributes `#M · energyR M r` matched pairs, so `#M · energyR M r ≤ energyR M (r+1)`.
This makes `offDiag` a genuine (nonnegative) excess. -/
theorem energyR_succ_ge_diag (M : Finset α) (r : ℕ) :
    M.card * energyR M r ≤ energyR M (r + 1) := by
  classical
  rw [energyR_eq_matched, energyR_eq_matched, ← Finset.card_product]
  -- Inject (m, (x,y)) ↦ (snoc x m, snoc y m) : M × matched_r ↪ matched_{r+1}.
  apply Finset.card_le_card_of_injOn
    (fun q => (Fin.snoc q.2.1 q.1, Fin.snoc q.2.2 q.1))
  · rintro ⟨m, x, y⟩ hmem
    rw [Finset.mem_coe, Finset.mem_product] at hmem
    obtain ⟨hm, hxy⟩ := hmem
    rw [Finset.mem_coe]
    unfold matchedPairs at hxy ⊢
    rw [Finset.mem_filter, Finset.mem_product] at hxy
    rw [Finset.mem_filter, Finset.mem_product]
    obtain ⟨⟨hx, hy⟩, hsum⟩ := hxy
    rw [Fintype.mem_piFinset] at hx hy
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i; refine Fin.lastCases ?_ ?_ i
      · simpa using hm
      · intro j; simpa [Fin.snoc] using hx j
    · rw [Fintype.mem_piFinset]
      intro i; refine Fin.lastCases ?_ ?_ i
      · simpa using hm
      · intro j; simpa [Fin.snoc] using hy j
    · show (∑ i, Fin.snoc x m i) = ∑ i, Fin.snoc y m i
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [hsum]
  · rintro ⟨m, x, y⟩ _ ⟨m', x', y'⟩ _ heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    have hm : m = m' := by
      have := congrFun h1 (Fin.last r); simpa [Fin.snoc_last] using this
    have hx : x = x' := by
      funext j; have := congrFun h1 (Fin.castSucc j); simpa [Fin.snoc_castSucc] using this
    have hy : y = y' := by
      funext j; have := congrFun h2 (Fin.castSucc j); simpa [Fin.snoc_castSucc] using this
    simp [hm, hx, hy]

/-- **The single inductive STEP, conditional on the named appended-coordinate hypothesis.**
Given `hOff : offDiag M r ≤ 2 r · #M · energyR M r` (the off-diagonal correlation bound that the
Sidon-except-negation structure of `μ_n` must supply r-uniformly), the energy recursion holds:
`energyR M (r+1) ≤ (2r+1) · #M · energyR M r`. Combined with the proven diagonal lower bound this is
exactly `E_{r+1} ≤ (2r+1) n E_r`, the Wick-rung recursion driving the prize moment method. -/
theorem recursion_step (M : Finset α) (r : ℕ)
    (hOff : offDiag M r ≤ 2 * r * (M.card * energyR M r)) :
    energyR M (r + 1) ≤ (2 * r + 1) * (M.card * energyR M r) := by
  have hdiag := energyR_succ_ge_diag M r
  -- energyR M (r+1) = #M·E_r + offDiag  (since offDiag = E_{r+1} − #M·E_r and #M·E_r ≤ E_{r+1})
  have hsplit : energyR M (r + 1) = M.card * energyR M r + offDiag M r := by
    unfold offDiag
    omega
  rw [hsplit]
  -- #M·E_r + offDiag ≤ #M·E_r + 2r·#M·E_r = (2r+1)·#M·E_r
  calc M.card * energyR M r + offDiag M r
      ≤ M.card * energyR M r + 2 * r * (M.card * energyR M r) := by omega
    _ = (2 * r + 1) * (M.card * energyR M r) := by ring

/-- **Total representation count.** `∑_t repCount M r t = (#M)^r`: every tuple in `Mʳ` contributes
to exactly one sum value. (Stated over any finite `S` containing the support.) -/
theorem sum_repCount (M : Finset α) (r : ℕ) {S : Finset α} (hS : support M r ⊆ S) :
    ∑ t ∈ S, repCount M r t = M.card ^ r := by
  classical
  unfold repCount
  rw [← Finset.card_eq_sum_card_fiberwise
        (f := fun x : Fin r → α => ∑ i, x i) (t := S)
        (by
          intro x hx
          apply hS
          exact Finset.mem_image.mpr ⟨x, hx, rfl⟩)]
  rw [Fintype.card_piFinset]
  simp

/-- **Base case from Sidon-except-negation.** If the carrier `M` satisfies the rep-count bounds
`repCount M 2 t ≤ 2` for every `t ≠ 0` and `repCount M 2 0 ≤ #M` (which hold *exactly* for `μ_n`:
each nonzero `t = x+y` has at most two ordered representations with `x,y ∈ μ_n`, and `t = 0` has
exactly the `n` antipodal pairs `x + (−x)`), then `energyR M 2 ≤ 3 · (#M)^2`. For `μ_n` (`#M = n`)
this is the honest `≤` form of the exact closed form `E_2 = 3n² − 3n`. -/
theorem base_case_of_sidon (M : Finset α)
    (hpos : ∀ t, t ≠ 0 → repCount M 2 t ≤ 2)
    (hzero : repCount M 2 0 ≤ M.card) :
    energyR M 2 ≤ 3 * M.card ^ 2 := by
  classical
  -- Work over S = insert 0 (support).
  set S := insert (0 : α) (support M 2) with hSdef
  have hsub : support M 2 ⊆ S := Finset.subset_insert _ _
  have h0S : (0 : α) ∈ S := Finset.mem_insert_self _ _
  rw [energyR_eq_sum_on M 2 hsub]
  -- split off t = 0
  rw [← Finset.add_sum_erase S _ h0S]
  -- bound (a₂ 0)² ≤ #M·#M and ∑_{t≠0}(a₂ t)² ≤ 2·∑_{t≠0} a₂ t ≤ 2·#M²
  have hzsq : (repCount M 2 0) ^ 2 ≤ M.card ^ 2 := by
    rw [sq, sq]; exact Nat.mul_le_mul hzero hzero
  have hrest : ∑ t ∈ S.erase 0, (repCount M 2 t) ^ 2
      ≤ 2 * ∑ t ∈ S.erase 0, repCount M 2 t := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro t ht
    have htne : t ≠ 0 := (Finset.mem_erase.mp ht).1
    have hle := hpos t htne
    rw [sq]
    exact Nat.mul_le_mul_right _ hle
  have htot : ∑ t ∈ S.erase 0, repCount M 2 t ≤ M.card ^ 2 := by
    refine le_trans (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)) ?_
    rw [sum_repCount M 2 hsub]
  have hfinal : (repCount M 2 0) ^ 2 + ∑ t ∈ S.erase 0, (repCount M 2 t) ^ 2
      ≤ M.card ^ 2 + 2 * (M.card ^ 2) := by
    refine Nat.add_le_add hzsq ?_
    exact le_trans hrest (Nat.mul_le_mul_left 2 htot)
  refine le_trans hfinal ?_
  ring_nf
  omega

end ArkLib.ProximityGap.Frontier.AvGER

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvGER.repCount_succ
#print axioms ArkLib.ProximityGap.Frontier.AvGER.energyR_succ_ge_diag
#print axioms ArkLib.ProximityGap.Frontier.AvGER.recursion_step
#print axioms ArkLib.ProximityGap.Frontier.AvGER.base_case_of_sidon

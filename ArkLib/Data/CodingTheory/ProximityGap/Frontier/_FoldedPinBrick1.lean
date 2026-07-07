/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.SubspaceDesignLineDecodable
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Folded-RS capacity pin, brick 1 — the rank-capped determining tuple on the FOLDED domain
# (issue #466, lane L7; dossier v3 §6 Tier-3 ★ "folded-RS / subspace-design capacity pin")

**Where this sits (the dependency map is `docs/kb/deltastar-466-folded-pin-map-2026-07-01.md`).**
The two proven halves of the workbench §2.5 R2 route are

* `CodingTheory.frs_is_subspaceDesign_gk16_of_admissible` (`SubspaceDesign.lean`, axiom-clean):
  the folded RS code IS a `τ`-subspace-design with the (repaired, crude) GK16 profile
  `τ(r) = (k−1)/n` on `[1, s]` — **and `τ(r) = 1` off `[1, s]`**;
* `ProximityGap.exists_determining_tuple` (`SubspaceDesignLineDecodable.lean`, axiom-clean):
  a `τ`-design with `∀ j, τ j ≤ θ` and `θ < θ' ≤ 1` admits, inside any agreement set of density
  `≥ θ'`, a coordinate tuple determining any span `H` of `finrank ≤ r`.

**The interface vacuity (found by this lane, machine-checked below).** These two theorems do
NOT compose: the consumer's profile hypothesis quantifies over ALL ranks `j : ℕ`, and the GK16
profile equals `1` off `[1, s]` (in particular at `j = 0`), so `∀ j, τ j ≤ θ` forces `θ ≥ 1`,
contradicting `θ < θ' ≤ 1` (`no_unranked_theta_for_gk16Profile`). The composition is therefore
unsatisfiable as stated — even though the underlying mathematics is fine, because the survival
induction only ever evaluates `τ` at ranks `1 … r`.

**What this file proves (all axiom-clean, no `sorry`).**

1. `VanishBudget` + `card_surv_ge_of_vanishBudget` — the survival count re-derived from the
   *local* hypothesis it actually uses: a fully-vanishing-coordinate budget `θ·n` for the
   subspaces `H' ≤ H` of rank `≥ 1` (no global profile bound). Same peeling induction as
   `SeparationSurvivalCount.card_surv_ge`, hypothesis weakened to its true footprint.
2. `exists_determining_tuple_of_vanishBudget` / `exists_recovering_tuple_of_vanishBudget` —
   the line-decodability conclusions under the budget hypothesis.
3. `vanishBudget_of_design` + `exists_determining_tuple_ranked` — the **rank-capped** design
   consumer: only `∀ j ∈ [1, r], τ j ≤ θ` is needed. This is the repaired socket.
4. `no_unranked_theta_for_gk16Profile` — the vacuity guard: the *unranked* socket is
   unsatisfiable for the GK16 profile (records why brick 1 is necessary, not cosmetic).
5. **The folded-domain instantiation (the headline):** `frs_exists_determining_tuple` /
   `frs_exists_recovering_tuple` — for the folded RS code `frsCode domain k s ω` under the
   standard `Admissible` side conditions, any span `H ≤ FRS` with `finrank H ≤ r ≤ s` is
   determined by `r` folded coordinates inside any agreement set of density
   `θ' > (k−1)/n` — **unconditional** (the design input is the in-tree GK16 theorem, not a
   hypothesis). Zero character sums.
6. `FrsCloseListSpanBound` (named deep input, OPEN) + `frs_close_codeword_unique_recovery`
   (its consumer): IF the `θ'`-close FRS codewords span a subspace of `finrank ≤ r` (the
   CZ25 / linear-algebraic list-recovery input, the JLR 2601.10047 §5 mechanism), THEN every
   close codeword is pinned by `r` folded coordinates in its own agreement set, uniquely
   among ALL close codewords — the GG25 §4.3 line-decodability shape that
   `GG25MCAFromCurveDecodability` turns into MCA.
7. **Brick 2 (the G2 collapse):** `frsCloseListSpanBound_of_listBound` /
   `frsCloseListSpanBound_of_listDecodable` — any per-received-word list-SIZE bound at
   relative radius `1 − θ'` yields `FrsCloseListSpanBound` (take `H` := span of the close
   list). Since the in-tree CZ25 chain (`ListDecoding/CZ25CapacityReduction.lean`,
   `ListDecoding/CZ25GeomCapacity.lean`) bounds `Λ(frsCode, δ)` conditional on the single
   named residual `CodingTheory.CZ25CoordFiberCap`, the deep input G2 is NOT a from-scratch
   project: it collapses to `CZ25CoordFiberCap` (the workbench §2.5 R2 GAP) modulo an
   `ℕ∞`/`ENNReal`-to-`ℕ` cast of those endpoints.
8. `FrsMCAPin` — the lane target stated against the REAL prize-facing object
   (`ProximityGap.epsMCA`), as a named `Prop`. It is OPEN; nothing here claims it.

**Honest scope / relation to the prize (dossier §11.6).** `isPrizeClosure := False`.
This lane banks deployment-relevant soundness for protocols that already fold (FRI/STIR/WHIR)
— goal-(A)-adjacent value. It does **not** touch plain-RS δ\* (goal (B), the $1M core):
`FoldingTransferNoGo.folding_transfer_no_go` PROVES the folded conclusion cannot transfer down
to the plain metric (one corruption per orbit kills every folded agreement while keeping plain
agreement `d/(d+1)`). Two further honest caveats:
* the in-tree PROVEN profile is the crude `(k−1)/n` (≈ `s·ρ_block`); the *capacity-sharp*
  profile `k/(n(s−r+1))` needs the GK16 Claim-15 strengthening (named gap G0 in the map doc) —
  so today's radius is nonvacuous (`θ' > (k−1)/n`) but not yet the capacity `θ' ≈ ρ + η`;
* the deep list-recovery input (`FrsCloseListSpanBound`) is carried as a named hypothesis —
  proving it is the CZ25 formalization project (gap G2), not attempted here.

References: [GG25] ePrint 2025/2054 §4.3; [JLR] arXiv 2601.10047 (Lemma 5.12 = the
subspace-design inequality, in-tree as `IsSubspaceDesign` + the GK16 budget); [GK16]
Guruswami–Kopparty; ABF26 §2.4–2.5 (Definitions 2.14–2.16, Theorem 2.18).
-/

open Finset CodingTheory
open scoped NNReal

namespace ProximityGap.FoldedPin

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] {F : Type} [Field F]

/-! ## 1. The vanishing budget — the hypothesis the survival induction actually uses -/

open Classical in
/-- **The vanishing budget.** Every subspace `H' ≤ H` of rank `≥ 1` fully vanishes on at most
`θ·n` coordinates. This is the exact footprint of the design hypothesis inside the
`card_surv_ge` induction — a *local* bound at the ranks `1 … finrank H` only, with no global
profile quantifier. `vanishBudget_of_design` discharges it from `IsSubspaceDesign` with a
rank-capped profile bound. -/
def VanishBudget {s : ℕ} (H : Submodule F (ι → Fin s → F)) (θ : ℝ) : Prop :=
  ∀ H' : Submodule F (ι → Fin s → F), H' ≤ H → 1 ≤ Module.finrank F H' →
    ((univ.filter (fun i : ι => H' ≤ LinearMap.ker
      (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))).card : ℝ)
      ≤ θ * Fintype.card ι

/-- The budget restricts along `≤`. -/
theorem VanishBudget.mono {s : ℕ} {H K : Submodule F (ι → Fin s → F)} {θ : ℝ}
    (hKH : K ≤ H) (h : VanishBudget H θ) : VanishBudget K θ :=
  fun H' hH' h1 => h H' (le_trans hH' hKH) h1

open Classical in
/-- **The survival count from the vanishing budget alone** (the rank-capped re-derivation of
`SeparationSurvivalCount.card_surv_ge`): if every rank-`≥ 1` subspace of `H` fully vanishes on
`≤ θ·n` coordinates, and `T` has density `≥ θ'`, then at least a `(θ'−θ)^r` fraction of the
`n^r` coordinate tuples both separate `H` and lie entirely in `T`. Same peeling induction;
the design profile is gone from the interface. -/
theorem card_surv_ge_of_vanishBudget {s : ℕ} {θ θ' : ℝ}
    (hθ0 : 0 ≤ θ) (hθθ' : θ ≤ θ') (hθ'1 : θ' ≤ 1)
    (T : Finset ι) (hT : θ' * (Fintype.card ι : ℝ) ≤ T.card)
    (r : ℕ) (H : Submodule F (ι → Fin s → F)) (hr : Module.finrank F H ≤ r)
    (hfv : VanishBudget H θ) :
    (θ' - θ) ^ r * (Fintype.card ι : ℝ) ^ r
      ≤ ((univ.filter (fun v : Fin r → ι => Separates H v ∧ ∀ j, v j ∈ T)).card : ℝ) := by
  have hd0 : (0 : ℝ) ≤ θ' - θ := by linarith
  induction r generalizing H with
  | zero =>
    have hH : H = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hr)
    have hone : (univ.filter (fun v : Fin 0 → ι => Separates H v ∧ ∀ j, v j ∈ T)) = univ := by
      ext v; simp only [mem_filter, mem_univ, true_and, iff_true]
      refine ⟨by simp [Separates, hH], fun j => j.elim0⟩
    rw [hone]; simp
  | succ k ih =>
    by_cases hH : H = ⊥
    · have hall : (univ.filter (fun v : Fin (k + 1) → ι => Separates H v ∧ ∀ j, v j ∈ T))
          = Fintype.piFinset (fun _ : Fin (k + 1) => T) := by
        ext v; simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
        exact ⟨fun hv => hv.2, fun hv => ⟨by simp [Separates, hH], hv⟩⟩
      rw [hall, Fintype.card_piFinset]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow]
      have hstep : (θ' - θ) * (Fintype.card ι : ℝ) ≤ (T.card : ℝ) := by nlinarith [hT, hθ0]
      calc (θ' - θ) ^ (k + 1) * (Fintype.card ι : ℝ) ^ (k + 1)
          = ((θ' - θ) * (Fintype.card ι : ℝ)) ^ (k + 1) := by rw [mul_pow]
        _ ≤ (T.card : ℝ) ^ (k + 1) := by gcongr
    · have hrank1 : 1 ≤ Module.finrank F H := by
        rw [Nat.one_le_iff_ne_zero]; exact fun h0 => hH (Submodule.finrank_eq_zero.mp h0)
      rw [card_surv_decomp, Nat.cast_sum]
      set Tsupp := T.filter (fun i₀ : ι => ¬ (H ≤ LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀))) with hTsupp
      -- `|T ∩ support| ≥ (θ'−θ)·n`, now directly from the budget at `H` itself
      have hTsuppcard : (θ' - θ) * (Fintype.card ι : ℝ) ≤ (Tsupp.card : ℝ) := by
        have hfull : ((univ.filter (fun i₀ : ι => H ≤ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀))).card : ℝ)
            ≤ θ * (Fintype.card ι : ℝ) := hfv H le_rfl hrank1
        have hsplit : (T.filter (fun i₀ : ι => H ≤ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀))).card + Tsupp.card = T.card := by
          rw [hTsupp]
          exact Finset.filter_card_add_filter_neg_card_eq_card
            (fun i₀ : ι => H ≤ LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀))
        have hsub2 : ((T.filter (fun i₀ : ι => H ≤ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀))).card : ℝ)
            ≤ ((univ.filter (fun i₀ : ι => H ≤ LinearMap.ker
                (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ T))
        have hsplitℝ : ((T.filter (fun i₀ : ι => H ≤ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀))).card : ℝ) + (Tsupp.card : ℝ)
            = (T.card : ℝ) := by exact_mod_cast hsplit
        nlinarith [hfull, hsplitℝ, hsub2, hT]
      -- per `i₀ ∈ Tsupp`: IH applies (reducing ⇒ dim drops; the budget restricts along `≤`)
      have hIH : ∀ i₀ ∈ Tsupp, (θ' - θ) ^ k * (Fintype.card ι : ℝ) ^ k
            ≤ ((univ.filter (fun w : Fin k → ι => Separates (H ⊓ LinearMap.ker
                (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)) w ∧ ∀ j, w j ∈ T)).card : ℝ) := by
        intro i₀ hi₀
        rw [hTsupp, mem_filter] at hi₀
        have hlt : H ⊓ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀) < H :=
          lt_of_le_of_ne inf_le_left (fun heq => hi₀.2 (heq ▸ inf_le_right))
        have hdrop : Module.finrank F (H ⊓ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)
            : Submodule F (ι → Fin s → F)) ≤ k := by
          have := Submodule.finrank_lt_finrank_of_lt hlt; omega
        exact ih _ hdrop (hfv.mono inf_le_left)
      calc (θ' - θ) ^ (k + 1) * (Fintype.card ι : ℝ) ^ (k + 1)
          = ((θ' - θ) * (Fintype.card ι : ℝ)) * ((θ' - θ) ^ k * (Fintype.card ι : ℝ) ^ k) := by ring
        _ ≤ (Tsupp.card : ℝ) * ((θ' - θ) ^ k * (Fintype.card ι : ℝ) ^ k) :=
            mul_le_mul_of_nonneg_right hTsuppcard (by positivity)
        _ = ∑ _i₀ ∈ Tsupp, ((θ' - θ) ^ k * (Fintype.card ι : ℝ) ^ k) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ i₀ ∈ Tsupp, ((univ.filter (fun w : Fin k → ι => Separates (H ⊓ LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)) w ∧ ∀ j, w j ∈ T)).card : ℝ) :=
            Finset.sum_le_sum hIH
        _ ≤ ∑ i₀ ∈ T, ((univ.filter (fun w : Fin k → ι => Separates (H ⊓ LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)) w ∧ ∀ j, w j ∈ T)).card : ℝ) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (by rw [hTsupp]; exact Finset.filter_subset _ _) ?_
            intro i₀ _ _; positivity

/-! ## 2. Line-decodability conclusions under the budget -/

open Classical in
/-- A good tuple exists under the budget: some `v` both separates `H` and lies in `T`. -/
theorem exists_surv_tuple_of_vanishBudget {s : ℕ} {θ θ' : ℝ}
    (hθ0 : 0 ≤ θ) (hθθ' : θ < θ') (hθ'1 : θ' ≤ 1)
    (T : Finset ι) (hT : θ' * (Fintype.card ι : ℝ) ≤ T.card)
    (r : ℕ) (H : Submodule F (ι → Fin s → F)) (hr : Module.finrank F H ≤ r)
    (hfv : VanishBudget H θ) :
    ∃ v : Fin r → ι, Separates H v ∧ ∀ j, v j ∈ T := by
  have hcount := card_surv_ge_of_vanishBudget hθ0 (le_of_lt hθθ') hθ'1 T hT r H hr hfv
  have hd : (0 : ℝ) < θ' - θ := by linarith
  have hnpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hpos : (0 : ℝ) < (θ' - θ) ^ r * (Fintype.card ι : ℝ) ^ r := by positivity
  have hcard : 0 < (univ.filter (fun v : Fin r → ι => Separates H v ∧ ∀ j, v j ∈ T)).card := by
    have : (0 : ℝ) < ((univ.filter (fun v : Fin r → ι => Separates H v ∧ ∀ j, v j ∈ T)).card : ℝ) :=
      lt_of_lt_of_le hpos hcount
    exact_mod_cast this
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hcard
  rw [mem_filter] at hv
  exact ⟨v, hv.2⟩

open Classical in
/-- **Determining tuple from the budget** (the repaired GG25 §4.3 conclusion): a tuple
`v ⊆ T` whose coordinates determine `H`. -/
theorem exists_determining_tuple_of_vanishBudget {s : ℕ} {θ θ' : ℝ}
    (hθ0 : 0 ≤ θ) (hθθ' : θ < θ') (hθ'1 : θ' ≤ 1)
    (T : Finset ι) (hT : θ' * (Fintype.card ι : ℝ) ≤ T.card)
    (r : ℕ) (H : Submodule F (ι → Fin s → F)) (hr : Module.finrank F H ≤ r)
    (hfv : VanishBudget H θ) :
    ∃ v : Fin r → ι, (∀ j, v j ∈ T) ∧
      ∀ y : ι → Fin s → F, {c : ι → Fin s → F | c ∈ H ∧ ∀ j, c (v j) = y (v j)}.Subsingleton := by
  obtain ⟨v, hsep, hvT⟩ := exists_surv_tuple_of_vanishBudget hθ0 hθθ' hθ'1 T hT r H hr hfv
  exact ⟨v, hvT, fun y => tuple_agree_subsingleton hsep y⟩

/-! ## 3. The rank-capped design consumer — the repaired socket -/

open Classical in
/-- **Design ⟹ budget, rank-capped.** A `τ`-subspace-design supplies the vanishing budget for
`H` at level `θ` as soon as `τ ≤ θ` on the ranks `[1, r]` actually visited
(`finrank H ≤ r`) — no global profile bound. This is what makes the GK16 folded-RS profile
(`τ = 1` off `[1, s]`) consumable. -/
theorem vanishBudget_of_design {s : ℕ} {τ : ℕ → ℝ} {θ : ℝ}
    {C : Submodule F (ι → Fin s → F)} (h : IsSubspaceDesign s τ C)
    {r : ℕ} (hτθ : ∀ j, 1 ≤ j → j ≤ r → τ j ≤ θ)
    {H : Submodule F (ι → Fin s → F)} (hHC : H ≤ C) (hr : Module.finrank F H ≤ r) :
    VanishBudget H θ := by
  intro H' hH' h1
  haveI : FiniteDimensional F (ι → Fin s → F) := inferInstance
  have hle : Module.finrank F H' ≤ r := le_trans (Submodule.finrank_mono hH') hr
  refine le_trans (subspaceDesign_fullVanish_card_le h h1 (le_trans hH' hHC) rfl) ?_
  exact mul_le_mul_of_nonneg_right (hτθ _ h1 hle) (Nat.cast_nonneg _)

open Classical in
/-- **The rank-capped determining tuple** (the socket `SubspaceDesignLineDecodable`
should have had): only `∀ j ∈ [1, r], τ j ≤ θ` is required of the profile. -/
theorem exists_determining_tuple_ranked {s : ℕ} {τ : ℕ → ℝ} {θ θ' : ℝ}
    {C : Submodule F (ι → Fin s → F)} (h : IsSubspaceDesign s τ C)
    (r : ℕ) (hτθ : ∀ j, 1 ≤ j → j ≤ r → τ j ≤ θ)
    (hθ0 : 0 ≤ θ) (hθθ' : θ < θ') (hθ'1 : θ' ≤ 1)
    (T : Finset ι) (hT : θ' * (Fintype.card ι : ℝ) ≤ T.card)
    (H : Submodule F (ι → Fin s → F)) (hHC : H ≤ C) (hr : Module.finrank F H ≤ r) :
    ∃ v : Fin r → ι, (∀ j, v j ∈ T) ∧
      ∀ y : ι → Fin s → F, {c : ι → Fin s → F | c ∈ H ∧ ∀ j, c (v j) = y (v j)}.Subsingleton :=
  exists_determining_tuple_of_vanishBudget hθ0 hθθ' hθ'1 T hT r H hr
    (vanishBudget_of_design h hτθ hHC hr)

/-- **The vacuity guard (why brick 1 is necessary).** The *unranked* socket
(`∀ j, τ j ≤ θ`, as in `exists_determining_tuple`) is unsatisfiable for the GK16 folded-RS
profile: the profile equals `1` off `[1, s]` (e.g. at `j = 0`), forcing `θ ≥ 1` and
contradicting `θ < θ' ≤ 1`. The in-tree design theorem and the in-tree tuple theorem could
never be composed before this brick. -/
theorem no_unranked_theta_for_gk16Profile (s k n : ℕ) {θ θ' : ℝ}
    (hθ : ∀ j : ℕ, (if j ∈ Finset.Icc 1 s then ((k : ℝ) - 1) / (n : ℝ) else 1) ≤ θ)
    (hθθ' : θ < θ') (hθ'1 : θ' ≤ 1) : False := by
  have h0 := hθ 0
  rw [if_neg (by simp)] at h0
  linarith

/-! ## 4. The folded-domain instantiation (the headline; zero character sums) -/

section Folded

variable [Fintype F] [DecidableEq F]

open Classical in
/-- **The folded RS determining tuple — unconditional.** For the folded Reed–Solomon code
`frsCode domain k s ω` under the standard side conditions (`Admissible`, `ω ≠ 0`,
`k ≤ s·n`, `k ≤ orderOf ω`, `1 ≤ k`), any subspace `H ≤ FRS` with `finrank H ≤ r ≤ s` is
determined by `r` folded coordinates lying inside any agreement set `T` of density
`θ' > (k−1)/n`. The design input is the PROVEN in-tree GK16 theorem
(`frs_is_subspaceDesign_gk16_of_admissible`) — not a hypothesis. No character sums anywhere.

(Radius honesty: `(k−1)/n` is the crude proven profile; the capacity-sharp
`k/(n(s−r+1))` awaits the GK16 Claim-15 strengthening — gap G0 of the map doc.) -/
theorem frs_exists_determining_tuple
    (domain : ι ↪ F) (k s : ℕ) (ω : F) (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (hω0 : ω ≠ 0) (hadm : ReedSolomon.Folded.Admissible L s ω)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω) (hk1 : 1 ≤ k)
    {θ' : ℝ} (hθθ' : ((k : ℝ) - 1) / (Fintype.card ι : ℝ) < θ') (hθ'1 : θ' ≤ 1)
    (T : Finset ι) (hT : θ' * (Fintype.card ι : ℝ) ≤ T.card)
    (r : ℕ) (hrs : r ≤ s)
    (H : Submodule F (ι → Fin s → F)) (hHC : H ≤ ReedSolomon.Folded.frsCode domain k s ω)
    (hr : Module.finrank F H ≤ r) :
    ∃ v : Fin r → ι, (∀ j, v j ∈ T) ∧
      ∀ y : ι → Fin s → F,
        {c : ι → Fin s → F | c ∈ H ∧ ∀ j, c (v j) = y (v j)}.Subsingleton := by
  have hdesign : IsSubspaceDesign s
      (fun j => if j ∈ Finset.Icc 1 s then (k - 1 : ℝ) / Fintype.card ι else 1)
      (ReedSolomon.Folded.frsCode domain k s ω) :=
    CodingTheory.frs_is_subspaceDesign_gk16_of_admissible domain k s ω L hL_dom hω0 hadm
      hkLs hkord
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hθ0 : (0 : ℝ) ≤ ((k : ℝ) - 1) / (Fintype.card ι : ℝ) :=
    div_nonneg (by linarith) (Nat.cast_nonneg _)
  refine exists_determining_tuple_ranked hdesign r
    (fun j h1 hjr => ?_) hθ0 hθθ' hθ'1 T hT H hHC hr
  rw [if_pos (Finset.mem_Icc.mpr ⟨h1, le_trans hjr hrs⟩)]

open Classical in
/-- **Per-codeword recovery on the folded domain — unconditional.** A codeword `c` of a span
`H ≤ FRS` (`finrank H ≤ r ≤ s`) agreeing with a received word `y` on a `> (k−1)/n` fraction of
folded coordinates is uniquely recovered: some tuple `v` of `r` folded coordinates has
`c = y` on `v`, and `c` is the only codeword of `H` agreeing with `y` there. -/
theorem frs_exists_recovering_tuple
    (domain : ι ↪ F) (k s : ℕ) (ω : F) (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (hω0 : ω ≠ 0) (hadm : ReedSolomon.Folded.Admissible L s ω)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω) (hk1 : 1 ≤ k)
    {θ' : ℝ} (hθθ' : ((k : ℝ) - 1) / (Fintype.card ι : ℝ) < θ') (hθ'1 : θ' ≤ 1)
    (r : ℕ) (hrs : r ≤ s)
    (H : Submodule F (ι → Fin s → F)) (hHC : H ≤ ReedSolomon.Folded.frsCode domain k s ω)
    (hr : Module.finrank F H ≤ r)
    (y c : ι → Fin s → F) (hcH : c ∈ H)
    (hagree : θ' * (Fintype.card ι : ℝ)
      ≤ ((univ.filter (fun i : ι => c i = y i)).card : ℝ)) :
    ∃ v : Fin r → ι, (∀ j, c (v j) = y (v j)) ∧
      ∀ c' : ι → Fin s → F, c' ∈ H → (∀ j, c' (v j) = y (v j)) → c' = c := by
  obtain ⟨v, hvT, hdet⟩ := frs_exists_determining_tuple domain k s ω L hL_dom hω0 hadm
    hkLs hkord hk1 hθθ' hθ'1 (univ.filter (fun i : ι => c i = y i)) hagree r hrs H hHC hr
  have hcv : ∀ j, c (v j) = y (v j) := fun j => (mem_filter.mp (hvT j)).2
  refine ⟨v, hcv, fun c' hc'H hc'agree => ?_⟩
  exact hdet y ⟨hc'H, hc'agree⟩ ⟨hcH, hcv⟩

/-! ## 5. The named deep input (OPEN) and its consumer -/

open Classical in
/-- **NAMED DEEP INPUT — OPEN, do not cite as proven.** The CZ25 / linear-algebraic
list-recovery bound (the [JLR 2601.10047] §5 mechanism, [GG25] §4.3's other half): for every
received word `y`, the FRS codewords agreeing with `y` on a `≥ θ'` fraction of folded
coordinates span a subspace of `finrank ≤ r`. GG25/JLR prove this for folded RS with
`r = O(1/η)` at `θ' = ρ + η` via the linear-algebraic list decoder; formalizing that proof is
gap G2 of the map doc (a genuine project — no character sums, but real work). Everything
downstream of this `Prop` in this file is proven. -/
def FrsCloseListSpanBound (domain : ι ↪ F) (k s : ℕ) (ω : F) (θ' : ℝ) (r : ℕ) : Prop :=
  ∀ y : ι → Fin s → F, ∃ H : Submodule F (ι → Fin s → F),
    H ≤ ReedSolomon.Folded.frsCode domain k s ω ∧ Module.finrank F H ≤ r ∧
    ∀ c ∈ ReedSolomon.Folded.frsCode domain k s ω,
      θ' * (Fintype.card ι : ℝ) ≤ ((univ.filter (fun i : ι => c i = y i)).card : ℝ) → c ∈ H

open Classical in
/-- **The list-span consumer (GG25 §4.3 line-decodability, folded, conditional only on the
span bound).** IF the close-list span bound holds at `(θ', r)` with `r ≤ s` and
`θ' > (k−1)/n`, THEN every `θ'`-close FRS codeword `c` is pinned by `r` folded coordinates
inside its own agreement set, uniquely among ALL `θ'`-close codewords. This is exactly the
per-codeword determinism that the in-tree engine
(`curveDecodable_of_curveListSize` → `all_seeds_close_of_curveDecodable`) needs as its
list-size input; wiring the count through to `epsMCA` is gaps G3–G4 of the map doc. -/
theorem frs_close_codeword_unique_recovery
    (domain : ι ↪ F) (k s : ℕ) (ω : F) (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (hω0 : ω ≠ 0) (hadm : ReedSolomon.Folded.Admissible L s ω)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω) (hk1 : 1 ≤ k)
    {θ' : ℝ} (hθθ' : ((k : ℝ) - 1) / (Fintype.card ι : ℝ) < θ') (hθ'1 : θ' ≤ 1)
    (r : ℕ) (hrs : r ≤ s)
    (hspan : FrsCloseListSpanBound domain k s ω θ' r)
    (y c : ι → Fin s → F) (hc : c ∈ ReedSolomon.Folded.frsCode domain k s ω)
    (hagree : θ' * (Fintype.card ι : ℝ)
      ≤ ((univ.filter (fun i : ι => c i = y i)).card : ℝ)) :
    ∃ v : Fin r → ι, (∀ j, c (v j) = y (v j)) ∧
      ∀ c' : ι → Fin s → F, c' ∈ ReedSolomon.Folded.frsCode domain k s ω →
        θ' * (Fintype.card ι : ℝ) ≤ ((univ.filter (fun i : ι => c' i = y i)).card : ℝ) →
        (∀ j, c' (v j) = y (v j)) → c' = c := by
  obtain ⟨H, hHC, hHr, hmem⟩ := hspan y
  obtain ⟨v, hcv, huniq⟩ := frs_exists_recovering_tuple domain k s ω L hL_dom hω0 hadm
    hkLs hkord hk1 hθθ' hθ'1 r hrs H hHC hHr y c (hmem c hc hagree) hagree
  exact ⟨v, hcv, fun c' hc' hclose' hagree' => huniq c' (hmem c' hc' hclose') hagree'⟩

/-! ## 5b. Brick 2 — the span-of-list glue: G2 collapses to a per-word list-size bound

The in-tree CZ25 chain (`ListDecoding/CZ25SpanBoundBridge.lean`,
`ListDecoding/CZ25CapacityReduction.lean`, `ListDecoding/CZ25GeomCapacity.lean`) already
bounds the FRS list size `Λ(frsCode, δ)` conditional on the single named residual
`CodingTheory.CZ25CoordFiberCap` (the workbench §2.5 R2 GAP). The theorems below convert any
per-received-word list-size bound at relative radius `1 − θ'` into `FrsCloseListSpanBound`:
the witness subspace is simply the span of the close list, with `finrank ≤ ncard ≤ r`. So
gap G2 of the map doc is NOT a from-scratch CZ25 formalization — modulo the `ℕ∞`/`ENNReal`
cast of the in-tree `Lambda` endpoints, it collapses to `CZ25CoordFiberCap`. -/

open Classical in
/-- **Brick 2 (the G2 collapse).** A per-received-word list-size bound at relative radius
`1 − θ'` yields `FrsCloseListSpanBound domain k s ω θ' r`: take `H` := the span of the close
list `Λ(C, 1−θ', y)`; then `H ≤ C`, `finrank H ≤ |Λ(C, 1−θ', y)| ≤ r`, and every codeword
agreeing with `y` on `≥ θ'·n` folded coordinates has relative distance `≤ 1 − θ'`, hence lies
in the list, hence in `H`. Zero deep content — this is the glue that lets the in-tree CZ25
`Λ`-bounds (conditional on `CZ25CoordFiberCap`) feed the folded pin. -/
theorem frsCloseListSpanBound_of_listBound
    (domain : ι ↪ F) (k s : ℕ) (ω : F) (θ' : ℝ) (r : ℕ)
    (hlist : ∀ y : ι → Fin s → F,
      (ListDecodable.closeCodewordsRel
        ((ReedSolomon.Folded.frsCode domain k s ω : Submodule F (ι → Fin s → F)) :
          Set (ι → Fin s → F)) y (1 - θ')).ncard ≤ r) :
    FrsCloseListSpanBound domain k s ω θ' r := by
  classical
  intro y
  set S : Set (ι → Fin s → F) :=
    ListDecodable.closeCodewordsRel
      ((ReedSolomon.Folded.frsCode domain k s ω : Submodule F (ι → Fin s → F)) :
        Set (ι → Fin s → F)) y (1 - θ') with hSdef
  haveI : Fintype S := (Set.toFinite S).fintype
  refine ⟨Submodule.span F S, ?_, ?_, ?_⟩
  · rw [Submodule.span_le]
    exact fun c hc => hc.1
  · calc Module.finrank F (Submodule.span F S)
        ≤ S.toFinset.card := finrank_span_le_card (R := F) S
      _ = S.ncard := (Set.ncard_eq_toFinset_card' S).symm
      _ ≤ r := hlist y
  · intro c hcC hagree
    have hn_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
    -- the ball bound with THIS context's decidability instances
    have key : ((Code.relHammingDist y c : ℚ≥0) : ℝ) ≤ 1 - θ' := by
      unfold Code.relHammingDist
      simp only [NNRat.cast_div, NNRat.cast_natCast]
      rw [div_le_iff₀ hn_pos]
      -- partition: agreement + distance = n
      have hpart : (univ.filter (fun i : ι => y i = c i)).card + hammingDist y c
          = Fintype.card ι := by
        rw [hammingDist]
        simpa using Finset.card_filter_add_card_filter_not (s := (univ : Finset ι))
          (p := fun i : ι => y i = c i)
      have horder : (univ.filter (fun i : ι => y i = c i))
          = (univ.filter (fun i : ι => c i = y i)) :=
        Finset.filter_congr (fun i _ => eq_comm)
      have hpartR : ((univ.filter (fun i : ι => c i = y i)).card : ℝ)
          + (hammingDist y c : ℝ) = (Fintype.card ι : ℝ) := by
        exact_mod_cast horder ▸ hpart
      linarith [hagree, hpartR]
    -- transport across the `Classical` instances baked into `relHammingBall`
    have hball : c ∈ ListDecodable.relHammingBall y (1 - θ') := by
      simp only [ListDecodable.relHammingBall, Set.mem_setOf_eq]
      convert key using 3
    exact Submodule.subset_span (show c ∈ S from ⟨hcC, hball⟩)

/-- **Brick 2, `listDecodable` form.** The hypothesis in the in-tree `listDecodable` shape
(`ListDecodability.lean`): if the folded code is `(1 − θ', r)`-list-decodable then the close
lists span `≤ r` dimensions and `FrsCloseListSpanBound domain k s ω θ' r` holds. -/
theorem frsCloseListSpanBound_of_listDecodable
    (domain : ι ↪ F) (k s : ℕ) (ω : F) (θ' : ℝ) (r : ℕ)
    (hld : ListDecodable.listDecodable
      ((ReedSolomon.Folded.frsCode domain k s ω : Submodule F (ι → Fin s → F)) :
        Set (ι → Fin s → F)) (1 - θ') (r : ℝ)) :
    FrsCloseListSpanBound domain k s ω θ' r :=
  frsCloseListSpanBound_of_listBound domain k s ω θ' r (fun y => by exact_mod_cast hld y)

/-! ## 6. The lane target (named, OPEN) and the honesty flags -/

/-- **THE LANE TARGET — OPEN; a named `Prop`, not a theorem.** The folded-RS MCA pin against
the real prize-facing object: `ε_mca(FRS[F, L, k, s, ω], δ) ≤ Λ/q`. The intended parameters
(GG25/JLR) are `δ` up to `1 − ρ_block − η` (capacity in the FOLDED metric) with
`Λ = poly(n, 1/η)`. Assembly route: G0 (sharp profile) + G2 (`FrsCloseListSpanBound`) +
G3 (curve list-size from the recovery tuple) + the proven engine
(`curveDecodable_of_curveListSize`, `all_seeds_close_of_curveDecodable`) + G4 (the
`mcaEvent` weld, pattern `LineListMCAWeld`). See the map doc for effort estimates. -/
def FrsMCAPin (domain : ι ↪ F) (k s : ℕ) (ω : F) (δ : ℝ≥0) (Λ : ℕ) : Prop :=
  epsMCA (F := F)
    ((ReedSolomon.Folded.frsCode domain k s ω : Submodule F (ι → Fin s → F)) :
      Set (ι → Fin s → F)) δ
    ≤ (Λ : ENNReal) / (Fintype.card F : ENNReal)

end Folded

/-- Honest classification: this lane banks folded-domain (FRI/STIR/WHIR-facing) soundness;
it does NOT close, advance, or bound the plain-RS δ\* prize core (dossier §11.6 goal (B)).
`FoldingTransferNoGo.folding_transfer_no_go` proves the folded conclusion cannot transfer to
the plain metric. -/
def isPrizeClosure : Prop := False

theorem not_prizeClosure : ¬ isPrizeClosure := id

end ProximityGap.FoldedPin

-- Axiom audit: every theorem must report exactly `[propext, Classical.choice, Quot.sound]`
-- (no `sorryAx`).
#print axioms ProximityGap.FoldedPin.card_surv_ge_of_vanishBudget
#print axioms ProximityGap.FoldedPin.exists_surv_tuple_of_vanishBudget
#print axioms ProximityGap.FoldedPin.exists_determining_tuple_of_vanishBudget
#print axioms ProximityGap.FoldedPin.vanishBudget_of_design
#print axioms ProximityGap.FoldedPin.exists_determining_tuple_ranked
#print axioms ProximityGap.FoldedPin.no_unranked_theta_for_gk16Profile
#print axioms ProximityGap.FoldedPin.frs_exists_determining_tuple
#print axioms ProximityGap.FoldedPin.frs_exists_recovering_tuple
#print axioms ProximityGap.FoldedPin.frs_close_codeword_unique_recovery
#print axioms ProximityGap.FoldedPin.frsCloseListSpanBound_of_listBound
#print axioms ProximityGap.FoldedPin.frsCloseListSpanBound_of_listDecodable
#print axioms ProximityGap.FoldedPin.not_prizeClosure

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.OnePunctureRetention
import ArkLib.Research.ProximityGap.Frontier.LocatorShortening
import ArkLib.Research.ProximityGap.Frontier.QuarterRateTwoRichFloor

/-! # A two-dimensional window of exact two-head probabilities

At fixed dimension and error count, a uniform scalar cap strictly below the
original length persists at every longer length. The two-head lower bound
remains attainable through length `k + 2e`. -/
set_option autoImplicit false
noncomputable section
open Finset Code
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.PunctureTwoHeadWindow
open _root_.ProximityGap _root_.ProximityGap.Ownership _root_.ProximityGap.MCAThresholdLedger
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
open Classical in
/-- A count cap below the initial block length never increases under lengthening
at fixed dimension and error count. Each induction step uses integrality. -/
theorem stable {m k e B : ℕ} (hB : B < m) (hroom : k + 1 ≤ m - e)
    (seed : ∀ (dom : Fin m ↪ F) (u v : Fin m → F),
      (univ.filter fun g : F => mcaEvent (ReedSolomon.code dom k : Set (Fin m → F))
        ((e : ℝ≥0) / m) u v g).card ≤ B)
    (r : ℕ) (dom : Fin (m + r) ↪ F) (u v : Fin (m + r) → F) :
    (univ.filter fun g : F => mcaEvent (ReedSolomon.code dom k : Set (Fin (m + r) → F))
      ((e : ℝ≥0) / (m + r : ℕ)) u v g).card ≤ B := by
  classical
  induction r with
  | zero => exact seed dom u v
  | succ r ih =>
    have bound := OnePunctureRetention.count (by omega : 0 < m + r)
      (by omega : k + 2 ≤ m + r + 1 - e) dom u v
      (fun i => ih (punctureDom dom i) (u ∘ i.succAbove) (v ∘ i.succAbove))
    let A := (univ.filter fun g : F => mcaEvent
      (ReedSolomon.code dom k : Set (Fin (m + (r + 1)) → F)) ((e : ℝ≥0) / (m + (r + 1) : ℕ)) u v g).card
    change A * (m + r) ≤ (m + r + 1) * B at bound
    change A ≤ B
    by_contra! large
    have lower := Nat.mul_le_mul_right (m + r) (Nat.succ_le_of_lt large)
    rw [Nat.succ_mul] at lower
    rw [Nat.succ_mul, mul_comm (m + r) B] at bound
    omega

/-- A seed bound on the worst probability transfers to longer domains without
any loss when its numerator is less than the seed length. -/
theorem stable_eps {m k e B : ℕ} [NeZero m] (hB : B < m) (hroom : k + 1 ≤ m - e)
    (seed : ∀ dom : Fin m ↪ F,
      epsMCA (F := F) (ReedSolomon.code dom k : Set (Fin m → F)) ((e : ℝ≥0) / m) ≤
        (B : ℝ≥0∞) / Fintype.card F)
    (r : ℕ) (dom : Fin (m + r) ↪ F) :
    epsMCA (F := F) (ReedSolomon.code dom k : Set (Fin (m + r) → F))
      ((e : ℝ≥0) / (m + r : ℕ)) ≤ (B : ℝ≥0∞) / Fintype.card F := by
  classical
  let : NeZero (m + r) := ⟨by omega⟩
  apply epsMCA_le_of_badCount_le
  intro u
  apply stable hB hroom _ r dom (u 0) (u 1)
  intro x v w
  let a : WordStack F (Fin 2) (Fin m) := ![v, w]
  have cap := seed x
  have q₀ : (Fintype.card F : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have qtop := ENNReal.natCast_ne_top (Fintype.card F)
  rw [epsMCA_eq_iSup_badCount_div, ENNReal.div_le_iff q₀ qtop, ENNReal.div_mul_cancel q₀ qtop] at cap
  exact Nat.cast_le.mp ((le_iSup _ a).trans cap)

abbrev n : ℕ := 1073741824
abbrev k : ℕ := 268435456
abbrev tolerance : ℝ≥0∞ := 1 / ((2 ^ 128 : ℕ) : ℝ≥0∞)

variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]

/-- The two-head cap holds on every longer domain, including lengths beyond
the range in which the matching two-head construction fits. -/
theorem upper (dom : I ↪ F) (length : n ≤ Fintype.card I) {e : ℕ}
    (lo : 402653184 ≤ e) (hi : e ≤ 447392427)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1968526676 → (i : F) ≠ 0) :
    epsMCA (F := F) (ReedSolomon.code dom k : Set (I → F)) ((e : ℝ≥0) / Fintype.card I) ≤
      ((2 * (e + 1) : ℕ) : ℝ≥0∞) / Fintype.card F := by
  let r := Fintype.card I - n
  have hn : Fintype.card I = n + r := by dsimp [r]; omega
  let d := Fintype.equivFinOfCardEq hn
  let x := d.symm.toEmbedding.trans dom
  rw [MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq d.symm x dom (fun _ => rfl), hn]
  apply stable_eps (by unfold n; omega) (by unfold k n; omega)
  intro y
  simpa only [Fintype.card_fin] using
    (QuarterRateTwoRichFloor.exact_through_saturation y (Fintype.card_fin _) lo hi (fun i h h' => hchar i h (by omega))).le

/-- Shorten a longer domain back to the desired dimension, preserving the cap
when the redundancy is at least that of the original quarter-rate code. -/
theorem upper_varying (dom : I ↪ F) {K e : ℕ} (pos : 0 < K) (dim : K ≤ k)
    (redundancy : 805306368 + K ≤ Fintype.card I)
    (room : Fintype.card I + (k - K) ≤ Fintype.card F)
    (lo : 402653184 ≤ e) (hi : e ≤ 447392427)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1968526676 → (i : F) ≠ 0) :
    epsMCA (F := F) (ReedSolomon.code dom K : Set (I → F)) ((e : ℝ≥0) / Fintype.card I) ≤
      ((2 * (e + 1) : ℕ) : ℝ≥0∞) / Fintype.card F := by
  let d := Fintype.equivFin I
  let x := d.symm.toEmbedding.trans dom
  let N := Fintype.card I + (k - K)
  let : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  let : NeZero N := ⟨by dsimp [N]; omega⟩
  obtain ⟨old, D, he⟩ := LocatorShortening.exists_extended_domain x (N := N) (by dsimp [N]; omega) room
  have tr := LocatorShortening.eps_le_extension old D pos e
  have lift : K + (N - Fintype.card I) = k := by dsimp [N]; omega
  rw [he, lift] at tr
  rw [MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq d.symm x dom (fun _ => rfl)]
  have hN : n ≤ Fintype.card (Fin N) := by rw [Fintype.card_fin]; dsimp [N,n,k] at *; omega
  exact tr.trans (by simpa only [Fintype.card_fin] using upper D hN lo hi hchar)

omit [DecidableEq F] [Nonempty I] [DecidableEq I] in
private theorem enough_sites {K e : ℕ} (hi : e ≤ 447392428) (fit : Fintype.card I ≤ K + 2 * e)
    (Kle : K ≤ k) (hchar : ∀ i : ℕ, 0 < i → i ≤ 1968526676 → (i : F) ≠ 0) :
    Fintype.card I + (k - K) ≤ Fintype.card F := by
  have q : 1968526676 < Fintype.card F := by
    by_contra! small
    exact hchar _ Fintype.card_pos small (Nat.cast_card_eq_zero F)
  unfold k at *
  omega

/-- Exact worst-pair probability throughout the two-head window, including
every positive interleaving width and every injective domain. -/
theorem exact_eps (dom : I ↪ F) {K e : ℕ} (dim : K ≤ k)
    (redundancy : 805306368 + K ≤ Fintype.card I) (private_room : 2 * (e + 1) ≤ Fintype.card I)
    (lo : 402653184 ≤ e) (hi : e ≤ 447392427) (fit : Fintype.card I ≤ K + 2 * e)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1968526676 → (i : F) ≠ 0)
    (width : ℕ) [NeZero width] :
    epsMCA (F := F) ((ReedSolomon.code dom K : Set (I → F)) ^⋈ (Fin width))
      ((e : ℝ≥0) / Fintype.card I) = ((2 * (e + 1) : ℕ) : ℝ≥0∞) / Fintype.card F := by
  rw [epsMCA_interleaved_eq]
  exact le_antisymm (upper_varying dom (by omega) dim redundancy
    (enough_sites (by omega) fit dim hchar) lo hi hchar)
    (TwoHeadLinearBudget.errors dom private_room fit (by omega))

/-- At a given length and budget the last safe step only needs the uniform
upper bound. The two-head layout is required at the first failing step. -/
theorem classification (dom : I ↪ F) {K B : ℕ} (dim : K ≤ k)
    (redundancy : 805306368 + K ≤ Fintype.card I)
    (private_room : 2 * (B / 2 + 1) ≤ Fintype.card I)
    (hB : Fintype.card F / 2 ^ 128 = B) (lo : 805306370 ≤ B) (hi : B ≤ 894784857)
    (fit : Fintype.card I ≤ K + 2 * (B / 2))
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1968526676 → (i : F) ≠ 0)
    (width : ℕ) [NeZero width] :
    let t : ℝ≥0 := ((B / 2 : ℕ) : ℝ≥0) / Fintype.card I
    mcaDeltaStar (F := F) ((ReedSolomon.code dom K : Set (I → F)) ^⋈ (Fin width)) tolerance = t ∧
      ∀ δ, epsMCA (F := F) ((ReedSolomon.code dom K : Set (I → F)) ^⋈ (Fin width)) δ ≤ tolerance ↔ δ < t := by
  let e := B / 2
  let C := (ReedSolomon.code dom K : Set (I → F))
  let t : ℝ≥0 := (e : ℝ≥0) / Fintype.card I
  have ratio (a : ℕ) : (a : ℝ≥0∞) / Fintype.card F ≤ tolerance ↔ a ≤ B :=
    hB ▸ BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by decide)
  have good : epsMCA (F := F) C (((e - 1 : ℕ) : ℝ≥0) / Fintype.card I) ≤ tolerance :=
    (upper_varying dom (by omega) dim redundancy (enough_sites (by omega) fit dim hchar)
      (by dsimp [e]; omega) (by dsimp [e]; omega) hchar).trans
      ((ratio _).mpr (by dsimp [e]; omega))
  have bad : tolerance < epsMCA (F := F) C t := by
    have attack := TwoHeadLinearBudget.errors dom (e := e) (k := K)
      private_room fit (by dsimp [e]; omega)
    exact lt_of_lt_of_le (lt_of_not_ge (fun h => (by dsimp [e]; omega : ¬2 * (e + 1) ≤ B)
      ((ratio _).mp h))) attack
  let d := Fintype.equivFin I
  let x := d.symm.toEmbedding.trans dom
  have hre := MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq d.symm x dom (fun _ => rfl) K
  let : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  have eq : mcaDeltaStar (F := F) C tolerance = t := by
    rw [show C = (ReedSolomon.code dom K : Set (I → F)) by rfl,
      MCAReindexThresholdEquiv.mcaDeltaStar_reindex_reedSolomon_eq d.symm x dom (fun _ => rfl)]
    apply MCAAdjacentFloorExactPin.mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad
      (a := e) (by dsimp [e]; omega) (by dsimp [e]; omega)
    · rw [← hre]; exact good
    · rw [← hre]; exact bad
  refine ⟨by rw [mcaDeltaStar_interleaved_eq]; exact eq, ?_⟩
  intro δ
  rw [epsMCA_interleaved_eq]
  constructor
  · intro safe
    by_contra! hδ
    exact bad.not_ge ((epsMCA_mono C hδ).trans safe)
  · intro hδ
    by_contra! unsafeAt
    have h := mcaDeltaStar_le_of_bad C tolerance unsafeAt
    rw [eq] at h
    exact hδ.not_ge h

#print axioms stable_eps
#print axioms exact_eps
#print axioms classification
end ArkLib.ProximityGap.Frontier.PunctureTwoHeadWindow

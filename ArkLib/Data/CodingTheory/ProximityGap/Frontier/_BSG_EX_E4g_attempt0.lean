/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BSG_EX_E4f_PathCalibrate

/-!
# BSG `E4g` — `PrunedFibreWithEnergy` as written is FALSE (the apex-confinement bug)

This file settles the achievability of the named residual `PrunedFibreWithEnergy` (stated in
`_BSG_EX_E4f_PathCalibrate.lean`). The downstream chain
`PrunedFibreWithEnergy → RelativeDiffCalibration → DRCRuzsaInputFixed → BareDRCExtract → BSGCore →
balog_szemeredi_gowers` is genuinely proven axiom-clean, **but its premise can never be supplied**:
`PrunedFibreWithEnergy C₁ s_C s_c` is FALSE for **every** choice of the constants `C₁, s_C, s_c`.

## The bug: apex confinement vs. the K-scale size demand

`PrunedFibreWithEnergy` requires the output set `A''` to satisfy *both*

* **apex confinement** `A'' ⊆ leftNbhd A G b₀` (so `#A'' ≤ rDeg A G b₀`), and
* the **K-scale size calibration** `C₁ · K · #A'' ≥ #A`.

But the only datum tying `b₀` to a large neighbourhood is `#A ≤ 4 K² · rDeg A G b₀` — a `K²`-scale
bound. On an instance where this holds with equality (`rDeg b₀ = #A / (4K²)` exactly), apex
confinement forces `#A'' ≤ #A / (4K²)`, hence `C₁ · K · #A'' ≤ C₁ · #A / (4K)`, which is `< #A` once
`K > C₁ / 4`. No *constant* `C₁` can win against a growing `K`.

The genuine Tao–Vu Lemma 2.30 escapes this precisely because it does **not** confine the output to
`leftNbhd b₀`: the K-scale gain comes from a *second* fibre `b₁` chosen by apex-averaging on the
cherry mass, and `A''` is pruned out of `leftNbhd b₁` (or more generally out of `A`), not out of
the size-`#A/(4K²)` set `leftNbhd b₀`. The residual as written hard-codes `A'' ⊆ leftNbhd b₀`,
which is the bug. (Compare `BareDRCExtract`, whose output obligation is `A' ⊆ A` — *not* confined to
any single neighbourhood — and which is therefore satisfiable on the very instance below by taking
`A' = A`.)

## The countermodel (machine-checked here)

Over `α = ℤ`, with `K = C₁ + 1`, `A = {0, 1, …, 4K² − 1}` (cardinality `4K²`) and the **diagonal**
graph `G = {(a, a) : a ∈ A}`:

* `rDeg A G b = 1` for every `b ∈ A`, so `leftNbhd A G b = {b}` and `#G = #A`,
  `∑_b rDeg² = #A`;
* the three hypotheses of `PrunedFibreWithEnergy` (`#A² ≤ 4K²#G`, `#A⁴ ≤ 16K⁴(#A·∑rDeg²)`,
  `#A ≤ 4K²·rDeg b₀`) all hold **with equality** (each reduces to `#A = 4K²`);
* but any `A'' ⊆ leftNbhd b₀ = {b₀}` that is nonempty has `#A'' = 1`, so the demanded
  `C₁ · K · #A'' ≥ #A` reads `C₁ · K ≥ 4K²`, i.e. `C₁ ≥ 4K = 4C₁ + 4`, a contradiction.

## Status

`PROVES-PRUNED` (refutation). `prunedFibreWithEnergy_false : ∀ C₁ s_C s_c, ¬ PrunedFibreWithEnergy
C₁ s_C s_c` is proven axiom-clean. The downstream calibration in `_BSG_EX_E4f_PathCalibrate.lean`
is correct, but `PrunedFibreWithEnergy` is the **wrong target** — its apex-confinement clause makes
its premise unsatisfiable, so it cannot complete BSG. The honest next residual must drop
`A'' ⊆ leftNbhd b₀` (replacing it with `A'' ⊆ A`, or with confinement to a *second* fibre `b₁`
whose neighbourhood is K-scale large) — i.e. the genuine Tao–Vu shape. The smallest residual that
still closes the chain is named here (`PrunedFibreWithEnergyFixed`) with the confinement clause
relaxed to `A'' ⊆ A`; it is NOT proven (the K-scale extraction is the real open core).

## References
* T. Tao, V. Vu, *Additive Combinatorics*, Cambridge (2006), Lemma 2.30, Theorem 2.29.
-/

open Finset
open scoped BigOperators Pointwise

namespace Finset.BSG

/-! ## The diagonal graph and its degrees -/

/-- The **diagonal graph** on `A`: `{(a, a) : a ∈ A}`. -/
noncomputable def diagGraph {α : Type*} [DecidableEq α] (A : Finset α) : Finset (α × α) :=
  A.image (fun a => (a, a))

lemma diagGraph_subset {α : Type*} [DecidableEq α] (A : Finset α) :
    diagGraph A ⊆ A ×ˢ A := by
  intro p hp
  rw [diagGraph, Finset.mem_image] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  exact Finset.mem_product.mpr ⟨ha, ha⟩

lemma mem_diagGraph {α : Type*} [DecidableEq α] {A : Finset α} {p : α × α} :
    p ∈ diagGraph A ↔ p.1 ∈ A ∧ p.1 = p.2 := by
  rw [diagGraph, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨ha, rfl⟩
  · obtain ⟨x, y⟩ := p
    rintro ⟨hx, hxy⟩
    simp only at hx hxy
    subst hxy
    exact ⟨x, hx, rfl⟩

/-- On the diagonal graph, the left-neighbourhood of any `b ∈ A` is the singleton `{b}`. -/
lemma leftNbhd_diagGraph {α : Type*} [AddCommGroup α] [DecidableEq α]
    (A : Finset α) {b : α} (hb : b ∈ A) :
    leftNbhd A (diagGraph A) b = {b} := by
  ext a
  rw [leftNbhd, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hab⟩
    rw [mem_diagGraph] at hab
    exact hab.2
  · rintro rfl
    refine ⟨hb, ?_⟩
    rw [mem_diagGraph]
    exact ⟨hb, rfl⟩

/-- On the diagonal graph, every `b ∈ A` has degree `1`. -/
lemma rDeg_diagGraph {α : Type*} [AddCommGroup α] [DecidableEq α]
    (A : Finset α) {b : α} (hb : b ∈ A) :
    rDeg A (diagGraph A) b = 1 := by
  rw [← card_leftNbhd, leftNbhd_diagGraph A hb, Finset.card_singleton]

/-- The diagonal graph has exactly `#A` edges. -/
lemma card_diagGraph {α : Type*} [DecidableEq α] (A : Finset α) :
    #(diagGraph A) = #A := by
  have hinj : Function.Injective (fun a : α => (a, a)) := by
    intro a a' h
    exact (Prod.mk.injEq _ _ _ _).mp h |>.1
  rw [diagGraph, Finset.card_image_of_injective A hinj]

/-- The cherry count of the diagonal graph is `#A` (each fibre contributes `1² = 1`). -/
lemma sum_rDeg_sq_diagGraph {α : Type*} [AddCommGroup α] [DecidableEq α] (A : Finset α) :
    ∑ b ∈ A, rDeg A (diagGraph A) b ^ 2 = #A := by
  rw [Finset.sum_congr rfl (fun b hb => by rw [rDeg_diagGraph A hb])]
  simp

/-! ## The refutation -/

/-- **`PrunedFibreWithEnergy` is FALSE for every choice of constants.**

The clause `A'' ⊆ leftNbhd A G b₀` (apex confinement) is incompatible with the K-scale size
demand `C₁ · K · #A'' ≥ #A`. On the diagonal instance over `ℤ` with `K = C₁ + 1` and
`#A = 4K²`, every left-neighbourhood is a singleton, so apex confinement forces `#A'' = 1` and the
size demand collapses to `C₁ ≥ 4K = 4C₁ + 4`, impossible.

This shows `PrunedFibreWithEnergy` is the **wrong target**: although every theorem downstream of it
is genuinely proven axiom-clean, its premise can never be supplied by the real DRC argument. -/
theorem prunedFibreWithEnergy_false (C₁ s_C s_c : ℕ) :
    ¬ PrunedFibreWithEnergy C₁ s_C s_c := by
  intro h
  classical
  -- The instance.
  set K : ℕ := C₁ + 1 with hK
  have hKpos : 0 < K := by omega
  -- `A = {0, …, 4K²-1} ⊆ ℤ` via the image of `range (4K²)`.
  set N : ℕ := 4 * K ^ 2 with hN
  have hNpos : 0 < N := by positivity
  have hinjZ : Function.Injective (fun n : ℕ => (n : ℤ)) := by
    intro a b hab
    simp only at hab
    exact Nat.cast_inj.mp hab
  set A : Finset ℤ := (Finset.range N).image (fun n : ℕ => (n : ℤ)) with hA
  have hAcard : #A = N := by
    rw [hA, Finset.card_image_of_injective _ hinjZ, Finset.card_range]
  have hAne : A.Nonempty := by
    rw [← Finset.card_pos, hAcard]; exact hNpos
  -- A representative `b₀ ∈ A` (keep `hAne` alive for the application below).
  set b₀ : ℤ := hAne.choose with hb₀def
  have hb₀ : b₀ ∈ A := hAne.choose_spec
  -- The diagonal graph.
  set G : Finset (ℤ × ℤ) := diagGraph A with hG
  have hGsub : G ⊆ A ×ˢ A := diagGraph_subset A
  -- Degree facts.
  have hrDeg_b₀ : rDeg A G b₀ = 1 := rDeg_diagGraph A hb₀
  have hcardG : #G = #A := card_diagGraph A
  have hcherrySum : ∑ b ∈ A, rDeg A G b ^ 2 = #A := sum_rDeg_sq_diagGraph A
  -- `#A = N = 4K²`.
  have hAN : #A = 4 * K ^ 2 := by rw [hAcard]
  -- Verify the three hypotheses (each reduces to `#A = 4K²`, holding with equality).
  have hH1 : #A ^ 2 ≤ 4 * K ^ 2 * #G := by
    rw [hcardG, hAN]; exact le_of_eq (by ring)
  have hH2 : #A ^ 4 ≤ 16 * K ^ 4 * (#A * ∑ b ∈ A, rDeg A G b ^ 2) := by
    rw [hcherrySum, hAN]; exact le_of_eq (by ring)
  have hH3 : #A ≤ 4 * K ^ 2 * rDeg A G b₀ := by
    rw [hrDeg_b₀, hAN, mul_one]
  -- Apply the (false) hypothesis.
  obtain ⟨A'', b₁, s, _hb₁, hsub, hne, _hBne, _hsbd, hsize₁, _hsize₂, _hrich, _henergy⟩ :=
    h A K G b₀ hKpos hAne hGsub hb₀ hH1 hH2 hH3
  -- Apex confinement forces `A'' ⊆ {b₀}`, hence `#A'' = 1`.
  have hsub' : A'' ⊆ {b₀} := by
    rw [← leftNbhd_diagGraph A hb₀]; exact hsub
  have hcardA'' : #A'' = 1 := by
    have hle : #A'' ≤ 1 := by
      calc #A'' ≤ #({b₀} : Finset ℤ) := Finset.card_le_card hsub'
        _ = 1 := Finset.card_singleton _
    have hpos : 0 < #A'' := hne.card_pos
    omega
  -- The size calibration `C₁·K·#A'' ≥ #A` becomes `C₁·K ≥ 4K²`, i.e. `C₁ ≥ 4K`.
  rw [hcardA'', mul_one, hAN] at hsize₁
  -- hsize₁ : 4 * K ^ 2 ≤ C₁ * K.  Cancel K > 0: 4K ≤ C₁.  But K = C₁+1 ⇒ contradiction.
  have hcancel : 4 * K ≤ C₁ := by
    have hmul : 4 * K * K ≤ C₁ * K := by
      have : 4 * K ^ 2 = 4 * K * K := by ring
      omega
    exact Nat.le_of_mul_le_mul_right hmul hKpos
  rw [hK] at hcancel
  omega

/-! ## The bug is inherited — the entire Ruzsa chain shares it

The apex-confinement clause `A'' ⊆ leftNbhd A G b₀` paired with the K-scale size demand
`C₁ · K · #A'' ≥ #A` is **not** unique to `PrunedFibreWithEnergy`. The identical pair appears in:

* `DRCRuzsaInput` (`_BSG_EX_E4d_Ruzsa.lean`, the conclusion clause `A'' ⊆ leftNbhd A G b₀` with
  `C₁ * K * #A'' ≥ #A`),
* `DRCRuzsaInputFixed` (`_BSG_EX_E4e_RuzsaShapeAudit.lean`),
* `RelativeDiffCalibration` (`_BSG_EX_E4e_PathCount.lean`), and
* `PrunedFibreWithEnergy` (`_BSG_EX_E4f_PathCalibrate.lean`).

So **all four are FALSE** by the same diagonal countermodel: each requires producing an
`A'' ⊆ leftNbhd A G b₀` with `C₁ K #A'' ≥ #A`, which the diagonal instance (every
`leftNbhd b₀` a singleton, `#A = 4K²`) makes impossible. We record the refutations of the two
closest residuals; `RelativeDiffCalibration_false` and `DRCRuzsaInputFixed_false` follow because the
relevant conclusion clauses (`A'' ⊆ leftNbhd b₀`, `C₁ K #A'' ≥ #A`, `A''.Nonempty`) are present in
every variant and are exactly the ones the countermodel contradicts. -/

/-- **`RelativeDiffCalibration` is FALSE for every choice of constants** — same apex-confinement bug.
Its conclusion clause `A'' ⊆ leftNbhd A G b₀ ∧ … ∧ C₁ K #A'' ≥ #A ∧ A''.Nonempty` is contradicted
by the diagonal countermodel exactly as for `PrunedFibreWithEnergy`. -/
theorem relativeDiffCalibration_false (C₁ s_C s_c : ℕ) :
    ¬ RelativeDiffCalibration C₁ s_C s_c := by
  intro h
  classical
  set K : ℕ := C₁ + 1 with hK
  have hKpos : 0 < K := by omega
  set N : ℕ := 4 * K ^ 2 with hN
  have hNpos : 0 < N := by positivity
  have hinjZ : Function.Injective (fun n : ℕ => (n : ℤ)) := by
    intro a b hab
    simp only at hab
    exact Nat.cast_inj.mp hab
  set A : Finset ℤ := (Finset.range N).image (fun n : ℕ => (n : ℤ)) with hA
  have hAcard : #A = N := by
    rw [hA, Finset.card_image_of_injective _ hinjZ, Finset.card_range]
  have hAne : A.Nonempty := by
    rw [← Finset.card_pos, hAcard]; exact hNpos
  set b₀ : ℤ := hAne.choose with hb₀def
  have hb₀ : b₀ ∈ A := hAne.choose_spec
  set G : Finset (ℤ × ℤ) := diagGraph A with hG
  have hGsub : G ⊆ A ×ˢ A := diagGraph_subset A
  have hrDeg_b₀ : rDeg A G b₀ = 1 := rDeg_diagGraph A hb₀
  have hcardG : #G = #A := card_diagGraph A
  have hcherrySum : ∑ b ∈ A, rDeg A G b ^ 2 = #A := sum_rDeg_sq_diagGraph A
  have hAN : #A = 4 * K ^ 2 := by rw [hAcard]
  have hH1 : #A ^ 2 ≤ 4 * K ^ 2 * #G := by rw [hcardG, hAN]; exact le_of_eq (by ring)
  have hH2 : #A ^ 4 ≤ 16 * K ^ 4 * (#A * ∑ b ∈ A, rDeg A G b ^ 2) := by
    rw [hcherrySum, hAN]; exact le_of_eq (by ring)
  have hH3 : #A ≤ 4 * K ^ 2 * rDeg A G b₀ := by rw [hrDeg_b₀, hAN, mul_one]
  obtain ⟨A'', b₁, s, _hb₁, hsub, hne, _hBne, _hsbd, hsize₁, _hdiff, _hsize₂⟩ :=
    h A K G b₀ hKpos hAne hGsub hb₀ hH1 hH2 hH3
  have hsub' : A'' ⊆ {b₀} := by rw [← leftNbhd_diagGraph A hb₀]; exact hsub
  have hcardA'' : #A'' = 1 := by
    have hle : #A'' ≤ 1 := by
      calc #A'' ≤ #({b₀} : Finset ℤ) := Finset.card_le_card hsub'
        _ = 1 := Finset.card_singleton _
    have hpos : 0 < #A'' := hne.card_pos
    omega
  rw [hcardA'', mul_one, hAN] at hsize₁
  have hcancel : 4 * K ≤ C₁ := by
    have hmul : 4 * K * K ≤ C₁ * K := by
      have : 4 * K ^ 2 = 4 * K * K := by ring
      omega
    exact Nat.le_of_mul_le_mul_right hmul hKpos
  rw [hK] at hcancel; omega

/-- **`DRCRuzsaInputFixed` is FALSE for every choice of constants** — same apex-confinement bug,
at the root of the Ruzsa chain. -/
theorem drcRuzsaInputFixed_false (C₁ s_C s_c : ℕ) :
    ¬ DRCRuzsaInputFixed C₁ s_C s_c := by
  intro h
  classical
  set K : ℕ := C₁ + 1 with hK
  have hKpos : 0 < K := by omega
  set N : ℕ := 4 * K ^ 2 with hN
  have hNpos : 0 < N := by positivity
  have hinjZ : Function.Injective (fun n : ℕ => (n : ℤ)) := by
    intro a b hab
    simp only at hab
    exact Nat.cast_inj.mp hab
  set A : Finset ℤ := (Finset.range N).image (fun n : ℕ => (n : ℤ)) with hA
  have hAcard : #A = N := by
    rw [hA, Finset.card_image_of_injective _ hinjZ, Finset.card_range]
  have hAne : A.Nonempty := by
    rw [← Finset.card_pos, hAcard]; exact hNpos
  set b₀ : ℤ := hAne.choose with hb₀def
  have hb₀ : b₀ ∈ A := hAne.choose_spec
  set G : Finset (ℤ × ℤ) := diagGraph A with hG
  have hGsub : G ⊆ A ×ˢ A := diagGraph_subset A
  have hrDeg_b₀ : rDeg A G b₀ = 1 := rDeg_diagGraph A hb₀
  have hcardG : #G = #A := card_diagGraph A
  have hcherrySum : ∑ b ∈ A, rDeg A G b ^ 2 = #A := sum_rDeg_sq_diagGraph A
  have hAN : #A = 4 * K ^ 2 := by rw [hAcard]
  have hH1 : #A ^ 2 ≤ 4 * K ^ 2 * #G := by rw [hcardG, hAN]; exact le_of_eq (by ring)
  have hH2 : #A ^ 4 ≤ 16 * K ^ 4 * (#A * ∑ b ∈ A, rDeg A G b ^ 2) := by
    rw [hcherrySum, hAN]; exact le_of_eq (by ring)
  have hH3 : #A ≤ 4 * K ^ 2 * rDeg A G b₀ := by rw [hrDeg_b₀, hAN, mul_one]
  obtain ⟨A'', b₁, s, _hb₁, hsub, hne, _hBne, _hsbd, hsize₁, _hdiff, _hsize₂⟩ :=
    h A K G b₀ hKpos hAne hGsub hb₀ hH1 hH2 hH3
  have hsub' : A'' ⊆ {b₀} := by rw [← leftNbhd_diagGraph A hb₀]; exact hsub
  have hcardA'' : #A'' = 1 := by
    have hle : #A'' ≤ 1 := by
      calc #A'' ≤ #({b₀} : Finset ℤ) := Finset.card_le_card hsub'
        _ = 1 := Finset.card_singleton _
    have hpos : 0 < #A'' := hne.card_pos
    omega
  rw [hcardA'', mul_one, hAN] at hsize₁
  have hcancel : 4 * K ≤ C₁ := by
    have hmul : 4 * K * K ≤ C₁ * K := by
      have : 4 * K ^ 2 = 4 * K * K := by ring
      omega
    exact Nat.le_of_mul_le_mul_right hmul hKpos
  rw [hK] at hcancel; omega

/-! ## The honest fixed target (confinement relaxed to `A'' ⊆ A`) — NOT proven

The minimal repair drops apex confinement `A'' ⊆ leftNbhd b₀` to the genuine Tao–Vu obligation
`A'' ⊆ A`. The consumer `bareDRCExtract_of_ruzsaInput` only ever used `A'' ⊆ A` (via
`hsub.trans (filter_subset …)`), so the repaired residual still closes `BareDRCExtract` — proven
below (`bareDRCExtract_of_drcRuzsaInputFixedRepaired`). The K-scale extraction that supplies this
residual (apex-averaging on the cherry mass for a second fibre `b₁` whose neighbourhood is K-scale
large, then per-`a` Markov pruning out of `A`) is the genuine remaining open core; it is **not**
proven here. -/

/-- **`DRCRuzsaInputFixedRepaired` — the minimal repair (NOT proven).** Identical to
`DRCRuzsaInputFixed` except the apex-confinement clause `A'' ⊆ leftNbhd A G b₀` is relaxed to the
correct obligation `A'' ⊆ A`. This is the residual that genuinely closes the BSG chain; it is the
honest open target after the refutation of the as-written residuals. -/
def DRCRuzsaInputFixedRepaired (C₁ s_C s_c : ℕ) : Prop :=
  ∀ {α : Type} [inst : AddCommGroup α] [inst2 : DecidableEq α],
    ∀ (A : Finset α) (K : ℕ) (G : Finset (α × α)) (b₀ : α),
      0 < K → A.Nonempty → G ⊆ A ×ˢ A → b₀ ∈ A →
      #A ^ 2 ≤ 4 * K ^ 2 * #G →
      #A ^ 4 ≤ 16 * K ^ 4 * (#A * (∑ b ∈ A, rDeg A G b ^ 2)) →
      #A ≤ 4 * K ^ 2 * rDeg A G b₀ →
      ∃ (A'' : Finset α) (b₁ : α) (s : ℕ),
        b₁ ∈ A ∧
        A'' ⊆ A ∧ A''.Nonempty ∧ (leftNbhd A G b₁).Nonempty ∧
        s ≤ s_C * K ^ s_c ∧
        C₁ * K * #A'' ≥ #A ∧
        #(A'' - leftNbhd A G b₁) ≤ s * #A'' ∧
        #A'' ≤ s * #(leftNbhd A G b₁)

/-- **`DRCRuzsaInputFixedRepaired → BareDRCExtract`** (PROVEN axiom-clean). The repaired residual
(with `A'' ⊆ A` instead of the unsatisfiable `A'' ⊆ leftNbhd b₀`) still closes `BareDRCExtract`:
`BareDRCExtract` needs only `A'' ⊆ A`, nonemptiness, the K-scale size bound, and the doubling bound
— and the doubling comes from the proven Ruzsa triangle `card_diffSet_le_of_ruzsa` applied to
`B = leftNbhd A G b₁`, exactly as in `bareDRCExtract_of_ruzsaInput`. We cannot route through
`DRCRuzsaInput`/`DRCRuzsaInputFixed` (their *statements* still demand `A'' ⊆ leftNbhd b₀`); we go
directly to `BareDRCExtract`. -/
theorem bareDRCExtract_of_drcRuzsaInputFixedRepaired {C₁ s_C s_c : ℕ}
    (h : DRCRuzsaInputFixedRepaired C₁ s_C s_c) :
    BareDRCExtract C₁ (s_C ^ 3) (3 * s_c) := by
  intro α _ _ A K G b₀ hK hA hGsub hb₀ hdense hcherry hgood
  classical
  obtain ⟨A'', b₁, s, _hb₁, hsubA, hne, hBne, hsbd, hsize, hdiff, hcomp⟩ :=
    h A K G b₀ hK hA hGsub hb₀ hdense hcherry hgood
  refine ⟨A'', hsubA, hne, hsize, ?_⟩
  -- doubling via the Ruzsa triangle with `B = leftNbhd A G b₁`.
  have hdoub : #(A'' - A'') ≤ s * s * s * #A'' :=
    card_diffSet_le_of_ruzsa A'' (leftNbhd A G b₁) s hBne hdiff hcomp
  have hscube : s * s * s ≤ s_C ^ 3 * K ^ (3 * s_c) := by
    have hpow : s ^ 3 ≤ (s_C * K ^ s_c) ^ 3 := Nat.pow_le_pow_left hsbd 3
    have he : (s_C * K ^ s_c) ^ 3 = s_C ^ 3 * K ^ (3 * s_c) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm s_c 3]
    calc s * s * s = s ^ 3 := by ring
      _ ≤ (s_C * K ^ s_c) ^ 3 := hpow
      _ = s_C ^ 3 * K ^ (3 * s_c) := he
  calc #(A'' - A'') ≤ s * s * s * #A'' := hdoub
    _ ≤ (s_C ^ 3 * K ^ (3 * s_c)) * #A'' := by gcongr
    _ = s_C ^ 3 * K ^ (3 * s_c) * #A'' := by ring

end Finset.BSG

-- Axiom audit (refutations + the repaired reduction must be axiom-clean:
-- propext, Classical.choice, Quot.sound — and NO sorryAx).
#print axioms Finset.BSG.prunedFibreWithEnergy_false
#print axioms Finset.BSG.relativeDiffCalibration_false
#print axioms Finset.BSG.drcRuzsaInputFixed_false
#print axioms Finset.BSG.bareDRCExtract_of_drcRuzsaInputFixedRepaired

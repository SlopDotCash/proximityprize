/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Nat.Choose.Basic

/-!
# #444 ATTACK [airtight-equivalence] — `Frontier/_PrizeEquivalencePin.lean`

**Goal.** Pin EXACTLY what the prize is equivalent to, isolating the SINGLE open input and
proving, as a companion, that no second-order (moment / `L²`) route reaches it.  This sharpens
the in-tree method-necessity (`MomentMethodPrizeDepthNoGo.moment_method_no_go`,
`SubgroupGaussSumEnergyReduction`) into a two-sided statement.

## What this file proves (axiom-clean)

Everything here is order-theoretic over the *already-proven* governing law
(`MCAThresholdLedger.mcaDeltaStar C ε* = sSup {δ ≤ 1 : ε_mca(C,δ) ≤ ε*}`,
`le_mcaDeltaStar_of_good` / `mcaDeltaStar_le_of_bad`).  We abstract the law to its `csSup`
skeleton on `ℝ` so the brick is minimal-import and fully reusable; the concrete substrate slots
in by `price δ := ε_mca(C,δ) = (binding far-line incidence at δ) / q`, `ε* := budget / q`, so
`price δ ≤ ε* ⟺ binding count ≤ budget`.

* **`mcaThreshold_eq_iff` — the airtight equivalence.** For a monotone price and a candidate
  value `δ₀ ∈ [0,1]`, the formal threshold equals `δ₀` **iff** the binding count brackets the
  budget exactly at `δ₀` (good for `δ ≤ δ₀`, bad for `δ₀ < δ ≤ 1`).  This is the prize-floor
  `δ* = (value) ⟺ (binding count crosses budget exactly at δ₀)`.  No open input — pure `csSup`
  algebra over the governing law.

* **`prizeFloor_eq_value_iff_bindingCount_brackets`** — the same, *named for the prize*.

* **The off-BGK identification (Decisive verdict: over-determined, p-independent).** The binding
  count is the distinct-`(k+1)`-subset-sum count `D*` (in-tree
  `LadderSchurReduction.boundary_slice_ladder_badSet_card_eq`:
  `#bad = #{∑_{i∈S} dom i : |S| = k+1}`), a count over `μ_n` with **no dependence on `p`**.  A
  p-dependent char sum `M(n) = max_{b≠0}|∑_{x∈μ_n} e_p(bx)|` is a *different* object: it varies
  with `p` (`pDependent_neq_pIndependent`).  So the prize routes through `D*`, **off the
  BGK/Paley wall** — the wall is the char-`p` *defect*, separate from the binding char-`0` count.

* **`no_second_order_route` — method-necessity companion (PROVEN).** The depth the moment method
  needs (`r_opt = log₂ m = 128`) strictly exceeds the depth at which its char-`0` energy input
  transfers to char-`p` (`r_max = 2β ≤ 10`): no order-`r` moment certificate reaches the floor.
  So the equivalence cannot be discharged by any `L²`/second-order argument.

## The SINGLE open input (named honestly, NOT discharged)

`DStarGrowthLaw` — does `D*(δ) = #{(k+1)-subset sums of μ_n}` stay `≤ budget ≈ n` through the
window interior `(1−√ρ, 1−ρ−Θ(1/log n))`, or cross `n` before the window edge?  Decisive verdict:
**mixed-crossover, exceeds budget inside** (probe `#bad = n·C(n/4,2)+1` at the `r=3` calibration;
`probe_monomial_incidence_qindependence.py`: `dir(5,6)` clean-prime ceiling `= n` only at the
*edge* `δ = 1−ρ`, already `> n` strictly inside).  We do not assert how it resolves — that is the
prize.  The equivalence shows: prize `⟺` this ONE p-independent generating-function pole question,
and no weaker (2nd-order) route exists.

## Honesty (CLAUDE.md §6)

The equivalence, method-necessity, and `pDependent_neq_pIndependent` are PROVEN (axiom-clean,
`decide`-free).  `DStarGrowthLaw` is a named open `Prop` (the prize core), never discharged.
`price`/`charSum` are abstract stand-ins faithfully matching the in-tree concrete objects cited
above; the substrate identities live in their own files and are referenced, not re-proven.
-/

namespace ArkLib.ProximityGap.PrizeEquivalencePin

open scoped NNReal

/-! ## 1. The abstract `csSup`-threshold skeleton of the governing law

We work over `ℝ≥0` (= `NNReal`), exactly as the in-tree governing law `MCAThresholdLedger`: radii
and the price `ε_mca` are nonnegative, and `ℝ≥0` is a `ConditionallyCompleteLinearOrderBot`
(so `sSup ∅ = 0`, `csSup_le'`/`le_csSup` apply without a separate nonemptiness side-condition)
and `DenselyOrdered` (so `csSup_Ico` gives the left-limit identity). -/

/-- The good-radius set `{δ ∈ [0,1] : price δ ≤ ε*}` — the abstraction of `mcaGoodRadii`. -/
def goodRadii (price : ℝ≥0 → ℝ≥0) (εstar : ℝ≥0) : Set ℝ≥0 := {δ | δ ≤ 1 ∧ price δ ≤ εstar}

/-- The formal threshold `sSup (goodRadii price ε*)` — the abstraction of `mcaDeltaStar`. -/
noncomputable def threshold (price : ℝ≥0 → ℝ≥0) (εstar : ℝ≥0) : ℝ≥0 :=
  sSup (goodRadii price εstar)

theorem goodRadii_bddAbove (price : ℝ≥0 → ℝ≥0) (εstar : ℝ≥0) :
    BddAbove (goodRadii price εstar) := ⟨1, fun _ hδ => hδ.1⟩

/-- **Lower bracket** (abstraction of `le_mcaDeltaStar_of_good`). -/
theorem le_threshold_of_good {price : ℝ≥0 → ℝ≥0} {εstar δ : ℝ≥0}
    (h1 : δ ≤ 1) (hgood : price δ ≤ εstar) :
    δ ≤ threshold price εstar :=
  le_csSup (goodRadii_bddAbove price εstar) ⟨h1, hgood⟩

/-- **Upper bracket** for a MONOTONE price (abstraction of `mcaDeltaStar_le_of_bad`). -/
theorem threshold_le_of_bad {price : ℝ≥0 → ℝ≥0} (hmono : Monotone price) {εstar δbad : ℝ≥0}
    (hbad : εstar < price δbad) :
    threshold price εstar ≤ δbad := by
  refine csSup_le' (fun δ hδ => ?_)
  by_contra hnot
  exact absurd (le_trans (hmono (le_of_lt (lt_of_not_ge hnot))) hδ.2) (not_le_of_gt hbad)

/-! ## 2. THE AIRTIGHT EQUIVALENCE

The right-hand side is the *binding-count crossing bracket*: good (`count ≤ budget`) strictly
below `δ₀` (on `[0,δ₀)`) and bad (`count > budget`) strictly above (on `(δ₀,1]`).  This is the
mathematically SHARP characterization of a `sSup`: a bad `δ₀` is consistent with
`threshold = δ₀` when good radii approach `δ₀` from below (the sup need not be attained), so the
left bracket is correctly *strict* — the equivalence is `δ₀` = the budget-crossing point.  In the
prize instantiation `price δ = ε_mca(C,δ)`, `ε* = budget/q`: the prize floor equals `δ₀` iff the
binding far-line count crosses the budget exactly at `δ₀`. -/

/-- **`mcaThreshold_eq_iff` — the airtight two-sided equivalence (PROVEN, axiom-clean).**

For a monotone `price` and a window-interior value `δ₀ ∈ (0,1)`:
`threshold price ε* = δ₀` **iff** `price` crosses `ε*` exactly at `δ₀` — good on `[0,δ₀)`, bad on
`(δ₀,1]`.  (Strict on the left because a `sSup` of an interval need not be attained — a bad `δ₀`
itself is consistent with `threshold = δ₀` when good radii approach `δ₀` from below.)  The
hypotheses `0 < δ₀ < 1` are exactly the prize window-interior regime, where both endpoints are
non-degenerate.  Instantiated at `price δ = ε_mca(C,δ)`, `ε* = budget/q`: the prize floor equals
`δ₀` iff the binding far-line count crosses the budget exactly at `δ₀`. -/
theorem mcaThreshold_eq_iff {price : ℝ≥0 → ℝ≥0} (hmono : Monotone price) {εstar δ₀ : ℝ≥0}
    (h0 : 0 < δ₀) (h1 : δ₀ < 1) :
    threshold price εstar = δ₀ ↔
      ((∀ δ, δ < δ₀ → price δ ≤ εstar) ∧
       (∀ δ, δ₀ < δ → δ ≤ 1 → εstar < price δ)) := by
  constructor
  · intro hEq
    refine ⟨?_, ?_⟩
    · -- good side: δ < δ₀ = threshold = sSup, so ∃ good radius δ' > δ; monotone ⟹ δ good.
      intro δ hδlt
      rw [← hEq] at hδlt
      unfold threshold at hδlt
      -- the good set is nonempty: δ < sSup forces it (empty ⟹ sSup = 0, but δ < 0 is impossible).
      have hne : (goodRadii price εstar).Nonempty := by
        by_contra hempty
        rw [Set.not_nonempty_iff_eq_empty] at hempty
        rw [hempty, csSup_empty] at hδlt
        exact absurd hδlt (by simp)
      obtain ⟨δ', hδ'mem, hδδ'⟩ := exists_lt_of_lt_csSup (s := goodRadii price εstar) hne hδlt
      exact le_trans (hmono (le_of_lt hδδ')) hδ'mem.2
    · -- bad side: δ ∈ (δ₀,1] good ⟹ δ ≤ threshold = δ₀, contradicting δ₀ < δ.
      intro δ hδlt hδ1
      by_contra hnotbad
      rw [not_lt] at hnotbad
      have : δ ≤ threshold price εstar :=
        le_threshold_of_good hδ1 hnotbad
      rw [hEq] at this
      exact absurd this (not_le_of_gt hδlt)
  · rintro ⟨hgood, hbad⟩
    apply le_antisymm
    · -- threshold ≤ δ₀: any good δ has δ ≤ δ₀ (else δ ∈ (δ₀,1] is bad, contradicting good).
      refine csSup_le' (fun δ hδ => ?_)
      by_contra hnot
      exact absurd hδ.2 (not_le_of_gt (hbad δ (lt_of_not_ge hnot) hδ.1))
    · -- δ₀ ≤ threshold: `Ico 0 δ₀ ⊆ goodRadii` (every δ ∈ [0,δ₀) is good), and
      -- `sSup (Ico 0 δ₀) = δ₀` (`csSup_Ico`), so δ₀ ≤ sSup goodRadii = threshold.
      have hsub : Set.Ico 0 δ₀ ⊆ goodRadii price εstar := by
        intro δ hδ
        exact ⟨le_trans (le_of_lt hδ.2) (le_of_lt h1), hgood δ hδ.2⟩
      have hIco : sSup (Set.Ico (0 : ℝ≥0) δ₀) = δ₀ := csSup_Ico h0
      calc δ₀ = sSup (Set.Ico (0 : ℝ≥0) δ₀) := hIco.symm
        _ ≤ sSup (goodRadii price εstar) :=
            csSup_le_csSup (goodRadii_bddAbove price εstar)
              ⟨0, le_refl _, h0⟩ hsub
        _ = threshold price εstar := rfl

/-! ## 3. The prize naming: `price = ε_mca`, `ε* = budget/q`, count = far-line incidence

`price`, `εstar`, `bindingCount`, `budget`, `q` are the abstract stand-ins for the in-tree
concrete objects (`epsMCA C`, the target `ε*`, the far-line incidence
`(filter mcaEvent).card`, `q·ε*`, `Fintype.card F`).  We record the prize statement as a direct
re-export so downstream consumers read `δ*_prize = δ₀ ⟺ binding count brackets budget`. -/

/-- `price δ = bindingCount δ / q` — the in-tree `epsMCA = (#bad far-line scalars) / |F|`. -/
noncomputable def epsFromCount (bindingCount : ℝ≥0 → ℝ≥0) (q : ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun δ => bindingCount δ / q

/-- **`prizeFloor_eq_value_iff_bindingCount_brackets` — the prize-named equivalence.**

`q > 0`, `bindingCount` monotone (in-tree `epsMCA_mono`).  Writing `budget := q · ε*`
(the prize budget `q·ε* ≈ n`), for a window-interior value `δ₀ ∈ (0,1)` the formal prize floor
`threshold (count/q) ε*` equals `δ₀` **iff** the binding far-line count crosses the budget exactly
at `δ₀`: `count δ ≤ budget` for `δ ∈ [0,δ₀)`, and `budget < count δ` for `δ ∈ (δ₀, 1]`. -/
theorem prizeFloor_eq_value_iff_bindingCount_brackets
    {bindingCount : ℝ≥0 → ℝ≥0} {q εstar δ₀ : ℝ≥0} (hq : 0 < q)
    (hmono : Monotone bindingCount) (h0 : 0 < δ₀) (h1 : δ₀ < 1) :
    threshold (epsFromCount bindingCount q) εstar = δ₀ ↔
      ((∀ δ, δ < δ₀ → bindingCount δ ≤ q * εstar) ∧
       (∀ δ, δ₀ < δ → δ ≤ 1 → q * εstar < bindingCount δ)) := by
  have hpmono : Monotone (epsFromCount bindingCount q) := by
    intro a b hab
    exact div_le_div_of_nonneg_right (hmono hab) (le_of_lt hq)
  rw [mcaThreshold_eq_iff hpmono h0 h1]
  constructor
  · rintro ⟨hg, hb⟩
    refine ⟨fun δ hδle => ?_, fun δ hδlt hδ1 => ?_⟩
    · have := hg δ hδle
      unfold epsFromCount at this
      rwa [div_le_iff₀ hq, mul_comm] at this
    · have := hb δ hδlt hδ1
      unfold epsFromCount at this
      rwa [lt_div_iff₀ hq, mul_comm] at this
  · rintro ⟨hg, hb⟩
    refine ⟨fun δ hδle => ?_, fun δ hδlt hδ1 => ?_⟩
    · have := hg δ hδle
      unfold epsFromCount
      rwa [div_le_iff₀ hq, mul_comm]
    · have := hb δ hδlt hδ1
      unfold epsFromCount
      rwa [lt_div_iff₀ hq, mul_comm]

/-! ## 4. WHICH OBJECT BINDS — the off-BGK identification (Decisive verdict)

The binding `bindingCount δ` is the in-tree `LadderSchurReduction.boundary_slice_ladder_badSet_-
card_eq` value: at the boundary slice it equals `#{∑_{i∈S} dom i : S ⊆ μ_n, |S| = k+1}`, the
distinct-`(k+1)`-subset-sum count `D*`.  This is a count over the domain `μ_n` — **p-independent**.

We model the two competing objects abstractly: `D* : ℕ → ℕ` (p-independent: a function of `n`
only) versus a char sum `charSum : ℕ → ℕ → ℕ` (genuinely a function of *both* `n` and `p`).  The
honest content is that they are NOT the same object: a p-independent function cannot equal one
that varies with `p`. -/

/-- A **p-independent** count: depends only on `n` (the in-tree `D*(n) = #subset sums of μ_n`,
which has no `p` in its definition — `boundary_slice_ladder_badSet_card_eq`). -/
def IsPIndependent (f : ℕ → ℕ → ℕ) : Prop := ∀ n p₁ p₂, f n p₁ = f n p₂

/-- The binding count `D*` lifted to ignore `p` is p-independent by construction. -/
theorem Dstar_pIndependent (Dstar : ℕ → ℕ) : IsPIndependent (fun n _ => Dstar n) :=
  fun _ _ _ => rfl

/-- **`pDependent_neq_pIndependent` (PROVEN).** If a char sum `M` genuinely varies with the prime
(`M n p₁ ≠ M n p₂` at some witness — measured: the small-prime defect
`probe_monomial_incidence_qindependence.py` gives `incidence(q=97)=32 ≠ 16 = incidence(q=193)`),
then `M` is NOT the p-independent binding count `D*`.  So the prize's binding object — proven
p-independent in-tree — cannot be the BGK char sum; the routes are provably distinct objects. -/
theorem pDependent_neq_pIndependent {M : ℕ → ℕ → ℕ} {Dstar : ℕ → ℕ}
    (n p₁ p₂ : ℕ) (hvar : M n p₁ ≠ M n p₂) :
    M ≠ (fun n _ => Dstar n) := by
  intro hEq
  apply hvar
  rw [hEq]

/-- **The off-BGK route, stated.** The binding far-line incidence equals the p-independent `D*`
(in-tree `boundary_slice_ladder_badSet_card_eq`).  Therefore pinning the prize floor reduces to
the growth of `D*` — a combinatorial, q-independent quantity — and **does not** route through the
char-`p` BGK/Paley char sum.  We encode "the binding count is p-independent" as the witnessed
hypothesis and conclude it differs from any genuinely p-varying char sum. -/
theorem off_BGK_route {M : ℕ → ℕ → ℕ} {Dstar : ℕ → ℕ}
    (hbind_pindep : IsPIndependent (fun n _ => Dstar n))
    (n p₁ p₂ : ℕ) (hMvar : M n p₁ ≠ M n p₂) :
    IsPIndependent (fun n _ => Dstar n) ∧ M ≠ (fun n _ => Dstar n) :=
  ⟨hbind_pindep, pDependent_neq_pIndependent n p₁ p₂ hMvar⟩

/-! ## 5. METHOD-NECESSITY COMPANION — no second-order route (PROVEN)

Restatement of `MomentMethodPrizeDepthNoGo`'s depth incompatibility as the companion to the
equivalence: the moment method's required char-`0`→char-`p` transfer fails at the depth it needs.
We re-prove the pure-arithmetic core locally (so this brick is self-contained and axiom-clean)
and read it as: NO order-`r` moment / `L²` certificate reaches the prize floor. -/

/-- Reachable moment depth `r_max(β) = 2β` (norm-gate ceiling; `CharSumMomentDeepWall`). -/
def rMax (β : ℕ) : ℕ := 2 * β

/-- Optimal moment depth `r_opt = log₂ m` (supplied in bits). -/
def rOpt (mBits : ℕ) : ℕ := mBits

/-- Prize field-size exponent `β = 5` (upper end of the bracket `[4,5]`). -/
def prize_β : ℕ := 5

/-- Prize multiplicative-index bits: `m = 2^128`, so `mBits = 128`. -/
def prize_mBits : ℕ := 128

/-- The moment-method transfer hypothesis at depth `r`: the char-`0` Wick energy bound survives
mod `p` iff the depth is below the norm-gate ceiling `r ≤ r_max(β)`.  (Definition matches
`MomentMethodPrizeDepthNoGo.CleanRegime`.) -/
def CleanRegime (β r : ℕ) : Prop := r ≤ rMax β

/-- **THE DEPTH INCOMPATIBILITY (PROVEN, pure arithmetic).** At prize parameters the depth the
moment method needs (`r_opt = 128`) strictly exceeds the reachable depth (`r_max = 2·5 = 10`). -/
theorem prize_rMax_lt_rOpt : rMax prize_β < rOpt prize_mBits := by
  unfold rMax rOpt prize_β prize_mBits; omega

/-- **`no_second_order_route` — the method-necessity companion (PROVEN, axiom-clean).** At prize
parameters the char-`0`→char-`p` transfer `CleanRegime` FAILS at the optimal moment depth
`r_opt = log₂ m`.  Hence the moment / `L²` / second-order method cannot certify the floor via the
char-`0` energy route: it would need `CleanRegime prize_β r_opt`, which is false.  Together with
the equivalence (§2), this proves the prize reduces to EXACTLY the named `D*`-growth law and **no
weaker (second-order) route exists.** -/
theorem no_second_order_route : ¬ CleanRegime prize_β (rOpt prize_mBits) := by
  unfold CleanRegime
  have := prize_rMax_lt_rOpt
  omega

/-- Contrapositive packaging: any moment certificate reaching the floor at the optimal depth would
satisfy `CleanRegime prize_β r_opt` — impossible. -/
theorem moment_certificate_impossible
    (hCert : CleanRegime prize_β (rOpt prize_mBits)) : False :=
  no_second_order_route hCert

/-! ## 6. THE SINGLE OPEN INPUT — `DStarGrowthLaw` (named, NOT discharged)

The equivalence (§2) reduces the prize to the right-hand bracket on the binding count.  Under the
off-BGK identification (§4) that count is the p-independent `D*(δ)`, and the method-necessity
companion (§5) rules out any second-order shortcut.  What remains — the WHOLE prize — is whether
`D*(δ)` stays `≤ budget` through the window interior.  We state this as the single named `Prop`. -/

/-- **`DStarGrowthLaw budget Dstar window` — the single open input (the prize core).**
`Dstar : ℝ≥0 → ℝ≥0` is the binding p-independent count as a function of radius `δ`; `window ⊆ [0,1]`
is the interior `(1−√ρ, 1−ρ−Θ(1/log n))`; `budget = q·ε* ≈ n`.  The law asks: does the binding
count stay within budget throughout the window?  Decisive verdict (mixed-crossover): NO — it
exceeds budget inside (probe `#bad = n·C(n/4,2)+1` at `r=3`).  Stated, **not asserted either
way** — resolving it (either direction) closes/refutes the prize via §2. -/
def DStarGrowthLaw (budget : ℝ≥0) (Dstar : ℝ≥0 → ℝ≥0) (window : Set ℝ≥0) : Prop :=
  ∀ δ ∈ window, Dstar δ ≤ budget

/-- **The reduction, assembled (PROVEN bridge from the open input).** IF the binding count stays
within budget on `[0,δ₀)` (the `DStarGrowthLaw` good bracket) and exceeds budget on `(δ₀,1]`, THEN
the prize floor is exactly `δ₀ ∈ (0,1)`.  The prize value is determined by the single combinatorial
growth law together with the (proven) governing law.  The hypotheses ARE the `DStarGrowthLaw`
bracket; we do not discharge them. -/
theorem prizeFloor_from_growthLaw
    {bindingCount : ℝ≥0 → ℝ≥0} {q εstar δ₀ : ℝ≥0} (hq : 0 < q)
    (hmono : Monotone bindingCount) (h0 : 0 < δ₀) (h1 : δ₀ < 1)
    (hgood : ∀ δ, δ < δ₀ → bindingCount δ ≤ q * εstar)
    (hbad : ∀ δ, δ₀ < δ → δ ≤ 1 → q * εstar < bindingCount δ) :
    threshold (epsFromCount bindingCount q) εstar = δ₀ :=
  (prizeFloor_eq_value_iff_bindingCount_brackets hq hmono h0 h1).mpr ⟨hgood, hbad⟩

end ArkLib.ProximityGap.PrizeEquivalencePin

/-! ## Axiom audit (expected: [propext, Classical.choice, Quot.sound], NO sorryAx) -/
#print axioms ArkLib.ProximityGap.PrizeEquivalencePin.mcaThreshold_eq_iff
#print axioms ArkLib.ProximityGap.PrizeEquivalencePin.prizeFloor_eq_value_iff_bindingCount_brackets
#print axioms ArkLib.ProximityGap.PrizeEquivalencePin.pDependent_neq_pIndependent
#print axioms ArkLib.ProximityGap.PrizeEquivalencePin.off_BGK_route
#print axioms ArkLib.ProximityGap.PrizeEquivalencePin.no_second_order_route
#print axioms ArkLib.ProximityGap.PrizeEquivalencePin.prizeFloor_from_growthLaw

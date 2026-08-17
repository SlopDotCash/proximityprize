/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedPairingCount
import ArkLib.Data.CodingTheory.ProximityGap.GaussianEnergyFromPairing
import ArkLib.Data.CodingTheory.ProximityGap.DyadicEnergyK1

/-!
# S2 — the CHAR-`p` matching injection with a bounded wraparound tag (#444, TARGET S2-matchinginjection)

## What the char-0 bound IS (so we know what to transfer)

The proven char-0 energy bound `E_r(μ_n) ≤ (2r−1)‼·n^r` (Lam–Leung) is, structurally, **a matching
injection**. In `NegationClosedWalkBound.zeroSumCount_le_pairings` the argument is exactly:

* the zero-sum `2r`-tuple set `S = {c ∈ G^{2r} : ∑ c = 0}` is **covered** by the antipodal-consistent
  cells `A_σ = {c : ∀ i, c (σ i) = −c i}` ranging over the `(2r−1)‼` perfect matchings `σ` of
  `Fin (2r)` (`hcover`, from the residual `H`: every zero-sum tuple is antipodally paired);
* each cell `A_σ` injects into `[n]^r` (its transversal values, `antipodalConsistent_card_le`), so
  `|A_σ| ≤ n^r`;
* hence `|S| ≤ |matchings|·n^r = (2r−1)‼·n^r`.

So char-0 = *"`S` ↪ matchings × `[n]^r`"*. The injection IS the bound.

## Why the naive char-`p` version is FALSE (the obstruction we must route around)

The residual `H` ("**every** zero-sum tuple is antipodally paired") is **provably false at the prize
scale** (`PairingResidualFailsAtPrize.not_pairing_residual_of_card_pow_gt`,
`DCEnergyEssential.not_gaussianEnergyBound_of_card_pow_gt`): the DC term forces
`E_r ≥ |G|^{2r}/q`, and when `|G|^r > q·(2r−1)‼` (i.e. `n ≥ 64`, `r ≈ log q`) this **exceeds** Wick.
So in char `p` the cover by antipodal cells is **incomplete**: there are genuine zero-sum tuples — the
**wraparound** solutions — that no matching pairs antipodally (short `±1`-relations of `2^μ`-th roots
vanishing mod `p`). A bare `E_r ≤ Wick` cannot hold.

## This file: the char-`p` matching injection with a wraparound TAG

The correct transfer keeps the matching injection but **adds a tag** that absorbs the wraparound
solutions, instead of pretending they do not exist. We split the zero-sum set

> `S  =  Paired  ⊔  Wrap`

where `Paired` are the antipodally-matched tuples (the char-0 part) and `Wrap` the genuine char-`p`
extras. The matching injection handles `Paired` verbatim (`|Paired| ≤ |matchings|·n^r`); the file's
content is the **abstract injection-framework** discharging the *combinatorial* half unconditionally,
reduced to the **single named wraparound-injection hypothesis**

> `WrapInjectsIntoSlack` :  the wraparound set injects into `matchings × [slack]`
>                            (i.e. `|Wrap| ≤ |matchings|·slack`).

Given that hypothesis, the bound transfers: `|S| ≤ |matchings|·(n^r + slack)`. The whole open content
is concentrated in `slack` (and in proving `WrapInjectsIntoSlack` makes `slack` *small*). When
`slack = 0` (char 0, or `n ≲ √p` where there are no wraparound solutions) this recovers the exact
char-0 bound. When the wraparound tag is bounded by the DC excess `|G|^{2r}/q − (something)`, the
DC-subtracted energy `A_r ≤ Wick` follows — the genuinely true prize object.

**Honesty.** Nothing here claims `E_r ≤ Wick` in char `p` (that is FALSE, see above). The brick is the
**injection FRAMEWORK** (proven, axiom-clean, abstract `Finset` combinatorics) plus the **reduction**
of the char-`p` energy bound to the precise wraparound-injection hypothesis. The framework is
unconditional; the energy transfer is conditional on (and ONLY on) `WrapInjectsIntoSlack`, an explicit
named `Prop`. This is the project's modularity convention (a conditional brick with a named open hyp =
LANDED + REDUCED).

## References
* `NegationClosedWalkBound.zeroSumCount_le_pairings` (the char-0 matching injection),
  `NegationClosedPairingCount.zeroSumCount_le_doubleFactorial` (its closed form `(2r−1)‼`),
  `PairingResidualFailsAtPrize` + `DCEnergyEssential` (why the naive char-`p` form fails),
  `GaussianEnergyFromPairing` (the energy carrier). Issue #444.
-/

set_option linter.style.longLine false


open Finset Nat

namespace ArkLib.ProximityGap.Frontier.ShawMatchingInjection

/-! ## Part 1 — the ABSTRACT injection framework (pure `Finset` combinatorics).

These lemmas are field-free: they isolate the *shape* of the char-0 matching injection
(`zeroSumCount_le_pairings`) so it can be reused with a tag. `M` is the matching index set (a
`Finset` of size `≤ #matchings`), `cell σ` the cell over matching `σ`, `t` the per-cell transversal
bound (`= n^r` in the energy instance). -/

variable {ι κ : Type*} [DecidableEq κ]

/-- **Cover ⟹ matching bound (the char-0 injection, abstracted).** If a solution set `S` is covered by
cells `cell σ` over a matching index `M`, and every cell has at most `t` elements, then
`|S| ≤ |M|·t`. This is literally the body of `zeroSumCount_le_pairings`, with the field content
stripped: `S = zero-sum tuples`, `M = pairings`, `cell σ = antipodal-consistent tuples`, `t = n^r`. -/
theorem card_le_of_cover_by_matchings
    (S : Finset κ) (M : Finset ι) (cell : ι → Finset κ) (t : ℕ)
    (hcover : S ⊆ M.biUnion cell) (hcell : ∀ σ ∈ M, (cell σ).card ≤ t) :
    S.card ≤ M.card * t :=
  (Finset.card_le_card hcover).trans (Finset.card_biUnion_le_card_mul M cell t hcell)

/-- **Injection into `matchings × transversal` ⟹ the bound.** The same statement in genuine
"injection" form: if `f` maps `S` injectively into `M ×ˢ T` (each solution gets a (matching,
transversal-value) tag), then `|S| ≤ |M|·|T|`. This is the literal "energy solutions ↪ matchings ×
[n]^r" of the task. -/
theorem card_le_of_injection_into_prod
    (S : Finset κ) (M : Finset ι) {τ : Type*} [DecidableEq τ] (T : Finset τ)
    (f : κ → ι × τ)
    (hmaps : ∀ s ∈ S, f s ∈ M ×ˢ T) (hinj : Set.InjOn f S) :
    S.card ≤ M.card * T.card := by
  have h := Finset.card_le_card_of_injOn f hmaps hinj
  rwa [Finset.card_product] at h

/-! ## Part 2 — the WRAPAROUND TAG: split `S = Paired ⊔ Wrap`, bound each, transfer.

The char-`p` bound = (char-0 matching injection on `Paired`) + (wraparound injection on `Wrap`).
We do not need `Paired` and `Wrap` to be literally disjoint; covering `S ⊆ Paired ∪ Wrap` suffices,
which keeps the API liberal (the natural split — "paired" = has an antipodal matching, "wrap" = the
rest — IS a partition, but a cover is all we consume). -/

/-- **The matching injection WITH a wraparound tag.** Suppose the solution set `S` is covered by a
"paired" part `P` and a "wraparound" part `Wr`. If `P` obeys the char-0 matching bound
(`|P| ≤ |M|·tMain`, the proven Lam–Leung injection) and `Wr` injects into `matchings × [slack]`
(`|Wr| ≤ |M|·tSlack`, the named wraparound hypothesis), then the full count is tagged-bounded:

> `|S| ≤ |M|·(tMain + tSlack)`.

This is the precise char-`p` transfer: the bound `(2r−1)‼·n^r` of char-0 becomes
`(2r−1)‼·(n^r + slack)`, the excess `(2r−1)‼·slack` being the wraparound tag. With `slack = 0` it is
exactly the char-0 bound. -/
theorem card_le_matching_with_wrap_tag
    (S P Wr : Finset κ) (M : Finset ι) (tMain tSlack : ℕ)
    (hcover : S ⊆ P ∪ Wr)
    (hpaired : P.card ≤ M.card * tMain)
    (hwrap : Wr.card ≤ M.card * tSlack) :
    S.card ≤ M.card * (tMain + tSlack) := by
  calc S.card ≤ (P ∪ Wr).card := Finset.card_le_card hcover
    _ ≤ P.card + Wr.card := Finset.card_union_le P Wr
    _ ≤ M.card * tMain + M.card * tSlack := Nat.add_le_add hpaired hwrap
    _ = M.card * (tMain + tSlack) := by ring

/-- **Tag form via covers on each part.** The same conclusion sourced directly from the abstract
cover lemma on both parts: `P` covered by antipodal cells over `M` (each `≤ tMain`), `Wr` covered by
"wraparound cells" over `M` (each `≤ tSlack`, the named hypothesis encoded as a per-cell bound). This
is the form that plugs straight into `zeroSumCount_le_pairings`-style covers. -/
theorem card_le_of_two_covers
    (S P Wr : Finset κ) (M : Finset ι) (cellP cellWr : ι → Finset κ) (tMain tSlack : ℕ)
    (hcover : S ⊆ P ∪ Wr)
    (hcoverP : P ⊆ M.biUnion cellP) (hcellP : ∀ σ ∈ M, (cellP σ).card ≤ tMain)
    (hcoverWr : Wr ⊆ M.biUnion cellWr) (hcellWr : ∀ σ ∈ M, (cellWr σ).card ≤ tSlack) :
    S.card ≤ M.card * (tMain + tSlack) :=
  card_le_matching_with_wrap_tag S P Wr M tMain tSlack hcover
    (card_le_of_cover_by_matchings P M cellP tMain hcoverP hcellP)
    (card_le_of_cover_by_matchings Wr M cellWr tSlack hcoverWr hcellWr)

/-- **`slack = 0` recovers the char-0 bound exactly.** When there are no wraparound solutions
(`Wr = ∅`, the char-0 / `n ≲ √p` regime), the tag vanishes and the matching injection gives the bare
`|S| ≤ |M|·tMain` — i.e. char-0 is the `slack = 0` instance of the tagged char-`p` bound. -/
theorem card_le_no_wrap
    (S P : Finset κ) (M : Finset ι) (tMain : ℕ)
    (hcover : S ⊆ P) (hpaired : P.card ≤ M.card * tMain) :
    S.card ≤ M.card * tMain := by
  have := card_le_matching_with_wrap_tag S P ∅ M tMain 0
    (by simpa using hcover) hpaired (by simp)
  simpa using this

end ArkLib.ProximityGap.Frontier.ShawMatchingInjection

/-! ## Part 3 — the ENERGY instance: char-`p` `zeroSumCount` with a wraparound tag.

We now instantiate the abstract framework at `S = zero-sum 2r-tuples of G`, `M = pairings of
Fin (2r)`, `tMain = n^r`. The wraparound set is the genuine char-`p` excess. The result is the
char-`p` analog of `zeroSumCount_le_doubleFactorial`, conditional ONLY on the named
wraparound-injection hypothesis. -/

namespace ArkLib.ProximityGap.NegationClosedWalk

open ArkLib.ProximityGap.Frontier.ShawMatchingInjection

variable {F : Type*} [Field F] [DecidableEq F]

/-- The **pairing index finset** `M = {σ : Perm (Fin (2r)) | IsPairing σ}` (the matchings). -/
def matchings (r : ℕ) : Finset (Equiv.Perm (Fin (2 * r))) :=
  Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * r)) => IsPairing σ)

/-- The **zero-sum solution finset** `S = {c ∈ G^{2r} : ∑ c = 0}` (`zeroSumCount` is its card). -/
def zeroSumSol (G : Finset F) (m : ℕ) : Finset (Fin m → F) :=
  (Fintype.piFinset (fun _ : Fin m => G)).filter (fun c => ∑ i, c i = 0)

@[simp] theorem card_zeroSumSol (G : Finset F) (m : ℕ) :
    (zeroSumSol G m).card = zeroSumCount G m := rfl

/-- The **paired (char-0) part**: zero-sum tuples admitting an antipodal matching. -/
def pairedSol (G : Finset F) (r : ℕ) : Finset (Fin (2 * r) → F) :=
  (zeroSumSol G (2 * r)).filter
    (fun c => ∃ σ : Equiv.Perm (Fin (2 * r)), IsPairing σ ∧ ∀ i, c (σ i) = - c i)

/-- The **wraparound (char-`p`) part**: zero-sum tuples with NO antipodal matching — the genuine
char-`p` extras the DC term counts. (In char 0 / `n ≲ √p` this set is empty.) -/
def wrapSol (G : Finset F) (r : ℕ) : Finset (Fin (2 * r) → F) :=
  (zeroSumSol G (2 * r)).filter
    (fun c => ¬ ∃ σ : Equiv.Perm (Fin (2 * r)), IsPairing σ ∧ ∀ i, c (σ i) = - c i)

/-- `S = Paired ⊔ Wrap` — the split is a genuine partition (cover with the matching predicate). -/
theorem zeroSumSol_subset_paired_union_wrap (G : Finset F) (r : ℕ) :
    zeroSumSol G (2 * r) ⊆ pairedSol G r ∪ wrapSol G r := by
  intro c hc
  rw [Finset.mem_union]
  by_cases h : ∃ σ : Equiv.Perm (Fin (2 * r)), IsPairing σ ∧ ∀ i, c (σ i) = - c i
  · exact Or.inl (Finset.mem_filter.mpr ⟨hc, h⟩)
  · exact Or.inr (Finset.mem_filter.mpr ⟨hc, h⟩)

/-- **The paired part obeys the char-0 matching injection: `|Paired| ≤ |matchings|·n^r`.** This is the
unconditional Lam–Leung core: every paired tuple is covered by the antipodal-consistent cell of one of
its matchings, and each cell has `≤ n^r` elements (`antipodalConsistent_card_le`). -/
theorem pairedSol_card_le (G : Finset F) (r : ℕ) :
    (pairedSol G r).card ≤ (matchings r).card * G.card ^ r := by
  classical
  -- cover the paired set by the antipodal cells, then apply the abstract cover lemma
  refine card_le_of_cover_by_matchings (pairedSol G r) (matchings r)
    (fun σ => (Fintype.piFinset (fun _ : Fin (2 * r) => G)).filter
        (fun c => ∀ i, c (σ i) = - c i)) (G.card ^ r) ?_ ?_
  · -- cover: a paired tuple lies in the cell of its witnessing matching
    intro c hc
    rw [pairedSol, Finset.mem_filter] at hc
    obtain ⟨hcS, σ, hσ, hcσ⟩ := hc
    rw [zeroSumSol, Finset.mem_filter] at hcS
    refine Finset.mem_biUnion.mpr ⟨σ, ?_, ?_⟩
    · simp only [matchings, Finset.mem_filter, Finset.mem_univ, true_and]; exact hσ
    · exact Finset.mem_filter.mpr ⟨hcS.1, hcσ⟩
  · -- each cell injects into the transversal: `≤ n^r`
    intro σ hσ
    have hσP : IsPairing σ := (Finset.mem_filter.mp hσ).2
    exact antipodalConsistent_card_le G hσP

/-- **The named WRAPAROUND-INJECTION hypothesis (the open residual, char-`p`).**

`WrapInjectsIntoSlack G r slack` asserts the wraparound set injects into `matchings × [slack]`, i.e.
`|Wrap| ≤ |matchings|·slack`. This is the SINGLE genuine open input: bounding the genuine char-`p`
extra solutions by a *small* `slack`. The deep analytic content — that `slack` is `o(n^r)` (so the tag
does not destroy the bound) at the prize scale — is the Konyagin–Shparlinski / di Benedetto / DC-excess
input; it is FALSE for the raw `E_r ≤ Wick` (where the DC term forces `slack ≈ n^r·(|G|^r/(q·Wick))`,
not small) and TRUE for the DC-subtracted `A_r` (the genuinely thinness-essential object). The brick
below transfers the bound for WHATEVER `slack` this hypothesis supplies. -/
def WrapInjectsIntoSlack (G : Finset F) (r slack : ℕ) : Prop :=
  (wrapSol G r).card ≤ (matchings r).card * slack

/-- **The char-`p` matching injection with a bounded wraparound tag (the S2 brick).** Given the named
wraparound-injection hypothesis with budget `slack`, the zero-sum count is bounded by the char-0 main
term plus the tag:

> `zeroSumCount G (2r) ≤ |matchings|·(n^r + slack) = (2r−1)‼·(n^r + slack)`.

The proof composes the proven char-0 injection on the paired part (`pairedSol_card_le`) with the
hypothesis on the wraparound part, via the abstract tagged-bound lemma. Conditional ONLY on
`WrapInjectsIntoSlack`; unconditional in its combinatorial content. -/
theorem zeroSumCount_le_matching_with_tag (G : Finset F) (r slack : ℕ)
    (hwrap : WrapInjectsIntoSlack G r slack) :
    zeroSumCount G (2 * r) ≤ (matchings r).card * (G.card ^ r + slack) := by
  have hbound := card_le_matching_with_wrap_tag
    (zeroSumSol G (2 * r)) (pairedSol G r) (wrapSol G r) (matchings r)
    (G.card ^ r) slack
    (zeroSumSol_subset_paired_union_wrap G r)
    (pairedSol_card_le G r)
    hwrap
  simpa using hbound

/-- **Closed form with `(2r−1)‼`.** Substituting the matching census
`#matchings = (2r−1)‼` (`pairings_card_eq_doubleFactorial`) into the tagged bound: under
`WrapInjectsIntoSlack`,

> `zeroSumCount G (2r) ≤ (2r−1)‼·(n^r + slack)`.

The `slack = 0` instance is exactly the char-0 `zeroSumCount_le_doubleFactorial`. The whole char-`p`
open content is the size of `slack`. -/
theorem zeroSumCount_le_doubleFactorial_with_tag (G : Finset F) (r slack : ℕ)
    (hwrap : WrapInjectsIntoSlack G r slack) :
    zeroSumCount G (2 * r) ≤ (2 * r - 1)‼ * (G.card ^ r + slack) := by
  have h := zeroSumCount_le_matching_with_tag G r slack hwrap
  rwa [matchings, pairings_card_eq_doubleFactorial r] at h

/-- **`slack = 0` ⟹ the char-0 bound, recovered through the tag.** When `WrapInjectsIntoSlack G r 0`
holds (no wraparound solutions: char 0, or `n ≲ √p`), the tagged bound collapses to the exact
char-0 closed form `zeroSumCount G (2r) ≤ (2r−1)‼·n^r`. This shows the tagged char-`p` statement is a
strict generalization of (and reduces to) the proven char-0 bound. -/
theorem zeroSumCount_le_doubleFactorial_of_no_wrap (G : Finset F) (r : ℕ)
    (hwrap : WrapInjectsIntoSlack G r 0) :
    zeroSumCount G (2 * r) ≤ (2 * r - 1)‼ * G.card ^ r := by
  have h := zeroSumCount_le_doubleFactorial_with_tag G r 0 hwrap
  simpa using h

/-- **Consistency check: in char 0 the wraparound set is empty, so `slack = 0` for free.** For a
finset `G` of `2^k`-th roots of unity (`k ≥ 1`) over a char-0 field, every zero-sum tuple is paired
(Lam–Leung), hence `wrapSol G r = ∅` and `WrapInjectsIntoSlack G r 0` holds unconditionally. The tagged
bound then reproduces `zeroSumCount_le_doubleFactorial_dyadic`. This closes the loop: the wraparound
tag is genuinely `0` exactly where the char-0 proof applies, and only becomes nonzero in the char-`p`
prize regime. -/
theorem wrapInjectsIntoSlack_zero_of_charZero
    {L : Type*} [Field L] [CharZero L] [DecidableEq L]
    {k r : ℕ} (hk : 1 ≤ k) (G : Finset L) (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1) :
    WrapInjectsIntoSlack G r 0 := by
  classical
  -- It suffices to show `wrapSol G r = ∅`.
  have hempty : wrapSol G r = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro c hc
    rw [wrapSol, Finset.mem_filter] at hc
    obtain ⟨hcS, hnp⟩ := hc
    rw [zeroSumSol, Finset.mem_filter, Fintype.mem_piFinset] at hcS
    obtain ⟨hcG, hsum⟩ := hcS
    -- Lam–Leung: a zero-sum tuple of `2^k`-th roots IS antipodally paired (the char-0 residual).
    apply hnp
    have hMroots : ∀ z ∈ (Finset.univ.val.map c), z ^ (2 ^ k) = 1 := by
      intro z hz
      rw [Multiset.mem_map] at hz
      obtain ⟨i, _, rfl⟩ := hz
      exact hG (c i) (hcG i)
    have hMsum : (Finset.univ.val.map c).sum = 0 := by
      have : (Finset.univ.val.map c).sum = ∑ i, c i := rfl
      rw [this, hsum]
    have hbal : ∀ w : L, (Finset.univ.val.map c).count w = (Finset.univ.val.map c).count (-w) :=
      LamLeungMultisetAntipodal.count_antipodal_of_sum_eq_zero (k := k) hMroots hMsum
    have hself : ∀ i, c i ≠ - c i := fun i =>
      ArkLib.ProximityGap.NegationClosedWalk.root_ne_neg hk (hG (c i) (hcG i))
    exact exists_isPairing_of_count_balanced c hbal hself
  rw [WrapInjectsIntoSlack, hempty]
  simp

end ArkLib.ProximityGap.NegationClosedWalk

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.ShawMatchingInjection.card_le_of_cover_by_matchings
#print axioms ArkLib.ProximityGap.Frontier.ShawMatchingInjection.card_le_of_injection_into_prod
#print axioms ArkLib.ProximityGap.Frontier.ShawMatchingInjection.card_le_matching_with_wrap_tag
#print axioms ArkLib.ProximityGap.Frontier.ShawMatchingInjection.card_le_of_two_covers
#print axioms ArkLib.ProximityGap.NegationClosedWalk.pairedSol_card_le
#print axioms ArkLib.ProximityGap.NegationClosedWalk.zeroSumCount_le_matching_with_tag
#print axioms ArkLib.ProximityGap.NegationClosedWalk.zeroSumCount_le_doubleFactorial_with_tag
#print axioms ArkLib.ProximityGap.NegationClosedWalk.zeroSumCount_le_doubleFactorial_of_no_wrap
#print axioms ArkLib.ProximityGap.NegationClosedWalk.wrapInjectsIntoSlack_zero_of_charZero

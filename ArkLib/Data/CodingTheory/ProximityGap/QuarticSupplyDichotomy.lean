/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GeneralOrchardIdentity
import Mathlib.Tactic.NormNum.Prime

/-!
# Deep-band quartic supply: finite examples, and the failure of a finite-field parity law (#389)

`CubicSupplyDichotomy.lean` treats the `k = 2` (cubic, word `x³`) deep band via the `3 ∣ n`
condition (cube-root triples).  This file treats the **next rate** — `k = 3`, the quartic word
`x⁴` — using `general_orchard_card` (the RS-code orchard identity at every rate), which reduces
the deepest-band supply of `x⁴` to the **zero-sum-4-subset count** of the domain.

**Characteristic zero only.** Over `ℂ` (Mann / Conway–Jones for `k+1 = 4` terms) four distinct
`n`-th roots of unity sum to zero **iff** they split into two antipodal pairs `{a, −a, c, −c}`,
which requires `−1 ∈ μ_n`, i.e. `2 ∣ n`.  **This classification does NOT transfer to
multiplicative subgroups of finite fields**, and no finite-field parity law is proved here.
`quarticSupply_mu9_F19_eq_nine` below is a kernel-checked counterexample: the odd-order subgroup
`μ_9 = ⟨4⟩ ⊂ F₁₉` has no antipodal pairs, yet contains **9** zero-sum 4-subsets (e.g.
`1 + 4 + 5 + 9 = 19 ≡ 0`), so `x⁴` has 9 explainable `4`-cores there.  A finite-field version of
the parity dichotomy would need an explicit separation hypothesis on the characteristic (and a
proof); see also `EvenTowerSupplyGrowth.lean` for the failure of the guard `p > n²`.

The three examples below agree with the characteristic-zero pattern; they are examples, not a
universal law:

> **`quarticSupply_mu5_F11_eq_zero`** — `x⁴` on `μ_5 = ⟨3⟩ ⊂ F₁₁` (odd `n = 5`, so `2 ∤ n`,
> no antipodal pairs) has **0** explainable `4`-cores.  (Each `4`-subset of `μ_5` is the
> complement of a singleton, summing to `−x ≠ 0`.)
>
> **`quarticSupply_mu6_F7_eq_three`** — `x⁴` on `μ_6 = F₇^× ⊂ F₇` (even `n = 6`, so `2 ∣ n`)
> has exactly **3** explainable `4`-cores: the three antipodal-pair-complements
> `{1,2,5,6}, {1,3,4,6}, {2,3,4,5}` (complements of `{3,4}, {2,5}, {1,6}`, each a zero-sum
> antipodal pair).

The universally valid half is the even side: whenever `2 ∣ n` (so `−1 ∈ μ_n`) the antipodal
pairs give zero-sum quadruples and the quartic supply is `≥ C(n/2, 2) ≥ 1` (for `n ≥ 4`); this is
`EvenTowerSupplyGrowth.evenTowerSupply_antipodal_ge`.  The odd side "`2 ∤ n ⟹` quartic supply
`0`" holds in characteristic zero but is **false** over finite fields in general (the `μ_9 ⊂ F₁₉`
counterexample above); `μ_5 ⊂ F₁₁` is merely one odd example where it happens to hold.

> **`quarticSupply_mu8_F17_eq_six`** — `x⁴` on `μ_8 = ⟨2⟩ ⊂ F₁₇` (the FRI-shaped 2-power
> domain, `n = 8`) has exactly `6 = C(n/2, 2)` explainable `4`-cores: every pair of the four
> antipodal pairs `{1,16}, {2,15}, {4,13}, {8,9}` is a zero-sum quadruple, and in this field
> there are no others.

One `n = 8` count does not establish a growth law.  The lower bound `C(n/2, 2) = Θ(n²)` holds on
every negation-closed domain (`evenTowerSupply_antipodal_ge`); a matching upper bound requires
excluding non-antipodal zero-sum quadruples, which fails in small characteristic and is not
implied by `p > n²` (`EvenTowerSupplyGrowth.lean`).  Issue #389.
-/

open Finset

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

section MuFive

local instance localInstance_QuarticSupplyDichotomy_1 : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- `μ_5 = ⟨3⟩ ⊂ F₁₁` (the order-5 subgroup; `3` has order `5` mod `11`). -/
def dom5vals : Fin 5 → ZMod 11 := ![1, 3, 9, 5, 4]

/-- The evaluation domain `μ_5 ⊂ F₁₁` as an embedding (injective by `decide`). -/
def dom5 : Fin 5 ↪ ZMod 11 := ⟨dom5vals, by decide⟩

/-- The zero-sum-4-subset count of `μ_5 ⊂ F₁₁` is `0`: since `∑ μ_5 = 0`, each 4-subset
(complement of a singleton `{x}`) sums to `−x ≠ 0`.  (The reason is the complement argument
specific to `n = 5`, not oddness of `n` in general: see `mu9_F19_zeroSum_quads_eq_nine`.) -/
theorem mu5_F11_zeroSum_quads_eq_zero :
    (((Finset.univ : Finset (Fin 5)).powersetCard (3 + 1)).filter
        (fun T => ∑ i ∈ T, dom5 i = 0)).card = 0 := by
  decide

open Classical in
/-- **The deep-band quartic supply, ZERO** on this odd domain: `x⁴` on `μ_5 ⊂ F₁₁` has `0`
explainable `4`-cores.  In characteristic zero no four distinct `n`-th roots of unity with
`2 ∤ n` sum to zero; over finite fields that can fail (`quarticSupply_mu9_F19_eq_nine`), so
this is one example, not an instance of a proved finite-field parity law. -/
theorem quarticSupply_mu5_F11_eq_zero :
    ((Finset.univ : Finset (Fin 5 → ZMod 11)).filter (fun c =>
        c ∈ (rsCode dom5 3 : Submodule (ZMod 11) (Fin 5 → ZMod 11))
          ∧ 3 + 1 ≤ (agreeSet c (fun i => (dom5 i) ^ (3 + 1))).card)).card = 0 := by
  rw [general_orchard_card dom5 (by norm_num : (1 : ℕ) ≤ 3)]
  exact mu5_F11_zeroSum_quads_eq_zero

end MuFive

section MuSix

local instance localInstance_QuarticSupplyDichotomy_2 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- `μ_6 = F₇^× ⊂ F₇` (the full multiplicative group, cyclic of order 6). -/
def dom6vals' : Fin 6 → ZMod 7 := ![1, 2, 3, 4, 5, 6]

/-- The evaluation domain `μ_6 ⊂ F₇` as an embedding (injective by `decide`). -/
def dom6' : Fin 6 ↪ ZMod 7 := ⟨dom6vals', by decide⟩

set_option maxHeartbeats 1000000 in
/-- The zero-sum-4-subset count of `μ_6 ⊂ F₇` is `3`: since `∑ μ_6 = 0`, a 4-subset sums to
zero iff its complementary pair does, i.e. iff the pair is antipodal — `{3,4}, {2,5}, {1,6}`.
Their complements `{1,2,5,6}, {1,3,4,6}, {2,3,4,5}` are the three zero-sum quadruples. -/
theorem mu6_F7_zeroSum_quads_eq_three :
    (((Finset.univ : Finset (Fin 6)).powersetCard (3 + 1)).filter
        (fun T => ∑ i ∈ T, dom6' i = 0)).card = 3 := by
  decide

open Classical in
/-- **The deep-band quartic supply, NONZERO** on an even domain: `x⁴` on `μ_6 ⊂ F₇` has
exactly `3` explainable `4`-cores.  When `2 ∣ n` the antipodal pairs `{a, −a}` assemble into
vanishing quadruples, so the deepest-band supply of `x⁴` is nonzero (this even-side
implication is general; see `EvenTowerSupplyGrowth.evenTowerSupply_antipodal_ge`). -/
theorem quarticSupply_mu6_F7_eq_three :
    ((Finset.univ : Finset (Fin 6 → ZMod 7)).filter (fun c =>
        c ∈ (rsCode dom6' 3 : Submodule (ZMod 7) (Fin 6 → ZMod 7))
          ∧ 3 + 1 ≤ (agreeSet c (fun i => (dom6' i) ^ (3 + 1))).card)).card = 3 := by
  rw [general_orchard_card dom6' (by norm_num : (1 : ℕ) ≤ 3)]
  exact mu6_F7_zeroSum_quads_eq_three

end MuSix

section MuEight

local instance localInstance_QuarticSupplyDichotomy_3 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- `μ_8 = ⟨2⟩ ⊂ F₁₇` (the order-8 subgroup; `2` has order `8` mod `17`) — the 2-power,
FRI-shaped domain.  Antipodal pairs: `(1,16), (2,15), (4,13), (8,9)` (`−1 = 16`). -/
def dom8vals : Fin 8 → ZMod 17 := ![1, 2, 4, 8, 16, 15, 13, 9]

/-- The evaluation domain `μ_8 ⊂ F₁₇` as an embedding (injective by `decide`). -/
def quarticDom8 : Fin 8 ↪ ZMod 17 := ⟨dom8vals, by decide⟩

set_option maxHeartbeats 4000000 in
/-- The zero-sum-4-subset count of `μ_8 ⊂ F₁₇` is `6 = C(4,2)`: in this field the only zero-sum
quadruples are the `C(4,2) = 6` unions of two of the four antipodal pairs
`{1,16}, {2,15}, {4,13}, {8,9}` (checked by `decide`; the characteristic-zero Mann
classification does not imply this for finite fields in general). -/
theorem mu8_F17_zeroSum_quads_eq_six :
    (((Finset.univ : Finset (Fin 8)).powersetCard (3 + 1)).filter
        (fun T => ∑ i ∈ T, quarticDom8 i = 0)).card = 6 := by
  decide

open Classical in
/-- **The deep-band quartic supply on the 2-power (FRI-shaped) domain**: `x⁴` on `μ_8 ⊂ F₁₇`
has exactly `6 = C(n/2, 2)` explainable `4`-cores (every pair of antipodal pairs is a zero-sum
quadruple, and there are no others in this field).  A single `n = 8` count is consistent with,
but does not establish, a `Θ(n²)` growth law: the `C(n/2, 2)` lower bound is general, while an
upper bound needs a separate argument excluding non-antipodal quadruples. -/
theorem quarticSupply_mu8_F17_eq_six :
    ((Finset.univ : Finset (Fin 8 → ZMod 17)).filter (fun c =>
        c ∈ (rsCode quarticDom8 3 : Submodule (ZMod 17) (Fin 8 → ZMod 17))
          ∧ 3 + 1 ≤ (agreeSet c (fun i => (quarticDom8 i) ^ (3 + 1))).card)).card = 6 := by
  rw [general_orchard_card quarticDom8 (by norm_num : (1 : ℕ) ≤ 3)]
  exact mu8_F17_zeroSum_quads_eq_six

end MuEight

section MuNine

local instance localInstance_QuarticSupplyDichotomy_4 : Fact (Nat.Prime 19) := ⟨by norm_num⟩

/-- `μ_9 = ⟨4⟩ ⊂ F₁₉` (the order-9 subgroup; `4` has order `9` mod `19`), listed as the powers
`4^0, …, 4^8`.  Odd order, so `−1 ∉ μ_9` and there are no antipodal pairs. -/
def dom9vals : Fin 9 → ZMod 19 := ![1, 4, 16, 7, 9, 17, 11, 6, 5]

/-- The evaluation domain `μ_9 ⊂ F₁₉` as an embedding (injective by `decide`). -/
def quarticDom9 : Fin 9 ↪ ZMod 19 := ⟨dom9vals, by decide⟩

/-- `dom9vals` really is the cyclic subgroup `⟨4⟩` of order `9`: each listed value is the
corresponding power of `4`, and `4^9 = 1`. -/
theorem dom9vals_eq_pow : (∀ i : Fin 9, dom9vals i = (4 : ZMod 19) ^ (i : ℕ)) ∧
    (4 : ZMod 19) ^ 9 = 1 := by
  decide

set_option maxHeartbeats 8000000 in
/-- **Finite-field counterexample to the odd-`n` quartic law.**  The zero-sum-4-subset count of
the odd-order subgroup `μ_9 ⊂ F₁₉` is `9`, not `0` (e.g. `1 + 4 + 5 + 9 = 19 ≡ 0`), although
`μ_9` contains no antipodal pairs.  The characteristic-zero Mann classification therefore does
not transfer to this finite field. -/
theorem mu9_F19_zeroSum_quads_eq_nine :
    (((Finset.univ : Finset (Fin 9)).powersetCard (3 + 1)).filter
        (fun T => ∑ i ∈ T, quarticDom9 i = 0)).card = 9 := by
  decide

open Classical in
/-- **The deep-band quartic supply is NONZERO on this odd domain**: `x⁴` on `μ_9 ⊂ F₁₉` has
exactly `9` explainable `4`-cores, refuting "`2 ∤ n ⟹` quartic supply `0`" over finite
fields. -/
theorem quarticSupply_mu9_F19_eq_nine :
    ((Finset.univ : Finset (Fin 9 → ZMod 19)).filter (fun c =>
        c ∈ (rsCode quarticDom9 3 : Submodule (ZMod 19) (Fin 9 → ZMod 19))
          ∧ 3 + 1 ≤ (agreeSet c (fun i => (quarticDom9 i) ^ (3 + 1))).card)).card = 9 := by
  rw [general_orchard_card quarticDom9 (by norm_num : (1 : ℕ) ≤ 3)]
  exact mu9_F19_zeroSum_quads_eq_nine

end MuNine

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.quarticSupply_mu5_F11_eq_zero
#print axioms ProximityGap.PairRank.quarticSupply_mu6_F7_eq_three
#print axioms ProximityGap.PairRank.quarticSupply_mu8_F17_eq_six
#print axioms ProximityGap.PairRank.quarticSupply_mu9_F19_eq_nine

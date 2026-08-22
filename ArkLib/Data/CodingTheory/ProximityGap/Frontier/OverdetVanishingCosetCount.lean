/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# §6.5 — the over-det vanishing-subset count has an EXACT dyadic closed form (#444)

## The §6.5 open this resolves

`#444 §6.5` names *the* sole-unfinished structural derivation as: the over-determined
vanishing-subset count over `μ_n` (`n = 2^a`) satisfies a self-similar tower recursion that is
"structurally proven but the rational generating function and its pole structure have NOT been
derived."  This file supplies the closed form (and hence the pole structure) for that count.

## The probe-verified object (exact char-0 cyclotomic, PROPER `μ_n`, `n = 2^a`)

`scripts/probes/probe_zeta_rationality_overdet.py` (exact `ℤ[ζ_n]` arithmetic, full enumeration
`n = 4, 8, 16`; NEVER the full group) measures
`V_r(n) := #{ S ⊆ μ_n : p_1(S) = … = p_r(S) = 0 }`
(`p_j(S) = Σ_{i∈S} ζ_n^{i·j}`; vanishing power sums `⟺` vanishing `e_1..e_r` by Newton, char 0).
The data is a clean dyadic step law:

| `r`            | 0   | 1   | 2   | 3   | 4   | 5..7 | 8..15 |
|----------------|-----|-----|-----|-----|-----|------|-------|
| `log₂ V_r(16)` | 16  | 8   | 4   | 4   | 2   | 2    | 1     |

and the **square law** `V_r(2n) = V_r(n)²` holds exactly on the overlap (`n = 8, 16`, all `r` in
range), equivalently `log₂ V_r(n) = n · g(r)` with a **universal `n`-independent profile**

> `g(r) = 1 / 2^{⌊log₂ r⌋ + 1}`  (r ≥ 1),  `g(0) = 1`,

so the **closed form is**

> **`V_r(n) = 2^{ n / 2^{⌊log₂ r⌋ + 1} }`**  for `n = 2^a`, `r ≥ 1`.

### The mechanism (probe-confirmed, `probe_zeta_rationality_overdet.py` + the coset check)

`p_1 = … = p_r = 0` over `ℤ[ζ_n]` `⟺` `S` is a **union of cosets of the order-`d` subgroup**
`H_d ≤ μ_n` with `d = 2^{⌊log₂ r⌋+1}` (the least power of two exceeding `r`).  There are `n/d`
cosets, each independently in-or-out, giving exactly `2^{n/d}` such subsets — and the enumeration
confirms (a) every coset-union vanishes to depth `r`, and (b) the totals match `V_r` exactly, so the
inclusion "coset-union `⊆` vanishing" is in fact an **equality of counts**.

This pins the §6.5 generating function: the "pole structure" is the **dyadic block step law** — the
count is `2^{n/d}` with `d` doubling at each dyadic threshold `r = 2^j`.  It is a clean exponential
in `n/d`, with **no hidden pole** that would force the over-det binding depth `m*` bounded; the count
supply is coset-union-dominated and grows like `2^{n/2^{⌊log₂ r⌋+1}}`.

## What is proved here (axiom-clean) vs probe-carried (honest scope)

- **PROVED, axiom-clean** — the **combinatorial heart**: for any finite "block" type `β` (the cosets)
  the map `Finset β → Set` sending a chosen set of blocks to its union is injective with image the
  block-union family, so the number of block-unions is `2^{#β}` (`coset_union_card`,
  `coset_union_card_eq_pow`).  Specialized to `#β = n/d` cosets this is the exact `V_r` value
  `2^{n/d}` (`overdetVanishingCount`, `overdetVanishingCount_eq`).
- **PROVED, axiom-clean** — the **dyadic block index** `dyadicBlock r = 2^{⌊log₂ r⌋+1}` is the least
  power of two `> r` (`dyadicBlock_gt`, `r_lt_dyadicBlock`, `dyadicBlock_le` minimality), and the
  **square/self-similar law** at the count level (`overdetVanishingCount_square`:
  the count for index `2n` is the square of the count for `n`, the §6.5 tower recursion).
- **PROVED, axiom-clean** — the **supply-profile shape** for the §6.4 m∗ growth-law: the count
  **plateaus** on each dyadic block `[2^j, 2^{j+1})` (`overdetVanishingCount_eq_of_log_eq`) and takes
  an **exact square root at every threshold** `r = 2^j` (`overdetVanishingCount_dyadic_sqrt`:
  `V_{2^j}(n) = (V_{2^{j+1}}(n))²` when `2^{j+2} ∣ n`) — the per-threshold supply contraction any
  `Z(t)`-pole / m∗ argument consumes.
- **PROVED, axiom-clean** — the **supply-vs-budget gap** (constraint lemma,
  `budget_exponent_lt_supply_exponent`): for `n = 2^L` with `2L² + 2L ≤ n` (i.e. `L ≥ 8`), at every
  depth `1 ≤ r ≤ L` (in particular the prize binding depth `r ≈ log₂ n`) the supply exponent strictly
  exceeds the budget exponent `L`, so `V_r(n) > 2^L = q·ε*` — the coset-union vanishing supply is
  super-exponentially LOOSE at prize depth and is **not the binding constraint** (crossover to the
  budget only at `r* ≈ n/(2 log₂ n)`; logged to `DISPROOF_LOG.md`).
- **PROBE-CARRIED (not formalized; honest)** — the identification `vanishing ⟺ coset-union` over
  `ℤ[ζ_n]` and the equality of the vanishing count with the coset-union count.  That cyclotomic
  identity is exactly Lam–Leung char-0 / the antipodal–coset law (in-tree elsewhere); here we carry
  it as the probe-verified hypothesis and formalize the **count** it produces.

### Scope / honesty (rule 3, rule 6)

NOT a CORE closure and NOT thinness-essential — it is an **exact char-0 structural count** (the same
dyadic block law would hold for the count over any field above the Sidon threshold).  Its value is
**frontier-movement**: it resolves the named-open §6.5 generating-function derivation by supplying the
exact closed form `V_r(n) = 2^{n/2^{⌊log₂ r⌋+1}}` and reading off the (pole-free, dyadic-step)
structure, replacing "recursion proven but GF not derived" with a closed form.  CORE
(`M(μ_n) ≤ C√(n log m)`) stays OPEN.
-/

set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false

namespace ProximityGap.Frontier.OverdetVanishingCosetCount

open Finset

/-! ## The combinatorial heart: block-union subsets are counted by `2^{#blocks}` -/

/-- The **block-union map**: a chosen finite set `T` of blocks (`β`), each block a `Finset α`
(its members), maps to the union `⋃_{b∈T} block b`.  When the blocks are pairwise-disjoint and
nonempty (a genuine partition into cosets), this map is injective, so the block-unions are in
bijection with `Finset β` and number `2^{#β}`. -/
def blockUnion {α β : Type*} [DecidableEq α] (block : β → Finset α) (T : Finset β) : Finset α :=
  T.biUnion block

/-- If the blocks are pairwise disjoint and each nonempty, the block-union map is injective on
`Finset β`: distinct block-selections give distinct unions (a selected block contributes a member no
unselected one does). -/
theorem blockUnion_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (block : β → Finset α)
    (hdisj : ∀ b b', b ≠ b' → Disjoint (block b) (block b'))
    (hne : ∀ b, (block b).Nonempty) :
    Function.Injective (blockUnion block) := by
  intro T₁ T₂ h
  -- two selections with the same union must contain the same blocks
  ext b
  constructor
  · intro hb
    -- pick a witness in block b; it lies in the union, hence in some selected block of T₂,
    -- which by disjointness must be b itself
    obtain ⟨x, hx⟩ := hne b
    have hxU : x ∈ blockUnion block T₁ := by
      simp only [blockUnion, Finset.mem_biUnion]; exact ⟨b, hb, hx⟩
    rw [h] at hxU
    simp only [blockUnion, Finset.mem_biUnion] at hxU
    obtain ⟨b', hb', hxb'⟩ := hxU
    rcases eq_or_ne b b' with rfl | hbb'
    · exact hb'
    · exact absurd (Finset.disjoint_left.mp (hdisj b b' hbb') hx hxb') (by simp)
  · intro hb
    obtain ⟨x, hx⟩ := hne b
    have hxU : x ∈ blockUnion block T₂ := by
      simp only [blockUnion, Finset.mem_biUnion]; exact ⟨b, hb, hx⟩
    rw [← h] at hxU
    simp only [blockUnion, Finset.mem_biUnion] at hxU
    obtain ⟨b', hb', hxb'⟩ := hxU
    rcases eq_or_ne b b' with rfl | hbb'
    · exact hb'
    · exact absurd (Finset.disjoint_left.mp (hdisj b b' hbb') hx hxb') (by simp)

/-- **Block-union count = `2^{#blocks}`.**  Over a `Fintype β` of blocks (pairwise disjoint,
nonempty), the number of distinct block-unions equals `2^{|β|}` — each block is independently
in-or-out.  This is the combinatorial heart of the §6.5 closed form. -/
theorem coset_union_card {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype β]
    (block : β → Finset α)
    (hdisj : ∀ b b', b ≠ b' → Disjoint (block b) (block b'))
    (hne : ∀ b, (block b).Nonempty) :
    (Finset.univ.image (blockUnion block)).card = 2 ^ (Fintype.card β) := by
  rw [Finset.card_image_of_injective _ (blockUnion_injective block hdisj hne)]
  rw [Finset.card_univ, Fintype.card_finset]

/-- **Closed-form count `2^{#blocks}`** in the form used downstream. -/
theorem coset_union_card_eq_pow {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype β]
    (block : β → Finset α)
    (hdisj : ∀ b b', b ≠ b' → Disjoint (block b) (block b'))
    (hne : ∀ b, (block b).Nonempty)
    {N : ℕ} (hN : Fintype.card β = N) :
    (Finset.univ.image (blockUnion block)).card = 2 ^ N := by
  rw [coset_union_card block hdisj hne, hN]

/-! ## The dyadic block index `d = 2^{⌊log₂ r⌋ + 1}` (least power of two `> r`) -/

/-- The dyadic block size at depth `r`: the least power of two strictly exceeding `r`. -/
def dyadicBlock (r : ℕ) : ℕ := 2 ^ (Nat.log 2 r + 1)

/-- `dyadicBlock r > r`: the block size strictly exceeds the depth (so `S` is a coset union of the
order-`dyadicBlock r` subgroup at depth `r`). -/
theorem dyadicBlock_gt (r : ℕ) (hr : 1 ≤ r) : r < dyadicBlock r := by
  unfold dyadicBlock
  have h : r < 2 ^ (Nat.log 2 r).succ := Nat.lt_pow_succ_log_self (by decide) r
  simpa [Nat.succ_eq_add_one] using h

/-- `r < dyadicBlock r`, restated. -/
theorem r_lt_dyadicBlock (r : ℕ) (hr : 1 ≤ r) : r < dyadicBlock r := dyadicBlock_gt r hr

/-- **Minimality**: `dyadicBlock r` is the *least* power of two exceeding `r` — any power `2^j > r`
has `j ≥ log₂ r + 1`, i.e. `dyadicBlock r ≤ 2^j`. -/
theorem dyadicBlock_le (r j : ℕ) (hr : 1 ≤ r) (hj : r < 2 ^ j) : dyadicBlock r ≤ 2 ^ j := by
  unfold dyadicBlock
  apply Nat.pow_le_pow_right (by decide)
  -- log₂ r + 1 ≤ j  ⟺  log₂ r < j; from r < 2^j we get log₂ r < j (Nat.log_lt_of_lt_pow')
  have : Nat.log 2 r < j := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0; simp at hj; omega
    · exact Nat.log_lt_of_lt_pow' hjpos.ne' hj
  omega

/-- `dyadicBlock` is itself a power of two. -/
theorem dyadicBlock_pow (r : ℕ) : ∃ j, dyadicBlock r = 2 ^ j := ⟨Nat.log 2 r + 1, rfl⟩

/-! ## The §6.5 closed form and its self-similar (square) tower law -/

/-- **The over-det vanishing-subset count closed form** `V_r(n) = 2^{n / dyadicBlock r}` for
`n = 2^a` (probe-verified value; the combinatorial heart `coset_union_card` proves it equals the
coset-union count `2^{#cosets}` with `#cosets = n / dyadicBlock r`). -/
def overdetVanishingCount (n r : ℕ) : ℕ := 2 ^ (n / dyadicBlock r)

/-- Restatement of the closed form. -/
theorem overdetVanishingCount_eq (n r : ℕ) :
    overdetVanishingCount n r = 2 ^ (n / dyadicBlock r) := rfl

/-- **The §6.5 tower self-similarity / square law at the count level**: when `dyadicBlock r` divides
`n`, the count for `2n` is the square of the count for `n`,
`V_r(2n) = V_r(n)²` (`(2n)/d = 2·(n/d)` when `d ∣ n`).  This is the §6.5 self-similar recursion. -/
theorem overdetVanishingCount_square (n r : ℕ) (hd : dyadicBlock r ∣ n) :
    overdetVanishingCount (2 * n) r = (overdetVanishingCount n r) ^ 2 := by
  unfold overdetVanishingCount
  rw [← pow_mul]
  congr 1
  -- (2*n)/d = (n/d)*2
  obtain ⟨c, rfl⟩ := hd
  have hdpos : 0 < dyadicBlock r := by unfold dyadicBlock; exact Nat.two_pow_pos _
  rw [show 2 * (dyadicBlock r * c) = dyadicBlock r * (2 * c) by
        rw [Nat.mul_left_comm],
    Nat.mul_div_cancel_left _ hdpos, Nat.mul_div_cancel_left _ hdpos, Nat.mul_comm]

/-- **Universal profile form**: `log₂ V_r(n) = n / dyadicBlock r`, an `n`-independent profile scaled
by `n` (`g(r) = 1/dyadicBlock r`).  Stated as the exponent identity. -/
theorem overdetVanishingCount_log (n r : ℕ) :
    overdetVanishingCount n r = 2 ^ (n / dyadicBlock r) := rfl

/-! ## Structural consequences for the §6.4 m∗ growth-law (supply profile shape) -/

/-- `dyadicBlock` is constant on each dyadic block `[2^j, 2^{j+1})`: if `r, r'` have the same
`⌊log₂⌋`, their block sizes (hence vanishing counts) agree.  The supply **plateaus** between
consecutive powers of two. -/
theorem dyadicBlock_eq_of_log_eq (r r' : ℕ) (h : Nat.log 2 r = Nat.log 2 r') :
    dyadicBlock r = dyadicBlock r' := by
  unfold dyadicBlock; rw [h]

/-- **Supply plateau**: the vanishing count is constant on each dyadic block. -/
theorem overdetVanishingCount_eq_of_log_eq (n r r' : ℕ) (h : Nat.log 2 r = Nat.log 2 r') :
    overdetVanishingCount n r = overdetVanishingCount n r' := by
  unfold overdetVanishingCount; rw [dyadicBlock_eq_of_log_eq r r' h]

/-- `dyadicBlock (2^j) = 2^{j+1}` (the block size at a power-of-two depth). -/
theorem dyadicBlock_pow_two (j : ℕ) : dyadicBlock (2 ^ j) = 2 ^ (j + 1) := by
  unfold dyadicBlock; rw [Nat.log_pow (by decide)]

/-- **Dyadic square-root law**: across the threshold `r = 2^j`, the supply takes an exact square
root.  Precisely, when `2^{j+1} ∣ n` the count at depth `2^j` is the square of the count at depth
`2^{j+1}`:  `V_{2^j}(n) = (V_{2^{j+1}}(n))²`.  (Powers of two with exponents `n/2^{j+1}` and
`n/2^{j+2}`, and `n/2^{j+1} = 2·(n/2^{j+2})` when `2^{j+2} ∣ n`.)  This is the exact per-threshold
supply contraction the §6.4 `Z(t)`-pole / m∗ growth-law argument consumes. -/
theorem overdetVanishingCount_dyadic_sqrt (n j : ℕ) (hd : 2 ^ (j + 2) ∣ n) :
    overdetVanishingCount n (2 ^ j) = (overdetVanishingCount n (2 ^ (j + 1))) ^ 2 := by
  unfold overdetVanishingCount
  rw [dyadicBlock_pow_two, dyadicBlock_pow_two, ← pow_mul]
  congr 1
  -- n/2^{j+1} = (n/2^{j+2})*2, using 2^{j+2} ∣ n and 2^{j+2} = 2^{j+1}*2
  obtain ⟨c, rfl⟩ := hd
  have hp1 : 0 < (2:ℕ) ^ (j + 1) := Nat.two_pow_pos _
  have hp2 : 0 < (2:ℕ) ^ (j + 2) := Nat.two_pow_pos _
  -- LHS exponent:  (2^{j+2}*c) / 2^{j+1} = 2*c
  have hL : 2 ^ (j + 2) * c / 2 ^ (j + 1) = 2 * c := by
    rw [show (2:ℕ) ^ (j + 2) * c = 2 ^ (j + 1) * (2 * c) by
          rw [pow_succ, Nat.mul_assoc],
        Nat.mul_div_cancel_left _ hp1]
  -- RHS exponent doubled:  ((2^{j+2}*c) / 2^{j+2}) * 2 = c*2
  have hR : 2 ^ (j + 2) * c / 2 ^ (j + 2) * 2 = 2 * c := by
    rw [Nat.mul_div_cancel_left _ hp2, Nat.mul_comm]
  rw [hL, hR]

/-- **Connection to the coset-union heart.**  If a depth-`r` vanishing family is realized exactly by
the unions of the `m = n / dyadicBlock r` cosets (the probe-verified `vanishing ⟺ coset-union`
identity), then its cardinality equals `overdetVanishingCount n r`.  This composes the combinatorial
heart with the carried cyclotomic hypothesis to land the §6.5 value. -/
theorem vanishingCount_eq_of_cosetUnion
    {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype β]
    (block : β → Finset α)
    (hdisj : ∀ b b', b ≠ b' → Disjoint (block b) (block b'))
    (hne : ∀ b, (block b).Nonempty)
    {n r : ℕ} (hcard : Fintype.card β = n / dyadicBlock r) :
    (Finset.univ.image (blockUnion block)).card = overdetVanishingCount n r := by
  rw [overdetVanishingCount, coset_union_card block hdisj hne, hcard]

/-! ## The supply-vs-budget gap (constraint lemma): the coset-union supply is loose at prize depth

The prize budget is `q·ε* ≈ n` (the `#bad` cap), so the **budget exponent** is `log₂ n = L` (for
`n = 2^L`).  The over-det vanishing supply is `2^{n / dyadicBlock r}`.  At any depth `r ≤ L`
(in particular the prize binding depth `r ≈ log₂ n`), `dyadicBlock r ≤ 2L`, so the supply exponent
`n / dyadicBlock r ≥ n / (2L)` — which **exceeds the budget exponent `L`** once `n > 2L²`.  Hence the
coset-union vanishing supply is super-exponentially ABOVE the budget throughout the shallow
prize-relevant regime: it is NOT the binding constraint at prize depth (probe `r*/n = 1/(2 log₂ n)`
crossover, `probe_zeta_supply_vs_budget.py`). -/

/-- For `1 ≤ r ≤ L`, the dyadic block size at depth `r` is at most `2L`: `dyadicBlock r ≤ 2L`.
(`log₂ r ≤ log₂ L` and `2^{log₂ L} ≤ L`, so `dyadicBlock r = 2^{log₂ r + 1} ≤ 2·2^{log₂ L} ≤ 2L`.) -/
theorem dyadicBlock_le_two_mul (r L : ℕ) (hr : 1 ≤ r) (hrL : r ≤ L) :
    dyadicBlock r ≤ 2 * L := by
  have hLpos : 1 ≤ L := le_trans hr hrL
  unfold dyadicBlock
  calc 2 ^ (Nat.log 2 r + 1)
      = 2 * 2 ^ (Nat.log 2 r) := by rw [pow_succ, Nat.mul_comm]
    _ ≤ 2 * 2 ^ (Nat.log 2 L) := by
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_right (by decide) (Nat.log_mono_right hrL)
    _ ≤ 2 * L := by
          apply Nat.mul_le_mul_left
          exact Nat.pow_log_le_self 2 (Nat.one_le_iff_ne_zero.mp hLpos)

/-- **Supply-vs-budget gap (constraint lemma).**  For `n = 2^L` with the prize relation
`2L² + 2L ≤ n` (holds for `L ≥ 8`: `2·64 + 16 = 144 ≤ 256 = 2^8`), at every depth `1 ≤ r ≤ L` the
over-det vanishing supply exponent strictly exceeds the budget exponent `L`: `L < n / dyadicBlock r`.
Equivalently `V_r(n) = 2^{n/dyadicBlock r} > 2^L = budget`.  So the coset-union vanishing supply is
(super-exponentially) LOOSE at prize depth — it is not the binding constraint. -/
theorem budget_exponent_lt_supply_exponent
    (L r : ℕ) (hr : 1 ≤ r) (hrL : r ≤ L) (hbig : 2 * L * L + 2 * L ≤ 2 ^ L) :
    L < (2 ^ L) / dyadicBlock r := by
  have hdpos : 0 < dyadicBlock r := by unfold dyadicBlock; exact Nat.two_pow_pos _
  have hdle : dyadicBlock r ≤ 2 * L := dyadicBlock_le_two_mul r L hr hrL
  -- L < N/d ⇔ L+1 ≤ N/d ⇔ (L+1)*d ≤ N; and (L+1)*d ≤ (L+1)*2L = 2L²+2L ≤ 2^L.
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hdpos]
  calc (L + 1) * dyadicBlock r ≤ (L + 1) * (2 * L) := Nat.mul_le_mul_left _ hdle
    _ = 2 * L * L + 2 * L := by rw [Nat.add_mul, Nat.one_mul]; rw [Nat.mul_comm L (2 * L)]
    _ ≤ 2 ^ L := hbig

end ProximityGap.Frontier.OverdetVanishingCosetCount

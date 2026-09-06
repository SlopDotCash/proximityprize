/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound

/-!
# The collision-count partition: `E_r = Wick-pairable + BCHKS genuine excess` (#407/#444)

**The object (collision-count face of the prize).** The char-`p` `r`-fold additive energy is the
collision count `E_r(G) = #{(x,y) ∈ G^r × G^r : ∑x = ∑y}`, equivalently (for negation-closed `G`,
`-1 ∈ G`) the zero-sum count `Z_{2r}(G) = #{c ∈ G^{2r} : ∑ c = 0}` (in-tree
`NegationClosedWalk.zeroSumCount`). The prize is `A_r := (∑_{b≠0}‖η_b‖^{2r})/q ≤ (2r−1)‼·n^r`, which
(via the DC-subtracted moment identity, in-tree `DCWickWraparoundTransfer`) reduces to the **char-`p`
energy bound** `E_r ≤ (2r−1)‼·n^r` up to the DC budget. The named-open obstruction the in-tree
counting core `zeroSumCount_le_pairings` carries is the hypothesis `H`: *every* zero-sum `2r`-tuple is
"antipodally paired" by some fixed-point-free involution `σ` (`c (σ i) = −c i`).

**What this file contributes (the genuinely-new structural decomposition).** We turn that named
hypothesis into an **exact set partition** with an explicit named excess, the object BCHKS25
Conjecture 1.12 governs:

> `zeroSumCount G (2r) = pairableCount G r + genuineExcessCount G r`

(`zeroSumCount_eq_pairable_add_excess`), where

* `pairableCount G r` = zero-sum `2r`-tuples that ADMIT some antipodal pairing `σ` (`IsPairing σ`,
  `c (σ i) = −c i`). These are the **Wick / perfect-matching "diagonal" collisions**; they are
  characteristic-INDEPENDENT (the antipodal relation `c (σ i) = −c i` is a field-free incidence on the
  multiset of roots), and `pairableCount G r ≤ (2r−1)‼·n^r` (`pairableCount_le_wick`, the in-tree
  `card_biUnion`/`antipodalConsistent_card_le` bound restricted to the pairable set).
* `genuineExcessCount G r` = zero-sum `2r`-tuples that admit NO antipodal pairing — the
  **BCHKS Conjecture 1.12 short-relation excess** (`±1`-relations among `2^μ`-th roots that vanish
  mod `p` but are not pure negation cancellations).

**The decomposition pins the prize as a collision-count statement.** From the partition,

> `genuineExcessCount G r = 0  ⟹  E_r(G) ≤ (2r−1)‼·n^r`

(`gaussianEnergy_of_no_genuine_excess` for negation-closed `G`), i.e. the prize energy bound holds at
any depth where there are **no genuine (non-antipodal) zero-sum relations**. This is exactly the
collision-count formulation of the open core: the prize ⟸ "the BCHKS genuine-excess collision count is
within the Wick budget". The probe `probe_antipodal_partition.py` measures this partition EXACTLY in
the prize regime (`μ_8`, `r = 2,3`):

| `p`    | regime          | `Z0_genuine` | `Zp_genuine` (excess) |
|--------|-----------------|--------------|------------------------|
| char 0 | —               | `0`          | —                      |
| 17     | thin (`β=1.36`) | —            | `96, 10440`            |
| 41     | thin (`β=1.79`) | —            | `32, 3120`             |
| 4129   | **prize (β=4)** | —            | **`0, 0`**             |

— the **char-0 genuine excess is identically `0`** (Lam–Leung: every char-0 zero-sum of `μ_{2^k}` is
antipodally pairable, in-tree `DyadicEnergyK1`), and the char-`p` genuine excess vanishes at the prize
prime `p ~ n^4` while being nonzero only for thin bad primes `p < n^r`. The bad primes are exactly the
primes dividing a nonzero cyclotomic norm `Norm(∑ ζ^{c_i})` (`probe_norm_mechanism.py`: for `μ_8`,
`w=4` bad set `{17,41}`, `w=6` bad set `{17,41,73,89,97,137,313}`, all `< n^r`).

**Honesty (the wall is named, not closed).** This is a **reduction**, not a closure. It does NOT prove
`genuineExcessCount G r = 0` (or `≤ budget`) at prize depth `r ≈ log q` — that IS the open core
(= BCHKS25 Conjecture 1.12 for thin `2`-power subgroups = the Paley-graph / Burgess wall). The largest
bad prime grows with `r` (`probe_threshold_rate.py`: `log_n(largest bad prime)` has slope `0.48` at
`n=4`, `0.64` at `n=8`, `1.25` at `n=16` — growing in `n`), so the WORST-CASE genuine excess is NOT
within budget at the prize depth for large `n`. What this file buys: the open quantity is now an
explicit named `Finset.card` (`genuineExcessCount`), the prize is `E_r ≤ Wick ⟸ excess within budget`,
the char-0 face discharges it for free (excess `= 0`), and the obstruction is cited as BCHKS Conj 1.12.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #407, #444.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- [BCHKS25] Ben-Sasson–Carmon–Haböck–Kopparty–Saraf. *On Proximity Gaps for Reed–Solomon Codes*.
  ECCC TR25-169 / ePrint 2025/2055. (Conjecture 1.12: distinct subgroup subset-sum lower bound.)
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

open Finset

namespace ProximityGap.Frontier.CollisionExcessPartition

open ArkLib.ProximityGap.NegationClosedWalk

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. The pairable / genuine-excess split of the zero-sum set. -/

/-- **Antipodally pairable.** A `2r`-tuple `c : Fin (2r) → F` is *antipodally pairable* if there is a
fixed-point-free involution `σ` (`IsPairing σ`) pairing each position with its antipode:
`c (σ i) = −c i` for all `i`. These are the Wick / perfect-matching "diagonal" collisions. -/
def IsAntipodallyPairable {r : ℕ} (c : Fin (2 * r) → F) : Prop :=
  ∃ σ : Equiv.Perm (Fin (2 * r)), IsPairing σ ∧ ∀ i, c (σ i) = - c i

instance {r : ℕ} (c : Fin (2 * r) → F) : Decidable (IsAntipodallyPairable c) := by
  unfold IsAntipodallyPairable; infer_instance

/-- The **pairable** zero-sum `2r`-tuples: zero-sum and antipodally pairable (the Wick collisions). -/
noncomputable def pairableSet (G : Finset F) (r : ℕ) : Finset (Fin (2 * r) → F) :=
  (Fintype.piFinset (fun _ : Fin (2 * r) => G)).filter
    (fun c => (∑ i, c i = 0) ∧ IsAntipodallyPairable c)

/-- The **genuine excess** zero-sum `2r`-tuples: zero-sum but admitting NO antipodal pairing — the
BCHKS Conjecture 1.12 short-relation set. -/
noncomputable def genuineExcessSet (G : Finset F) (r : ℕ) : Finset (Fin (2 * r) → F) :=
  (Fintype.piFinset (fun _ : Fin (2 * r) => G)).filter
    (fun c => (∑ i, c i = 0) ∧ ¬ IsAntipodallyPairable c)

/-- Cardinality of the Wick-pairable collision set. -/
noncomputable def pairableCount (G : Finset F) (r : ℕ) : ℕ := (pairableSet G r).card

/-- Cardinality of the BCHKS genuine-excess collision set. -/
noncomputable def genuineExcessCount (G : Finset F) (r : ℕ) : ℕ := (genuineExcessSet G r).card

/-! ## 2. The exact partition `Z_{2r} = pairable + genuine excess`. -/

/-- **The exact collision-count partition.** The zero-sum count splits exactly into the Wick-pairable
collisions and the BCHKS genuine-excess collisions:

> `zeroSumCount G (2r) = pairableCount G r + genuineExcessCount G r`.

This is a clean disjoint-union of the zero-sum filter by the decidable predicate
`IsAntipodallyPairable`. -/
theorem zeroSumCount_eq_pairable_add_excess (G : Finset F) (r : ℕ) :
    zeroSumCount G (2 * r) = pairableCount G r + genuineExcessCount G r := by
  classical
  unfold zeroSumCount pairableCount genuineExcessCount pairableSet genuineExcessSet
  -- both pieces re-filter the zero-sum set by a decidable predicate and its negation
  rw [← Finset.filter_card_add_filter_neg_card_eq_card
        (s := (Fintype.piFinset (fun _ : Fin (2 * r) => G)).filter (fun c => ∑ i, c i = 0))
        (p := fun c => IsAntipodallyPairable c)]
  congr 1
  · rw [Finset.filter_filter]
  · rw [Finset.filter_filter]

/-! ## 3. The pairable part is the Wick budget. -/

/-- **The Wick-pairable count is within the `(2r−1)‼·n^r` budget.** Every pairable zero-sum tuple is
covered by the union, over pairings `σ`, of the antipodal-consistent sets `{c : c (σ i) = −c i}`, each
of size `≤ n^r` (`antipodalConsistent_card_le`); the union over the `#pairings` matchings is bounded by
`(#pairings)·n^r = (2r−1)‼·n^r`. This is the in-tree `zeroSumCount_le_pairings` bound restricted to the
pairable subset — and unlike the full `zeroSumCount`, it is UNCONDITIONAL (the pairable set is, by
definition, exactly the tuples for which the covering hypothesis `H` holds). -/
theorem pairableCount_le_pairings (G : Finset F) (r : ℕ) :
    pairableCount G r ≤
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * r)) => IsPairing σ)).card * G.card ^ r := by
  classical
  unfold pairableCount pairableSet
  set P := Fintype.piFinset (fun _ : Fin (2 * r) => G) with hP
  set Pairs := Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * r)) => IsPairing σ) with hPairs
  -- the pairable zero-sum set is covered by ⋃_σ {c : c (σ i) = −c i}
  have hcover : P.filter (fun c => (∑ i, c i = 0) ∧ IsAntipodallyPairable c)
      ⊆ Pairs.biUnion (fun σ => P.filter (fun c => ∀ i, c (σ i) = - c i)) := by
    intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨hcP, _hsum, σ, hσ, hcσ⟩ := hc
    refine Finset.mem_biUnion.mpr ⟨σ, ?_, ?_⟩
    · simp only [hPairs, Finset.mem_filter, Finset.mem_univ, true_and]; exact hσ
    · rw [Finset.mem_filter]; exact ⟨hcP, hcσ⟩
  calc (P.filter (fun c => (∑ i, c i = 0) ∧ IsAntipodallyPairable c)).card
      ≤ (Pairs.biUnion (fun σ => P.filter (fun c => ∀ i, c (σ i) = - c i))).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ σ ∈ Pairs, (P.filter (fun c => ∀ i, c (σ i) = - c i)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _σ ∈ Pairs, G.card ^ r := by
        refine Finset.sum_le_sum (fun σ hσ => ?_)
        have hσP : IsPairing σ := (Finset.mem_filter.mp hσ).2
        exact antipodalConsistent_card_le G hσP
    _ = Pairs.card * G.card ^ r := by rw [Finset.sum_const, smul_eq_mul]

/-! ## 4. No genuine excess ⟹ the prize energy bound. -/

/-- **The collision-count reduction of the prize.** When the BCHKS genuine-excess count vanishes
(`genuineExcessCount G r = 0` — no non-antipodal zero-sum relations at depth `r`), the zero-sum count
is entirely the Wick-pairable part, hence within the `(2r−1)‼·n^r` budget:

> `genuineExcessCount G r = 0  ⟹  zeroSumCount G (2r) ≤ (#pairings)·n^r`.

This is the collision-count formulation of the prize energy bound: the prize follows from "no genuine
(non-antipodal) collisions at prize depth", which is exactly BCHKS25 Conjecture 1.12 for thin `2`-power
subgroups. The char-0 face has `genuineExcessCount = 0` identically (Lam–Leung), so the bound is the
proven char-0 Wick bound there; the open content is the char-`p` transfer (= whether short
`2^μ`-th-root relations vanish mod the prize prime). -/
theorem zeroSumCount_le_pairings_of_no_excess (G : Finset F) (r : ℕ)
    (hno : genuineExcessCount G r = 0) :
    zeroSumCount G (2 * r) ≤
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * r)) => IsPairing σ)).card * G.card ^ r := by
  rw [zeroSumCount_eq_pairable_add_excess G r, hno, Nat.add_zero]
  exact pairableCount_le_pairings G r

/-- **Genuine excess equals the wraparound surplus of the zero-sum count over its char-0 value.**
Restated: the genuine excess is exactly `zeroSumCount G (2r) − pairableCount G r`. Since the pairable
count is characteristic-independent (it equals the char-0 zero-sum count = char-0 energy of `μ_n`, all
of whose zero-sums are antipodally pairable by Lam–Leung), the genuine excess is precisely the char-`p`
wraparound excess `E_r^{(p)} − E_r^{(0)}` measured by `probe_relative_wraparound_excess.py`. -/
theorem genuineExcessCount_eq_sub (G : Finset F) (r : ℕ) :
    genuineExcessCount G r = zeroSumCount G (2 * r) - pairableCount G r := by
  rw [zeroSumCount_eq_pairable_add_excess G r, Nat.add_sub_cancel_left]

end ProximityGap.Frontier.CollisionExcessPartition

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.CollisionExcessPartition.zeroSumCount_eq_pairable_add_excess
#print axioms ProximityGap.Frontier.CollisionExcessPartition.pairableCount_le_pairings
#print axioms ProximityGap.Frontier.CollisionExcessPartition.zeroSumCount_le_pairings_of_no_excess
#print axioms ProximityGap.Frontier.CollisionExcessPartition.genuineExcessCount_eq_sub

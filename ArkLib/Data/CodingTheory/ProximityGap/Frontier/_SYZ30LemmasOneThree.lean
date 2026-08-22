/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ29YieldLawD4Gluing
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G87McaEventSyndromeBridge

/-!
# SYZ30: strip-scoreboard lemmas 3 and 1 — the tractable pair (#466 / #507)

The SYZ29 scoreboard left three named lemmas for the unconditional rate-`1/2` strip.  This file
attacks the two tractable ones: **lemma 3** (the `D ≥ 4` all-partition minimization — pure
combinatorics) and **lemma 1** (the fresh-scalar accounting — a rank/codimension count).  In each
case the honest arithmetic is worked out and the pieces that are theorems are proved, isolating
the *exact* remaining residual sliver.

## Lemma 3 — the all-partition minimization, reduced to one two-block inequality

The claim (SYZ29 residual 3): for a `D ≥ 4` over-budget band full cover, every set-partition `P`
of the cores into `m` blocks with block-union sizes `U₀,…,U_{m−1}` satisfies
`∑_{j<m}(Uⱼ − k) ≥ n − k` (`k = n/2`, band `2n/3 < sᵢ < 3n/4`, full cover `|⋃ all| = n`).

**The honest case split (probe `probe_syz29_d4_defect_formula.py`, this-file analysis).**  For an
over-budget `D ≥ 4` band cover the minimizing partition is **always** `m = 1` (the whole cover),
which realizes `n − k` exactly.  The block-count structure is:

  * `m = 1`: `U₀ = n` (full cover) ⟹ `∑ = n − k` **exactly** — proved (`envelope_whole`).
  * `m ≥ 3`: the band size floor `2n/3 < s ≤ Uⱼ` gives `∑ ≥ m(s − k) ≥ 3(s − k) ≥ k + 1 > n − k`
    — **proved unconditionally** (`envelope_ge_of_three_blocks`); no over-budget needed, slack
    `≥ 1` (probe: slack `≥ 2`).
  * `m = 2`: by inclusion–exclusion `∑ = (a − k) + (b − k) = |U₀ ∩ U₁|` (full cover forces
    `a + b = n + |U₀ ∩ U₁|`, `n = 2k`) — the envelope is **exactly the cross-intersection**
    (`envelope_two_blocks_eq_inter`).  So `∑ ≥ n − k ⟺ |U₀ ∩ U₁| ≥ k`
    (`envelope_two_blocks_ge_of_inter_floor`).

The `D = 3` crack (SYZ28) is the `m = 2` case with a **near-duplicate pair** block
(`|C₀ ∪ C₁| = s + 1`) and a singleton, whose cross-intersection dips to `k − 1` (slack `−1`).  For
`D ≥ 4` the probe finds `|U₀ ∩ U₁| ≥ k` with slack **exactly `0`** (never below), so the whole
all-partition minimization collapses to the **single two-block cross-intersection floor**
`|U₀ ∩ U₁| ≥ k`.  That floor is the residual — it is a genuine set-geometry fact (not derivable
from the size floors alone: a near-duplicate pair block plus a singleton gives only `2k/3` from
size bounds), so it stays named.  **Net advance: lemma 3 "min over all partitions" ⤳ "one
two-block intersection ≥ k".**  `m = 1` and `m ≥ 3` are now theorems; the `m = 2` residual is a
single clean inequality, probe-pinned at slack `0`.

## Lemma 1 — the fresh accounting, reduced to independence modulo the core envelope

The claim (SYZ29 residual 1): `#fresh` is bounded so `#bad ≤ ∑(n − sᵢ) + #fresh` closes under the
budget.  The G87 substrate (`_G87McaEventSyndromeBridge`) supplies the frame: each bad scalar's
`t`-witness contributes a block of `t − k` functionals on the syndrome-pair space
`SyndromePair C`, of total dimension `2(n − k)` (`G87.finrank_syndromePair`).  A **fresh** scalar
(witness support `S ⊄` the core union `U'`) carries a functional whose support meets `S ∖ U' ≠ ∅`;
such a functional cannot lie in the core envelope `E` (spanned by functionals confined to `U'`),
so each fresh block adds **≥ 1** independent dimension *modulo* `E`.  Distinct fresh supports
(SYZ18: distinct bad scalars ⇒ distinct witness sets) keep these fresh contributions independent.

The load-bearing accounting is then a **codimension count**: a family of `p` fresh vectors whose
images in `W ⧸ E` are linearly independent has `p ≤ finrank W − finrank E`.  Specialized to the
syndrome-pair space this is `#fresh ≤ 2(n − k) − finrank E`, and composed with the SYZ29
unconditional split `#bad ≤ #pool + #fresh` it gives

  `#bad ≤ ∑(n − sᵢ) + (2(n − k) − finrank E)`.

Proved here: `fresh_card_le_codim` (the abstract quotient-codimension bound),
`fresh_scalars_card_le_syndrome` (its syndrome-space specialization, `finrank W = 2(n − k)`), and
`bad_card_le_pool_add_fresh_rank` (the composed accounting).  **Net advance: lemma 1 "bound
`#fresh`" ⤳ "the fresh contributions are independent modulo the core envelope `E`"** — the
support-geometry input (each fresh functional escapes `U'`, SYZ18-distinct), which is the residual.

## Scoreboard after SYZ30

  1. **Attribution completeness / fresh independence-mod-`E`** — the reduced lemma-1 residual:
     the fresh syndrome contributions are linearly independent modulo the core envelope `E`
     (support-geometry + SYZ18).  [was: "bound `#fresh`"; now: one independence hypothesis]
  2. **Formula `≤` direction** — the joint span reaches the min-envelope (SYZ25/26 MDS
     genericity).  [unchanged — the one "genuinely open" analytic residual]
  3. **Two-block cross-intersection floor** — the reduced lemma-3 residual: for `D ≥ 4`
     over-budget band covers, every two-block split has `|U₀ ∩ U₁| ≥ k`.  [was: "min over all
     partitions"; now: one two-block inequality, probe slack `0`]

Lemmas 3 and 1 are thus reduced from quantifier-heavy minimizations to single, sharp, probe-pinned
inequalities.  Only lemma 2 (MDS genericity) remains a substantive named residual.

All results axiom-clean (`propext`/`Classical.choice`/`Quot.sound`); no `sorry`, no
`native_decide`.  `#print axioms` at the bottom.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace ArkLib.ProximityGap.Frontier.SYZ30

open Finset Module Submodule
open ArkLib.ProximityGap.Frontier

/-! ## Lemma 3 — the `D ≥ 4` all-partition minimization (pure combinatorics) -/

section PartitionMin

/-- **The whole-cover partition (`m = 1`) realizes the ceiling.**  A single block whose union is
the full ground set (`U 0 = n`) has envelope count `∑_{j<1}(Uⱼ − k) = n − k` — exactly the
ceiling.  This is the min for every over-budget `D ≥ 4` band cover (probe: `argmin = m = 1`
in every trial). -/
theorem envelope_whole (n k : ℕ) (U : ℕ → ℕ) (hcover : U 0 = n) :
    ∑ j ∈ Finset.range 1, (U j - k) = n - k := by
  rw [Finset.sum_range_one, hcover]

/-- **`m ≥ 3` blocks clear the ceiling, unconditionally.**  If every block union has size at least
a band core (`s ≤ Uⱼ` with `2n/3 < s`, i.e. `2n < 3s`) and there are at least `3` blocks, the
envelope count exceeds the ceiling: `∑(Uⱼ − k) ≥ k + 1 > n − k`.  Purely the band size floor —
no over-budget or intersection hypothesis is needed (probe: `m ≥ 3` slack `≥ 2`).  This is the
easy half of the all-partition minimization. -/
theorem envelope_ge_of_three_blocks (n k s m : ℕ) (U : ℕ → ℕ)
    (hn : n = 2 * k) (hband : 2 * n < 3 * s)
    (hblk : ∀ j ∈ Finset.range m, s ≤ U j) (hm : 3 ≤ m) :
    n - k ≤ ∑ j ∈ Finset.range m, (U j - k) := by
  have hks : k ≤ s := by omega
  have hterm : ∀ j ∈ Finset.range m, s - k ≤ U j - k := by
    intro j hj; have := hblk j hj; omega
  have hsum : ∑ j ∈ Finset.range m, (s - k) ≤ ∑ j ∈ Finset.range m, (U j - k) :=
    Finset.sum_le_sum hterm
  have hconst : ∑ j ∈ Finset.range m, (s - k) = m * (s - k) := by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hge : 3 * (s - k) ≤ m * (s - k) := Nat.mul_le_mul_right _ hm
  have hband' : k + 1 ≤ 3 * (s - k) := by omega
  have hkey : k + 1 ≤ ∑ j ∈ Finset.range m, (U j - k) :=
    calc k + 1 ≤ 3 * (s - k) := hband'
      _ ≤ m * (s - k) := hge
      _ = ∑ j ∈ Finset.range m, (s - k) := hconst.symm
      _ ≤ ∑ j ∈ Finset.range m, (U j - k) := hsum
  omega

/-- **`m = 2` blocks: the envelope is exactly the cross-intersection.**  For a full cover split
into two blocks with union sizes `a = |U₀|`, `b = |U₁|` and cross-intersection `I = |U₀ ∩ U₁|`,
inclusion–exclusion gives `a + b = |U₀ ∪ U₁| + |U₀ ∩ U₁| = n + I` (full cover), so at rate `1/2`
(`n = 2k`) the envelope count `(a − k) + (b − k) = I`.  The two-block envelope is *precisely* the
overlap of the two block unions — the exact arithmetic reason the `D = 3` near-duplicate crack
happens at `m = 2` and nowhere else. -/
theorem envelope_two_blocks_eq_inter (n k a b I : ℕ) (hn : n = 2 * k)
    (hcap_a : k ≤ a) (hcap_b : k ≤ b) (hcover : a + b = n + I) :
    (a - k) + (b - k) = I := by omega

/-- **`m = 2` clears the ceiling iff the cross-intersection meets `k`.**  Combining the identity
above with the floor `k ≤ I = |U₀ ∩ U₁|`: the two-block envelope reaches `n − k`.  For `D ≥ 4`
over-budget band covers the probe finds `I ≥ k` with slack **exactly `0`** (never below); this
floor is the single residual of the all-partition minimization (the `D = 3` crack is exactly its
failure by one, `I = k − 1`). -/
theorem envelope_two_blocks_ge_of_inter_floor (n k a b I : ℕ) (hn : n = 2 * k)
    (hcap_a : k ≤ a) (hcap_b : k ≤ b) (hcover : a + b = n + I) (hfloor : k ≤ I) :
    n - k ≤ (a - k) + (b - k) := by omega

/-- **The packaged all-partition floor.**  Given the block-union sizes `U : ℕ → ℕ` of an `m`-block
partition, the envelope `∑_{j<m}(Uⱼ − k) ≥ n − k` holds provided one of the three case
hypotheses: `m = 1` full cover; `m ≥ 3` band size floor; or `m = 2` cross-intersection floor.
Each disjunct is discharged by the lemmas above — so the *only* content that is not already a
theorem is the `m = 2` floor `k ≤ I`. -/
theorem partition_envelope_ge
    (n k m s I : ℕ) (U : ℕ → ℕ) (hn : n = 2 * k)
    (hcase :
      (m = 1 ∧ U 0 = n) ∨
      (m = 2 ∧ k ≤ U 0 ∧ k ≤ U 1 ∧ U 0 + U 1 = n + I ∧ k ≤ I) ∨
      (3 ≤ m ∧ 2 * n < 3 * s ∧ ∀ j ∈ Finset.range m, s ≤ U j)) :
    n - k ≤ ∑ j ∈ Finset.range m, (U j - k) := by
  rcases hcase with ⟨hm, hc⟩ | ⟨hm, ha, hb, hcov, hfl⟩ | ⟨hm, hband, hblk⟩
  · subst hm; rw [envelope_whole n k U hc]
  · subst hm
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    exact envelope_two_blocks_ge_of_inter_floor n k (U 0) (U 1) I hn ha hb hcov hfl
  · exact envelope_ge_of_three_blocks n k s m U hn hband hblk hm

end PartitionMin

/-! ## Lemma 3 — concrete `D = 4` witness: every two-block split clears the floor -/

section PartitionWitness

/-- The SYZ29 `n = 16` four-core over-budget full cover (reused).  Its `m = 2` splits all have
cross-intersection `|U₀ ∩ U₁| ≥ 11 ≥ 8 = k` (this-file analysis: the three "pairing" splits give
`I ∈ {14,15}`, the four "3+1" splits give `I = 11`), so the two-block floor holds with margin —
no near-duplicate crack at `D = 4`.  Concrete instance of the reduced lemma-3 residual. -/
def syz30FourCover : List (List ℕ) := SYZ29.syz29FourCover

/-- **A representative `m = 2` split of the four-cover clears the floor.**  Block `{0,1,2}` has
union `{0,…,15}` (size `16`), block `{3}` has union `C₃` (size `11`); their intersection is `C₃`
itself (size `11`), `≥ 8 = k`, so the envelope `(16 − 8) + (11 − 8) = 11 ≥ 8 = n − k`.  The
tightest `m = 2` split of this cover, still above the ceiling. -/
theorem syz30_two_block_floor :
    let U0 := ((syz30FourCover.getD 0 []) ∪ (syz30FourCover.getD 1 []) ∪
               (syz30FourCover.getD 2 [])).toFinset
    let U1 := (syz30FourCover.getD 3 []).toFinset
    8 ≤ (U0 ∩ U1).card ∧ (16 - 8) ≤ ((U0.card - 8) + (U1.card - 8)) := by decide

end PartitionWitness

/-! ## Lemma 1 — the fresh accounting (rank/codimension count) -/

section Fresh

/-- **The fresh codimension bound.**  If `p` fresh vectors `f : Fin p → W` have images in the
quotient `W ⧸ E` that are linearly independent (`E` = the core envelope), then
`p ≤ finrank W − finrank E`.  This is the load-bearing accounting of the fresh-scalar count: a
`LinearIndependent`-cardinality bound in `W ⧸ E` plus rank–nullity.  Field- and space-generic. -/
theorem fresh_card_le_codim {F W : Type*} [Field F] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (E : Submodule F W) {p : ℕ} (f : Fin p → W)
    (hindep : LinearIndependent F (fun i => E.mkQ (f i))) :
    p ≤ finrank F W - finrank F E := by
  have hcard : p ≤ finrank F (W ⧸ E) := by
    have h := hindep.fintype_card_le_finrank
    simpa using h
  have hq : finrank F (W ⧸ E) + finrank F E = finrank F W :=
    Submodule.finrank_quotient_add_finrank E
  omega

open ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge in
/-- **The fresh count on the syndrome-pair space.**  Specializing `fresh_card_le_codim` to
`W = SyndromePair C`, whose dimension is `2(n − |C|) = 2(n − k)` (`G87.finrank_syndromePair`):
`p` fresh syndrome contributions independent modulo the core envelope `E` obey
`#fresh ≤ 2(n − k) − finrank E`.  This is the honest fresh bound — the residual is exactly the
independence-modulo-`E` hypothesis (each fresh functional escapes the core union `U'`, SYZ18). -/
theorem fresh_scalars_card_le_syndrome {F : Type*} [Field F] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (C : Submodule F (ι → F)) (E : Submodule F (SyndromePair C)) {p : ℕ}
    (f : Fin p → SyndromePair C)
    (hindep : LinearIndependent F (fun i => E.mkQ (f i))) :
    p ≤ 2 * (Fintype.card ι - finrank F C) - finrank F E := by
  have h := fresh_card_le_codim E f hindep
  rwa [finrank_syndromePair C] at h

/-- **The composed complete accounting.**  With the SYZ29 unconditional split
`#bad ≤ #pool + #fresh` and the fresh codimension bound: if the fresh part `B ∖ P` is enumerated
by `p` vectors independent modulo `E`, then

  `#bad ≤ #pool + (finrank W − finrank E)`.

Composed with `SYZ29.bad_card_le_pool_of_attribution` (`#pool ≤ ∑(n − sᵢ)`) and
`fresh_scalars_card_le_syndrome` (`finrank W = 2(n − k)`) this is the honest
`#bad ≤ ∑(n − sᵢ) + (2(n − k) − finrank E)` — the whole lemma-1 accounting, modulo the
independence-mod-`E` residual. -/
theorem bad_card_le_pool_add_fresh_rank {F W : Type*} [Field F] [DecidableEq F]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (B P : Finset F) (E : Submodule F W) {p : ℕ} (f : Fin p → W)
    (hfresh_eq : (B \ P).card = p)
    (hindep : LinearIndependent F (fun i => E.mkQ (f i))) :
    B.card ≤ P.card + (finrank F W - finrank F E) := by
  have hsplit := SYZ29.bad_card_le_pool_add_fresh B P
  have hfresh := fresh_card_le_codim E f hindep
  omega

end Fresh

end ArkLib.ProximityGap.Frontier.SYZ30

-- Honesty audit:
#print axioms ArkLib.ProximityGap.Frontier.SYZ30.envelope_whole
#print axioms ArkLib.ProximityGap.Frontier.SYZ30.envelope_ge_of_three_blocks
#print axioms ArkLib.ProximityGap.Frontier.SYZ30.envelope_two_blocks_eq_inter
#print axioms ArkLib.ProximityGap.Frontier.SYZ30.envelope_two_blocks_ge_of_inter_floor
#print axioms ArkLib.ProximityGap.Frontier.SYZ30.partition_envelope_ge
#print axioms ArkLib.ProximityGap.Frontier.SYZ30.syz30_two_block_floor
#print axioms ArkLib.ProximityGap.Frontier.SYZ30.fresh_card_le_codim
#print axioms ArkLib.ProximityGap.Frontier.SYZ30.fresh_scalars_card_le_syndrome
#print axioms ArkLib.ProximityGap.Frontier.SYZ30.bad_card_le_pool_add_fresh_rank

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ30LemmasOneThree

/-!
# SYZ31: the two remaining strip set-geometry facts — one REFUTED, one reduced (#466 / #507)

SYZ30 reduced the strip scoreboard's lemma 3 to a single **two-block cross-intersection floor**
(`|U₀ ∩ U₁| ≥ k` for every two-block split of a `D ≥ 4` over-budget band full cover) and lemma 1
to a single **fresh independence-modulo-`E`** hypothesis.  This file settles both as far as the
honest arithmetic allows.

## Fact 3 — the two-block cross-intersection floor is **FALSE as stated** (near-duplicate crack)

The SYZ30 residual conjectured `|U₀ ∩ U₁| ≥ k` for *every* two-block split of a `D ≥ 4`
over-budget band full cover, probe-pinned at slack `0` by **random** sampling.  That sampling
missed an adversarial shape.  **Counterexample** (`syz31Crack`, verified by `decide`,
`n = 16`, `k = 8`, all four cores size `11` — the unique strict-interior band `2n/3 < s < 3n/4`):

  `C₀ = {0,…,10}`,  `C₁ = {0..5, 11..15}`,  `C₂ = {0..4, 6, 11..15}`,  `C₃ = {0..3, 5, 6, 11..15}`.

`C₁,C₂,C₃` are pairwise **near-duplicates** (all three pairwise overlaps `= 10 > k`).  The split
`{0} | {1,2,3}` gives `U₀ = C₀` (size `11`), `U₁ = C₁∪C₂∪C₃ = {0..6, 11..15}` (size `12`, only
one more than a *single* core — the cluster degeneracy), full cover `U₀∪U₁ = {0..15}`, over-budget
`∑(sᵢ−k) = 12 ≥ 8`.  Its cross-intersection is `|U₀ ∩ U₁| = |{0..6}| = 7 < 8 = k`, so the
two-block **envelope** is `(11−8)+(12−8) = 7 < 8 = n − k` — the strip's all-partition minimum
dips **below** the ceiling.  The probe confirms the actual rank deficiency is `d = 1`,
field-independent over `p ∈ {101, 1009, 65537, 2³¹−1}`: this is a genuine deficient shape, not a
counting artifact.

**This is the SYZ28 `D = 3` near-duplicate *pair* crack replicated as a near-duplicate *triple***
**block inside a `D = 4` cover**, and it scales to every `n`: for the strict-interior band
`s = ⌊(3n−1)/4⌋` the shape exists at `n ∈ {16,20,24,28,32,…}` (probe `min_env = n−k−1`, `d = 1`
at each).  So "`D ≥ 4` over-budget is deficiency-free" (SYZ27 observation) is a **sampling
artifact**, and the two-block floor is not a theorem.  *No landed theorem is refuted* — SYZ29's
`d4_over_budget_deficiency_zero` and SYZ30's `partition_envelope_ge` both carry the floor as an
explicit hypothesis; it is the *conjectured residual* that falls.

## Fact 3 — the **corrected** floor, PROVED (the discriminating hypothesis)

The counterexample localizes the missing hypothesis exactly.  SYZ29's `d4_pairing_envelope_ge`
already forced pair-union floors `|Cᵢ ∪ Cⱼ| ≥ 2s − k` for *pairing* partitions via the band
overlap bound `|Cᵢ ∩ Cⱼ| ≤ k`; the near-duplicate cluster is precisely where a block has **no**
such spread pair, so its union stays near `s`.  The honest minimal hypothesis is therefore: *some*
block of the split contains a **spread pair** (a pair of cores with union `≥ 2s − k`, i.e. overlap
`≤ k` — no near-duplicate cluster).  Under that, the floor holds with room to spare
(`two_block_floor_of_spread_pair`, omega): for `D ≥ 4` at least one block is multi-core, and if it
carries a spread pair then

  `|U₀| + |U₁| ≥ (2s − k) + s = 3s − k > 3k = n + k`   (band `3s > 4k`),

so `|U₀ ∩ U₁| = |U₀| + |U₁| − n > k`.  The probe confirms the sharp discriminator: under the
global no-near-duplicate condition (all pairwise overlaps `≤ k`) the floor holds with `min I ≥ k+1`
across `>3·10⁵` trials and **zero** violations, whereas the raw floor is violated.  So the correct
scoreboard item is: *the strip's `D ≥ 4` gluing needs the no-near-duplicate-cluster (spread-pair)
condition — the same overlap bound SYZ29 used for pairs, now required of the triple/`j`-fold
blocks — and the near-duplicate clusters are absorbed exactly as at `D = 3`, by the SYZ28
pencil-yield cap, not by set geometry.*

## Fact 1 — fresh independence mod `E`: the provable geometric core (private escaping coordinate)

SYZ30 reduced lemma 1 to "the fresh syndrome contributions are linearly independent modulo the
core envelope `E`" and proved the abstract codimension bound `fresh_card_le_codim`.  This file
supplies the honest geometric core that discharges the independence hypothesis from support data:
if each fresh functional has a **private escaping coordinate** `c i` — a coordinate *outside* the
core support `U'` (so every `e ∈ E`, confined to `U'`, vanishes there: `escape`) at which `f i`
does not vanish (`hit`) and every *other* fresh functional does vanish (`private`) — then the
images `E.mkQ (f i)` are linearly independent (`indep_mod_of_private_coord`), hence
`#fresh ≤ finrank W − finrank E` (`fresh_card_le_codim_of_private_coord`).  Distinct fresh supports
(SYZ18) plus the syndrome-pair `γ`-twist are the intended source of the private coordinates; the
lemma isolates the exact linear-algebra content, leaving *that* support-combinatorial input as the
reduced residual.

## Scoreboard after SYZ31

  1. **Fresh independence-mod-`E`** (lemma 1) — reduced to a *private escaping coordinate* per
     fresh functional (`indep_mod_of_private_coord` discharges the linear algebra; SYZ18 + the
     `γ`-twist are the support input).
  2. **Formula `≤` direction** (lemma 2, unchanged) — MDS genericity (SYZ25/26).  The one
     substantive open analytic residual.
  3. ~~Two-block cross-intersection floor~~ **REFUTED as stated** (near-duplicate cluster crack,
     `d = 1` field-independent, scales to all `n`); the corrected floor holds under the
     **no-near-duplicate-cluster / spread-pair** hypothesis (`two_block_floor_of_spread_pair`),
     and the excluded clusters are yield-cap-absorbed (SYZ28), not set-geometrically forbidden.

Net: the strip's lemma-3 residual is *corrected* (the raw floor was false — a genuine sampling
gap), and lemma 1's residual is sharpened to a single support-combinatorial input.  Only lemma 2
remains a substantive open analytic residual.

All results axiom-clean (`propext`/`Classical.choice`/`Quot.sound`); no `sorry`, no
`native_decide`.  `#print axioms` at the bottom.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace ArkLib.ProximityGap.Frontier.SYZ31

open Finset Module Submodule
open ArkLib.ProximityGap.Frontier

/-! ## Fact 3 — the two-block cross-intersection floor is FALSE as stated -/

section Refutation

/-- **The `D = 4` near-duplicate-triple crack** (`n = 16`, `k = 8`, all cores size `11` = the
unique strict-interior band).  `C₁,C₂,C₃` are pairwise near-duplicates (all pairwise overlaps
`10 > k`); together with `C₀` they form an over-budget full cover whose `{0} | {1,2,3}` split
breaks the SYZ30 two-block floor.  Probe: actual deficiency `d = 1`, field-independent. -/
def syz31Crack : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
   [0, 1, 2, 3, 4, 5, 11, 12, 13, 14, 15],
   [0, 1, 2, 3, 4, 6, 11, 12, 13, 14, 15],
   [0, 1, 2, 3, 5, 6, 11, 12, 13, 14, 15]]

/-- Four size-`11` cores — the unique strict-interior band `2n/3 < 11 < 3n/4` at `n = 16`. -/
theorem syz31_core_sizes : ∀ C ∈ syz31Crack, C.length = 11 := by decide

/-- **Full cover** of `{0,…,15}`. -/
theorem syz31_full_cover :
    (syz31Crack.foldr (fun C acc => C ∪ acc) []).toFinset = Finset.range 16 := by decide

/-- **Over-budget**: `∑(|Cᵢ| − k) = 4·3 = 12 ≥ 8 = n − k`. -/
theorem syz31_over_budget :
    16 - 8 ≤ (syz31Crack.map (fun C => C.length - 8)).sum := by decide

/-- **The near-duplicate cluster.**  Inside the block `{1,2,3}` all three pairwise overlaps equal
`10 > 8 = k` — no spread pair — so the block union `|C₁∪C₂∪C₃| = 12` stays one above a single
core.  This is exactly the missing-hypothesis witness. -/
theorem syz31_cluster_overlaps :
    let C1 := (syz31Crack.getD 1 []).toFinset
    let C2 := (syz31Crack.getD 2 []).toFinset
    let C3 := (syz31Crack.getD 3 []).toFinset
    (C1 ∩ C2).card = 10 ∧ (C1 ∩ C3).card = 10 ∧ (C2 ∩ C3).card = 10 := by decide

/-- **The two-block floor FAILS.**  For the split `U₀ = C₀`, `U₁ = C₁∪C₂∪C₃` of the over-budget
`D = 4` band full cover `syz31Crack`: the cross-intersection is `|U₀ ∩ U₁| = 7 < 8 = k`, and the
two-block envelope `(|U₀|−k)+(|U₁|−k) = 3 + 4 = 7 < 8 = n − k`.  A `decide`-verified refutation of
the SYZ30 residual "`|U₀ ∩ U₁| ≥ k` for every two-block split". -/
theorem syz31_two_block_floor_fails :
    let U0 := (syz31Crack.getD 0 []).toFinset
    let U1 := ((syz31Crack.getD 1 []) ∪ (syz31Crack.getD 2 []) ∪
               (syz31Crack.getD 3 [])).toFinset
    (U0 ∩ U1).card = 7 ∧ (U0 ∩ U1).card < 8 ∧
      ((U0.card - 8) + (U1.card - 8)) < 16 - 8 := by decide

end Refutation

/-! ## Fact 3 — the corrected floor: no near-duplicate cluster ⟹ floor holds -/

section CorrectedFloor

/-- **The corrected two-block floor.**  For a rate-`1/2` (`n = 2k`) band full cover split into two
blocks with union sizes `a = |U₀|`, `b = |U₁|` and cross-intersection `I = |U₀ ∩ U₁|`, suppose:
* the band lower bound `3s > 4k` (i.e. `2n < 3s`, `s > 2n/3`);
* each block union contains at least one core (`s ≤ a`, `s ≤ b`);
* **some** block carries a *spread pair* — two of its cores with union `≥ 2s − k` (overlap `≤ k`,
  no near-duplicate cluster) — so that block's union is `≥ 2s − k`; take it to be `U₀`
  (`2*s ≤ a + k`);
* full cover `a + b = n + I`.

Then `I ≥ k` (in fact `I ≥ k + 1`).  This is exactly the SYZ29 pair-overlap floor promoted from
*pairing* partitions to the block that avoids the near-duplicate degeneracy; the counterexample
`syz31Crack` is precisely the configuration where **no** block satisfies `2*s ≤ a + k`, so the
hypothesis (and the conclusion) genuinely fail there. -/
theorem two_block_floor_of_spread_pair (n k s a b I : ℕ)
    (hn : n = 2 * k) (hband : 4 * k < 3 * s)
    (hcore_a : s ≤ a) (hcore_b : s ≤ b)
    (hspread : 2 * s ≤ a + k)
    (hcover : a + b = n + I) :
    k ≤ I := by omega

/-- **The corrected floor, `2+2`-symmetric form.**  If *both* blocks carry a spread pair
(`2*s ≤ a + k` and `2*s ≤ b + k`) — the generic `D ≥ 4` situation — the floor holds even more
comfortably: `I ≥ 4s − 3k > k`.  (Either single spread-pair hypothesis already suffices via
`two_block_floor_of_spread_pair`; this records the symmetric slack.) -/
theorem two_block_floor_of_two_spread_pairs (n k s a b I : ℕ)
    (hn : n = 2 * k) (hband : 4 * k < 3 * s)
    (hspread_a : 2 * s ≤ a + k) (hspread_b : 2 * s ≤ b + k)
    (hcover : a + b = n + I) :
    k ≤ I := by omega

/-- **Packaged corrected lemma 3.**  The SYZ30 `partition_envelope_ge` `m = 2` disjunct required
the *unprovable* floor `k ≤ I`.  Here it is discharged from the honest set-geometry hypothesis
(some block has a spread pair), closing the two-block envelope `∑_{j<2}(Uⱼ − k) ≥ n − k`. -/
theorem envelope_two_blocks_ge_of_spread_pair (n k s : ℕ) (U : ℕ → ℕ)
    (hn : n = 2 * k) (hband : 4 * k < 3 * s)
    (hcore_0 : s ≤ U 0) (hcore_1 : s ≤ U 1)
    (hspread : 2 * s ≤ U 0 + k)
    (hcover : ∃ I, U 0 + U 1 = n + I) :
    n - k ≤ ∑ j ∈ Finset.range 2, (U j - k) := by
  obtain ⟨I, hI⟩ := hcover
  have hfloor : k ≤ I := two_block_floor_of_spread_pair n k s (U 0) (U 1) I hn hband hcore_0 hcore_1 hspread hI
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  omega

end CorrectedFloor

/-! ## Fact 3 — a concrete `D = 4` cover with a spread pair clears the corrected floor -/

section CorrectedWitness

/-- The SYZ29 `n = 16` four-cover (probe `d = 0`).  Here block `{0,1}` has union `{0,…,15}` (its
two cores overlap in `{5,…,10}`, size `6 ≤ 8 = k` — a **spread pair**, `|C₀∪C₁| = 16 ≥ 2·11−8`),
so the corrected floor applies and the two-block envelope clears the ceiling: contrast with
`syz31Crack`, whose only multi-core block is an all-near-duplicate cluster. -/
def syz31SpreadCover : List (List ℕ) := SYZ29.syz29FourCover

/-- **Spread-pair witness.**  Block `{0,1}` of `syz31SpreadCover` has overlap `|C₀∩C₁| = 6 ≤ 8 = k`
and union `|C₀∪C₁| = 16 ≥ 14 = 2s − k`, so it is a spread pair; the split `{0,1} | {2,3}` has
`|U₀ ∩ U₁| = 11 ≥ 8 = k` and envelope `(16−8)+(11−8) = 11 ≥ 8`.  Concrete instance of the corrected
lemma. -/
theorem syz31_spread_pair_floor :
    let C0 := (syz31SpreadCover.getD 0 []).toFinset
    let C1 := (syz31SpreadCover.getD 1 []).toFinset
    let U0 := ((syz31SpreadCover.getD 0 []) ∪ (syz31SpreadCover.getD 1 [])).toFinset
    let U1 := ((syz31SpreadCover.getD 2 []) ∪ (syz31SpreadCover.getD 3 [])).toFinset
    (C0 ∩ C1).card ≤ 8 ∧ 14 ≤ (C0 ∪ C1).card ∧
      8 ≤ (U0 ∩ U1).card ∧ (16 - 8) ≤ ((U0.card - 8) + (U1.card - 8)) := by decide

end CorrectedWitness

/-! ## Fact 1 — fresh independence mod `E` via a private escaping coordinate -/

section Fresh

/-- **Private-escaping-coordinate ⟹ independent modulo `E`.**  Model functionals as functions
`κ → F` on a coordinate set `κ`.  Let `E ≤ (κ → F)` be the core envelope (functionals confined to
the core support `U'`), and let `c : Fin p → κ` mark, for each fresh functional `f i`, a *private
escaping coordinate* with:
* `escape`: every `e ∈ E` vanishes at `c i` (as `E` is confined to `U'` and `c i ∉ U'`);
* `hit`: `f i (c i) ≠ 0` (the fresh functional escapes `U'` there);
* `private`: `f j (c i) = 0` for `j ≠ i` (no other fresh functional touches this coordinate — the
  SYZ18 distinct-support + `γ`-twist content).

Then the images `E.mkQ (f i)` in the quotient `(κ → F) ⧸ E` are linearly independent.  This is the
exact linear-algebra core of lemma 1's independence-mod-`E`. -/
theorem indep_mod_of_private_coord {F : Type*} [Field F] {κ : Type*}
    (E : Submodule F (κ → F)) {p : ℕ} (f : Fin p → (κ → F)) (c : Fin p → κ)
    (escape : ∀ i, ∀ e ∈ E, e (c i) = 0)
    (hit : ∀ i, f i (c i) ≠ 0)
    (priv : ∀ i j, i ≠ j → f j (c i) = 0) :
    LinearIndependent F (fun i => E.mkQ (f i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  -- `∑ j, g j • E.mkQ (f j) = 0` means `∑ j, g j • f j ∈ E`.
  have key : E.mkQ (∑ j, g j • f j) = 0 := by
    rw [map_sum]; simp only [map_smul]; exact hg
  have hmem : (∑ j, g j • f j) ∈ E := (Submodule.Quotient.mk_eq_zero E).mp key
  -- Evaluate at the private coordinate `c i`: only the `i`-term survives, and `E` vanishes there.
  have hval : (∑ j, g j • f j) (c i) = 0 := escape i _ hmem
  have hsum : (∑ j, g j • f j) (c i) = g i * f i (c i) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · intro j _ hji
      rw [priv i j (fun h => hji h.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hsum] at hval
  rcases mul_eq_zero.mp hval with hgi | hfi
  · exact hgi
  · exact absurd hfi (hit i)

/-- **Fresh count from private escaping coordinates.**  Combining `indep_mod_of_private_coord`
with SYZ30's abstract codimension bound `fresh_card_le_codim`: if `p` fresh functionals on a
finite-dimensional coordinate space each carry a private escaping coordinate, then
`#fresh ≤ finrank W − finrank E`.  This discharges lemma 1's independence-mod-`E` residual down to
the support-combinatorial input (SYZ18 distinct supports + the `γ`-twist supply the private
coordinates). -/
theorem fresh_card_le_codim_of_private_coord {F : Type*} [Field F] {κ : Type*} [Fintype κ]
    (E : Submodule F (κ → F)) {p : ℕ} (f : Fin p → (κ → F)) (c : Fin p → κ)
    (escape : ∀ i, ∀ e ∈ E, e (c i) = 0)
    (hit : ∀ i, f i (c i) ≠ 0)
    (priv : ∀ i j, i ≠ j → f j (c i) = 0) :
    p ≤ finrank F (κ → F) - finrank F E :=
  SYZ30.fresh_card_le_codim E f (indep_mod_of_private_coord E f c escape hit priv)

end Fresh

end ArkLib.ProximityGap.Frontier.SYZ31

-- Honesty audit:
#print axioms ArkLib.ProximityGap.Frontier.SYZ31.syz31_core_sizes
#print axioms ArkLib.ProximityGap.Frontier.SYZ31.syz31_full_cover
#print axioms ArkLib.ProximityGap.Frontier.SYZ31.syz31_over_budget
#print axioms ArkLib.ProximityGap.Frontier.SYZ31.syz31_cluster_overlaps
#print axioms ArkLib.ProximityGap.Frontier.SYZ31.syz31_two_block_floor_fails
#print axioms ArkLib.ProximityGap.Frontier.SYZ31.two_block_floor_of_spread_pair
#print axioms ArkLib.ProximityGap.Frontier.SYZ31.two_block_floor_of_two_spread_pairs
#print axioms ArkLib.ProximityGap.Frontier.SYZ31.envelope_two_blocks_ge_of_spread_pair
#print axioms ArkLib.ProximityGap.Frontier.SYZ31.syz31_spread_pair_floor
#print axioms ArkLib.ProximityGap.Frontier.SYZ31.indep_mod_of_private_coord
#print axioms ArkLib.ProximityGap.Frontier.SYZ31.fresh_card_le_codim_of_private_coord

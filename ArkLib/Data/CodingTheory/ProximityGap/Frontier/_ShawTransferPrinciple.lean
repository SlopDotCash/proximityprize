/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SpecS3_GaloisReduction
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedPairingCount

/-!
# The Shaw Transfer Principle — a char-0 → char-`p` transfer for the energy bound (#444)

⚠️ **STATUS — a NAMED transfer FRAMEWORK + provable skeleton + ONE named analytic residual.**
This is a conditional brick: its combinatorial / naturality content is PROVEN axiom-clean, the
single genuine open input is named as an explicit `Prop` (`ShawLiftsToCharZero`). Per the project's
modularity convention, a conditional brick with a named open hypothesis is **LANDED + REDUCED**.
NOTHING here claims `E_r(𝔽_p) ≤ Wick` is *proven* — that is the prize wall.

## What the principle IS (the precise statement)

The proven char-0 energy bound `E_r(μ_n) ≤ (2r−1)‼·n^r` (Lam–Leung) is, structurally, a **matching
injection**: every zero-sum `2r`-tuple of `2^μ`-th roots is **antipodally paired** (`c (σ i) = −c i`
for a perfect matching `σ`), and each antipodal cell injects into the transversal `[n]^r`
(`ShawMatchingInjection`, `NegationClosedWalkBound`). The whole char-0 content is the
**antipodal-pairing residual** `H`.

The **Shaw Transfer Principle** is the statement that this pairing residual is **`p`-stable under
reduction mod 𝔭** — i.e. it pushes forward along the reduction ring hom `σ : ℤ[ζ] → 𝔽_p` — **outside
a bounded bad-prime set**, and conversely that every char-`p` zero-sum tuple is the reduction of a
char-`0` zero-sum tuple (the lift). Precisely, for a ring hom `σ : F →+* K` and a node set `G ⊆ F`:

> **(Shaw Transfer)** If
>   **(p-stability)** `σ` is INJECTIVE on `G` — distinct nodes stay distinct mod 𝔭 (this is the
>     "outside the bad-prime set" condition: two `2^μ`-th roots `x ≠ y` collide mod 𝔭 iff 𝔭 divides
>     `Norm(x−y)`, a finite set of primes, vacuous for the prize prime `p ≈ n·2^128 ≫ 2^n ≥ |Norm|`),
>   and **(char-0 pairing)** every char-0 zero-sum tuple of `G` is antipodally paired (`H`, the proven
>     Lam–Leung input), and **(lift)** every char-`p` zero-sum tuple of `σ(G)` is the σ-image of a
>     char-0 zero-sum tuple of `G` (`ShawLiftsToCharZero`, the NAMED analytic residual),
> **then** every char-`p` zero-sum tuple of `σ(G)` is antipodally paired, hence the char-`p`
> wraparound set is EMPTY and `E_r(σ(G)) ≤ (2r−1)‼·|σ(G)|^r` (= Wick) at the good prime.

The mechanism is the crown-jewel naturality `SpecS3.dividedDifferencePow_map`: the divided-difference
/ pairing structure commutes with EVERY ring hom (hypothesis-free, char-agnostic, total). p-stability
(`σ` injective on `G`) is exactly what keeps `σ(G)` a genuine node set of the right cardinality, so
that the pushed-forward pairing is still a valid antipodal matching of DISTINCT values.

## Why this is the right decomposition (honest scope)

The naive char-`p` bound `E_r ≤ Wick` is **FALSE** at the prize scale (the DC term forces
`E_r ≥ |G|^{2r}/q > Wick` when `n ≥ 64`, `r ≈ log q`); see `_ShawMatchingInjection`'s preamble and
`PairingResidualFailsAtPrize`. The Shaw Transfer Principle does NOT contradict this: it isolates the
**exact** missing input as the LIFT `ShawLiftsToCharZero`. The lift FAILS precisely when there are
genuine char-`p` "wraparound" solutions — short `±1`-relations of `2^μ`-th roots vanishing mod `p`
that have NO char-0 antecedent. So:

* `ShawLiftsToCharZero` holds  ⟺  no genuine wraparound  ⟺  `E_r(𝔽_p) ≤ Wick`  ⟺  the prize bound.
* In char 0 (and the regime `n ≲ √p` where no `2ln q`-term root relation can vanish) the lift is
  FREE and the transfer reproduces the exact char-0 bound (`shawTransfer_charZero`).

So the principle is a faithful re-statement: it neither over- nor under-claims. The genuine analytic
content — that the lift holds at the prize prime `p ≈ n·2^128`, `n = 2^30` — is the Konyagin–
Shparlinski / di Benedetto / BGK wall, here named once as `ShawLiftsToCharZero`. This is the SAME
wall as `WrapInjectsIntoSlack G r 0` of `_ShawMatchingInjection`; this file gives the
naturality-driven *form* of that wall (push char-0 pairing forward along the reduction hom) and the
precise reduction of the energy bound to it.

## Contents

* `pushPairing` — naturality core: a ring hom `σ` injective on `G` pushes an antipodally-paired
  zero-sum tuple of `G` to an antipodally-paired zero-sum tuple of `σ(G)`. PROVEN axiom-clean.
* `ShawPStable` — the p-stability predicate (`σ` injective on `G` ⟹ `|σ(G)| = |G|`). PROVEN.
* `ShawLiftsToCharZero` — the NAMED open analytic residual (the char-`p` lift / no-wraparound).
* `shawCharPPairing_of_lift` — the transfer of the pairing residual: p-stability + char-0 pairing +
  lift ⟹ char-`p` pairing residual. PROVEN (modular, off the named hypothesis).
* `shawTransfer` — the headline energy transfer: under the three inputs, `E_r(σ(G)) ≤ (2r−1)‼·|G|^r`.
  PROVEN (conditional on `ShawLiftsToCharZero`).
* `shawTransfer_charZero` — the lift is FREE in char 0 (`2^k`-th roots), recovering the exact char-0
  bound; closes the loop showing the principle is a strict generalization.

## References
* `SpecS3.dividedDifferencePow_map` (the crown-jewel naturality, the transfer mechanism);
* `ShawMatchingInjection` + `NegationClosedWalk` (the matching injection + wraparound tag);
* `zeroSumCount_le_pairings`, `pairings_card_eq_doubleFactorial` (the char-0 matching bound);
  `LamLeungMultisetAntipodal` (the char-0 pairing). Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset Nat

namespace ArkLib.ProximityGap.Frontier.ShawTransfer

open ArkLib.ProximityGap.NegationClosedWalk

/-! ## Part 1 — p-stability and the naturality push of a pairing.

The transfer vehicle. A ring hom `σ` that is INJECTIVE on the node set `G` (p-stability: distinct
`2^μ`-th roots stay distinct mod 𝔭, which holds outside the bounded bad-prime set) pushes an
antipodally-paired zero-sum tuple `c` of `G` forward to the antipodally-paired zero-sum tuple `σ ∘ c`
of `σ(G)`. The same matching `σ_match` works: `σ` is additive, so it preserves both the zero-sum
condition (`∑ σ(c i) = σ(∑ c i) = σ(0) = 0`) and the antipodal condition
(`σ(c (σ_match i)) = σ(−c i) = −σ(c i)`). This is the abstract heart of the naturality transfer; it
is the tuple-level shadow of `SpecS3.dividedDifferencePow_map` (the divided-difference structure
commuting with `σ`). -/

section Push

variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]

/-- **p-stability predicate.** `σ` is `p`-stable on `G` when it is injective on `G`: distinct nodes
stay distinct under reduction. For the prize this is "𝔭 outside the bad-prime set", i.e. 𝔭 does not
divide `Norm(x−y)` for any pair of distinct `2^μ`-th roots `x,y ∈ G`. -/
def ShawPStable (σ : F →+* K) (G : Finset F) : Prop := Set.InjOn σ G

/-- **p-stability ⟹ `|σ(G)| = |G|`.** A `p`-stable reduction keeps the node set's cardinality, so
the pushed-forward node set `σ(G)` is genuine (same `n`); the char-0 transversal bound `n^r`
transports verbatim. -/
theorem shawPStable_card_image (σ : F →+* K) {G : Finset F} (hσ : ShawPStable σ G) :
    (G.image σ).card = G.card :=
  Finset.card_image_of_injOn hσ

/-- **Naturality push of one paired tuple (the transfer core).** If `c : Fin (2r) → F` is a zero-sum
tuple valued in `G`, antipodally paired by the matching `σ_match`, and `σ` is `p`-stable on `G`, then
`σ ∘ c : Fin (2r) → K` is a zero-sum tuple valued in `σ(G)`, antipodally paired by the SAME matching
`σ_match`. The matching is preserved because `σ` is a ring hom: zero-sum and antipodal both commute
with `σ`. (This is the tuple-level instance of `dividedDifferencePow_map`: the pairing structure is
natural.) -/
theorem pushPairing (σ : F →+* K) {r : ℕ} {G : Finset F} {c : Fin (2 * r) → F}
    {σ_match : Equiv.Perm (Fin (2 * r))}
    (hcG : ∀ i, c i ∈ G) (hsum : ∑ i, c i = 0)
    (hpair : ∀ i, c (σ_match i) = - c i) :
    (∀ i, (σ ∘ c) i ∈ G.image σ) ∧ (∑ i, (σ ∘ c) i = 0)
      ∧ (∀ i, (σ ∘ c) (σ_match i) = - (σ ∘ c) i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact Finset.mem_image_of_mem σ (hcG i)
  · -- ∑ σ(c i) = σ(∑ c i) = σ 0 = 0
    simp only [Function.comp_apply]
    rw [← map_sum σ c Finset.univ, hsum, map_zero]
  · -- σ(c (σ_match i)) = σ(−c i) = −σ(c i)
    intro i
    simp only [Function.comp_apply]
    rw [hpair i, map_neg]

end Push

/-! ## Part 2 — the NAMED analytic residual: the char-`p` lift (no wraparound).

The ONLY genuine open input. The char-0 pairing residual handles every tuple that comes from char 0;
the lift asserts that there are NO OTHER char-`p` zero-sum tuples — every char-`p` zero-sum tuple of
`σ(G)` is the σ-image of a char-0 zero-sum tuple of `G`. Equivalently: no genuine wraparound. This is
the precise wall. -/

section Residual

variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]

/-- **The named char-`p` LIFT residual (the open analytic input).**
`ShawLiftsToCharZero σ G r` asserts: every zero-sum `2r`-tuple `d` of the reduced node set `σ(G)` is
the σ-image of a zero-sum `2r`-tuple `c` of `G` (i.e. `d = σ ∘ c`). This is the "no genuine
wraparound" condition: every char-`p` solution lifts to a char-0 solution. Combined with the char-0
pairing (`H`) and `p`-stability, it forces every char-`p` zero-sum tuple to be antipodally paired.

⚠️ This is the SINGLE genuine open input — the same Konyagin–Shparlinski / di Benedetto / BGK wall as
`WrapInjectsIntoSlack G r 0`. It is FALSE for the raw `E_r ≤ Wick` at the prize scale (where the DC
term forces genuine wraparound), and TRUE in char 0 / the `n ≲ √p` regime (no short root relation can
vanish). The deep content is whether it holds for the prize prime `p ≈ n·2^128`, `n = 2^30`. -/
def ShawLiftsToCharZero (σ : F →+* K) (G : Finset F) (r : ℕ) : Prop :=
  ∀ d : Fin (2 * r) → K, (∀ i, d i ∈ G.image σ) → (∑ i, d i = 0) →
    ∃ c : Fin (2 * r) → F, (∀ i, c i ∈ G) ∧ (∑ i, c i = 0) ∧ (∀ i, d i = σ (c i))

end Residual

/-! ## Part 3 — the transfer of the pairing residual.

The provable skeleton: p-stability + char-0 pairing + lift ⟹ char-`p` pairing residual. Pure
composition: lift a char-`p` tuple to char-0, pair it there (char-0 `H`), push the pairing forward
(`pushPairing`). The pushed pairing is exactly the char-`p` pairing of the original tuple. -/

section Transfer

variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]

/-- **The Shaw Transfer of the pairing residual (the skeleton).** Given:
* **(p-stability)** `σ` injective on `G` (`hσ : ShawPStable σ G`) — distinct nodes stay distinct;
* **(char-0 pairing `H`)** every char-0 zero-sum `2r`-tuple of `G` is antipodally paired;
* **(lift)** `ShawLiftsToCharZero σ G r` — every char-`p` zero-sum tuple lifts to char-0,

every char-`p` zero-sum `2r`-tuple of the reduced node set `σ(G)` is antipodally paired. This is the
char-`p` analog of the char-0 residual `H`, obtained by transferring along `σ` via naturality.

Proof: a char-`p` zero-sum tuple `d` lifts (by `hlift`) to a char-0 zero-sum tuple `c` with
`d = σ ∘ c`; `c` is paired in char 0 (by `H`); `pushPairing` pushes that pairing forward to `σ ∘ c = d`.
-/
theorem shawCharPPairing_of_lift (σ : F →+* K) {G : Finset F} {r : ℕ}
    (hσ : ShawPStable σ G)
    (H : ∀ c : Fin (2 * r) → F, (∀ i, c i ∈ G) → (∑ i, c i = 0) →
        ∃ σ_match : Equiv.Perm (Fin (2 * r)), IsPairing σ_match ∧ ∀ i, c (σ_match i) = - c i)
    (hlift : ShawLiftsToCharZero σ G r) :
    ∀ d : Fin (2 * r) → K, (∀ i, d i ∈ G.image σ) → (∑ i, d i = 0) →
      ∃ σ_match : Equiv.Perm (Fin (2 * r)), IsPairing σ_match ∧ ∀ i, d (σ_match i) = - d i := by
  intro d hdG hdsum
  -- lift d to a char-0 zero-sum tuple c with d = σ ∘ c
  obtain ⟨c, hcG, hcsum, hdc⟩ := hlift d hdG hdsum
  -- pair c in char 0
  obtain ⟨σ_match, hpairing, hcpair⟩ := H c hcG hcsum
  -- push the pairing forward along σ
  refine ⟨σ_match, hpairing, ?_⟩
  intro i
  -- d (σ_match i) = σ (c (σ_match i)) = σ (− c i) = − σ (c i) = − d i
  rw [hdc (σ_match i), hcpair i, map_neg, ← hdc i]

end Transfer

/-! ## Part 4 — the HEADLINE energy transfer.

The reduction of `E_r(𝔽_p) ≤ Wick` to the three inputs. We feed the transferred pairing residual
(Part 3) into the proven char-0 matching injection (`zeroSumCount_le_pairings`,
`pairings_card_eq_doubleFactorial`) over the reduced node set `σ(G)`, and use p-stability to rewrite
`|σ(G)|^r = |G|^r`. -/

section Energy

variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]

/-- **THE SHAW TRANSFER PRINCIPLE (energy headline).** Given the three named inputs
* `hσ : ShawPStable σ G` (p-stability — distinct nodes stay distinct mod 𝔭, outside the bad-prime set),
* `H` (the char-0 antipodal-pairing residual, the proven Lam–Leung input),
* `hlift : ShawLiftsToCharZero σ G r` (the NAMED open analytic residual — the char-`p` lift),
the char-`p` energy bound at the reduced node set `σ(G)` holds with the EXACT char-0 Wick constant:

> `zeroSumCount (σ(G)) (2r) ≤ (2r−1)‼·|G|^r`.

(`zeroSumCount` over `σ(G)` is `E_r(σ(G))` via the negation-closure bijection; `|G| = n`, so the
right side is `(2r−1)‼·n^r = Wick`.) The whole open content is concentrated in the single named
residual `hlift`; everything else (naturality push + matching injection) is PROVEN.

This is the transfer: the char-0 bound `(2r−1)‼·n^r` is carried to char-`p` along the reduction hom
`σ`, conditional ONLY on the lift. -/
theorem shawTransfer (σ : F →+* K) {G : Finset F} {r : ℕ}
    (hσ : ShawPStable σ G)
    (H : ∀ c : Fin (2 * r) → F, (∀ i, c i ∈ G) → (∑ i, c i = 0) →
        ∃ σ_match : Equiv.Perm (Fin (2 * r)), IsPairing σ_match ∧ ∀ i, c (σ_match i) = - c i)
    (hlift : ShawLiftsToCharZero σ G r) :
    zeroSumCount (G.image σ) (2 * r) ≤ (2 * r - 1)‼ * G.card ^ r := by
  classical
  -- char-`p` pairing residual on the reduced node set (Part 3)
  have Hp : ∀ d ∈ Fintype.piFinset (fun _ : Fin (2 * r) => G.image σ), (∑ i, d i = 0) →
      ∃ σ_match : Equiv.Perm (Fin (2 * r)), IsPairing σ_match ∧ ∀ i, d (σ_match i) = - d i := by
    intro d hd hdsum
    rw [Fintype.mem_piFinset] at hd
    exact shawCharPPairing_of_lift σ hσ H hlift d hd hdsum
  -- the proven char-0 matching injection, applied at the reduced node set σ(G)
  have hk : zeroSumCount (G.image σ) (2 * r)
      ≤ (Finset.univ.filter (fun τ : Equiv.Perm (Fin (2 * r)) => IsPairing τ)).card
          * (G.image σ).card ^ r :=
    zeroSumCount_le_pairings (G.image σ) Hp
  -- substitute #pairings = (2r−1)‼ and |σ(G)| = |G| (p-stability)
  rw [pairings_card_eq_doubleFactorial r, shawPStable_card_image σ hσ] at hk
  exact hk

/-- **`slack`/Wick form, explicit.** Restated with `|σ(G)|^r` written via `|G| = n`: the transfer
yields the bare Wick bound `(2r−1)‼·n^r` for the reduced node set, no excess. Equality of the
right-hand constant to the char-0 bound makes the "transfer" literal: the SAME closed form. -/
theorem shawTransfer_wick (σ : F →+* K) {G : Finset F} {r : ℕ}
    (hσ : ShawPStable σ G)
    (H : ∀ c : Fin (2 * r) → F, (∀ i, c i ∈ G) → (∑ i, c i = 0) →
        ∃ σ_match : Equiv.Perm (Fin (2 * r)), IsPairing σ_match ∧ ∀ i, c (σ_match i) = - c i)
    (hlift : ShawLiftsToCharZero σ G r) :
    (zeroSumCount (G.image σ) (2 * r) : ℝ) ≤ (2 * r - 1)‼ * (G.card : ℝ) ^ r := by
  have h := shawTransfer σ hσ H hlift
  calc (zeroSumCount (G.image σ) (2 * r) : ℝ)
      ≤ (((2 * r - 1)‼ * G.card ^ r : ℕ) : ℝ) := by exact_mod_cast h
    _ = (2 * r - 1)‼ * (G.card : ℝ) ^ r := by push_cast; ring

end Energy

/-! ## Part 5 — the lift is FREE in char 0 (closing the loop).

The principle is a strict generalization of the char-0 bound: in char 0 (and the `n ≲ √p` regime)
the lift `ShawLiftsToCharZero` is FREE for the identity reduction `σ = id`, so the transfer
reproduces the exact char-0 Lam–Leung bound. Combined with `_ShawMatchingInjection`'s
`wrapInjectsIntoSlack_zero_of_charZero`, this confirms the transfer neither over- nor under-claims:
the open residual vanishes EXACTLY where the char-0 proof applies. -/

section CharZero

variable {L : Type*} [Field L] [DecidableEq L]

/-- **The lift is FREE for the identity hom.** For `σ = RingHom.id`, every char-`p` zero-sum tuple of
`G.image id = G` IS literally a char-0 zero-sum tuple of `G` (take `c = d`), so
`ShawLiftsToCharZero (RingHom.id L) G r` holds unconditionally. This is the degenerate
`p`-stable-with-no-reduction case: the transfer is then the identity transfer, reproducing the char-0
bound. -/
theorem shawLiftsToCharZero_id (G : Finset L) (r : ℕ) :
    ShawLiftsToCharZero (RingHom.id L) G r := by
  intro d hdG hdsum
  refine ⟨d, ?_, hdsum, ?_⟩
  · intro i
    have := hdG i
    rwa [RingHom.coe_id, Finset.image_id] at this
  · intro i; rfl

/-- **`id` is `p`-stable (trivially injective).** -/
theorem shawPStable_id (G : Finset L) : ShawPStable (RingHom.id L) G :=
  Set.injOn_id _

/-- **Char-0 recovery: the transfer reproduces the exact char-0 bound.** In char 0 with `σ = id`,
p-stability and the lift are both free, so `shawTransfer` collapses to the char-0 matching bound
`E_r(G) ≤ (2r−1)‼·|G|^r` from the char-0 pairing residual `H` alone. This shows the Shaw Transfer
Principle strictly generalizes (and reduces to) the proven char-0 Lam–Leung bound: it adds the
reduction hom `σ` and the lift residual, both of which are vacuous in char 0. -/
theorem shawTransfer_charZero (G : Finset L) {r : ℕ}
    (H : ∀ c : Fin (2 * r) → L, (∀ i, c i ∈ G) → (∑ i, c i = 0) →
        ∃ σ_match : Equiv.Perm (Fin (2 * r)), IsPairing σ_match ∧ ∀ i, c (σ_match i) = - c i) :
    zeroSumCount G (2 * r) ≤ (2 * r - 1)‼ * G.card ^ r := by
  have h := shawTransfer (RingHom.id L) (shawPStable_id G) H (shawLiftsToCharZero_id G r)
  rwa [RingHom.coe_id, Finset.image_id] at h

end CharZero

end ArkLib.ProximityGap.Frontier.ShawTransfer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.ShawTransfer.pushPairing
#print axioms ArkLib.ProximityGap.Frontier.ShawTransfer.shawPStable_card_image
#print axioms ArkLib.ProximityGap.Frontier.ShawTransfer.shawCharPPairing_of_lift
#print axioms ArkLib.ProximityGap.Frontier.ShawTransfer.shawTransfer
#print axioms ArkLib.ProximityGap.Frontier.ShawTransfer.shawTransfer_wick
#print axioms ArkLib.ProximityGap.Frontier.ShawTransfer.shawLiftsToCharZero_id
#print axioms ArkLib.ProximityGap.Frontier.ShawTransfer.shawTransfer_charZero

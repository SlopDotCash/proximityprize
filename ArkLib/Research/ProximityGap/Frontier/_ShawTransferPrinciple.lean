/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._SpecS3_GaloisReduction
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
char-`0` zero-sum tuple (the lift). Precisely, for a ring hom `σ : F →+* K` from a commutative ring
`F` (e.g. `F = ℤ[ζ]`) to a field `K` (e.g. `K = 𝔽_p`) and a node set `G ⊆ F`:

(Audit correction CW-B14-02: an earlier version required `F` to be a *field*.  A ring hom out of a
field is injective and preserves the characteristic, so it cannot model `ℤ[ζ] → 𝔽_p`, and
`ShawPStable` was automatic (`shawPStable_of_field`).  The source is now an arbitrary commutative
ring; no reduction hom is instantiated in this file.)

> **(Shaw Transfer)** If
>   **(p-stability)** `σ` is INJECTIVE on `G` — distinct nodes stay distinct mod 𝔭 (this is the
>     "outside the bad-prime set" condition: two `2^μ`-th roots `x ≠ y` collide mod 𝔭 iff 𝔭 divides
>     `Norm(x−y)`, a finite set of primes; for `2^μ`-th roots these norms are powers of `2`, so odd
>     primes are good — note the earlier "`p ≫ 2^n`" justification was false at `n = 2^30`),
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
`PairingResidualFailsAtPrize`. The Shaw Transfer Principle does NOT contradict this: it isolates a
sufficient missing input, the LIFT `ShawLiftsToCharZero`, which must therefore also FAIL at that
scale. The lift fails when there are genuine char-`p` "wraparound" solutions — short `±1`-relations
of `2^μ`-th roots vanishing mod `p`
that have NO char-0 antecedent. So:

* Proved here: `ShawLiftsToCharZero` (with p-stability and char-0 pairing) ⟹ every char-`p`
  zero-sum tuple is paired ⟹ `E_r(σ(G)) ≤ Wick`.  The converse directions (no wraparound ⟹ lift,
  Wick bound ⟹ lift) are **not** proved, and no equivalence with the prize bound is claimed.
* For `σ = id` the lift is FREE and the transfer is the same-field identity, reproducing the
  char-0 matching bound (`shawTransfer_charZero`).  There is **no** "`n ≲ √p` ⟹ no wraparound"
  regime: `μ₁₆ ⊂ 𝔽₂₅₇` (`16 ≤ √257`) already has the unpaired zero-sum tuple `(1,1,2,−4)`
  (see `_ShawMatchingInjection`, audit CW-B14-03).

So the file proves one implication (lift ⟹ Wick-bound at the reduced node set); since the Wick
bound itself fails at the prize scale, so does the lift there, and this route cannot by itself
deliver the prize bound — any prize argument must control the wraparound excess rather than assume
it away.  `ShawLiftsToCharZero` is closely related to `WrapInjectsIntoSlack G r 0` of
`_ShawMatchingInjection`; this file gives the naturality-driven *form* of that condition (push
char-0 pairing forward along a reduction hom).

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
  bound (a same-field identity re-proving `zeroSumCount_le_pairings`; not a char-`p` result).
* `shawPStable_of_field` — for a field source p-stability is automatic (why `F` is a ring).

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

variable {F K : Type*} [CommRing F] [Field K] [DecidableEq F] [DecidableEq K]

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

omit [DecidableEq K] in
/-- **For a field source, p-stability is automatic (audit CW-B14-02).**  A ring hom out of a field
is injective, so `ShawPStable` carries no content there; it is only meaningful for a genuine
reduction such as `ℤ[ζ] →+* 𝔽_p`. -/
theorem shawPStable_of_field {L : Type*} [Field L] (σ : L →+* K) (G : Finset L) :
    ShawPStable σ G :=
  σ.injective.injOn

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

variable {F K : Type*} [CommRing F] [Field K] [DecidableEq F] [DecidableEq K]

/-- **The named char-`p` LIFT residual (the open analytic input).**
`ShawLiftsToCharZero σ G r` asserts: every zero-sum `2r`-tuple `d` of the reduced node set `σ(G)` is
the σ-image of a zero-sum `2r`-tuple `c` of `G` (i.e. `d = σ ∘ c`). This is the "no genuine
wraparound" condition: every char-`p` solution lifts to a char-0 solution. Combined with the char-0
pairing (`H`) and `p`-stability, it forces every char-`p` zero-sum tuple to be antipodally paired.

⚠️ Named open input, closely related to `WrapInjectsIntoSlack G r 0` of `_ShawMatchingInjection`.
It must FAIL wherever `E_r ≤ Wick` fails (e.g. at the prize scale, where the DC term forces genuine
wraparound), and it can fail even for small `n ≤ √p` (`μ₁₆ ⊂ 𝔽₂₅₇`, tuple `(1,1,2,−4)`).  It holds
trivially for `σ = id`. -/
def ShawLiftsToCharZero (σ : F →+* K) (G : Finset F) (r : ℕ) : Prop :=
  ∀ d : Fin (2 * r) → K, (∀ i, d i ∈ G.image σ) → (∑ i, d i = 0) →
    ∃ c : Fin (2 * r) → F, (∀ i, c i ∈ G) ∧ (∑ i, c i = 0) ∧ (∀ i, d i = σ (c i))

end Residual

/-! ## Part 3 — the transfer of the pairing residual.

The provable skeleton: p-stability + char-0 pairing + lift ⟹ char-`p` pairing residual. Pure
composition: lift a char-`p` tuple to char-0, pair it there (char-0 `H`), push the pairing forward
(`pushPairing`). The pushed pairing is exactly the char-`p` pairing of the original tuple. -/

section Transfer

variable {F K : Type*} [CommRing F] [Field K] [DecidableEq F] [DecidableEq K]

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

variable {F K : Type*} [CommRing F] [Field K] [DecidableEq F] [DecidableEq K]

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

For the identity `σ = id` (a same-field identity, not a reduction) the lift `ShawLiftsToCharZero`
is FREE, so the transfer reproduces the char-0 matching bound `zeroSumCount_le_pairings` — nothing
new.  This is the only instance in the file; no genuine reduction `ℤ[ζ] → 𝔽_p` is constructed. -/

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
Principle specializes to the matching bound at `σ = id`; this re-proves `zeroSumCount_le_pairings`
in the transfer's packaging and is not new content. -/
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
#print axioms ArkLib.ProximityGap.Frontier.ShawTransfer.shawPStable_of_field
#print axioms ArkLib.ProximityGap.Frontier.ShawTransfer.shawCharPPairing_of_lift
#print axioms ArkLib.ProximityGap.Frontier.ShawTransfer.shawTransfer
#print axioms ArkLib.ProximityGap.Frontier.ShawTransfer.shawTransfer_wick
#print axioms ArkLib.ProximityGap.Frontier.ShawTransfer.shawLiftsToCharZero_id
#print axioms ArkLib.ProximityGap.Frontier.ShawTransfer.shawTransfer_charZero

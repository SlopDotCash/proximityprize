/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic

/-!
# G80: the exact primitive-padding encoding space

G79S consumes the padded-sector envelope

`J * (r.descFactorial s)^2 * n^(r-s)`.

This file identifies that number as the exact cardinality of the natural cancellation code:

* one primitive depth-`s` core from a type `P` of cardinality `J`;
* an embedding of its left residual positions into `Fin r`;
* an embedding of its right residual positions into `Fin r`;
* one ordered common padding tuple of length `r-s` over `Fin n`.

It then proves that any injective encoding of a finite collision sector into this code has exactly
the G79S envelope bound.  The remaining concrete task is deliberately visible: construct the
injective encoding by maximal common-multiset cancellation for the actual shadow tuples.  No
surjectivity or canonical-decomposition claim is assumed silently here.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G80PrimitivePaddingEncoding

/-- The complete data needed to reconstruct a padded ordered collision from a primitive core. -/
abbrev PaddingCode (P : Type*) (n r s : ℕ) :=
  P × (Fin s ↪ Fin r) × (Fin s ↪ Fin r) × (Fin (r - s) → Fin n)

/-- **Exact cardinality of the primitive-padding code.** -/
theorem card_paddingCode (P : Type*) [Fintype P] (n r s : ℕ) :
    Fintype.card (PaddingCode P n r s) =
      Fintype.card P * (r.descFactorial s) ^ 2 * n ^ (r - s) := by
  simp only [PaddingCode, Fintype.card_prod, Fintype.card_embedding_eq,
    Fintype.card_fin, Fintype.card_fun, pow_two]
  ring

/-- An injective cancellation encoding gives the G79S padded-sector envelope immediately. -/
theorem card_le_paddingEnvelope_of_injective
    {W P : Type*} [Fintype W] [Fintype P]
    (n r s : ℕ) (encode : W → PaddingCode P n r s)
    (hinj : Function.Injective encode) :
    Fintype.card W ≤ Fintype.card P * (r.descFactorial s) ^ 2 * n ^ (r - s) := by
  rw [← card_paddingCode P n r s]
  exact Fintype.card_le_of_injective encode hinj

/-- Embedding-valued form, convenient when the concrete cancellation construction is naturally
packaged as a `Function.Embedding`. -/
theorem card_le_paddingEnvelope_of_embedding
    {W P : Type*} [Fintype W] [Fintype P]
    (n r s : ℕ) (encode : W ↪ PaddingCode P n r s) :
    Fintype.card W ≤ Fintype.card P * (r.descFactorial s) ^ 2 * n ^ (r - s) :=
  card_le_paddingEnvelope_of_injective n r s encode encode.injective

/-- Finset-sector form: an injection defined only on the realized sector still yields the same
envelope, with `W.card` on the left. -/
theorem finset_card_le_paddingEnvelope_of_injOn
    {α P : Type*} [Fintype P] (W : Finset α)
    (n r s : ℕ) (encode : α → PaddingCode P n r s)
    (hinj : Set.InjOn encode W) :
    W.card ≤ Fintype.card P * (r.descFactorial s) ^ 2 * n ^ (r - s) := by
  let e : {x // x ∈ W} ↪ PaddingCode P n r s :=
    ⟨fun x => encode x.1, fun x y h => Subtype.ext (hinj x.2 y.2 h)⟩
  have hcard : Fintype.card {x // x ∈ W} = W.card := Fintype.card_coe W
  rw [← hcard]
  exact card_le_paddingEnvelope_of_embedding n r s e

/-! ## Relative-order audit -/

/-- Fully common ordered tuple pairs: choose an injective left tuple and a permutation giving the
relative order of the same values in the right tuple.  This is a genuine family of pairs with
maximal common multiset and primitive residual depth zero. -/
abbrev FullyCommonOrderedPairs (n r : ℕ) :=
  (Fin r ↪ Fin n) × Equiv.Perm (Fin r)

/-- The fully common ordered family has an extra `r!` relative-order factor. -/
theorem card_fullyCommonOrderedPairs (n r : ℕ) :
    Fintype.card (FullyCommonOrderedPairs n r) = n.descFactorial r * r.factorial := by
  simp only [FullyCommonOrderedPairs, Fintype.card_prod, Fintype.card_embedding_eq,
    Fintype.card_fin, Fintype.card_perm]

/-- **Smallest relative-order obstruction.**  For `n=3`, `r=2`, there are twelve fully common
ordered pairs but the advertised depth-zero padding code has only nine elements.  Therefore no
injective maximal-cancellation encoding into `PaddingCode Unit 3 2 0` exists.

This does not affect sectors whose collision objects have already been quotiented by independent
left/right permutations.  For raw ordered tuples, however, the G79 envelope needs either an extra
relative-padding permutation, or a prior symmetry quotient with its multiplicity accounted for. -/
theorem no_injective_fullyCommon_to_paddingCode_three_two :
    ¬ ∃ encode : FullyCommonOrderedPairs 3 2 → PaddingCode Unit 3 2 0,
        Function.Injective encode := by
  rintro ⟨encode, hinj⟩
  have hcard := Fintype.card_le_of_injective encode hinj
  rw [card_fullyCommonOrderedPairs, card_paddingCode] at hcard
  norm_num at hcard

/-! ## Corrected raw-ordered code -/

/-- For raw ordered tuple pairs, reconstruction also needs the relative permutation of the common
padding entries on the right. -/
abbrev OrderedPaddingCode (P : Type*) (n r s : ℕ) :=
  PaddingCode P n r s × Equiv.Perm (Fin (r - s))

/-- **Exact corrected cardinality.**  The missing relative-order factor is `(r-s)!`. -/
theorem card_orderedPaddingCode (P : Type*) [Fintype P] (n r s : ℕ) :
    Fintype.card (OrderedPaddingCode P n r s) =
      Fintype.card P * (r.descFactorial s) ^ 2 * n ^ (r - s) * (r - s).factorial := by
  simp only [OrderedPaddingCode, PaddingCode, Fintype.card_prod, Fintype.card_perm,
    Fintype.card_fin, Fintype.card_embedding_eq, Fintype.card_fun]
  ring

/-- Any injective encoding of raw ordered collisions into the corrected code pays the additional
relative-padding factorial. -/
theorem card_le_orderedPaddingEnvelope_of_injective
    {W P : Type*} [Fintype W] [Fintype P]
    (n r s : ℕ) (encode : W → OrderedPaddingCode P n r s)
    (hinj : Function.Injective encode) :
    Fintype.card W ≤
      Fintype.card P * (r.descFactorial s) ^ 2 * n ^ (r - s) * (r - s).factorial := by
  rw [← card_orderedPaddingCode P n r s]
  exact Fintype.card_le_of_injective encode hinj

/-- The natural reconstruction form: a surjective decoder from corrected padding codes onto a
finite collision fiber gives the same bound.  This is weaker and better suited to repeated padding
values than choosing an injective canonical encoder. -/
theorem card_le_orderedPaddingEnvelope_of_surjective
    {W P : Type*} [Fintype W] [Fintype P]
    (n r s : ℕ) (decode : OrderedPaddingCode P n r s → W)
    (hsurj : Function.Surjective decode) :
    Fintype.card W ≤
      Fintype.card P * (r.descFactorial s) ^ 2 * n ^ (r - s) * (r - s).factorial := by
  rw [← card_orderedPaddingCode P n r s]
  exact Fintype.card_le_of_surjective decode hsurj

/-- Fixed-core specialization: if `P` is a singleton, a surjective reconstruction bounds one
primitive core fiber by exactly the corrected per-core envelope. -/
theorem card_fixedCoreFiber_le_of_surjective
    {W : Type*} [Fintype W]
    (n r s : ℕ) (decode : OrderedPaddingCode Unit n r s → W)
    (hsurj : Function.Surjective decode) :
    Fintype.card W ≤ (r.descFactorial s) ^ 2 * n ^ (r - s) * (r - s).factorial := by
  simpa using card_le_orderedPaddingEnvelope_of_surjective n r s decode hsurj

/-- At the G79S nominal production parameters, the corrected depth-two single-orbit envelope is
already strictly larger than the two-factor Wick allocation.  Thus the raw-ordered correction is
not a harmless constant: factorial padding order destroys that absorption calculation. -/
theorem production_depth_two_corrected_envelope_exceeds_oddTail :
    (2 * (110 - 0) - 1) * (2 * (110 - 1) - 1) * (2 ^ 30) ^ 110 <
      (2 ^ 30) * ((110 : ℕ).descFactorial 2) ^ 2 * (2 ^ 30) ^ (110 - 2) *
        (110 - 2).factorial := by
  norm_num [Nat.descFactorial, Nat.factorial]

/-- The corrected raw-ordered padded-sector envelope. -/
def orderedPadEnvelope (n r J s : ℕ) : ℕ :=
  J * (r.descFactorial s) ^ 2 * n ^ (r - s) * (r - s).factorial

/-- **Full-Wick repair.**  Although the relative-order factorial cannot be paid from only the last
`s` Wick factors, it is absorbed by the full double factorial whenever the displayed
denominator-cleared criterion holds. -/
theorem orderedPaddedSector_le_fullWick
    {n r J s W : ℕ} (hsr : s ≤ r)
    (hW : W ≤ orderedPadEnvelope n r J s)
    (hbudget : J * (r.descFactorial s) ^ 2 * (r - s).factorial ≤
      n ^ s * Nat.doubleFactorial (2 * r - 1)) :
    W ≤ Nat.doubleFactorial (2 * r - 1) * n ^ r := by
  calc
    W ≤ orderedPadEnvelope n r J s := hW
    _ = (J * (r.descFactorial s) ^ 2 * (r - s).factorial) * n ^ (r - s) := by
      unfold orderedPadEnvelope
      ring
    _ ≤ (n ^ s * Nat.doubleFactorial (2 * r - 1)) * n ^ (r - s) := by gcongr
    _ = Nat.doubleFactorial (2 * r - 1) * (n ^ s * n ^ (r - s)) := by ring
    _ = Nat.doubleFactorial (2 * r - 1) * n ^ r := by
      rw [← pow_add, Nat.add_sub_of_le hsr]

/-- At the nominal production parameters, the corrected single-orbit depth-two envelope is still
absorbed by the FULL Wick budget, with more than 122 bits of numerical slack.  What fails is only
the stronger allocation to the last two Wick factors. -/
theorem production_depth_two_corrected_envelope_le_fullWick :
    orderedPadEnvelope (2 ^ 30) 110 (2 ^ 30) 2 ≤
      Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  apply orderedPaddedSector_le_fullWick (n := 2 ^ 30) (r := 110)
      (J := 2 ^ 30) (s := 2) (W := orderedPadEnvelope (2 ^ 30) 110 (2 ^ 30) 2)
  · norm_num
  · rfl
  · norm_num [Nat.descFactorial, Nat.factorial, Nat.doubleFactorial]

/-- The production Wick budget absorbs at least `2^122` corrected depth-two, linear-size orbit
envelopes simultaneously.  This turns the single-orbit repair into a quantitative collective
budget. -/
theorem production_depth_two_2pow122_envelopes_le_fullWick :
    2 ^ 122 * orderedPadEnvelope (2 ^ 30) 110 (2 ^ 30) 2 ≤
      Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  norm_num [orderedPadEnvelope, Nat.descFactorial, Nat.factorial, Nat.doubleFactorial]

/-- **Collective orbit-pool consumer.**  Any union of at most `2^122` depth-two primitive orbit
sectors, each charged by the corrected linear-size envelope, fits in one production Wick budget. -/
theorem production_depth_two_orbit_pool_absorbed
    {K W : ℕ} (hK : K ≤ 2 ^ 122)
    (hW : W ≤ K * orderedPadEnvelope (2 ^ 30) 110 (2 ^ 30) 2) :
    W ≤ Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  calc
    W ≤ K * orderedPadEnvelope (2 ^ 30) 110 (2 ^ 30) 2 := hW
    _ ≤ 2 ^ 122 * orderedPadEnvelope (2 ^ 30) 110 (2 ^ 30) 2 := by gcongr
    _ ≤ Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 :=
      production_depth_two_2pow122_envelopes_le_fullWick

/-! ## Closing the depth-two core-count residual -/

/-- The ambient universe of ordered depth-two primitive cores: an ordered left pair and an ordered
right pair of subgroup indices.  Every realized primitive depth-two core is a member of this type,
before imposing disjointness, nontriviality, vanishing, or quotienting by rotation. -/
abbrev DepthTwoCoreUniverse (n : ℕ) :=
  (Fin 2 → Fin n) × (Fin 2 → Fin n)

/-- The entire raw depth-two core universe has exactly `n^4` elements. -/
theorem card_depthTwoCoreUniverse (n : ℕ) :
    Fintype.card (DepthTwoCoreUniverse n) = n ^ 4 := by
  simp only [DepthTwoCoreUniverse, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  ring

/-- At production order `n=2^30`, the full raw core universe has size `2^120`, hence fits below
the certified `2^122` collective budget even before any primitive/disjoint/rotation reduction. -/
theorem production_card_depthTwoCoreUniverse_le_2pow122 :
    Fintype.card (DepthTwoCoreUniverse (2 ^ 30)) ≤ 2 ^ 122 := by
  rw [card_depthTwoCoreUniverse]
  norm_num

/-- Every realized finset of production depth-two cores inherits the same `2^122` cap. -/
theorem production_depthTwoCoreFinset_card_le_2pow122
    (P : Finset (DepthTwoCoreUniverse (2 ^ 30))) :
    P.card ≤ 2 ^ 122 := by
  calc
    P.card ≤ Fintype.card (DepthTwoCoreUniverse (2 ^ 30)) := Finset.card_le_univ P
    _ ≤ 2 ^ 122 := production_card_depthTwoCoreUniverse_le_2pow122

/-- **Depth-two pool count discharged.**  No separate orbit-count theorem is needed: if a realized
depth-two core finset `P` contributes at most one corrected linear envelope per core, its entire
mass fits in the full production Wick budget.  Since orbit quotienting can only reduce the index
set, this also covers any orbit-indexed subfamily admitting the same per-item charge. -/
theorem production_depth_two_all_cores_absorbed
    (P : Finset (DepthTwoCoreUniverse (2 ^ 30))) {W : ℕ}
    (hW : W ≤ P.card * orderedPadEnvelope (2 ^ 30) 110 (2 ^ 30) 2) :
    W ≤ Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  exact production_depth_two_orbit_pool_absorbed
    (production_depthTwoCoreFinset_card_le_2pow122 P) hW

end ArkLib.ProximityGap.Frontier.G80PrimitivePaddingEncoding

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G80PrimitivePaddingEncoding.card_paddingCode
#print axioms
  ArkLib.ProximityGap.Frontier.G80PrimitivePaddingEncoding.card_le_paddingEnvelope_of_injective
#print axioms
  ArkLib.ProximityGap.Frontier.G80PrimitivePaddingEncoding.finset_card_le_paddingEnvelope_of_injOn
#print axioms
  ArkLib.ProximityGap.Frontier.G80PrimitivePaddingEncoding.no_injective_fullyCommon_to_paddingCode_three_two
#print axioms ArkLib.ProximityGap.Frontier.G80PrimitivePaddingEncoding.card_orderedPaddingCode
#print axioms
  ArkLib.ProximityGap.Frontier.G80PrimitivePaddingEncoding.card_fixedCoreFiber_le_of_surjective
#print axioms
  ArkLib.ProximityGap.Frontier.G80PrimitivePaddingEncoding.production_depth_two_corrected_envelope_exceeds_oddTail
#print axioms
  ArkLib.ProximityGap.Frontier.G80PrimitivePaddingEncoding.orderedPaddedSector_le_fullWick
#print axioms
  ArkLib.ProximityGap.Frontier.G80PrimitivePaddingEncoding.production_depth_two_corrected_envelope_le_fullWick
#print axioms
  ArkLib.ProximityGap.Frontier.G80PrimitivePaddingEncoding.production_depth_two_2pow122_envelopes_le_fullWick
#print axioms
  ArkLib.ProximityGap.Frontier.G80PrimitivePaddingEncoding.production_depth_two_orbit_pool_absorbed
#print axioms ArkLib.ProximityGap.Frontier.G80PrimitivePaddingEncoding.card_depthTwoCoreUniverse
#print axioms
  ArkLib.ProximityGap.Frontier.G80PrimitivePaddingEncoding.production_depth_two_all_cores_absorbed

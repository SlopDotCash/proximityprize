/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G151CompositePacketOnsetDepthFour
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS11GenericDepthDecomposition
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS5TrivialCountClosedForm

/-!
# G153: FS11 wraparound is witnessed by a primitive nonzero packet

The G147--G151 packet tree is a decomposition of an equal-sum collision in the finite field.
For the FS11 application one must retain a second, characteristic-zero label: lift every
`2m`-th root back to its signed monomial in `ℤ[X]`.  The finite-field sum of a packet vanishes,
but this lifted polynomial need not vanish.  Precisely those nonzero labels are the wraparound
mass.

This file supplies the missing *lower* charge transfer.  An additive signed label of a root is
the sum of the labels of its primitive leaves.  Therefore a nonzero root label forces a nonzero
primitive leaf.  At depth at most seven the G150 minimum packet depth then gives the quantitative
bound

`1 ≤ number of nonzero primitive leaves ≤ number of leaves ≤ 3`.

The final theorem applies this to an injective FS11 depth-seven tuple pair.  After cancelling
the common field-valued support, every injective wraparound configuration is thus an assembly of
at most three primitive balanced packets, at least one of which has a nonzero cyclotomic lift.
This is an unconditional bounded-depth reduction of the injective sector.  Repeated-coordinate
tuples still require a multiplicity-packet analogue; no claim about their census is made here.

Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.G153FS11PrimitivePacketNonzeroCharge

open ArkLib.ProximityGap.Frontier.FS4Depth3PatternDecomposition
open ArkLib.ProximityGap.Frontier.FS5TrivialCountClosedForm
open ArkLib.ProximityGap.Frontier.FS11GenericDepthDecomposition
open ArkLib.ProximityGap.Frontier.G147ConnectedBalancedCoreRecursion
open ArkLib.ProximityGap.Frontier.G148FinitePrimitivePacketTree
open ArkLib.ProximityGap.Frontier.G149PrimitivePacketChargeTransfer
open ArkLib.ProximityGap.Frontier.G150PrimitivePacketDepthTwoBase

open scoped BigOperators Classical

section AbstractCharge

variable {F A : Type*} [AddCommGroup F] [DecidableEq F] [AddCommGroup A]

/-- The signed lift of a balanced packet through an arbitrary additive label. -/
def signedPacketLabel (lift : F → A) (c : Finset F × Finset F) : A :=
  (∑ x ∈ c.1, lift x) - ∑ x ∈ c.2, lift x

/-- Sum of the signed labels over all primitive leaves of a packet tree. -/
def leafLabelSum (lift : F → A) {c : Finset F × Finset F} :
    PrimitivePacketTree c → A
  | .leaf _ => signedPacketLabel lift c
  | .split _ _ _ _ _ _ _ _ _ left right => leafLabelSum lift left + leafLabelSum lift right

/-- Number of primitive leaves on which the signed lift is nonzero. -/
noncomputable def nonzeroLeafCount (lift : F → A) {c : Finset F × Finset F} :
    PrimitivePacketTree c → ℕ
  | .leaf _ => if signedPacketLabel lift c = 0 then 0 else 1
  | .split _ _ _ _ _ _ _ _ _ left right =>
      nonzeroLeafCount lift left + nonzeroLeafCount lift right

/-- Signed labels are additive across every disjoint packet split. -/
theorem signedPacketLabel_split
    (lift : F → A) {c d e : Finset F × Finset F}
    (hdisjL : Disjoint d.1 e.1) (hdisjR : Disjoint d.2 e.2)
    (hreconL : d.1 ∪ e.1 = c.1) (hreconR : d.2 ∪ e.2 = c.2) :
    signedPacketLabel lift c = signedPacketLabel lift d + signedPacketLabel lift e := by
  unfold signedPacketLabel
  rw [← hreconL, ← hreconR, Finset.sum_union hdisjL, Finset.sum_union hdisjR]
  abel

/-- Exact label conservation: the root label is the sum of its primitive-leaf labels. -/
theorem leafLabelSum_eq_root
    (lift : F → A) {c : Finset F × Finset F} (T : PrimitivePacketTree c) :
    leafLabelSum lift T = signedPacketLabel lift c := by
  induction T with
  | leaf hc => rfl
  | split hc hd he hdlt helt hdisjL hdisjR hreconL hreconR left right ihL ihR =>
      simp only [leafLabelSum, ihL, ihR]
      exact (signedPacketLabel_split lift hdisjL hdisjR hreconL hreconR).symm

/-- A nonzero root label is witnessed by a nonzero primitive leaf. -/
theorem exists_primitive_leaf_label_ne_zero
    (lift : F → A) {c : Finset F × Finset F} (T : PrimitivePacketTree c)
    (hroot : signedPacketLabel lift c ≠ 0) :
    ∃ d : Finset F × Finset F,
      IsPrimitiveBalancedCore d ∧ signedPacketLabel lift d ≠ 0 := by
  induction T with
  | leaf hc => exact ⟨_, hc, hroot⟩
  | split hc hd he hdlt helt hdisjL hdisjR hreconL hreconR left right ihL ihR =>
      have hsum := signedPacketLabel_split lift hdisjL hdisjR hreconL hreconR
      by_cases hleft : leafLabelSum lift left = 0
      · apply ihR
        intro hrightRoot
        apply hroot
        rw [hsum, ← leafLabelSum_eq_root lift left,
          hleft, hrightRoot, zero_add]
      · apply ihL
        intro hleftRoot
        apply hleft
        rw [leafLabelSum_eq_root lift left, hleftRoot]

/-- The nonzero-leaf charge never exceeds the total number of primitive leaves. -/
theorem nonzeroLeafCount_le_leafCount
    (lift : F → A) {c : Finset F × Finset F} (T : PrimitivePacketTree c) :
    nonzeroLeafCount lift T ≤ T.leafCount := by
  induction T with
  | leaf hc =>
      simp only [nonzeroLeafCount, PrimitivePacketTree.leafCount]
      split <;> omega
  | split hc hd he hdlt helt hdisjL hdisjR hreconL hreconR left right ihL ihR =>
      simp only [nonzeroLeafCount, PrimitivePacketTree.leafCount]
      exact Nat.add_le_add ihL ihR

/-- A nonzero root contributes at least one unit of nonzero primitive-leaf charge. -/
theorem one_le_nonzeroLeafCount
    (lift : F → A) {c : Finset F × Finset F} (T : PrimitivePacketTree c)
    (hroot : signedPacketLabel lift c ≠ 0) :
    1 ≤ nonzeroLeafCount lift T := by
  induction T with
  | leaf hc => simp [nonzeroLeafCount, hroot]
  | split hc hd he hdlt helt hdisjL hdisjR hreconL hreconR left right ihL ihR =>
      have hsum := signedPacketLabel_split lift hdisjL hdisjR hreconL hreconR
      by_cases hleft : leafLabelSum lift left = 0
      · have hright : leafLabelSum lift right ≠ 0 := by
          intro hrightZero
          apply hroot
          rw [hsum, ← leafLabelSum_eq_root lift left,
            ← leafLabelSum_eq_root lift right, hleft, hrightZero, zero_add]
        simp only [nonzeroLeafCount]
        apply le_add_left
        apply ihR
        intro hrightRoot
        apply hright
        rw [leafLabelSum_eq_root lift right, hrightRoot]
      · simp only [nonzeroLeafCount]
        apply le_add_right
        apply ihL
        intro hleftRoot
        apply hleft
        rw [leafLabelSum_eq_root lift left, hleftRoot]

/-- **Depth-seven charge interval.** A nonzero packet of depth at most seven has between one and
three nonzero primitive leaves. -/
theorem nonzeroLeafCount_between_one_and_three
    (lift : F → A) {c : Finset F × Finset F} (T : PrimitivePacketTree c)
    (hdepth : c.1.card ≤ 7) (hroot : signedPacketLabel lift c ≠ 0) :
    1 ≤ nonzeroLeafCount lift T ∧ nonzeroLeafCount lift T ≤ 3 := by
  have htwo := two_mul_leafCount_le_rootDepth T
  have hcharge := nonzeroLeafCount_le_leafCount lift T
  exact ⟨one_le_nonzeroLeafCount lift T hroot, by omega⟩

end AbstractCharge

section CyclotomicLift

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem packet_card_sdiff_eq_card_sdiff {S T : Finset F} (hcard : S.card = T.card) :
    (S \ T).card = (T \ S).card := by
  rw [Finset.card_sdiff, Finset.card_sdiff, Finset.inter_comm S T, hcard]

theorem packet_disjoint_sdiff_sdiff (S T : Finset F) : Disjoint (S \ T) (T \ S) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1

theorem packet_sum_sdiff_eq_sum_sdiff {S T : Finset F}
    (hsum : (∑ x ∈ S, x) = ∑ x ∈ T, x) :
    (∑ x ∈ S \ T, x) = ∑ x ∈ T \ S, x := by
  have hST : S \ T = S \ (S ∩ T) := by ext x; simp
  have hTS : T \ S = T \ (S ∩ T) := by ext x; simp [and_comm]
  rw [hST, hTS, Finset.sum_sdiff_eq_sub Finset.inter_subset_left,
    Finset.sum_sdiff_eq_sub Finset.inter_subset_right, hsum]

/-- Canonical exponent in `[0,n)` when `x` is an `n`-th root power; zero off that image. -/
noncomputable def rootLog (zeta : F) (n : ℕ) (x : F) : ℕ :=
  if h : ∃ a : ℕ, a < n ∧ zeta ^ a = x then Classical.choose h else 0

theorem rootLog_spec {zeta x : F} {n : ℕ}
    (hx : ∃ a : ℕ, a < n ∧ zeta ^ a = x) :
    rootLog zeta n x < n ∧ zeta ^ rootLog zeta n x = x := by
  rw [rootLog, dif_pos hx]
  exact Classical.choose_spec hx

theorem rootLog_pow_eq {zeta : F} {n a : ℕ} (hprim : IsPrimitiveRoot zeta n)
    (ha : a < n) : rootLog zeta n (zeta ^ a) = a := by
  have hs := rootLog_spec (zeta := zeta) (n := n) (x := zeta ^ a) ⟨a, ha, rfl⟩
  exact hprim.pow_inj hs.1 ha hs.2

/-- Characteristic-zero signed-monomial lift of a finite-field root power. -/
noncomputable def cyclotomicLift (zeta : F) (m : ℕ) (x : F) : ℤ[X] :=
  monomF m (rootLog zeta (2 * m) x)

theorem cyclotomicLift_pow {zeta : F} {m a : ℕ}
    (hprim : IsPrimitiveRoot zeta (2 * m)) (ha : a < 2 * m) :
    cyclotomicLift zeta m (zeta ^ a) = monomF m a := by
  rw [cyclotomicLift, rootLog_pow_eq hprim ha]

/-- Field-valued support of an indexed exponent tuple. -/
noncomputable def rootSupport {r : ℕ} (zeta : F) (a : Fin r → ℕ) : Finset F :=
  Finset.univ.image fun i => zeta ^ a i

/-- Cancel the common support of two field-valued tuples. -/
noncomputable def tupleCancellationCore {r : ℕ} (zeta : F)
    (a b : Fin r → ℕ) : Finset F × Finset F :=
  (rootSupport zeta a \ rootSupport zeta b, rootSupport zeta b \ rootSupport zeta a)

/-- Finite injective-coordinate portion of FS11's wraparound configurations. -/
noncomputable def injectiveWraparoundPairs (zeta : F) (m r : ℕ) :
    Finset ((Fin r → ℕ) × (Fin r → ℕ)) :=
  (expTuples (2 * m) r ×ˢ expTuples (2 * m) r).filter fun ab =>
    (patternPolyG m ab.1 ab.2 ≠ 0 ∧
      aeval zeta (patternPolyG m ab.1 ab.2) = 0) ∧
      (Function.Injective ab.1 ∧ Function.Injective ab.2)

/-- Cardinality of the injective-coordinate portion of FS11's wraparound excess. -/
noncomputable def injectiveWraparoundExcessG (zeta : F) (m r : ℕ) : ℕ :=
  (injectiveWraparoundPairs zeta m r).card

/-- Finite repeated-coordinate portion of FS11's wraparound configurations. -/
noncomputable def repeatedWraparoundPairs (zeta : F) (m r : ℕ) :
    Finset ((Fin r → ℕ) × (Fin r → ℕ)) :=
  (expTuples (2 * m) r ×ˢ expTuples (2 * m) r).filter fun ab =>
    (patternPolyG m ab.1 ab.2 ≠ 0 ∧
      aeval zeta (patternPolyG m ab.1 ab.2) = 0) ∧
      ¬ (Function.Injective ab.1 ∧ Function.Injective ab.2)

/-- Cardinality of the complementary repeated-coordinate wraparound sector. -/
noncomputable def repeatedWraparoundExcessG (zeta : F) (m r : ℕ) : ℕ :=
  (repeatedWraparoundPairs zeta m r).card

/-- **Exact multiplicity partition.** FS11 wraparound mass is the disjoint sum of the injective
sector controlled below by primitive packets and the still-open repeated-coordinate sector. -/
theorem wraparoundExcessG_eq_injective_add_repeated (zeta : F) (m r : ℕ) :
    wraparoundExcessG zeta m r =
      injectiveWraparoundExcessG zeta m r + repeatedWraparoundExcessG zeta m r := by
  classical
  let S := expTuples (2 * m) r ×ˢ expTuples (2 * m) r
  let P := fun ab : (Fin r → ℕ) × (Fin r → ℕ) =>
    patternPolyG m ab.1 ab.2 ≠ 0 ∧ aeval zeta (patternPolyG m ab.1 ab.2) = 0
  let Q := fun ab : (Fin r → ℕ) × (Fin r → ℕ) =>
    Function.Injective ab.1 ∧ Function.Injective ab.2
  have hunion : S.filter P =
      S.filter (fun ab => P ab ∧ Q ab) ∪ S.filter (fun ab => P ab ∧ ¬ Q ab) := by
    ext ab
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  have hdisj : Disjoint (S.filter (fun ab => P ab ∧ Q ab))
      (S.filter (fun ab => P ab ∧ ¬ Q ab)) := by
    apply Finset.disjoint_left.mpr
    intro ab hab hba
    exact (Finset.mem_filter.mp hba).2.2 (Finset.mem_filter.mp hab).2.2
  unfold wraparoundExcessG injectiveWraparoundExcessG repeatedWraparoundExcessG
    injectiveWraparoundPairs repeatedWraparoundPairs
  change (S.filter P).card =
    (S.filter (fun ab => P ab ∧ Q ab)).card + (S.filter (fun ab => P ab ∧ ¬ Q ab)).card
  rw [hunion, Finset.card_union_of_disjoint hdisj]

theorem mem_injectiveWraparoundExcessG_set {zeta : F} {m r : ℕ}
    {ab : (Fin r → ℕ) × (Fin r → ℕ)}
    (hab : ab ∈ injectiveWraparoundPairs zeta m r) :
    (∀ i, ab.1 i < 2 * m) ∧ (∀ i, ab.2 i < 2 * m) ∧
      patternPolyG m ab.1 ab.2 ≠ 0 ∧
      aeval zeta (patternPolyG m ab.1 ab.2) = 0 ∧
      Function.Injective ab.1 ∧ Function.Injective ab.2 := by
  rw [injectiveWraparoundPairs, Finset.mem_filter, Finset.mem_product] at hab
  obtain ⟨⟨ha, hb⟩, ⟨hne, heval⟩, hinja, hinjb⟩ := hab
  rw [expTuples, Fintype.mem_piFinset] at ha hb
  exact ⟨fun i => Finset.mem_range.mp (ha i), fun i => Finset.mem_range.mp (hb i),
    hne, heval, hinja, hinjb⟩

theorem rootTuple_injective {zeta : F} {m r : ℕ} (hprim : IsPrimitiveRoot zeta (2 * m))
    {a : Fin r → ℕ} (ha : ∀ i, a i < 2 * m) (hinj : Function.Injective a) :
    Function.Injective (fun i => zeta ^ a i) := by
  intro i j hij
  exact hinj (hprim.pow_inj (ha i) (ha j) hij)

theorem rootSupport_card {zeta : F} {m r : ℕ} (hprim : IsPrimitiveRoot zeta (2 * m))
    {a : Fin r → ℕ} (ha : ∀ i, a i < 2 * m) (hinj : Function.Injective a) :
    (rootSupport zeta a).card = r := by
  rw [rootSupport, Finset.card_image_of_injective _ (rootTuple_injective hprim ha hinj),
    Finset.card_univ, Fintype.card_fin]

theorem sum_rootSupport {zeta : F} {m r : ℕ} (hprim : IsPrimitiveRoot zeta (2 * m))
    {a : Fin r → ℕ} (ha : ∀ i, a i < 2 * m) (hinj : Function.Injective a) :
    (∑ x ∈ rootSupport zeta a, x) = ∑ i, zeta ^ a i := by
  rw [rootSupport, Finset.sum_image]
  exact fun i _ j _ hij => rootTuple_injective hprim ha hinj hij

theorem sum_cyclotomicLift_rootSupport
    {zeta : F} {m r : ℕ} (hprim : IsPrimitiveRoot zeta (2 * m))
    {a : Fin r → ℕ} (ha : ∀ i, a i < 2 * m) (hinj : Function.Injective a) :
    (∑ x ∈ rootSupport zeta a, cyclotomicLift zeta m x) =
      ∑ i, monomF m (a i) := by
  rw [rootSupport, Finset.sum_image]
  · exact Finset.sum_congr rfl fun i _ => cyclotomicLift_pow hprim (ha i)
  · exact fun i _ j _ hij => rootTuple_injective hprim ha hinj hij

/-- Cancelling a common support preserves the signed sum of arbitrary labels. -/
theorem signedLabel_tupleCancellationCore
    {r : ℕ} (lift : F → ℤ[X]) (zeta : F) (a b : Fin r → ℕ) :
    signedPacketLabel lift (tupleCancellationCore zeta a b) =
      (∑ x ∈ rootSupport zeta a, lift x) - ∑ x ∈ rootSupport zeta b, lift x := by
  let A := rootSupport zeta a
  let B := rootSupport zeta b
  have hAB : A \ B = A \ (A ∩ B) := by ext x; simp
  have hBA : B \ A = B \ (A ∩ B) := by ext x; simp [and_comm]
  unfold signedPacketLabel tupleCancellationCore
  change (∑ x ∈ A \ B, lift x) - ∑ x ∈ B \ A, lift x = _
  rw [hAB, hBA, Finset.sum_sdiff_eq_sub Finset.inter_subset_left,
    Finset.sum_sdiff_eq_sub Finset.inter_subset_right]
  ring

/-- The characteristic-zero signed label of the cancellation core is exactly FS11's pattern
polynomial. -/
theorem tupleCancellationCore_label_eq_patternPolyG
    {zeta : F} {m r : ℕ} (hprim : IsPrimitiveRoot zeta (2 * m))
    {a b : Fin r → ℕ} (ha : ∀ i, a i < 2 * m) (hb : ∀ i, b i < 2 * m)
    (hinja : Function.Injective a) (hinjb : Function.Injective b) :
    signedPacketLabel (cyclotomicLift zeta m) (tupleCancellationCore zeta a b) =
      patternPolyG m a b := by
  rw [signedLabel_tupleCancellationCore,
    sum_cyclotomicLift_rootSupport hprim ha hinja,
    sum_cyclotomicLift_rootSupport hprim hb hinjb]
  rfl

/-- An injective FS11 wraparound pair produces a balanced cancellation core of depth at most `r`
whose characteristic-zero label is nonzero. -/
theorem tupleCancellationCore_balanced
    {zeta : F} {m r : ℕ} (hm : 0 < m) (hprim : IsPrimitiveRoot zeta (2 * m))
    {a b : Fin r → ℕ} (ha : ∀ i, a i < 2 * m) (hb : ∀ i, b i < 2 * m)
    (hinja : Function.Injective a) (hinjb : Function.Injective b)
    (hne : patternPolyG m a b ≠ 0) (heval : aeval zeta (patternPolyG m a b) = 0) :
    IsBalancedCore (tupleCancellationCore zeta a b) ∧
      (tupleCancellationCore zeta a b).1.card ≤ r ∧
      signedPacketLabel (cyclotomicLift zeta m) (tupleCancellationCore zeta a b) ≠ 0 := by
  let A := rootSupport zeta a
  let B := rootSupport zeta b
  have hAcard : A.card = r := rootSupport_card hprim ha hinja
  have hBcard : B.card = r := rootSupport_card hprim hb hinjb
  have hsumTuple : (∑ i, zeta ^ a i) = ∑ i, zeta ^ b i :=
    (sum_eq_iff_aeval_patternPolyG (ζ := zeta) (zeta_pow_m hm hprim) ha hb).2 heval
  have hsumSets : (∑ x ∈ A, x) = ∑ x ∈ B, x := by
    rw [sum_rootSupport hprim ha hinja, sum_rootSupport hprim hb hinjb]
    exact hsumTuple
  have hcard : (A \ B).card = (B \ A).card :=
    packet_card_sdiff_eq_card_sdiff (hAcard.trans hBcard.symm)
  have hlabel : signedPacketLabel (cyclotomicLift zeta m)
      (tupleCancellationCore zeta a b) ≠ 0 := by
    rw [tupleCancellationCore_label_eq_patternPolyG hprim ha hb hinja hinjb]
    exact hne
  have hnonempty : (A \ B).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hright : B \ A = ∅ := Finset.card_eq_zero.mp (by rw [← hcard, h]; rfl)
    apply hlabel
    simp [signedPacketLabel, tupleCancellationCore, A, B, h, hright]
  refine ⟨⟨hnonempty, hcard, packet_disjoint_sdiff_sdiff A B,
    packet_sum_sdiff_eq_sum_sdiff hsumSets⟩, ?_, hlabel⟩
  change (A \ B).card ≤ r
  rw [← hAcard]
  exact Finset.card_le_card Finset.sdiff_subset

/-- **G153 capstone.** Every injective depth-seven FS11 wraparound configuration decomposes into
at most three primitive balanced packets, with between one and three nonzero cyclotomic leaves.
In particular a primitive characteristic-`p` packet with nonzero characteristic-zero lift exists. -/
theorem injective_depthSeven_wraparound_primitive_charge
    {zeta : F} {m : ℕ} (hm : 0 < m) (hprim : IsPrimitiveRoot zeta (2 * m))
    {a b : Fin 7 → ℕ} (ha : ∀ i, a i < 2 * m) (hb : ∀ i, b i < 2 * m)
    (hinja : Function.Injective a) (hinjb : Function.Injective b)
    (hne : patternPolyG m a b ≠ 0) (heval : aeval zeta (patternPolyG m a b) = 0) :
    ∃ T : PrimitivePacketTree (tupleCancellationCore zeta a b),
      1 ≤ nonzeroLeafCount (cyclotomicLift zeta m) T ∧
      nonzeroLeafCount (cyclotomicLift zeta m) T ≤ T.leafCount ∧
      T.leafCount ≤ 3 ∧
      ∃ d : Finset F × Finset F,
        IsPrimitiveBalancedCore d ∧
          signedPacketLabel (cyclotomicLift zeta m) d ≠ 0 := by
  obtain ⟨hbal, hdepth, hlabel⟩ :=
    tupleCancellationCore_balanced hm hprim ha hb hinja hinjb hne heval
  obtain ⟨T⟩ := exists_primitivePacketTree _ hbal
  have hbetween := nonzeroLeafCount_between_one_and_three
    (cyclotomicLift zeta m) T hdepth hlabel
  have hcharge := nonzeroLeafCount_le_leafCount (cyclotomicLift zeta m) T
  have htwo := two_mul_leafCount_le_rootDepth T
  have hleafThree : T.leafCount ≤ 3 := by omega
  exact ⟨T, hbetween.1, hcharge, hleafThree,
    exists_primitive_leaf_label_ne_zero (cyclotomicLift zeta m) T hlabel⟩

/-- Finset-membership form of the capstone, directly consumable by the injective summand in the
exact FS11 multiplicity partition. -/
theorem mem_injectiveDepthSevenWraparound_has_primitive_charge
    {zeta : F} {m : ℕ} (hm : 0 < m) (hprim : IsPrimitiveRoot zeta (2 * m))
    {ab : (Fin 7 → ℕ) × (Fin 7 → ℕ)}
    (hab : ab ∈ injectiveWraparoundPairs zeta m 7) :
    ∃ T : PrimitivePacketTree (tupleCancellationCore zeta ab.1 ab.2),
      1 ≤ nonzeroLeafCount (cyclotomicLift zeta m) T ∧
      nonzeroLeafCount (cyclotomicLift zeta m) T ≤ T.leafCount ∧
      T.leafCount ≤ 3 ∧
      ∃ d : Finset F × Finset F,
        IsPrimitiveBalancedCore d ∧ signedPacketLabel (cyclotomicLift zeta m) d ≠ 0 := by
  obtain ⟨ha, hb, hne, heval, hinja, hinjb⟩ := mem_injectiveWraparoundExcessG_set hab
  exact injective_depthSeven_wraparound_primitive_charge hm hprim ha hb hinja hinjb hne heval

/-- A chosen primitive-packet tree for every injective depth-seven wraparound configuration. -/
noncomputable def injectivePacketTree {zeta : F} {m : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot zeta (2 * m))
    (ab : ↑(injectiveWraparoundPairs zeta m 7)) :
    PrimitivePacketTree (tupleCancellationCore zeta ab.1.1 ab.1.2) :=
  Classical.choose (mem_injectiveDepthSevenWraparound_has_primitive_charge hm hprim ab.2)

theorem injectivePacketTree_spec {zeta : F} {m : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot zeta (2 * m))
    (ab : ↑(injectiveWraparoundPairs zeta m 7)) :
    1 ≤ nonzeroLeafCount (cyclotomicLift zeta m) (injectivePacketTree hm hprim ab) ∧
    nonzeroLeafCount (cyclotomicLift zeta m) (injectivePacketTree hm hprim ab) ≤
      (injectivePacketTree hm hprim ab).leafCount ∧
    (injectivePacketTree hm hprim ab).leafCount ≤ 3 := by
  have hs := Classical.choose_spec
    (mem_injectiveDepthSevenWraparound_has_primitive_charge hm hprim ab.2)
  exact ⟨hs.1, hs.2.1, hs.2.2.1⟩

/-- Total nonzero primitive-leaf incidence mass across the injective depth-seven sector. -/
noncomputable def injectivePrimitiveChargeMass {zeta : F} {m : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot zeta (2 * m)) : ℕ :=
  ∑ ab : ↑(injectiveWraparoundPairs zeta m 7),
    nonzeroLeafCount (cyclotomicLift zeta m) (injectivePacketTree hm hprim ab)

/-- **Sharp limitation of the packet-existence reduction.** Without an incidence-multiplicity
estimate, the primitive charge is only a factor-three re-encoding of the original injective
wraparound census.  In particular leaf existence alone supplies no `n⁷` or field-size saving. -/
theorem injectivePrimitiveChargeMass_sandwich {zeta : F} {m : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot zeta (2 * m)) :
    injectiveWraparoundExcessG zeta m 7 ≤ injectivePrimitiveChargeMass hm hprim ∧
      injectivePrimitiveChargeMass hm hprim ≤ 3 * injectiveWraparoundExcessG zeta m 7 := by
  constructor
  · have hsum : (∑ _ab : ↑(injectiveWraparoundPairs zeta m 7), 1) ≤
        ∑ ab : ↑(injectiveWraparoundPairs zeta m 7),
          nonzeroLeafCount (cyclotomicLift zeta m) (injectivePacketTree hm hprim ab) := by
      exact Finset.sum_le_sum fun ab _ => (injectivePacketTree_spec hm hprim ab).1
    simpa [injectiveWraparoundExcessG, injectivePrimitiveChargeMass] using hsum
  · have hsum :
        (∑ ab : ↑(injectiveWraparoundPairs zeta m 7),
          nonzeroLeafCount (cyclotomicLift zeta m) (injectivePacketTree hm hprim ab)) ≤
        ∑ _ab : ↑(injectiveWraparoundPairs zeta m 7), 3 := by
      apply Finset.sum_le_sum
      intro ab _
      exact (injectivePacketTree_spec hm hprim ab).2.1.trans
        (injectivePacketTree_spec hm hprim ab).2.2
    simpa [injectiveWraparoundExcessG, injectivePrimitiveChargeMass, Nat.mul_comm] using hsum

#print axioms signedPacketLabel_split
#print axioms leafLabelSum_eq_root
#print axioms exists_primitive_leaf_label_ne_zero
#print axioms nonzeroLeafCount_between_one_and_three
#print axioms tupleCancellationCore_label_eq_patternPolyG
#print axioms tupleCancellationCore_balanced
#print axioms wraparoundExcessG_eq_injective_add_repeated
#print axioms injective_depthSeven_wraparound_primitive_charge
#print axioms mem_injectiveDepthSevenWraparound_has_primitive_charge
#print axioms injectivePrimitiveChargeMass_sandwich

end CyclotomicLift

end ArkLib.ProximityGap.Frontier.G153FS11PrimitivePacketNonzeroCharge

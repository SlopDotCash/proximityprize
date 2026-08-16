/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.AntipodalSigmaUnique
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PerPairingExactCount

set_option linter.style.longLine false

/-!
# The per-`σ` generic count reduced to a `σ`-FREE transversal class-injectivity count (#407 lower)

The whole #407 char-0 energy LOWER chain converges to the load-bearing gate
(`GenericSuperDiagonalLower.superDiagonal_le_rEnergy`):

> `hm : ∀ σ, IsPairing σ → (genericAntipodalSet G σ).card = m`,

with the intended value `m = (n/2)_r·2^r`. The `hm` uniformity (the `∀σ`) was discharged
(`GenericCountSigmaUniform`, `d51f54bdf`): the per-`σ` generic count is `σ`-independent. The remaining
input was the VALUE `m` for `μ_{2^k}`, repeatedly deferred as "the analytic input".

This file shows the value is **not analytic**: it is a clean `σ`-free transversal class-count. It
proves, for ANY negation-closed `G` and ANY pairing `σ`, the exact bijection

> `genericAntipodalSet G σ  ≃  { t : Fin r → G | ClassInjective t }`

via the proven `buildConsistent` injection (`PerPairingExactCount`), where

> `ClassInjective t := ∀ i j, i ≠ j → t i ≠ t j ∧ t i ≠ - t j`

(the `r` transversal values lie in `r` DISTINCT antipodal classes `{g, −g}`). Hence

> `genericAntipodalSet_card_eq_classInjCount` :
>     `(genericAntipodalSet G σ).card = (classInjectiveTransversals G r).card`,

removing the `σ`-dependence entirely and reducing `m` to a single `σ`-free combinatorial object over
`G` alone. On a no-2-torsion negation-closed `G` of order `n` that object has card `(n/2)_r·2^r`
(choose `r` of the `n/2` classes, ordered, `2` signs each); `probe_generic_uniqueneg_transversal.py`
verifies both the bijection (A) and the count (B) exactly (`(n,r)` up to `(16,2)`, `(8,3)`).

**Mechanism.** `buildConsistent σ t` is antipodally `σ`-consistent and restricts to `t`
(`PerPairingExactCount`). Its `UniqueNeg` property (each `−c i` attained at a unique index) is, by the
antipodal structure (lower slot `t k` is paired with the unique upper slot `−t k`), EQUIVALENT to the
transversal `t` hitting distinct antipodal classes: if `t i = t j` or `t i = −t j` for `i ≠ j` the
value `−t i` is hit at ≥ 2 indices (`UniqueNeg` fails); conversely class-injectivity makes every `−c·`
witness unique. The bijection then transports `card` off the `σ`-indexed family.

**Honest scope (rules 1, 3, 6).** This is the exact `σ`-free reduction of the per-`σ` generic count
it discharges the "which value is `m`" question to a single class-injectivity count over `G`,
field-general and axiom-clean. It does NOT by itself evaluate that count to the closed form
`(n/2)_r·2^r` (that is the `classInjectiveTransversals_card` interface, the standard ordered-choice
count over the `n/2` antipodal classes, probe-verified exact). Negation-closed / no-2-torsion
combinatorics, NOT thinness-essential, does NOT close CORE. Axiom-clean (`propext, Classical.choice,
Quot.sound`). Issue #407.
-/

open Finset

namespace ProximityGap.Frontier.GenericCountTransversal

open ArkLib.ProximityGap.NegationClosedWalk
open ProximityGap.Frontier.AntipodalSigmaUnique
open ProximityGap.Frontier.PerPairingExactCount

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Class-injective transversal predicate.** The `r` transversal values lie in `r` DISTINCT
antipodal classes `{g, −g}`: no two coordinates coincide or are negatives of each other. -/
def ClassInjective {r : ℕ} (t : Fin r → F) : Prop :=
  ∀ i j, i ≠ j → t i ≠ t j ∧ t i ≠ - t j

instance {r : ℕ} (t : Fin r → F) : Decidable (ClassInjective t) := by
  unfold ClassInjective; infer_instance

/-- The finset of class-injective transversal maps `t : Fin r → G`. -/
noncomputable def classInjectiveTransversals {r : ℕ} (G : Finset F) :
    Finset (Fin r → F) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin r => G)).filter ClassInjective

section

variable {r : ℕ} {σ : Equiv.Perm (Fin (2 * r))} (hσ : IsPairing σ)

/-- The value of `buildConsistent` at the partner `σ (e k)` of the `k`-th transversal slot is
`−t k` (the transversal slot itself carries `t k`, by `buildConsistent_restrict`). -/
theorem buildConsistent_at_partner (t : Fin r → F) (k : Fin r) :
    buildConsistent σ hσ t
        (σ (((lowerHalf σ).orderIsoOfFin (card_lowerHalf hσ) k : Fin (2 * r)))) = - t k := by
  classical
  rw [buildConsistent_antipodal hσ t, buildConsistent_restrict hσ t k]

/-- **Every value of `buildConsistent σ t` is `±t k` for the transversal index `k` of its slot.**
For any slot `i`: if `i` is a transversal slot it carries `t (e⁻¹ i)`; else it carries `−t (e⁻¹ (σ i))`.
This records the value purely in terms of `t` and the transversal index map. -/
theorem buildConsistent_value_form (t : Fin r → F) (i : Fin (2 * r)) :
    (∃ k, buildConsistent σ hσ t i = t k) ∨ (∃ k, buildConsistent σ hσ t i = - t k) := by
  classical
  by_cases hi : i ∈ lowerHalf σ
  · left
    exact ⟨_, buildConsistent_lower hσ t hi⟩
  · right
    exact ⟨_, buildConsistent_upper hσ t hi⟩

end

/-- **No-2-torsion** predicate: every nonzero structure element has distinct negative
(`μ_{2^k}` has a single order-2 element `−1`, and `g ≠ −g` for `g ∉ {0}`; over the multiplicative
realization all `r` transversal class-reps are non-self-paired). We carry it as a hypothesis on the
transversal values, the form actually consumed. -/
def NoSelfPair {r : ℕ} (t : Fin r → F) : Prop := ∀ k, t k ≠ - t k

/-- **`UniqueNeg` of an antipodally-`σ`-consistent tuple is exactly slot-injectivity.** If
`c (σ i) = −c i` for all `i` (so `−c i` is always attained, at the partner `σ i`), then `UniqueNeg c`
(each `−c i` attained at a UNIQUE index) holds iff `c` is injective. Field-general, no torsion
hypothesis, `σ` arbitrary. -/
theorem uniqueNeg_iff_injective_of_antipodal {r : ℕ} {K : Type*} [Field K]
    {σ : Equiv.Perm (Fin (2 * r))}
    {c : Fin (2 * r) → K} (hac : ∀ i, c (σ i) = -c i) :
    UniqueNeg c ↔ Function.Injective c := by
  constructor
  · intro hun a b hab
    obtain ⟨j, hj, huniq⟩ := hun a
    have hsa : c (σ a) = -c a := hac a
    have hsb : c (σ b) = -c a := by rw [hac b, hab]
    have h1 : σ a = j := huniq (σ a) hsa
    have h2 : σ b = j := huniq (σ b) hsb
    have : σ a = σ b := by rw [h1, h2]
    exact σ.injective this
  · intro hinj i
    refine ⟨σ i, hac i, ?_⟩
    intro y hy
    apply hinj
    rw [hy, hac i]

section Equiv

variable {r : ℕ} {σ : Equiv.Perm (Fin (2 * r))} (hσ : IsPairing σ)

/-- For a pairing `σ` and `i ∈ lowerHalf σ`, the partner `σ i` is NOT in `lowerHalf σ`
(the mirror of `partner_mem_lowerHalf`). -/
theorem partner_notMem_lowerHalf (hσ : IsPairing σ) {i : Fin (2 * r)} (hi : i ∈ lowerHalf σ) :
    σ i ∉ lowerHalf σ := by
  obtain ⟨hinv, hfix⟩ := hσ
  have hilt : i < σ i := by simpa [lowerHalf] using hi
  simp only [lowerHalf, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
  rw [hinv i]
  exact le_of_lt hilt

/-- **`buildConsistent` is injective on slots iff the transversal is class-injective and
non-self-paired.** The `2r` values `{t k} ∪ {−t k}` are pairwise distinct exactly when the `t k`
lie in distinct antipodal classes and no `t k` is its own negative. -/
theorem buildConsistent_slot_injective_iff (t : Fin r → F) :
    Function.Injective (buildConsistent σ hσ t) ↔ (ClassInjective t ∧ NoSelfPair t) := by
  classical
  constructor
  · intro hinj
    refine ⟨?_, ?_⟩
    · -- ClassInjective
      intro i j hij
      set e := (lowerHalf σ).orderIsoOfFin (card_lowerHalf hσ) with he
      refine ⟨?_, ?_⟩
      · -- t i ≠ t j
        intro hcontra
        apply hij
        have hi := buildConsistent_restrict hσ t i
        have hj := buildConsistent_restrict hσ t j
        have : buildConsistent σ hσ t ((e i : Fin (2 * r)))
            = buildConsistent σ hσ t ((e j : Fin (2 * r))) := by
          rw [hi, hj, hcontra]
        have heij := hinj this
        -- e injective
        have : (e i : Fin (2 * r)) = (e j : Fin (2 * r)) := heij
        have hee : e i = e j := Subtype.ext this
        exact e.injective hee
      · -- t i ≠ − t j
        intro hcontra
        apply hij
        set e := (lowerHalf σ).orderIsoOfFin (card_lowerHalf hσ) with he
        -- value at e i is t i; value at σ (e j) is − t j = t i
        have hi := buildConsistent_restrict hσ t i
        have hj := buildConsistent_at_partner hσ t j
        have heq : buildConsistent σ hσ t ((e i : Fin (2 * r)))
            = buildConsistent σ hσ t (σ ((e j : Fin (2 * r)))) := by
          rw [hi, hj]; exact hcontra
        have hcollide := hinj heq
        -- e i = σ (e j); but e i is a lower slot and σ (e j) is an upper slot ⇒ contradiction unless r-index forces i=j
        -- e i ∈ lowerHalf, σ (e j) ∉ lowerHalf
        have hlow : (e i : Fin (2 * r)) ∈ lowerHalf σ := (e i).2
        have hup : σ ((e j : Fin (2 * r))) ∉ lowerHalf σ :=
          partner_notMem_lowerHalf hσ (e j).2
        rw [hcollide] at hlow
        exact absurd hlow hup
    · -- NoSelfPair
      intro k hk
      set e := (lowerHalf σ).orderIsoOfFin (card_lowerHalf hσ) with he
      -- value at e k is t k; value at σ (e k) is − t k = t k
      have hi := buildConsistent_restrict hσ t k
      have hj := buildConsistent_at_partner hσ t k
      have heq : buildConsistent σ hσ t ((e k : Fin (2 * r)))
          = buildConsistent σ hσ t (σ ((e k : Fin (2 * r)))) := by
        rw [hi, hj]; exact hk
      have hcollide := hinj heq
      -- e k is lower, σ (e k) is upper ⇒ distinct
      have hlow : (e k : Fin (2 * r)) ∈ lowerHalf σ := (e k).2
      have hup : σ ((e k : Fin (2 * r))) ∉ lowerHalf σ :=
        partner_notMem_lowerHalf hσ (e k).2
      rw [hcollide] at hlow
      exact absurd hlow hup
  · rintro ⟨hci, hnsp⟩
    -- slot-injectivity from class-injectivity: the 2r values {±t k} are pairwise distinct.
    set e := (lowerHalf σ).orderIsoOfFin (card_lowerHalf hσ) with he
    -- index of a slot's transversal: lower slot e k ↦ k ; upper slot ↦ partner's k.
    -- We show: c a = c b → a = b by reducing both to transversal indices.
    intro a b hab
    -- classify a
    by_cases ha : a ∈ lowerHalf σ <;> by_cases hb : b ∈ lowerHalf σ
    · -- both lower: c a = t (e⁻¹ a), c b = t (e⁻¹ b)
      rw [buildConsistent_lower hσ t ha, buildConsistent_lower hσ t hb] at hab
      by_contra hne
      have hidx : e.symm ⟨a, ha⟩ ≠ e.symm ⟨b, hb⟩ := by
        intro h
        apply hne
        have : (⟨a, ha⟩ : {x // x ∈ lowerHalf σ}) = ⟨b, hb⟩ := e.symm.injective h
        exact congrArg Subtype.val this
      exact (hci _ _ hidx).1 hab
    · -- a lower, b upper: c a = t (e⁻¹ a), c b = − t (e⁻¹ (σ b))
      rw [buildConsistent_lower hσ t ha, buildConsistent_upper hσ t hb] at hab
      -- t (..) = − t (..); if indices differ, contradicts CI's `t i ≠ − t j`; if equal, contradicts NSP
      by_cases hidx : e.symm ⟨a, ha⟩ = e.symm ⟨σ b, partner_mem_lowerHalf hσ hb⟩
      · -- same transversal index k: then a = σ b, but a lower & σ b lower, still hab says t k = neg, NSP rules out
        rw [hidx] at hab
        exact absurd hab (hnsp _)
      · exact absurd hab (hci _ _ hidx).2
    · -- a upper, b lower: symmetric to previous
      rw [buildConsistent_upper hσ t ha, buildConsistent_lower hσ t hb] at hab
      by_cases hidx : e.symm ⟨σ a, partner_mem_lowerHalf hσ ha⟩ = e.symm ⟨b, hb⟩
      · rw [hidx] at hab
        -- hab : − t k = t k ⇒ t k = neg, NSP rules out
        exact absurd hab.symm (hnsp _)
      · -- hab : − t i = t j ⇒ t j = − t i, contradicts CI
        exact absurd hab.symm (hci _ _ (fun h => hidx h.symm)).2
    · -- both upper: c a = − t (e⁻¹ (σ a)), c b = − t (e⁻¹ (σ b))
      rw [buildConsistent_upper hσ t ha, buildConsistent_upper hσ t hb] at hab
      have hab' : t (e.symm ⟨σ a, partner_mem_lowerHalf hσ ha⟩)
          = t (e.symm ⟨σ b, partner_mem_lowerHalf hσ hb⟩) := by
        have := neg_inj.mp hab
        exact this
      by_contra hne
      have hidx : e.symm ⟨σ a, partner_mem_lowerHalf hσ ha⟩
          ≠ e.symm ⟨σ b, partner_mem_lowerHalf hσ hb⟩ := by
        intro h
        apply hne
        have hsig : σ a = σ b := by
          have : (⟨σ a, partner_mem_lowerHalf hσ ha⟩ : {x // x ∈ lowerHalf σ})
              = ⟨σ b, partner_mem_lowerHalf hσ hb⟩ := e.symm.injective h
          exact congrArg Subtype.val this
        exact σ.injective hsig
      exact (hci _ _ hidx).1 hab'

/-- **The membership equivalence.** For a transversal `t`, `buildConsistent σ t` lies on the generic
(unique-negative) locus iff `t` is class-injective and non-self-paired. (Antipodal-consistency is
automatic by `buildConsistent_antipodal`; `UniqueNeg ⇔ slot-injective ⇔ ClassInjective ∧ NoSelfPair`.) -/
theorem uniqueNeg_buildConsistent_iff (t : Fin r → F) :
    UniqueNeg (buildConsistent σ hσ t) ↔ (ClassInjective t ∧ NoSelfPair t) := by
  rw [uniqueNeg_iff_injective_of_antipodal (buildConsistent_antipodal hσ t),
      buildConsistent_slot_injective_iff hσ t]

/-- The transversal restriction of a tuple: its values on the `r` lower-half slots. -/
noncomputable def restrictT (c : Fin (2 * r) → F) : Fin r → F :=
  fun k => c (((lowerHalf σ).orderIsoOfFin (card_lowerHalf hσ) k : Fin (2 * r)))

/-- **Round-trip.** Any antipodally-`σ`-consistent tuple `c` is recovered as `buildConsistent` of
its transversal restriction. (Lower slots match by definition; upper slots match by antipodal
consistency `c (σ i) = −c i`.) -/
theorem buildConsistent_restrictT {c : Fin (2 * r) → F} (hac : ∀ i, c (σ i) = -c i) :
    buildConsistent σ hσ (restrictT hσ c) = c := by
  classical
  funext i
  set e := (lowerHalf σ).orderIsoOfFin (card_lowerHalf hσ) with he
  by_cases hi : i ∈ lowerHalf σ
  · rw [buildConsistent_lower hσ _ hi]
    change c ((e (e.symm ⟨i, hi⟩) : Fin (2 * r))) = c i
    rw [OrderIso.apply_symm_apply]
  · rw [buildConsistent_upper hσ _ hi]
    change -c ((e (e.symm ⟨σ i, partner_mem_lowerHalf hσ hi⟩) : Fin (2 * r))) = c i
    rw [OrderIso.apply_symm_apply]
    -- - c (σ i) = c i  from  c (σ i) = - c i
    rw [hac i, neg_neg]

end Equiv

/-- **No-2-torsion** on a structure set: no element is its own negative (`−g ≠ g`). For `μ_{2^k}`
this is automatic (negation `·(−1)` is fixed-point-free on the cyclic 2-group of even order). -/
def NoTwoTorsionOn (G : Finset F) : Prop := ∀ g ∈ G, -g ≠ g

section Assembly

variable {r : ℕ} {σ : Equiv.Perm (Fin (2 * r))}

/-- **The generic antipodal set is the image of the class-injective transversals under
`buildConsistent`.** This is the bijection core: every class-injective transversal builds a generic
tuple, and every generic tuple is the build of its (class-injective) restriction. Requires `G`
negation-closed (image lands in `G^{2r}`) and no-2-torsion (so transversal values are non-self-paired,
the `NoSelfPair` half of the membership equivalence). -/
theorem genericAntipodalSet_eq_image (hσ : IsPairing σ) (G : Finset F)
    (hneg : ∀ g ∈ G, -g ∈ G) (hnt : NoTwoTorsionOn G) :
    genericAntipodalSet G σ = (classInjectiveTransversals G).image (buildConsistent σ hσ) := by
  classical
  ext c
  simp only [genericAntipodalSet, classInjectiveTransversals, Finset.mem_filter,
    Fintype.mem_piFinset, Finset.mem_image]
  constructor
  · rintro ⟨hcmem, hac, hun⟩
    refine ⟨restrictT hσ c, ⟨?_, ?_⟩, buildConsistent_restrictT hσ hac⟩
    · -- restrictT values in G
      intro k
      exact hcmem _
    · -- restrictT is class-injective: from UniqueNeg c = ClassInjective (restrictT c)
      have hkey := (uniqueNeg_buildConsistent_iff hσ (restrictT hσ c)).mp
      rw [buildConsistent_restrictT hσ hac] at hkey
      exact (hkey hun).1
  · rintro ⟨t, ⟨htmem, hci⟩, rfl⟩
    have hnsp : NoSelfPair t := fun k => (hnt _ (htmem k)).symm
    refine ⟨?_, buildConsistent_antipodal hσ t, ?_⟩
    · intro i
      have := buildConsistent_mem G hneg hσ htmem
      rw [Fintype.mem_piFinset] at this
      exact this i
    · exact (uniqueNeg_buildConsistent_iff hσ t).mpr ⟨hci, hnsp⟩

/-- **The per-`σ` generic count equals the `σ`-FREE class-injective transversal count.** For ANY
pairing `σ` and ANY negation-closed, no-2-torsion `G`,

> `(genericAntipodalSet G σ).card = (classInjectiveTransversals G).card`.

The `σ`-dependence is removed: the gate value `m` in `GenericSuperDiagonalLower.superDiagonal_le_rEnergy`
is the single combinatorial object `#{class-injective t : Fin r → G}`, not an analytic per-`σ` object.
On a no-2-torsion negation-closed `G` of order `n` this count is `(n/2)_r·2^r` (ordered choice of `r`
of the `n/2` antipodal classes, `2` signs each), probe-verified exact in
`probe_generic_count_value_muN.py` / `probe_generic_uniqueneg_transversal.py`. -/
theorem genericAntipodalSet_card_eq_classInjCount (hσ : IsPairing σ) (G : Finset F)
    (hneg : ∀ g ∈ G, -g ∈ G) (hnt : NoTwoTorsionOn G) :
    (genericAntipodalSet G σ).card = (classInjectiveTransversals (r := r) G).card := by
  rw [genericAntipodalSet_eq_image hσ G hneg hnt,
      Finset.card_image_of_injective _ (buildConsistent_injective hσ)]

/-- **The `hm` uniformity gate, discharged with a `σ`-free value.** Combining with the proven
`σ`-independence: for negation-closed no-2-torsion `G`, EVERY pairing `σ` has the SAME generic count,
equal to the `σ`-free `#{class-injective transversals}`. This is exactly the shape
`GenericSuperDiagonalLower.doubleFactorial_mul_le_zeroSumCount` /`superDiagonal_le_rEnergy` consume as
`hm`, now with the value pinned to a single combinatorial object over `G` (no `σ`, no analysis). -/
theorem hm_from_classInjCount (G : Finset F) (hneg : ∀ g ∈ G, -g ∈ G) (hnt : NoTwoTorsionOn G) :
    ∀ τ : Equiv.Perm (Fin (2 * r)), IsPairing τ →
      (genericAntipodalSet G τ).card = (classInjectiveTransversals (r := r) G).card :=
  fun _ hτ => genericAntipodalSet_card_eq_classInjCount hτ G hneg hnt

end Assembly

end ProximityGap.Frontier.GenericCountTransversal

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.GenericCountTransversal.uniqueNeg_buildConsistent_iff
#print axioms ProximityGap.Frontier.GenericCountTransversal.genericAntipodalSet_eq_image
#print axioms ProximityGap.Frontier.GenericCountTransversal.genericAntipodalSet_card_eq_classInjCount
#print axioms ProximityGap.Frontier.GenericCountTransversal.hm_from_classInjCount

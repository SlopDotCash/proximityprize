/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G121DescentMatchingIdentity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G85EndpointAssemblyEquiv

/-!
# G123: the triangular moment ladder — every lower rung constrains the depth census

G121 proved the `m = 1` descent identity.  This file proves the whole ladder.  For
`matchCountM m (v, w) = #{(e₁, e₂) : (Fin m ↪ Fin r)² | ∀ t, v (e₁ t) = w (e₂ t)}` (ordered
`m`-matchings), the G84/G85 slot machinery bijects the fixed-embedding slice onto
(common core word) × (rung-`(r−m)` pair):

```text
Σ_{(v,w) equal-sum, rung r} matchCountM m = (r)_m² · #A^m · E_{r−m}(A)
Σ_{(v,w) all pairs,  rung r} matchCountM m = (r)_m² · #A^m · #A^{2(r−m)}
```

hence the signed `m`-moment of the depth measure equals `(r)_m² · #A^m` times the
rung-`(r−m)` global DC anomaly and is **nonnegative for every `m ≤ r` unconditionally**
(G95 floor) — the entire rung hierarchy below `r` acts as exact positivity constraints on the
rung-`r` signed depth census, with no sign law assumed and full immunity to the
`(64, 16778497, 5)` counterexample.

**Triangularity.**  An `m`-matching forces a common sub-multiset of size `m`
(`le_commonPart_card_of_matching`), so `matchCountM m` vanishes on all depths `> r − m`: the
`m`-th row of the ladder sees exactly depths `0..r−m` and is exactly determined by rung
`r − m`.  The fully-disjoint sector is invisible to every row `m ≥ 1` — it is the unique
sector carrying non-descent information, now pinned against the whole hierarchy.

**Honest scope.**  Exact identities and unconditional inequalities; no bound on the
fully-disjoint sector (the wall).  CORE remains OPEN.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G123TriangularMomentLadder

open Finset Fintype
open ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation
open ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G84AEndpointAssembly
open ArkLib.ProximityGap.Frontier.G84SCorePaddingSlotPartition
open ArkLib.ProximityGap.Frontier.G85EndpointAssemblyEquiv

variable {α : Type*} [DecidableEq α]

/-- The ordered `m`-matching count of a pair of `r`-tuples: pairs of injective position maps
along which the two words agree. -/
noncomputable def matchCountM (m : ℕ) {r : ℕ} (y : (Fin r → α) × (Fin r → α)) : ℕ :=
  #{ee ∈ (univ : Finset ((Fin m ↪ Fin r) × (Fin m ↪ Fin r))) |
      ∀ t, y.1 (ee.1 t) = y.2 (ee.2 t)}

section Identities

variable [AddCancelCommMonoid α]

/-- Any coordinate of an assembled word lies in `A` when core and padding are `A`-valued. -/
private theorem assemble_mem {r m : ℕ} (hsr : m ≤ r) (e : Fin m ↪ Fin r)
    {A : Finset α} {c : Fin m → α} {p : Fin (r - m) → α}
    (hc : ∀ t, c t ∈ A) (hp : ∀ t, p t ∈ A) (t : Fin r) :
    assemble hsr e c p t ∈ A := by
  cases h : (slotEquiv hsr e).symm t with
  | inl i =>
      have ht : t = e i := by
        have := congrArg (slotEquiv hsr e) h
        simpa using this
      subst ht
      rw [assemble_core]
      exact hc i
  | inr j =>
      have ht : t = padSlots hsr e j := by
        have := congrArg (slotEquiv hsr e) h
        simpa using this
      subst ht
      rw [assemble_pad]
      exact hp j

/-- The sum of a word splits as core sum plus padding sum. -/
private theorem sum_eq_core_add_pad {r m : ℕ} (hsr : m ≤ r) (e : Fin m ↪ Fin r)
    (v : Fin r → α) :
    ∑ t, v t = (∑ t, coreAt e v t) + ∑ t, paddingAt hsr e v t := by
  have h := ArkLib.ProximityGap.Frontier.G88EqualSumCorrectedDecoder.wordSum_assemble
    (ι := (id : α → α)) hsr e (coreAt e v) (paddingAt hsr e v)
  rw [assemble_coreAt_paddingAt] at h
  simpa [ArkLib.ProximityGap.Frontier.G88EqualSumCorrectedDecoder.wordSum] using h

/-- The fixed-embedding slice of the rung-`r` equal-sum set bijects onto
(common `A`-valued core word) × (rung-`(r−m)` equal-sum pairs). -/
theorem card_matchSliceM (A : Finset α) {r m : ℕ} (hsr : m ≤ r)
    (e₁ e₂ : Fin m ↪ Fin r) :
    #{y ∈ energySet A r | ∀ t, y.1 (e₁ t) = y.2 (e₂ t)}
      = A.card ^ m * Finset.addREnergy (r - m) A := by
  classical
  have key : #{y ∈ energySet A r | ∀ t, y.1 (e₁ t) = y.2 (e₂ t)}
      = #((piFinset fun _ : Fin m => A) ×ˢ energySet A (r - m)) := by
    refine Finset.card_bij'
      (fun y _ => (coreAt e₁ y.1, (paddingAt hsr e₁ y.1, paddingAt hsr e₂ y.2)))
      (fun z _ => (assemble hsr e₁ z.1 z.2.1, assemble hsr e₂ z.1 z.2.2))
      ?hi ?hj ?li ?ri
    case hi =>
      intro y hy
      have hy' := Finset.mem_filter.mp hy
      have hE := Finset.mem_filter.mp hy'.1
      have hprod := Finset.mem_product.mp hE.1
      have h1 : ∀ t, y.1 t ∈ A := fun t => Fintype.mem_piFinset.mp hprod.1 t
      have h2 : ∀ t, y.2 t ∈ A := fun t => Fintype.mem_piFinset.mp hprod.2 t
      have hsum : ∑ t, y.1 t = ∑ t, y.2 t := hE.2
      have hmatch : ∀ t, y.1 (e₁ t) = y.2 (e₂ t) := hy'.2
      refine Finset.mem_product.mpr
        ⟨Fintype.mem_piFinset.mpr (fun t => h1 _), ?_⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Fintype.mem_piFinset.mpr (fun t => h1 _),
          Fintype.mem_piFinset.mpr (fun t => h2 _)⟩, ?_⟩
      -- padding sums agree: cancel the matching core sums
      have hcore : ∀ t, coreAt e₁ y.1 t = coreAt e₂ y.2 t := fun t => hmatch t
      have hcoresum : ∑ t, coreAt e₁ y.1 t = ∑ t, coreAt e₂ y.2 t :=
        Finset.sum_congr rfl (fun t _ => hcore t)
      have d1 := sum_eq_core_add_pad hsr e₁ y.1
      have d2 := sum_eq_core_add_pad hsr e₂ y.2
      apply add_left_cancel (a := ∑ t, coreAt e₁ y.1 t)
      calc
        (∑ t, coreAt e₁ y.1 t) + ∑ t, paddingAt hsr e₁ y.1 t
            = ∑ t, y.1 t := d1.symm
        _ = ∑ t, y.2 t := hsum
        _ = (∑ t, coreAt e₂ y.2 t) + ∑ t, paddingAt hsr e₂ y.2 t := d2
        _ = (∑ t, coreAt e₁ y.1 t) + ∑ t, paddingAt hsr e₂ y.2 t := by
          rw [hcoresum]
    case hj =>
      intro z hz
      have hz' := Finset.mem_product.mp hz
      have hc : ∀ t, z.1 t ∈ A := fun t => Fintype.mem_piFinset.mp hz'.1 t
      have hzE := Finset.mem_filter.mp hz'.2
      have hzprod := Finset.mem_product.mp hzE.1
      have hp1 : ∀ t, z.2.1 t ∈ A := fun t => Fintype.mem_piFinset.mp hzprod.1 t
      have hp2 : ∀ t, z.2.2 t ∈ A := fun t => Fintype.mem_piFinset.mp hzprod.2 t
      have hzsum : ∑ t, z.2.1 t = ∑ t, z.2.2 t := hzE.2
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
      · exact Fintype.mem_piFinset.mpr (fun t => assemble_mem hsr e₁ hc hp1 t)
      · exact Fintype.mem_piFinset.mpr (fun t => assemble_mem hsr e₂ hc hp2 t)
      · -- assembled sums agree
        have d1 := sum_eq_core_add_pad hsr e₁ (assemble hsr e₁ z.1 z.2.1)
        have d2 := sum_eq_core_add_pad hsr e₂ (assemble hsr e₂ z.1 z.2.2)
        rw [d1, d2, coreAt_assemble, paddingAt_assemble, coreAt_assemble,
          paddingAt_assemble, hzsum]
      · intro t
        dsimp only
        rw [assemble_core, assemble_core]
    case li =>
      intro y hy
      have hy' := Finset.mem_filter.mp hy
      have hmatch : ∀ t, y.1 (e₁ t) = y.2 (e₂ t) := hy'.2
      have hcore : coreAt e₁ y.1 = coreAt e₂ y.2 := funext (fun t => hmatch t)
      have hfst : assemble hsr e₁ (coreAt e₁ y.1) (paddingAt hsr e₁ y.1) = y.1 :=
        assemble_coreAt_paddingAt hsr e₁ y.1
      have hsnd : assemble hsr e₂ (coreAt e₁ y.1) (paddingAt hsr e₂ y.2) = y.2 := by
        rw [hcore]
        exact assemble_coreAt_paddingAt hsr e₂ y.2
      exact Prod.ext hfst hsnd
    case ri =>
      intro z hz
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact coreAt_assemble hsr e₁ z.1 z.2.1
      · exact paddingAt_assemble hsr e₁ z.1 z.2.1
      · exact paddingAt_assemble hsr e₂ z.1 z.2.2
  rw [key, Finset.card_product, card_piFinset_const, card_energySet]

/-- The population analogue of the fixed-embedding slice. -/
theorem card_matchSliceM_cube (A : Finset α) {r m : ℕ} (hsr : m ≤ r)
    (e₁ e₂ : Fin m ↪ Fin r) :
    #{y ∈ (piFinset fun _ : Fin r => A) ×ˢ (piFinset fun _ : Fin r => A) |
        ∀ t, y.1 (e₁ t) = y.2 (e₂ t)}
      = A.card ^ m * (A.card ^ (r - m) * A.card ^ (r - m)) := by
  classical
  have key : #{y ∈ (piFinset fun _ : Fin r => A) ×ˢ (piFinset fun _ : Fin r => A) |
        ∀ t, y.1 (e₁ t) = y.2 (e₂ t)}
      = #((piFinset fun _ : Fin m => A) ×ˢ
          ((piFinset fun _ : Fin (r - m) => A) ×ˢ (piFinset fun _ : Fin (r - m) => A))) := by
    refine Finset.card_bij'
      (fun y _ => (coreAt e₁ y.1, (paddingAt hsr e₁ y.1, paddingAt hsr e₂ y.2)))
      (fun z _ => (assemble hsr e₁ z.1 z.2.1, assemble hsr e₂ z.1 z.2.2))
      ?hi ?hj ?li ?ri
    case hi =>
      intro y hy
      have hy' := Finset.mem_filter.mp hy
      have hprod := Finset.mem_product.mp hy'.1
      have h1 : ∀ t, y.1 t ∈ A := fun t => Fintype.mem_piFinset.mp hprod.1 t
      have h2 : ∀ t, y.2 t ∈ A := fun t => Fintype.mem_piFinset.mp hprod.2 t
      exact Finset.mem_product.mpr
        ⟨Fintype.mem_piFinset.mpr (fun t => h1 _), Finset.mem_product.mpr
          ⟨Fintype.mem_piFinset.mpr (fun t => h1 _),
            Fintype.mem_piFinset.mpr (fun t => h2 _)⟩⟩
    case hj =>
      intro z hz
      have hz' := Finset.mem_product.mp hz
      have hc : ∀ t, z.1 t ∈ A := fun t => Fintype.mem_piFinset.mp hz'.1 t
      have hz2' := Finset.mem_product.mp hz'.2
      have hp1 : ∀ t, z.2.1 t ∈ A := fun t => Fintype.mem_piFinset.mp hz2'.1 t
      have hp2 : ∀ t, z.2.2 t ∈ A := fun t => Fintype.mem_piFinset.mp hz2'.2 t
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Fintype.mem_piFinset.mpr (fun t => assemble_mem hsr e₁ hc hp1 t)
      · exact Fintype.mem_piFinset.mpr (fun t => assemble_mem hsr e₂ hc hp2 t)
      · intro t
        dsimp only
        rw [assemble_core, assemble_core]
    case li =>
      intro y hy
      have hy' := Finset.mem_filter.mp hy
      have hmatch : ∀ t, y.1 (e₁ t) = y.2 (e₂ t) := hy'.2
      have hcore : coreAt e₁ y.1 = coreAt e₂ y.2 := funext (fun t => hmatch t)
      have hfst : assemble hsr e₁ (coreAt e₁ y.1) (paddingAt hsr e₁ y.1) = y.1 :=
        assemble_coreAt_paddingAt hsr e₁ y.1
      have hsnd : assemble hsr e₂ (coreAt e₁ y.1) (paddingAt hsr e₂ y.2) = y.2 := by
        rw [hcore]
        exact assemble_coreAt_paddingAt hsr e₂ y.2
      exact Prod.ext hfst hsnd
    case ri =>
      intro z hz
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact coreAt_assemble hsr e₁ z.1 z.2.1
      · exact paddingAt_assemble hsr e₁ z.1 z.2.1
      · exact paddingAt_assemble hsr e₂ z.1 z.2.2
  rw [key, Finset.card_product, Finset.card_product, card_piFinset_const,
    card_piFinset_const]

/-- **Triangular ladder (equal-sum side).**  The `m`-th matching moment over the rung-`r`
equal-sum set equals `(r)_m² · #A^m · E_{r−m}(A)`. -/
theorem sum_matchCountM_energySet (A : Finset α) {r m : ℕ} (hsr : m ≤ r) :
    ∑ y ∈ energySet A r, matchCountM m y
      = (r.descFactorial m) ^ 2 * (A.card ^ m * Finset.addREnergy (r - m) A) := by
  classical
  have hswap : ∑ y ∈ energySet A r, matchCountM m y
      = ∑ ee ∈ (univ : Finset ((Fin m ↪ Fin r) × (Fin m ↪ Fin r))),
          #{y ∈ energySet A r | ∀ t, y.1 (ee.1 t) = y.2 (ee.2 t)} := by
    unfold matchCountM
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap,
    Finset.sum_congr rfl (fun ee _ => card_matchSliceM A hsr ee.1 ee.2),
    Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin,
    smul_eq_mul, ← sq]

/-- **Triangular ladder (population side).** -/
theorem sum_matchCountM_cube (A : Finset α) {r m : ℕ} (hsr : m ≤ r) :
    ∑ y ∈ (piFinset fun _ : Fin r => A) ×ˢ (piFinset fun _ : Fin r => A),
        matchCountM m y
      = (r.descFactorial m) ^ 2 *
          (A.card ^ m * (A.card ^ (r - m) * A.card ^ (r - m))) := by
  classical
  have hswap : ∑ y ∈ (piFinset fun _ : Fin r => A) ×ˢ (piFinset fun _ : Fin r => A),
        matchCountM m y
      = ∑ ee ∈ (univ : Finset ((Fin m ↪ Fin r) × (Fin m ↪ Fin r))),
          #{y ∈ (piFinset fun _ : Fin r => A) ×ˢ (piFinset fun _ : Fin r => A) |
              ∀ t, y.1 (ee.1 t) = y.2 (ee.2 t)} := by
    unfold matchCountM
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap,
    Finset.sum_congr rfl (fun ee _ => card_matchSliceM_cube A hsr ee.1 ee.2),
    Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin,
    smul_eq_mul, ← sq]

end Identities

/-! ## The unconditional ladder positivity -/

section Transfer

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Ladder anomaly transfer.**  For every `m ≤ r`, the signed `m`-th matching moment of the
rung-`r` depth measure equals `(r)_m² · #A^m` times the rung-`(r−m)` global DC anomaly. -/
theorem ladder_anomaly_transfer (A : Finset F) {r m : ℕ} (hsr : m ≤ r) :
    (Fintype.card F : ℤ) * ∑ y ∈ energySet A r, (matchCountM m y : ℤ)
        - ∑ y ∈ (piFinset fun _ : Fin r => A) ×ˢ (piFinset fun _ : Fin r => A),
            (matchCountM m y : ℤ)
      = (r.descFactorial m) ^ 2 * (A.card : ℤ) ^ m *
          ((Fintype.card F : ℤ) * Finset.addREnergy (r - m) A
            - (A.card : ℤ) ^ (2 * (r - m))) := by
  have h1 := sum_matchCountM_energySet A hsr
  have h2 := sum_matchCountM_cube A hsr
  have h1' : ∑ y ∈ energySet A r, (matchCountM m y : ℤ)
      = ((r.descFactorial m) ^ 2 * (A.card ^ m * Finset.addREnergy (r - m) A) : ℕ) := by
    rw [← h1]; push_cast; rfl
  have h2' : ∑ y ∈ (piFinset fun _ : Fin r => A) ×ˢ (piFinset fun _ : Fin r => A),
        (matchCountM m y : ℤ)
      = ((r.descFactorial m) ^ 2 *
          (A.card ^ m * (A.card ^ (r - m) * A.card ^ (r - m))) : ℕ) := by
    rw [← h2]; push_cast; rfl
  rw [h1', h2']
  push_cast
  have hpow : ((A.card : ℤ)) ^ (r - m) * (A.card : ℤ) ^ (r - m)
      = (A.card : ℤ) ^ (2 * (r - m)) := by
    rw [← pow_add]; congr 1; omega
  rw [← hpow]
  ring

/-- **Unconditional ladder positivity.**  Every row of the ladder is nonnegative at every
prime, every set, every rung — the G95 floor at rung `r − m`, transported. -/
theorem ladder_moment_nonneg (A : Finset F) {r m : ℕ} (hsr : m ≤ r) :
    0 ≤ (Fintype.card F : ℤ) * ∑ y ∈ energySet A r, (matchCountM m y : ℤ)
        - ∑ y ∈ (piFinset fun _ : Fin r => A) ×ˢ (piFinset fun _ : Fin r => A),
            (matchCountM m y : ℤ) := by
  rw [ladder_anomaly_transfer A hsr]
  apply mul_nonneg
  · positivity
  · have h := card_pow_le_card_mul_addREnergy (α := F) (r - m) A
    have : ((A.card : ℤ)) ^ (2 * (r - m))
        ≤ (Fintype.card F : ℤ) * Finset.addREnergy (r - m) A := by
      exact_mod_cast h
    omega

end Transfer

/-! ## Triangularity: deep sectors are invisible -/

section Invisibility

/-- The value bag as a multiset map over the position universe. -/
theorem valueBag_eq_map {r : ℕ} (v : Fin r → α) :
    valueBag v = Multiset.map v (Finset.univ : Finset (Fin r)).val := by
  unfold valueBag
  rw [List.ofFn_eq_map, ← Multiset.map_coe]
  rfl

/-- The marked values along an injective position map form a sub-multiset of the bag. -/
theorem marked_le_valueBag {r m : ℕ} (v : Fin r → α) (e : Fin m ↪ Fin r) :
    ((List.ofFn fun t => v (e t)) : Multiset α) ≤ valueBag v := by
  have hofn : ((List.ofFn fun t => v (e t)) : Multiset α)
      = Multiset.map v (Multiset.map (⇑e) (Finset.univ : Finset (Fin m)).val) := by
    rw [Multiset.map_map]
    exact valueBag_eq_map (fun t => v (e t))
  have hnodup : (Multiset.map (⇑e) (Finset.univ : Finset (Fin m)).val).Nodup :=
    Finset.univ.nodup.map e.injective
  have hsub : Multiset.map (⇑e) (Finset.univ : Finset (Fin m)).val ⊆
      (Finset.univ : Finset (Fin r)).val := by
    intro x _
    rw [Finset.mem_val]
    exact Finset.mem_univ x
  have hle : Multiset.map (⇑e) (Finset.univ : Finset (Fin m)).val
      ≤ (Finset.univ : Finset (Fin r)).val :=
    (Multiset.le_iff_subset hnodup).mpr hsub
  rw [hofn, valueBag_eq_map]
  exact Multiset.map_le_map hle

/-- **An `m`-matching forces a common sub-multiset of size `m`.**  The matched values (with
multiplicity) lie in both bags, hence in their intersection. -/
theorem le_commonPart_card_of_matching {r m : ℕ}
    (y : (Fin r → α) × (Fin r → α)) (e₁ e₂ : Fin m ↪ Fin r)
    (hmatch : ∀ t, y.1 (e₁ t) = y.2 (e₂ t)) :
    m ≤ (commonPart (valueBag y.1) (valueBag y.2)).card := by
  have h1 : ((List.ofFn fun t => y.1 (e₁ t)) : Multiset α) ≤ valueBag y.1 :=
    marked_le_valueBag y.1 e₁
  have hCw : ((List.ofFn fun t => y.1 (e₁ t)) : Multiset α)
      = ((List.ofFn fun t => y.2 (e₂ t)) : Multiset α) := by
    congr 1
    exact congrArg List.ofFn (funext hmatch)
  have h2 : ((List.ofFn fun t => y.1 (e₁ t)) : Multiset α) ≤ valueBag y.2 := by
    rw [hCw]
    exact marked_le_valueBag y.2 e₂
  have hint : ((List.ofFn fun t => y.1 (e₁ t)) : Multiset α)
      ≤ commonPart (valueBag y.1) (valueBag y.2) := by
    unfold commonPart
    exact Multiset.le_inter h1 h2
  have hcard := Multiset.card_le_card hint
  simpa using hcard

/-- **Triangularity / deep invisibility.**  The `m`-th matching moment vanishes on every pair
of cancellation depth exceeding `r − m`: rows of the ladder are blind to the deep sectors. -/
theorem matchCountM_eq_zero_of_lt_depth {r m : ℕ}
    (y : (Fin r → α) × (Fin r → α)) (h : r - m < cancelDepth y) :
    matchCountM m y = 0 := by
  unfold matchCountM
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨e₁, e₂⟩ _
  intro hmatch
  have hcm := le_commonPart_card_of_matching y e₁ e₂ hmatch
  have hrec := congrArg Multiset.card
    (left_reconstruct (valueBag y.1) (valueBag y.2))
  rw [Multiset.card_add] at hrec
  have hbag : (valueBag y.1).card = r := by simp [valueBag]
  unfold cancelDepth at h
  omega

end Invisibility

end ArkLib.ProximityGap.Frontier.G123TriangularMomentLadder

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G123TriangularMomentLadder.card_matchSliceM
#print axioms ArkLib.ProximityGap.Frontier.G123TriangularMomentLadder.card_matchSliceM_cube
#print axioms
  ArkLib.ProximityGap.Frontier.G123TriangularMomentLadder.sum_matchCountM_energySet
#print axioms ArkLib.ProximityGap.Frontier.G123TriangularMomentLadder.sum_matchCountM_cube
#print axioms
  ArkLib.ProximityGap.Frontier.G123TriangularMomentLadder.ladder_anomaly_transfer
#print axioms ArkLib.ProximityGap.Frontier.G123TriangularMomentLadder.ladder_moment_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.G123TriangularMomentLadder.le_commonPart_card_of_matching
#print axioms
  ArkLib.ProximityGap.Frontier.G123TriangularMomentLadder.matchCountM_eq_zero_of_lt_depth

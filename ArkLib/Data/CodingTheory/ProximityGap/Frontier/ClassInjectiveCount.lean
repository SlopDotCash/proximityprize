/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.GenericCountTransversal
import Mathlib.Tactic

/-!
# Closed form for the class-injective transversal count (#407 lower, completes the `hm` value)

`GenericCountTransversal.genericAntipodalSet_card_eq_classInjCount` reduced the `hm` gate value to the
`σ`-free count `#{ t : Fin r → G | ClassInjective t }`. On a no-2-torsion negation-closed `G` of order
`n` this count is `2^r · (n/2)_r = ∏_{i<r} (n − 2i)` — ordered choice of `r` of the `n/2` antipodal
classes, with `2` signs each. This file proves the closed form via the clean uniform recursion

> `#CI(r) = #CI(r−1) · (n − 2(r−1))`

(probe `probe_classinj_recursion.py`: each class-injective prefix of length `r−1` extends by a value
avoiding the `2(r−1)` excluded class-reps `{t k, −t k}`, a UNIFORM count `n − 2(r−1)`).

**Honest scope.** This is the final combinatorial evaluation of the `σ`-free count isolated by
`genericAntipodalSet_card_eq_classInjCount`. Negation-closed / no-2-torsion combinatorics, NOT
thinness-essential, does NOT close CORE. Axiom-clean. Issue #407.
-/

set_option linter.style.longLine false


open Finset

namespace ProximityGap.Frontier.ClassInjectiveCount

open ProximityGap.Frontier.GenericCountTransversal
open ProximityGap.Frontier.AntipodalSigmaUnique
open ArkLib.ProximityGap.NegationClosedWalk

variable {F : Type*} [Field F] [DecidableEq F]

/-- The set of class-reps blocked by a class-injective prefix `t : Fin r → F`: the `2r` values
`{t k, −t k}`. On a no-2-torsion class-injective `t` these are pairwise distinct, so `#blocked = 2r`. -/
noncomputable def blocked {r : ℕ} (t : Fin r → F) : Finset F :=
  (Finset.univ.image t) ∪ (Finset.univ.image (fun k => - t k))

/-- On a no-2-torsion class-injective prefix, the blocked set has card exactly `2r`: the `r` values
`t k` are distinct (class-injectivity), the `r` negatives `−t k` are distinct, and no `t k` equals any
`−t l` (class-injectivity for `k ≠ l`, no-2-torsion for `k = l`). -/
theorem blocked_card {r : ℕ} {t : Fin r → F} (hci : ClassInjective t)
    (hnsp : NoSelfPair t) : (blocked t).card = 2 * r := by
  classical
  -- t injective
  have htinj : Function.Injective t := by
    intro a b hab
    by_contra hne
    exact (hci a b hne).1 hab
  -- (fun k => -t k) injective
  have hninj : Function.Injective (fun k => - t k) := by
    intro a b hab
    by_contra hne
    simp only at hab
    exact (hci a b hne).1 (neg_injective hab)
  -- the two images are disjoint: t k = -t l impossible (k≠l by CI, k=l by NSP)
  have hdisj : Disjoint (Finset.univ.image t) (Finset.univ.image (fun k => - t k)) := by
    rw [Finset.disjoint_left]
    rintro x hx hx'
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hx'
    by_cases hab : a = b
    · subst hab
      exact hnsp a (hb.symm)
    · exact (hci a b hab).2 hb.symm
  rw [blocked, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ htinj,
      Finset.card_image_of_injective _ hninj,
      Finset.card_univ, Fintype.card_fin]
  ring

/-- The closed-form product `∏_{i<r} (n − 2i) = 2^r · (n/2)_r`. We state it as the descending product
`descFactorTwo n r` to drive the induction without rational arithmetic. -/
def descFactorTwo (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | (r + 1) => descFactorTwo n r * (n - 2 * r)

/-- A class-injective prefix `t : Fin r → G` (values in `G`) leaves exactly `n − 2r` admissible
extension values in `G` (those outside `blocked t`), on a no-2-torsion `G` (so `blocked t ⊆ G` with
card `2r`). -/
theorem admissible_card {r : ℕ} {G : Finset F} {t : Fin r → F}
    (hmem : ∀ k, t k ∈ G) (hci : ClassInjective t) (hnsp : NoSelfPair t)
    (hneg : ∀ g ∈ G, -g ∈ G) :
    (G \ blocked t).card = G.card - 2 * r := by
  classical
  have hsub : blocked t ⊆ G := by
    intro x hx
    rw [blocked, Finset.mem_union] at hx
    rcases hx with hx | hx
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx; exact hmem k
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx; exact hneg _ (hmem k)
  rw [Finset.card_sdiff_of_subset hsub, blocked_card hci hnsp]

/-- **Snoc characterization.** Appending `v` to a tuple `t : Fin r → F` (via `Fin.snoc`) yields a
class-injective `(r+1)`-tuple iff `t` is class-injective and `v` avoids `blocked t` (i.e. `v` is in a
fresh antipodal class, `v ≠ t k` and `v ≠ −t k` for all `k`). -/
theorem classInjective_snoc {r : ℕ} {t : Fin r → F} {v : F} :
    ClassInjective (Fin.snoc t v : Fin (r + 1) → F) ↔
      (ClassInjective t ∧ v ∉ blocked t) := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · -- restriction to Fin r is class-injective
      intro i j hij
      have hij' : (i.castSucc) ≠ (j.castSucc) := by
        simp [Fin.castSucc_inj, hij]
      have := h i.castSucc j.castSucc hij'
      rwa [Fin.snoc_castSucc, Fin.snoc_castSucc] at this
    · -- v ∉ blocked t
      intro hv
      rw [blocked, Finset.mem_union] at hv
      rcases hv with hv | hv
      · obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hv
        have hne : (Fin.last r) ≠ k.castSucc := by
          exact (Fin.castSucc_lt_last k).ne'
        have := (h (Fin.last r) k.castSucc hne).1
        rw [Fin.snoc_last, Fin.snoc_castSucc] at this
        exact this hk.symm
      · obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hv
        have hne : (Fin.last r) ≠ k.castSucc := (Fin.castSucc_lt_last k).ne'
        have := (h (Fin.last r) k.castSucc hne).2
        rw [Fin.snoc_last, Fin.snoc_castSucc] at this
        exact this hk.symm
  · rintro ⟨hci, hv⟩
    -- helper: v ∉ blocked t unpacks to v ≠ t k and v ≠ -t k
    have hvne : ∀ k : Fin r, v ≠ t k ∧ v ≠ - t k := by
      intro k
      refine ⟨?_, ?_⟩ <;> intro hc <;> apply hv <;> rw [blocked, Finset.mem_union]
      · exact Or.inl (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hc.symm⟩)
      · exact Or.inr (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hc.symm⟩)
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd rfl hij
      | cast j0 =>
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        exact ⟨(hvne j0).1, (hvne j0).2⟩
    | cast i0 =>
      induction j using Fin.lastCases with
      | last =>
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        refine ⟨fun hc => (hvne i0).1 hc.symm, ?_⟩
        intro hc
        -- hc : t i0 = - v  ⇒  v = - t i0, contradicting (hvne i0).2
        apply (hvne i0).2
        rw [hc, neg_neg]
      | cast j0 =>
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        have hij0 : i0 ≠ j0 := by
          intro h; apply hij; rw [h]
        exact hci i0 j0 hij0

/-- **The closed-form count via the snoc bijection.** For a negation-closed no-2-torsion `G` of order
`n`, the class-injective transversal count is `∏_{i<r}(n − 2i) = descFactorTwo n r`. Proved by
induction on `r`: `classInjectiveTransversals (r+1)` is in bijection with `Σ t ∈ CI(r), (G \ blocked t)`
via `Fin.snoc` (`classInjective_snoc`); each fiber has card `n − 2r` (`admissible_card`). -/
theorem classInjectiveTransversals_card {G : Finset F} (hneg : ∀ g ∈ G, -g ∈ G)
    (hnt : NoTwoTorsionOn G) (r : ℕ) :
    (classInjectiveTransversals (r := r) G).card = descFactorTwo G.card r := by
  classical
  induction r with
  | zero =>
    -- only the empty tuple; it is vacuously class-injective
    simp only [descFactorTwo]
    have hall : classInjectiveTransversals (r := 0) G
        = Fintype.piFinset (fun _ : Fin 0 => G) := by
      rw [classInjectiveTransversals]
      apply Finset.filter_true_of_mem
      intro c _ i; exact i.elim0
    rw [hall, Fintype.card_piFinset]
    simp
  | succ r ih =>
    -- Map each class-injective x : Fin (r+1) -> F to its restriction Fin.init x ∈ CI(r).
    -- Fiber over t is in bijection with the admissible last values G \ blocked t (card n - 2r).
    rw [Finset.card_eq_sum_card_fiberwise
        (f := fun x => Fin.init x) (t := classInjectiveTransversals (r := r) G) ?_]
    · -- each fiber has card (G \ blocked t).card = n - 2r, and there are descFactorTwo n r prefixes
      have hfib : ∀ t ∈ classInjectiveTransversals (r := r) G,
          ((classInjectiveTransversals (r := r + 1) G).filter
            (fun x => Fin.init x = t)).card = G.card - 2 * r := by
        intro t ht
        rw [classInjectiveTransversals, Finset.mem_filter, Fintype.mem_piFinset] at ht
        obtain ⟨htmem, htci⟩ := ht
        have hnsp : NoSelfPair t := fun k => (hnt _ (htmem k)).symm
        -- bijection fiber <-> G \ blocked t  via  x ↦ x (last),  inverse v ↦ Fin.snoc t v
        rw [← admissible_card htmem htci hnsp hneg]
        apply Finset.card_bij (fun x _ => x (Fin.last r))
        · -- maps into G \ blocked t
          intro x hx
          rw [Finset.mem_filter, classInjectiveTransversals, Finset.mem_filter,
            Fintype.mem_piFinset] at hx
          obtain ⟨⟨hxmem, hxci⟩, hinit⟩ := hx
          -- x = Fin.snoc (Fin.init x) (x last) = Fin.snoc t (x last)
          have hsnoc : x = Fin.snoc t (x (Fin.last r)) := by
            rw [← hinit]; exact (Fin.snoc_init_self x).symm
          rw [hsnoc] at hxci
          have := (classInjective_snoc).mp hxci
          rw [Finset.mem_sdiff]
          exact ⟨hxmem (Fin.last r), this.2⟩
        · -- injective on the fiber
          intro x hx y hy hxy
          rw [Finset.mem_filter] at hx hy
          -- x and y agree on init (= t) and on last (= hxy), so equal
          funext i
          induction i using Fin.lastCases with
          | last => exact hxy
          | cast i0 =>
            have hx2 : Fin.init x = Fin.init y := by rw [hx.2, hy.2]
            exact congrFun hx2 i0
        · -- surjective: every v ∈ G \ blocked t comes from Fin.snoc t v
          intro v hv
          rw [Finset.mem_sdiff] at hv
          refine ⟨Fin.snoc t v, ?_, ?_⟩
          · rw [Finset.mem_filter, classInjectiveTransversals, Finset.mem_filter,
              Fintype.mem_piFinset]
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · intro k
              induction k using Fin.lastCases with
              | last => rw [Fin.snoc_last]; exact hv.1
              | cast k0 => rw [Fin.snoc_castSucc]; exact htmem k0
            · exact (classInjective_snoc).mpr ⟨htci, hv.2⟩
            · rw [Fin.init_snoc]
          · rw [Fin.snoc_last]
      rw [Finset.sum_congr rfl hfib, Finset.sum_const, ih, smul_eq_mul, descFactorTwo,
        Nat.mul_comm]
    · -- the restriction map lands in CI(r)
      intro x hx
      rw [Finset.mem_coe, classInjectiveTransversals, Finset.mem_filter,
        Fintype.mem_piFinset] at hx
      obtain ⟨hxmem, hxci⟩ := hx
      simp only [Finset.mem_coe, classInjectiveTransversals, Finset.mem_filter,
        Fintype.mem_piFinset]
      refine ⟨fun k => hxmem k.castSucc, ?_⟩
      intro i j hij
      have hij' : i.castSucc ≠ j.castSucc := by simp [Fin.castSucc_inj, hij]
      have hkey := hxci i.castSucc j.castSucc hij'
      simpa only [Fin.init] using hkey

/-- **The `hm` gate value, fully evaluated.** Combining the `σ`-free reduction
(`GenericCountTransversal.genericAntipodalSet_card_eq_classInjCount`) with the closed-form count: for
any pairing `σ` and any negation-closed no-2-torsion `G` of order `n`, the per-`σ` generic count is
the explicit constant `∏_{i<r}(n − 2i) = 2^r·(n/2)_r`. This DISCHARGES the `hm` hypothesis of
`GenericSuperDiagonalLower.superDiagonal_le_rEnergy` with a concrete closed-form value (no `σ`, no
remaining analytic input). -/
theorem genericAntipodalSet_card_eq_descFactorTwo {r : ℕ}
    {σ : Equiv.Perm (Fin (2 * r))} (hσ : IsPairing σ) (G : Finset F)
    (hneg : ∀ g ∈ G, -g ∈ G) (hnt : NoTwoTorsionOn G) :
    (genericAntipodalSet G σ).card = descFactorTwo G.card r := by
  rw [genericAntipodalSet_card_eq_classInjCount hσ G hneg hnt,
      classInjectiveTransversals_card hneg hnt r]

end ProximityGap.Frontier.ClassInjectiveCount

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ClassInjectiveCount.blocked_card
#print axioms ProximityGap.Frontier.ClassInjectiveCount.classInjective_snoc
#print axioms ProximityGap.Frontier.ClassInjectiveCount.classInjectiveTransversals_card
#print axioms ProximityGap.Frontier.ClassInjectiveCount.genericAntipodalSet_card_eq_descFactorTwo

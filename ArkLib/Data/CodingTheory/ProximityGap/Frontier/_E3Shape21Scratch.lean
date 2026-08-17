import ArkLib.Data.CodingTheory.ProximityGap.LamLeungMultisetAntipodal
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._E3StrataCount
import Mathlib.Tactic

open ArkLib.ProximityGap.Frontier.E3StrataCount (twoValue_count)

set_option linter.style.longLine false
set_option autoImplicit false

/-! Scratch: the per-P fiber count for shape-(2,1). If this lands, shape-(2,1)=360 follows by
summing over P. Fiber bijection: c ↦ ({i∈P : c i = x}, {i∈Pᶜ : c i = y}) to a product of
two `powersetCard`s. -/

open Finset

namespace E3Shape21Scratch

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- The per-`P` fiber count: tuples `c : Fin 6 → F` that are `±x` on `P` (balanced: `|P|/2` x's)
and `±y` off `P` (balanced: `|Pᶜ|/2` y's) number `C(|P|,|P|/2)·C(|Pᶜ|,|Pᶜ|/2)`. (Here `x,-x,y,-y`
are 4 distinct values.) -/
theorem fiber_card (P : Finset (Fin 6)) (x y : F)
    (hx : x ≠ -x) (hy : y ≠ -y) (hxy : x ≠ y) (hxy' : x ≠ -y) (hmxy : -x ≠ y) (hmxy' : -x ≠ -y) :
    ((Finset.univ.filter (fun c : Fin 6 → F =>
        (∀ i, i ∈ P → (c i = x ∨ c i = -x)) ∧ (∀ i, i ∉ P → (c i = y ∨ c i = -y))
        ∧ (Finset.univ.filter (fun i => c i = x)).card = P.card / 2
        ∧ (Finset.univ.filter (fun i => c i = y)).card = Pᶜ.card / 2))).card
      = Nat.choose P.card (P.card / 2) * Nat.choose Pᶜ.card (Pᶜ.card / 2) := by
  classical
  -- value distinctness helpers
  have hxny : x ≠ -y := hxy'
  rw [show Nat.choose P.card (P.card / 2) * Nat.choose Pᶜ.card (Pᶜ.card / 2)
        = ((P.powersetCard (P.card / 2)) ×ˢ (Pᶜ.powersetCard (Pᶜ.card / 2))).card by
        rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard]]
  refine Finset.card_nbij'
    (fun c => (P.filter (fun i => c i = x), Pᶜ.filter (fun i => c i = y)))
    (fun pr => fun i => if i ∈ pr.1 then x else if i ∈ P then -x else if i ∈ pr.2 then y else -y)
    ?_ ?_ ?_ ?_
  · -- forward into the product
    intro c hc
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨hP, hPc, hxk, hyk⟩ := hc
    -- x occurs only on P
    have hxonP : Finset.univ.filter (fun i => c i = x) = P.filter (fun i => c i = x) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; refine ⟨?_, h⟩
        by_contra hiP
        rcases hPc i hiP with h' | h'
        · exact hxy (h.symm.trans h')
        · exact hxy' (h.symm.trans h')
      · exact fun h => h.2
    have hyonPc : Finset.univ.filter (fun i => c i = y) = Pᶜ.filter (fun i => c i = y) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
      constructor
      · intro h; refine ⟨?_, h⟩
        intro hmem
        rcases hP i hmem with h' | h'
        · exact hxy (h'.symm.trans h)
        · exact hmxy (h'.symm.trans h)
      · exact fun h => h.2
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard]
    refine ⟨⟨Finset.filter_subset _ _, ?_⟩, ⟨Finset.filter_subset _ _, ?_⟩⟩
    · rw [← hxonP]; exact hxk
    · rw [← hyonPc]; exact hyk
  · -- backward into the fiber
    intro pr hpr
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard] at hpr
    obtain ⟨⟨hAxP, hAxc⟩, ⟨hAyPc, hAyc⟩⟩ := hpr
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hiP
      by_cases h : i ∈ pr.1
      · left; simp [h]
      · right; simp [h, hiP]
    · intro i hiP
      have hiAx : i ∉ pr.1 := fun h => hiP (hAxP h)
      by_cases h : i ∈ pr.2
      · left; simp [hiAx, hiP, h]
      · right; simp [hiAx, hiP, h]
    · -- #x = |Ax| = |P|/2
      rw [show (Finset.univ.filter (fun i => (if i ∈ pr.1 then x else if i ∈ P then -x else if i ∈ pr.2 then y else -y) = x)) = pr.1 from ?_, hAxc]
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h : i ∈ pr.1
      · simp [h]
      · by_cases h2 : i ∈ P
        · simp [h, h2, (Ne.symm hx)]
        · by_cases h3 : i ∈ pr.2
          · simp [h, h2, h3, Ne.symm hxy]
          · simp [h, h2, h3, Ne.symm hxy']
    · rw [show (Finset.univ.filter (fun i => (if i ∈ pr.1 then x else if i ∈ P then -x else if i ∈ pr.2 then y else -y) = y)) = pr.2 from ?_, hAyc]
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hAyP : i ∈ pr.2 → i ∉ P := fun h hP => by
        have := hAyPc h; rw [Finset.mem_compl] at this; exact this hP
      by_cases h : i ∈ pr.1
      · have hiP : i ∈ P := hAxP h
        have hi2 : i ∉ pr.2 := fun hh => (Finset.mem_compl.mp (hAyPc hh)) hiP
        simp [h, hxy, hi2]
      · by_cases h2 : i ∈ P
        · have hi2 : i ∉ pr.2 := fun hh => (Finset.mem_compl.mp (hAyPc hh)) h2
          simp [h, h2, hmxy, hi2]
        · by_cases h3 : i ∈ pr.2
          · simp [h, h2, h3]
          · simp [h, h2, h3, (Ne.symm hy)]
  · -- left inverse
    intro c hc
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨hP, hPc, _, _⟩ := hc
    funext i
    by_cases h : i ∈ P
    · rcases hP i h with h' | h'
      · simp only; rw [if_pos (Finset.mem_filter.mpr ⟨h, h'⟩)]; exact h'.symm
      · have hnx : i ∉ P.filter (fun j => c j = x) := by
          simp only [Finset.mem_filter, not_and]; intro _; rw [h']; exact (Ne.symm hx)
        simp only; rw [if_neg hnx, if_pos h]; exact h'.symm
    · rcases hPc i h with h' | h'
      · have hnx : i ∉ P.filter (fun j => c j = x) := fun hh => h (Finset.mem_filter.mp hh).1
        have hy' : i ∈ Pᶜ.filter (fun j => c j = y) := Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr h, h'⟩
        simp only; rw [if_neg hnx, if_neg h, if_pos hy']; exact h'.symm
      · have hnx : i ∉ P.filter (fun j => c j = x) := fun hh => h (Finset.mem_filter.mp hh).1
        have hny : i ∉ Pᶜ.filter (fun j => c j = y) := by
          simp only [Finset.mem_filter, not_and]; intro _; rw [h']; exact (Ne.symm hy)
        simp only; rw [if_neg hnx, if_neg h, if_neg hny]; exact h'.symm
  · -- right inverse
    intro pr hpr
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard] at hpr
    obtain ⟨⟨hAxP, _⟩, ⟨hAyPc, _⟩⟩ := hpr
    have hAyP : ∀ i ∈ pr.2, i ∉ P := fun i h hP => by
      have := hAyPc h; rw [Finset.mem_compl] at this; exact this hP
    refine Prod.ext ?_ ?_
    · ext i
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hiP, hval⟩
        by_cases h : i ∈ pr.1
        · exact h
        · exfalso; rw [if_neg h, if_pos hiP] at hval; exact (Ne.symm hx) hval
      · intro h; exact ⟨hAxP h, by rw [if_pos h]⟩
    · ext i
      simp only [Finset.mem_filter, Finset.mem_compl]
      constructor
      · rintro ⟨hiP, hval⟩
        by_cases h : i ∈ pr.2
        · exact h
        · exfalso
          by_cases h1 : i ∈ pr.1
          · rw [if_pos h1] at hval; exact hxy hval
          · rw [if_neg h1, if_neg hiP, if_neg h] at hval; exact (Ne.symm hy) hval
      · intro h
        refine ⟨hAyP i h, ?_⟩
        have h1 : i ∉ pr.1 := fun hh => (hAyP i h) (hAxP hh)
        rw [if_neg h1, if_neg (hAyP i h), if_pos h]

/-- `#{balanced ∧ valued in {x,-x,y,-y}} = 400` (4 distinct values). Via
`card_eq_sum_card_fiberwise` over the x-position map: each fiber over `P` equals `fiber_card P`'s
set when `|P|` is even (balance forces even x-positions) and is empty for odd `|P|`; the resulting
even-guarded binomial sum is `400` (`decide`). -/
theorem balanced_valued_count (x y : F)
    (hx : x ≠ -x) (hy : y ≠ -y) (hxy : x ≠ y) (hxy' : x ≠ -y) (hmxy : -x ≠ y) (hmxy' : -x ≠ -y) :
    ((Finset.univ.filter (fun c : Fin 6 → F =>
        (∀ i, c i = x ∨ c i = -x ∨ c i = y ∨ c i = -y)
        ∧ (Finset.univ.filter (fun i => c i = x)).card = (Finset.univ.filter (fun i => c i = -x)).card
        ∧ (Finset.univ.filter (fun i => c i = y)).card = (Finset.univ.filter (fun i => c i = -y)).card))).card
      = 400 := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
      (f := fun c => Finset.univ.filter (fun i => c i = x ∨ c i = -x))
      (t := (Finset.univ : Finset (Fin 6)).powerset)
      (fun c _ => Finset.mem_powerset.mpr (Finset.filter_subset _ _))]
  rw [show (400 : ℕ) = ∑ P ∈ (Finset.univ : Finset (Fin 6)).powerset,
        (if Even P.card then Nat.choose P.card (P.card / 2) * Nat.choose Pᶜ.card (Pᶜ.card / 2) else 0)
        by decide]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  -- key: for a tuple valued in {x,-x,y,-y}, the x-position set is exactly {i : c i = x ∨ c i = -x},
  -- and #x + #(-x) over it = its card.
  by_cases hev : Even P.card
  · rw [if_pos hev]
    obtain ⟨kP, hkP⟩ := hev
    have hPc6 : Pᶜ.card = 6 - P.card := by rw [Finset.card_compl, Fintype.card_fin]
    rw [show ((Finset.univ.filter (fun c : Fin 6 → F =>
            (∀ i, c i = x ∨ c i = -x ∨ c i = y ∨ c i = -y)
            ∧ (Finset.univ.filter (fun i => c i = x)).card = (Finset.univ.filter (fun i => c i = -x)).card
            ∧ (Finset.univ.filter (fun i => c i = y)).card = (Finset.univ.filter (fun i => c i = -y)).card)).filter
          (fun c => Finset.univ.filter (fun i => c i = x ∨ c i = -x) = P))
        = (Finset.univ.filter (fun c : Fin 6 → F =>
            (∀ i, i ∈ P → (c i = x ∨ c i = -x)) ∧ (∀ i, i ∉ P → (c i = y ∨ c i = -y))
            ∧ (Finset.univ.filter (fun i => c i = x)).card = P.card / 2
            ∧ (Finset.univ.filter (fun i => c i = y)).card = Pᶜ.card / 2)) from ?_]
    · exact fiber_card P x y hx hy hxy hxy' hmxy hmxy'
    · ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hval, hbx, hby⟩, hpos⟩
        -- x-positions = P
        have hxpos : ∀ i, (c i = x ∨ c i = -x) ↔ i ∈ P := by
          intro i; rw [← hpos]; simp [Finset.mem_filter]
        -- on P, c is ±x; off P, c is ±y
        have hP : ∀ i, i ∈ P → (c i = x ∨ c i = -x) := fun i hi => (hxpos i).mpr hi
        have hPc : ∀ i, i ∉ P → (c i = y ∨ c i = -y) := by
          intro i hi
          rcases hval i with h | h | h | h
          · exact absurd ((hxpos i).mp (Or.inl h)) hi
          · exact absurd ((hxpos i).mp (Or.inr h)) hi
          · exact Or.inl h
          · exact Or.inr h
        -- #x + #(-x) = |P|
        have hsumP : (Finset.univ.filter (fun i => c i = x)).card
            + (Finset.univ.filter (fun i => c i = -x)).card = P.card := by
          rw [← Finset.card_union_of_disjoint, show (Finset.univ.filter (fun i => c i = x))
                ∪ (Finset.univ.filter (fun i => c i = -x)) = P from ?_]
          · ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [← hxpos i]
          · rw [Finset.disjoint_left]; intro i hi hi'
            rw [Finset.mem_filter] at hi hi'; exact hx (hi.2 ▸ hi'.2)
        have hsumPc : (Finset.univ.filter (fun i => c i = y)).card
            + (Finset.univ.filter (fun i => c i = -y)).card = Pᶜ.card := by
          rw [← Finset.card_union_of_disjoint, show (Finset.univ.filter (fun i => c i = y))
                ∪ (Finset.univ.filter (fun i => c i = -y)) = Pᶜ from ?_]
          · ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
            constructor
            · rintro (h | h)
              · intro hiP; rcases (hxpos i).mpr hiP with h' | h'
                · exact hxy (h'.symm.trans h)
                · exact hmxy (h'.symm.trans h)
              · intro hiP; rcases (hxpos i).mpr hiP with h' | h'
                · exact hxy' (h'.symm.trans h)
                · exact hmxy' (h'.symm.trans h)
            · intro hiP; rcases hPc i hiP with h | h
              · exact Or.inl h
              · exact Or.inr h
          · rw [Finset.disjoint_left]; intro i hi hi'
            rw [Finset.mem_filter] at hi hi'; exact hy (hi.2 ▸ hi'.2)
        refine ⟨hP, hPc, ?_, ?_⟩
        · omega
        · omega
      · rintro ⟨hP, hPc, hxk, hyk⟩
        have hxpos : Finset.univ.filter (fun i => c i = x ∨ c i = -x) = P := by
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro (h | h)
            · by_contra hiP; rcases hPc i hiP with h' | h'
              · exact hxy (h.symm.trans h')
              · exact hxy' (h.symm.trans h')
            · by_contra hiP; rcases hPc i hiP with h' | h'
              · exact hmxy (h.symm.trans h')
              · exact hmxy' (h.symm.trans h')
          · exact hP i
        refine ⟨⟨fun i => ?_, ?_, ?_⟩, hxpos⟩
        · by_cases hiP : i ∈ P
          · rcases hP i hiP with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          · rcases hPc i hiP with h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h))
        · have hsumP : (Finset.univ.filter (fun i => c i = x)).card
              + (Finset.univ.filter (fun i => c i = -x)).card = P.card := by
            rw [← Finset.card_union_of_disjoint, show (Finset.univ.filter (fun i => c i = x))
                  ∪ (Finset.univ.filter (fun i => c i = -x)) = P from ?_]
            · ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
              rw [← hxpos]; simp [Finset.mem_filter]
            · rw [Finset.disjoint_left]; intro i hi hi'
              rw [Finset.mem_filter] at hi hi'; exact hx (hi.2 ▸ hi'.2)
          omega
        · have hsumPc : (Finset.univ.filter (fun i => c i = y)).card
              + (Finset.univ.filter (fun i => c i = -y)).card = Pᶜ.card := by
            rw [← Finset.card_union_of_disjoint, show (Finset.univ.filter (fun i => c i = y))
                  ∪ (Finset.univ.filter (fun i => c i = -y)) = Pᶜ from ?_]
            · ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
              constructor
              · rintro (h | h)
                · intro hiP; rw [← hxpos] at hiP; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiP
                  rcases hiP with h' | h'
                  · exact hxy (h'.symm.trans h)
                  · exact hmxy (h'.symm.trans h)
                · intro hiP; rw [← hxpos] at hiP; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiP
                  rcases hiP with h' | h'
                  · exact hxy' (h'.symm.trans h)
                  · exact hmxy' (h'.symm.trans h)
              · intro hiP; rcases hPc i hiP with h | h
                · exact Or.inl h
                · exact Or.inr h
            · rw [Finset.disjoint_left]; intro i hi hi'
              rw [Finset.mem_filter] at hi hi'; exact hy (hi.2 ▸ hi'.2)
          omega
  · rw [if_neg hev, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c hc
    rw [Finset.mem_filter] at hc
    intro hpos
    -- x-positions = P, but its card = #x + #(-x) = 2·#x is even
    apply hev
    rw [← hpos]
    obtain ⟨_, hbx, _⟩ := hc.2
    have hsplit : (Finset.univ.filter (fun i => c i = x ∨ c i = -x)).card
        = (Finset.univ.filter (fun i => c i = x)).card + (Finset.univ.filter (fun i => c i = -x)).card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
      · rw [Finset.disjoint_left]; intro i hi hi'
        rw [Finset.mem_filter] at hi hi'; exact hx (hi.2 ▸ hi'.2)
    rw [hsplit, hbx]; exact ⟨_, rfl⟩

/-- Among balanced tuples valued in `{x,-x,y,-y}`, those with image exactly `{x,-x}` are the
ones with `x` in 3 positions (valued in `{x,-x}`, balanced) — `C(6,3)=20` of them. -/
theorem valued_image_two (x y : F)
    (hx : x ≠ -x) (hy : y ≠ -y) (hxy : x ≠ y) (hxy' : x ≠ -y) (hmxy : -x ≠ y) (hmxy' : -x ≠ -y) :
    ((Finset.univ.filter (fun c : Fin 6 → F =>
        (∀ i, c i = x ∨ c i = -x ∨ c i = y ∨ c i = -y)
        ∧ (Finset.univ.filter (fun i => c i = x)).card = (Finset.univ.filter (fun i => c i = -x)).card
        ∧ (Finset.univ.filter (fun i => c i = y)).card = (Finset.univ.filter (fun i => c i = -y)).card)).filter
      (fun c => Finset.image c Finset.univ = {x, -x})).card = 20 := by
  classical
  rw [show (20 : ℕ) = Nat.choose (Fintype.card (Fin 6)) 3 by decide,
      ← twoValue_count (ι := Fin 6) 3 x hx]
  congr 1
  ext c
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_univ, true_and]
  -- helper: a tuple valued in {x,-x} has #x + #(-x) = 6
  have twoSum : (∀ i, c i ∈ ({x, -x} : Finset F)) →
      (Finset.univ.filter (fun i => c i = x)).card + (Finset.univ.filter (fun i => c i = -x)).card = 6 := by
    intro hval
    have hdisj : Disjoint (Finset.univ.filter (fun i => c i = x)) (Finset.univ.filter (fun i => c i = -x)) := by
      rw [Finset.disjoint_left]; intro i hi hi'
      rw [Finset.mem_filter] at hi hi'; exact hx (hi.2 ▸ hi'.2)
    have hcov : (Finset.univ.filter (fun i => c i = x)) ∪ (Finset.univ.filter (fun i => c i = -x)) = Finset.univ := by
      ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      rcases Finset.mem_insert.mp (hval i) with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    have hu := Finset.card_union_of_disjoint hdisj
    rw [hcov, Finset.card_univ, Fintype.card_fin] at hu; omega
  constructor
  · rintro ⟨⟨_, hbx, _⟩, himg⟩
    have hval2 : ∀ i, c i ∈ ({x, -x} : Finset F) :=
      fun i => himg ▸ Finset.mem_image_of_mem c (Finset.mem_univ i)
    exact ⟨hval2, by have := twoSum hval2; omega⟩
  · rintro ⟨hval2, hk⟩
    have hsum := twoSum hval2
    have hnegx3 : (Finset.univ.filter (fun i => c i = -x)).card = 3 := by omega
    have hempty : ∀ w : F, w ≠ x → w ≠ -x → (Finset.univ.filter (fun i => c i = w)).card = 0 := by
      intro w hwx hwnx
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro i _ hci
      rcases Finset.mem_insert.mp (hval2 i) with h | h
      · exact hwx (hci ▸ h)
      · exact hwnx (hci ▸ Finset.mem_singleton.mp h)
    refine ⟨⟨fun i => ?_, ?_, ?_⟩, ?_⟩
    · rcases Finset.mem_insert.mp (hval2 i) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Finset.mem_singleton.mp h))
    · rw [hk, hnegx3]
    · rw [hempty y (fun h => hxy h.symm) (fun h => hmxy h.symm),
          hempty (-y) (fun h => hxy' h.symm) (fun h => hmxy' h.symm)]
    · apply Finset.Subset.antisymm
      · intro w hw; rw [Finset.mem_image] at hw; obtain ⟨i, _, hi⟩ := hw; exact hi ▸ hval2 i
      · intro w hw
        rw [Finset.mem_image]
        rcases Finset.mem_insert.mp hw with h | h
        · have hpos : 0 < (Finset.univ.filter (fun i => c i = x)).card := by rw [hk]; norm_num
          obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos; rw [Finset.mem_filter] at hi
          exact ⟨i, Finset.mem_univ i, by rw [hi.2]; exact h.symm⟩
        · have h' := Finset.mem_singleton.mp h
          have hpos : 0 < (Finset.univ.filter (fun i => c i = -x)).card := by rw [hnegx3]; norm_num
          obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos; rw [Finset.mem_filter] at hi
          exact ⟨i, Finset.mem_univ i, by rw [hi.2]; exact h'.symm⟩

/-- Among balanced tuples valued in `{x,-x,y,-y}`, those with **no `x`-pair** (`#x = 0`) are the
ones valued in `{y,-y}` with `y` in 3 positions — `C(6,3) = 20` (the `x ↔ y` mirror of
`valued_image_two`, charted by `#x=0` instead of `image={y,-y}`). -/
theorem valued_noX_count (x y : F)
    (hx : x ≠ -x) (hy : y ≠ -y) (hxy : x ≠ y) (hxy' : x ≠ -y) (hmxy : -x ≠ y) (hmxy' : -x ≠ -y) :
    ((Finset.univ.filter (fun c : Fin 6 → F =>
        (∀ i, c i = x ∨ c i = -x ∨ c i = y ∨ c i = -y)
        ∧ (Finset.univ.filter (fun i => c i = x)).card = (Finset.univ.filter (fun i => c i = -x)).card
        ∧ (Finset.univ.filter (fun i => c i = y)).card = (Finset.univ.filter (fun i => c i = -y)).card)).filter
      (fun c => (Finset.univ.filter (fun i => c i = x)).card = 0)).card = 20 := by
  classical
  rw [show (20 : ℕ) = Nat.choose (Fintype.card (Fin 6)) 3 by decide,
      ← twoValue_count (ι := Fin 6) 3 y hy]
  congr 1
  ext c
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_univ, true_and]
  have twoSum : (∀ i, c i ∈ ({y, -y} : Finset F)) →
      (Finset.univ.filter (fun i => c i = y)).card + (Finset.univ.filter (fun i => c i = -y)).card = 6 := by
    intro hval
    have hdisj : Disjoint (Finset.univ.filter (fun i => c i = y)) (Finset.univ.filter (fun i => c i = -y)) := by
      rw [Finset.disjoint_left]; intro i hi hi'
      rw [Finset.mem_filter] at hi hi'; exact hy (hi.2 ▸ hi'.2)
    have hcov : (Finset.univ.filter (fun i => c i = y)) ∪ (Finset.univ.filter (fun i => c i = -y)) = Finset.univ := by
      ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      rcases Finset.mem_insert.mp (hval i) with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    have hu := Finset.card_union_of_disjoint hdisj
    rw [hcov, Finset.card_univ, Fintype.card_fin] at hu; omega
  constructor
  · rintro ⟨⟨hval4, hbx, hby⟩, hx0⟩
    have hnx0 : (Finset.univ.filter (fun i => c i = -x)).card = 0 := by omega
    have hval2 : ∀ i, c i ∈ ({y, -y} : Finset F) := by
      intro i
      rcases hval4 i with h | h | h | h
      · exact absurd (Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩⟩) (by rw [hx0]; exact lt_irrefl 0)
      · exact absurd (Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩⟩) (by rw [hnx0]; exact lt_irrefl 0)
      · exact Finset.mem_insert.mpr (Or.inl h)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))
    exact ⟨hval2, by have := twoSum hval2; omega⟩
  · rintro ⟨hval2, hyk⟩
    have hsum := twoSum hval2
    have hx0 : (Finset.univ.filter (fun i => c i = x)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro i _ hi
      rcases Finset.mem_insert.mp (hval2 i) with h | h
      · exact hxy (hi ▸ h)
      · exact hxy' (hi ▸ Finset.mem_singleton.mp h)
    have hnx0 : (Finset.univ.filter (fun i => c i = -x)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro i _ hi
      rcases Finset.mem_insert.mp (hval2 i) with h | h
      · exact hmxy (hi ▸ h)
      · exact hmxy' (hi ▸ Finset.mem_singleton.mp h)
    refine ⟨⟨fun i => ?_, ?_, ?_⟩, hx0⟩
    · rcases Finset.mem_insert.mp (hval2 i) with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp h)))
    · rw [hx0, hnx0]
    · omega

/-- **shape-(2,1) = 360.** Among the `400` balanced 6-tuples valued in `{x,-x,y,-y}`
(`balanced_valued_count`), those with image exactly `{x,-x,y,-y}` are the complement of the two
sub-image classes `#x=0` (image `{y,-y}`) and `#y=0` (image `{x,-x}`), each of size `20`
(`valued_noX_count`); so `360 = 400 - 20 - 20`. -/
theorem shape21 (x y : F)
    (hx : x ≠ -x) (hy : y ≠ -y) (hxy : x ≠ y) (hxy' : x ≠ -y) (hmxy : -x ≠ y) (hmxy' : -x ≠ -y) :
    ((Finset.univ.filter (fun c : Fin 6 → F =>
        (∀ i, c i = x ∨ c i = -x ∨ c i = y ∨ c i = -y)
        ∧ (Finset.univ.filter (fun i => c i = x)).card = (Finset.univ.filter (fun i => c i = -x)).card
        ∧ (Finset.univ.filter (fun i => c i = y)).card = (Finset.univ.filter (fun i => c i = -y)).card)).filter
      (fun c => Finset.image c Finset.univ = {x, -x, y, -y})).card = 360 := by
  classical
  set A := Finset.univ.filter (fun c : Fin 6 → F =>
      (∀ i, c i = x ∨ c i = -x ∨ c i = y ∨ c i = -y)
      ∧ (Finset.univ.filter (fun i => c i = x)).card = (Finset.univ.filter (fun i => c i = -x)).card
      ∧ (Finset.univ.filter (fun i => c i = y)).card = (Finset.univ.filter (fun i => c i = -y)).card)
    with hAdef
  have hAcard : A.card = 400 := balanced_valued_count x y hx hy hxy hxy' hmxy hmxy'
  have hx20 : (A.filter (fun c => (Finset.univ.filter (fun i => c i = x)).card = 0)).card = 20 :=
    valued_noX_count x y hx hy hxy hxy' hmxy hmxy'
  -- y-mirror, with the `A`-predicate reordering absorbed
  have hy20 : (A.filter (fun c => (Finset.univ.filter (fun i => c i = y)).card = 0)).card = 20 := by
    have hmir := valued_noX_count y x hy hx (Ne.symm hxy) (Ne.symm hmxy) (Ne.symm hxy') (Ne.symm hmxy')
    rw [← hmir]
    congr 1
    ext c
    rw [hAdef]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hreorder : (∀ i, c i = x ∨ c i = -x ∨ c i = y ∨ c i = -y)
                  ↔ (∀ i, c i = y ∨ c i = -y ∨ c i = x ∨ c i = -x) := by
      constructor <;> intro hh i <;> [skip; skip] <;>
        · rcases hh i with h | h | h | h <;> tauto
    rw [hreorder, and_comm (a := (Finset.univ.filter (fun i => c i = x)).card = (Finset.univ.filter (fun i => c i = -x)).card)]
  -- the two sub-image classes are disjoint (no tuple has both #x=0 and #y=0)
  have hdisjxy : Disjoint (A.filter (fun c => (Finset.univ.filter (fun i => c i = x)).card = 0))
      (A.filter (fun c => (Finset.univ.filter (fun i => c i = y)).card = 0)) := by
    rw [Finset.disjoint_left]
    intro c hcx hcy
    rw [Finset.mem_filter, hAdef, Finset.mem_filter] at hcx hcy
    obtain ⟨⟨_, hval4, hbx, hby⟩, hx0⟩ := hcx
    obtain ⟨_, hy0⟩ := hcy
    have hnx0 : (Finset.univ.filter (fun i => c i = -x)).card = 0 := by omega
    have hny0 : (Finset.univ.filter (fun i => c i = -y)).card = 0 := by omega
    -- position 0 must take some value, but every fiber is empty — contradiction
    rcases hval4 0 with h | h | h | h
    · exact Finset.card_ne_zero_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ 0, h⟩) hx0
    · exact Finset.card_ne_zero_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ 0, h⟩) hnx0
    · exact Finset.card_ne_zero_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ 0, h⟩) hy0
    · exact Finset.card_ne_zero_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ 0, h⟩) hny0
  -- ⊇ direction of the image: a balanced tuple with #x>0 and #y>0 has image exactly {x,-x,y,-y}
  have img4 : ∀ c, c ∈ A → 0 < (Finset.univ.filter (fun i => c i = x)).card →
      0 < (Finset.univ.filter (fun i => c i = y)).card →
      Finset.image c Finset.univ = ({x, -x, y, -y} : Finset F) := by
    intro c hcA hxpos hypos
    rw [hAdef, Finset.mem_filter] at hcA
    obtain ⟨_, hval4, hbx, hby⟩ := hcA
    have pick : ∀ z : F, 0 < (Finset.univ.filter (fun i => c i = z)).card → ∃ i, c i = z := by
      intro z hz; obtain ⟨i, hi⟩ := Finset.card_pos.mp hz; exact ⟨i, (Finset.mem_filter.mp hi).2⟩
    apply Finset.Subset.antisymm
    · intro w hw; rw [Finset.mem_image] at hw; obtain ⟨i, _, hi⟩ := hw
      rcases hval4 i with h | h | h | h <;> simp [hi ▸ h]
    · intro w hw
      rw [Finset.mem_image]
      rcases Finset.mem_insert.mp hw with h | h
      · obtain ⟨i, hi⟩ := pick x hxpos; exact ⟨i, Finset.mem_univ i, by rw [hi, h]⟩
      rcases Finset.mem_insert.mp h with h | h
      · obtain ⟨i, hi⟩ := pick (-x) (by omega); exact ⟨i, Finset.mem_univ i, by rw [hi, h]⟩
      rcases Finset.mem_insert.mp h with h | h
      · obtain ⟨i, hi⟩ := pick y hypos; exact ⟨i, Finset.mem_univ i, by rw [hi, h]⟩
      · obtain ⟨i, hi⟩ := pick (-y) (by omega); exact ⟨i, Finset.mem_univ i, by rw [hi, Finset.mem_singleton.mp h]⟩
  -- the non-4set tuples in A are exactly the two sub-image classes
  have hcompl : A.filter (fun c => ¬ Finset.image c Finset.univ = ({x, -x, y, -y} : Finset F))
      = (A.filter (fun c => (Finset.univ.filter (fun i => c i = x)).card = 0))
        ∪ (A.filter (fun c => (Finset.univ.filter (fun i => c i = y)).card = 0)) := by
    apply Finset.ext
    intro c
    constructor
    · intro hmem
      have hcA : c ∈ A := Finset.mem_of_mem_filter c hmem
      have himg : ¬ Finset.image c Finset.univ = ({x, -x, y, -y} : Finset F) := (Finset.mem_filter.mp hmem).2
      rw [Finset.mem_union]
      by_contra hcon
      push_neg at hcon
      have hxpos : 0 < (Finset.univ.filter (fun i => c i = x)).card :=
        Nat.pos_of_ne_zero (fun h => hcon.1 (Finset.mem_filter.mpr ⟨hcA, h⟩))
      have hypos : 0 < (Finset.univ.filter (fun i => c i = y)).card :=
        Nat.pos_of_ne_zero (fun h => hcon.2 (Finset.mem_filter.mpr ⟨hcA, h⟩))
      exact himg (img4 c hcA hxpos hypos)
    · intro hmem
      rw [Finset.mem_union] at hmem
      rcases hmem with hm | hm
      · have hcA : c ∈ A := Finset.mem_of_mem_filter c hm
        have hx0 := (Finset.mem_filter.mp hm).2
        refine Finset.mem_filter.mpr ⟨hcA, fun himg => ?_⟩
        have hxin : x ∈ Finset.image c Finset.univ := by rw [himg]; simp
        rw [Finset.mem_image] at hxin; obtain ⟨i, _, hi⟩ := hxin
        exact absurd (Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩) (by rw [hx0]; exact lt_irrefl 0)
      · have hcA : c ∈ A := Finset.mem_of_mem_filter c hm
        have hy0 := (Finset.mem_filter.mp hm).2
        refine Finset.mem_filter.mpr ⟨hcA, fun himg => ?_⟩
        have hyin : y ∈ Finset.image c Finset.univ := by rw [himg]; simp
        rw [Finset.mem_image] at hyin; obtain ⟨i, _, hi⟩ := hyin
        exact absurd (Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩) (by rw [hy0]; exact lt_irrefl 0)
  -- card arithmetic: |img=4set| = |A| - |¬img=4set| = 400 - 40 = 360
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := A) (p := fun c => Finset.image c Finset.univ = ({x, -x, y, -y} : Finset F))
  rw [hcompl, Finset.card_union_of_disjoint hdisjxy, hx20, hy20, hAcard] at hsplit
  omega

/-- **Size-4 image contribution = 360** (the `image_count_two`/`image_count_six` analogue, in the
`piFinset G` form the strata partition consumes). For a neg-closed 4-set `{x,-x,y,-y} ⊆ G`, the
balanced 6-tuples of `G` with image exactly `{x,-x,y,-y}` number `360` (`shape21`); the `∀z`-balance
collapses to `#x=#(-x) ∧ #y=#(-y)` on tuples valued in the 4-set. -/
theorem image_count_four (G : Finset F) (x y : F)
    (hx : x ≠ -x) (hy : y ≠ -y) (hxy : x ≠ y) (hxy' : x ≠ -y) (hmxy : -x ≠ y) (hmxy' : -x ≠ -y)
    (hxG : x ∈ G) (hnxG : -x ∈ G) (hyG : y ∈ G) (hnyG : -y ∈ G) :
    ((Fintype.piFinset (fun _ : Fin 6 => G)).filter
      (fun c => (∀ z : F, (Finset.univ.filter (fun i => c i = z)).card
                       = (Finset.univ.filter (fun i => c i = -z)).card)
              ∧ Finset.image c Finset.univ = {x, -x, y, -y})).card = 360 := by
  classical
  rw [← shape21 x y hx hy hxy hxy' hmxy hmxy']
  congr 1
  ext c
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, hbal, himg⟩
    have hval4 : ∀ i, c i = x ∨ c i = -x ∨ c i = y ∨ c i = -y := by
      intro i
      have : c i ∈ ({x, -x, y, -y} : Finset F) := himg ▸ Finset.mem_image_of_mem c (Finset.mem_univ i)
      rcases Finset.mem_insert.mp this with h | h
      · exact Or.inl h
      rcases Finset.mem_insert.mp h with h | h
      · exact Or.inr (Or.inl h)
      rcases Finset.mem_insert.mp h with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp h)))
    exact ⟨⟨hval4, hbal x, hbal y⟩, himg⟩
  · rintro ⟨⟨hval4, hbx, hby⟩, himg⟩
    have hvalG : ∀ i, c i ∈ G := by
      intro i; rcases hval4 i with h | h | h | h
      · exact h ▸ hxG
      · exact h ▸ hnxG
      · exact h ▸ hyG
      · exact h ▸ hnyG
    refine ⟨hvalG, ?_, himg⟩
    -- ∀z balance from #x,#y balance + valued in 4-set
    have hempty : ∀ w : F, w ≠ x → w ≠ -x → w ≠ y → w ≠ -y →
        (Finset.univ.filter (fun i => c i = w)).card = 0 := by
      intro w h1 h2 h3 h4
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro i _ hci
      rcases hval4 i with h | h | h | h
      · exact h1 (hci ▸ h)
      · exact h2 (hci ▸ h)
      · exact h3 (hci ▸ h)
      · exact h4 (hci ▸ h)
    intro z
    by_cases hzx : z = x
    · subst hzx; exact hbx
    by_cases hznx : z = -x
    · subst hznx; rw [neg_neg]; exact hbx.symm
    by_cases hzy : z = y
    · subst hzy; exact hby
    by_cases hzny : z = -y
    · subst hzny; rw [neg_neg]; exact hby.symm
    · rw [hempty z hzx hznx hzy hzny,
          hempty (-z) (fun h => hznx (by rw [← neg_neg z, h]))
            (fun h => hzx (by rw [← neg_neg z, h, neg_neg]))
            (fun h => hzny (by rw [← neg_neg z, h]))
            (fun h => hzy (by rw [← neg_neg z, h, neg_neg]))]

end E3Shape21Scratch

#print axioms E3Shape21Scratch.fiber_card

#print axioms E3Shape21Scratch.balanced_valued_count

#print axioms E3Shape21Scratch.valued_image_two

#print axioms E3Shape21Scratch.valued_noX_count

#print axioms E3Shape21Scratch.shape21


#print axioms E3Shape21Scratch.image_count_four

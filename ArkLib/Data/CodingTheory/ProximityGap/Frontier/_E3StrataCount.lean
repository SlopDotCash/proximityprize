/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungMultisetAntipodal
import Mathlib.Tactic

/-!
# The field-free negation-symmetric strata count toward `E₃ = 15n³−45n²+40n` (#444, WIP)

`negSymCount G 6` counts 6-tuples of `G` whose value fibers are antipodally balanced.
For a negation-closed `G` with `0 ∉ G` and `|G| = n` (so `h = n/2` antipodal pairs), the
partitions-of-3 strata give (kb note `e3-exact-via-negation-symmetric-strata`):

  shape (3):     h · 20      = 10n            arrangements 6!/3!3! = 20
  shape (2,1):   h(h−1) · 180 = 45n²−90n      arrangements 6!/2!2! = 180
  shape (1,1,1): C(h,3) · 720 = 15n³−90n²+120n arrangements 6! = 720

This file lands the **strata → closed-form arithmetic bridge** (the field-free, count-free
identity that the three stratum cardinalities sum to `15n³−45n²+40n`). The remaining open
build step is the count identity `negSymCount G 6 = (the three stratum cards)` (the multinomial
enumeration); the converse `sum_eq_zero_of_fiber_balanced` is already axiom-clean.
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Finset

namespace ArkLib.ProximityGap.Frontier.E3StrataCount

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- `negSymCount G m` = number of `m`-tuples of `G` whose value fibers are antipodally
balanced (`#{i : c i = z} = #{i : c i = -z}` for every `z`). The field-free count object
the strata enumeration evaluates. -/
noncomputable def negSymCount (G : Finset F) (m : ℕ) : ℕ :=
  (Fintype.piFinset (fun _ : Fin m => G)).filter
    (fun c => ∀ z : F, (Finset.univ.filter (fun i => c i = z)).card
                     = (Finset.univ.filter (fun i => c i = -z)).card)
    |>.card

/-- **`720 · C(h,3) = 120 · h(h−1)(h−2)`** for all `h` (the (1,1,1)-stratum cardinality in
non-`choose` form). Via `descFactorial`: `h.descFactorial 3 = h(h−1)(h−2)`, `3! = 6 ∣ it`,
and `C(h,3) = descFactorial/6`. -/
theorem stratum111_card (h : ℕ) :
    720 * Nat.choose h 3 = 120 * (h * (h - 1) * (h - 2)) := by
  have hdf : Nat.descFactorial h 3 = h * (h - 1) * (h - 2) := by
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_succ,
        Nat.descFactorial_zero]
    simp only [Nat.sub_zero, Nat.mul_one]
    ring
  have hdvd : 6 ∣ Nat.descFactorial h 3 := by
    have h6 : (6 : ℕ) = Nat.factorial 3 := rfl
    rw [h6]; exact Nat.factorial_dvd_descFactorial h 3
  obtain ⟨q, hq⟩ := hdvd
  have hch : Nat.choose h 3 = q := by
    rw [Nat.choose_eq_descFactorial_div_factorial, hq]
    have : Nat.factorial 3 = 6 := rfl
    rw [this]; omega
  rw [hch, ← hdf, hq]; ring

/-- **The strata → closed-form arithmetic bridge.** With `h = n/2` antipodal pairs, the three
stratum cardinalities (`(3)`: `20h`, `(2,1)`: `180·h(h−1)`, `(1,1,1)`: `720·C(h,3)`) sum to the
target closed form `15n³−45n²+40n` at `n = 2h`. Field-free, count-free arithmetic. -/
theorem strata_sum_eq_closed (h : ℕ) :
    (20 * h + 180 * (h * (h - 1)) + 720 * Nat.choose h 3 : ℤ)
      = 15 * (2 * h) ^ 3 - 45 * (2 * h) ^ 2 + 40 * (2 * h) := by
  have h111 : (720 * Nat.choose h 3 : ℤ) = (120 * (h * (h - 1) * (h - 2)) : ℕ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (stratum111_card h)
  rcases h with _ | _ | _ | k
  · simp
  · simp
  · simp [Nat.choose]
  · -- h = k+3: every ℕ subtraction is exact, push_cast then ring
    rw [h111]
    push_cast
    ring

/-! ### Pairing structure: a negation-closed `G` (`0 ∉ G`, char ≠ 2) has even cardinality,
so `h = |G| / 2` antipodal pairs — the `h` the strata counts are stated in. -/

/-- **`|G|` is even** for negation-closed `G` avoiding `0` (char ≠ 2): the map `x ↦ −x` is a
fixed-point-free involution on `G`. -/
theorem negClosed_card_even (G : Finset F) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ x ∈ G, -x ∈ G) : Even G.card := by
  classical
  -- parity via the fixed-point-free involution `x ↦ -x`: `∑_{x∈G} 1 = 0` in `ZMod 2`
  have hsum : ∑ _x ∈ G, (1 : ZMod 2) = 0 := by
    apply Finset.sum_involution (fun x _ => -x)
    · intro a _; decide
    · intro a ha _ hcontra
      have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
      have h2a : (2 : F) * a = 0 := by linear_combination -hcontra
      rcases mul_eq_zero.mp h2a with h' | h'
      · exact h2 h'
      · exact ha0 h'
    · intro a _; exact neg_neg a
    · intro a ha; exact hneg a ha
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  have hdvd : (2 : ℕ) ∣ G.card :=
    (CharP.cast_eq_zero_iff (ZMod 2) 2 G.card).mp (by exact_mod_cast hsum)
  obtain ⟨c, hc⟩ := hdvd
  exact ⟨c, by omega⟩

/-- **A negation transversal exists.** For negation-closed `G` (`0∉G`, char≠2) there is `T ⊆ G`
with one representative per antipodal pair: `T` and `T.image (-·)` are disjoint and cover `G`, so
`2·|T| = |G|`. Construction: linearly order the finite `F` (classically) and take the smaller of
each pair, `T = G.filter (· ≤ -·)`. This is the `T` the in-tree `InvolutionClosedCount` engine
and the strata counts consume. -/
theorem exists_neg_transversal (G : Finset F) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ x ∈ G, -x ∈ G) :
    ∃ T : Finset F, T ⊆ G ∧ Disjoint T (T.image (fun x => -x))
      ∧ T ∪ T.image (fun x => -x) = G ∧ 2 * T.card = G.card := by
  classical
  letI : LinearOrder F := LinearOrder.lift' (Fintype.equivFin F) (Equiv.injective _)
  have hxne : ∀ x ∈ G, x ≠ -x := by
    intro x hx hcontra
    have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
    have h2a : (2 : F) * x = 0 := by linear_combination hcontra
    rcases mul_eq_zero.mp h2a with h' | h'
    · exact h2 h'
    · exact hx0 h'
  set T := G.filter (fun x => x ≤ -x) with hTdef
  have hsub : T ⊆ G := Finset.filter_subset _ _
  have hdisj : Disjoint T (T.image (fun x => -x)) := by
    rw [Finset.disjoint_left]
    intro a haT haI
    rw [hTdef, Finset.mem_filter] at haT
    rw [Finset.mem_image] at haI
    obtain ⟨b, hbT, hba⟩ := haI
    rw [hTdef, Finset.mem_filter] at hbT
    have hab : a = -b := hba.symm
    have hbne : b ≠ -b := hxne b hbT.1
    have hle2 : -b ≤ b := by rw [hab] at haT; simpa using haT.2
    exact hbne (le_antisymm hbT.2 hle2)
  have hcov : T ∪ T.image (fun x => -x) = G := by
    apply Finset.Subset.antisymm
    · intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact hsub h
      · rw [Finset.mem_image] at h; obtain ⟨y, hy, rfl⟩ := h
        exact hneg y (hsub hy)
    · intro x hx
      rw [Finset.mem_union]
      by_cases hle : x ≤ -x
      · exact Or.inl (by rw [hTdef, Finset.mem_filter]; exact ⟨hx, hle⟩)
      · right
        rw [Finset.mem_image]
        exact ⟨-x, by rw [hTdef, Finset.mem_filter]
                      exact ⟨hneg x hx, by simp only [neg_neg]; exact (not_le.mp hle).le⟩,
               by simp⟩
  refine ⟨T, hsub, hdisj, hcov, ?_⟩
  have himg : (T.image (fun x => -x)).card = T.card :=
    Finset.card_image_of_injective _ neg_injective
  have hu := Finset.card_union_of_disjoint hdisj
  rw [hcov, himg] at hu
  omega

/-- **Rep/sign dichotomy.** Given a negation transversal `T` of `G` (disjoint + covering), every
`g ∈ G` has exactly one of `g`, `-g` in `T` — the well-definedness of "the `T`-representative and
sign of `g`" that the stratum counts encode each value by. -/
theorem transversal_dichotomy {G T : Finset F}
    (hdisj : Disjoint T (T.image (fun x => -x)))
    (hcov : T ∪ T.image (fun x => -x) = G) {g : F} (hg : g ∈ G) :
    (g ∈ T ∧ -g ∉ T) ∨ (g ∉ T ∧ -g ∈ T) := by
  rw [← hcov, Finset.mem_union] at hg
  rcases hg with hgT | hgI
  · left
    refine ⟨hgT, ?_⟩
    intro hngT
    -- -g ∈ T ⟹ g = -(-g) ∈ T.image neg, contradicting disjointness with g ∈ T
    have : g ∈ T.image (fun x => -x) := by
      rw [Finset.mem_image]; exact ⟨-g, hngT, by simp⟩
    exact (Finset.disjoint_left.mp hdisj hgT) this
  · right
    rw [Finset.mem_image] at hgI
    obtain ⟨t, htT, htg⟩ := hgI
    have hng : -g = t := by rw [← htg]; simp
    refine ⟨?_, hng ▸ htT⟩
    intro hgT
    have : g ∈ T.image (fun x => -x) := by
      rw [Finset.mem_image]; exact ⟨t, htT, htg⟩
    exact (Finset.disjoint_left.mp hdisj hgT) this

/-- **A balanced tuple's image is negation-closed.** If `c`'s value fibers are antipodally
balanced, its value set is closed under negation — `count z = count (−z)` makes a nonempty
`z`-fiber force a nonempty `−z`-fiber. The first node of the "partition by image" count route
(image of size `2i` ↦ `C(|T|,i)` neg-closed `2i`-subsets via the in-tree subset engine). -/
theorem balanced_image_neg_closed {m : ℕ} (c : Fin m → F)
    (hbal : ∀ z : F, (Finset.univ.filter (fun i => c i = z)).card
                   = (Finset.univ.filter (fun i => c i = -z)).card)
    {z : F} (hz : z ∈ Finset.image c Finset.univ) :
    -z ∈ Finset.image c Finset.univ := by
  classical
  rw [Finset.mem_image] at hz ⊢
  obtain ⟨i, _, hi⟩ := hz
  have h1 : 1 ≤ (Finset.univ.filter (fun j => c j = z)).card :=
    Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  have h2 : 1 ≤ (Finset.univ.filter (fun j => c j = -z)).card := by rw [← hbal]; exact h1
  obtain ⟨j, hj⟩ := Finset.card_pos.mp h2
  rw [Finset.mem_filter] at hj
  exact ⟨j, Finset.mem_univ j, hj.2⟩

/-- **Two-value count = `C(n,k)`.** For `x ≠ -x`, the tuples `c : Fin n → F` valued in `{x,-x}`
with `x` in exactly `k` positions are in bijection (`c ↦ {i | c i = x}`) with the `k`-subsets of
`Fin n`, so there are `C(n,k)` of them. The reusable engine behind every per-image arrangement
factor (shape-(3) is `n=6,k=3`; the size-4 count splits into two such). -/
theorem twoValue_count {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (x : F) (hx : x ≠ -x) :
    ((Fintype.piFinset (fun _ : ι => ({x, -x} : Finset F))).filter
      (fun c => (Finset.univ.filter (fun i => c i = x)).card = k)).card
      = Nat.choose (Fintype.card ι) k := by
  classical
  have key : ((Fintype.piFinset (fun _ : ι => ({x, -x} : Finset F))).filter
      (fun c => (Finset.univ.filter (fun i => c i = x)).card = k)).card
      = ((Finset.univ : Finset ι).powersetCard k).card := by
    refine Finset.card_nbij' (fun c => Finset.univ.filter (fun i => c i = x))
      (fun S => fun i => if i ∈ S then x else -x) ?_ ?_ ?_ ?_
    · intro c hc
      simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hc
      simp only [Finset.mem_coe, Finset.mem_powersetCard]
      exact ⟨Finset.filter_subset _ _, hc.2⟩
    · intro S hS
      simp only [Finset.mem_coe, Finset.mem_powersetCard] at hS
      simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun i => ?_, ?_⟩
      · by_cases h : i ∈ S <;> simp [h]
      · have heq : (Finset.univ.filter (fun i => (if i ∈ S then x else -x) = x)) = S := by
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases h : i ∈ S <;> simp [h, hx, Ne.symm hx]
        rw [heq, hS.2]
    · intro c hc
      simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hc
      funext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs with hsplit
      · exact hsplit.symm
      · have hmem := hc.1 i
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        exact (hmem.resolve_left hsplit).symm
    · intro S hS
      simp only [Finset.mem_coe, Finset.mem_powersetCard] at hS
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h : i ∈ S <;> simp [h, hx, Ne.symm hx]
  rw [key, Finset.card_powersetCard, Finset.card_univ]

/-- **Shape-(3) arrangement count = 20** (`ι = Fin 6, k = 3` of `twoValue_count`). -/
theorem arrangements_shape3 (x : F) (hx : x ≠ -x) :
    ((Fintype.piFinset (fun _ : Fin 6 => ({x, -x} : Finset F))).filter
      (fun c => (Finset.univ.filter (fun i => c i = x)).card = 3)).card = 20 :=
  (twoValue_count (ι := Fin 6) 3 x hx).trans (by decide)

/-- **A balanced `Fin 6`-tuple's image has even card `≤ 6`.** Its image is negation-closed
(`balanced_image_neg_closed`), avoids `0` (values lie in `G`, `0∉G`), so by `negClosed_card_even`
the image has even cardinality; and it is `≤ 6 = |Fin 6|`. So the image size ∈ {0,2,4,6} — the
sizes the partition-by-image sums over (here {2,4,6}, since `Fin 6` is nonempty). -/
theorem balanced_image_card (G : Finset F) (c : Fin 6 → F) (h2 : (2 : F) ≠ 0)
    (h0 : (0 : F) ∉ G) (hval : ∀ i, c i ∈ G)
    (hbal : ∀ z : F, (Finset.univ.filter (fun i => c i = z)).card
                   = (Finset.univ.filter (fun i => c i = -z)).card) :
    Even (Finset.image c Finset.univ).card ∧ (Finset.image c Finset.univ).card ≤ 6 := by
  classical
  refine ⟨?_, ?_⟩
  · apply negClosed_card_even _ h2
    · intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨i, _, hi⟩ := hmem
      exact h0 (hi ▸ hval i)
    · intro z hz
      exact balanced_image_neg_closed c hbal hz
  · calc (Finset.image c Finset.univ).card ≤ (Finset.univ : Finset (Fin 6)).card :=
            Finset.card_image_le
        _ = 6 := by simp

/-- **Shape-(1,1,1) arrangement count = 720.** A size-6 image `S` admits exactly `6! = 720`
tuples `c : Fin 6 → F` valued in `S` with `image c = S`: these are exactly the bijections
`Fin 6 → ↥S` (`image card 6 = domain card 6` forces injectivity), counted by
`Fintype.card (Fin 6 ↪ ↥S) = (|S|).descFactorial 6 = 720`. -/
theorem arrangements_shape111 (S : Finset F) (hS : S.card = 6) :
    ((Fintype.piFinset (fun _ : Fin 6 => S)).filter
      (fun c => Finset.image c Finset.univ = S)).card = 720 := by
  classical
  -- every counted tuple is valued in `S` and injective
  have key : ∀ c ∈ (Fintype.piFinset (fun _ : Fin 6 => S)).filter
      (fun c => Finset.image c Finset.univ = S),
      (∀ k, c k ∈ S) ∧ Function.Injective c := by
    intro c hc
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hc
    refine ⟨hc.1, ?_⟩
    have hcard : (Finset.image c Finset.univ).card = (Finset.univ : Finset (Fin 6)).card := by
      rw [hc.2, hS]; simp
    have hinj : Set.InjOn c ↑(Finset.univ : Finset (Fin 6)) := Finset.injOn_of_card_image_eq hcard
    intro a b hab
    exact hinj (by simp) (by simp) hab
  rw [show (720 : ℕ) = (Finset.univ : Finset (Fin 6 ↪ {x // x ∈ S})).card by
        rw [Finset.card_univ, Fintype.card_embedding_eq, Fintype.card_coe, hS]; decide]
  refine Finset.card_bij'
    (fun c hc => ⟨fun k => ⟨c k, (key c hc).1 k⟩, fun a b hab => (key c hc).2 (by simpa using hab)⟩)
    (fun f _ k => (f k : F)) ?_ ?_ ?_ ?_
  · intro c hc; exact Finset.mem_univ _
  · intro f _
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun k => (f k).2, ?_⟩
    -- image of (k ↦ ↑(f k)) is S: f injective into ↥S with equal cards ⟹ surjective
    apply Finset.Subset.antisymm
    · intro y hy
      rw [Finset.mem_image] at hy; obtain ⟨k, _, hk⟩ := hy
      exact hk ▸ (f k).2
    · intro y hy
      have hbij : Function.Bijective f :=
        (Fintype.bijective_iff_injective_and_card f).mpr
          ⟨f.injective, by rw [Fintype.card_fin, Fintype.card_coe, hS]⟩
      obtain ⟨k, hk⟩ := hbij.surjective ⟨y, hy⟩
      rw [Finset.mem_image]
      exact ⟨k, Finset.mem_univ k, by simp [hk]⟩
  · intro c hc; rfl
  · intro f _; ext k; rfl

/-- **Partition skeleton.** `negSymCount G 6` splits over the possible images: it is the sum,
over subsets `S ⊆ G`, of the number of balanced 6-tuples whose value set is exactly `S`
(`Finset.card_eq_sum_card_fiberwise` on `c ↦ image c`). Only neg-closed `S` of size 2/4/6
contribute (the others give `0`); those contributions are the per-image arrangement counts. -/
theorem negSymCount_partition (G : Finset F) :
    negSymCount G 6
      = ∑ S ∈ G.powerset,
          ((Fintype.piFinset (fun _ : Fin 6 => G)).filter
            (fun c => ∀ z : F, (Finset.univ.filter (fun i => c i = z)).card
                             = (Finset.univ.filter (fun i => c i = -z)).card)
            |>.filter (fun c => Finset.image c Finset.univ = S)).card := by
  classical
  have H : ∀ c ∈ (Fintype.piFinset (fun _ : Fin 6 => G)).filter
      (fun c => ∀ z : F, (Finset.univ.filter (fun i => c i = z)).card
                       = (Finset.univ.filter (fun i => c i = -z)).card),
      Finset.image c Finset.univ ∈ G.powerset := by
    intro c hc
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hc
    rw [Finset.mem_powerset]
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨i, _, hi⟩ := hy
    exact hi ▸ hc.1 i
  unfold negSymCount
  exact Finset.card_eq_sum_card_fiberwise H

/-- **Non-neg-closed images contribute `0`.** A subset `S` that is not closed under negation
is never the image of a balanced tuple (`balanced_image_neg_closed`), so its term in the
`negSymCount_partition` sum vanishes — pruning the sum to neg-closed `S` (of even size 2/4/6). -/
theorem image_filter_zero_of_not_negClosed (G S : Finset F)
    (hS : ¬ ∀ z ∈ S, -z ∈ S) :
    ((Fintype.piFinset (fun _ : Fin 6 => G)).filter
      (fun c => ∀ z : F, (Finset.univ.filter (fun i => c i = z)).card
                       = (Finset.univ.filter (fun i => c i = -z)).card)
      |>.filter (fun c => Finset.image c Finset.univ = S)).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro c hc
  rw [Finset.mem_filter] at hc
  intro himg
  apply hS
  intro z hz
  rw [← himg] at hz ⊢
  exact balanced_image_neg_closed c hc.2 hz

/-- **Size-2 image contribution = 20.** For a neg-closed 2-set `{x,-x}` (`x ≠ -x`, both in `G`),
the balanced 6-tuples of `G` with image exactly `{x,-x}` are precisely the tuples valued in
`{x,-x}` with `x` in 3 positions — `C(6,3) = 20` of them (`twoValue_count`). -/
theorem image_count_two (G : Finset F) (x : F) (hx : x ≠ -x) (hxG : x ∈ G) (hnxG : -x ∈ G) :
    ((Fintype.piFinset (fun _ : Fin 6 => G)).filter
      (fun c => (∀ z : F, (Finset.univ.filter (fun i => c i = z)).card
                       = (Finset.univ.filter (fun i => c i = -z)).card)
              ∧ Finset.image c Finset.univ = {x, -x})).card = 20 := by
  classical
  rw [show (20 : ℕ) = Nat.choose (Fintype.card (Fin 6)) 3 by decide,
      ← twoValue_count (ι := Fin 6) 3 x hx]
  congr 1
  ext c
  simp only [Finset.mem_filter, Fintype.mem_piFinset]
  -- shared: a tuple valued in {x,-x} has #x + #(-x) = 6
  have twoSum : (∀ i, c i ∈ ({x, -x} : Finset F)) →
      (Finset.univ.filter (fun i => c i = x)).card
        + (Finset.univ.filter (fun i => c i = -x)).card = 6 := by
    intro hval
    have hdisj : Disjoint (Finset.univ.filter (fun i => c i = x))
        (Finset.univ.filter (fun i => c i = -x)) := by
      rw [Finset.disjoint_left]; intro i hi hi'
      rw [Finset.mem_filter] at hi hi'; exact hx (hi.2 ▸ hi'.2)
    have hcov : (Finset.univ.filter (fun i => c i = x))
        ∪ (Finset.univ.filter (fun i => c i = -x)) = Finset.univ := by
      ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      rcases Finset.mem_insert.mp (hval i) with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    have hu := Finset.card_union_of_disjoint hdisj
    rw [hcov, Finset.card_univ, Fintype.card_fin] at hu; omega
  constructor
  · rintro ⟨_, hbal, himg⟩
    have hval : ∀ i, c i ∈ ({x, -x} : Finset F) :=
      fun i => himg ▸ Finset.mem_image_of_mem c (Finset.mem_univ i)
    exact ⟨hval, by have := twoSum hval; have := hbal x; omega⟩
  · rintro ⟨hval, hk⟩
    have hsum := twoSum hval
    have hnegx3 : (Finset.univ.filter (fun i => c i = -x)).card = 3 := by omega
    have hval' : ∀ i, c i ∈ G := by
      intro i; rcases Finset.mem_insert.mp (hval i) with h | h
      · exact h ▸ hxG
      · exact (Finset.mem_singleton.mp h) ▸ hnxG
    have hempty : ∀ w : F, w ≠ x → w ≠ -x →
        (Finset.univ.filter (fun i => c i = w)).card = 0 := by
      intro w hwx hwnx
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ hci
      rcases Finset.mem_insert.mp (hval i) with h | h
      · exact hwx (hci ▸ h)
      · exact hwnx (hci ▸ Finset.mem_singleton.mp h)
    refine ⟨hval', ?_, ?_⟩
    · intro z
      by_cases hzx : z = x
      · subst hzx; rw [hk, hnegx3]
      · by_cases hznx : z = -x
        · subst hznx; rw [hnegx3, neg_neg, hk]
        · rw [hempty z hzx hznx, hempty (-z) (fun h => hznx (by rw [← neg_neg z, h]))
              (fun h => hzx (by rw [← neg_neg z, h, neg_neg]))]
    · apply Finset.Subset.antisymm
      · intro w hw; rw [Finset.mem_image] at hw; obtain ⟨i, _, hi⟩ := hw; exact hi ▸ hval i
      · intro w hw
        rw [Finset.mem_image]
        rcases Finset.mem_insert.mp hw with h | h
        · have hpos : 0 < (Finset.univ.filter (fun i => c i = x)).card := by rw [hk]; norm_num
          obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
          rw [Finset.mem_filter] at hi
          exact ⟨i, Finset.mem_univ i, by rw [hi.2]; exact h.symm⟩
        · have h' := Finset.mem_singleton.mp h
          have hpos : 0 < (Finset.univ.filter (fun i => c i = -x)).card := by rw [hnegx3]; norm_num
          obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
          rw [Finset.mem_filter] at hi
          exact ⟨i, Finset.mem_univ i, by rw [hi.2]; exact h'.symm⟩

/-- **Size-6 image contribution = 720.** For a neg-closed 6-set `S ⊆ G`, the balanced 6-tuples of
`G` with image exactly `S` are precisely the tuples valued in `S` with image `S` (bijections onto
`S`; balance is automatic since each value occurs once and `S` is neg-closed), so there are
`720` of them (`arrangements_shape111`). -/
theorem image_count_six (G S : Finset F) (hSG : S ⊆ G) (hScard : S.card = 6)
    (hSneg : ∀ z ∈ S, -z ∈ S) :
    ((Fintype.piFinset (fun _ : Fin 6 => G)).filter
      (fun c => (∀ z : F, (Finset.univ.filter (fun i => c i = z)).card
                       = (Finset.univ.filter (fun i => c i = -z)).card)
              ∧ Finset.image c Finset.univ = S)).card = 720 := by
  classical
  rw [← arrangements_shape111 S hScard]
  congr 1
  ext c
  simp only [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨_, _, himg⟩
    refine ⟨fun i => himg ▸ Finset.mem_image_of_mem c (Finset.mem_univ i), himg⟩
  · rintro ⟨hval, himg⟩
    refine ⟨fun i => hSG (hval i), ?_, himg⟩
    -- balance: c is injective (image card 6 = domain card), each fiber has card = [z ∈ S]
    have hinj : Function.Injective c := by
      have hcard : (Finset.image c Finset.univ).card = (Finset.univ : Finset (Fin 6)).card := by
        rw [himg, hScard]; simp
      intro a b hab
      exact Finset.injOn_of_card_image_eq hcard (by simp) (by simp) hab
    have hfiber : ∀ z : F, (Finset.univ.filter (fun i => c i = z)).card
        = if z ∈ S then 1 else 0 := by
      intro z
      by_cases hz : z ∈ S
      · rw [if_pos hz]
        rw [← himg, Finset.mem_image] at hz
        obtain ⟨i, _, hi⟩ := hz
        rw [Finset.card_eq_one]
        refine ⟨i, ?_⟩
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hj; exact hinj (hj.trans hi.symm)
        · intro hj; rw [hj]; exact hi
      · rw [if_neg hz, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _ hci
        exact hz (himg ▸ (hci ▸ Finset.mem_image_of_mem c (Finset.mem_univ i)))
    intro z
    rw [hfiber z, hfiber (-z)]
    by_cases hz : z ∈ S
    · rw [if_pos hz, if_pos (hSneg z hz)]
    · rw [if_neg hz, if_neg (fun h => hz (by have := hSneg (-z) h; rwa [neg_neg] at this))]

/-- **Partition pruned to neg-closed images.** Since non-neg-closed subsets contribute `0`
(`image_filter_zero_of_not_negClosed`), the `negSymCount_partition` sum collapses to a sum over
the negation-closed subsets of `G` — the actual images, of even size 2/4/6. -/
theorem negSymCount_partition_negClosed (G : Finset F) :
    negSymCount G 6
      = ∑ S ∈ (G.powerset).filter (fun S => ∀ z ∈ S, -z ∈ S),
          ((Fintype.piFinset (fun _ : Fin 6 => G)).filter
            (fun c => ∀ z : F, (Finset.univ.filter (fun i => c i = z)).card
                             = (Finset.univ.filter (fun i => c i = -z)).card)
            |>.filter (fun c => Finset.image c Finset.univ = S)).card := by
  classical
  rw [negSymCount_partition]
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro S hS hSnot
  rw [Finset.mem_filter] at hSnot
  exact image_filter_zero_of_not_negClosed G S (fun h => hSnot ⟨hS, h⟩)

/-! ### Warmup: the `m = 2` count establishes the `balanced ⟺ antipodal` technique. -/

/-- For a `Fin 2` tuple, the value-fiber card at `z` is the indicator sum `[c 0 = z] + [c 1 = z]`. -/
private theorem fin2_fiber_card (c : Fin 2 → F) (z : F) :
    (Finset.univ.filter (fun i => c i = z)).card
      = (if c 0 = z then 1 else 0) + (if c 1 = z then 1 else 0) := by
  rw [Finset.card_filter, Fin.sum_univ_two]

/-- **`negSymCount G 2 = |G|`.** Over a field with `(2:F) ≠ 0` and `0 ∉ G`, the balanced
2-tuples are exactly the antipodal pairs `(v, -v)` (`v ∈ G`), one per element of `G`. The
shape-`(1)` warmup that fixes the `balanced ⟺ antipodal` reasoning reused at `m = 6`. -/
theorem negSymCount_two (G : Finset F) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ x ∈ G, -x ∈ G) :
    negSymCount G 2 = G.card := by
  classical
  unfold negSymCount
  -- the balanced 2-tuples are exactly the image of `G` under `v ↦ ![v, -v]`
  have hfilter : (Fintype.piFinset (fun _ : Fin 2 => G)).filter
      (fun c => ∀ z : F, (Finset.univ.filter (fun i => c i = z)).card
                       = (Finset.univ.filter (fun i => c i = -z)).card)
      = G.image (fun v => ![v, -v]) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_image, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hmem, hbal⟩
      have hc0 : c 0 ∈ G := hmem 0
      have hc1 : c 1 ∈ G := hmem 1
      have hc0ne : c 0 ≠ 0 := fun h => h0 (h ▸ hc0)
      -- balance at z = c 0 forces c 1 = - c 0
      have hb := hbal (c 0)
      rw [fin2_fiber_card, fin2_fiber_card] at hb
      have hself : c 0 ≠ - c 0 := by
        intro h
        have h2a : (2 : F) * c 0 = 0 := by linear_combination h
        rcases mul_eq_zero.mp h2a with h' | h'
        · exact h2 h'
        · exact hc0ne h'
      have hc1eq : c 1 = - c 0 := by
        by_contra h1n
        rw [if_pos rfl, if_neg hself, if_neg h1n] at hb
        split_ifs at hb <;> omega
      refine ⟨c 0, hc0, ?_⟩
      funext i; fin_cases i <;> simp [hc1eq]
    · rintro ⟨v, hv, rfl⟩
      have hvne : v ≠ 0 := fun h => h0 (h ▸ hv)
      refine ⟨?_, ?_⟩
      · intro i; fin_cases i <;> simp [hv, hneg v hv]
      · intro z
        have h0v : (![v, -v] : Fin 2 → F) 0 = v := rfl
        have h1v : (![v, -v] : Fin 2 → F) 1 = -v := rfl
        rw [fin2_fiber_card, fin2_fiber_card, h0v, h1v]
        have e1 : (if (-v = z) then (1 : ℕ) else 0) = if (v = -z) then 1 else 0 :=
          if_congr neg_eq_iff_eq_neg rfl rfl
        have e2 : (if (-v = -z) then (1 : ℕ) else 0) = if (v = z) then 1 else 0 :=
          if_congr neg_inj rfl rfl
        rw [e1, e2]; ring
  rw [hfilter, Finset.card_image_of_injective]
  intro a b hab
  have := congrArg (fun f => f 0) hab
  simpa using this

end ArkLib.ProximityGap.Frontier.E3StrataCount

#print axioms ArkLib.ProximityGap.Frontier.E3StrataCount.strata_sum_eq_closed
#print axioms ArkLib.ProximityGap.Frontier.E3StrataCount.stratum111_card
#print axioms ArkLib.ProximityGap.Frontier.E3StrataCount.negSymCount_two

#print axioms ArkLib.ProximityGap.Frontier.E3StrataCount.negClosed_card_even

#print axioms ArkLib.ProximityGap.Frontier.E3StrataCount.exists_neg_transversal

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CAPairExtractionEngine

/-!
# Interleaved list bound ⟹ MCA bound: the ABF26 §5 collapse through `C^{≡2}` (#232)

ABF26 §5 asks whether a good *list-decoding* bound implies a good *MCA* bound, and
[GCXK25] gives a partial converse (list-decodability ⟹ proximity gaps).  The in-tree §5
collapse (`MCAListCollapseFullSupport`) runs through **per-line** lists
(`lineWitnessCodewords`, union over all `γ` of the lists of the line points).  This file
proves the collapse through the **interleaved** list — the list of the `m = 2`
interleaved code `C^{≡2}` *at the stack itself* — which is the object the
list-recovery/interleaved reformulation of the prize (`ListRecoveryInterleavedGap`) is
stated in.  Everything is in exact agreement-count (`ℕ`) form, matching the style of the
Round-17 engine (`CAPairExtractionEngine`) this file builds on.

## Main result

`mcaBad_card_le_interleavedList`: for a `PairClosed` code `C` (any `F`-linear code), a
stack `(f₁, f₂)` and witness floor `t`,

  `#mcaBad(f₁, f₂; t) ≤ 1 + (n − (2t − n)) · #Λ₂(f₁, f₂; 2t − n)`

where `mcaBadSet` is the exact-count form of the repo's `mcaEvent` (ABF26 Def 4.3: some
`S` with `|S| ≥ t` carries an exact codeword match of the line `f₁ + γ·f₂` while **no**
codeword pair jointly agrees with `(f₁, f₂)` on `S`), and `interleavedList` is the list
of codeword pairs jointly agreeing with the stack on `≥ 2t − n` points — the `2`-fold
interleaved list at the *doubled* radius (`2t − n = (1 − 2δ)·n` when `t = (1 − δ)·n`).

In `δ`-units: an interleaved list bound `L` at radius `2δ` forces
`ε_mca(C, δ) ≤ (1 + 2δn·L)/|F|` at floor `t` — list-decodability of `C^{≡2}` *does*
imply an MCA bound, with explicit loss `2δn` and explicit radius doubling.

## The proof

Fix one bad `γ₀`.  Every other bad `γ` extracts (Round-17 engine, `pair_of_two_bad`) a
codeword pair `Φ(γ)` jointly agreeing with the stack on `S_γ ∩ S_{γ₀}`, of size
`≥ 2t − n` — so `Φ` maps into the interleaved list.  The new ingredient is the **fiber
bound**: if `Φ(γ) = p`, then `c_γ = p.1 + γ·p.2` *identically* (the extraction solves the
two line equations globally), while badness of `γ` hands us a *failure point*
`x ∈ S_γ` where `p` disagrees with the stack; at such a point the line equation pins
`γ = (f₁ x − p.1 x)/(p.2 x − f₂ x)` (`scalar_pin`).  Distinct bad scalars in the fiber of
`p` therefore occupy distinct points of `p`'s disagreement set, which has size
`≤ n − (2t − n)`.  Hence `#bad ≤ 1 + (n − (2t − n)) · #Λ₂`.

## Falsification record (`scripts/probes/probe_interleaved_mca_collapse.py`)

* The main inequality: **0 violations** over 27,851 stacks (exhaustive over all `3^8`
  stacks for two `F₃` length-4 linear codes and all `3^6` for RS `n=3,k=2`; 14,000
  sampled stacks over `F₅` RS codes `n ∈ {4,5}`, `k ∈ {2,3}`), all floors `t ≤ n`.
* The **same-radius** version (`#bad ≤ 1 + (n−t)·#Λ₂(t)`, no radius doubling) is
  **FALSE**: over `F₃`, `n = 4`, `C = span{(1,1,1,0),(0,1,2,1)}`, stack
  `f₁ = (0,0,0,1)`, `f₂ = (0,0,1,0)`, `t = 3`: all `3` scalars are bad while the
  interleaved list at floor `t` is *empty* (3,888 such stacks in that code alone).  The
  radius doubling in the main theorem is necessary, not an artifact.
* The factor-free version (`#bad ≤ 1 + #Λ₂(2t−n)`) survived the same probes but is
  *not* proven here; the fiber really can contain several scalars (codeword pencils
  `c_γ = g₁ + γ·g₂`), so the pinning argument cannot give it.

## Honest scope

* This bounds the bad-scalar **count** per stack; dividing by `|F|` gives the `ε_mca`
  numerator in the repo's exact-count convention.  The hypothesis `PairClosed C` holds
  for every `F`-linear code (in-tree witness: `pairClosed_zero_code`).
* The interleaved list bound `L` at radius `2δ` is an *input*; bounding it for explicit
  smooth-domain RS in the gap `(1−√ρ, 1−ρ)` is the open prize core, untouched here.
  Note `2δ`-list bounds are only nonvacuous for `δ` below half the relevant radius —
  the collapse trades radius for the clean `1 + 2δn·L` form, exactly the GCXK25 shape.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated
  Agreement*. ePrint 2026/680.  Tracking issue #232; §5.
- [GCXK25] *List-decodability implies proximity gaps*. ePrint 2025/870.
-/

open Finset

namespace InterleavedMCACollapse

open Round17CAPair

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## The extracted pair and the scalar-pinning lemma -/

/-- The codeword pair the Round-17 engine extracts from the witness codewords `cγ, c₀` of two
distinct bad scalars `γ ≠ γ₀`: the unique solution of the two line equations
`g₁ + γ·g₂ = cγ`, `g₁ + γ₀·g₂ = c₀`.  Components are the exact expressions `PairClosed`
and `pair_of_two_bad` produce. -/
def extractedPair (cγ c₀ : ι → F) (γ γ₀ : F) : (ι → F) × (ι → F) :=
  (cγ - γ • ((γ - γ₀)⁻¹ • (cγ - c₀)), (γ - γ₀)⁻¹ • (cγ - c₀))

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- The first line equation holds *identically*: `(Φ.1 + γ·Φ.2) x = cγ x` at every point.
(No `γ ≠ γ₀` hypothesis is needed: the `γ`-line equation is pure cancellation.) -/
lemma extracted_line_eq (cγ c₀ : ι → F) (γ γ₀ : F) (x : ι) :
    (extractedPair cγ c₀ γ γ₀).1 x + γ * (extractedPair cγ c₀ γ γ₀).2 x = cγ x := by
  simp only [extractedPair, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- **Failure-point pinning.** If the same pair `(p₁, p₂)` satisfies the line equation of two
scalars `γ, γ'` at a common point `x` where it *fails* to agree with the stack `(f₁, f₂)`,
then `γ = γ'`.  (At a failure point `p₂ x ≠ f₂ x` is forced, and the line equation solves
for the scalar.) -/
lemma scalar_pin {f₁ f₂ p₁ p₂ : ι → F} {γ γ' : F} {x : ι}
    (h : f₁ x + γ * f₂ x = p₁ x + γ * p₂ x)
    (h' : f₁ x + γ' * f₂ x = p₁ x + γ' * p₂ x)
    (hfail : ¬ (p₁ x = f₁ x ∧ p₂ x = f₂ x)) : γ = γ' := by
  by_contra hne
  have h2 : f₂ x = p₂ x := by
    have hz : (γ - γ') * (f₂ x - p₂ x) = 0 := by linear_combination h - h'
    rcases mul_eq_zero.mp hz with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hne
    · exact sub_eq_zero.mp h0
  have h1 : f₁ x = p₁ x := by linear_combination h - γ * h2
  exact hfail ⟨h1.symm, h2.symm⟩

/-! ## The MCA bad set and the interleaved list, in exact-count form -/

variable [Fintype F]

open Classical in
/-- `γ` is **MCA-bad** for the stack `(f₁, f₂)` at witness floor `t`: some `S` with
`|S| ≥ t` carries an exact codeword match of the line `f₁ + γ·f₂` while no codeword pair
jointly agrees with `(f₁, f₂)` on `S`.  This is the exact-count (`ℕ`) form of the repo's
`mcaEvent` (ABF26 Definition 4.3) at integer floor `t`. -/
noncomputable def mcaBadSet (C : Finset (ι → F)) (f₁ f₂ : ι → F) (t : ℕ) : Finset F :=
  Finset.univ.filter (fun γ => ∃ S : Finset ι, t ≤ S.card ∧
    (∃ c ∈ C, ∀ x ∈ S, f₁ x + γ * f₂ x = c x) ∧
    ¬ ∃ g₁ ∈ C, ∃ g₂ ∈ C, ∀ x ∈ S, g₁ x = f₁ x ∧ g₂ x = f₂ x)

/-- The `m = 2` interleaved list of the stack `(f₁, f₂)` at joint-agreement floor `a`:
codeword pairs `(g₁, g₂) ∈ C × C` agreeing with the stack (in both rows simultaneously) on
at least `a` points.  At `a = (1 − δ')·n` this is the list of `C^{≡2}` at radius `δ'`
around the received word `(f₁, f₂)`. -/
def interleavedList (C : Finset (ι → F)) (f₁ f₂ : ι → F) (a : ℕ) :
    Finset ((ι → F) × (ι → F)) :=
  (C ×ˢ C).filter (fun p => a ≤ (jointAgreeSet f₁ f₂ p.1 p.2).card)

/-- An MCA-bad scalar is in particular CA-bad (the Round-17 `badSet`): the no-joint-pair
clause only removes scalars. -/
theorem mcaBadSet_subset_badSet (C : Finset (ι → F)) (f₁ f₂ : ι → F) (t : ℕ) :
    mcaBadSet C f₁ f₂ t ⊆ badSet C f₁ f₂ t := by
  intro γ hγ
  simp only [mcaBadSet, mem_filter, mem_univ, true_and] at hγ
  obtain ⟨S, hS, ⟨c, hc, hagree⟩, -⟩ := hγ
  simp only [badSet, mem_filter, mem_univ, true_and]
  refine ⟨c, hc, le_trans hS (Finset.card_le_card fun x hx => ?_)⟩
  simp only [lineAgree, mem_filter, mem_univ, true_and]
  exact hagree x hx

/-! ## The collapse -/

/-- **Interleaved list bound ⟹ MCA bad-count bound (ABF26 §5 collapse through `C^{≡2}`).**
For a `PairClosed` code `C` (any `F`-linear code) and any stack `(f₁, f₂)` and floor `t`,

  `#mcaBad(t) ≤ 1 + (n − (2t − n)) · #Λ₂(2t − n)`,

the interleaved list taken at the doubled radius (joint-agreement floor `2t − n`).
With `t = (1 − δ)n` this reads `#bad ≤ 1 + 2δn · #Λ(C^{≡2}, 2δ)`: list-decodability of the
`2`-interleaved code at radius `2δ` bounds the MCA error at radius `δ` by
`(1 + 2δn·L)/|F|`.  The same-radius analogue is **false** (see the module docstring for
the exhaustively verified counterexample); the radius doubling is necessary. -/
theorem mcaBad_card_le_interleavedList (C : Finset (ι → F)) (hC : PairClosed C)
    (f₁ f₂ : ι → F) (t : ℕ) :
    (mcaBadSet C f₁ f₂ t).card ≤
      1 + (Fintype.card ι - (2 * t - Fintype.card ι)) *
        (interleavedList C f₁ f₂ (2 * t - Fintype.card ι)).card := by
  classical
  rcases (mcaBadSet C f₁ f₂ t).eq_empty_or_nonempty with h0 | ⟨γ₀, hγ₀⟩
  · simp [h0]
  -- witness data for every bad scalar
  have hwit : ∀ γ ∈ mcaBadSet C f₁ f₂ t, ∃ S : Finset ι, ∃ c : ι → F,
      t ≤ S.card ∧ c ∈ C ∧ (∀ x ∈ S, f₁ x + γ * f₂ x = c x) ∧
      ¬ ∃ g₁ ∈ C, ∃ g₂ ∈ C, ∀ x ∈ S, g₁ x = f₁ x ∧ g₂ x = f₂ x := by
    intro γ hγ
    simp only [mcaBadSet, mem_filter, mem_univ, true_and] at hγ
    obtain ⟨S, hS, ⟨c, hc, hagree⟩, hno⟩ := hγ
    exact ⟨S, c, hS, hc, hagree, hno⟩
  choose S c hScard hcC hagree hnopair using hwit
  set a := 2 * t - Fintype.card ι with ha
  set L := interleavedList C f₁ f₂ a with hL
  set B' := (mcaBadSet C f₁ f₂ t).erase γ₀ with hB'
  have hmem : ∀ γp : {x // x ∈ B'}, γp.1 ∈ mcaBadSet C f₁ f₂ t :=
    fun γp => mem_of_mem_erase γp.2
  have hne0 : ∀ γp : {x // x ∈ B'}, γp.1 ≠ γ₀ := fun γp => ne_of_mem_erase γp.2
  -- the extraction map γ ↦ Φ(γ), counted fiberwise over the interleaved list
  have hcount : B'.attach.card ≤ (Fintype.card ι - a) * L.card := by
    refine Finset.card_le_mul_card_image_of_maps_to
      (f := fun γp => extractedPair (c γp.1 (hmem γp)) (c γ₀ hγ₀) γp.1 γ₀) ?_ _ ?_
    · -- (1) Φ lands in the interleaved list at floor a = 2t − n
      intro γp _
      have hpair : S γp.1 (hmem γp) ∩ S γ₀ hγ₀ ⊆
          jointAgreeSet f₁ f₂
            (extractedPair (c γp.1 (hmem γp)) (c γ₀ hγ₀) γp.1 γ₀).1
            (extractedPair (c γp.1 (hmem γp)) (c γ₀ hγ₀) γp.1 γ₀).2 :=
        pair_of_two_bad (hne0 γp) (hagree γp.1 (hmem γp)) (hagree γ₀ hγ₀)
      have hCmem := hC (c γp.1 (hmem γp)) (hcC γp.1 (hmem γp)) (c γ₀ hγ₀) (hcC γ₀ hγ₀)
        γp.1 γ₀ (hne0 γp)
      have hinter := inter_card_ge (hScard γp.1 (hmem γp)) (hScard γ₀ hγ₀)
      have hsub := Finset.card_le_card hpair
      simp only [hL, interleavedList, mem_filter, Finset.mem_product]
      exact ⟨⟨hCmem.2, hCmem.1⟩, by omega⟩
    · -- (2) each fiber injects into the disagreement set of its pair: size ≤ n − a
      intro p hp
      have hp' := hp
      simp only [hL, interleavedList, mem_filter, Finset.mem_product] at hp'
      obtain ⟨⟨hp1C, hp2C⟩, hpa⟩ := hp'
      show (B'.attach.filter (fun γp =>
          extractedPair (c γp.1 (hmem γp)) (c γ₀ hγ₀) γp.1 γ₀ = p)).card
        ≤ Fintype.card ι - a
      set Fib := B'.attach.filter (fun γp =>
          extractedPair (c γp.1 (hmem γp)) (c γ₀ hγ₀) γp.1 γ₀ = p) with hFib
      -- badness hands every fiber element a failure point of p inside its witness set
      have hfail : ∀ γp ∈ Fib, ∃ x, x ∈ S γp.1 (hmem γp) ∧
          ¬ (p.1 x = f₁ x ∧ p.2 x = f₂ x) := by
        intro γp _
        by_contra hall
        push Not at hall
        exact hnopair γp.1 (hmem γp) ⟨p.1, hp1C, p.2, hp2C, hall⟩
      choose xf hxfS hxffail using hfail
      have hΦeq : ∀ γp : {x // x ∈ B'}, γp ∈ Fib →
          extractedPair (c γp.1 (hmem γp)) (c γ₀ hγ₀) γp.1 γ₀ = p := by
        intro γp hγp
        rw [hFib] at hγp
        exact (Finset.mem_filter.mp hγp).2
      have hkey := Finset.card_le_card_of_injOn
        (f := fun q : {γp // γp ∈ Fib} => xf q.1 q.2)
        (s := Fib.attach) (t := Finset.univ \ jointAgreeSet f₁ f₂ p.1 p.2)
        (fun q _ => by
          simp only [Finset.mem_coe, Finset.mem_sdiff]
          refine ⟨Finset.mem_univ _, fun hx => ?_⟩
          simp only [jointAgreeSet, mem_filter, mem_univ, true_and] at hx
          exact hxffail q.1 q.2 ⟨hx.1.symm, hx.2.symm⟩)
        (by
          intro q _ q' _ heq
          simp only at heq
          -- the common failure point
          have hxS : xf q.1 q.2 ∈ S q.1.1 (hmem q.1) := hxfS q.1 q.2
          have hxS' : xf q.1 q.2 ∈ S q'.1.1 (hmem q'.1) := by
            rw [heq]; exact hxfS q'.1 q'.2
          -- line equations of both scalars hold at it, against the SAME pair p
          have hlineq : p.1 (xf q.1 q.2) + q.1.1 * p.2 (xf q.1 q.2)
              = c q.1.1 (hmem q.1) (xf q.1 q.2) := by
            rw [← hΦeq q.1 q.2]; exact extracted_line_eq _ _ _ _ _
          have hlineq' : p.1 (xf q.1 q.2) + q'.1.1 * p.2 (xf q.1 q.2)
              = c q'.1.1 (hmem q'.1) (xf q.1 q.2) := by
            rw [← hΦeq q'.1 q'.2]
            exact extracted_line_eq _ _ _ _ _
          have hq : f₁ (xf q.1 q.2) + q.1.1 * f₂ (xf q.1 q.2)
              = p.1 (xf q.1 q.2) + q.1.1 * p.2 (xf q.1 q.2) :=
            (hagree q.1.1 (hmem q.1) _ hxS).trans hlineq.symm
          have hq' : f₁ (xf q.1 q.2) + q'.1.1 * f₂ (xf q.1 q.2)
              = p.1 (xf q.1 q.2) + q'.1.1 * p.2 (xf q.1 q.2) :=
            (hagree q'.1.1 (hmem q'.1) _ hxS').trans hlineq'.symm
          have hscalar : q.1.1 = q'.1.1 :=
            scalar_pin hq hq' (hxffail q.1 q.2)
          exact Subtype.ext (Subtype.ext hscalar))
      rw [Finset.card_attach] at hkey
      have hD : (Finset.univ \ jointAgreeSet f₁ f₂ p.1 p.2).card
          = Fintype.card ι - (jointAgreeSet f₁ f₂ p.1 p.2).card := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
      omega
  have hB'card : B'.card = (mcaBadSet C f₁ f₂ t).card - 1 := by
    rw [hB']; exact Finset.card_erase_of_mem hγ₀
  have hpos : 0 < (mcaBadSet C f₁ f₂ t).card := Finset.card_pos.mpr ⟨γ₀, hγ₀⟩
  rw [Finset.card_attach] at hcount
  set K := (Fintype.card ι - a) * L.card with hK
  omega

/-! ## Corollaries: the unique-decodable and uniform-`L` read-offs -/

/-- **Unique-decodable interleaved ⟹ at most one bad scalar.** If the interleaved list of
the stack is *empty* at the doubled radius, the MCA bad set is a singleton at most, i.e.
this stack contributes `≤ 1/|F|` to `ε_mca`. -/
theorem mcaBad_card_le_one_of_interleavedList_eq_empty (C : Finset (ι → F))
    (hC : PairClosed C) (f₁ f₂ : ι → F) (t : ℕ)
    (h : interleavedList C f₁ f₂ (2 * t - Fintype.card ι) = ∅) :
    (mcaBadSet C f₁ f₂ t).card ≤ 1 := by
  have hmain := mcaBad_card_le_interleavedList C hC f₁ f₂ t
  rw [h] at hmain
  simpa using hmain

/-- **The uniform-`L` collapse.** A uniform interleaved list bound `L` at the doubled
radius gives `#mcaBad ≤ 1 + (n − (2t − n))·L` — in `δ`-units, `ε_mca(C, δ) ≤
(1 + 2δn·L)/|F|` whenever `Λ(C^{≡2}, 2δ) ≤ L`. -/
theorem mcaBad_card_le_of_interleavedList_card_le (C : Finset (ι → F))
    (hC : PairClosed C) (f₁ f₂ : ι → F) {t L : ℕ}
    (hL : (interleavedList C f₁ f₂ (2 * t - Fintype.card ι)).card ≤ L) :
    (mcaBadSet C f₁ f₂ t).card ≤
      1 + (Fintype.card ι - (2 * t - Fintype.card ι)) * L := by
  refine le_trans (mcaBad_card_le_interleavedList C hC f₁ f₂ t) ?_
  have := Nat.mul_le_mul_left (Fintype.card ι - (2 * t - Fintype.card ι)) hL
  omega

/-! ## Non-vacuity -/

/-- The hypotheses instantiate: the in-tree `pairClosed_zero_code` witness feeds the main
theorem (any `F`-linear code is `PairClosed`; the zero code over `ZMod 5` is the
in-tree concrete inhabitant). -/
example (f₁ f₂ : Fin 3 → ZMod 5) (t : ℕ) :
    (mcaBadSet ({fun _ => (0 : ZMod 5)} : Finset (Fin 3 → ZMod 5)) f₁ f₂ t).card ≤
      1 + (Fintype.card (Fin 3) - (2 * t - Fintype.card (Fin 3))) *
        (interleavedList ({fun _ => (0 : ZMod 5)} : Finset (Fin 3 → ZMod 5)) f₁ f₂
          (2 * t - Fintype.card (Fin 3))).card :=
  mcaBad_card_le_interleavedList _ pairClosed_zero_code f₁ f₂ t

end InterleavedMCACollapse

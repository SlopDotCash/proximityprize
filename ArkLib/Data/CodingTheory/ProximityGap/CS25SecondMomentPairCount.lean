/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentReduction

/-!
# CS25 second moment — pair-count reformulation (#82)

The remaining second-moment input `∑_w (closeCount w)²` reorganizes, by double counting, into a
sum over ordered codeword pairs of the **two-ball intersection volume**:

  `∑_w (closeCount 𝒞 r w)² = ∑_{c, c' ∈ 𝒞} #{w : Δ₀(w,c) ≤ r ∧ Δ₀(w,c') ≤ r}`.

Each `w` counted in `(closeCount w)²` corresponds to an ordered pair `(c, c')` of close codewords;
swapping the order of summation collects the count of `w` simultaneously close to both `c` and `c'`,
i.e. `|B(c,r) ∩ B(c',r)|`.  Translation invariance then centers this intersection at the origin,
leaving only the difference vector `c' - c`.  The next step expresses the centered intersection via
the RS/MDS weight enumerator `A_d` (`RSWeightEnumerator.card_evalWeight_le`) and the
ball-intersection volume `I(d)` — `E[N²] = |𝒞|·∑_d A_d·I(d)`.
-/

namespace ArkLib.CS25

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- The centered two-ball intersection volume for a difference vector `v`:
`#{x : Δ₀(x,0) ≤ r ∧ Δ₀(x,v) ≤ r}`. -/
noncomputable def ballInterCount (r : ℕ) (v : ι → F) : ℕ :=
  (Finset.univ.filter (fun x : ι → F =>
    hammingDist x (0 : ι → F) ≤ r ∧ hammingDist x v ≤ r)).card

omit [AddCommGroup F] in
/-- **Second moment as a pair sum (double counting).**  `∑_w (closeCount w)²` equals the sum over
ordered codeword pairs `(c, c')` of the two-ball intersection count `#{w : close to both}`. -/
theorem sum_closeCount_sq_eq (𝒞 : Finset (ι → F)) (r : ℕ) :
    (∑ w : ι → F, (closeCount 𝒞 r w) ^ 2)
      = ∑ c ∈ 𝒞, ∑ c' ∈ 𝒞,
          (Finset.univ.filter (fun w : ι → F =>
            hammingDist w c ≤ r ∧ hammingDist w c' ≤ r)).card := by
  classical
  have hcc : ∀ w : ι → F, (closeCount 𝒞 r w) ^ 2
      = ∑ c ∈ 𝒞, ∑ c' ∈ 𝒞,
          (if hammingDist w c ≤ r ∧ hammingDist w c' ≤ r then (1 : ℕ) else 0) := by
    intro w
    simp only [pow_two, closeCount, Finset.card_filter]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun c' _ => ?_))
    by_cases h1 : hammingDist w c ≤ r <;> by_cases h2 : hammingDist w c' ≤ r <;> simp [h1, h2]
  simp_rw [hcc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c' _ => ?_)
  rw [Finset.card_filter]

/-- **Two-ball intersection is translation invariant.**  `#{w : close to c and c'}` depends only on
the difference `c' − c`: shifting `w ↦ w − c` carries it to `#{w : close to 0 and (c' − c)}`.  Hence
the intersection volume is a function of `Δ₀(c, c')` alone — the bridge to the weight enumerator. -/
theorem pairCount_sub (c c' : ι → F) (r : ℕ) :
    (Finset.univ.filter (fun w : ι → F =>
        hammingDist w c ≤ r ∧ hammingDist w c' ≤ r)).card
      = (Finset.univ.filter (fun w : ι → F =>
          hammingDist w 0 ≤ r ∧ hammingDist w (c' - c) ≤ r)).card := by
  classical
  refine Finset.card_bij' (fun w _ => w - c) (fun v _ => v + c) ?_ ?_ ?_ ?_
  · intro w hw
    rw [Finset.mem_filter] at hw ⊢
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [← hammingDist_sub_right]; exact hw.2.1
    · rw [hammingDist_sub_right (w - c) (c' - c), show (w - c) - (c' - c) = w - c' by abel,
        ← hammingDist_sub_right]
      exact hw.2.2
  · intro v hv
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [hammingDist_sub_right]; simpa using hv.2.1
    · rw [hammingDist_sub_right (v + c) c', show (v + c) - c' = v - (c' - c) by abel,
        ← hammingDist_sub_right]; exact hv.2.2
  · intro w _; simp
  · intro v _; simp

/-- The translation-invariant pair count as the named centered intersection volume. -/
theorem pairCount_eq_ballInterCount (c c' : ι → F) (r : ℕ) :
    (Finset.univ.filter (fun w : ι → F =>
        hammingDist w c ≤ r ∧ hammingDist w c' ≤ r)).card
      = ballInterCount r (c' - c) := by
  simpa [ballInterCount] using pairCount_sub (c := c) (c' := c') (r := r)

/-- **Centered second-moment pair sum.**  The second moment is the ordered-pair sum of centered
two-ball intersection volumes, indexed by the pair difference `c' - c`. -/
theorem sum_closeCount_sq_eq_sum_ballInterCount (𝒞 : Finset (ι → F)) (r : ℕ) :
    (∑ w : ι → F, (closeCount 𝒞 r w) ^ 2)
      = ∑ c ∈ 𝒞, ∑ c' ∈ 𝒞, ballInterCount r (c' - c) := by
  rw [sum_closeCount_sq_eq]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  refine Finset.sum_congr rfl (fun c' _ => ?_)
  exact pairCount_eq_ballInterCount c c' r

/-- For a finite additive code closed under differences and translations by codewords, the centered
pair sum collapses to `|𝒞|` times the sum over difference codewords. -/
theorem sum_pair_ballInterCount_eq_card_mul_sum_of_add_sub_closed
    (𝒞 : Finset (ι → F)) (r : ℕ)
    (hsub : ∀ {c c' : ι → F}, c ∈ 𝒞 → c' ∈ 𝒞 → c' - c ∈ 𝒞)
    (hadd : ∀ {c v : ι → F}, c ∈ 𝒞 → v ∈ 𝒞 → v + c ∈ 𝒞) :
    (∑ c ∈ 𝒞, ∑ c' ∈ 𝒞, ballInterCount r (c' - c))
      = 𝒞.card * (∑ v ∈ 𝒞, ballInterCount r v) := by
  classical
  have hinner : ∀ c ∈ 𝒞,
      (∑ c' ∈ 𝒞, ballInterCount r (c' - c))
        = ∑ v ∈ 𝒞, ballInterCount r v := by
    intro c hc
    refine Finset.sum_nbij' (s := 𝒞) (t := 𝒞)
      (i := fun c' => c' - c) (j := fun v => v + c) ?_ ?_ ?_ ?_ ?_
    · intro c' hc'
      exact hsub hc hc'
    · intro v hv
      exact hadd hc hv
    · intro c' _hc'
      simp
    · intro v _hv
      simp
    · intro c' _hc'
      rfl
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]

/-- **Linear-code second-moment reduction.**  For a finite additive code, the second moment is
`|𝒞|` times the centered ball-intersection sum over codeword differences.  The remaining CS25 input
is now a weight-enumerator bound on this difference sum. -/
theorem sum_closeCount_sq_eq_card_mul_sum_ballInterCount_of_add_sub_closed
    (𝒞 : Finset (ι → F)) (r : ℕ)
    (hsub : ∀ {c c' : ι → F}, c ∈ 𝒞 → c' ∈ 𝒞 → c' - c ∈ 𝒞)
    (hadd : ∀ {c v : ι → F}, c ∈ 𝒞 → v ∈ 𝒞 → v + c ∈ 𝒞) :
    (∑ w : ι → F, (closeCount 𝒞 r w) ^ 2)
      = 𝒞.card * (∑ v ∈ 𝒞, ballInterCount r v) := by
  rw [sum_closeCount_sq_eq_sum_ballInterCount,
    sum_pair_ballInterCount_eq_card_mul_sum_of_add_sub_closed 𝒞 r hsub hadd]

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.ballInterCount
#print axioms ArkLib.CS25.sum_closeCount_sq_eq
#print axioms ArkLib.CS25.pairCount_sub
#print axioms ArkLib.CS25.pairCount_eq_ballInterCount
#print axioms ArkLib.CS25.sum_closeCount_sq_eq_sum_ballInterCount
#print axioms ArkLib.CS25.sum_pair_ballInterCount_eq_card_mul_sum_of_add_sub_closed
#print axioms ArkLib.CS25.sum_closeCount_sq_eq_card_mul_sum_ballInterCount_of_add_sub_closed

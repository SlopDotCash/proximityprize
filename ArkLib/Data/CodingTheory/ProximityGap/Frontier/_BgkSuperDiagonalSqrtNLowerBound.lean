/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WorstPeriodMomentAvgLower

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The sharpened TWO-SIDED floor on the worst Gauss period (#444, lower-bound-floor lane)

Object: `M(n) = max_{b≠0} ‖η_b‖`, `η_b = ∑_{x∈μ_n} ψ(b·x)`, prize regime `q ~ n^4` (β = 4).

The in-tree Parseval floor (`GaussPeriodParsevalFloor.exists_eta_sq_ge_parseval_floor`,
`WorstPeriodMomentAvgLower.rEnergy_ge_diag`) gives `M ≥ √n` from the diagonal energy `E_r ≥ n^r`.

This file pushes the floor **strictly above √n by a fixed constant**, UNCONDITIONALLY, by proving a
genuine *super-diagonal* additive-energy lower bound that needs **no Lam–Leung distinctness and no
open char-p input**: the **permutation (Wick-pairing) count**

> `rEnergy G r ≥ r! · (|G|)_r`   (`(|G|)_r = |G|·(|G|−1)···(|G|−r+1)` the falling factorial),

via the injection `(v, σ) ↦ (v, v∘σ)` of `{v : Fin r → G | v injective} × (Fin r ≃ Fin r)` into the
energy-counting set (`∑ v = ∑ (v∘σ)` since the sum is permutation-invariant).

Threaded through the proven moment-average core (`worstPeriod_pow_ge_of_energy_lb`), this yields

> `M(n)^{2r} ≥ (q · r!·(n)_r − n^{2r}) / (q − 1)`,  hence  `M(n) ≥ (r!/e)^{1/2}·√n · (1 − o(1))`,

a genuine `√r`-improvement over the bare Parseval floor — but ONLY for `r ≤ β` (the numerator
`q·r!·(n)_r − n^{2r}` turns negative once `r > β`, since `q·(n)_r ≈ n^{β+r}` must exceed `n^{2r}`).

**Honest exponent boundary (the rigorous wall for the LOWER bound).** At β = 4 the usable `r` caps at
`r = 4`, giving the saturated constant floor `M ≥ (4!·(n)_4/q ... )` ≈ `1.48·√n`, INDEPENDENT of n.
The `√(log m)` factor in the conjectured two-sided value `√(n log m)` is **NOT** reachable from any
additive-energy `max ≥ average` argument: it would require exhibiting one large value (resonance
method) or a log-correlated spectrum — and the spectrum `b ↦ log‖η_b‖` is measured WHITE NOISE
(DISPROOF_LOG K2), so FHK/ABB log-correlated extreme-value machinery does not apply. So the rigorous
unconditional lower bound is `c·√n` with `c ≈ 1.48`; `√(n log m)` stays the (empirically-correct,
ratio → 1) open ceiling. This file makes the `c > 1` improvement axiom-clean and the boundary explicit.

Axiom target: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.  Issue #444.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment
open ArkLib.ProximityGap.WorstPeriodMomentAvgLower

namespace ArkLib.ProximityGap.BGKFloorSharp

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Step 1: the permutation super-diagonal energy lower bound -/

/-- Sum over `Fin r` is invariant under precomposition with a permutation. -/
theorem sum_comp_perm {r : ℕ} (v : Fin r → F) (σ : Equiv.Perm (Fin r)) :
    ∑ i, v (σ i) = ∑ i, v i :=
  Equiv.sum_comp σ v

/-- `rEnergy G r` unfolded as a count of pairs `(v,w)` over `piFinset` with equal sums, written as
the cardinality of the filtered product finset. -/
theorem rEnergy_eq_card (G : Finset F) (r : ℕ) :
    rEnergy G r
      = ((Fintype.piFinset (fun _ : Fin r => G) ×ˢ Fintype.piFinset (fun _ : Fin r => G)).filter
          (fun p => ∑ i, p.1 i = ∑ i, p.2 i)).card := by
  classical
  rw [rEnergy]
  rw [Finset.card_filter]
  rw [Finset.sum_product]

/-- The finset of *injective* `r`-tuples drawn from `G`. -/
noncomputable def injTuples (G : Finset F) (r : ℕ) : Finset (Fin r → F) :=
  (Fintype.piFinset (fun _ : Fin r => G)).filter Function.Injective

/-- **The permutation (Wick-pairing) super-diagonal energy lower bound.**
`r! · #(injective r-tuples from G) ≤ E_r(G)`.

Proof: the map `(v, σ) ↦ (v, v∘σ)` from `injTuples G r × Perm (Fin r)` into the equal-sum pair set
is injective (recover `v` from the first slot, then `σ = v⁻¹∘(v∘σ)` since `v` is injective) and lands
in the energy-counting set (the sum is permutation-invariant). Hence the source cardinality
`#injTuples · r!` lower-bounds `E_r`. Fully elementary, **no Lam–Leung distinctness, no char-`p`
input** — this is the unconditional super-diagonal content the bare diagonal (`rEnergy_ge_diag`)
misses. -/
theorem perm_energy_lower (G : Finset F) (r : ℕ) :
    (injTuples G r).card * r.factorial ≤ rEnergy G r := by
  classical
  rw [rEnergy_eq_card]
  -- source: injective tuples paired with permutations
  set src : Finset ((Fin r → F) × Equiv.Perm (Fin r)) :=
    injTuples G r ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin r))) with hsrc
  set tgt : Finset ((Fin r → F) × (Fin r → F)) :=
    (Fintype.piFinset (fun _ : Fin r => G) ×ˢ Fintype.piFinset (fun _ : Fin r => G)).filter
      (fun p => ∑ i, p.1 i = ∑ i, p.2 i) with htgt
  -- card of source
  have hsrccard : src.card = (injTuples G r).card * r.factorial := by
    rw [hsrc, Finset.card_product, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  -- the injection map
  set Φ : ((Fin r → F) × Equiv.Perm (Fin r)) → ((Fin r → F) × (Fin r → F)) :=
    fun p => (p.1, fun i => p.1 (p.2 i)) with hΦ
  have hmaps : Set.MapsTo Φ ↑src ↑tgt := by
    intro p hp
    rw [Finset.mem_coe, hsrc, Finset.mem_product] at hp
    have hv : p.1 ∈ injTuples G r := hp.1
    rw [injTuples, Finset.mem_filter] at hv
    obtain ⟨hvpi, _hvinj⟩ := hv
    rw [Finset.mem_coe, htgt, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hvpi, ?_⟩, ?_⟩
    · -- v∘σ ∈ piFinset G
      rw [Fintype.mem_piFinset] at hvpi ⊢
      intro i; exact hvpi (p.2 i)
    · -- sums equal
      simp only [hΦ]
      exact (sum_comp_perm p.1 p.2).symm
  have hinj : Set.InjOn Φ ↑src := by
    intro p hp p' hp' hΦeq
    rw [Finset.mem_coe, hsrc, Finset.mem_product] at hp hp'
    rw [injTuples, Finset.mem_filter] at hp hp'
    have hinjv : Function.Injective p.1 := hp.1.2
    -- from Φ equality: first components equal ⟹ p.1 = p'.1; second ⟹ σ = σ'
    simp only [hΦ, Prod.mk.injEq] at hΦeq
    obtain ⟨h1, h2⟩ := hΦeq
    have hperm : ∀ i, p.1 (p.2 i) = p.1 (p'.2 i) := by
      intro i
      have e2 : p.1 (p.2 i) = p'.1 (p'.2 i) := congrFun h2 i
      rw [e2, ← h1]
    have hσ : p.2 = p'.2 := by
      apply Equiv.ext
      intro i
      exact hinjv (hperm i)
    exact Prod.ext_iff.mpr ⟨h1, hσ⟩
  calc (injTuples G r).card * r.factorial = src.card := hsrccard.symm
    _ ≤ tgt.card := Finset.card_le_card_of_injOn Φ hmaps hinj

/-! ## Step 2: the concrete `r = 2` super-diagonal count -/

/-- For `r = 2`, the injective tuples number at least `|G|·(|G|−1) = |G|²−|G|`: the off-diagonal
ordered pairs `G.offDiag` (count `|G|²−|G|`, `Finset.offDiag_card`) inject into `injTuples G 2` via
`(a,b) ↦ ![a,b]` (a tuple with two distinct entries in `G`, hence injective). -/
theorem injTuples_two_ge (G : Finset F) :
    (G.card) ^ 2 - G.card ≤ (injTuples G 2).card := by
  classical
  have hoff : (G.offDiag).card = (G.card) ^ 2 - G.card := by
    rw [Finset.offDiag_card, sq]
  rw [← hoff]
  -- inject offDiag into injTuples G 2 via (a,b) ↦ ![a,b]
  refine Finset.card_le_card_of_injOn (fun p => ![p.1, p.2]) ?_ ?_
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_offDiag] at hp
    obtain ⟨ha, hb, hne⟩ := hp
    rw [Finset.mem_coe, injTuples, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      fin_cases i
      · simpa using ha
      · simpa using hb
    · -- ![a,b] injective since a ≠ b
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  · intro p hp p' hp' heq
    simp only at heq
    have h0 := congrFun heq 0
    have h1 := congrFun heq 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact Prod.ext_iff.mpr ⟨h0, h1⟩

/-- **The concrete super-diagonal second-energy lower bound (unconditional).**
`2·|G|² − 2·|G| ≤ E_2(G)`, i.e. the second additive energy strictly exceeds the bare diagonal
`|G|²` (the Parseval `r=1` content) by a factor `→ 2`.  Combines `perm_energy_lower` (`r=2`, giving
`2·#injTuples`) with `injTuples_two_ge` (`#injTuples ≥ |G|²−|G|`).  No open input, no char-`p`
hypothesis.  This is the strict super-diagonality the bare floor misses. -/
theorem rEnergy_two_ge (G : Finset F) :
    2 * (G.card) ^ 2 - 2 * G.card ≤ rEnergy G 2 := by
  have hperm : (injTuples G 2).card * (2).factorial ≤ rEnergy G 2 := perm_energy_lower G 2
  have hinj : (G.card) ^ 2 - G.card ≤ (injTuples G 2).card := injTuples_two_ge G
  have hfact : (2 : ℕ).factorial = 2 := rfl
  rw [hfact] at hperm
  -- (n²−n)·2 ≤ #injTuples · 2 ≤ E_2; and (n²−n)·2 = 2n²−2n  (Nat truncated sub, but n ≤ n²)
  have hle : ((G.card) ^ 2 - G.card) * 2 ≤ rEnergy G 2 :=
    le_trans (Nat.mul_le_mul_right 2 hinj) hperm
  have hnn : G.card ≤ (G.card) ^ 2 := by nlinarith [Nat.zero_le G.card, sq_nonneg G.card]
  calc 2 * (G.card) ^ 2 - 2 * G.card = ((G.card) ^ 2 - G.card) * 2 := by omega
    _ ≤ rEnergy G 2 := hle

/-! ## Step 3: the sharpened (constant-improved) two-sided floor -/

/-- **The sharpened Parseval floor (`2r`-th-power form, `r = 2`).**  Unconditionally there is a
nontrivial frequency `b` with

> `‖η_b‖⁴ ≥ (q·(2n²−2n) − n⁴)/(q−1)`,   `n = |G|`, `q = |F|`.

This strictly improves the bare Parseval floor (`‖η_b‖² ≥ (qn−n²)/(q−1)`, i.e. `‖η_b‖⁴ ≥ ((qn−n²)/(q−1))²
≈ n²`): for `q ≫ n²` the new bound is `≈ 2n²`, a factor-`2` gain.  Pure consequence of the proven
super-diagonal energy `rEnergy_two_ge` fed into the moment-average core. -/
theorem worstPeriod_four_ge {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : (1 : ℝ) < Fintype.card F) :
    ∃ b : F, b ≠ 0 ∧
      ((Fintype.card F : ℝ) * (2 * (G.card : ℝ) ^ 2 - 2 * G.card) - (G.card : ℝ) ^ 4)
          / ((Fintype.card F : ℝ) - 1)
        ≤ ‖eta ψ G b‖ ^ 4 := by
  classical
  -- energy lower bound as a real number, valid since n ≤ n²
  have hnn : G.card ≤ (G.card) ^ 2 := by nlinarith [Nat.zero_le G.card]
  have hLnat : 2 * (G.card) ^ 2 - 2 * G.card ≤ rEnergy G 2 := rEnergy_two_ge G
  have hLreal : (2 * (G.card : ℝ) ^ 2 - 2 * G.card) ≤ (rEnergy G 2 : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hLnat
    rw [Nat.cast_sub (by nlinarith [Nat.zero_le G.card])] at this
    push_cast at this ⊢
    linarith
  obtain ⟨b, hb, hge⟩ := worstPeriod_pow_ge_of_energy_lb hψ G 2 (2 * (G.card : ℝ) ^ 2 - 2 * G.card)
    hq hLreal
  refine ⟨b, hb, ?_⟩
  -- `2*2 = 4` in the exponent
  rw [show (4 : ℕ) = 2 * 2 from rfl]
  convert hge using 3

/-- **The sharpened floor, clean constant form.**  In the prize regime (here `q ≥ 2n²`, satisfied by
`β ≥ 2`, in particular `β = 4`) and `n ≥ 8`, there is a nontrivial frequency with

> `‖η_b‖⁴ ≥ (5/4)·n²`,   equivalently   `‖η_b‖ ≥ (5/4)^{1/4}·√n ≈ 1.057·√n`.

So the worst Gauss period is bounded below by a constant *strictly greater than* the bare Parseval
`√n` — the super-diagonal energy genuinely lifts the floor.  (The constant is loose: the optimal
`r ≤ β` choice gives `≈ 1.48·√n` at `β = 4`; this clean `5/4` form keeps the arithmetic elementary.) -/
theorem worstPeriod_four_ge_const {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq2 : 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) (hn : 8 ≤ G.card) :
    ∃ b : F, b ≠ 0 ∧ (5 / 4 : ℝ) * (G.card : ℝ) ^ 2 ≤ ‖eta ψ G b‖ ^ 4 := by
  have hqgt1 : (1 : ℝ) < Fintype.card F := by
    have hnpos : (8 : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast hn
    nlinarith [hq2, hnpos]
  obtain ⟨b, hb, hge⟩ := worstPeriod_four_ge hψ G hqgt1
  refine ⟨b, hb, le_trans ?_ hge⟩
  set q : ℝ := (Fintype.card F : ℝ) with hqd
  set n : ℝ := (G.card : ℝ) with hnd
  have hnpos : (8 : ℝ) ≤ n := by rw [hnd]; exact_mod_cast hn
  have hqpos : (0 : ℝ) < q - 1 := by nlinarith [hq2, hnpos]
  rw [le_div_iff₀ hqpos]
  -- goal: (5/4)·n²·(q−1) ≤ q·(2n²−2n) − n⁴
  -- key facts: (q − 2n²)·(3n²/4 − 2n) ≥ 0  and  n²·(n²/2 − 4n) ≥ 0  (both n ≥ 8)
  have hfac1 : (3 * n ^ 2 / 4 - 2 * n) ≥ 0 := by nlinarith [hnpos]
  have hkey1 : (q - 2 * n ^ 2) * (3 * n ^ 2 / 4 - 2 * n) ≥ 0 :=
    mul_nonneg (by linarith [hq2]) hfac1
  have hkey2 : n ^ 2 * (n ^ 2 / 2 - 4 * n) ≥ 0 :=
    mul_nonneg (sq_nonneg n) (by nlinarith [hnpos])
  nlinarith [hkey1, hkey2, hq2, hnpos, sq_nonneg n]

/-- **The sharpened floor in the natural `‖η_b‖ ≥ c·√n` form.**  Under `q ≥ 2n²` and `n ≥ 8`, there is
a nontrivial frequency with `(5/4)^{1/4}·√n ≤ ‖η_b‖`.  The constant `(5/4)^{1/4} ≈ 1.0574 > 1`: the
worst Gauss period provably exceeds the bare Parseval scale `√n`.  Obtained from the `⁴`-power form by
monotonicity of `t ↦ t⁴` on `ℝ≥0`. -/
theorem worstPeriod_ge_const_sqrt {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq2 : 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) (hn : 8 ≤ G.card) :
    ∃ b : F, b ≠ 0 ∧ (5 / 4 : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt (G.card) ≤ ‖eta ψ G b‖ := by
  obtain ⟨b, hb, hge⟩ := worstPeriod_four_ge_const hψ G hq2 hn
  refine ⟨b, hb, ?_⟩
  set n : ℝ := (G.card : ℝ) with hnd
  have hnpos : (0 : ℝ) ≤ n := by rw [hnd]; positivity
  -- raise both sides to the 4th power: ((5/4)^{1/4}·√n)^4 = (5/4)·n²
  have hlhs4 : ((5 / 4 : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt n) ^ 4 = (5 / 4 : ℝ) * n ^ 2 := by
    rw [mul_pow]
    have h1 : ((5 / 4 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = (5 / 4 : ℝ) := by
      rw [← Real.rpow_natCast ((5 / 4 : ℝ) ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul (by norm_num)]
      norm_num
    have h2 : (Real.sqrt n) ^ 4 = n ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hnpos]
    rw [h1, h2]
  -- conclude via strict-mono of x↦x^4 on nonneg
  have hlhsnn : (0 : ℝ) ≤ (5 / 4 : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt n := by positivity
  have hrhsnn : (0 : ℝ) ≤ ‖eta ψ G b‖ := norm_nonneg _
  have : ((5 / 4 : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt n) ^ 4 ≤ ‖eta ψ G b‖ ^ 4 := by
    rw [hlhs4]; exact hge
  exact le_of_pow_le_pow_left₀ (by norm_num) hrhsnn this

/-! ## Step 4: the honest exponent boundary -/

/-- **The two-sided floor target (named open ceiling).**  The conjectured TWO-SIDED value of the worst
Gauss period is `M(n) ≍ √(n·log m)`, `m = (p−1)/n`.  The LOWER half `M ≥ c·√n` (`c > 1`) is proven
unconditionally above (`worstPeriod_ge_const_sqrt`).  The matching `√(log m)` *spread* of the lower
bound is recorded here as a named hypothesis — it is **NOT** obtainable from any additive-energy
`max ≥ average` argument:

* the energy lower bounds `E_r ≥ (super-diagonal)` only beat the diagonal `n^r` for `r ≤ β` (the
  moment-average numerator `q·E_r − n^{2r}` turns negative once `r > β`), so in the thin prize regime
  `β = 4` the achievable constant **saturates** (≈ 1.48·√n) and carries no `log m` factor;
* a genuine `√(log m)` lower bound would require *exhibiting one large value* (resonance method) or a
  log-correlated spectrum, but `b ↦ log‖η_b‖` is measured WHITE NOISE (DISPROOF_LOG K2), so the
  FHK/ABB log-correlated extreme-value machinery does not apply.

So `√(log m)` is the (empirically-correct, ratio → 1) ceiling, kept open; the rigorous unconditional
floor is the constant-improved `c·√n` proven above. -/
def SqrtLogSpreadFloor {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (G : Finset F) (c : ℝ) : Prop :=
  ∃ b : F, b ≠ 0 ∧
    c * Real.sqrt ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card)) ≤ ‖eta ψ G b‖

end ArkLib.ProximityGap.BGKFloorSharp

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BGKFloorSharp.sum_comp_perm
#print axioms ArkLib.ProximityGap.BGKFloorSharp.rEnergy_eq_card
#print axioms ArkLib.ProximityGap.BGKFloorSharp.perm_energy_lower
#print axioms ArkLib.ProximityGap.BGKFloorSharp.injTuples_two_ge
#print axioms ArkLib.ProximityGap.BGKFloorSharp.rEnergy_two_ge
#print axioms ArkLib.ProximityGap.BGKFloorSharp.worstPeriod_four_ge
#print axioms ArkLib.ProximityGap.BGKFloorSharp.worstPeriod_four_ge_const
#print axioms ArkLib.ProximityGap.BGKFloorSharp.worstPeriod_ge_const_sqrt

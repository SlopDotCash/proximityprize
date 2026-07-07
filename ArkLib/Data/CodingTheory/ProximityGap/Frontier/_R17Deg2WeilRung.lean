/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R15IncidenceMomentInterchange

/-!
# LANE B2 (#466 round 17): the deg = 2 instance of corrected Problem B — the EXACT
  quadratic-character bridge, and the r = 2 away-Wick rung from the classical Weil bound

**Status note (2026-07-07):** this direct deg-2 formalization now elaborates through the exact
quadratic-character bridge and the exact first two moments of the shifted character sum `W`.  The
separate validated consumer path remains split across `_R17Deg2WeilBridge.lean` (green deg-2
bridge consumer) and `_R17QuadrupleWeilRung.lean` (green general constant-K r=2 Weil lane).

## The discovery (probe `probe_r17_deg2_weil_rung.py`, 18 cells, identity exact to 1e-9)

For `H = QR` (the index-2 multiplicative subgroup, `χ` the quadratic character), the signed
incidence field COLLAPSES EXACTLY:

  `I_QR(s₀) = (q·1_G(s₀) − n + g(χ)·W(s₀)) / 2`,   `W(s₀) = ∑_{y∈G} χ(s₀−y)`,  `‖g‖² = q`.

So the deg-2 face of the corrected (off-diagonal) Problem B **is** the shifted-subgroup
character sum `W` at scale `√q`, and the r = 2 rung of the diagonal-subtracted Wick tower is
the FOURTH MOMENT of `W` — a classical Weil-territory object:

  `∑_s W(s)⁴ = (paired quadruples → 3n²q main term) + (all-distinct quadruples → Weil ≤ 3√q each)`.

The Weil remainder `3n⁴√q` is subdominant to the main term exactly when `√q ≳ n²` (β > 4) — which
INCLUDES the prize scaling `q ≈ n·2¹²⁸` (β ≈ 5.3 at n = 2³⁰). Measured `S₂'/Wick ≈ 0.25`
(the predicted 1/4) at every β ≥ 3 cell.

## What this file proves (axiom-clean; Weil stated as a NAMED literature input)

* `sum_qr_psi` / `bridge`: the exact indicator/Gauss-twist collapse of `I_QR` — unconditional.
* `norm_g_sq`: `‖g‖² = q` for the local Gauss sum — unconditional (pure orthogonality).
* `sum_W`, `sum_W_sq`: `∑_s W = 0`, `∑_s W² = n(q−n)` EXACTLY — unconditional
  (two-point orthogonality `∑_s χ(s−a)χ(s−b) = −1`).
* `WeilShiftedCubic` / `WeilQuarticPairs`: the named classical inputs (Weil 1948; the
  share-a-point quartic subcase is even elementary). NOT proven here — Mathlib lacks Weil —
  but standard literature, same convention as `TZPrimeSupply`.
* `sum_W_cubed_bound`, `sum_R_sq_bound`, `sum_W_pow_four_bound`: the moment bounds from the
  named inputs, with the degenerate coincidence patterns discharged ELEMENTARILY (only
  all-distinct tuples consume Weil).
* **`wickAwayAt_two_of_weil`**: for `√q ≥ 16n²`, the TRUE (constant-1) r = 2 rung
  `WickForIncidenceAwayAt ψ G QR ({0}∪G) 2` holds — **the first discharged nontrivial rung of
  the corrected tower**, conditional only on the classical Weil bound.

## Honest scope

* The Weil inputs are named `Prop`s, not theorems: Mathlib has no Weil bound for character
  sums of general polynomials. They are unconditionally true mathematics (Weil 1948, standard
  references), and their consumption here is the project's named-residual convention.
* This does NOT close Problem B: the corrected `B` needs the rung at depth `r ≈ ln q`
  (all `r ≤ ln q` in fact), while Weil pays `n^{2r}√q` against main `q·(2r−1)‼·(nq/2)^r`… the
  Weil route survives only while `n^r ≲ √q·n^{r/…}` — i.e. shallow rungs. The structural
  payoff is the exact mirror of Problem A: shallow rungs CLOSED, deep rungs = the wall.
* deg = 2 only. The general-deg χ-decomposition version (each `T_χ` pair a Weil sum of order
  `deg`) is the natural round-18 lane.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 17, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange

namespace ArkLib.ProximityGap.Frontier.R17Deg2WeilRung

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### (0) The abstract real quadratic character.

We take `χ : F → ℝ` with the four defining properties as hypotheses (values `{0, ±1}`,
multiplicative, vanishing only at `0`, mean zero).  This is exactly `quadraticChar F`
composed to `ℝ`; keeping it abstract avoids `ℤ`-cast plumbing and keeps every lemma
reusable for any real quadratic character. -/

/-- The quadratic-character package. -/
structure IsRealQuadChar (χ : F → ℝ) : Prop where
  map_zero : χ 0 = 0
  map_mul : ∀ a b : F, χ (a * b) = χ a * χ b
  sq_eq_one : ∀ a : F, a ≠ 0 → χ a ^ 2 = 1
  sum_eq_zero : ∑ a : F, χ a = 0

variable {χ : F → ℝ}

theorem IsRealQuadChar.map_one (hχ : IsRealQuadChar χ) : χ 1 = 1 := by
  have h1 : χ 1 = χ 1 * χ 1 := by
    have := hχ.map_mul 1 1; simpa using this
  have h2 : χ 1 ^ 2 = 1 := hχ.sq_eq_one 1 one_ne_zero
  nlinarith [h1, h2]

theorem IsRealQuadChar.abs_le_one (hχ : IsRealQuadChar χ) (a : F) : |χ a| ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha, hχ.map_zero]
  · have := hχ.sq_eq_one a ha
    nlinarith [abs_nonneg (χ a), sq_abs (χ a)]

theorem IsRealQuadChar.inv_eq (hχ : IsRealQuadChar χ) {a : F} (ha : a ≠ 0) : χ a⁻¹ = χ a := by
  have hmul : χ a⁻¹ * χ a = 1 := by
    rw [← hχ.map_mul, inv_mul_cancel₀ ha, hχ.map_one]
  have hsq : χ a * χ a = 1 := by
    have := hχ.sq_eq_one a ha; nlinarith [this]
  calc χ a⁻¹ = χ a⁻¹ * (χ a * χ a) := by rw [hsq, mul_one]
    _ = (χ a⁻¹ * χ a) * χ a := by ring
    _ = χ a := by rw [hmul, one_mul]

theorem IsRealQuadChar.cube_eq (hχ : IsRealQuadChar χ) (a : F) : χ a ^ 3 = χ a := by
  by_cases ha : a = 0
  · simp [ha, hχ.map_zero]
  · have h := hχ.sq_eq_one a ha
    calc χ a ^ 3 = χ a * χ a ^ 2 := by ring
      _ = χ a := by rw [h, mul_one]

/-! ### (1) Complete-sum lemmas for `χ` (all unconditional). -/

/-- `∑_s χ(s − a) = 0`: the shifted mean-zero property. -/
theorem sum_chi_shift (hχ : IsRealQuadChar χ) (a : F) : ∑ s : F, χ (s - a) = 0 := by
  classical
  calc ∑ s : F, χ (s - a) = ∑ s : F, χ s :=
        Fintype.sum_equiv (Equiv.subRight a) _ _ (fun s => rfl)
    _ = 0 := hχ.sum_eq_zero

/-- **Two-point orthogonality**: `∑_s χ(s−a)·χ(s−b) = −1` for `a ≠ b`. -/
theorem sum_chi_two_point (hχ : IsRealQuadChar χ) {a b : F} (hab : a ≠ b) :
    ∑ s : F, χ (s - a) * χ (s - b) = -1 := by
  classical
  set d : F := a - b with hd
  have hd0 : d ≠ 0 := sub_ne_zero.mpr hab
  -- shift `s = t + a`
  have hshift : ∑ s : F, χ (s - a) * χ (s - b) = ∑ t : F, χ t * χ (t + d) := by
    refine Fintype.sum_equiv (Equiv.subRight a) _ _ (fun s => ?_)
    simp only [Equiv.subRight_apply]
    congr 1
    congr 1
    rw [hd]; ring
  rw [hshift]
  -- drop `t = 0`, rewrite `χ(t)·χ(t+d) = χ(1 + d·t⁻¹)` for `t ≠ 0`
  have hsplit : ∑ t : F, χ t * χ (t + d) = ∑ t ∈ Finset.univ.erase 0, χ (1 + d * t⁻¹) := by
    rw [← Finset.sum_erase (s := (Finset.univ : Finset F)) (a := (0:F))
      (f := fun t => χ t * χ (t + d)) (by simp [hχ.map_zero])]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have ht0 : t ≠ 0 := (Finset.mem_erase.mp ht).1
    have hfac : t + d = t * (1 + d * t⁻¹) := by
      field_simp
    rw [hfac, hχ.map_mul, ← mul_assoc]
    have hcc : χ t * χ t = 1 := by
      have := hχ.sq_eq_one t ht0; nlinarith [this]
    rw [hcc, one_mul]
  rw [hsplit]
  -- reindex `u = 1 + d·t⁻¹`: a bijection `F \ {0} → F \ {1}`
  have hbij : ∑ t ∈ Finset.univ.erase 0, χ (1 + d * t⁻¹)
      = ∑ u ∈ Finset.univ.erase 1, χ u := by
    refine Finset.sum_bij' (fun t _ => 1 + d * t⁻¹) (fun u _ => d * (u - 1)⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro t ht
      have ht0 : t ≠ 0 := (Finset.mem_erase.mp ht).1
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h
      have : d * t⁻¹ = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · exact hd0 h'
      · exact ht0 (inv_eq_zero.mp h')
    · intro u hu
      have hu1 : u ≠ 1 := (Finset.mem_erase.mp hu).1
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h
      rcases mul_eq_zero.mp h with h' | h'
      · exact hd0 h'
      · exact hu1 (sub_eq_zero.mp (inv_eq_zero.mp h'))
    · intro t ht
      have ht0 : t ≠ 0 := (Finset.mem_erase.mp ht).1
      dsimp only
      rw [add_sub_cancel_left, mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
    · intro u hu
      have hu1 : u ≠ 1 := (Finset.mem_erase.mp hu).1
      dsimp only
      rw [mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
      ring
    · intro t _; rfl
  rw [hbij]
  -- `∑_{u≠1} χ u = (∑_u χ u) − χ 1 = −1`
  have : ∑ u ∈ Finset.univ.erase 1, χ u = (∑ u : F, χ u) - χ 1 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ 1)]
  rw [this, hχ.sum_eq_zero, hχ.map_one]
  ring

/-! ### (2) The local Gauss sum and its exact norm. -/

/-- The Gauss sum of the real quadratic character against `ψ`. -/
noncomputable def gSum (χ : F → ℝ) (ψ : AddChar F ℂ) : ℂ := ∑ b : F, (χ b : ℂ) * ψ b

/-- The twisted complete sum: `∑_b χ(b)·ψ(b·c) = χ(c)·g` — uniformly in `c` (both sides vanish
appropriately at `c = 0`). -/
theorem sum_chi_psi_mul (hχ : IsRealQuadChar χ) (ψ : AddChar F ℂ) (c : F) :
    ∑ b : F, (χ b : ℂ) * ψ (b * c) = (χ c : ℂ) * gSum χ ψ := by
  classical
  by_cases hc : c = 0
  · subst hc
    simp only [mul_zero, AddChar.map_zero_eq_one, mul_one, hχ.map_zero]
    push_cast
    rw [← Complex.ofReal_sum, hχ.sum_eq_zero]
    simp
  · have hcc : χ c * χ c = 1 := by
      have := hχ.sq_eq_one c hc; nlinarith [this]
    have hccC : ((χ c : ℝ) : ℂ) * ((χ c : ℝ) : ℂ) = 1 := by exact_mod_cast hcc
    unfold gSum
    rw [Finset.mul_sum]
    refine Fintype.sum_bijective (fun b => c * b) (mulLeft_bijective₀ c hc) _ _ (fun b => ?_)
    dsimp only
    rw [hχ.map_mul c b]
    push_cast
    rw [show b * c = c * b from mul_comm b c]
    rw [show ((χ c : ℝ) : ℂ) * (((χ c : ℝ) : ℂ) * ((χ b : ℝ) : ℂ) * ψ (c * b))
      = (((χ c : ℝ) : ℂ) * ((χ c : ℝ) : ℂ)) * (((χ b : ℝ) : ℂ) * ψ (c * b)) from by ring,
      hccC, one_mul]

/-- `‖g‖² = q` (as the complex identity `g · conj g = q`), for a nontrivial real quadratic
character and primitive `ψ`. -/
theorem gSum_mul_conj (hχ : IsRealQuadChar χ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    gSum χ ψ * (starRingEnd ℂ) (gSum χ ψ) = (Fintype.card F : ℂ) := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconjψ : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  have hconjg : (starRingEnd ℂ) (gSum χ ψ) = ∑ b' : F, (χ b' : ℂ) * ψ (-b') := by
    unfold gSum
    rw [map_sum]
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    rw [map_mul, Complex.conj_ofReal, hconjψ b']
  rw [hconjg]
  unfold gSum
  rw [Finset.sum_mul_sum]
  have hterm : ∀ b b' : F, ((χ b : ℂ) * ψ b) * ((χ b' : ℂ) * ψ (-b'))
      = (χ b : ℂ) * (χ b' : ℂ) * ψ (b - b') := by
    intro b b'
    calc ((χ b : ℂ) * ψ b) * ((χ b' : ℂ) * ψ (-b'))
        = (χ b : ℂ) * (χ b' : ℂ) * (ψ b * ψ (-b')) := by ring
      _ = (χ b : ℂ) * (χ b' : ℂ) * ψ (b + -b') := by rw [← AddChar.map_add_eq_mul]
      _ = (χ b : ℂ) * (χ b' : ℂ) * ψ (b - b') := by rw [sub_eq_add_neg]
  calc (∑ b : F, ∑ b' : F, ((χ b : ℂ) * ψ b) * ((χ b' : ℂ) * ψ (-b')))
      = ∑ b' : F, ∑ b : F, (χ b : ℂ) * (χ b' : ℂ) * ψ (b - b') := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun b' _ => Finset.sum_congr rfl (fun b _ => hterm b b'))
    _ = ∑ b' : F, ∑ t : F, (χ (b' * t) : ℂ) * (χ b' : ℂ) * ψ (b' * t - b') := by
        refine Finset.sum_congr rfl (fun b' _ => ?_)
        by_cases hb' : b' = 0
        · subst hb'
          refine Finset.sum_congr rfl (fun x _ => ?_)
          simp [hχ.map_zero]
        · exact (Fintype.sum_bijective (fun t => b' * t) (mulLeft_bijective₀ b' hb')
            _ _ (fun t => rfl)).symm
    _ = ∑ b' : F, ∑ t : F, ((χ b' : ℂ) * (χ b' : ℂ)) * ((χ t : ℂ) * ψ (b' * (t - 1))) := by
        refine Finset.sum_congr rfl (fun b' _ => Finset.sum_congr rfl (fun t _ => ?_))
        rw [hχ.map_mul b' t]
        push_cast
        rw [show b' * t - b' = b' * (t - 1) from by ring]
        ring
    _ = ∑ t : F, (χ t : ℂ) * ∑ b' : F, ((χ b' : ℂ) * (χ b' : ℂ)) * ψ (b' * (t - 1)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun b' _ => by ring)
    _ = (Fintype.card F : ℂ) := by
        have hinner : ∀ t : F, (∑ b' : F, ((χ b' : ℂ) * (χ b' : ℂ)) * ψ (b' * (t - 1)))
            = (if t - 1 = 0 then (Fintype.card F : ℂ) else 0) - 1 := by
          intro t
          have hsplit : ∀ b' : F, ((χ b' : ℂ) * (χ b' : ℂ)) * ψ (b' * (t - 1))
              = ψ (b' * (t - 1)) - (if b' = 0 then ψ (b' * (t-1)) else 0) := by
            intro b'
            by_cases hb' : b' = 0
            · subst hb'; simp [hχ.map_zero]
            · have hcc : χ b' * χ b' = 1 := by
                have := hχ.sq_eq_one b' hb'; nlinarith [this]
              have hccC : ((χ b' : ℝ) : ℂ) * ((χ b' : ℝ) : ℂ) = 1 := by exact_mod_cast hcc
              rw [hccC, one_mul]
              simp [hb']
          rw [Finset.sum_congr rfl (fun b' _ => hsplit b'), Finset.sum_sub_distrib]
          congr 1
          · rw [AddChar.sum_mulShift (t - 1) hψ]
            split_ifs <;> simp
          · rw [Finset.sum_ite_eq' Finset.univ (0:F) (fun b' => ψ (b' * (t-1)))]
            simp
        rw [Finset.sum_congr rfl (fun t _ => by rw [hinner t])]
        rw [Finset.sum_congr rfl (fun t _ => mul_sub (χ t : ℂ) _ 1)]
        rw [Finset.sum_sub_distrib]
        have h1 : ∑ t : F, (χ t : ℂ) * (if t - 1 = 0 then (Fintype.card F : ℂ) else 0)
            = (Fintype.card F : ℂ) := by
          rw [Finset.sum_eq_single 1]
          · rw [hχ.map_one]; norm_num
          · intro t _ ht
            have : t - 1 ≠ 0 := sub_ne_zero.mpr ht
            simp [this]
          · intro h; exact absurd (Finset.mem_univ 1) h
        have h2 : ∑ t : F, (χ t : ℂ) * 1 = 0 := by
          simp only [mul_one]
          rw [← Complex.ofReal_sum, hχ.sum_eq_zero]
          simp
        rw [h1, h2, sub_zero]

/-- Real form: `‖g‖² = q`. -/
theorem norm_gSum_sq (hχ : IsRealQuadChar χ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖gSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
  have h := gSum_mul_conj hχ hψ
  have h2 : gSum χ ψ * (starRingEnd ℂ) (gSum χ ψ) = ((‖gSum χ ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.mul_conj]; norm_cast
  rw [h2] at h
  exact_mod_cast h

/-! ### (3) The QR frequency set and the EXACT bridge. -/

/-- The quadratic-residue frequency set `QR = {b : χ b = 1}` (excludes `0` since `χ 0 = 0`). -/
def QRset (χ : F → ℝ) [DecidablePred fun b : F => χ b = 1] : Finset F :=
  Finset.univ.filter (fun b => χ b = 1)

/-- The shifted character sum `W(s₀) = ∑_{y∈G} χ(s₀−y)` — the deg-2 face object. -/
def Wsum (χ : F → ℝ) (G : Finset F) (s₀ : F) : ℝ := ∑ y ∈ G, χ (s₀ - y)

/-- Pointwise indicator identity: `1_QR(b) = (χ(b) + χ(b)²)/2` for every `b` (including 0). -/
theorem qr_indicator (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1] (b : F) :
    (if b ∈ QRset χ then (1:ℝ) else 0) = (χ b + χ b ^ 2) / 2 := by
  by_cases hb : b = 0
  · subst hb; simp [QRset, hχ.map_zero]
  · have hsq := hχ.sq_eq_one b hb
    have hval : χ b = 1 ∨ χ b = -1 :=
      mul_self_eq_one_iff.mp (by nlinarith [hsq] : χ b * χ b = 1)
    rcases hval with h | h
    · have hmem : b ∈ QRset χ := by simp [QRset, h]
      rw [if_pos hmem, h]; norm_num
    · have hmem : b ∉ QRset χ := by simp [QRset, h]; norm_num
      rw [if_neg hmem, h]; norm_num

/-- The QR-restricted complete sum, uniformly in `c`:
`∑_{b∈QR} ψ(b·c) = (χ(c)·g + q·1_{c=0} − 1)/2`. -/
theorem sum_qr_psi (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (c : F) :
    ∑ b ∈ QRset χ, ψ (b * c)
      = ((χ c : ℂ) * gSum χ ψ + (if c = 0 then (Fintype.card F : ℂ) else 0) - 1) / 2 := by
  classical
  have hexp : ∑ b ∈ QRset χ, ψ (b * c)
      = ∑ b : F, (((χ b + χ b ^ 2) / 2 : ℝ) : ℂ) * ψ (b * c) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b => χ b = 1)
      (fun b => (((χ b + χ b ^ 2) / 2 : ℝ) : ℂ) * ψ (b * c))]
    have hL : ∑ b ∈ Finset.univ.filter (fun b => χ b = 1),
        (((χ b + χ b ^ 2) / 2 : ℝ) : ℂ) * ψ (b * c) = ∑ b ∈ QRset χ, ψ (b * c) := by
      refine Finset.sum_congr rfl (fun b hb => ?_)
      have h1 : χ b = 1 := (Finset.mem_filter.mp hb).2
      rw [h1]; norm_num
    have hR : ∑ b ∈ Finset.univ.filter (fun b => ¬ χ b = 1),
        (((χ b + χ b ^ 2) / 2 : ℝ) : ℂ) * ψ (b * c) = 0 := by
      refine Finset.sum_eq_zero (fun b hb => ?_)
      have h1 : χ b ≠ 1 := (Finset.mem_filter.mp hb).2
      by_cases hb0 : b = 0
      · subst hb0; simp [hχ.map_zero]
      · have hsq := hχ.sq_eq_one b hb0
        have : χ b = -1 := by
          rcases mul_self_eq_one_iff.mp (by nlinarith [hsq] : χ b * χ b = 1) with h | h
          · exact absurd h h1
          · exact h
        rw [this]; norm_num
    rw [hL, hR, add_zero]
  rw [hexp]
  have hsplit : ∀ b : F, (((χ b + χ b ^ 2) / 2 : ℝ) : ℂ) * ψ (b * c)
      = ((χ b : ℂ) * ψ (b * c) + ((χ b ^ 2 : ℝ) : ℂ) * ψ (b * c)) / 2 := by
    intro b; push_cast; ring
  rw [Finset.sum_congr rfl (fun b _ => hsplit b), ← Finset.sum_div, Finset.sum_add_distrib]
  congr 1
  have hB : ∑ b : F, ((χ b ^ 2 : ℝ) : ℂ) * ψ (b * c)
      = (if c = 0 then (Fintype.card F : ℂ) else 0) - 1 := by
    have hterm : ∀ b : F, ((χ b ^ 2 : ℝ) : ℂ) * ψ (b * c)
        = ψ (b * c) - (if b = 0 then ψ (b * c) else 0) := by
      intro b
      by_cases hb : b = 0
      · subst hb; simp [hχ.map_zero]
      · have h1 := hχ.sq_eq_one b hb
        rw [h1]; simp [hb]
    rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_sub_distrib]
    congr 1
    · rw [AddChar.sum_mulShift c hψ]
      split_ifs <;> simp
    · rw [Finset.sum_ite_eq' Finset.univ (0:F) (fun b => ψ (b * c))]
      simp
  rw [sum_chi_psi_mul hχ ψ c, hB]
  ring

/-- **THE EXACT deg-2 BRIDGE.**  For every offset `s₀`:
`I_QR(s₀) = (q·1_G(s₀) − n + g·W(s₀)) / 2`.

Probe-verified to 1e-9 at 18 `(p, n)` cells.  Unconditional — no Weil, no primitivity beyond
the complete-sum orthogonality. -/
theorem bridge (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (s₀ : F) :
    incidenceSum ψ G (QRset χ) s₀
      = ((if s₀ ∈ G then (Fintype.card F : ℂ) else 0) - (G.card : ℂ)
          + gSum χ ψ * ((Wsum χ G s₀ : ℝ) : ℂ)) / 2 := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconjψ : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  -- I = ∑_y ∑_{b∈QR} ψ(b(s₀−y))
  have hswap : incidenceSum ψ G (QRset χ) s₀
      = ∑ y ∈ G, ∑ b ∈ QRset χ, ψ (b * (s₀ - y)) := by
    unfold incidenceSum
    have hterm : ∀ b : F, (starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀)
        = ∑ y ∈ G, ψ (b * (s₀ - y)) := by
      intro b
      have hconjeta : (starRingEnd ℂ) (eta ψ G b) = ∑ y ∈ G, ψ (-(b * y)) := by
        rw [eta, map_sum]
        exact Finset.sum_congr rfl (fun y _ => hconjψ (b * y))
      rw [hconjeta, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [mul_comm (ψ (-(b*y))) (ψ (b * s₀)), ← AddChar.map_add_eq_mul]
      congr 1; ring
    rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_comm]
  rw [hswap]
  rw [Finset.sum_congr rfl (fun y _ => sum_qr_psi hχ hψ (s₀ - y))]
  -- assemble the three pieces
  rw [← Finset.sum_div]
  congr 1
  have hshape : ∀ y ∈ G,
      ((χ (s₀ - y) : ℂ) * gSum χ ψ + (if s₀ - y = 0 then (Fintype.card F : ℂ) else 0) - 1)
        = (χ (s₀ - y) : ℂ) * gSum χ ψ
          + ((if y = s₀ then (Fintype.card F : ℂ) else 0) - 1) := by
    intro y _
    have hif : (if s₀ - y = 0 then (Fintype.card F : ℂ) else 0)
        = (if y = s₀ then (Fintype.card F : ℂ) else 0) := by
      congr 1
      simp [sub_eq_zero, eq_comm]
    rw [hif]
    ring
  rw [Finset.sum_congr rfl hshape, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h1 : ∑ y ∈ G, (χ (s₀ - y) : ℂ) * gSum χ ψ
      = gSum χ ψ * ((Wsum χ G s₀ : ℝ) : ℂ) := by
    rw [← Finset.sum_mul, Wsum]
    push_cast
    ring
  have h2 : ∑ y ∈ G, (if y = s₀ then (Fintype.card F : ℂ) else 0)
      = (if s₀ ∈ G then (Fintype.card F : ℂ) else 0) := by
    rw [Finset.sum_ite_eq' G s₀ (fun _ => (Fintype.card F : ℂ))]
  have h3 : ∑ _y ∈ G, (1 : ℂ) = (G.card : ℂ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [h1, h2, h3]
  ring

/-! ### (4) The exact low moments of `W` (unconditional). -/

/-- `∑_s W(s) = 0`. -/
theorem sum_W (hχ : IsRealQuadChar χ) (G : Finset F) : ∑ s : F, Wsum χ G s = 0 := by
  unfold Wsum
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero (fun y _ => sum_chi_shift hχ y)

/-- `∑_s W(s)² = n·(q − n)` EXACTLY. -/
theorem sum_W_sq (hχ : IsRealQuadChar χ) (G : Finset F) :
    ∑ s : F, (Wsum χ G s) ^ 2 = (G.card : ℝ) * ((Fintype.card F : ℝ) - G.card) := by
  classical
  have hexp : ∀ s : F, (Wsum χ G s) ^ 2
      = ∑ y ∈ G, ∑ y' ∈ G, χ (s - y) * χ (s - y') := by
    intro s
    rw [Wsum, sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl (fun s _ => hexp s)]
  rw [Finset.sum_comm]
  have houter : ∀ y ∈ G, ∑ s : F, ∑ y' ∈ G, χ (s - y) * χ (s - y')
      = (Fintype.card F : ℝ) - G.card := by
    intro y hy
    rw [Finset.sum_comm]
    -- per y': the s-sum is (q−1) if y'=y, else −1
    have hval : ∀ y' ∈ G, (∑ s : F, χ (s - y) * χ (s - y'))
        = -1 + (if y' = y then (Fintype.card F : ℝ) else 0) := by
      intro y' _
      by_cases h : y' = y
      · subst h
        have hterm : ∀ s : F, χ (s - y') * χ (s - y')
            = 1 - (if s = y' then (1:ℝ) else 0) := by
          intro s
          by_cases hs : s = y'
          · subst hs; simp [hχ.map_zero]
          · have hsq := hχ.sq_eq_one (s - y') (sub_ne_zero.mpr hs)
            have : χ (s - y') * χ (s - y') = 1 := by nlinarith [hsq]
            simp [hs, this]
        rw [Finset.sum_congr rfl (fun s _ => hterm s), Finset.sum_sub_distrib]
        rw [Finset.sum_const, Finset.sum_ite_eq' Finset.univ y' (fun _ => (1:ℝ))]
        simp [Finset.card_univ]
        ring
      · rw [sum_chi_two_point hχ (fun hc => h hc.symm)]
        simp [h]
    rw [Finset.sum_congr rfl hval, Finset.sum_add_distrib]
    rw [Finset.sum_const, Finset.sum_ite_eq' G y (fun _ => (Fintype.card F : ℝ))]
    simp [hy]
    ring
  rw [Finset.sum_congr rfl houter, Finset.sum_const, nsmul_eq_mul]


/-! ### (5) The named classical Weil input (Weil 1948; literature, not in Mathlib). -/

/-- **Named input (quartic Weil over pair-products)**: for two distinct-entry pairs that do not
match as unordered pairs, the quartic shifted character sum has square-root cancellation
(one-sided form; only the upper bound is consumed).  The share-one-value subcase is elementary
(`≤ 2`); the four-distinct case is Weil 1948.  Named-residual convention (cf. `TZPrimeSupply`). -/
def WeilQuarticPairs (χ : F → ℝ) : Prop :=
  ∀ p p' : F × F, p.1 ≠ p.2 → p'.1 ≠ p'.2 → p' ≠ p → p' ≠ Prod.swap p →
    ∑ s : F, χ (s - p.1) * χ (s - p.2) * (χ (s - p'.1) * χ (s - p'.2))
      ≤ 3 * Real.sqrt (Fintype.card F)

/-! ### (6) The off-diagonal kernel `R` and the moment bounds. -/

/-- The off-diagonal part of `W²`: `R(s) = ∑_{(y,y')∈G², y≠y'} χ(s−y)χ(s−y')`. -/
def Rker (χ : F → ℝ) (G : Finset F) (s : F) : ℝ :=
  ∑ p ∈ G ×ˢ G, (if p.1 = p.2 then 0 else χ (s - p.1) * χ (s - p.2))

/-- Pointwise: `|W(s)| ≤ n`. -/
theorem abs_Wsum_le (hχ : IsRealQuadChar χ) (G : Finset F) (s : F) :
    |Wsum χ G s| ≤ (G.card : ℝ) := by
  calc |Wsum χ G s| ≤ ∑ y ∈ G, |χ (s - y)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _y ∈ G, (1:ℝ) := Finset.sum_le_sum (fun y _ => hχ.abs_le_one (s - y))
    _ = (G.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Pointwise: `|R(s)| ≤ n²`. -/
theorem abs_Rker_le (hχ : IsRealQuadChar χ) (G : Finset F) (s : F) :
    |Rker χ G s| ≤ (G.card : ℝ) ^ 2 := by
  calc |Rker χ G s|
      ≤ ∑ p ∈ G ×ˢ G, |if p.1 = p.2 then 0 else χ (s - p.1) * χ (s - p.2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ G ×ˢ G, (1:ℝ) := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        split_ifs
        · norm_num
        · rw [abs_mul]
          calc |χ (s - p.1)| * |χ (s - p.2)| ≤ 1 * 1 :=
                mul_le_mul (hχ.abs_le_one _) (hχ.abs_le_one _) (abs_nonneg _) zero_le_one
            _ = 1 := mul_one 1
    _ = (G.card : ℝ) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_product]
        push_cast; ring

/-- **The diagonal split**: `W(s)² = (n − 1_G(s)) + R(s)`. -/
theorem Wsum_sq_eq (hχ : IsRealQuadChar χ) (G : Finset F) (s : F) :
    (Wsum χ G s) ^ 2
      = ((G.card : ℝ) - (if s ∈ G then 1 else 0)) + Rker χ G s := by
  classical
  have hexp : (Wsum χ G s) ^ 2 = ∑ p ∈ G ×ˢ G, χ (s - p.1) * χ (s - p.2) := by
    rw [Wsum, sq, Finset.sum_mul_sum, Finset.sum_product]
  have hsplit : ∀ p ∈ G ×ˢ G, χ (s - p.1) * χ (s - p.2)
      = (if p.1 = p.2 then χ (s - p.1) ^ 2 else 0)
        + (if p.1 = p.2 then 0 else χ (s - p.1) * χ (s - p.2)) := by
    intro p _
    split_ifs with h
    · rw [h]; ring
    · ring
  rw [hexp, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  unfold Rker
  congr 1
  -- diagonal: ∑_{p∈G×G, p1=p2} χ(s−p1)² = ∑_{y∈G} χ(s−y)² = n − 1_G(s)
  have hdiag : ∑ p ∈ G ×ˢ G, (if p.1 = p.2 then χ (s - p.1) ^ 2 else 0)
      = ∑ y ∈ G, χ (s - y) ^ 2 := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [Finset.sum_ite_eq G y (fun _ => χ (s - y) ^ 2), if_pos hy]
  rw [hdiag]
  have hval : ∀ y ∈ G, χ (s - y) ^ 2 = 1 - (if s = y then (1:ℝ) else 0) := by
    intro y _
    by_cases hs : s = y
    · subst hs; simp [hχ.map_zero]
    · rw [hχ.sq_eq_one (s - y) (sub_ne_zero.mpr hs)]
      simp [hs]
  rw [Finset.sum_congr rfl hval, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    mul_one, Finset.sum_ite_eq G s (fun _ => (1:ℝ))]

/-- `∑_s R(s) ≤ 0` (each off-diagonal pair contributes exactly `−1`). -/
theorem sum_Rker_nonpos (hχ : IsRealQuadChar χ) (G : Finset F) :
    ∑ s : F, Rker χ G s ≤ 0 := by
  classical
  unfold Rker
  rw [Finset.sum_comm]
  refine Finset.sum_nonpos (fun p _ => ?_)
  by_cases h : p.1 = p.2
  · simp [h]
  · have := sum_chi_two_point hχ h
    calc ∑ s : F, (if p.1 = p.2 then (0:ℝ) else χ (s - p.1) * χ (s - p.2))
        = ∑ s : F, χ (s - p.1) * χ (s - p.2) := by
          exact Finset.sum_congr rfl (fun s _ => by simp [h])
      _ = -1 := this
      _ ≤ 0 := by norm_num

/-- **The `R` second moment** from the quartic Weil input:
`∑_s R(s)² ≤ 2n²q + 3n⁴√q`. -/
theorem sum_Rker_sq_bound (hχ : IsRealQuadChar χ) (G : Finset F)
    (hweil : WeilQuarticPairs χ) :
    ∑ s : F, (Rker χ G s) ^ 2
      ≤ 2 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ)
        + 3 * (G.card : ℝ) ^ 4 * Real.sqrt (Fintype.card F) := by
  classical
  set n : ℝ := (G.card : ℝ)
  set q : ℝ := (Fintype.card F : ℝ)
  have hq0 : (0:ℝ) ≤ q := by positivity
  have hs0 : (0:ℝ) ≤ Real.sqrt q := Real.sqrt_nonneg q
  -- expand R² into the double pair sum and swap with s
  have hexp : ∑ s : F, (Rker χ G s) ^ 2
      = ∑ p ∈ G ×ˢ G, ∑ p' ∈ G ×ˢ G,
          ∑ s : F, (if p.1 = p.2 then 0 else χ (s - p.1) * χ (s - p.2))
            * (if p'.1 = p'.2 then 0 else χ (s - p'.1) * χ (s - p'.2)) := by
    have h1 : ∀ s : F, (Rker χ G s) ^ 2
        = ∑ p ∈ G ×ˢ G, ∑ p' ∈ G ×ˢ G,
            (if p.1 = p.2 then 0 else χ (s - p.1) * χ (s - p.2))
              * (if p'.1 = p'.2 then 0 else χ (s - p'.1) * χ (s - p'.2)) := by
      intro s
      rw [Rker, sq, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl (fun s _ => h1 s), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_comm]
  rw [hexp]
  -- pointwise: each (p,p') term is ≤ (if p'=p ∨ p'=swap p then q else 0) + 3√q
  have hpt : ∀ p ∈ G ×ˢ G, ∀ p' ∈ G ×ˢ G,
      (∑ s : F, (if p.1 = p.2 then 0 else χ (s - p.1) * χ (s - p.2))
        * (if p'.1 = p'.2 then 0 else χ (s - p'.1) * χ (s - p'.2)))
      ≤ ((if p' = p then (1:ℝ) else 0) + (if p' = Prod.swap p then (1:ℝ) else 0)) * q
        + 3 * Real.sqrt q := by
    intro p _ p' _
    by_cases hp : p.1 = p.2
    · -- degenerate row: all terms 0
      have : ∀ s : F, (if p.1 = p.2 then (0:ℝ) else χ (s - p.1) * χ (s - p.2))
          * (if p'.1 = p'.2 then 0 else χ (s - p'.1) * χ (s - p'.2)) = 0 := by
        intro s; simp [hp]
      rw [Finset.sum_congr rfl (fun s _ => this s), Finset.sum_const, smul_zero]
      positivity
    by_cases hp' : p'.1 = p'.2
    · have : ∀ s : F, (if p.1 = p.2 then (0:ℝ) else χ (s - p.1) * χ (s - p.2))
          * (if p'.1 = p'.2 then 0 else χ (s - p'.1) * χ (s - p'.2)) = 0 := by
        intro s; simp [hp']
      rw [Finset.sum_congr rfl (fun s _ => this s), Finset.sum_const, smul_zero]
      positivity
    -- both pairs distinct-entry: drop the ifs
    have hplain : (∑ s : F, (if p.1 = p.2 then (0:ℝ) else χ (s - p.1) * χ (s - p.2))
        * (if p'.1 = p'.2 then 0 else χ (s - p'.1) * χ (s - p'.2)))
        = ∑ s : F, χ (s - p.1) * χ (s - p.2) * (χ (s - p'.1) * χ (s - p'.2)) := by
      exact Finset.sum_congr rfl (fun s _ => by simp [hp, hp'])
    rw [hplain]
    by_cases hmatch : p' = p ∨ p' = Prod.swap p
    · -- matching pair: the product is a square, each term ≤ 1, total ≤ q
      have hterm : ∀ s : F, χ (s - p.1) * χ (s - p.2) * (χ (s - p'.1) * χ (s - p'.2)) ≤ 1 := by
        intro s
        have habs : |χ (s - p.1) * χ (s - p.2) * (χ (s - p'.1) * χ (s - p'.2))| ≤ 1 := by
          rw [abs_mul, abs_mul, abs_mul]
          have a1 := hχ.abs_le_one (s - p.1)
          have a2 := hχ.abs_le_one (s - p.2)
          have a3 := hχ.abs_le_one (s - p'.1)
          have a4 := hχ.abs_le_one (s - p'.2)
          have h12 : |χ (s - p.1)| * |χ (s - p.2)| ≤ 1 := by
            calc |χ (s - p.1)| * |χ (s - p.2)| ≤ 1 * 1 :=
                  mul_le_mul a1 a2 (abs_nonneg _) zero_le_one
              _ = 1 := mul_one 1
          have h34 : |χ (s - p'.1)| * |χ (s - p'.2)| ≤ 1 := by
            calc |χ (s - p'.1)| * |χ (s - p'.2)| ≤ 1 * 1 :=
                  mul_le_mul a3 a4 (abs_nonneg _) zero_le_one
              _ = 1 := mul_one 1
          calc |χ (s - p.1)| * |χ (s - p.2)| * (|χ (s - p'.1)| * |χ (s - p'.2)|)
              ≤ 1 * 1 := mul_le_mul h12 h34 (by positivity) zero_le_one
            _ = 1 := mul_one 1
        exact le_trans (le_abs_self _) habs
      have hsum : (∑ s : F, χ (s - p.1) * χ (s - p.2) * (χ (s - p'.1) * χ (s - p'.2))) ≤ q := by
        calc (∑ s : F, χ (s - p.1) * χ (s - p.2) * (χ (s - p'.1) * χ (s - p'.2)))
            ≤ ∑ _s : F, (1:ℝ) := Finset.sum_le_sum (fun s _ => hterm s)
          _ = q := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
      rcases hmatch with h | h
      · rw [if_pos h]
        have : ((1:ℝ) + (if p' = Prod.swap p then (1:ℝ) else 0)) * q + 3 * Real.sqrt q ≥ q := by
          have hnn : (0:ℝ) ≤ (if p' = Prod.swap p then (1:ℝ) else 0) := by positivity
          nlinarith [hs0, hq0]
        linarith
      · rw [if_pos h]
        have : ((if p' = p then (1:ℝ) else 0) + 1) * q + 3 * Real.sqrt q ≥ q := by
          have hnn : (0:ℝ) ≤ (if p' = p then (1:ℝ) else 0) := by positivity
          nlinarith [hs0, hq0]
        linarith
    · -- non-matching: the Weil input
      push_neg at hmatch
      have h := hweil p p' hp hp' hmatch.1 hmatch.2
      have h1 : (if p' = p then (1:ℝ) else 0) = 0 := if_neg hmatch.1
      have h2 : (if p' = Prod.swap p then (1:ℝ) else 0) = 0 := if_neg hmatch.2
      rw [h1, h2]
      simpa using h
  -- sum the pointwise bound and count
  have htotal : (∑ p ∈ G ×ˢ G, ∑ p' ∈ G ×ˢ G,
      ∑ s : F, (if p.1 = p.2 then 0 else χ (s - p.1) * χ (s - p.2))
        * (if p'.1 = p'.2 then 0 else χ (s - p'.1) * χ (s - p'.2)))
      ≤ ∑ p ∈ G ×ˢ G, ∑ p' ∈ G ×ˢ G,
          (((if p' = p then (1:ℝ) else 0) + (if p' = Prod.swap p then (1:ℝ) else 0)) * q
            + 3 * Real.sqrt q) :=
    Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun p' hp' => hpt p hp p' hp'))
  refine le_trans htotal ?_
  -- count: ∑_p [∑_{p'} (1_{p'=p} + 1_{p'=swap p})·q + 3√q·n²] ≤ 2n²q + 3n⁴√q
  have hinner : ∀ p ∈ G ×ˢ G, ∑ p' ∈ G ×ˢ G,
      (((if p' = p then (1:ℝ) else 0) + (if p' = Prod.swap p then (1:ℝ) else 0)) * q
        + 3 * Real.sqrt q)
      ≤ 2 * q + (n^2) * (3 * Real.sqrt q) := by
    intro p _
    rw [Finset.sum_add_distrib]
    have hc1 : ∑ p' ∈ G ×ˢ G,
        ((if p' = p then (1:ℝ) else 0) + (if p' = Prod.swap p then (1:ℝ) else 0)) * q
        ≤ 2 * q := by
      rw [Finset.sum_congr rfl (fun p' _ => add_mul (if p' = p then (1:ℝ) else 0)
        (if p' = Prod.swap p then (1:ℝ) else 0) q), Finset.sum_add_distrib]
      have e1 : ∑ p' ∈ G ×ˢ G, (if p' = p then (1:ℝ) else 0) * q ≤ q := by
        have hptw : ∀ p' ∈ G ×ˢ G, (if p' = p then (1:ℝ) else 0) * q
            = (if p' = p then q else 0) := by
          intro p' _; split_ifs <;> ring
        rw [Finset.sum_congr rfl hptw, Finset.sum_ite_eq' (G ×ˢ G) p (fun _ => q)]
        split_ifs <;> first | linarith | positivity
      have e2 : ∑ p' ∈ G ×ˢ G, (if p' = Prod.swap p then (1:ℝ) else 0) * q ≤ q := by
        have hptw : ∀ p' ∈ G ×ˢ G, (if p' = Prod.swap p then (1:ℝ) else 0) * q
            = (if p' = Prod.swap p then q else 0) := by
          intro p' _; split_ifs <;> ring
        rw [Finset.sum_congr rfl hptw, Finset.sum_ite_eq' (G ×ˢ G) (Prod.swap p) (fun _ => q)]
        split_ifs <;> first | linarith | positivity
      linarith
    have hc2 : ∑ _p' ∈ G ×ˢ G, (3 * Real.sqrt q) = (n^2) * (3 * Real.sqrt q) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_product]
      push_cast [n]
      ring
    rw [hc2]
    linarith [hc1]
  calc (∑ p ∈ G ×ˢ G, ∑ p' ∈ G ×ˢ G,
      (((if p' = p then (1:ℝ) else 0) + (if p' = Prod.swap p then (1:ℝ) else 0)) * q
        + 3 * Real.sqrt q))
      ≤ ∑ _p ∈ G ×ˢ G, (2 * q + (n^2) * (3 * Real.sqrt q)) :=
        Finset.sum_le_sum hinner
    _ = (n^2) * (2 * q + (n^2) * (3 * Real.sqrt q)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_product]
        push_cast [n]
        ring
    _ = 2 * n ^ 2 * q + 3 * n ^ 4 * Real.sqrt q := by ring

/-- **The fourth moment**: `∑_s W⁴ ≤ 3n²q + 2n³ + 3n⁴√q` (quartic Weil input only). -/
theorem sum_W_pow_four_bound (hχ : IsRealQuadChar χ) (G : Finset F)
    (hweil : WeilQuarticPairs χ) :
    ∑ s : F, (Wsum χ G s) ^ 4
      ≤ 3 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) + 2 * (G.card : ℝ) ^ 3
        + 3 * (G.card : ℝ) ^ 4 * Real.sqrt (Fintype.card F) := by
  classical
  set n : ℝ := (G.card : ℝ)
  set q : ℝ := (Fintype.card F : ℝ)
  have hW4 : ∀ s : F, (Wsum χ G s) ^ 4
      = ((n - (if s ∈ G then 1 else 0)) + Rker χ G s) ^ 2 := by
    intro s
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, Wsum_sq_eq hχ G s]
  rw [Finset.sum_congr rfl (fun s _ => hW4 s)]
  have hexp : ∀ s : F, ((n - (if s ∈ G then 1 else 0)) + Rker χ G s) ^ 2
      = (n - (if s ∈ G then 1 else 0)) ^ 2
        + 2 * (n - (if s ∈ G then 1 else 0)) * Rker χ G s + (Rker χ G s) ^ 2 := by
    intro s; ring
  rw [Finset.sum_congr rfl (fun s _ => hexp s), Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hA : ∑ s : F, (n - (if s ∈ G then 1 else 0)) ^ 2 ≤ n ^ 2 * q := by
    have hpt : ∀ s : F, (n - (if s ∈ G then 1 else 0)) ^ 2 ≤ n ^ 2 := by
      intro s
      have hn0 : (0:ℝ) ≤ n := by positivity
      split_ifs with h
      · have hn1 : (1:ℝ) ≤ n := by
          have h1 : 1 ≤ G.card := Finset.card_pos.mpr ⟨s, h⟩
          have h2 : (1:ℝ) ≤ (G.card : ℝ) := by exact_mod_cast h1
          simpa [n] using h2
        nlinarith
      · nlinarith
    calc ∑ s : F, (n - (if s ∈ G then 1 else 0)) ^ 2 ≤ ∑ _s : F, n ^ 2 :=
          Finset.sum_le_sum (fun s _ => hpt s)
      _ = n ^ 2 * q := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]; ring
  have hB : ∑ s : F, 2 * (n - (if s ∈ G then 1 else 0)) * Rker χ G s ≤ 2 * n ^ 3 := by
    -- split: 2n·∑R − 2·∑_{s∈G} R ≤ 0 + 2n·n²
    have hsplit : ∀ s : F, 2 * (n - (if s ∈ G then 1 else 0)) * Rker χ G s
        = 2 * n * Rker χ G s - 2 * (if s ∈ G then Rker χ G s else 0) := by
      intro s; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun s _ => hsplit s), Finset.sum_sub_distrib]
    have h1 : ∑ s : F, 2 * n * Rker χ G s ≤ 0 := by
      rw [← Finset.mul_sum]
      have := sum_Rker_nonpos hχ G
      have hn0 : (0:ℝ) ≤ 2 * n := by positivity
      exact mul_nonpos_of_nonneg_of_nonpos hn0 this
    have h2 : -(∑ s : F, 2 * (if s ∈ G then Rker χ G s else 0)) ≤ 2 * n ^ 3 := by
      have habs : |∑ s : F, 2 * (if s ∈ G then Rker χ G s else 0)| ≤ 2 * n ^ 3 := by
        calc |∑ s : F, 2 * (if s ∈ G then Rker χ G s else 0)|
            ≤ ∑ s : F, |2 * (if s ∈ G then Rker χ G s else 0)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ s : F, 2 * (if s ∈ G then n ^ 2 else 0) := by
              refine Finset.sum_le_sum (fun s _ => ?_)
              rw [abs_mul]
              have : |if s ∈ G then Rker χ G s else 0| ≤ (if s ∈ G then n ^ 2 else 0) := by
                split_ifs
                · exact abs_Rker_le hχ G s
                · simp
              calc |(2:ℝ)| * |if s ∈ G then Rker χ G s else 0|
                  ≤ |(2:ℝ)| * (if s ∈ G then n ^ 2 else 0) :=
                    mul_le_mul_of_nonneg_left this (abs_nonneg 2)
                _ = 2 * (if s ∈ G then n ^ 2 else 0) := by norm_num
          _ = 2 * n ^ 3 := by
              rw [← Finset.mul_sum]
              have : ∑ s : F, (if s ∈ G then n ^ 2 else 0) = n * n ^ 2 := by
                rw [Finset.sum_ite_mem Finset.univ G (fun _ => n ^ 2)]
                rw [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
                try ring
              calc 2 * ∑ s : F, (if s ∈ G then n ^ 2 else 0)
                  = 2 * (n * n ^ 2) := by rw [this]
                _ = 2 * n ^ 3 := by ring
      linarith [neg_abs_le (∑ s : F, 2 * (if s ∈ G then Rker χ G s else 0)), habs]
    linarith
  have hC := sum_Rker_sq_bound hχ G hweil
  -- combine
  have := add_le_add (add_le_add hA hB) hC
  calc (∑ s : F, (n - (if s ∈ G then 1 else 0)) ^ 2)
        + (∑ s : F, 2 * (n - (if s ∈ G then 1 else 0)) * Rker χ G s)
        + ∑ s : F, (Rker χ G s) ^ 2
      ≤ n ^ 2 * q + 2 * n ^ 3 + (2 * n ^ 2 * q + 3 * n ^ 4 * Real.sqrt q) := this
    _ = 3 * n ^ 2 * q + 2 * n ^ 3 + 3 * n ^ 4 * Real.sqrt q := by ring

/-- **The third moment via Cauchy–Schwarz** (no cubic Weil input needed):
`|∑_s W³| ≤ n² + √(nq·(2n²q + 3n⁴√q))`. -/
theorem sum_W_cubed_bound (hχ : IsRealQuadChar χ) (G : Finset F)
    (hweil : WeilQuarticPairs χ) :
    |∑ s : F, (Wsum χ G s) ^ 3|
      ≤ (G.card : ℝ) ^ 2
        + Real.sqrt ((G.card : ℝ) * (Fintype.card F : ℝ)
            * (2 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ)
              + 3 * (G.card : ℝ) ^ 4 * Real.sqrt (Fintype.card F))) := by
  classical
  set n : ℝ := (G.card : ℝ)
  set q : ℝ := (Fintype.card F : ℝ)
  -- W³ = W·(n − 1_G) + W·R
  have hsplit : ∀ s : F, (Wsum χ G s) ^ 3
      = Wsum χ G s * (n - (if s ∈ G then 1 else 0)) + Wsum χ G s * Rker χ G s := by
    intro s
    have := Wsum_sq_eq hχ G s
    calc (Wsum χ G s) ^ 3 = Wsum χ G s * (Wsum χ G s) ^ 2 := by ring
      _ = Wsum χ G s * ((n - (if s ∈ G then 1 else 0)) + Rker χ G s) := by rw [this]
      _ = _ := by ring
  rw [Finset.sum_congr rfl (fun s _ => hsplit s), Finset.sum_add_distrib]
  have hT1 : |∑ s : F, Wsum χ G s * (n - (if s ∈ G then 1 else 0))| ≤ n ^ 2 := by
    -- = n·∑W − ∑_{s∈G} W = −∑_{s∈G} W, and |∑_{s∈G} W| ≤ n·n
    have hpt : ∀ s : F, Wsum χ G s * (n - (if s ∈ G then 1 else 0))
        = n * Wsum χ G s - (if s ∈ G then Wsum χ G s else 0) := by
      intro s; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun s _ => hpt s), Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, sum_W hχ G, mul_zero]
    rw [zero_sub, abs_neg]
    calc |∑ s : F, (if s ∈ G then Wsum χ G s else 0)|
        ≤ ∑ s : F, |if s ∈ G then Wsum χ G s else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s : F, (if s ∈ G then n else 0) := by
          refine Finset.sum_le_sum (fun s _ => ?_)
          split_ifs
          · exact abs_Wsum_le hχ G s
          · simp
      _ = n ^ 2 := by
          rw [Finset.sum_ite_mem Finset.univ G (fun _ => n)]
          rw [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
          ring
  have hT2 : |∑ s : F, Wsum χ G s * Rker χ G s|
      ≤ Real.sqrt (n * q * (2 * n ^ 2 * q + 3 * n ^ 4 * Real.sqrt q)) := by
    -- Cauchy–Schwarz + the two moment bounds
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun s => Wsum χ G s)
      (fun s => Rker χ G s)
    have hW2 : ∑ s : F, (Wsum χ G s) ^ 2 ≤ n * q := by
      rw [sum_W_sq hχ G]
      have hn0 : (0:ℝ) ≤ n := by positivity
      nlinarith [hn0, Finset.card_le_univ G, (by exact_mod_cast Finset.card_le_univ G :
        (G.card : ℝ) ≤ (Fintype.card F : ℝ))]
    have hR2 := sum_Rker_sq_bound hχ G hweil
    have hrhs_nn : (0:ℝ) ≤ n * q * (2 * n ^ 2 * q + 3 * n ^ 4 * Real.sqrt q) := by positivity
    have hsq : (∑ s : F, Wsum χ G s * Rker χ G s) ^ 2
        ≤ n * q * (2 * n ^ 2 * q + 3 * n ^ 4 * Real.sqrt q) := by
      have hprod : (∑ s : F, (Wsum χ G s) ^ 2) * (∑ s : F, (Rker χ G s) ^ 2)
          ≤ (n * q) * (2 * n ^ 2 * q + 3 * n ^ 4 * Real.sqrt q) := by
        have h1 : (0:ℝ) ≤ ∑ s : F, (Rker χ G s) ^ 2 := by positivity
        have h2 : (0:ℝ) ≤ n * q := by positivity
        exact mul_le_mul hW2 hR2 h1 h2
      calc (∑ s : F, Wsum χ G s * Rker χ G s) ^ 2
          ≤ (∑ s : F, (Wsum χ G s) ^ 2) * (∑ s : F, (Rker χ G s) ^ 2) := hcs
        _ ≤ _ := hprod
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  calc |(∑ s : F, Wsum χ G s * (n - (if s ∈ G then 1 else 0)))
        + ∑ s : F, Wsum χ G s * Rker χ G s|
      ≤ |∑ s : F, Wsum χ G s * (n - (if s ∈ G then 1 else 0))|
        + |∑ s : F, Wsum χ G s * Rker χ G s| := abs_add_le _ _
    _ ≤ n ^ 2 + Real.sqrt (n * q * (2 * n ^ 2 * q + 3 * n ^ 4 * Real.sqrt q)) :=
        add_le_add hT1 hT2

/-! ### (7) The QR spectral weight: exact value of the plain part, `√q·n²` bound on the twist. -/

/-- `η_0 = |G|`. -/
theorem eta_zero (ψ : AddChar F ℂ) (G : Finset F) : eta ψ G 0 = (G.card : ℂ) := by
  unfold eta
  rw [Finset.sum_congr rfl (fun y _ => by rw [zero_mul, AddChar.map_zero_eq_one])]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The χ-twisted spectral weight collapses through the Gauss sum:
`∑_b χ(b)·‖η_b‖² = g · ∑_{y,y'} χ(y−y')` (as a complex identity). -/
theorem twisted_weight_eq (hχ : IsRealQuadChar χ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) :
    ∑ b : F, ((χ b : ℝ) : ℂ) * (((‖eta ψ G b‖ ^ 2 : ℝ)) : ℂ)
      = gSum χ ψ * ∑ y ∈ G, ∑ y' ∈ G, ((χ (y - y') : ℝ) : ℂ) := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconjψ : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  have hnormsq : ∀ b : F, (((‖eta ψ G b‖ ^ 2 : ℝ)) : ℂ)
      = ∑ y ∈ G, ∑ y' ∈ G, ψ (b * (y - y')) := by
    intro b
    have h1 : (((‖eta ψ G b‖ ^ 2 : ℝ)) : ℂ) = eta ψ G b * (starRingEnd ℂ) (eta ψ G b) := by
      rw [RCLike.mul_conj]; norm_cast
    rw [h1]
    have hconjeta : (starRingEnd ℂ) (eta ψ G b) = ∑ y' ∈ G, ψ (-(b * y')) := by
      rw [eta, map_sum]; exact Finset.sum_congr rfl (fun y' _ => hconjψ (b * y'))
    rw [hconjeta, eta, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun y' _ => ?_))
    rw [← AddChar.map_add_eq_mul]
    congr 1; ring
  calc ∑ b : F, ((χ b : ℝ) : ℂ) * (((‖eta ψ G b‖ ^ 2 : ℝ)) : ℂ)
      = ∑ b : F, ∑ y ∈ G, ∑ y' ∈ G, ((χ b : ℝ) : ℂ) * ψ (b * (y - y')) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [hnormsq b, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun y _ => by rw [Finset.mul_sum])
    _ = ∑ y ∈ G, ∑ y' ∈ G, ∑ b : F, ((χ b : ℝ) : ℂ) * ψ (b * (y - y')) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun y _ => Finset.sum_comm)
    _ = ∑ y ∈ G, ∑ y' ∈ G, ((χ (y - y') : ℝ) : ℂ) * gSum χ ψ := by
        exact Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun y' _ =>
          sum_chi_psi_mul hχ ψ (y - y')))
    _ = gSum χ ψ * ∑ y ∈ G, ∑ y' ∈ G, ((χ (y - y') : ℝ) : ℂ) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun y' _ =>
          mul_comm _ _))

set_option maxHeartbeats 800000 in
/-- **The QR spectral-weight lower bound**:
`Σ_QR := ∑_{b∈QR} ‖η_b‖² ≥ (q·n − n² − n²·√q)/2`. -/
theorem qr_weight_lower (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2
        - (G.card : ℝ) ^ 2 * Real.sqrt (Fintype.card F)) / 2
      ≤ ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2 := by
  classical
  set n : ℝ := (G.card : ℝ)
  set q : ℝ := (Fintype.card F : ℝ)
  -- indicator split: ∑_QR f = (T + P)/2 with T the χ-twist and P the punctured plain sum
  have hsplitsum : ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2
      = ∑ b : F, ((χ b + χ b ^ 2) / 2) * ‖eta ψ G b‖ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b => χ b = 1)
      (fun b => ((χ b + χ b ^ 2) / 2) * ‖eta ψ G b‖ ^ 2)]
    have hL : ∑ b ∈ Finset.univ.filter (fun b => χ b = 1),
        ((χ b + χ b ^ 2) / 2) * ‖eta ψ G b‖ ^ 2 = ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2 := by
      refine Finset.sum_congr rfl (fun b hb => ?_)
      have h1 : χ b = 1 := (Finset.mem_filter.mp hb).2
      rw [h1]; norm_num
    have hR : ∑ b ∈ Finset.univ.filter (fun b => ¬ χ b = 1),
        ((χ b + χ b ^ 2) / 2) * ‖eta ψ G b‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero (fun b hb => ?_)
      have h1 : χ b ≠ 1 := (Finset.mem_filter.mp hb).2
      by_cases hb0 : b = 0
      · subst hb0; simp [hχ.map_zero]
      · have hsq := hχ.sq_eq_one b hb0
        have : χ b = -1 := by
          rcases mul_self_eq_one_iff.mp (by nlinarith [hsq] : χ b * χ b = 1) with h | h
          · exact absurd h h1
          · exact h
        rw [this]; norm_num
    rw [hL, hR, add_zero]
  rw [hsplitsum]
  have hexpand : ∑ b : F, ((χ b + χ b ^ 2) / 2) * ‖eta ψ G b‖ ^ 2
      = ((∑ b : F, χ b * ‖eta ψ G b‖ ^ 2) + ∑ b : F, χ b ^ 2 * ‖eta ψ G b‖ ^ 2) / 2 := by
    have hpt : ∀ b : F, ((χ b + χ b ^ 2) / 2) * ‖eta ψ G b‖ ^ 2
        = (χ b * ‖eta ψ G b‖ ^ 2 + χ b ^ 2 * ‖eta ψ G b‖ ^ 2) / 2 := fun b => by ring
    rw [Finset.sum_congr rfl (fun b _ => hpt b), ← Finset.sum_div, Finset.sum_add_distrib]
  rw [hexpand]
  -- the plain (punctured) part: ∑ χ²‖η‖² = qn − n²
  have hplain : ∑ b : F, χ b ^ 2 * ‖eta ψ G b‖ ^ 2 = q * n - n ^ 2 := by
    have hpt : ∀ b : F, χ b ^ 2 * ‖eta ψ G b‖ ^ 2
        = ‖eta ψ G b‖ ^ 2 - (if b = 0 then ‖eta ψ G b‖ ^ 2 else 0) := by
      intro b
      by_cases hb : b = 0
      · subst hb; simp [hχ.map_zero]
      · rw [hχ.sq_eq_one b hb]; simp [hb]
    rw [Finset.sum_congr rfl (fun b _ => hpt b), Finset.sum_sub_distrib]
    rw [subgroup_gaussSum_secondMoment hψ G]
    rw [Finset.sum_ite_eq' Finset.univ (0:F) (fun b => ‖eta ψ G b‖ ^ 2)]
    simp only [Finset.mem_univ, if_true]
    rw [eta_zero ψ G, Complex.norm_natCast]
    try push_cast
    try ring
  -- the twisted part: |T| ≤ n²√q
  have htwist : |∑ b : F, χ b * ‖eta ψ G b‖ ^ 2| ≤ n ^ 2 * Real.sqrt q := by
    have hcx : ((∑ b : F, χ b * ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ)
        = gSum χ ψ * ∑ y ∈ G, ∑ y' ∈ G, ((χ (y - y') : ℝ) : ℂ) := by
      rw [← twisted_weight_eq hχ hψ G]
      push_cast
      rfl
    have hnorm : |∑ b : F, χ b * ‖eta ψ G b‖ ^ 2|
        = ‖((∑ b : F, χ b * ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real]
      rfl
    rw [hnorm, hcx, norm_mul]
    have hg : ‖gSum χ ψ‖ = Real.sqrt q := by
      have h2 := norm_gSum_sq hχ hψ
      have : ‖gSum χ ψ‖ = Real.sqrt (‖gSum χ ψ‖ ^ 2) := by
        rw [Real.sqrt_sq (norm_nonneg _)]
      rw [this, h2]
    rw [hg]
    have hinner : ‖∑ y ∈ G, ∑ y' ∈ G, ((χ (y - y') : ℝ) : ℂ)‖ ≤ n ^ 2 := by
      calc ‖∑ y ∈ G, ∑ y' ∈ G, ((χ (y - y') : ℝ) : ℂ)‖
          ≤ ∑ y ∈ G, ‖∑ y' ∈ G, ((χ (y - y') : ℝ) : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ y ∈ G, ∑ y' ∈ G, ‖((χ (y - y') : ℝ) : ℂ)‖ :=
            Finset.sum_le_sum (fun y _ => norm_sum_le _ _)
        _ ≤ ∑ _y ∈ G, ∑ _y' ∈ G, (1:ℝ) := by
            refine Finset.sum_le_sum (fun y _ => Finset.sum_le_sum (fun y' _ => ?_))
            rw [Complex.norm_real]
            exact hχ.abs_le_one (y - y')
        _ = n ^ 2 := by
            rw [Finset.sum_congr rfl (fun y _ => Finset.sum_const (1:ℝ))]
            simp only [nsmul_eq_mul, mul_one, Finset.sum_const]
            push_cast [n]
            ring
    calc Real.sqrt q * ‖∑ y ∈ G, ∑ y' ∈ G, ((χ (y - y') : ℝ) : ℂ)‖
        ≤ Real.sqrt q * n ^ 2 := mul_le_mul_of_nonneg_left hinner (Real.sqrt_nonneg q)
      _ = n ^ 2 * Real.sqrt q := by ring
  -- combine
  have hT := neg_abs_le (∑ b : F, χ b * ‖eta ψ G b‖ ^ 2)
  have : -(n ^ 2 * Real.sqrt q) ≤ ∑ b : F, χ b * ‖eta ψ G b‖ ^ 2 := by
    linarith [htwist, hT]
  rw [hplain]
  linarith

/-! ### (8) THE ROUND-17 THEOREM: the r = 2 rung at deg 2 from the quartic Weil input. -/

set_option maxHeartbeats 3200000 in
/-- **The r = 2 diagonal-subtracted Wick rung at deg = 2, conditional ONLY on the classical
quartic Weil bound** (`WeilQuarticPairs`, Weil 1948).  Hypotheses: `χ` a real quadratic
character, `ψ` primitive, and the prize-window size condition `16·n² ≤ √q`.

This is the **first discharged nontrivial rung of the corrected (round-16) tower**: at the
prize scaling (`β ≈ 5.3 > 4`) the deg-2 instance of the diagonal-subtracted fourth-moment
bound is CLASSICAL, not open.  Probe `probe_r17_deg2_weil_rung.py`: measured `S₂'/Wick ≈
0.22–0.29` at 18 cells — the true constant is `≈ 1/4`, and this proof certifies `≤ 1`. -/
theorem wickAwayAt_two_of_weil (hχ : IsRealQuadChar χ)
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hweil : WeilQuarticPairs χ)
    (hbig : 16 * (G.card : ℝ) ^ 2 ≤ Real.sqrt (Fintype.card F))
    (hGne : G.Nonempty) :
    WickForIncidenceAwayAt ψ G (QRset χ) (insert (0:F) G) 2 := by
  classical
  set n : ℝ := (G.card : ℝ) with hn_def
  set q : ℝ := (Fintype.card F : ℝ) with hq_def
  set sq : ℝ := Real.sqrt q with hsq_def
  have hn1 : (1:ℝ) ≤ n := by
    have h1 : 1 ≤ G.card := Finset.card_pos.mpr hGne
    have h2 : (1:ℝ) ≤ (G.card : ℝ) := by exact_mod_cast h1
    simpa [hn_def] using h2
  have hq1 : (1:ℝ) ≤ q := by
    have h1 : 1 ≤ Fintype.card F := Fintype.card_pos
    have h2 : (1:ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast h1
    simpa [hq_def] using h2
  have hsq0 : (0:ℝ) ≤ sq := Real.sqrt_nonneg q
  have hsqq : sq ^ 2 = q := Real.sq_sqrt (by linarith)
  have hsq16 : 16 * n ^ 2 ≤ sq := hbig
  have hsq1 : (1:ℝ) ≤ sq := by nlinarith [hn1, hsq16]
  -- x := Re g, with x² ≤ q and |x| ≤ √q
  set x : ℝ := (gSum χ ψ).re with hx_def
  have hgnorm : ‖gSum χ ψ‖ ^ 2 = q := norm_gSum_sq hχ hψ
  have hx2 : x ^ 2 ≤ q := by
    have h1 : x ^ 2 ≤ ‖gSum χ ψ‖ ^ 2 := by
      have := Complex.abs_re_le_norm (gSum χ ψ)
      have hx0 : |x| ≤ ‖gSum χ ψ‖ := by simpa [hx_def] using this
      nlinarith [hx0, abs_nonneg x, sq_abs x]
    linarith [hgnorm ▸ h1]
  have hxabs : |x| ≤ sq := by
    have h1 : x ^ 2 ≤ sq ^ 2 := by rw [hsqq]; exact hx2
    nlinarith [sq_abs x, h1, abs_nonneg x, hsq0]
  -- STEP 1: pointwise identity off the diagonal: ‖I(s)‖² = q·W² − 2n·x·W + n²
  have hIsq : ∀ s : F, s ∉ (insert (0:F) G) →
      ‖incidenceSum ψ G (QRset χ) s‖ ^ 2
        = (q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) / 4 := by
    intro s hs
    have hsG : s ∉ G := fun h => hs (Finset.mem_insert_of_mem h)
    have hbr := bridge hχ hψ G s
    rw [if_neg hsG] at hbr
    -- I = (g·W − n)/2
    have hI : incidenceSum ψ G (QRset χ) s
        = (gSum χ ψ * ((Wsum χ G s : ℝ) : ℂ) - (G.card : ℂ)) / 2 := by
      rw [hbr]; ring
    rw [hI]
    have h2n : ‖(2:ℂ)‖ = 2 := by norm_num
    rw [norm_div, norm_sub_rev, div_pow, h2n]
    have hz : ‖(G.card : ℂ) - gSum χ ψ * ((Wsum χ G s : ℝ) : ℂ)‖ ^ 2
        = q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2 := by
      set W : ℝ := Wsum χ G s
      have hre : ((G.card : ℂ) - gSum χ ψ * ((W : ℝ) : ℂ)).re = n - x * W := by
        simp [Complex.sub_re, Complex.mul_re, hx_def, hn_def]
      have him : ((G.card : ℂ) - gSum χ ψ * ((W : ℝ) : ℂ)).im = -((gSum χ ψ).im * W) := by
        simp [Complex.sub_im, Complex.mul_im]
      rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
      have hxy : x ^ 2 + (gSum χ ψ).im ^ 2 = q := by
        have := Complex.sq_norm (gSum χ ψ)
        have h2 : Complex.normSq (gSum χ ψ) = q := by
          rw [← this, hgnorm]
        rw [Complex.normSq_apply] at h2
        nlinarith [h2]
      nlinarith [hxy]
    rw [hz]
    norm_num
  -- STEP 2: the away moment is bounded by the full sum of the quartic polynomial in W
  have hstep2 : incidenceMomentAway ψ G (QRset χ) (insert (0:F) G) 2
      ≤ (∑ s : F, (q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) ^ 2) / 16 := by
    unfold incidenceMomentAway
    have hpt : ∀ s ∈ Finset.univ \ (insert (0:F) G),
        ‖incidenceSum ψ G (QRset χ) s‖ ^ (2 * 2)
          = ((q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) / 4) ^ 2 := by
      intro s hs
      have hs' : s ∉ (insert (0:F) G) := (Finset.mem_sdiff.mp hs).2
      rw [pow_mul, hIsq s hs']
    rw [Finset.sum_congr rfl hpt]
    have hsub : ∑ s ∈ Finset.univ \ (insert (0:F) G),
        ((q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) / 4) ^ 2
        ≤ ∑ s : F, ((q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) / 4) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
        (fun s _ _ => by positivity)
    refine le_trans hsub (le_of_eq ?_)
    have hshape : ∀ s : F,
        ((q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) / 4) ^ 2
          = (q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) ^ 2 / 16 := by
      intro s; ring
    rw [Finset.sum_congr rfl (fun s _ => hshape s), ← Finset.sum_div]
  -- STEP 3: expand the square and apply the moment bounds
  have hW2 := sum_W_sq hχ G
  have hW1 := sum_W hχ G
  have hW4 := sum_W_pow_four_bound hχ G hweil
  have hW3 := sum_W_cubed_bound hχ G hweil
  have hexpand : ∑ s : F, (q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) ^ 2
      = q ^ 2 * (∑ s : F, (Wsum χ G s) ^ 4)
        + (4 * n ^ 2 * x ^ 2 + 2 * q * n ^ 2) * (∑ s : F, (Wsum χ G s) ^ 2)
        + q * n ^ 4
        - 4 * n * q * x * (∑ s : F, (Wsum χ G s) ^ 3)
        - 4 * n ^ 3 * x * (∑ s : F, Wsum χ G s) := by
    have hpt : ∀ s : F, (q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) ^ 2
        = q ^ 2 * (Wsum χ G s) ^ 4
          + (4 * n ^ 2 * x ^ 2 + 2 * q * n ^ 2) * (Wsum χ G s) ^ 2
          + n ^ 4
          - 4 * n * q * x * (Wsum χ G s) ^ 3
          - 4 * n ^ 3 * x * Wsum χ G s := by
      intro s; ring
    rw [Finset.sum_congr rfl (fun s _ => hpt s)]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  -- assemble all numeric bounds
  set SW4 : ℝ := ∑ s : F, (Wsum χ G s) ^ 4
  set SW3 : ℝ := ∑ s : F, (Wsum χ G s) ^ 3
  have hbound : ∑ s : F, (q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) ^ 2
      ≤ q ^ 2 * (3 * n ^ 2 * q + 2 * n ^ 3 + 3 * n ^ 4 * sq)
        + (4 * n ^ 2 * q + 2 * q * n ^ 2) * (n * q)
        + q * n ^ 4
        + 4 * n * q * sq * (n ^ 2 + Real.sqrt (n * q * (2 * n ^ 2 * q + 3 * n ^ 4 * sq))) := by
    rw [hexpand, hW1, hW2]
    have hSW4nn : (0:ℝ) ≤ q ^ 2 := by positivity
    have b1 : q ^ 2 * SW4 ≤ q ^ 2 * (3 * n ^ 2 * q + 2 * n ^ 3 + 3 * n ^ 4 * sq) :=
      mul_le_mul_of_nonneg_left hW4 hSW4nn
    have b2 : (4 * n ^ 2 * x ^ 2 + 2 * q * n ^ 2) * (n * (q - n))
        ≤ (4 * n ^ 2 * q + 2 * q * n ^ 2) * (n * q) := by
      have hc1 : 4 * n ^ 2 * x ^ 2 + 2 * q * n ^ 2 ≤ 4 * n ^ 2 * q + 2 * q * n ^ 2 := by
        nlinarith [hx2, hn1]
      have hc2 : n * (q - n) ≤ n * q := by nlinarith [hn1]
      have hc3 : (0:ℝ) ≤ n * (q - n) := by
        have hnq : n ≤ q := by
          have h1 : G.card ≤ Fintype.card F := Finset.card_le_univ G
          have h2 : (G.card : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast h1
          simpa [hn_def, hq_def] using h2
        nlinarith [hn1]
      have hc4 : (0:ℝ) ≤ 4 * n ^ 2 * x ^ 2 + 2 * q * n ^ 2 := by positivity
      calc (4 * n ^ 2 * x ^ 2 + 2 * q * n ^ 2) * (n * (q - n))
          ≤ (4 * n ^ 2 * q + 2 * q * n ^ 2) * (n * (q - n)) :=
            mul_le_mul_of_nonneg_right hc1 hc3
        _ ≤ (4 * n ^ 2 * q + 2 * q * n ^ 2) * (n * q) := by
            have : (0:ℝ) ≤ 4 * n ^ 2 * q + 2 * q * n ^ 2 := by positivity
            exact mul_le_mul_of_nonneg_left hc2 this
    have b3 : -(4 * n * q * x * SW3) ≤ 4 * n * q * sq
        * (n ^ 2 + Real.sqrt (n * q * (2 * n ^ 2 * q + 3 * n ^ 4 * sq))) := by
      have habs : |4 * n * q * x * SW3| ≤ 4 * n * q * sq
          * (n ^ 2 + Real.sqrt (n * q * (2 * n ^ 2 * q + 3 * n ^ 4 * sq))) := by
        rw [abs_mul]
        have h1 : |4 * n * q * x| ≤ 4 * n * q * sq := by
          rw [abs_mul]
          have : |(4 * n * q : ℝ)| = 4 * n * q := abs_of_nonneg (by positivity)
          rw [this]
          exact mul_le_mul_of_nonneg_left hxabs (by positivity)
        have h2 : |SW3| ≤ n ^ 2 + Real.sqrt (n * q * (2 * n ^ 2 * q + 3 * n ^ 4 * sq)) := hW3
        have h3 : (0:ℝ) ≤ |SW3| := abs_nonneg _
        calc |4 * n * q * x| * |SW3| ≤ (4 * n * q * sq) * |SW3| :=
              mul_le_mul_of_nonneg_right h1 h3
          _ ≤ (4 * n * q * sq)
              * (n ^ 2 + Real.sqrt (n * q * (2 * n ^ 2 * q + 3 * n ^ 4 * sq))) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
      linarith [neg_abs_le (4 * n * q * x * SW3), habs]
    have b4 : -(4 * n ^ 3 * x * 0) = 0 := by ring
    -- combine: LHS = q²SW4 + (…)·n(q−n) + qn⁴ − 4nqx·SW3 − 0
    nlinarith [b1, b2, b3]
  -- STEP 4: the final polynomial inequality
  have hqr := qr_weight_lower hχ (χ := χ) hψ G
  unfold WickForIncidenceAwayAt
  have hdf : (Nat.doubleFactorial (2 * 2 - 1) : ℝ) = 3 := by
    have h3 : Nat.doubleFactorial (2 * 2 - 1) = 3 := by decide
    rw [h3]; norm_num
  rw [hdf]
  -- lower bound on the Wick RHS via the QR weight
  have hnq : n ≤ q := by
    have h1 : G.card ≤ Fintype.card F := Finset.card_le_univ G
    have h2 : (G.card : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast h1
    simpa [hn_def, hq_def] using h2
  have hL : (0:ℝ) ≤ (q * n - n ^ 2 - n ^ 2 * sq) / 2 := by
    -- n²·sq ≤ (sq/16)·sq = q/16 and n² ≤ q/256 ≤ q; qn ≥ q
    have h1 : n ^ 2 * sq ≤ (sq / 16) * sq := by
      have : n ^ 2 ≤ sq / 16 := by linarith [hsq16]
      exact mul_le_mul_of_nonneg_right this hsq0
    have h2 : (sq / 16) * sq = q / 16 := by
      have : sq * sq = q := by nlinarith [hsqq]
      nlinarith [this]
    have h3 : n ^ 2 ≤ q / 16 := by
      have h4 : n ^ 2 ≤ sq / 16 := by linarith [hsq16]
      have h5 : sq ≤ q := by nlinarith [hsq1, hsqq]
      linarith
    have h6 : q * 1 ≤ q * n := mul_le_mul_of_nonneg_left hn1 (by linarith : (0:ℝ) ≤ q)
    nlinarith [hn1, hq1, h1, h2, h3, h6]
  have hwick_lower : q * 3 * ((q * n - n ^ 2 - n ^ 2 * sq) / 2) ^ 2
      ≤ q * 3 * (∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ 2 := by
    have h2 : (0:ℝ) ≤ ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2 := by positivity
    have h3 : ((q * n - n ^ 2 - n ^ 2 * sq) / 2) ^ 2
        ≤ (∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ 2 := by
      have hle : (q * n - n ^ 2 - n ^ 2 * sq) / 2 ≤ ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2 := hqr
      nlinarith [hL, hle, h2]
    have h4 : (0:ℝ) ≤ q * 3 := by positivity
    exact mul_le_mul_of_nonneg_left h3 h4
  -- CS-sqrt simplification: √(nq(2n²q + 3n⁴·sq)) ≤ 3n²q
  have hcs_bound : Real.sqrt (n * q * (2 * n ^ 2 * q + 3 * n ^ 4 * sq)) ≤ 3 * n ^ 2 * q := by
    have h1 : n ^ 2 ≤ sq / 16 := by linarith [hsq16]
    have h2 : n ^ 5 * sq ≤ n ^ 3 * q / 16 := by
      have h3 : n ^ 2 * sq ≤ (sq / 16) * sq := mul_le_mul_of_nonneg_right h1 hsq0
      have h4 : (sq / 16) * sq = q / 16 := by nlinarith [hsqq]
      have h5 : n ^ 5 * sq = n ^ 3 * (n ^ 2 * sq) := by ring
      have h6 : (0:ℝ) ≤ n ^ 3 := by positivity
      calc n ^ 5 * sq = n ^ 3 * (n ^ 2 * sq) := h5
        _ ≤ n ^ 3 * (q / 16) := mul_le_mul_of_nonneg_left (by linarith [h3, h4]) h6
        _ = n ^ 3 * q / 16 := by ring
    have harg : n * q * (2 * n ^ 2 * q + 3 * n ^ 4 * sq) ≤ (3 * n ^ 2 * q) ^ 2 := by
      have h7 : 3 * q * (n ^ 5 * sq) ≤ 3 * q * (n ^ 3 * q / 16) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have h8 : n ^ 3 * q ^ 2 ≤ n ^ 4 * q ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (by positivity : (0:ℝ) ≤ n ^ 3 * q ^ 2)]
      nlinarith [h7, h8, hn1, hq1]
    calc Real.sqrt (n * q * (2 * n ^ 2 * q + 3 * n ^ 4 * sq))
        ≤ Real.sqrt ((3 * n ^ 2 * q) ^ 2) := Real.sqrt_le_sqrt harg
      _ = 3 * n ^ 2 * q := Real.sqrt_sq (by positivity)
  -- monotone glue on the numeric bound
  have hbound2 : ∑ s : F, (q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) ^ 2
      ≤ q ^ 2 * (3 * n ^ 2 * q + 2 * n ^ 3 + 3 * n ^ 4 * sq)
        + (4 * n ^ 2 * q + 2 * q * n ^ 2) * (n * q)
        + q * n ^ 4
        + 4 * n * q * sq * (n ^ 2 + 3 * n ^ 2 * q) := by
    refine le_trans hbound ?_
    have h0 : (0:ℝ) ≤ 4 * n * q * sq := by positivity
    have := mul_le_mul_of_nonneg_left
      (by linarith [hcs_bound] :
        n ^ 2 + Real.sqrt (n * q * (2 * n ^ 2 * q + 3 * n ^ 4 * sq)) ≤ n ^ 2 + 3 * n ^ 2 * q)
      h0
    linarith [this]
  -- THE POLYNOMIAL INEQUALITY (in n, sq only; q = sq², sq ≥ 16n², n ≥ 1)
  have hpoly : q ^ 2 * (3 * n ^ 2 * q + 2 * n ^ 3 + 3 * n ^ 4 * sq)
        + (4 * n ^ 2 * q + 2 * q * n ^ 2) * (n * q)
        + q * n ^ 4
        + 4 * n * q * sq * (n ^ 2 + 3 * n ^ 2 * q)
      ≤ 16 * (q * 3 * ((q * n - n ^ 2 - n ^ 2 * sq) / 2) ^ 2) := by
    have e1 : q = sq ^ 2 := hsqq.symm
    rw [e1]
    -- monomial bridge lemmas from sq ≥ 16n², n ≥ 1, sq ≥ 1
    have k1 : 16 * n ^ 4 * sq ^ 5 ≤ n ^ 2 * sq ^ 6 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsq16) (by positivity : (0:ℝ) ≤ n ^ 2 * sq ^ 5)]
    have k2 : 16 * n ^ 3 * sq ^ 5 ≤ n * sq ^ 6 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsq16) (by positivity : (0:ℝ) ≤ n * sq ^ 5)]
    have k3 : 16 * n ^ 3 * sq ^ 4 ≤ n * sq ^ 5 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsq16) (by positivity : (0:ℝ) ≤ n * sq ^ 4)]
    have k4 : 16 * n ^ 3 * sq ^ 3 ≤ n * sq ^ 4 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsq16) (by positivity : (0:ℝ) ≤ n * sq ^ 3)]
    have k5 : n * sq ^ 6 ≤ n ^ 2 * sq ^ 6 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (by positivity : (0:ℝ) ≤ sq ^ 6)]
    have k6 : n * sq ^ 5 ≤ n ^ 2 * sq ^ 6 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsq1) (by positivity : (0:ℝ) ≤ n * sq ^ 5), k5,
        mul_nonneg (sub_nonneg.mpr hn1) (by positivity : (0:ℝ) ≤ sq ^ 5)]
    have k7 : n * sq ^ 4 ≤ n ^ 2 * sq ^ 6 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsq1) (by positivity : (0:ℝ) ≤ n * sq ^ 4), k6,
        mul_nonneg (sub_nonneg.mpr hsq1) (by positivity : (0:ℝ) ≤ n * sq ^ 5)]
    have k8 : (0:ℝ) ≤ n ^ 4 * sq ^ 4 := by positivity
    have k9 : (0:ℝ) ≤ n ^ 4 * sq ^ 3 := by positivity
    have k10 : (0:ℝ) ≤ n ^ 4 * sq ^ 2 := by positivity
    nlinarith [k1, k2, k3, k4, k5, k6, k7, k8, k9, k10]
  -- final chain
  calc incidenceMomentAway ψ G (QRset χ) (insert (0:F) G) 2
      ≤ (∑ s : F, (q * (Wsum χ G s) ^ 2 - 2 * n * x * Wsum χ G s + n ^ 2) ^ 2) / 16 := hstep2
    _ ≤ (q ^ 2 * (3 * n ^ 2 * q + 2 * n ^ 3 + 3 * n ^ 4 * sq)
          + (4 * n ^ 2 * q + 2 * q * n ^ 2) * (n * q)
          + q * n ^ 4
          + 4 * n * q * sq * (n ^ 2 + 3 * n ^ 2 * q)) / 16 := by
        gcongr
    _ ≤ q * 3 * ((q * n - n ^ 2 - n ^ 2 * sq) / 2) ^ 2 := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 16)]
        linarith [hpoly]
    _ ≤ q * 3 * (∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ 2 := hwick_lower
    _ = (Fintype.card F : ℝ) * 3 * (∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ 2 := by
        rw [hq_def]

end ArkLib.ProximityGap.Frontier.R17Deg2WeilRung

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R17Deg2WeilRung.sum_chi_two_point
#print axioms ArkLib.ProximityGap.Frontier.R17Deg2WeilRung.gSum_mul_conj
#print axioms ArkLib.ProximityGap.Frontier.R17Deg2WeilRung.bridge
#print axioms ArkLib.ProximityGap.Frontier.R17Deg2WeilRung.sum_W
#print axioms ArkLib.ProximityGap.Frontier.R17Deg2WeilRung.sum_W_sq
#print axioms ArkLib.ProximityGap.Frontier.R17Deg2WeilRung.sum_Rker_sq_bound
#print axioms ArkLib.ProximityGap.Frontier.R17Deg2WeilRung.sum_W_pow_four_bound
#print axioms ArkLib.ProximityGap.Frontier.R17Deg2WeilRung.sum_W_cubed_bound
#print axioms ArkLib.ProximityGap.Frontier.R17Deg2WeilRung.qr_weight_lower
#print axioms ArkLib.ProximityGap.Frontier.R17Deg2WeilRung.wickAwayAt_two_of_weil

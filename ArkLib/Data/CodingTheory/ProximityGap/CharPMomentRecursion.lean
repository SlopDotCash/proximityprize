/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import Mathlib.Data.Fin.Tuple.Finset

/-!
# The char-`p` additive-moment recursion `E_{r+1} = n·E_r + cross_r` (Issue #407, "T4")

The substrate `SubgroupGaussSumMoment.lean` proves the exact `2r`-th moment identity
`∑_b ‖η_b‖^{2r} = q · E_r(G)` (`subgroup_gaussSum_moment`), where `η_b = ∑_{y∈G} ψ(b·y)` is the
subgroup Gauss sum and `E_r(G) = rEnergy G r = #{(v,w) ∈ (Fin r → G)² : ∑v = ∑w}` is the
`r`-fold additive energy.

This file supplies the **exact one-step additive-moment recursion** for that `E_r` (the "T4"
identity of issue #407), built on the `r`-fold sum-frequency `f_r(d) := #{v ∈ (Fin r → G) : ∑v = d}`
(`freq`). Everything is exact, holds in `char`-`p` for **any** finite set `G` (no subgroup
hypothesis), and uses **no** Weil / sum-product / analytic input — pure counting and
character-orthogonality (the latter only via the cited substrate moment):

* `freq_succ`     : `f_{r+1}(d) = ∑_{s∈G} f_r(d − s)`              — the convolution atom (`sum_nbij'`).
* `rEnergy_eq_sum_freq_sq` : `E_r(G) = ∑_d f_r(d)²`                — the energy is the `ℓ²` of `f_r`.
                    Hence (via the substrate) `∑_b ‖η_b‖^{2r} = q·∑_d f_r(d)²`.
* `autocorr` / `autocorr_zero` : `C_r(δ) = ∑_e f_r(e)·f_r(e+δ)`,  `C_r(0) = E_r`.
* `autocorr_le_energy` : `C_r(δ) ≤ E_r`                            — the diagonal bound (AM–GM).
* `rEnergy_succ`  : `E_{r+1} = |G|·E_r + cross_r`, with
    `cross_r = ∑_{s∈G} ∑_{t∈G, t≠s} C_r(s − t)`                    — **THE RECURSION**.
* `rEnergy_succ_le` : `E_{r+1} ≤ |G|² · E_r`                       — the unconditional "free deep
    tail" growth ceiling (off-diagonal `C_r ≤ E_r`). Honest scope: this is the **non-prize** deep
    regime — it becomes operative only for `r` large, whereas the prize moment depth is
    `r ≍ log m ≪ 1.36 n`. The prize-relevant short-depth control of `C_r` (equivalently of
    `B = max_{b≠0}‖η_b‖`) is NOT addressed here; it remains the open BGK/Lam–Leung wall
    (CLAUDE.md face #3).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy subgroup_gaussSum_moment)

namespace ArkLib.ProximityGap.CharPMomentRecursion

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The `r`-fold sum-frequency `freq G r d = #{v ∈ (Fin r → G) : ∑ v = d}`, as a count
(indicator sum over the `r`-tuples). This is the combinatorial atom of the additive-moment ladder
(`E_r = ∑_d freq²`). -/
noncomputable def freq (G : Finset F) (r : ℕ) (d : F) : ℕ :=
  ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G), (if ∑ i, v i = d then 1 else 0)

/-- **The convolution recursion (the atom): `freq G (r+1) d = ∑_{s∈G} freq G r (d − s)`.**
Strip the first coordinate `s = v 0` of an `(r+1)`-tuple summing to `d`; the remaining `r`-tuple
must sum to `d − s`. Proven by the cons/tail bijection `(Fin (r+1) → G) ≃ G × (Fin r → G)`. -/
theorem freq_succ (G : Finset F) (r : ℕ) (d : F) :
    freq G (r + 1) d = ∑ s ∈ G, freq G r (d - s) := by
  unfold freq
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun v => ⟨v 0, Fin.tail v⟩) (fun p => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · rintro v hv
    rw [Fintype.mem_piFinset] at hv
    simp only [Finset.mem_sigma, Finset.mem_univ, Fintype.mem_piFinset, true_and]
    exact ⟨hv 0, fun i => hv i.succ⟩
  · rintro ⟨s, w⟩ hp
    simp only [Finset.mem_sigma, Fintype.mem_piFinset] at hp
    rw [Fintype.mem_piFinset]
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa using hp.1
    · intro j; simpa using hp.2 j
  · rintro v hv; simp [Fin.cons_self_tail]
  · rintro ⟨s, w⟩ hp; simp [Fin.tail_cons, Fin.cons_zero]
  · rintro v hv
    have hsum : ∑ i, v i = v 0 + ∑ i, Fin.tail v i := Fin.sum_univ_succ v
    have hiff : (∑ i, v i = d) ↔ (∑ i, Fin.tail v i = d - v 0) := by
      rw [hsum, eq_sub_iff_add_eq, add_comm]
    simp only [hiff]

/-- The total frequency mass at level `r` is `|G|^r` (the number of `r`-tuples). -/
theorem sum_freq (G : Finset F) (r : ℕ) :
    ∑ d : F, freq G r d = G.card ^ r := by
  unfold freq
  rw [Finset.sum_comm]
  calc ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G), ∑ d : F, (if ∑ i, v i = d then 1 else 0)
      = ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G), (1 : ℕ) := by
        refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [Finset.sum_ite_eq Finset.univ (∑ i, v i) (fun _ => (1:ℕ))]
        simp
    _ = G.card ^ r := by
        rw [Finset.sum_const, Fintype.card_piFinset_const, smul_eq_mul, mul_one]

/-- **The `r`-fold additive energy is the `ℓ²` of the sum-frequency: `E_r(G) = ∑_d freq G r d ²`.**
Regroup the energy double sum `∑_{v,w} [∑v = ∑w]` by the common sum value `d`. Combined with the
substrate `subgroup_gaussSum_moment`, this gives `∑_b ‖η_b‖^{2r} = q · ∑_d freq G r d ²`. -/
theorem rEnergy_eq_sum_freq_sq (G : Finset F) (r : ℕ) :
    rEnergy G r = ∑ d : F, freq G r d ^ 2 := by
  have step1 : ∀ (sv sw : F),
      (if sv = sw then (1:ℕ) else 0)
        = ∑ d : F, (if sv = d then 1 else 0) * (if sw = d then 1 else 0) := by
    intro sv sw
    rw [Finset.sum_eq_single sv]
    · by_cases h : sv = sw <;> simp [h, eq_comm]
    · intro d _ hd; simp [Ne.symm hd]
    · intro h; exact absurd (Finset.mem_univ sv) h
  unfold rEnergy
  calc ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G), ∑ w ∈ Fintype.piFinset (fun _ : Fin r => G),
          (if ∑ i, v i = ∑ i, w i then 1 else 0)
      = ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G), ∑ w ∈ Fintype.piFinset (fun _ : Fin r => G),
          ∑ d : F, (if ∑ i, v i = d then 1 else 0) * (if ∑ i, w i = d then 1 else 0) := by
        refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun w _ => ?_))
        exact step1 (∑ i, v i) (∑ i, w i)
    _ = ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G), ∑ d : F,
          ∑ w ∈ Fintype.piFinset (fun _ : Fin r => G),
          (if ∑ i, v i = d then 1 else 0) * (if ∑ i, w i = d then 1 else 0) := by
        refine Finset.sum_congr rfl (fun v _ => ?_)
        exact Finset.sum_comm
    _ = ∑ d : F, ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G),
          ∑ w ∈ Fintype.piFinset (fun _ : Fin r => G),
          (if ∑ i, v i = d then 1 else 0) * (if ∑ i, w i = d then 1 else 0) := Finset.sum_comm
    _ = ∑ d : F, freq G r d ^ 2 := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        simp only [freq]
        rw [sq, Finset.sum_mul_sum]

/-- The `r`-fold autocorrelation at offset `δ`: `C_r(δ) = ∑_e freq(e)·freq(e + δ)`. -/
noncomputable def autocorr (G : Finset F) (r : ℕ) (δ : F) : ℕ :=
  ∑ e : F, freq G r e * freq G r (e + δ)

/-- **Diagonal = energy:** `C_r(0) = E_r`. -/
theorem autocorr_zero (G : Finset F) (r : ℕ) :
    autocorr G r 0 = rEnergy G r := by
  rw [rEnergy_eq_sum_freq_sq]
  unfold autocorr
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [add_zero, sq]

/-- **The autocorrelation diagonal bound `C_r(δ) ≤ E_r`** for every offset `δ`. Elementary AM–GM
(`a·b ≤ (a²+b²)/2`, over `ℤ`) summed termwise, then reindex `e ↦ e + δ` to fold both halves back
to `E_r`. The unconditional ingredient behind the "free deep tail". -/
theorem autocorr_le_energy (G : Finset F) (r : ℕ) (δ : F) :
    autocorr G r δ ≤ rEnergy G r := by
  rw [rEnergy_eq_sum_freq_sq]
  have hAMGM : ∀ e : F, 2 * (freq G r e * freq G r (e + δ))
      ≤ freq G r e ^ 2 + freq G r (e + δ) ^ 2 := by
    intro e
    have : (2 * (freq G r e * freq G r (e + δ)) : ℤ)
        ≤ (freq G r e ^ 2 + freq G r (e + δ) ^ 2 : ℤ) := by
      nlinarith [sq_nonneg ((freq G r e : ℤ) - (freq G r (e + δ) : ℤ))]
    exact_mod_cast this
  have hsum : 2 * autocorr G r δ
      ≤ ∑ e : F, (freq G r e ^ 2 + freq G r (e + δ) ^ 2) := by
    unfold autocorr; rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun e _ => hAMGM e)
  have hsplit : ∑ e : F, (freq G r e ^ 2 + freq G r (e + δ) ^ 2)
      = 2 * ∑ d : F, freq G r d ^ 2 := by
    rw [Finset.sum_add_distrib]
    have h2 : ∑ e : F, freq G r (e + δ) ^ 2 = ∑ e : F, freq G r e ^ 2 :=
      Fintype.sum_equiv (Equiv.addRight δ) _ _ (fun e => rfl)
    rw [h2]; ring
  rw [hsplit] at hsum
  omega

/-! ### The exact one-step recursion -/

/-- `E_{r+1} = ∑_{s,t ∈ G} C_r(s − t)`: regroup the `(r+1)`-fold energy by stripping the last
coordinate of each side (the convolution `freq_succ`). Undivided double sum form. -/
theorem rEnergy_succ_double_sum (G : Finset F) (r : ℕ) :
    rEnergy G (r + 1) = ∑ s ∈ G, ∑ t ∈ G, autocorr G r (s - t) := by
  rw [rEnergy_eq_sum_freq_sq]
  have hexp : ∀ d : F, freq G (r + 1) d ^ 2
      = ∑ s ∈ G, ∑ t ∈ G, freq G r (d - s) * freq G r (d - t) := by
    intro d
    rw [freq_succ, sq, Finset.sum_mul_sum]
  calc ∑ d : F, freq G (r + 1) d ^ 2
      = ∑ d : F, ∑ s ∈ G, ∑ t ∈ G, freq G r (d - s) * freq G r (d - t) := by
        refine Finset.sum_congr rfl (fun d _ => hexp d)
    _ = ∑ s ∈ G, ∑ t ∈ G, ∑ d : F, freq G r (d - s) * freq G r (d - t) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun s _ => Finset.sum_comm)
    _ = ∑ s ∈ G, ∑ t ∈ G, autocorr G r (s - t) := by
        refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => ?_))
        unfold autocorr
        rw [← Fintype.sum_equiv (Equiv.addRight s)
              (fun e => freq G r e * freq G r (e + (s - t)))
              (fun d => freq G r (d - s) * freq G r (d - t))]
        intro d
        simp only [Equiv.coe_addRight]
        congr 2 <;> ring

/-- **THE RECURSION (T4): `E_{r+1} = |G|·E_r + cross_r`,** where
`cross_r = ∑_{s∈G} ∑_{t∈G, t≠s} C_r(s − t)` is the sum of off-diagonal autocorrelations. The
diagonal `s = t` of `∑_{s,t} C_r(s−t)` contributes `|G|·C_r(0) = |G|·E_r`; the rest is `cross_r`.
Exact, char-`p`, any finite set `G`, no analytic input (orthogonality only via the substrate). -/
theorem rEnergy_succ (G : Finset F) (r : ℕ) :
    rEnergy G (r + 1)
      = G.card * rEnergy G r + ∑ s ∈ G, ∑ t ∈ G.erase s, autocorr G r (s - t) := by
  rw [rEnergy_succ_double_sum]
  have hsplit : ∀ s ∈ G, ∑ t ∈ G, autocorr G r (s - t)
      = autocorr G r 0 + ∑ t ∈ G.erase s, autocorr G r (s - t) := by
    intro s hs
    rw [← Finset.add_sum_erase G (fun t => autocorr G r (s - t)) hs, sub_self]
  rw [Finset.sum_congr rfl hsplit]
  rw [Finset.sum_add_distrib, autocorr_zero, Finset.sum_const, smul_eq_mul]

/-- **The unconditional "free deep tail" growth ceiling: `E_{r+1} ≤ |G|² · E_r`.** Every
off-diagonal autocorrelation `C_r(s−t)` is `≤ E_r` (the diagonal bound), and `cross_r` has
`|G|·(|G|−1)` terms, so `E_{r+1} = |G|·E_r + cross_r ≤ |G|·E_r + |G|(|G|−1)·E_r = |G|²·E_r`.
Honest scope: this is the *non-prize* deep regime (operative only for `r` large; the prize moment
depth `r ≍ log m` is far below it). Fully unconditional — no Weil, sum-product, or Lam–Leung. -/
theorem rEnergy_succ_le (G : Finset F) (r : ℕ) :
    rEnergy G (r + 1) ≤ G.card ^ 2 * rEnergy G r := by
  rw [rEnergy_succ]
  have hcross : ∑ s ∈ G, ∑ t ∈ G.erase s, autocorr G r (s - t)
      ≤ ∑ s ∈ G, ∑ _t ∈ G.erase s, rEnergy G r := by
    refine Finset.sum_le_sum (fun s _ => ?_)
    exact Finset.sum_le_sum (fun t _ => autocorr_le_energy G r (s - t))
  have hconst : ∑ s ∈ G, ∑ _t ∈ G.erase s, rEnergy G r
      = ∑ _s ∈ G, (G.card - 1) * rEnergy G r := by
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [Finset.sum_const, Finset.card_erase_of_mem hs, smul_eq_mul]
  rw [hconst, Finset.sum_const, smul_eq_mul] at hcross
  calc G.card * rEnergy G r + ∑ s ∈ G, ∑ t ∈ G.erase s, autocorr G r (s - t)
      ≤ G.card * rEnergy G r + G.card * ((G.card - 1) * rEnergy G r) :=
        Nat.add_le_add_left hcross _
    _ = G.card ^ 2 * rEnergy G r := by
        cases Nat.eq_zero_or_pos G.card with
        | inl h => simp [h]
        | inr h =>
            have hge : G.card ≤ G.card ^ 2 := by nlinarith [h]
            have hmul : G.card * (G.card - 1) = G.card ^ 2 - G.card := by
              rw [Nat.mul_sub_one]; ring_nf
            rw [show G.card * ((G.card - 1) * rEnergy G r)
                  = (G.card * (G.card - 1)) * rEnergy G r by ring, hmul,
                Nat.sub_mul, ← Nat.add_sub_assoc (Nat.mul_le_mul_right _ hge)]
            omega

end ArkLib.ProximityGap.CharPMomentRecursion

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CharPMomentRecursion.freq_succ
#print axioms ArkLib.ProximityGap.CharPMomentRecursion.rEnergy_eq_sum_freq_sq
#print axioms ArkLib.ProximityGap.CharPMomentRecursion.autocorr_zero
#print axioms ArkLib.ProximityGap.CharPMomentRecursion.autocorr_le_energy
#print axioms ArkLib.ProximityGap.CharPMomentRecursion.rEnergy_succ
#print axioms ArkLib.ProximityGap.CharPMomentRecursion.rEnergy_succ_le

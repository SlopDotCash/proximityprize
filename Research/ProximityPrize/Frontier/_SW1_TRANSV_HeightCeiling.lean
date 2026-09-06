/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# SW1/TRANSV — the transversality seam in the `W_r` gauge: exact height ceiling and its cap

**Target.** Doctrine v2 §3(1) (`docs/kb/deltastar-466-tool-shape-doctrine-v2-2026-07-10.md`)
ranks "Galois/ideal transversality across embeddings" as the only seam where the numbers are
"even close" (height ceiling `≈ 0.22·n/log n` vs requirement `≈ 0.25·n/log n`).  Those two
numbers live in the census-determinant (CRT) gauge (OC-PIECEB allowance `(n/2)·log 6/log p`
vs G82 threshold `(n/4)·log 6/log p`, factor exactly 2).  This file pins what the
multiplicity/height data can give in the gauge that matters for CORE — the spurious count
`W_r` at ONE embedding — and shows the slack there is not a constant but the factor `2p/n`.

**Model.** `U` = the `n/2` degree-one primes `𝔭_u` of `ℤ[ζ_n]` above `p ≡ 1 (mod n)`;
`S` = the `2r`-term signed sums `β` (tuples); `spur u` = the tuples with `𝔭_u ∣ β`, `β ≠ 0`;
`mult β = #{u : 𝔭_u ∣ β}`.  Height data: an integer `N β` (the cyclotomic norm) with
`N β ≠ 0` for spurious `β`, `p^{mult β} ∣ N β` (distinct degree-one primes dividing `β` give
`p^{mult}` dividing the norm) and `|N β| ≤ H` (`H = (2r)^{n/2}` by the triangle inequality,
`(Σ c_a²)^{n/4}` by AM-GM/Parseval).  Galois symmetry `#(spur u) = W` for every `u` is the
SW1 lane SPARSE identity (cited, not re-proved: here it is a hypothesis).

**Results (all axiom-clean, Mathlib-only).**
* `sum_mult_eq_card_mul` — `Σ_β mult β = |U|·W` (the Galois-average identity, model form).
* `sum_mult_eq_sum_layers` — layer-cake: `Σ_β mult β = Σ_{j=1}^{|U|} #{β : mult β ≥ j}`.
* `mult_le_log_of_height` / `layer_eq_empty_of_height` — the exact height ceiling
  `mult β ≤ ⌊log_p H⌋` and `#{β : mult β ≥ j} = 0` for `p^j > H` (the ideal
  `∏_{u∈U'} 𝔭_u`, `|U'| = j`, has index `p^j`; a nonzero element of it has norm `≥ p^j`).
* `card_mul_le_card_mul_log` — the model cap `|U|·W ≤ |S|·⌊log_p H⌋`; with perfect
  transversality (`mult ≤ 1`) `|U|·W ≤ |S|` (`card_mul_le_card_of_transversal`).
* `height_le_of_spurious` — any admissible height bound satisfies `H ≥ p` as soon as ONE
  spurious relation exists, so `⌊log_p H⌋ ≥ 1` cannot be improved away.
* `blockModel` + `height_model_cannot_certify_core` (HEADLINE) — for every `p > C·|U|` and
  every `H ≥ p`, ALL of the above hypotheses (Galois symmetry, perfect transversality
  `mult ≡ 1`, norm data `p^{mult} ∣ N`, `|N| ≤ H`) are satisfied by an explicit model in which
  the CORE inequality `p·W ≤ C·|S|` FAILS.  Hence no argument whose only inputs are these
  (height, norm-divisibility, multiplicity, Galois symmetry — including any Lehmer /
  Dobrowolski / Mahler / 2-adic / antipodal refinement of `H`, which only changes
  `⌊log_p H⌋ ≥ 1`) can prove CORE; the cap-to-requirement ratio is `2p·⌊log_p H⌋/n ≥ 2p/n`.
* `prize_gate_vacuous` — at the prize cell the gate `(2r)^{n/2} < p` fails already at
  `r = 2` (`4^{2^29} > 2^30·2^128`), so `H ≥ p` is unavoidable there.

**Classification (dossier v4 §6):** exact pin + refutation-no-go IN THE ABSTRACT MODEL.
No bound on `M(μ_n)`; CORE remains OPEN / ON-BGK.
Probe: `scripts/probes/sw1_transv_multiplicity_profile.py`.
KB: `docs/kb/deltastar-sw1-transv-2026-09-05.md`.
-/

namespace SW1Transv

open Finset

/-- The multiplicity model: for each embedding `u` the finite set of tuples spurious at `u`. -/
structure MultModel (S U : Type*) where
  /-- tuples `β ≠ 0` with `𝔭_u ∣ β` -/
  spur : U → Finset S

variable {S U : Type*} [Fintype S] [DecidableEq S] [Fintype U] [DecidableEq U]

namespace MultModel

variable (M : MultModel S U)

/-- `mult β = #{u : β ∈ spur u}`. -/
def mult (β : S) : ℕ := (univ.filter fun u : U => β ∈ M.spur u).card

/-- The `j`-th layer `A_j = {β : mult β ≥ j}`. -/
def layer (j : ℕ) : Finset S := univ.filter fun β : S => j ≤ M.mult β

theorem mult_le_card (β : S) : M.mult β ≤ Fintype.card U := by
  unfold mult
  exact (card_filter_le _ _).trans (le_of_eq card_univ)

/-- Double counting: `Σ_β mult β = Σ_u #(spur u)`. -/
theorem sum_mult_eq_sum_card : ∑ β, M.mult β = ∑ u, (M.spur u).card := by
  calc ∑ β, M.mult β = ∑ β, ∑ u, (if β ∈ M.spur u then 1 else 0) := by
        refine sum_congr rfl fun β _ => ?_
        rw [mult, card_filter]
    _ = ∑ u, ∑ β, (if β ∈ M.spur u then 1 else 0) := sum_comm
    _ = ∑ u, (M.spur u).card := by
        refine sum_congr rfl fun u _ => ?_
        rw [← card_filter, filter_mem_eq_inter, univ_inter]

/-- The Galois-average identity in model form: `Σ_β mult β = |U| · W`. -/
theorem sum_mult_eq_card_mul {W : ℕ} (hW : ∀ u, (M.spur u).card = W) :
    ∑ β, M.mult β = Fintype.card U * W := by
  rw [sum_mult_eq_sum_card]
  simp [hW]

theorem card_filter_Icc_le {K m : ℕ} (hm : m ≤ K) :
    ((Icc 1 K).filter fun j => j ≤ m).card = m := by
  have h : ((Icc 1 K).filter fun j => j ≤ m) = Icc 1 m := by
    ext j
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2.trans hm⟩, h2⟩
  rw [h, Nat.card_Icc]
  omega

/-- Layer-cake (the two-level count): `Σ_β mult β = Σ_{j=1}^{|U|} #A_j`. -/
theorem sum_mult_eq_sum_layers :
    ∑ β, M.mult β = ∑ j ∈ Icc 1 (Fintype.card U), (M.layer j).card := by
  calc ∑ β, M.mult β
      = ∑ β, ∑ j ∈ Icc 1 (Fintype.card U), (if j ≤ M.mult β then 1 else 0) := by
        refine sum_congr rfl fun β _ => ?_
        rw [← card_filter, card_filter_Icc_le (M.mult_le_card β)]
    _ = ∑ j ∈ Icc 1 (Fintype.card U), ∑ β, (if j ≤ M.mult β then 1 else 0) := sum_comm
    _ = ∑ j ∈ Icc 1 (Fintype.card U), (M.layer j).card := by
        refine sum_congr rfl fun j _ => ?_
        rw [layer, card_filter]

section Height

variable {p H : ℕ} (N : S → ℤ)

/-- Norm divisibility: `p^{mult β} ≤ |N β|` for a spurious `β` (nonzero norm). -/
theorem pow_mult_le_abs (β : S) (hN : N β ≠ 0) (hdvd : (p : ℤ) ^ M.mult β ∣ N β) :
    ((p ^ M.mult β : ℕ) : ℤ) ≤ |N β| := by
  push_cast
  exact Int.le_of_dvd (abs_pos.mpr hN) ((dvd_abs _ _).mpr hdvd)

theorem pow_mult_le_height (β : S) (hN : N β ≠ 0) (hdvd : (p : ℤ) ^ M.mult β ∣ N β)
    (hH : |N β| ≤ H) : p ^ M.mult β ≤ H := by
  have h := (M.pow_mult_le_abs N β hN hdvd).trans hH
  exact_mod_cast h

/-- The exact height ceiling: `mult β ≤ ⌊log_p H⌋`. -/
theorem mult_le_log_of_height (hp : 1 < p) (β : S) (hN : N β ≠ 0)
    (hdvd : (p : ℤ) ^ M.mult β ∣ N β) (hH : |N β| ≤ H) : M.mult β ≤ Nat.log p H :=
  Nat.le_log_of_pow_le hp (M.pow_mult_le_height N β hN hdvd hH)

/-- Any admissible height bound is `≥ p` once a single spurious relation exists: the
per-`β` multiplicity cap `⌊log_p H⌋ ≥ 1` cannot be improved away by a sharper height input. -/
theorem height_le_of_spurious (hp : 1 < p) (β : S) (h1 : 1 ≤ M.mult β) (hN : N β ≠ 0)
    (hdvd : (p : ℤ) ^ M.mult β ∣ N β) (hH : |N β| ≤ H) : p ≤ H := by
  have h := M.pow_mult_le_height N β hN hdvd hH
  calc p = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ M.mult β := Nat.pow_le_pow_right (by omega) h1
    _ ≤ H := h

/-- The layer `A_j` is empty as soon as `p^j > H`: a nonzero element of the ideal
`∏_{u ∈ U'} 𝔭_u` (`|U'| = j`, index `p^j`) has norm at least `p^j`. -/
theorem layer_eq_empty_of_height (hp : 1 < p) (hN : ∀ β, 1 ≤ M.mult β → N β ≠ 0)
    (hdvd : ∀ β, (p : ℤ) ^ M.mult β ∣ N β) (hH : ∀ β, |N β| ≤ H) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : H < p ^ j) : M.layer j = ∅ := by
  rw [layer, filter_eq_empty_iff]
  intro β _ hβ
  have h1 : p ^ M.mult β ≤ H :=
    M.pow_mult_le_height N β (hN β (hj1.trans hβ)) (hdvd β) (hH β)
  have h2 : p ^ j ≤ p ^ M.mult β := Nat.pow_le_pow_right (by omega) hβ
  omega

/-- The height-model cap: `|U| · W ≤ |S| · ⌊log_p H⌋`.  In the cyclotomic instance
`|U| = n/2`, `|S| = n^{2r}`, `H = (2r)^{n/2}`, this is `W_r ≤ (2/n)·⌊(n/2)·log(2r)/log p⌋·n^{2r}`
against the requirement `W_r ≤ n^{2r}/p`: ratio `2p·⌊log_p H⌋/n`. -/
theorem card_mul_le_card_mul_log (hp : 1 < p) {W : ℕ} (hW : ∀ u, (M.spur u).card = W)
    (hN : ∀ β, 1 ≤ M.mult β → N β ≠ 0) (hdvd : ∀ β, (p : ℤ) ^ M.mult β ∣ N β)
    (hH : ∀ β, |N β| ≤ H) : Fintype.card U * W ≤ Fintype.card S * Nat.log p H := by
  rw [← M.sum_mult_eq_card_mul hW]
  calc ∑ β, M.mult β ≤ ∑ _β : S, Nat.log p H := by
        refine sum_le_sum fun β _ => ?_
        rcases Nat.eq_zero_or_pos (M.mult β) with h0 | h0
        · rw [h0]
          exact Nat.zero_le _
        · exact M.mult_le_log_of_height N hp β (hN β h0) (hdvd β) (hH β)
    _ = Fintype.card S * Nat.log p H := by rw [sum_const, card_univ, smul_eq_mul]

end Height

/-- Perfect transversality (`mult ≤ 1`, i.e. the spurious sets are pairwise disjoint — the
strongest conceivable multiplicity invariant, and what every accessible cell shows) still only
gives the pigeonhole cap `|U| · W ≤ |S|`, i.e. `W_r ≤ 2 n^{2r-1}`: a factor `2p/n` above the
requirement `n^{2r}/p`. -/
theorem card_mul_le_card_of_transversal {W : ℕ} (hW : ∀ u, (M.spur u).card = W)
    (hT : ∀ β, M.mult β ≤ 1) : Fintype.card U * W ≤ Fintype.card S := by
  rw [← M.sum_mult_eq_card_mul hW]
  calc ∑ β, M.mult β ≤ ∑ _β : S, 1 := sum_le_sum fun β _ => hT β
    _ = Fintype.card S := by rw [sum_const, card_univ, smul_eq_mul, mul_one]

end MultModel

/-- The extremal model: `S = U × Fin W`, `spur u = {u} × Fin W` (pairwise disjoint blocks,
each of size `W`, covering `S`). -/
def blockModel (U : Type*) (W : ℕ) : MultModel (U × Fin W) U where
  spur u := univ.map (Function.Embedding.sectR u (Fin W))

theorem blockModel_card (u : U) (W : ℕ) : ((blockModel U W).spur u).card = W := by
  simp [blockModel]

theorem blockModel_mult (W : ℕ) (β : U × Fin W) : (blockModel U W).mult β = 1 := by
  have h : (univ.filter fun u : U => β ∈ (blockModel U W).spur u) = {β.1} := by
    ext u
    rw [mem_filter, mem_singleton]
    show (u ∈ univ ∧ β ∈ univ.map (Function.Embedding.sectR u (Fin W))) ↔ u = β.1
    rw [mem_map]
    constructor
    · rintro ⟨-, i, -, hi⟩
      exact congrArg Prod.fst hi
    · intro hu
      exact ⟨mem_univ _, β.2, mem_univ _, by subst hu; rfl⟩
  rw [MultModel.mult, h, card_singleton]

/-- **HEADLINE (model cap).**  For every prime-size `p > C·|U|` and every height bound
`H ≥ p`, the full hypothesis set of the transversality/height seam — Galois symmetry
(`#(spur u) = W` for all `u`), perfect transversality (`mult ≡ 1`), and per-`β` norm data
(`N β ≠ 0`, `p^{mult β} ∣ N β`, `|N β| ≤ H`) — is satisfied by an explicit model in which the
CORE inequality `p · W ≤ C · |S|` fails.  Consequently no argument whose only inputs are
these can bound `W_r` below `|S|/|U| = 2n^{2r-1}`, a factor `2p/n` above the DC requirement
`n^{2r}/p`; sharpening `H` (Lehmer/Dobrowolski/Mahler lower bounds, AM-GM/Parseval, 2-adic
content, antipodal reduction) never changes this, because `H ≥ p` is forced by
`height_le_of_spurious` as soon as one spurious relation exists. -/
theorem height_model_cannot_certify_core (U : Type*) [Fintype U] [DecidableEq U]
    (W p H C : ℕ) (hp : 1 ≤ p) (hpH : p ≤ H) (hW : 1 ≤ W) (hC : C * Fintype.card U < p) :
    ∃ N : U × Fin W → ℤ,
      (∀ u, ((blockModel U W).spur u).card = W) ∧
      (∀ β, (blockModel U W).mult β ≤ 1) ∧
      (∀ β, N β ≠ 0) ∧
      (∀ β, (p : ℤ) ^ (blockModel U W).mult β ∣ N β) ∧
      (∀ β, |N β| ≤ H) ∧
      C * Fintype.card (U × Fin W) < p * W := by
  refine ⟨fun _ => (p : ℤ), fun u => blockModel_card u W,
    fun β => by rw [blockModel_mult],
    fun _ => by
      show (p : ℤ) ≠ 0
      exact_mod_cast (by omega : p ≠ 0),
    fun β => by rw [blockModel_mult, pow_one],
    fun _ => by
      show |(p : ℤ)| ≤ (H : ℤ)
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast hpH,
    ?_⟩
  rw [Fintype.card_prod, Fintype.card_fin, ← mul_assoc]
  exact Nat.mul_lt_mul_of_pos_right hC hW

/-- At the prize cell `n = 2^30`, `p = n · 2^128`, the height gate `(2r)^{n/2} < p` (the only
way to get `⌊log_p H⌋ = 0`) already fails at `r = 2`: `4^{2^29} > 2^30 · 2^128`. -/
theorem prize_gate_vacuous : (2 : ℕ) ^ 30 * 2 ^ 128 < 4 ^ (2 ^ 29) := by
  have h1 : (2 : ℕ) ^ 30 * 2 ^ 128 = 2 ^ 158 := by norm_num
  have h3 : (2 : ℕ) * 2 ^ 29 = 2 ^ 30 := by norm_num
  have h2 : (4 : ℕ) ^ (2 ^ 29) = 2 ^ (2 ^ 30) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, h3]
  rw [h1, h2]
  exact Nat.pow_lt_pow_right (by norm_num) (by norm_num)

end SW1Transv

#print axioms SW1Transv.MultModel.sum_mult_eq_sum_card
#print axioms SW1Transv.MultModel.sum_mult_eq_card_mul
#print axioms SW1Transv.MultModel.sum_mult_eq_sum_layers
#print axioms SW1Transv.MultModel.mult_le_log_of_height
#print axioms SW1Transv.MultModel.height_le_of_spurious
#print axioms SW1Transv.MultModel.layer_eq_empty_of_height
#print axioms SW1Transv.MultModel.card_mul_le_card_mul_log
#print axioms SW1Transv.MultModel.card_mul_le_card_of_transversal
#print axioms SW1Transv.blockModel_card
#print axioms SW1Transv.blockModel_mult
#print axioms SW1Transv.height_model_cannot_certify_core
#print axioms SW1Transv.prize_gate_vacuous

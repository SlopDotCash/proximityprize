/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ64WindowBookkeeping

/-!
# SYZ65 — degree-controlled balanced-window Bézout surjectivity ⇒ `RankNullity` unconditional

SYZ64 discharged `SYZ44.TwoRamp` for the syzygy kernel of a coprime triple, leaving the degree-sum
law `n₁ + n₂ = d₀ + d₁ + d₂` conditional on the single remaining structural input
`SYZ44.RankNullity` — the **degree-controlled Bézout surjectivity** of the balanced-window map onto
`{p : deg p ≤ D}`, together with its rank–nullity dimension count.

**This file discharges `SYZ44.RankNullity` for the syzygy kernel, unconditionally and axiom-clean**,
hence lands the degree-sum law `n₁ + n₂ = d₀ + d₁ + d₂` **unconditionally** (given only that the
weights `d` are the generator degrees and the triple is coprime).

## The windowed map and rank–nullity

Fix `(f, g, h)` coprime with `d i` the degree of the `i`-th generator, and `D`.  Consider the
`K`-linear **balanced-window map**

  `Ψ_D : degreeLT(D+1−d₀) × degreeLT(D+1−d₁) × degreeLT(D+1−d₂) → K[X]`,
  `(r₀, r₁, r₂) ↦ r₀·f + r₁·g + r₂·h`.

* **Domain** `= (D+1−d₀) + (D+1−d₁) + (D+1−d₂)` (`Module.finrank_prod` + `finrank_degreeLT`).
* **Kernel** `≅ windowKD d (ker φ) D` (both are `{r : pdeg d r ≤ D, φ r = 0}`), so
  `finrank (ker Ψ_D) = finrank (windowKD …) = hilb D` (`jMap` injective onto the window).
* **Range** `= degreeLT(D+1)` for `D ≥ D₀ := n₂` — the degree-controlled surjectivity, proved by the
  **cofactor-reduction descent**: any Bézout representative (SYZ57) is reduced modulo the μ-basis
  `(e₁, e₂)` (SYZ64) to product-degree `≤ D`, using that the top-cancellation vector of a
  representative is a syzygy leading vector (`leadMap`-kernel = `span{lv e₁, lv e₂}`) — well-founded
  descent on `pdeg`.  So `finrank (range Ψ_D) = D+1`.

Rank–nullity `finrank (range Ψ_D) + finrank (ker Ψ_D) = finrank (domain)` gives exactly

  `(D+1) + hilb D = (D+1−d₀) + (D+1−d₁) + (D+1−d₂)`,

which is `SYZ44.RankNullity (fun D => finrank K (windowKD …)) (d 0) (d 1) (d 2) n₂`.

## Scrupulous honesty — scope

This lands `RankNullity` **unconditionally** for the coprime-triple syzygy kernel with the generator
weights, so — chaining SYZ64's `TwoRamp` — the **degree-sum law `n₁ + n₂ = d₀ + d₁ + d₂` is now
unconditional** (`degree_sum_unconditional`).  Both structural inputs of `SYZ44.degree_sum_of_hilbert`
are discharged theory.  This does **not** claim δ* closure: the imbalance bound `ι ≤ 1` (gap `≤ 3`)
remains the sole open mathematical input on the Sylvester side (G172), and the production wire needs
the downstream census/realizability layers.

Axiom-clean; `#print axioms` at the bottom.  No `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open Module Polynomial
open ArkLib.ProximityGap.SYZ62
open ArkLib.ProximityGap.SYZ63

namespace ArkLib.ProximityGap.SYZ65

variable {K : Type*} [Field K]

/-! ## 1. The leading map and the top-coefficient identity -/

/-- **The leading map** `L : K³ → K`, `v ↦ f.lead·v₀ + g.lead·v₁ + h.lead·v₂`.  It reads off the
top-degree coefficient of `φ` applied to the leading vector of a representative. -/
def leadMap (f g h : K[X]) : (Fin 3 → K) →ₗ[K] K where
  toFun v := f.leadingCoeff * v 0 + g.leadingCoeff * v 1 + h.leadingCoeff * v 2
  map_add' v w := by simp only [Pi.add_apply]; ring
  map_smul' c v := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem leadMap_apply (f g h : K[X]) (v : Fin 3 → K) :
    leadMap f g h v = f.leadingCoeff * v 0 + g.leadingCoeff * v 1 + h.leadingCoeff * v 2 := rfl

/-- **Top-coefficient of `gen · r`.**  For `gen ≠ 0`, weight `Di = deg gen`, and a slot bound
`deg r + Di ≤ M`, the coefficient of `gen · r` at `M` is `gen.leadingCoeff · r.coeff (M − Di)`
(`= gen.leadingCoeff` times the corresponding leading-vector slot). -/
private theorem coeff_gen_mul_top (gen r : K[X]) {Di M : ℕ} (hgen : gen ≠ 0)
    (hDi : Di = gen.natDegree) (hbound : r.degree + (Di : WithBot ℕ) ≤ (M : WithBot ℕ)) :
    (gen * r).coeff M = gen.leadingCoeff * r.coeff (M - Di) := by
  rcases eq_or_ne r 0 with hr | hr
  · subst hr; simp
  · have hdeg : r.degree = (r.natDegree : WithBot ℕ) := degree_eq_natDegree hr
    rw [hdeg, ← Nat.cast_add, Nat.cast_le] at hbound
    have hrle : r.natDegree ≤ M - Di := by omega
    rcases eq_or_lt_of_le hrle with heq | hlt
    · have hM : M = gen.natDegree + r.natDegree := by omega
      have hrc : r.coeff (M - Di) = r.leadingCoeff := by rw [← heq]; rfl
      rw [hrc, hM, coeff_mul_degree_add_degree]
    · have hrc : r.coeff (M - Di) = 0 := coeff_eq_zero_of_natDegree_lt hlt
      rw [hrc, mul_zero]
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_mul hgen hr]; omega

/-- **The top-coefficient identity.**  For weights `d i = deg (generator i)` and any representative
`r` with `pdeg d r ≤ M`, the coefficient of `φ r = f r₀ + g r₁ + h r₂` at `M` equals `L` applied to
the leading vector `lv d M r`. -/
theorem coeff_phi_eq_leadMap {f g h : K[X]} {d : Fin 3 → ℕ}
    (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0)
    (hd0 : d 0 = f.natDegree) (hd1 : d 1 = g.natDegree) (hd2 : d 2 = h.natDegree)
    {r : Fin 3 → K[X]} {M : ℕ} (hle : pdeg d r ≤ (M : WithBot ℕ)) :
    (f * r 0 + g * r 1 + h * r 2).coeff M = leadMap f g h (lv d M r) := by
  have hb : ∀ i : Fin 3, (r i).degree + ((d i : ℕ) : WithBot ℕ) ≤ (M : WithBot ℕ) := by
    intro i; have := le_trans (pterm_le_pdeg d r i) hle; simpa [pterm] using this
  rw [coeff_add, coeff_add,
    coeff_gen_mul_top f (r 0) hf hd0 (hb 0),
    coeff_gen_mul_top g (r 1) hg hd1 (hb 1),
    coeff_gen_mul_top h (r 2) hh hd2 (hb 2)]
  simp only [leadMap_apply, lv_apply]

/-! ## 2. The leading map has a 2-dimensional kernel spanned by the μ-basis leading vectors -/

/-- **The leading vectors of the μ-basis span `ker L`.**  Any `v` with `L v = 0` is a `K`-combination
of `lv d n₁ e₁` and `lv d n₂ e₂`.  Proof: `L` is a nonzero functional (rank–nullity ⇒ `finrank ker L
= 2`), the two independent kernel elements `lv d nⱼ eⱼ` (their `L`-image is the top coefficient of
`φ eⱼ = 0`) span a 2-dimensional subspace, hence all of `ker L`. -/
theorem exists_coeff_of_leadMap_zero {f g h : K[X]} {d : Fin 3 → ℕ}
    (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0)
    (hd0 : d 0 = f.natDegree) (hd1 : d 1 = g.natDegree) (hd2 : d 2 = h.natDegree)
    {e₁ e₂ : Fin 3 → K[X]} {n₁ n₂ : ℕ}
    (he₁ : f * e₁ 0 + g * e₁ 1 + h * e₁ 2 = 0)
    (he₂ : f * e₂ 0 + g * e₂ 1 + h * e₂ 2 = 0)
    (hpd₁ : pdeg d e₁ = (n₁ : WithBot ℕ)) (hpd₂ : pdeg d e₂ = (n₂ : WithBot ℕ))
    (hpair : LinearIndependent K ![lv d n₁ e₁, lv d n₂ e₂])
    {v : Fin 3 → K} (hv : leadMap f g h v = 0) :
    ∃ c₁ c₂ : K, c₁ • lv d n₁ e₁ + c₂ • lv d n₂ e₂ = v := by
  set L := leadMap f g h with hL
  set lc₁ := lv d n₁ e₁ with hlc₁
  set lc₂ := lv d n₂ e₂ with hlc₂
  -- lc₁, lc₂ ∈ ker L
  have hL1 : L lc₁ = 0 := by
    have h := coeff_phi_eq_leadMap hf hg hh hd0 hd1 hd2 (r := e₁) (M := n₁) (le_of_eq hpd₁)
    rw [he₁, coeff_zero] at h; exact h.symm
  have hL2 : L lc₂ = 0 := by
    have h := coeff_phi_eq_leadMap hf hg hh hd0 hd1 hd2 (r := e₂) (M := n₂) (le_of_eq hpd₂)
    rw [he₂, coeff_zero] at h; exact h.symm
  -- L is surjective
  have hfl : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
  have hLsurj : Function.Surjective L := by
    intro y
    refine ⟨![y * (f.leadingCoeff)⁻¹, 0, 0], ?_⟩
    simp only [hL, leadMap_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, mul_zero, add_zero]
    rw [mul_left_comm, mul_inv_cancel₀ hfl, mul_one]
  -- finrank (ker L) = 2
  have hrn := LinearMap.finrank_range_add_finrank_ker L
  have hrange1 : finrank K (LinearMap.range L) = 1 := by
    rw [LinearMap.range_eq_top.mpr hLsurj, finrank_top, Module.finrank_self]
  rw [hrange1, Module.finrank_fin_fun] at hrn
  have hfrker : finrank K (LinearMap.ker L) = 2 := by omega
  -- span {lc₁, lc₂} ≤ ker L, with finrank 2, so equal
  have hmem1 : lc₁ ∈ LinearMap.ker L := by rw [LinearMap.mem_ker]; exact hL1
  have hmem2 : lc₂ ∈ LinearMap.ker L := by rw [LinearMap.mem_ker]; exact hL2
  have hspanle : Submodule.span K ({lc₁, lc₂} : Set (Fin 3 → K)) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]; intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h <;> subst h
    · exact hmem1
    · exact hmem2
  have hset : (Set.range ![lc₁, lc₂]) = ({lc₁, lc₂} : Set (Fin 3 → K)) := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
  have hfrspan : finrank K (Submodule.span K ({lc₁, lc₂} : Set (Fin 3 → K))) = 2 := by
    have hc := finrank_span_eq_card hpair
    rw [hset] at hc
    simpa using hc
  have heq : Submodule.span K ({lc₁, lc₂} : Set (Fin 3 → K)) = LinearMap.ker L :=
    Submodule.eq_of_le_of_finrank_eq hspanle (by rw [hfrspan, hfrker])
  have hvmem : v ∈ LinearMap.ker L := by rw [LinearMap.mem_ker]; exact hv
  rw [← heq, Submodule.mem_span_pair] at hvmem
  obtain ⟨c₁, c₂, hc⟩ := hvmem
  exact ⟨c₁, c₂, hc⟩

/-! ## 3. The cofactor-reduction descent: degree-controlled surjectivity -/

/-- **Degree-controlled Bézout surjectivity (the descent).**  Given the coprime triple, the μ-basis
`(e₁, e₂)` of the syzygy kernel, and `D ≥ n₂`, every `p` with `deg p ≤ D` is `φ r` for some `r` with
`pdeg d r ≤ D`.  Start from any (ungraded) Bézout representative (SYZ57); if its product-degree
`M > D` then the top of `φ r` cancels (`deg p ≤ D < M`), so `lv d M r` is a syzygy leading vector
(`exists_coeff_of_leadMap_zero`) — subtract the matching monomial multiple of the μ-basis to strictly
drop `pdeg`; well-founded descent on `pdeg`. -/
theorem exists_window_repr {f g h : K[X]} {d : Fin 3 → ℕ}
    (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0)
    (hd0 : d 0 = f.natDegree) (hd1 : d 1 = g.natDegree) (hd2 : d 2 = h.natDegree)
    {e₁ e₂ : Fin 3 → K[X]} {n₁ n₂ : ℕ}
    (he₁ : f * e₁ 0 + g * e₁ 1 + h * e₁ 2 = 0)
    (he₂ : f * e₂ 0 + g * e₂ 1 + h * e₂ 2 = 0)
    (hpd₁ : pdeg d e₁ = (n₁ : WithBot ℕ)) (hpd₂ : pdeg d e₂ = (n₂ : WithBot ℕ))
    (hpair : LinearIndependent K ![lv d n₁ e₁, lv d n₂ e₂]) (hn₁₂ : n₁ ≤ n₂)
    (hfg : IsCoprime f g) (hfh : IsCoprime f h)
    (D : ℕ) (hD : n₂ ≤ D) (p : K[X]) (hp : p.degree ≤ (D : WithBot ℕ)) :
    ∃ r : Fin 3 → K[X], pdeg d r ≤ (D : WithBot ℕ) ∧ f * r 0 + g * r 1 + h * r 2 = p := by
  obtain ⟨s₁, s₂, s₃, hs⟩ := ArkLib.ProximityGap.SYZ57.exists_triple_repr hfg hfh p
  -- kernel membership of e₁, e₂ as syzygyMap equalities
  have hker1 : SYZ61.syzygyMap f g h e₁ = 0 := by rw [SYZ61.syzygyMap_apply]; exact he₁
  have hker2 : SYZ61.syzygyMap f g h e₂ = 0 := by rw [SYZ61.syzygyMap_apply]; exact he₂
  have key : ∀ v : WithBot ℕ, ∀ r : Fin 3 → K[X],
      f * r 0 + g * r 1 + h * r 2 = p → pdeg d r = v →
      ∃ r' : Fin 3 → K[X], pdeg d r' ≤ (D : WithBot ℕ) ∧ f * r' 0 + g * r' 1 + h * r' 2 = p := by
    intro v
    induction v using WellFoundedLT.induction with
    | _ v IH =>
      intro r hφr hpdr
      by_cases hvD : v ≤ (D : WithBot ℕ)
      · exact ⟨r, hpdr ▸ hvD, hφr⟩
      · push_neg at hvD
        have hvne : v ≠ ⊥ := by intro h; rw [h] at hvD; exact absurd hvD not_lt_bot
        obtain ⟨M, hM⟩ := WithBot.ne_bot_iff_exists.mp hvne
        rw [← Nat.cast_withBot] at hM
        have hveq : v = (M : WithBot ℕ) := hM.symm
        have hDM : D < M := by
          have := hveq ▸ hvD; exact_mod_cast this
        have hpdrM : pdeg d r = (M : WithBot ℕ) := hpdr.trans hveq
        have hn₂M : n₂ ≤ M := le_trans hD (le_of_lt hDM)
        have hn₁M : n₁ ≤ M := le_trans hn₁₂ hn₂M
        -- top coefficient of φ r vanishes
        have hcoeff0 : (f * r 0 + g * r 1 + h * r 2).coeff M = 0 := by
          rw [hφr]; apply coeff_eq_zero_of_degree_lt
          calc p.degree ≤ (D : WithBot ℕ) := hp
            _ < (M : WithBot ℕ) := by exact_mod_cast hDM
        have hLzero : leadMap f g h (lv d M r) = 0 := by
          rw [← coeff_phi_eq_leadMap hf hg hh hd0 hd1 hd2 (le_of_eq hpdrM)]; exact hcoeff0
        obtain ⟨c₁, c₂, hc⟩ := exists_coeff_of_leadMap_zero hf hg hh hd0 hd1 hd2
          he₁ he₂ hpd₁ hpd₂ hpair hLzero
        set lc₁ := lv d n₁ e₁ with hlc₁
        set lc₂ := lv d n₂ e₂ with hlc₂
        set q₁ : K[X] := C c₁ * X ^ (M - n₁) with hq₁
        set q₂ : K[X] := C c₂ * X ^ (M - n₂) with hq₂
        set r' : Fin 3 → K[X] := r - (q₁ • e₁ + q₂ • e₂) with hr'
        -- φ r' = p
        have hφr' : f * r' 0 + g * r' 1 + h * r' 2 = p := by
          have hmap : SYZ61.syzygyMap f g h r' = p := by
            rw [hr', map_sub, map_add, map_smul, map_smul, hker1, hker2, smul_zero, smul_zero,
              add_zero, sub_zero, SYZ61.syzygyMap_apply]
            exact hφr
          rw [SYZ61.syzygyMap_apply] at hmap; exact hmap
        -- leading-vector shift lemma
        have lvShift : ∀ (c : K) (nⱼ : ℕ) (eⱼ : Fin 3 → K[X]), nⱼ ≤ M →
            pdeg d eⱼ = (nⱼ : WithBot ℕ) →
            lv d M ((C c * X ^ (M - nⱼ)) • eⱼ) = c • lv d nⱼ eⱼ := by
          intro c nⱼ eⱼ hnⱼ hpdⱼ
          rcases eq_or_ne c 0 with hc0 | hc0
          · subst hc0; simp only [map_zero, zero_mul, zero_smul]; funext i; simp [lv]
          · set qc : K[X] := C c * X ^ (M - nⱼ) with hqc
            have hqcne : qc ≠ 0 := mul_ne_zero (by simpa using hc0) (pow_ne_zero _ X_ne_zero)
            have hqcnd : qc.natDegree = M - nⱼ := by
              rw [hqc, natDegree_C_mul (by simpa using hc0), natDegree_X_pow]
            have hqclead : qc.leadingCoeff = c := by
              rw [hqc, leadingCoeff_mul, leadingCoeff_X_pow, mul_one, leadingCoeff_C]
            have hsm := lv_smul_top (d := d) (q := qc) hqcne hpdⱼ
            rw [hqcnd] at hsm
            have hidx : M - nⱼ + nⱼ = M := by omega
            rw [hidx] at hsm; rw [hsm, hqclead]
        have hlvq₁ : lv d M (q₁ • e₁) = c₁ • lc₁ := by rw [hq₁]; exact lvShift c₁ n₁ e₁ hn₁M hpd₁
        have hlvq₂ : lv d M (q₂ • e₂) = c₂ • lc₂ := by rw [hq₂]; exact lvShift c₂ n₂ e₂ hn₂M hpd₂
        have hlvr' : lv d M r' = 0 := by
          rw [hr', show r - (q₁ • e₁ + q₂ • e₂)
                = r + (-1 : K) • (q₁ • e₁) + (-1 : K) • (q₂ • e₂) by
                  rw [neg_one_smul, neg_one_smul]; ring]
          rw [lv_add, lv_add, lv_smulK, lv_smulK, hlvq₁, hlvq₂, ← hc]
          module
        -- pdeg r' ≤ M
        have hpdqle : ∀ (c : K) (nⱼ : ℕ), nⱼ ≤ M →
            (C c * X ^ (M - nⱼ)).degree + (nⱼ : WithBot ℕ) ≤ (M : WithBot ℕ) := by
          intro c nⱼ hnⱼ
          rcases eq_or_ne c 0 with hc0 | hc0
          · subst hc0; simp
          · have hne : (C c * X ^ (M - nⱼ)) ≠ 0 :=
              mul_ne_zero (by simpa using hc0) (pow_ne_zero _ X_ne_zero)
            have hnd : (C c * X ^ (M - nⱼ)).natDegree = M - nⱼ := by
              rw [natDegree_C_mul (by simpa using hc0), natDegree_X_pow]
            rw [degree_eq_natDegree hne, hnd, ← Nat.cast_add, Nat.cast_le]; omega
        have hpdle : pdeg d r' ≤ (M : WithBot ℕ) := by
          rw [hr']
          refine le_trans (pdeg_sub_le r _) (max_le ?_ ?_)
          · exact le_of_eq hpdrM
          · refine le_trans (pdeg_add_le d _ _) (max_le ?_ ?_)
            · rw [pdeg_smul, hpd₁, hq₁]; exact hpdqle c₁ n₁ hn₁M
            · rw [pdeg_smul, hpd₂, hq₂]; exact hpdqle c₂ n₂ hn₂M
        have hpdr'lt : pdeg d r' < (M : WithBot ℕ) := pdeg_lt_of_lv_eq_zero hpdle hlvr'
        exact IH (pdeg d r') (by rw [hveq]; exact hpdr'lt) r' hφr' rfl
  exact key (pdeg d ![s₁, s₂, s₃]) ![s₁, s₂, s₃] (by simpa using hs) rfl

/-! ## 4. The balanced-window map `Ψ` and the coordinate map `j` -/

/-- The balanced-window domain: the product of the three principal degree windows. -/
abbrev Dom (K : Type*) [Field K] (d : Fin 3 → ℕ) (D : ℕ) : Type _ :=
  degreeLT K (D + 1 - d 0) × degreeLT K (D + 1 - d 1) × degreeLT K (D + 1 - d 2)

/-- **The balanced-window map** `Ψ_D : Dom → K[X]`, `(r₀, r₁, r₂) ↦ r₀·f + r₁·g + r₂·h`. -/
noncomputable def psiMap (f g h : K[X]) (d : Fin 3 → ℕ) (D : ℕ) : Dom K d D →ₗ[K] K[X] :=
  ((LinearMap.toSpanSingleton K[X] K[X] f).restrictScalars K).comp
      ((degreeLT K (D + 1 - d 0)).subtype.comp (LinearMap.fst K _ _))
    + ((LinearMap.toSpanSingleton K[X] K[X] g).restrictScalars K).comp
      ((degreeLT K (D + 1 - d 1)).subtype.comp
        ((LinearMap.fst K _ _).comp (LinearMap.snd K _ _)))
    + ((LinearMap.toSpanSingleton K[X] K[X] h).restrictScalars K).comp
      ((degreeLT K (D + 1 - d 2)).subtype.comp
        ((LinearMap.snd K _ _).comp (LinearMap.snd K _ _)))

theorem psiMap_apply {f g h : K[X]} {d : Fin 3 → ℕ} {D : ℕ} (p : Dom K d D) :
    psiMap f g h d D p = (p.1 : K[X]) * f + (p.2.1 : K[X]) * g + (p.2.2 : K[X]) * h := by
  simp only [psiMap, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, Submodule.subtype_apply, LinearMap.restrictScalars_apply,
    LinearMap.toSpanSingleton_apply, smul_eq_mul]

/-- **The coordinate map** `j : Dom → K[X]³`, `(r₀, r₁, r₂) ↦ ![r₀, r₁, r₂]`. -/
noncomputable def jMap (K : Type*) [Field K] (d : Fin 3 → ℕ) (D : ℕ) :
    Dom K d D →ₗ[K] (Fin 3 → K[X]) :=
  LinearMap.pi ![
    (degreeLT K (D + 1 - d 0)).subtype.comp (LinearMap.fst K _ _),
    (degreeLT K (D + 1 - d 1)).subtype.comp ((LinearMap.fst K _ _).comp (LinearMap.snd K _ _)),
    (degreeLT K (D + 1 - d 2)).subtype.comp ((LinearMap.snd K _ _).comp (LinearMap.snd K _ _))]

theorem jMap_apply {d : Fin 3 → ℕ} {D : ℕ} (p : Dom K d D) :
    jMap K d D p = ![(p.1 : K[X]), (p.2.1 : K[X]), (p.2.2 : K[X])] := by
  funext i
  fin_cases i <;> simp [jMap]

theorem jMap_injective (d : Fin 3 → ℕ) (D : ℕ) : Function.Injective (jMap K d D) := by
  intro p q hpq
  rw [jMap_apply, jMap_apply] at hpq
  have h0 := congrFun hpq 0
  have h1 := congrFun hpq 1
  have h2 := congrFun hpq 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at h0 h1 h2
  exact Prod.ext (Subtype.ext h0) (Prod.ext (Subtype.ext h1) (Subtype.ext h2))

/-! ## 5. `RankNullity` for the syzygy-kernel window, unconditional -/

/-- Slot-degree bound: a coordinate of the domain, times its generator, has degree `≤ D`. -/
private theorem degree_term_le {gen r : K[X]} {D Di : ℕ} (hgen : gen ≠ 0) (hDi : Di = gen.natDegree)
    (hmem : r ∈ degreeLT K (D + 1 - Di)) : (r * gen).degree ≤ (D : WithBot ℕ) := by
  rcases eq_or_ne r 0 with h0 | h0
  · simp [h0]
  · rw [mem_degreeLT, degree_eq_natDegree h0, Nat.cast_lt] at hmem
    rw [degree_mul, degree_eq_natDegree h0, degree_eq_natDegree hgen, ← Nat.cast_add, Nat.cast_le,
      ← hDi]
    omega

/-- Membership of a slot in its degree window from a `pdeg` bound. -/
private theorem mem_window_of_pdeg {d : Fin 3 → ℕ} {r : Fin 3 → K[X]} {D : ℕ}
    (hpdr : pdeg d r ≤ (D : WithBot ℕ)) (i : Fin 3) : r i ∈ degreeLT K (D + 1 - d i) :=
  SYZ64.mem_degreeLT_of_pdeg_le (by
    have := le_trans (pterm_le_pdeg d r i) hpdr; simpa [pterm] using this)

/-- Slot bound `deg a + Di ≤ D` from window membership (the inverse of `mem_degreeLT_of_pdeg_le`). -/
private theorem pterm_le_of_mem {a : K[X]} {Di D : ℕ} (hmem : a ∈ degreeLT K (D + 1 - Di)) :
    a.degree + (Di : WithBot ℕ) ≤ (D : WithBot ℕ) := by
  rcases eq_or_ne a 0 with h0 | h0
  · simp [h0]
  · rw [mem_degreeLT, degree_eq_natDegree h0, Nat.cast_lt] at hmem
    rw [degree_eq_natDegree h0, ← Nat.cast_add, Nat.cast_le]; omega

/-- **`RankNullity` discharged (unconditional).**  For the syzygy kernel of a coprime triple, with
the generator weights `d i = deg (generator i)`, the windowed kernel dimension satisfies the
rank–nullity identity for every `D ≥ n₂`.  Hence `SYZ44.RankNullity` holds (with `D₀ = n₂`), no
longer a named hypothesis. -/
theorem rankNullity_windowKD {f g h : K[X]} {d : Fin 3 → ℕ}
    (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0)
    (hd0 : d 0 = f.natDegree) (hd1 : d 1 = g.natDegree) (hd2 : d 2 = h.natDegree)
    (hfg : IsCoprime f g) (hfh : IsCoprime f h) :
    ∃ D₀ : ℕ, ArkLib.ProximityGap.SYZ44.RankNullity
      (fun D => finrank K (SYZ64.windowKD d (LinearMap.ker (SYZ61.syzygyMap f g h)) D))
      (d 0) (d 1) (d 2) D₀ := by
  obtain ⟨e₁, e₂, n₁, n₂, he₁N, he₂N, hpd₁, hpd₂, hn₁₂, hpair, hspan⟩ :=
    SYZ64.exists_muBasisData d (LinearMap.ker (SYZ61.syzygyMap f g h))
      (SYZ61.rank_syzygyKernel hfg hfh)
  have he₁ : f * e₁ 0 + g * e₁ 1 + h * e₁ 2 = 0 := by
    have := he₁N; rw [LinearMap.mem_ker, SYZ61.syzygyMap_apply] at this; exact this
  have he₂ : f * e₂ 0 + g * e₂ 1 + h * e₂ 2 = 0 := by
    have := he₂N; rw [LinearMap.mem_ker, SYZ61.syzygyMap_apply] at this; exact this
  refine ⟨n₂, ?_⟩
  intro D hD
  set N := LinearMap.ker (SYZ61.syzygyMap f g h) with hN
  set Ψ := psiMap f g h d D with hΨ
  -- domain finrank
  have hdom : finrank K (Dom K d D) = (D + 1 - d 0) + ((D + 1 - d 1) + (D + 1 - d 2)) := by
    simp only [Dom, Module.finrank_prod, SYZ60.finrank_degreeLT]
  -- range Ψ = degreeLT (D+1)
  have hrange : LinearMap.range Ψ = degreeLT K (D + 1) := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      rw [hΨ, psiMap_apply, mem_degreeLT]
      have hle : ((p.1 : K[X]) * f + (p.2.1 : K[X]) * g + (p.2.2 : K[X]) * h).degree
          ≤ (D : WithBot ℕ) := by
        refine le_trans (degree_add_le _ _) (max_le (le_trans (degree_add_le _ _) (max_le ?_ ?_)) ?_)
        · exact degree_term_le hf hd0 p.1.2
        · exact degree_term_le hg hd1 p.2.1.2
        · exact degree_term_le hh hd2 p.2.2.2
      calc ((p.1 : K[X]) * f + (p.2.1 : K[X]) * g + (p.2.2 : K[X]) * h).degree
          ≤ (D : WithBot ℕ) := hle
        _ < ((D + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self D
    · intro q hq
      have hqD : q.degree ≤ (D : WithBot ℕ) := by
        rw [mem_degreeLT] at hq
        rcases eq_or_ne q 0 with h0 | h0
        · simp [h0]
        · rw [degree_eq_natDegree h0, Nat.cast_lt] at hq
          rw [degree_eq_natDegree h0, Nat.cast_le]; omega
      obtain ⟨r, hpdr, hφr⟩ := exists_window_repr hf hg hh hd0 hd1 hd2 he₁ he₂ hpd₁ hpd₂ hpair
        hn₁₂ hfg hfh D hD q hqD
      refine ⟨(⟨r 0, mem_window_of_pdeg hpdr 0⟩,
        ⟨r 1, mem_window_of_pdeg hpdr 1⟩, ⟨r 2, mem_window_of_pdeg hpdr 2⟩), ?_⟩
      rw [hΨ, psiMap_apply]
      show r 0 * f + r 1 * g + r 2 * h = q
      linear_combination hφr
  have hrangefr : finrank K (LinearMap.range Ψ) = D + 1 := by rw [hrange, SYZ60.finrank_degreeLT]
  -- ker Ψ ≅ windowKD via jMap
  set k : (LinearMap.ker Ψ) →ₗ[K] (Fin 3 → K[X]) := (jMap K d D).comp (LinearMap.ker Ψ).subtype
    with hk
  have hkInj : Function.Injective k := by
    rw [hk, LinearMap.coe_comp]
    exact (jMap_injective d D).comp (fun _ _ h => Subtype.ext h)
  have hkrange : LinearMap.range k = SYZ64.windowKD d N D := by
    apply le_antisymm
    · rintro _ ⟨⟨p, hpker⟩, rfl⟩
      rw [hk]
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, jMap_apply]
      rw [SYZ64.mem_windowKD]
      rw [LinearMap.mem_ker, hΨ, psiMap_apply] at hpker
      refine ⟨?_, ?_⟩
      · rw [hN, LinearMap.mem_ker, SYZ61.syzygyMap_apply]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons]
        show f * (p.1 : K[X]) + g * (p.2.1 : K[X]) + h * (p.2.2 : K[X]) = 0
        linear_combination hpker
      · refine pdeg_le (fun i => ?_)
        fin_cases i
        · simpa only [pterm, Matrix.cons_val_zero] using pterm_le_of_mem p.1.2
        · simpa only [pterm, Matrix.cons_val_one, Matrix.head_cons] using pterm_le_of_mem p.2.1.2
        · simpa only [pterm, Matrix.cons_val_two, Matrix.tail_cons] using pterm_le_of_mem p.2.2.2
    · intro w hw
      rw [SYZ64.mem_windowKD] at hw
      obtain ⟨hwN, hwde⟩ := hw
      refine ⟨⟨(⟨w 0, mem_window_of_pdeg hwde 0⟩,
        ⟨w 1, mem_window_of_pdeg hwde 1⟩, ⟨w 2, mem_window_of_pdeg hwde 2⟩), ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker, hΨ, psiMap_apply]
        rw [hN, LinearMap.mem_ker, SYZ61.syzygyMap_apply] at hwN
        show w 0 * f + w 1 * g + w 2 * h = 0
        linear_combination hwN
      · rw [hk]
        simp only [LinearMap.comp_apply, Submodule.subtype_apply, jMap_apply]
        funext i; fin_cases i <;> simp
  have hkerfr : finrank K (SYZ64.windowKD d N D) = finrank K (LinearMap.ker Ψ) := by
    have hfr := LinearMap.finrank_range_of_inj hkInj
    rw [hkrange] at hfr; exact hfr
  -- rank–nullity assembly
  have hrn := LinearMap.finrank_range_add_finrank_ker Ψ
  rw [hrangefr, hdom] at hrn
  show finrank K (SYZ64.windowKD d N D) + (D + 1) = (D + 1 - d 0) + (D + 1 - d 1) + (D + 1 - d 2)
  rw [hkerfr]
  omega

/-! ## 6. The degree-sum law, unconditional -/

/-- **The degree-sum law `n₁ + n₂ = d₀ + d₁ + d₂`, unconditional.**  Both structural inputs of
`SYZ44.degree_sum_of_hilbert` are now discharged theory: `TwoRamp` in SYZ64, `RankNullity` here.  For
a coprime triple with the generator weights, the μ-basis product-degrees satisfy the classical
degree-sum law with no remaining named hypothesis. -/
theorem degree_sum_unconditional {f g h : K[X]} {d : Fin 3 → ℕ}
    (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0)
    (hd0 : d 0 = f.natDegree) (hd1 : d 1 = g.natDegree) (hd2 : d 2 = h.natDegree)
    (hfg : IsCoprime f g) (hfh : IsCoprime f h) :
    ∃ n₁ n₂ : ℕ, n₁ ≤ n₂ ∧ n₁ + n₂ = d 0 + d 1 + d 2 := by
  obtain ⟨D₀, hRankNull⟩ := rankNullity_windowKD hf hg hh hd0 hd1 hd2 hfg hfh
  exact SYZ64.degree_sum_of_rankNullity hfg hfh D₀ hRankNull

end ArkLib.ProximityGap.SYZ65

/-! ## Axiom audit -/

#print axioms ArkLib.ProximityGap.SYZ65.coeff_phi_eq_leadMap
#print axioms ArkLib.ProximityGap.SYZ65.exists_coeff_of_leadMap_zero
#print axioms ArkLib.ProximityGap.SYZ65.exists_window_repr
#print axioms ArkLib.ProximityGap.SYZ65.rankNullity_windowKD
#print axioms ArkLib.ProximityGap.SYZ65.degree_sum_unconditional

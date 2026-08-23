/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CurveDecodability
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# The far-word supply, discharged by counting (#357)

`FarWordSupply C δ` — every word has a codeword at relative distance `> δ` — is the
counting input of [Jo26] Lemma 5.4 and one of the named open surfaces of the #357
tracker (§6).  The in-tree sufficient condition (`farWordSupply_of_far_pair`: two
codewords at relative distance `> 2δ`) inherently caps at `δ < 1/2`, while the
curve-decodability consumers want it throughout the capacity range.

This file discharges the surface for **every nondegenerate linear code at every
`δ` with `δ + 1/|F| < 1`** — in particular for every Reed–Solomon code — by the
averaging argument:

* `card_smul_fiber_le` — at a coordinate carrying a nonzero codeword value, every
  evaluation fiber `{v ∈ C : v i = c}` has size at most `|C|/|F|` (the map
  `(a, v) ↦ v + a • u₀` injects `F × fiber` into `C`);
* `card_mul_sum_agreement_le` — double count: summing agreements over all codewords,
  `|F| · Σ_{v ∈ C} #{j : v j = w j} ≤ n · |C|` for every center `w`;
* `farWordSupply_of_forall_exists_ne` — if every codeword were `δ`-close to `w`, each
  would contribute `≥ n − δn` agreements, so `|C|(n − δn) ≤ n|C|/|F|`, i.e.
  `1 ≤ δ + 1/|F|` — contradiction.  Hence a far word exists.
* `farWordSupply_rs` — Reed–Solomon codes (`k ≥ 1`) are nondegenerate (the constant
  codeword `1`), so the supply holds for all `δ + 1/|F| < 1`.
* `curveDecodable_iff_marked_rs` / `markedCurveDecodable_interleaved_of_curveDecodable_rs`
  — the [Jo26] §5 marked-equivalence and interleaving-transfer consumers, now
  **unconditional for RS** in that range.

Honest scope: `1 − 1/|F|` is what the averaging argument yields, not a per-code optimum
(e.g. the full code `F^ι` supplies far words at every `δ < 1`); some threshold below `1`
is necessary in general (the zero code — degenerate, excluded by the hypothesis — has no
far word for `w = 0` at any `δ`).  What matters for the consumers is that
`1 − 1/|F|` covers the entire capacity range `δ ≤ 1 − ρ` of every Reed–Solomon code at
cryptographic field sizes, where the previous far-pair route stopped at `1/2`.

## References
* [Jo26] ePrint 2026/891, §5 (Lemma 5.4 / Theorem 5.5).
* Issue #357 §6 (named surface `FarWordSupply`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Code

namespace ProximityGap.CurveDec

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **The fiber bound.**  If some codeword is nonzero at coordinate `i`, then for every
value `c` the evaluation fiber `{v ∈ C : v i = c}` has size at most `|C| / |F|`:
the map `(a, v) ↦ v + a • u₀` injects `F × fiber` into `C`. -/
theorem card_smul_fiber_le (C : Submodule F (ι → A)) {i : ι} {u₀ : ι → A}
    (hu₀ : u₀ ∈ C) (hne : u₀ i ≠ 0) (c : A) :
    Fintype.card F *
        (Finset.univ.filter (fun v : ι → A => v ∈ C ∧ v i = c)).card
      ≤ (Finset.univ.filter (fun v : ι → A => v ∈ C)).card := by
  classical
  set fib : Finset (ι → A) :=
    Finset.univ.filter (fun v : ι → A => v ∈ C ∧ v i = c) with hfib
  have hmaps : ∀ p ∈ (Finset.univ : Finset F) ×ˢ fib,
      (p.2 + p.1 • u₀) ∈ Finset.univ.filter (fun v : ι → A => v ∈ C) := by
    rintro ⟨a, v⟩ hp
    obtain ⟨-, hv⟩ := Finset.mem_product.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact C.add_mem ((Finset.mem_filter.mp hv).2.1) (C.smul_mem a hu₀)
  have hinj : Set.InjOn (fun p : F × (ι → A) => p.2 + p.1 • u₀)
      ↑((Finset.univ : Finset F) ×ˢ fib) := by
    rintro ⟨a, v⟩ hav ⟨a', v'⟩ hav' heq
    have hv : v ∈ fib := (Finset.mem_product.mp (Finset.mem_coe.mp hav)).2
    have hv' : v' ∈ fib := (Finset.mem_product.mp (Finset.mem_coe.mp hav')).2
    have hvi : v i = c := ((Finset.mem_filter.mp hv).2).2
    have hvi' : v' i = c := ((Finset.mem_filter.mp hv').2).2
    have heqi : v i + a • u₀ i = v' i + a' • u₀ i := by
      have := congrFun heq i
      simpa using this
    rw [hvi, hvi'] at heqi
    have hsmul : a • u₀ i = a' • u₀ i := by
      exact add_left_cancel heqi
    have haa : a = a' := by
      by_contra hne'
      have hsub : (a - a') • u₀ i = 0 := by
        rw [sub_smul, hsmul, sub_self]
      have h0 : u₀ i = 0 := by
        have hinv := congrArg (fun x => (a - a')⁻¹ • x) hsub
        simpa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne')] using hinv
      exact hne h0
    subst haa
    have hvv : v = v' := by
      have := add_right_cancel heq
      exact this
    exact Prod.ext rfl hvv
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rwa [Finset.card_product, Finset.card_univ] at hcard

open Classical in
/-- **The double count.**  For a code with no degenerate coordinate, summing the
agreement counts of all codewords with any fixed center `w` gives at most `n·|C|/|F|`:

  `|F| · Σ_{v ∈ C} #{j : v j = w j} ≤ n · |C|`. -/
theorem card_mul_sum_agreement_le (C : Submodule F (ι → A))
    (hnd : ∀ i : ι, ∃ u ∈ C, u i ≠ 0) (w : ι → A) :
    Fintype.card F *
        ∑ v ∈ Finset.univ.filter (fun v : ι → A => v ∈ C),
          (Finset.univ.filter (fun j => v j = w j)).card
      ≤ Fintype.card ι *
          (Finset.univ.filter (fun v : ι → A => v ∈ C)).card := by
  classical
  set Cfin : Finset (ι → A) := Finset.univ.filter (fun v : ι → A => v ∈ C) with hCfin
  have hswap : ∑ v ∈ Cfin, (Finset.univ.filter (fun j => v j = w j)).card
      = ∑ j : ι, (Finset.univ.filter (fun v : ι → A => v ∈ C ∧ v j = w j)).card := by
    have h1 : ∀ v : ι → A, (Finset.univ.filter (fun j => v j = w j)).card
        = ∑ j : ι, if v j = w j then 1 else 0 := fun v => Finset.card_filter _ _
    have h2 : ∀ j : ι, (Finset.univ.filter (fun v : ι → A => v ∈ C ∧ v j = w j)).card
        = ∑ v ∈ Cfin, if v j = w j then 1 else 0 := by
      intro j
      rw [← Finset.filter_filter]
      exact (Finset.card_filter _ _)
    simp_rw [h1, h2]
    exact Finset.sum_comm
  rw [hswap, Finset.mul_sum]
  have hbound : ∀ j : ι,
      Fintype.card F *
          (Finset.univ.filter (fun v : ι → A => v ∈ C ∧ v j = w j)).card
        ≤ Cfin.card := by
    intro j
    obtain ⟨u₀, hu₀, hne⟩ := hnd j
    exact card_smul_fiber_le C hu₀ hne (w j)
  calc ∑ j : ι, Fintype.card F *
          (Finset.univ.filter (fun v : ι → A => v ∈ C ∧ v j = w j)).card
      ≤ ∑ _j : ι, Cfin.card := Finset.sum_le_sum fun j _ => hbound j
    _ = Fintype.card ι * Cfin.card := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

set_option maxHeartbeats 1000000 in
open Classical in
/-- **The far-word supply, discharged for nondegenerate linear codes.**  If every
coordinate carries a nonzero codeword value and `δ + 1/|F| < 1`, then every word has a
codeword at relative distance `> δ`.

Averaging: were every codeword `δ`-close to `w`, each would agree with `w` on
`≥ n − δn` coordinates, so `|C|·(n − δn) ≤ Σ agreements ≤ n·|C|/|F|`, forcing
`1 ≤ δ + 1/|F|`. -/
theorem farWordSupply_of_forall_exists_ne (C : Submodule F (ι → A))
    (hnd : ∀ i : ι, ∃ u ∈ C, u i ≠ 0) {δ : ℚ≥0}
    (hδ : δ + 1 / (Fintype.card F : ℚ≥0) < 1) :
    FarWordSupply (C : Set (ι → A)) δ := by
  classical
  intro w
  by_contra hcon
  push Not at hcon
  set n := Fintype.card ι with hn
  set q := Fintype.card F with hq
  set Cfin : Finset (ι → A) := Finset.univ.filter (fun v : ι → A => v ∈ C) with hCfin
  have hn0 : (0 : ℚ≥0) < (n : ℚ≥0) := by
    exact_mod_cast Fintype.card_pos
  have hq0 : (0 : ℚ≥0) < (q : ℚ≥0) := by
    exact_mod_cast Fintype.card_pos
  have hc0 : (0 : ℚ≥0) < (Cfin.card : ℚ≥0) := by
    have h0 : (0 : ι → A) ∈ Cfin :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.zero_mem⟩
    exact_mod_cast Finset.card_pos.mpr ⟨0, h0⟩
  -- per-codeword: n ≤ agreement + δ·n
  have hper : ∀ v ∈ Cfin,
      (n : ℚ≥0) ≤ ((Finset.univ.filter (fun j => v j = w j)).card : ℚ≥0) + δ * n := by
    intro v hv
    have hd : δᵣ(w, v) ≤ δ := hcon v ((Finset.mem_filter.mp hv).2)
    have hdist : ((hammingDist w v : ℕ) : ℚ≥0) ≤ δ * n := by
      have hd' : ((hammingDist w v : ℕ) : ℚ≥0) / (n : ℚ≥0) ≤ δ := hd
      calc ((hammingDist w v : ℕ) : ℚ≥0)
          = ((hammingDist w v : ℕ) : ℚ≥0) / (n : ℚ≥0) * (n : ℚ≥0) := by
            rw [div_mul_cancel₀ _ hn0.ne']
        _ ≤ δ * n := by gcongr
    have hsplit : (Finset.univ.filter (fun j => v j = w j)).card
        + hammingDist w v = n := by
      have h := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset ι)) (p := fun j => v j = w j)
      rw [Finset.card_univ] at h
      have hdeq : (Finset.univ.filter (fun j => ¬ v j = w j)).card
          = hammingDist w v := by
        rw [hammingDist]
        congr 1
        ext j
        simp [eq_comm]
      rw [hdeq] at h
      exact h
    calc (n : ℚ≥0)
        = ((Finset.univ.filter (fun j => v j = w j)).card : ℚ≥0)
            + ((hammingDist w v : ℕ) : ℚ≥0) := by exact_mod_cast hsplit.symm
      _ ≤ ((Finset.univ.filter (fun j => v j = w j)).card : ℚ≥0) + δ * n := by
          gcongr
  -- sum over the code
  have hsum : (Cfin.card : ℚ≥0) * n
      ≤ (∑ v ∈ Cfin,
            ((Finset.univ.filter (fun j => v j = w j)).card : ℚ≥0))
          + (Cfin.card : ℚ≥0) * (δ * n) := by
    have h := Finset.sum_le_sum hper
    rw [Finset.sum_const, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      nsmul_eq_mul] at h
    exact h
  -- the counting bound, cast to ℚ≥0
  have hcount : (q : ℚ≥0) *
      (∑ v ∈ Cfin,
          ((Finset.univ.filter (fun j => v j = w j)).card : ℚ≥0))
      ≤ (n : ℚ≥0) * Cfin.card := by
    have h := card_mul_sum_agreement_le C hnd w
    have hcast : ((q * ∑ v ∈ Cfin,
        (Finset.univ.filter (fun j => v j = w j)).card : ℕ) : ℚ≥0)
        ≤ ((n * Cfin.card : ℕ) : ℚ≥0) := by exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sum] at hcast
    exact hcast
  -- multiply the per-sum bound by q and chain
  have hδq : δ * q + 1 < (q : ℚ≥0) := by
    have h := mul_lt_mul_of_pos_right hδ hq0
    rwa [add_mul, one_div, inv_mul_cancel₀ hq0.ne', one_mul] at h
  have hchain : (q : ℚ≥0) * ((Cfin.card : ℚ≥0) * n)
      < (q : ℚ≥0) * ((Cfin.card : ℚ≥0) * n) := by
    calc (q : ℚ≥0) * ((Cfin.card : ℚ≥0) * n)
        ≤ (q : ℚ≥0) * ((∑ v ∈ Cfin,
              ((Finset.univ.filter (fun j => v j = w j)).card : ℚ≥0))
            + (Cfin.card : ℚ≥0) * (δ * n)) := by
          exact mul_le_mul_of_nonneg_left hsum (zero_le _)
      _ = (q : ℚ≥0) * (∑ v ∈ Cfin,
              ((Finset.univ.filter (fun j => v j = w j)).card : ℚ≥0))
            + (q : ℚ≥0) * ((Cfin.card : ℚ≥0) * (δ * n)) := by ring
      _ ≤ (n : ℚ≥0) * Cfin.card
            + (q : ℚ≥0) * ((Cfin.card : ℚ≥0) * (δ * n)) := by
          gcongr
      _ = (1 + δ * q) * ((Cfin.card : ℚ≥0) * n) := by ring
      _ < (q : ℚ≥0) * ((Cfin.card : ℚ≥0) * n) := by
          refine mul_lt_mul_of_pos_right ?_ (mul_pos hc0 hn0)
          rwa [add_comm] at hδq
  exact lt_irrefl _ hchain

/-- **Reed–Solomon codes are nondegenerate** (`k ≥ 1`): the constant codeword `1` is
nonzero at every coordinate. -/
theorem rs_exists_ne (domain : ι ↪ F) {k : ℕ} (hk : 1 ≤ k) (i : ι) :
    ∃ u ∈ ReedSolomon.code domain k, u i ≠ 0 := by
  classical
  refine ⟨ReedSolomon.evalOnPoints domain (Polynomial.C 1), ?_, ?_⟩
  · refine Submodule.mem_map.mpr ⟨Polynomial.C 1, ?_, rfl⟩
    rw [Polynomial.mem_degreeLT, Polynomial.degree_C one_ne_zero]
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  · show Polynomial.eval (domain i) (Polynomial.C 1) ≠ 0
    rw [Polynomial.eval_C]
    exact one_ne_zero

/-- **The far-word supply for Reed–Solomon codes** (`k ≥ 1`, `δ + 1/|F| < 1`):
the [Jo26] Lemma 5.4 counting input, discharged. -/
theorem farWordSupply_rs (domain : ι ↪ F) {k : ℕ} (hk : 1 ≤ k) {δ : ℚ≥0}
    (hδ : δ + 1 / (Fintype.card F : ℚ≥0) < 1) :
    FarWordSupply (ReedSolomon.code domain k : Set (ι → F)) δ :=
  farWordSupply_of_forall_exists_ne _ (rs_exists_ne domain hk) hδ

/-- **[Jo26] Theorem 5.5 for Reed–Solomon, unconditional**: curve decodability and
marked curve decodability coincide for RS codes at every `δ + 1/|F| < 1`. -/
theorem curveDecodable_iff_marked_rs (domain : ι ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {ℓ a b : ℕ} {δ : ℚ≥0} (hδ : δ + 1 / (Fintype.card F : ℚ≥0) < 1) :
    CurveDecodable F (ReedSolomon.code domain k : Set (ι → F)) ℓ δ a b ↔
      MarkedCurveDecodable F (ReedSolomon.code domain k : Set (ι → F)) ℓ δ a b :=
  curveDecodable_iff_markedCurveDecodable (farWordSupply_rs domain hk hδ)

/-- **[Jo26] Theorem 5.7 for Reed–Solomon from the original hypothesis,
unconditional**: curve decodability of an RS code transfers to every interleaving in
marked form, with the far-word input supplied by counting. -/
theorem markedCurveDecodable_interleaved_of_curveDecodable_rs (domain : ι ↪ F)
    {k : ℕ} (hk : 1 ≤ k) (ℓ : ℕ) {δ : ℚ≥0} {a b : ℕ} (s : ℕ) [NeZero s]
    (hba : b ≤ a) (hchoose : a.choose b ≤ Fintype.card F)
    (hδ : δ + 1 / (Fintype.card F : ℚ≥0) < 1)
    (hC : CurveDecodable F (ReedSolomon.code domain k : Set (ι → F)) ℓ δ a b) :
    MarkedCurveDecodable F
      ((ReedSolomon.code domain k : Set (ι → F))^⋈ (Fin s)) ℓ δ a b :=
  markedCurveDecodable_interleaved_of_curveDecodable _ ℓ δ s hba hchoose
    (farWordSupply_rs domain hk hδ) hC

/-! ## Source audit -/

#print axioms card_smul_fiber_le
#print axioms card_mul_sum_agreement_le
#print axioms farWordSupply_of_forall_exists_ne
#print axioms rs_exists_ne
#print axioms farWordSupply_rs
#print axioms curveDecodable_iff_marked_rs
#print axioms markedCurveDecodable_interleaved_of_curveDecodable_rs

end ProximityGap.CurveDec

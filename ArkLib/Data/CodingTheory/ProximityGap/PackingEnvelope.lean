/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BadFamilyCensus

/-!
# The packing law and the piecewise envelope: `2(n−t)+2` bad scalars at every radius,
# beyond `n` via the OVERLAPPING construction (#371, round 9)

Round 8 (`BadFamilyCensus.lean`) discovered the BISIMPLEX (two disjoint `(e+1)`-simplices
on one affine line, `2e+2` bad scalars) and conjectured an "overlapping" variant plus a
"k disjoint simplices" generalization.  This file lands the round-9 resolution
(probe: `scripts/probes/probe_packing_envelope.py`), which settles both:

## 1.  The k-simplex packing COLLAPSES (probe T1/T2, theorem `kPacking_subsumed`)

The "k pairwise-disjoint `(e+1)`-simplices" stack `u₁ = q₀|_{S₁}`, `u₀ = (X·q₀)|_{S₁}`
(`q₀` = vanishing polynomial of the complement `Z` of the union) is in fact a
TWO-parameter family — only `s₁ = |S₁|` and `z = |Z|` matter; the remaining `k−1` blocks
are an undifferentiated reservoir `B₂` whose every point `x` contributes the bad scalar
`γ = −x` through the codeword `(X−x)·q₀`.  Count `n − z` at threshold
`min(n−s₁+1, s₁+z+1)`; the per-radius optimum over `(s₁, z)` at threshold `t` is
attained at `z = max(0, 2t−n−2)` and equals the bisimplex value `2(n−t)+2` (capped at
`n` for this disjoint mechanism).  The k-reading has count `k(e+1) = n − z ≤ 2E+2` at
its own radius `E = (k−1)(e+1)−1` with the unified window implied (`kPacking_subsumed`)
— `k ≥ 3` NEVER appears on the envelope.  Probe T2: at `(p,n,d) = (97,16,5)`, `t = 9`,
the `k=3, e=3` stack yields exactly its `12` while the unified optimum yields `16` at
the same threshold.

## 2.  THE OVERLAPPING LAW IS REAL — the count passes `n` (probe T3, the new theorem)

The round-8 hint (`20 = 2(e+1)` at `e = 9`, heuristically observed at
`(p,n,d,t) = (97,16,2,7)` where `2e+2 > n`) is a genuine char-0 family, replicated
independently at `p = 97` AND `p = 257` with identical structure (two `(E+1)`-point
simplex blocks overlapping in `|Y| = n−2t+2` points, ZERO leftovers).  The
reverse-engineered mechanism (`overlap_packing_epsMCA_lower_bound`):

Pick `S` (`|S| = s`), an overlap part `Y ⊆ S` (`|Y| = c`), and per-point tuned scalars
`γᴷ, γᴬ` on `Y`.  Stack: on `S∖Y` the pencil pair `(X, 1)`; on `Y` the tuned values
`b_x = (γᴬ_x + x)/(γᴬ_x − γᴷ_x)`, `a_x = −γᴷ_x·b_x`; zero off `S`.  Then:

* every `x ∈ S∖Y` kills its coordinate at `γ = −x` (witness: `complement(S) ∪ {x}`
  against the ZERO codeword, forced `q₁ = 0` vs `u₁(x) = 1`);
* every `x ∉ S` aligns at `γ = −x` (witness: `(S∖Y) ∪ {x}` against the codeword
  `X + γ`, which vanishes at `x`; forced `q₁ = 1` vs `u₁(x) = 0`);
* every `x ∈ Y` contributes TWO scalars: its kill `γᴷ_x` (`a_x + γᴷ_x b_x = 0`) and its
  align `γᴬ_x` (`a_x + γᴬ_x b_x = x + γᴬ_x`), with `u₁(x) = b_x ∉ {0, 1}`.

**Count `n + c`** at threshold `min(n−s+1, s−c+1)`; at `s = n−t+1`, `c = n−2t+2` this is
**`2(n−t)+2` — the bisimplex formula UNCAPPED**, exceeding `n` at every deep radius
`2t < n+2`.  The grand packing law over both regimes:

  `W_packing(n,d,t) = 2(n−t)+2` on the whole window `d+2 ≤ t`, `2t ≤ n+d+1`

(deep regime `2t ≤ n+2` by the overlap family; shoulder regime `n+2 ≤ 2t` by the landed
bisimplex).  Word-level exact at `(12289, 16, 2)`: the concrete stacks below carry
exactly `20` bad scalars at `t = 7` and `18` at `t = 8` (probe-verified), giving the
first machine-checked beyond-`n` bad-scalar counts and the new δ* bands
`δ* ≤ 1/2` at `ε* < 18/p` and `δ* ≤ 9/16` at `ε* < 20/p` for the `d = 2` code — filling
the budget gap `[16/p, 40/p)` between the antipodal pencil and the level-1 staircase
where the best landed bound was `5/8`.

## 3.  The piecewise envelope

`envelopeFloor` packages the PROVEN per-threshold floor (packing ∪ pencil rungs ∪
simplex ladder) with `envelopeFloor_le_epsMCA` as its one-shot consumer, and
`CompleteEnvelopeConjecture` states the matching good side — the round-8/9 census
verdict that the catalogue (staircase / packing / pencil / simplex / explosion) is
COMPLETE at every radius for `p` large (the probe's exhaustive cells match the formula
at every censused `(d, t)`, the two known mod-17 surpluses excepted) — in the round-7
named-Prop convention.  The bad half is proven; the good half is the census-true
obligation.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26 Code
open ProximityGap.KKH26DeltaStarReduction
open ArkLib.ProximityGap.OwnershipCensus
open ArkLib.ProximityGap.KKH26DimGeneral
open ArkLib.ProximityGap.Level1Rung
open ArkLib.ProximityGap.BadFamilyCensus

namespace ArkLib.ProximityGap.PackingEnvelope

/-- Injectivity of `i ↦ g^i` below the order of `g` (local copy of the `private` helper
of the sibling files). -/
private lemma pow_inj_below_order'''' {F : Type*} [Field F] {h : F} (h0 : h ≠ 0) {N : ℕ}
    (hN : orderOf h = N) :
    ∀ i, i < N → ∀ j, j < N → h ^ i = h ^ j → i = j := by
  have main : ∀ i j, i ≤ j → j < N → h ^ i = h ^ j → i = j := by
    intro i j hij hj heq
    have hadd : i + (j - i) = j := by omega
    have h2 : h ^ i * h ^ (j - i) = h ^ i * 1 := by
      rw [mul_one, ← pow_add, hadd, heq]
    have h3 : h ^ (j - i) = 1 := mul_left_cancel₀ (pow_ne_zero i h0) h2
    have h4 : N ∣ j - i := hN ▸ orderOf_dvd_of_pow_eq_one h3
    have h5 : j - i = 0 :=
      Nat.eq_zero_of_dvd_of_lt h4 (lt_of_le_of_lt (Nat.sub_le j i) hj)
    omega
  intro i hi j hj heq
  rcases le_total i j with hle | hle
  · exact main i j hle hj heq
  · exact (main j i hle hi heq.symm).symm

/-! ## The k-simplex packing subsumption (the round-8 conjecture 3, REFUTED as an
envelope extension)

A "k pairwise-disjoint `(e+1)`-simplices" packing (`k ≥ 2`, footprint `k(e+1) ≤ n`,
window `n−k(e+1)+1 ≤ d`) has count `k(e+1)` at radius `E = (k−1)(e+1)−1`.  The unified
packing at the same radius counts `2E+2` with window `n ≤ d+2E+1` — and the k-packing's
parameters always satisfy the unified window with a smaller-or-equal count.  So `k ≥ 3`
packings are pointwise subsumed: the envelope never needs them. -/
theorem kPacking_subsumed {n d k e : ℕ} (hk : 2 ≤ k) (he1 : 1 ≤ e)
    (hdlo : n + 1 ≤ d + k * (e + 1)) :
    k * (e + 1) ≤ 2 * ((k - 1) * (e + 1) - 1) + 2 ∧
    n + 1 ≤ d + 2 * ((k - 1) * (e + 1) - 1) + 2 := by
  have h1 : k * (e + 1) ≤ 2 * ((k - 1) * (e + 1)) := by
    have hk2 : k ≤ 2 * (k - 1) := by omega
    calc k * (e + 1) ≤ 2 * (k - 1) * (e + 1) := Nat.mul_le_mul_right _ hk2
    _ = 2 * ((k - 1) * (e + 1)) := by ring
  have h2 : 1 ≤ (k - 1) * (e + 1) := by
    have hk1 : 1 ≤ k - 1 := by omega
    calc 1 = 1 * 1 := by ring
    _ ≤ (k - 1) * (e + 1) := Nat.mul_le_mul hk1 (by omega)
  omega

/-! ## The overlapping packing family: `n + c` bad scalars

The main theorem of the round.  The freshness of the `2c` tuned scalars is taken as
hypotheses (they are free parameters; any choice outside `−⟨g⟩` with the stated
non-collisions works, and the concrete instances below discharge them by `decide`). -/

open Classical in
/-- **The overlapping-packing lower bound**: `n + c` bad scalars at radius `1 − t/n`.

Geometry: `S = {0,…,s−1}` with overlap part `Y = {s−c,…,s−1}`, complement
`{s,…,n−1}`.  The stack is the pencil pair `(X, 1)` on `S∖Y`, the `(γᴷ, γᴬ)`-tuned
values on `Y`, and zero off `S`.  Every domain point off `Y` contributes one bad scalar
(`−x`: a kill for `x ∈ S∖Y`, a root-alignment for `x ∉ S`), and every overlap point
contributes TWO (`γᴷ_x` and `γᴬ_x`).  At `s = n−t+1`, `c = n−2t+2` the count is
`2(n−t)+2` — the bisimplex value continued past the `n` cap into the deep-radius regime
`2t ≤ n+2` (round-9 probe: char-0 real, replicated at `p ∈ {97, 257}` and word-level
exact at `p = 12289`). -/
theorem overlap_packing_epsMCA_lower_bound {p n : ℕ} [Fact p.Prime] [NeZero n]
    {d s c t : ℕ} {g : ZMod p} (hg : orderOf g = n)
    (γK γA : Fin n → ZMod p)
    (hd : 1 ≤ d) (hd1 : s + d + 1 ≤ n) (hd2 : c + d + 1 ≤ s)
    (ht1 : t + s ≤ n + 1) (ht2 : t + c ≤ s + 1)
    (hKA : ∀ x : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s → γK x ≠ γA x)
    (hKdom : ∀ x : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
      ∀ j : Fin n, γK x ≠ -(g ^ (j : ℕ)))
    (hAdom : ∀ x : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
      ∀ j : Fin n, γA x ≠ -(g ^ (j : ℕ)))
    (hKinj : ∀ x y : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
      s - c ≤ (y : ℕ) → (y : ℕ) < s → γK x = γK y → x = y)
    (hAinj : ∀ x y : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
      s - c ≤ (y : ℕ) → (y : ℕ) < s → γA x = γA y → x = y)
    (hcross : ∀ x y : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
      s - c ≤ (y : ℕ) → (y : ℕ) < s → γK x ≠ γA y) :
    ((n + c : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)
      ≤ epsMCA (F := ZMod p) (evalCode g n d)
          (1 - ((t : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) := by
  classical
  have hn0 : 0 < n := by omega
  have hcs : c ≤ s := by omega
  have hsn : s < n := by omega
  have htn : t ≤ n := by omega
  have hg0 : g ≠ 0 := by
    rintro rfl
    have h1 : (0 : ZMod p) ^ n = 1 := by
      rw [← hg]; exact pow_orderOf_eq_one 0
    rw [zero_pow (by omega : n ≠ 0)] at h1
    exact zero_ne_one h1
  have hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j := by
    intro i j hij
    exact Fin.ext (pow_inj_below_order'''' hg0 hg _ i.isLt _ j.isLt hij)
  -- the tuned values on the overlap part
  set bF : Fin n → ZMod p := fun x => (γA x + g ^ (x : ℕ)) * (γA x - γK x)⁻¹
    with hbF
  set aF : Fin n → ZMod p := fun x => -(γK x) * bF x with haF
  have hsub_ne : ∀ x : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
      γA x - γK x ≠ 0 := by
    intro x hx1 hx2
    exact sub_ne_zero.mpr (Ne.symm (hKA x hx1 hx2))
  have hb_ne0 : ∀ x : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s → bF x ≠ 0 := by
    intro x hx1 hx2
    refine mul_ne_zero ?_ (inv_ne_zero (hsub_ne x hx1 hx2))
    intro hcon
    exact hAdom x hx1 hx2 x (by linear_combination hcon)
  have hb_key : ∀ x : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
      (γA x - γK x) * bF x = γA x + g ^ (x : ℕ) := by
    intro x hx1 hx2
    have hne := hsub_ne x hx1 hx2
    simp only [hbF]
    rw [mul_comm (γA x - γK x) ((γA x + g ^ (x : ℕ)) * (γA x - γK x)⁻¹),
      mul_assoc, inv_mul_cancel₀ hne, mul_one]
  have hb_ne1 : ∀ x : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s → bF x ≠ 1 := by
    intro x hx1 hx2 hcon
    have h1 := hb_key x hx1 hx2
    rw [hcon, mul_one] at h1
    exact hKdom x hx1 hx2 x (by linear_combination -h1)
  -- the per-point line identities
  have ha_kill : ∀ x : Fin n, aF x + γK x * bF x = 0 := by
    intro x
    simp only [haF]
    ring
  have ha_align : ∀ x : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
      aF x + γA x * bF x = g ^ (x : ℕ) + γA x := by
    intro x hx1 hx2
    have hkey := hb_key x hx1 hx2
    simp only [haF]
    linear_combination hkey
  -- the stack
  set u : WordStack (ZMod p) (Fin 2) (Fin n) :=
    ![fun j => if (j : ℕ) < s - c then g ^ (j : ℕ)
        else if (j : ℕ) < s then aF j else 0,
      fun j => if (j : ℕ) < s - c then 1
        else if (j : ℕ) < s then bF j else 0] with hu
  have hu0_base : ∀ j : Fin n, (j : ℕ) < s - c → u 0 j = g ^ (j : ℕ) := by
    intro j hj
    rw [hu]
    simp [hj]
  have hu0_Y : ∀ j : Fin n, s - c ≤ (j : ℕ) → (j : ℕ) < s → u 0 j = aF j := by
    intro j hj1 hj2
    have h1 : ¬ (j : ℕ) < s - c := by omega
    rw [hu]
    simp [h1, hj2]
  have hu0_comp : ∀ j : Fin n, s ≤ (j : ℕ) → u 0 j = 0 := by
    intro j hj
    have h1 : ¬ (j : ℕ) < s - c := by omega
    have h2 : ¬ (j : ℕ) < s := by omega
    rw [hu]
    simp [h1, h2]
  have hu1_base : ∀ j : Fin n, (j : ℕ) < s - c → u 1 j = 1 := by
    intro j hj
    rw [hu]
    simp [hj]
  have hu1_Y : ∀ j : Fin n, s - c ≤ (j : ℕ) → (j : ℕ) < s → u 1 j = bF j := by
    intro j hj1 hj2
    have h1 : ¬ (j : ℕ) < s - c := by omega
    rw [hu]
    simp [h1, hj2]
  have hu1_comp : ∀ j : Fin n, s ≤ (j : ℕ) → u 1 j = 0 := by
    intro j hj
    have h1 : ¬ (j : ℕ) < s - c := by omega
    have h2 : ¬ (j : ℕ) < s := by omega
    rw [hu]
    simp [h1, h2]
  -- shared witness-size arithmetic: any witness of `≥ t` points is large enough
  have hsizeS : ∀ S : Finset (Fin n), t ≤ S.card →
      ((S.card : ℕ) : ℝ≥0) ≥ (1 - (1 - ((t : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)))
        * (Fintype.card (Fin n) : ℝ≥0) := by
    intro S hS
    have hn0' : ((n : ℕ) : ℝ≥0) ≠ 0 := by exact_mod_cast hn0.ne'
    have hle1 : ((t : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) ≤ 1 := by
      rw [div_le_one (lt_of_le_of_ne (zero_le _) (Ne.symm hn0'))]
      exact_mod_cast htn
    have h1δ : (1 : ℝ≥0) - (1 - ((t : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0))
        = ((t : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) := tsub_tsub_cancel_of_le hle1
    rw [h1δ, Fintype.card_fin, div_mul_cancel₀ _ hn0']
    exact_mod_cast hS
  -- THE KILL MECHANISM: x ∈ S, scalar killing coordinate x; witness = complement ∪ {x}
  have killCase : ∀ (x : Fin n) (γ : ZMod p), (x : ℕ) < s →
      u 0 x + γ * u 1 x = 0 → u 1 x ≠ 0 →
      mcaEvent (evalCode g n d)
        (1 - ((t : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) (u 0) (u 1) γ := by
    intro x γ hxs hkill hne
    have hflt : ∀ k : Fin (n - s), s + (k : ℕ) < n := fun k => by
      have := k.isLt
      omega
    set f : Fin (n - s) → Fin n := fun k => ⟨s + (k : ℕ), hflt k⟩ with hf
    set Scomp : Finset (Fin n) := Finset.univ.image f with hSc
    have hcomp_ge : ∀ j ∈ Scomp, s ≤ (j : ℕ) := by
      intro j hjc
      obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hjc
      subst hk
      show s ≤ s + (k : ℕ)
      omega
    have hfinj : Function.Injective f := by
      intro a b hab
      have h1 := congrArg Fin.val hab
      simp only [hf] at h1
      exact Fin.ext (by omega)
    have hScomp_card : Scomp.card = n - s := by
      rw [hSc, Finset.card_image_of_injective _ hfinj, Finset.card_univ,
        Fintype.card_fin]
    have hx_notin : x ∉ Scomp := by
      intro hmem
      have := hcomp_ge x hmem
      omega
    set S : Finset (Fin n) := insert x Scomp with hS
    have hScard : S.card = n - s + 1 := by
      rw [hS, Finset.card_insert_of_notMem hx_notin, hScomp_card]
    refine ⟨S, hsizeS S (by rw [hScard]; omega),
      ⟨fun j => (0 : Polynomial (ZMod p)).eval (g ^ (j : ℕ)),
       polyEval_mem_evalCode 0 (by simp), ?_⟩, ?_⟩
    · -- agreement with the zero codeword
      intro j hj
      simp only [Polynomial.eval_zero, smul_eq_mul]
      rcases Finset.mem_insert.mp hj with rfl | hjc
      · exact hkill.symm
      · have hge := hcomp_ge j hjc
        rw [hu0_comp j hge, hu1_comp j hge]
        ring
    · -- no joint pair: the direction vanishes on the complement but not at `x`
      rintro ⟨v₀, -, v₁, hv₁, hpair⟩
      obtain ⟨q₁, hq₁deg, hq₁⟩ := hv₁
      have hq₁zero : q₁ = 0 := by
        refine fit_unique hginj (B := Scomp) ?_ hq₁deg (by simp) fun j hjc => ?_
        · rw [hScomp_card]
          omega
        · have hge := hcomp_ge j hjc
          have h1 : v₁ j = u 1 j := (hpair j (Finset.mem_insert_of_mem hjc)).2
          have h2 : v₁ j = q₁.eval (g ^ (j : ℕ)) := hq₁ j
          rw [← h2, h1, hu1_comp j hge]
          simp
      have h4 : v₁ x = u 1 x := (hpair x (Finset.mem_insert_self _ _)).2
      have h5 : v₁ x = q₁.eval (g ^ ((x : Fin n) : ℕ)) := hq₁ x
      rw [hq₁zero] at h5
      simp only [Polynomial.eval_zero] at h5
      exact hne (by rw [← h4, h5])
  -- THE ALIGN MECHANISM: x off the base, scalar aligning with `X + γ` at x;
  -- witness = base ∪ {x}
  have alignCase : ∀ (x : Fin n) (γ : ZMod p), s - c ≤ (x : ℕ) →
      u 0 x + γ * u 1 x = g ^ (x : ℕ) + γ → u 1 x ≠ 1 →
      mcaEvent (evalCode g n d)
        (1 - ((t : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) (u 0) (u 1) γ := by
    intro x γ hxsc halign hne
    have hflt : ∀ k : Fin (s - c), (k : ℕ) < n := fun k => by
      have := k.isLt
      omega
    set f : Fin (s - c) → Fin n := fun k => ⟨(k : ℕ), hflt k⟩ with hf
    set Sbase : Finset (Fin n) := Finset.univ.image f with hSb
    have hbase_lt : ∀ j ∈ Sbase, (j : ℕ) < s - c := by
      intro j hjb
      obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hjb
      subst hk
      exact k.isLt
    have hfinj : Function.Injective f := by
      intro a b hab
      have h1 := congrArg Fin.val hab
      simp only [hf] at h1
      exact Fin.ext h1
    have hSbase_card : Sbase.card = s - c := by
      rw [hSb, Finset.card_image_of_injective _ hfinj, Finset.card_univ,
        Fintype.card_fin]
    have hx_notin : x ∉ Sbase := by
      intro hmem
      have := hbase_lt x hmem
      omega
    set S : Finset (Fin n) := insert x Sbase with hS
    have hScard : S.card = s - c + 1 := by
      rw [hS, Finset.card_insert_of_notMem hx_notin, hSbase_card]
    set qpoly : Polynomial (ZMod p) := Polynomial.X + Polynomial.C γ with hqp
    have hqdeg : qpoly.natDegree ≤ d := by
      refine le_trans (Polynomial.natDegree_add_le _ _) ?_
      simpa [Polynomial.natDegree_X, Polynomial.natDegree_C] using hd
    have hq_eval : ∀ y : ZMod p, qpoly.eval y = y + γ := by
      intro y
      rw [hqp]
      simp
    refine ⟨S, hsizeS S (by rw [hScard]; omega),
      ⟨fun j => qpoly.eval (g ^ (j : ℕ)),
       polyEval_mem_evalCode qpoly hqdeg, ?_⟩, ?_⟩
    · -- agreement with the codeword `X + γ`
      intro j hj
      show qpoly.eval (g ^ (j : ℕ)) = u 0 j + γ • u 1 j
      rw [hq_eval]
      simp only [smul_eq_mul]
      rcases Finset.mem_insert.mp hj with rfl | hjb
      · exact halign.symm
      · have hlt := hbase_lt j hjb
        rw [hu0_base j hlt, hu1_base j hlt]
        ring
    · -- no joint pair: the direction is the constant 1 on the base but not at `x`
      rintro ⟨v₀, -, v₁, hv₁, hpair⟩
      obtain ⟨q₁, hq₁deg, hq₁⟩ := hv₁
      have hq₁one : q₁ = Polynomial.C 1 := by
        refine fit_unique hginj (B := Sbase) ?_ hq₁deg (by simp) fun j hjb => ?_
        · rw [hSbase_card]
          omega
        · have hlt := hbase_lt j hjb
          have h1 : v₁ j = u 1 j := (hpair j (Finset.mem_insert_of_mem hjb)).2
          have h2 : v₁ j = q₁.eval (g ^ (j : ℕ)) := hq₁ j
          rw [← h2, h1, hu1_base j hlt]
          simp
      have h4 : v₁ x = u 1 x := (hpair x (Finset.mem_insert_self _ _)).2
      have h5 : v₁ x = q₁.eval (g ^ ((x : Fin n) : ℕ)) := hq₁ x
      rw [hq₁one] at h5
      simp only [Polynomial.eval_C] at h5
      exact hne (by rw [← h4, h5])
  -- the bad-scalar set: the skip map over the non-overlap points + the two tuned
  -- families on the overlap part
  have hσlt : ∀ i : Fin (n - c), (if (i : ℕ) < s - c then (i : ℕ)
      else (i : ℕ) + c) < n := by
    intro i
    have := i.isLt
    split <;> omega
  set σ : Fin (n - c) → Fin n := fun i => ⟨if (i : ℕ) < s - c then (i : ℕ)
    else (i : ℕ) + c, hσlt i⟩ with hσ
  have hσval : ∀ i : Fin (n - c), ((σ i : Fin n) : ℕ)
      = if (i : ℕ) < s - c then (i : ℕ) else (i : ℕ) + c := by
    intro i
    simp [hσ]
  have hσ_spec : ∀ i : Fin (n - c), ((σ i : Fin n) : ℕ) < s - c ∨
      s ≤ ((σ i : Fin n) : ℕ) := by
    intro i
    rw [hσval i]
    rcases Nat.lt_or_ge (i : ℕ) (s - c) with hi | hi
    · rw [if_pos hi]
      omega
    · rw [if_neg (by omega)]
      have := i.isLt
      omega
  have hσinj : Function.Injective σ := by
    intro i j hij
    have h1 : (if (i : ℕ) < s - c then (i : ℕ) else (i : ℕ) + c)
        = (if (j : ℕ) < s - c then (j : ℕ) else (j : ℕ) + c) := by
      rw [← hσval i, ← hσval j, hij]
    refine Fin.ext ?_
    rcases Nat.lt_or_ge (i : ℕ) (s - c) with hi | hi <;>
      rcases Nat.lt_or_ge (j : ℕ) (s - c) with hj | hj
    · rw [if_pos hi, if_pos hj] at h1
      omega
    · rw [if_pos hi, if_neg (by omega)] at h1
      omega
    · rw [if_neg (by omega), if_pos hj] at h1
      omega
    · rw [if_neg (by omega), if_neg (by omega)] at h1
      omega
  set Ywin : Finset (Fin n) :=
    Finset.univ.filter (fun x : Fin n => s - c ≤ (x : ℕ) ∧ (x : ℕ) < s) with hYw
  have hYmem : ∀ x : Fin n, x ∈ Ywin ↔ (s - c ≤ (x : ℕ) ∧ (x : ℕ) < s) := by
    intro x
    rw [hYw, Finset.mem_filter]
    simp
  have hYcard : Ywin.card = c := by
    have hYflt : ∀ k : Fin c, s - c + (k : ℕ) < n := fun k => by
      have := k.isLt
      omega
    have hinj : Function.Injective
        (fun k : Fin c => (⟨s - c + (k : ℕ), hYflt k⟩ : Fin n)) := by
      intro a b hab
      have h1 := congrArg Fin.val hab
      simp only at h1
      exact Fin.ext (by omega)
    have hset : Ywin = Finset.univ.image
        (fun k : Fin c => (⟨s - c + (k : ℕ), hYflt k⟩ : Fin n)) := by
      ext x
      rw [hYmem x]
      constructor
      · rintro ⟨h1, h2⟩
        refine Finset.mem_image.mpr ⟨⟨(x : ℕ) - (s - c), by omega⟩,
          Finset.mem_univ _, ?_⟩
        refine Fin.ext ?_
        show s - c + ((x : ℕ) - (s - c)) = (x : ℕ)
        omega
      · intro hx
        obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hx
        subst hk
        have := k.isLt
        constructor
        · show s - c ≤ s - c + (k : ℕ)
          omega
        · show s - c + (k : ℕ) < s
          omega
    rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin]
  set Dpart : Finset (ZMod p) :=
    Finset.univ.image (fun i : Fin (n - c) => -(g ^ ((σ i : Fin n) : ℕ))) with hDp
  set Kpart : Finset (ZMod p) := Ywin.image γK with hKp
  set Apart : Finset (ZMod p) := Ywin.image γA with hAp
  set Λ : Finset (ZMod p) := Dpart ∪ (Kpart ∪ Apart) with hΛ
  have hDcard : Dpart.card = n - c := by
    have hinj : Function.Injective
        (fun i : Fin (n - c) => -(g ^ ((σ i : Fin n) : ℕ))) := by
      intro i j hij
      simp only at hij
      have heq : g ^ ((σ i : Fin n) : ℕ) = g ^ ((σ j : Fin n) : ℕ) :=
        neg_injective hij
      exact hσinj (hginj _ _ heq)
    rw [hDp, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin]
  have hKcard : Kpart.card = c := by
    rw [hKp, Finset.card_image_of_injOn, hYcard]
    intro x hx y hy hxy
    obtain ⟨hx1, hx2⟩ := (hYmem x).mp (Finset.mem_coe.mp hx)
    obtain ⟨hy1, hy2⟩ := (hYmem y).mp (Finset.mem_coe.mp hy)
    exact hKinj x y hx1 hx2 hy1 hy2 hxy
  have hAcard : Apart.card = c := by
    rw [hAp, Finset.card_image_of_injOn, hYcard]
    intro x hx y hy hxy
    obtain ⟨hx1, hx2⟩ := (hYmem x).mp (Finset.mem_coe.mp hx)
    obtain ⟨hy1, hy2⟩ := (hYmem y).mp (Finset.mem_coe.mp hy)
    exact hAinj x y hx1 hx2 hy1 hy2 hxy
  have hdisjKA : Disjoint Kpart Apart := by
    rw [Finset.disjoint_left]
    intro γ hγK hγA
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp hγK
    obtain ⟨y, hy, hye⟩ := Finset.mem_image.mp hγA
    rw [hYmem] at hx hy
    exact hcross x y hx.1 hx.2 hy.1 hy.2 (by rw [hxe, hye])
  have hdisjD : Disjoint Dpart (Kpart ∪ Apart) := by
    rw [Finset.disjoint_left]
    intro γ hγD hγKA
    obtain ⟨i, -, hie⟩ := Finset.mem_image.mp hγD
    rcases Finset.mem_union.mp hγKA with hγK | hγA
    · obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp hγK
      rw [hYmem] at hx
      exact hKdom x hx.1 hx.2 (σ i) (by rw [hxe, ← hie])
    · obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp hγA
      rw [hYmem] at hx
      exact hAdom x hx.1 hx.2 (σ i) (by rw [hxe, ← hie])
  have hΛcard : Λ.card = n + c := by
    rw [hΛ, Finset.card_union_of_disjoint hdisjD,
      Finset.card_union_of_disjoint hdisjKA, hDcard, hKcard, hAcard]
    omega
  -- every scalar of Λ is bad
  have hbad : ∀ γ ∈ Λ, mcaEvent (evalCode g n d)
      (1 - ((t : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) (u 0) (u 1) γ := by
    intro γ hγ
    rcases Finset.mem_union.mp hγ with hγD | hγKA
    · -- the skip orbit: kills on the base, root-alignments on the complement
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hγD
      rcases hσ_spec i with hbase | hcomp
      · -- kill at x = σ i in the base
        refine killCase (σ i) _ (by omega) ?_ ?_
        · rw [hu0_base _ hbase, hu1_base _ hbase]
          ring
        · rw [hu1_base _ hbase]
          exact one_ne_zero
      · -- root-alignment at x = σ i in the complement
        refine alignCase (σ i) _ (by omega) ?_ ?_
        · rw [hu0_comp _ hcomp, hu1_comp _ hcomp]
          ring
        · rw [hu1_comp _ hcomp]
          exact zero_ne_one
    · rcases Finset.mem_union.mp hγKA with hγK | hγA
      · -- the tuned kill at an overlap point
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hγK
        rw [hYmem] at hx
        refine killCase x _ hx.2 ?_ ?_
        · rw [hu0_Y x hx.1 hx.2, hu1_Y x hx.1 hx.2]
          exact ha_kill x
        · rw [hu1_Y x hx.1 hx.2]
          exact hb_ne0 x hx.1 hx.2
      · -- the tuned alignment at an overlap point
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hγA
        rw [hYmem] at hx
        refine alignCase x _ hx.1 ?_ ?_
        · rw [hu0_Y x hx.1 hx.2, hu1_Y x hx.1 hx.2]
          exact ha_align x hx.1 hx.2
        · rw [hu1_Y x hx.1 hx.2]
          exact hb_ne1 x hx.1 hx.2
  -- feed the set into the in-tree engine
  have hengine := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (F := ZMod p) (evalCode g n d)
    (1 - ((t : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) u Λ hbad
  rw [ZMod.card p] at hengine
  refine le_trans ?_ hengine
  rw [hΛcard]

/-- **The overlapping-packing `δ*` upper bound**: every budget `ε* < (n+c)/p` forces
`δ* ≤ 1 − t/n`. -/
theorem mcaDeltaStar_le_overlap_packing {p n : ℕ} [Fact p.Prime] [NeZero n]
    {d s c t : ℕ} {g : ZMod p} (hg : orderOf g = n)
    (γK γA : Fin n → ZMod p)
    (hd : 1 ≤ d) (hd1 : s + d + 1 ≤ n) (hd2 : c + d + 1 ≤ s)
    (ht1 : t + s ≤ n + 1) (ht2 : t + c ≤ s + 1)
    (hKA : ∀ x : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s → γK x ≠ γA x)
    (hKdom : ∀ x : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
      ∀ j : Fin n, γK x ≠ -(g ^ (j : ℕ)))
    (hAdom : ∀ x : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
      ∀ j : Fin n, γA x ≠ -(g ^ (j : ℕ)))
    (hKinj : ∀ x y : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
      s - c ≤ (y : ℕ) → (y : ℕ) < s → γK x = γK y → x = y)
    (hAinj : ∀ x y : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
      s - c ≤ (y : ℕ) → (y : ℕ) < s → γA x = γA y → x = y)
    (hcross : ∀ x y : Fin n, s - c ≤ (x : ℕ) → (x : ℕ) < s →
      s - c ≤ (y : ℕ) → (y : ℕ) < s → γK x ≠ γA y)
    (εstar : ℝ≥0∞) (hεstar : εstar < ((n + c : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n d) εstar
      ≤ 1 - ((t : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) :=
  mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hεstar (overlap_packing_epsMCA_lower_bound hg γK γA hd hd1 hd2
      ht1 ht2 hKA hKdom hAdom hKinj hAinj hcross))

/-! ## The proven per-threshold envelope floor -/

/-- The PROVEN packing value at threshold `t`: the bisimplex `2(n−t)+2` on the shoulder
regime `n+2 ≤ 2t ≤ n+d+1`, and the overlap family's `c = 0` cap value `n` on the deep
regime `2t ≤ n+1` (the full `2(n−t)+2` deep value needs the `2c` fresh tuned scalars —
provided by `overlap_packing_epsMCA_lower_bound` under explicit freshness, as in the
concrete instances; this def keeps the unconditional floor). -/
def provedPackingCount (n d t : ℕ) : ℕ :=
  if d + 2 ≤ t ∧ n + 2 ≤ 2 * t ∧ 2 * t ≤ n + d + 1 then 2 * (n - t) + 2
  else if 1 ≤ d ∧ 2 * t ≤ n + 1 ∧ 2 * d + 2 ≤ n ∧ t + d ≤ n then n
  else 0

/-- The pencil-rung value at threshold `t = n/2 + s` (`s ∣ n/2`, `s ≤ d`). -/
def pencilRungCount (n d t : ℕ) : ℕ :=
  if n % 2 = 0 ∧ n / 2 < t ∧ (t - n / 2) ∣ (n / 2) ∧ t - n / 2 ≤ d ∧ d + 1 ≤ n / 2
  then n / (t - n / 2) else 0

/-- The simplex-ladder value at threshold `t` (`e = n − t ≥ 1`). -/
def simplexLadderCount (n d t : ℕ) : ℕ :=
  if d + 2 ≤ t ∧ t + 1 ≤ n then n - t + 1 else 0

/-- The proven per-threshold envelope floor: the maximum of the three proven families. -/
def envelopeFloor (n d t : ℕ) : ℕ :=
  max (provedPackingCount n d t) (max (pencilRungCount n d t) (simplexLadderCount n d t))

/-- The proven packing floor is a lower bound for `ε_mca` at radius `1 − t/n`. -/
theorem provedPacking_le_epsMCA {p n : ℕ} [Fact p.Prime] [NeZero n] {d t : ℕ}
    {g : ZMod p} (hg : orderOf g = n) :
    ((provedPackingCount n d t : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)
      ≤ epsMCA (F := ZMod p) (evalCode g n d)
          (1 - ((t : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) := by
  rw [provedPackingCount]
  split_ifs with h1 h2
  · -- shoulder regime: the bisimplex at `e = n − t`
    obtain ⟨hdt, hlo, hhi⟩ := h1
    have h := bisimplex_epsMCA_lower_bound (p := p) (n := n) (d := d) (e := n - t)
      (g := g) hg (by omega) (by omega) (by omega) (by omega)
    have he : n - (n - t) = t := by omega
    rw [he] at h
    exact h
  · -- deep regime: the overlap family at `c = 0`, `s = max (d+1) (t−1)`
    obtain ⟨hd, hcap, hdn, htd⟩ := h2
    have h := overlap_packing_epsMCA_lower_bound (p := p) (n := n) (d := d)
      (s := max (d + 1) (t - 1)) (c := 0) (t := t) (g := g) hg
      (fun _ => 0) (fun _ => 0) hd
      (by omega) (by omega) (by omega) (by omega)
      (fun x hx1 hx2 => absurd (lt_of_le_of_lt hx1 hx2) (by omega))
      (fun x hx1 hx2 => absurd (lt_of_le_of_lt hx1 hx2) (by omega))
      (fun x hx1 hx2 => absurd (lt_of_le_of_lt hx1 hx2) (by omega))
      (fun x y hx1 hx2 _ _ _ => absurd (lt_of_le_of_lt hx1 hx2) (by omega))
      (fun x y hx1 hx2 _ _ _ => absurd (lt_of_le_of_lt hx1 hx2) (by omega))
      (fun x y hx1 hx2 _ _ => absurd (lt_of_le_of_lt hx1 hx2) (by omega))
    simpa using h
  · simp

/-- The pencil-rung floor is a lower bound for `ε_mca` at radius `1 − t/n`. -/
theorem pencilRung_le_epsMCA {p n : ℕ} [Fact p.Prime] [NeZero n] {d t : ℕ}
    {g : ZMod p} (hg : orderOf g = n) :
    ((pencilRungCount n d t : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)
      ≤ epsMCA (F := ZMod p) (evalCode g n d)
          (1 - ((t : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) := by
  rw [pencilRungCount]
  split_ifs with h1
  · obtain ⟨hpar, hht, hdvd, hsd, hdh⟩ := h1
    have h := pencil_rung_epsMCA_lower_bound (p := p) (n := n) (h := n / 2)
      (d := d) (s := t - n / 2) (by omega) (by omega) (g := g) hg
      (by omega) hdvd hsd hdh
    have he : n / 2 + (t - n / 2) = t := by omega
    rw [he] at h
    exact h
  · simp

/-- The simplex-ladder floor is a lower bound for `ε_mca` at radius `1 − t/n`. -/
theorem simplexLadder_le_epsMCA {p n : ℕ} [Fact p.Prime] [NeZero n] {d t : ℕ}
    {g : ZMod p} (hg : orderOf g = n) :
    ((simplexLadderCount n d t : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)
      ≤ epsMCA (F := ZMod p) (evalCode g n d)
          (1 - ((t : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) := by
  rw [simplexLadderCount]
  split_ifs with h1
  · obtain ⟨hdt, htn⟩ := h1
    have h := simplex_epsMCA_lower_bound (p := p) (n := n) (d := d) (e := n - t)
      (g := g) hg (by omega) (by omega)
    have he : n - (n - t) = t := by omega
    rw [he] at h
    have hc : (((n - t) + 1 : ℕ) : ℝ≥0∞) = ((n - t + 1 : ℕ) : ℝ≥0∞) := rfl
    rw [hc] at h
    exact h
  · simp

/-- **The proven envelope floor, one-shot consumer**: at every threshold `t`, the
maximum of the proven catalogue families bounds `ε_mca` from below at radius
`1 − t/n`.  (The conjectural good side — that this max together with the staircase
and explosion terms is EXACT for large `p` — is `CompleteEnvelopeConjecture`.) -/
theorem envelopeFloor_le_epsMCA {p n : ℕ} [Fact p.Prime] [NeZero n] {d t : ℕ}
    {g : ZMod p} (hg : orderOf g = n) :
    ((envelopeFloor n d t : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)
      ≤ epsMCA (F := ZMod p) (evalCode g n d)
          (1 - ((t : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) := by
  rw [envelopeFloor]
  rcases max_choice (provedPackingCount n d t)
    (max (pencilRungCount n d t) (simplexLadderCount n d t)) with hm | hm <;> rw [hm]
  · exact provedPacking_le_epsMCA hg
  · rcases max_choice (pencilRungCount n d t) (simplexLadderCount n d t) with
      hm2 | hm2 <;> rw [hm2]
    · exact pencilRung_le_epsMCA hg
    · exact simplexLadder_le_epsMCA hg

/-! ## The complete-envelope conjecture (general form)

The good side of the two-layer census law.  `spectrumKKH26` is the exact subset-sum
spectrum count of the level-`j` staircase family (`N(ν, r)` of the round-8 probes,
matching `TwoPowerSubsetSumSpectrum`); `fullCatalogueCount` assembles the conjectured
complete per-threshold catalogue: explosion (`t ≤ d+2`), staircase, FULL packing law
(`2(n−t)+2` on its whole window, beyond-`n` included), pencil rungs, and the simplex
ladder. -/

/-- The 2-power subset-sum spectrum count `N(ν, r) = Σ_{a ≡ r (2), r ≤ 2h−a} 2^a·C(h,a)`
with `h = 2^(ν−1)`. -/
def spectrumKKH26 (ν r : ℕ) : ℕ :=
  ∑ a ∈ Finset.range (r + 1),
    if a % 2 = r % 2 ∧ r ≤ 2 * 2 ^ (ν - 1) - a then 2 ^ a * Nat.choose (2 ^ (ν - 1)) a
    else 0

/-- The staircase contribution at threshold `t` for the 2-power domain `n = 2^μ`:
the level-`j` family fires at threshold `r'_j·2^j ≥ t` with `r'_j = d/2^j + 2`. -/
def staircaseCount (μ d t : ℕ) : ℕ :=
  Finset.sup (Finset.range μ) fun j =>
    if d / 2 ^ j + 2 ≤ 2 ^ (μ - j - 1) ∧ t ≤ (d / 2 ^ j + 2) * 2 ^ j
    then spectrumKKH26 (μ - j) (d / 2 ^ j + 2) else 0

/-- The FULL packing law (conjecture side): `2(n−t)+2` on the whole window
`d+2 ≤ t`, `2t ≤ n+d+1` — beyond `n` in the deep regime via the overlap family. -/
def packingLawCount (n d t : ℕ) : ℕ :=
  if d + 2 ≤ t ∧ 2 * t ≤ n + d + 1 then 2 * (n - t) + 2 else 0

/-- The conjectured complete per-threshold catalogue value at `n = 2^μ`. -/
def fullCatalogueCount (p μ d t : ℕ) : ℕ :=
  if t ≤ d + 2 then p
  else max (packingLawCount (2 ^ μ) d t)
    (max (pencilRungCount (2 ^ μ) d t)
      (max (simplexLadderCount (2 ^ μ) d t) (staircaseCount μ d t)))

/-- **THE COMPLETE-ENVELOPE CONJECTURE** (the round-9 upgrade of the round-8
`CompleteEnvelopeF17`): for every 2-power smooth domain and degree bound, for all
sufficiently large primes, `ε_mca` at radius `1 − t/n` is bounded by the catalogue
envelope `fullCatalogueCount / p` at every threshold `t` — i.e. the catalogue
(explosion / staircase / packing `2(n−t)+2` / pencil rungs / simplex ladder) is the
COMPLETE list of char-0 bad families, so `δ*(ε*)` equals the maximal radius at which
the envelope count exceeds `ε*·p`.

Status: TRUE at every exhaustively censused cell (`(17,8)` for `d ∈ {1,2,3}`, all
thresholds; `(97,8)` at the `d = 3` shoulder cell), with the proven bad sides
(`envelopeFloor_le_epsMCA`, `overlap_packing_epsMCA_lower_bound`,
`bisimplex_epsMCA_lower_bound`, the staircase spectrum theorems) matching it from
below.  The `∃ p₀` guard is essential: at small `p` the censused mod-`p` surpluses
(`+3` at `(17,8,2), t=5`; `+1` at `(17,8,3), t=6`) exceed the char-0 envelope. -/
def CompleteEnvelopeConjecture : Prop :=
  ∀ μ d : ℕ, 2 ≤ μ → 1 ≤ d → ∃ p₀ : ℕ, ∀ p : ℕ, ∀ _ : Fact p.Prime, p₀ ≤ p →
    ∀ g : ZMod p, orderOf g = 2 ^ μ → ∀ t : ℕ, d + 2 ≤ t → t ≤ 2 ^ μ →
      epsMCA (F := ZMod p) (evalCode g (2 ^ μ) d)
          (1 - ((t : ℕ) : ℝ≥0) / ((2 ^ μ : ℕ) : ℝ≥0))
        ≤ ((fullCatalogueCount p μ d t : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)

/-! ## The concrete beyond-`n` instances at the deployed-shape code
(`p = 12289`, `n = 16`, `d = 2`)

The tuned scalars `{2,…,9}` avoid `−⟨4134⟩ = ⟨4134⟩` (the 16th roots of unity mod
12289), so the freshness hypotheses are decidable facts.  Word-level probe-exact:
the `t = 7` stack carries exactly `20` bad scalars and the `t = 8` stack exactly
`18`. -/

section Concrete12289

local instance fact_prime_12289'''' : Fact (Nat.Prime 12289) := ⟨by norm_num⟩

/-- The tuned kill scalars of the `t = 7` instance (`Y = {6,7,8,9}`). -/
private def γK20 : Fin 16 → ZMod 12289 :=
  ![0, 0, 0, 0, 0, 0, 2, 3, 4, 5, 0, 0, 0, 0, 0, 0]

/-- The tuned align scalars of the `t = 7` instance. -/
private def γA20 : Fin 16 → ZMod 12289 :=
  ![0, 0, 0, 0, 0, 0, 6, 7, 8, 9, 0, 0, 0, 0, 0, 0]

/-- **TWENTY bad scalars at radius `9/16`** for the `d = 2` code — the first
machine-checked beyond-`n` count (`20 > n = 16`): the overlap family at
`s = 10`, `c = 4`, `t = 7`. -/
theorem overlap20_epsMCA_F12289_d2 :
    (20 : ℝ≥0∞) / (12289 : ℝ≥0∞)
      ≤ epsMCA (F := ZMod 12289) (evalCode (4134 : ZMod 12289) 16 2) (9 / 16 : ℝ≥0) := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  have h := overlap_packing_epsMCA_lower_bound (p := 12289) (n := 16) (d := 2)
    (s := 10) (c := 4) (t := 7) (g := (4134 : ZMod 12289)) orderOf_4134
    γK20 γA20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e1 : ((16 + 4 : ℕ) : ℝ≥0∞) = (20 : ℝ≥0∞) := by norm_num
  have e2 : ((12289 : ℕ) : ℝ≥0∞) = (12289 : ℝ≥0∞) := by norm_num
  have e3 : (1 : ℝ≥0) - ((7 : ℕ) : ℝ≥0) / ((16 : ℕ) : ℝ≥0) = 9 / 16 := by
    have hd : ((7 : ℕ) : ℝ≥0) / ((16 : ℕ) : ℝ≥0) = 7 / 16 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e1, e2, e3] at h
  exact h

/-- The new `δ*` band: every budget `ε* < 20/p` forces `δ* ≤ 9/16` — beating the
landed `5/8` (level-1 staircase, `ε* < 40/p`) on the band `[16/p, 20/p)` where the
antipodal pencil (`16` scalars) no longer bites. -/
theorem deltaStar_le_overlap20_F12289_d2 (εstar : ℝ≥0∞)
    (hεstar : εstar < (20 : ℝ≥0∞) / (12289 : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod 12289) (A := ZMod 12289)
      (evalCode (4134 : ZMod 12289) 16 2) εstar ≤ 9 / 16 :=
  mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le hεstar overlap20_epsMCA_F12289_d2)

/-- The tuned kill scalars of the `t = 8` instance (`Y = {7,8}`). -/
private def γK18 : Fin 16 → ZMod 12289 :=
  ![0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0]

/-- The tuned align scalars of the `t = 8` instance. -/
private def γA18 : Fin 16 → ZMod 12289 :=
  ![0, 0, 0, 0, 0, 0, 0, 4, 5, 0, 0, 0, 0, 0, 0, 0]

/-- **EIGHTEEN bad scalars at radius `1/2`** for the `d = 2` code (`s = 9`, `c = 2`,
`t = 8`) — also beyond `n`. -/
theorem overlap18_epsMCA_F12289_d2 :
    (18 : ℝ≥0∞) / (12289 : ℝ≥0∞)
      ≤ epsMCA (F := ZMod 12289) (evalCode (4134 : ZMod 12289) 16 2) (1 / 2 : ℝ≥0) := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  have h := overlap_packing_epsMCA_lower_bound (p := 12289) (n := 16) (d := 2)
    (s := 9) (c := 2) (t := 8) (g := (4134 : ZMod 12289)) orderOf_4134
    γK18 γA18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e1 : ((16 + 2 : ℕ) : ℝ≥0∞) = (18 : ℝ≥0∞) := by norm_num
  have e2 : ((12289 : ℕ) : ℝ≥0∞) = (12289 : ℝ≥0∞) := by norm_num
  have e3 : (1 : ℝ≥0) - ((8 : ℕ) : ℝ≥0) / ((16 : ℕ) : ℝ≥0) = 1 / 2 := by
    have hd : ((8 : ℕ) : ℝ≥0) / ((16 : ℕ) : ℝ≥0) = 1 / 2 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e1, e2, e3] at h
  exact h

/-- The new `δ*` band: every budget `ε* < 18/p` forces `δ* ≤ 1/2`.  With
`overlap20` and the landed pencil bands, the `d = 2` budget curve now reads
`δ* ≤ 7/16` on `ε* < 16/p` · `≤ 1/2` on `[16/p, 18/p)` · `≤ 9/16` on `[18/p, 20/p)`
· `≤ 5/8` on `[20/p, 40/p)` (staircase). -/
theorem deltaStar_le_overlap18_F12289_d2 (εstar : ℝ≥0∞)
    (hεstar : εstar < (18 : ℝ≥0∞) / (12289 : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod 12289) (A := ZMod 12289)
      (evalCode (4134 : ZMod 12289) 16 2) εstar ≤ 1 / 2 :=
  mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le hεstar overlap18_epsMCA_F12289_d2)

end Concrete12289

end ArkLib.ProximityGap.PackingEnvelope

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.PackingEnvelope.kPacking_subsumed
#print axioms ArkLib.ProximityGap.PackingEnvelope.overlap_packing_epsMCA_lower_bound
#print axioms ArkLib.ProximityGap.PackingEnvelope.mcaDeltaStar_le_overlap_packing
#print axioms ArkLib.ProximityGap.PackingEnvelope.provedPacking_le_epsMCA
#print axioms ArkLib.ProximityGap.PackingEnvelope.pencilRung_le_epsMCA
#print axioms ArkLib.ProximityGap.PackingEnvelope.simplexLadder_le_epsMCA
#print axioms ArkLib.ProximityGap.PackingEnvelope.envelopeFloor_le_epsMCA
#print axioms ArkLib.ProximityGap.PackingEnvelope.overlap20_epsMCA_F12289_d2
#print axioms ArkLib.ProximityGap.PackingEnvelope.deltaStar_le_overlap20_F12289_d2
#print axioms ArkLib.ProximityGap.PackingEnvelope.overlap18_epsMCA_F12289_d2
#print axioms ArkLib.ProximityGap.PackingEnvelope.deltaStar_le_overlap18_F12289_d2

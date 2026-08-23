/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound
import ArkLib.Data.CodingTheory.ProximityGap.ValueSpreadSecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.QuotientDeepCore
import ArkLib.Data.CodingTheory.ProximityGap.SmoothFiberCount

/-!
# Theorem Q assembled in-tree: the per-prime lower half as an `epsMCA` statement

`theoremQ_epsMCA_lower` — for any finite field with a full set `H` of `n`-th roots of unity
(`|H| = n = s·m`), any `2 ≤ r ≤ s`, `k = (r−1)·m`, any `δ` with `(1−δ)·n ≤ r·m`, and field
size `q > n + k`: some `B` with `C(s,r)·(q−n) ≤ B·((q−n) + C(s,r)·k)` satisfies
`epsMCA(evalCode H k, δ) ≥ B/q`, exhibited by an explicit deep-quotient line. Numerically
`B ≳ ½·min(C(s,r), (q−n)/k)`, beating `2^{−128}·q` throughout `2^{129} ≤ q < 2^{127}·C(s,r)`
— every prime, every 2-power gap, the whole prize window (the lower half of the Grand MCA
determination; mathematics from [KKH ePrint 2026/782 App. A] + [CS25] + [BCHKS25 §6] +
[BCIKS20]; see `QuotientPerPrimeInstantiation.md`).

Composes the three verified bricks: `ValueSpreadSecondMoment` (the z-selection second
moment), `QuotientDeepCore` (far side, DEEP divisibility, quotient degree, bad-scalar
agreement), `SmoothFiberCount` (the exact `m`-to-1 fiber count), into the in-tree
`epsMCA` framework (`MCALowerBound.epsMCA_eq_iSup_badCount_div`).

Statement-fidelity notes (review record): the statement strengthens the markdown note in
four sound directions (any finite field; `r ≤ s`; any admissible `δ`; no 2-power
hypothesis on `n, s` — the root-of-unity hypotheses carry the structure), and its closed
form `C(s,r)(q−n)/((q−n)+C(s,r)k)/q` is strictly sharper than the note's
`(½min(C, q/k) − n)/q` at the top window edge. The hypothesis `q > n + k` is harmless:
below it the note's bound is vacuous.

Verification provenance: proved and axiom-audited (`[propext, Classical.choice,
Quot.sound]`, zero warnings) as a single concatenated translation unit against built
oleans (`lake env lean`); committed in import form with identical content.
-/

/-! ### The assembly: Theorem Q as an in-tree `epsMCA` lower bound -/

set_option autoImplicit false

namespace ArkLib.ProximityGap.TheoremQAssembly

open Polynomial _root_.ProximityGap _root_.Code
open scoped NNReal ENNReal BigOperators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The evaluation code of polynomials of degree `< k` on the subtype domain of `H`. -/
def evalCode (H : Finset F) (k : ℕ) : Set ({x : F // x ∈ H} → F) :=
  {f | ∃ p : F[X], p.natDegree < k ∧ ∀ i, f i = p.eval i.1}

omit [Field F] [Fintype F] [DecidableEq F] in
/-- Filtering the subtype universe by a predicate on the underlying element has the same
cardinality as filtering `H` itself. -/
private lemma card_filter_subtype (H : Finset F) (P : F → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x : {x : F // x ∈ H} => P x.1).card = (H.filter P).card := by
  classical
  refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
  · intro a ha
    rcases Finset.mem_filter.mp ha with ⟨-, hP⟩
    exact Finset.mem_filter.mpr ⟨a.2, hP⟩
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro b hb
    rcases Finset.mem_filter.mp hb with ⟨hbH, hP⟩
    exact ⟨⟨b, hbH⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩, rfl⟩

omit [Fintype F] in
/-- Root-count helper: a set of field elements on which a nonzero polynomial vanishes has at
most `natDegree` elements. -/
private lemma card_le_natDegree_of_roots (D : Finset F) (P : F[X]) (hP : P ≠ 0)
    (h : ∀ x ∈ D, P.eval x = 0) : D.card ≤ P.natDegree := by
  classical
  have hsub : D ⊆ P.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hP]
    exact h x hx
  calc D.card ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := P.card_roots'

/-- Division-free monotonicity of the spread bound in the domain size: if
`c·a ≤ b·(a + d)` and `a' ≤ a` (with `0 < a + d`), then `c·a' ≤ b·(a' + d)`. -/
private lemma spread_mono {a a' b c d : ℕ} (ha : a' ≤ a) (had : 0 < a + d)
    (h : c * a ≤ b * (a + d)) : c * a' ≤ b * (a' + d) := by
  have h1 : c * a' * a ≤ b * (a + d) * a' := by
    calc c * a' * a = a' * (c * a) := by ring
      _ ≤ a' * (b * (a + d)) := Nat.mul_le_mul_left _ h
      _ = b * (a + d) * a' := by ring
  have hca' : c * a' ≤ b * (a + d) :=
    le_trans (Nat.mul_le_mul_left _ ha) h
  have h2 : c * a' * d ≤ b * d * (a + d) := by
    calc c * a' * d ≤ b * (a + d) * d := Nat.mul_le_mul_right _ hca'
      _ = b * d * (a + d) := by ring
  have key : c * a' * (a + d) ≤ b * (a' + d) * (a + d) := by
    calc c * a' * (a + d) = c * a' * a + c * a' * d := by ring
      _ ≤ b * (a + d) * a' + b * d * (a + d) := Nat.add_le_add h1 h2
      _ = b * (a' + d) * (a + d) := by ring
  exact Nat.le_of_mul_le_mul_right key had

omit [Fintype F] [DecidableEq F] in
/-- The vanishing-polynomial map is injective on finsets. -/
private lemma prod_X_sub_C_inj {S S' : Finset F}
    (h : (∏ a ∈ S, (X - C a) : F[X]) = ∏ a ∈ S', (X - C a)) : S = S' := by
  classical
  have hroots := congrArg Polynomial.roots h
  rw [roots_prod_X_sub_C, roots_prod_X_sub_C] at hroots
  exact Finset.val_injective hroots

omit [Fintype F] [DecidableEq F] in
/-- The difference of two tail polynomials, composed with `X^m`: nonzero of degree `≤ (r−1)m`
whenever the underlying `r`-sets differ. -/
private lemma diff_poly_spec {S S' : Finset F} (hSS' : S ≠ S')
    (r m : ℕ) (hm : 1 ≤ m) (hScard : S.card = r) (hS'card : S'.card = r) :
    ((∏ a ∈ S', (X - C a) : F[X]) - ∏ a ∈ S, (X - C a)).comp ((X : F[X]) ^ m) ≠ 0 ∧
    (((∏ a ∈ S', (X - C a) : F[X]) - ∏ a ∈ S, (X - C a)).comp ((X : F[X]) ^ m)).natDegree
      ≤ (r - 1) * m := by
  classical
  have hdne : ((∏ a ∈ S', (X - C a) : F[X]) - ∏ a ∈ S, (X - C a)) ≠ 0 := by
    intro h0
    exact hSS' (prod_X_sub_C_inj (sub_eq_zero.mp h0)).symm
  constructor
  · intro h0
    rcases (comp_eq_zero_iff).mp h0 with h | ⟨-, hXc⟩
    · exact hdne h
    · have := congrArg Polynomial.natDegree hXc
      rw [natDegree_X_pow, natDegree_C] at this
      omega
  · have hdeg_d : ((∏ a ∈ S', (X - C a) : F[X]) - ∏ a ∈ S, (X - C a)).natDegree ≤ r - 1 := by
      have hrw : (∏ a ∈ S', (X - C a) : F[X]) - ∏ a ∈ S, (X - C a)
          = ((X : F[X]) ^ S.card - ∏ a ∈ S, (X - C a))
            - ((X : F[X]) ^ S'.card - ∏ a ∈ S', (X - C a)) := by
        rw [hScard, hS'card]
        ring
      rw [hrw]
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (ArkLib.ProximityGap.QuotientCore.tail_natDegree_le S).trans (by rw [hScard])
      · exact (ArkLib.ProximityGap.QuotientCore.tail_natDegree_le S').trans (by rw [hS'card])
    refine natDegree_comp_le.trans ?_
    rw [natDegree_X_pow]
    exact Nat.mul_le_mul_right _ hdeg_d

/-- **Theorem Q, assembled in-tree** (the per-prime lower half of the Grand MCA determination;
`QuotientPerPrimeInstantiation.md`, DISPROOF_LOG "the lower half closes"; mathematics from
[KKH ePrint 2026/782 App. A] + [CS25] + [BCHKS25 §6] + [BCIKS20]).

`H` a full set of `n`-th roots of unity (`|H| = n = s·m`), `2 ≤ r ≤ s`, `k := (r−1)·m`,
`δ` with `(1−δ)·n ≤ r·m`, field size `q > n + k`. Then some `B` with the value-spread bound
`C(s,r)·(q−n) ≤ B·((q−n) + C(s,r)·k)` satisfies `epsMCA(evalCode H k, δ) ≥ B/q` — exhibited by
an explicit deep-quotient line. (Numerically `B ≳ ½·min(C(s,r), (q−n)/k)`, which beats
`2^{−128}·q` throughout `2^129 ≤ q < 2^{127}·C(s,r)`: every prime, every 2-power gap, the whole
prize window.) -/
theorem theoremQ_epsMCA_lower
    (H : Finset F) [Nonempty {x : F // x ∈ H}] (n s m r : ℕ)
    (hroots : ∀ x ∈ H, x ^ n = 1) (hcard : H.card = n)
    (hnsm : n = s * m) (hm : 1 ≤ m) (hr : 2 ≤ r) (hrs : r ≤ s)
    (hbig : n + (r - 1) * m < Fintype.card F)
    (δ : ℝ≥0)
    (hδ₁ : (1 - δ) * ((Fintype.card {x : F // x ∈ H} : ℕ) : ℝ≥0) ≤ ((r * m : ℕ) : ℝ≥0)) :
    ∃ B : ℕ,
      Nat.choose s r * (Fintype.card F - n)
          ≤ B * ((Fintype.card F - n) + Nat.choose s r * ((r - 1) * m)) ∧
      (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
          ≤ epsMCA (F := F) (A := F) (evalCode H ((r - 1) * m)) δ := by
  classical
  set k := (r - 1) * m with hk
  set q := Fintype.card F with hq
  have hs : 1 ≤ s := le_trans (by omega) hrs
  have hk1 : 1 ≤ k := by
    have h1 : 1 ≤ r - 1 := by omega
    calc 1 = 1 * 1 := rfl
      _ ≤ (r - 1) * m := Nat.mul_le_mul h1 hm
  have hn1 : 1 ≤ n := by
    rw [hnsm]
    calc 1 = 1 * 1 := rfl
      _ ≤ s * m := Nat.mul_le_mul hs hm
  have hcard_ι : Fintype.card {x : F // x ∈ H} = n := by
    rw [Fintype.card_coe, hcard]
  -- ## the image domain G, with exact fiber structure
  set G := H.image (fun x => x ^ m) with hG
  have hGsub : G ⊆ H.image (fun x => x ^ m) := by
    intro x hx
    rwa [hG] at hx
  obtain ⟨himg_eq, -⟩ :=
    ArkLib.ProximityGap.SmoothFiberCount.image_pow_eq_nthRoots H hroots hcard hnsm hs hm
  have hGcard : G.card = s := by
    have hpre := ArkLib.ProximityGap.SmoothFiberCount.preimage_card_eq H hroots hcard hnsm hs hm
      G hGsub
    have hall : H.filter (fun x => x ^ m ∈ G) = H :=
      Finset.filter_true_of_mem fun x hx => Finset.mem_image_of_mem _ hx
    rw [hall, hcard, hnsm] at hpre
    have hms : m * G.card = m * s := by
      rw [← hpre, Nat.mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hm hms
  -- ## the punctured evaluation domain for z-selection
  have hXn_ne : ((X : F[X]) ^ n - C 1) ≠ 0 := by
    intro hz
    have hdeg := natDegree_X_pow_sub_C (n := n) (r := (1 : F))
    rw [hz] at hdeg
    simp only [natDegree_zero] at hdeg
    omega
  set T := Finset.univ.filter (fun z : F => z ^ n = 1) with hT
  have hT_le : T.card ≤ n := by
    refine (card_le_natDegree_of_roots T _ hXn_ne (fun x hx => ?_)).trans ?_
    · rcases Finset.mem_filter.mp hx with ⟨-, hx1⟩
      simp [hx1]
    · rw [natDegree_X_pow_sub_C]
  have hZcard : Fintype.card {z : F // ¬ z ^ n = 1} = q - T.card := by
    rw [Fintype.card_subtype]
    have hcompl : Finset.univ.filter (fun z : F => ¬ z ^ n = 1) = Tᶜ := by
      ext z
      simp [hT]
    rw [hcompl, Finset.card_compl, hT, hq]
  have hZ_ge : q - n ≤ Fintype.card {z : F // ¬ z ^ n = 1} := by
    rw [hZcard]
    omega
  haveI hZne : Nonempty {z : F // ¬ z ^ n = 1} := by
    rw [← Fintype.card_pos_iff, hZcard]
    omega
  -- ## the value family on the punctured domain
  set cfun : Finset F → ({z : F // ¬ z ^ n = 1} → F) := fun S =>
    fun z => z.1 ^ (r * m) - (∏ a ∈ S, (X - C a)).eval (z.1 ^ m) with hcfun
  have hagree_pair : ∀ S ∈ G.powersetCard r, ∀ S' ∈ G.powersetCard r, S ≠ S' →
      (Finset.univ.filter fun z : {z : F // ¬ z ^ n = 1} => cfun S z = cfun S' z).card
        ≤ k := by
    intro S hS S' hS' hne
    have hScard := (Finset.mem_powersetCard.mp hS).2
    have hS'card := (Finset.mem_powersetCard.mp hS').2
    obtain ⟨hPne, hPdeg⟩ := diff_poly_spec hne r m hm hScard hS'card
    have hsub : ((Finset.univ.filter
        fun z : {z : F // ¬ z ^ n = 1} => cfun S z = cfun S' z).image
          fun z => z.1) ⊆
        (((∏ a ∈ S', (X - C a) : F[X]) - ∏ a ∈ S, (X - C a)).comp
          ((X : F[X]) ^ m)).roots.toFinset := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
      rcases Finset.mem_filter.mp hz with ⟨-, hzz⟩
      rw [Multiset.mem_toFinset, mem_roots hPne]
      have h' : (∏ a ∈ S, (X - C a) : F[X]).eval (z.1 ^ m)
          = (∏ a ∈ S', (X - C a)).eval (z.1 ^ m) := by
        have hzz' := hzz
        simp only [hcfun] at hzz'
        exact sub_right_inj.mp hzz'
      simp only [IsRoot, eval_comp, eval_pow, eval_X, eval_sub]
      rw [← h', sub_self]
    have himg_card : (Finset.univ.filter
        fun z : {z : F // ¬ z ^ n = 1} => cfun S z = cfun S' z).card
          = ((Finset.univ.filter
        fun z : {z : F // ¬ z ^ n = 1} => cfun S z = cfun S' z).image fun z => z.1).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    calc (Finset.univ.filter fun z : {z : F // ¬ z ^ n = 1} => cfun S z = cfun S' z).card
        = _ := himg_card
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ Multiset.card (((∏ a ∈ S', (X - C a) : F[X]) - ∏ a ∈ S, (X - C a)).comp
            ((X : F[X]) ^ m)).roots := Multiset.toFinset_card_le _
      _ ≤ _ := Polynomial.card_roots' _
      _ ≤ k := hPdeg
  -- ## the family's cardinality
  set 𝓛 : Finset ({z : F // ¬ z ^ n = 1} → F) := (G.powersetCard r).image cfun with h𝓛
  have hcfun_injOn : ∀ S ∈ G.powersetCard r, ∀ S' ∈ G.powersetCard r,
      cfun S = cfun S' → S = S' := by
    intro S hS S' hS' heq
    by_contra hne
    have hag := hagree_pair S hS S' hS' hne
    have hall : (Finset.univ.filter
        fun z : {z : F // ¬ z ^ n = 1} => cfun S z = cfun S' z) = Finset.univ :=
      Finset.filter_true_of_mem fun z _ => congrFun heq z
    rw [hall, Finset.card_univ] at hag
    have := hZ_ge
    omega
  have h𝓛card : 𝓛.card = Nat.choose s r := by
    rw [h𝓛, Finset.card_image_of_injOn hcfun_injOn, Finset.card_powersetCard, hGcard]
  -- ## value spread: select the good point z₀
  have hA𝓛 : ∀ f ∈ 𝓛, ∀ g ∈ 𝓛, f ≠ g →
      (Finset.univ.filter fun z : {z : F // ¬ z ^ n = 1} => f z = g z).card ≤ k := by
    intro f hf g hg hfg
    rcases Finset.mem_image.mp hf with ⟨S, hS, rfl⟩
    rcases Finset.mem_image.mp hg with ⟨S', hS', rfl⟩
    exact hagree_pair S hS S' hS' (fun h => hfg (h ▸ rfl))
  obtain ⟨z₀, hz₀⟩ :=
    ArkLib.ProximityGap.ValueSpread.exists_eval_image_spread 𝓛 k hA𝓛
  set Λ := 𝓛.image (fun f => f z₀) with hΛ
  refine ⟨Λ.card, ?_, ?_⟩
  · -- the spread bound, transferred from |Z| down to q − n
    rw [h𝓛card] at hz₀
    have had : 0 < Fintype.card {z : F // ¬ z ^ n = 1} + Nat.choose s r * k := by
      have := hZ_ge
      have : 0 < Fintype.card {z : F // ¬ z ^ n = 1} := Fintype.card_pos
      omega
    exact spread_mono hZ_ge had hz₀
  · -- ## the deep-quotient line and its Λ.card bad scalars
    set w : F := z₀.1 ^ m with hw
    have hxw : ∀ x : {x : F // x ∈ H}, x.1 ^ m - w ≠ 0 := by
      intro x hzero
      have hxG : x.1 ^ m ∈ G := Finset.mem_image_of_mem _ x.2
      have hxw_eq : x.1 ^ m = w := by
        have := sub_eq_zero.mp hzero
        exact this
      have hwG : w ∈ G := hxw_eq ▸ hxG
      have hsne : ((X : F[X]) ^ s - 1) ≠ 0 := by
        intro hzz
        have hdeg := natDegree_X_pow_sub_C (n := s) (r := (1 : F))
        rw [C_1] at hdeg
        rw [hzz] at hdeg
        simp only [natDegree_zero] at hdeg
        omega
      rw [hG, himg_eq, Multiset.mem_toFinset, mem_roots hsne] at hwG
      have hws : w ^ s = 1 := by
        simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_one] at hwG
        exact sub_eq_zero.mp hwG
      refine z₀.2 ?_
      calc z₀.1 ^ n = (z₀.1 ^ m) ^ s := by rw [← pow_mul, mul_comm m s, ← hnsm]
        _ = w ^ s := by rw [← hw]
        _ = 1 := hws
    -- ## the two words of the deep-quotient line
    set u₀ : {x : F // x ∈ H} → F := fun x => x.1 ^ (r * m) / (x.1 ^ m - w) with hu₀
    set u₁ : {x : F // x ∈ H} → F := fun x => 1 / (x.1 ^ m - w) with hu₁
    -- every value of the family at z₀ yields a bad scalar
    have hbad : ∀ v ∈ Λ, mcaEvent (F := F) (A := F) (evalCode H k) δ u₀ u₁ (-v) := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨f, hf, rfl⟩
      rcases Finset.mem_image.mp hf with ⟨S, hSmem, rfl⟩
      obtain ⟨hSG, hScard⟩ := Finset.mem_powersetCard.mp hSmem
      obtain ⟨qp, hqp⟩ := ArkLib.ProximityGap.QuotientCore.quotient_exists
        ((X : F[X]) ^ S.card - ∏ a ∈ S, (X - C a)) w m
      have hqdeg : qp.natDegree < k := by
        have h1 := ArkLib.ProximityGap.QuotientCore.quotient_natDegree_le
          (p := (X : F[X]) ^ S.card - ∏ a ∈ S, (X - C a)) (q := qp) (w := w) (m := m) (r := r)
          hm (by omega)
          ((ArkLib.ProximityGap.QuotientCore.tail_natDegree_le S).trans (by rw [hScard])) hqp
        have h2 : (r - 2) * m + m = k := by
          have h3 : r - 1 = (r - 2) + 1 := by omega
          rw [hk, h3, Nat.add_mul, one_mul]
        omega
      have hveq : cfun S z₀ = ((X : F[X]) ^ S.card - ∏ a ∈ S, (X - C a)).eval w := by
        simp only [hcfun, eval_sub, eval_pow, eval_X, hw, hScard]
        rw [← pow_mul, mul_comm m r]
      set Sfin := Finset.univ.filter (fun x : {x : F // x ∈ H} => x.1 ^ m ∈ S) with hSfin
      have hSfin_card : Sfin.card = m * r := by
        have h2 := ArkLib.ProximityGap.SmoothFiberCount.preimage_card_eq H hroots hcard hnsm
          hs hm S (hSG.trans hGsub)
        rw [hScard] at h2
        rw [← h2]
        exact card_filter_subtype H fun y => y ^ m ∈ S
      refine ⟨Sfin, ?_, ⟨fun x => qp.eval x.1, ⟨qp, hqdeg, fun i => rfl⟩, ?_⟩, ?_⟩
      · -- the agreement set is large enough
        rw [ge_iff_le, hSfin_card, Nat.mul_comm m r]
        exact hδ₁
      · -- the quotient polynomial matches the line on the fiber
        intro x hx
        rcases Finset.mem_filter.mp hx with ⟨-, hxS⟩
        have hD := hxw x
        have hkey := ArkLib.ProximityGap.QuotientCore.quotient_agree
          (S := S) (q := qp) (w := w) (m := m) hqp hxS
        simp only [hu₀, hu₁, smul_eq_mul, mul_one_div]
        rw [← add_div, eq_div_iff hD, hkey, hveq, hScard]
        ring
      · -- no joint pair: the second row would invert x^m − w on too many points
        rintro ⟨v₀, hv₀, v₁, ⟨p₁, hp₁deg, hp₁⟩, hagree⟩
        have hall : ∀ x ∈ H.filter (fun x => x ^ m ∈ S), p₁.eval x * (x ^ m - w) = 1 := by
          intro x hxD
          rcases Finset.mem_filter.mp hxD with ⟨hxH, hxS⟩
          have hD' : x ^ m - w ≠ 0 := hxw ⟨x, hxH⟩
          have hx' : (⟨x, hxH⟩ : {x : F // x ∈ H}) ∈ Sfin := by
            rw [hSfin]
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxS⟩
          have h2 := (hagree _ hx').2
          have hval : p₁.eval x = 1 / (x ^ m - w) := by
            calc p₁.eval x = v₁ ⟨x, hxH⟩ := (hp₁ ⟨x, hxH⟩).symm
              _ = u₁ ⟨x, hxH⟩ := h2
              _ = 1 / (x ^ m - w) := by simp only [hu₁]
          rw [hval]
          exact one_div_mul_cancel hD'
        have hfar := ArkLib.ProximityGap.QuotientCore.farness_card_le
          (m := m) (H.filter (fun x => x ^ m ∈ S)) w hk1 hm p₁ hp₁deg
        have hfull : (H.filter (fun x => x ^ m ∈ S)).filter
            (fun x => p₁.eval x * (x ^ m - w) = 1) = H.filter (fun x => x ^ m ∈ S) :=
          Finset.filter_true_of_mem hall
        rw [hfull] at hfar
        have hDcard : (H.filter (fun x => x ^ m ∈ S)).card = m * r := by
          rw [ArkLib.ProximityGap.SmoothFiberCount.preimage_card_eq H hroots hcard hnsm hs hm S
            (hSG.trans hGsub), hScard]
        rw [hDcard] at hfar
        have hmr : m * r = (r - 1) * m + m := by
          have h3 : r = (r - 1) + 1 := by omega
          calc m * r = r * m := Nat.mul_comm m r
            _ = ((r - 1) + 1) * m := by rw [← h3]
            _ = (r - 1) * m + m := by rw [Nat.add_mul, one_mul]
        omega
    -- ## count the bad scalars and transfer through the closed form
    have hcount : Λ.card ≤ (Finset.univ.filter
        (fun γ : F => mcaEvent (F := F) (A := F) (evalCode H k) δ u₀ u₁ γ)).card :=
      Finset.card_le_card_of_injOn (fun v => -v)
        (fun v hv => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad v hv⟩)
        (fun a _ b _ h => neg_injective h)
    rw [epsMCA_eq_iSup_badCount_div, hq]
    refine ENNReal.div_le_div_right ?_ _
    refine le_trans ?_ (le_iSup (fun u : WordStack F (Fin 2) {x : F // x ∈ H} =>
      ((Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F) (A := F) (evalCode H k) δ (u 0) (u 1) γ)).card : ℝ≥0∞))
      (![u₀, u₁]))
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact_mod_cast hcount

end ArkLib.ProximityGap.TheoremQAssembly

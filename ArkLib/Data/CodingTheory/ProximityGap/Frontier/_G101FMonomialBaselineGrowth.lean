/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G92SpreadExcessProbe

/-!
# G101F: the monomial-baseline growth law at Johnson-boundary cells (#466)

Successor lane to `_G92SpreadExcessProbe.lean`.  G92's kill surface
(`not_spreadExcessLaw_of_floor_beats`) refutes `SpreadExcessLaw C` at any window cell where
`C · monoBaseline < n − (a−1)`, and its probe read the search value `worst_mono = 6` at the
cell `n = 32, k = 4, a = 11` as evidence that monomial baselines **collapse to `O(1)`** near
the Johnson boundary — which would kill the law at every constant `C` (the G92 ledger entry
ends: "the surviving open question is the monomial-baseline growth law at boundary cells").

**This lane's answer: the collapse premise is FALSE.  Monomial baselines provably grow.**

## The generalized pencil floor (the new mechanism)

G92's elevated-agreement floor `worstBad_ge_of_agree_pred` is the `z = a − 1` case of a
one-parameter family.  For ANY codeword `h` agreeing with the direction `u₁` on a set `Z` of
size `z`, split the off-agreement coordinates into `B` disjoint blocks of size `a − z` and give
block `r` its own scalar `γ_r`: the single explicit offset

  `u₀ = h  on Z`,  `u₀ = h − γ_r·(u₁ − h)  on block r`

makes every `γ_r` bad, witnessed by the codeword `(1 + γ_r)·h` (agreement `Z ∪ block r`, size
`≥ a`).  Hence (`worstBad_ge_of_pencil_blocks`, `worstBad_ge_pencil_div`):

  `worstBad dom k a u₁  ≥  (n − z) / (a − z)`.

Combined with Lagrange interpolation (any direction admits a codeword with agreement `≥ k`)
this gives the **universal far-direction floor** (`worstBad_ge_div_of_far`): every `a`-far
direction has `worstBad ≥ (n−k)/(a−k)`, so (`monoBaseline_ge_div_universal`)

  `monoBaseline dom k a  ≥  (n − k) / (a − k)`   at every cell `k < a ≤ n`,

which is `≈ √(n/k)` at the Johnson boundary `a ≈ √(nk)` — **growth, not collapse**
(`monoBaseline_gt_of_window_room` packages the "no `O(1)` bound survives" reading).

## The gcd boost on smooth domains, and the G92 correction

On a multiplicative domain `dom = (ω^l)_l` with `orderOf ω = n`, the constant codeword `1`
agrees with the monomial direction `x^j` exactly on the subgroup `{l : n ∣ l·j}` of size
`gcd(j, n)` — a `z` far larger than `k`.  At G92's kill cell `n = 32, k = 4, a = 11` the
direction `x^8` (far by pure degree count, `4 ≤ 8 < 11`) has `z = 8`, so

  `monoBaseline ≥ (32 − 8)/(11 − 8) = 8`   (`monoBaseline_ge_eight_g92cell`).

Consequences (the honest correction to the G92 ledger entry):

1. the planned certification `monoBaseline ≤ 7` at that cell is **impossible**
   (`no_le_seven_certificate_g92cell`);
2. the G92 refutation socket can **never fire at `C = 3`** on a μ₃₂ domain at `(k,a) = (4,11)`:
   the strongest floor is `n − (a−1) = 22 < 24 ≤ 3·monoBaseline`
   (`floor_socket_blocked_c3_g92cell`, `g92_kill_route_c3_impossible`);
3. the "C = 3 refuted in evidence" headline of G92 is thereby weakened: with the true baseline
   `≥ 8`, the in-evidence ratio at its violation cell drops to `23/8 = 2.875 < 3` unless the
   spread side is pushed past `24` (probe stage 2s below: it was not, at symmetric effort).

Forward cells are pinned the same way: `monoBaseline ≥ 7` at the exact-boundary cell
`n = 64, k = 4, a = 16` and `≥ 18` at `n = 64, k = 2, a = 11`
(`monoBaseline_ge_seven_boundary64`, `monoBaseline_ge_eighteen_n64k2`).

## Probe (part A — `scripts/probes/probe_g101f_monomial_baseline.py`)

* Stage 1 (certified, every claimed bad `γ` verified by explicit witness): pencil floors across
  `n ∈ {16,…,256}`, `k ∈ {2,4}`, all window levels.  At the boundary `a* = ⌊√(nk)⌋` the
  certified floor grows with endpoint-fitted exponent `θ ≈ 0.43` (`k=2`) / `θ ≈ 0.58` (`k=4`)
  — `θ ≈ 1/2` with power-of-two wobble, matching `(n−z)/(a−z) ≈ 2√(n/k)`.
* Stage 2 (search above the floor): pencil-seeded symmetric search; at `n=16,k=4,a=7` the true
  baseline (search `9–10`) exceeds the pencil floor `4`, so the pencil is a floor, not a
  formula.  Stage 3: EXACT `worstBad` (coset-exhaustive over `u₀` mod `span{1,…,x^{k−1},u₁}`)
  at the boundary cell `n=8,k=2,q=17,a=4`.  Outputs: `scripts/probes/_out_g101f_s*.txt`.

## What is NOT proven (honest scope)

No upper bound on `monoBaseline` is proved here (the far cap `C(n,a)` of G92 remains the only
one), so this file neither kills nor saves `SpreadExcessLaw C`: it proves the specific kill
ROUTE G92 proposed (O(1)-baseline certification at boundary cells) is closed at the probed and
forward cells, and replaces the collapse conjecture by a certified growth law from below.
Whether some constant `C` survives now hinges on upper-bounding `worstBad` of spread directions
against these growing baselines — open.  The pencil floor is generic in the direction; nothing
here is specific to monomials except the gcd computation of `z`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ProximityGap.Frontier.G101FMonomialBaselineGrowth

open ProximityGap.SpikeFloor ProximityGap.Ownership ProximityGap.Frontier.SpreadExcess
open ProximityGap.Frontier.G92SpreadExcessProbe

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## Disjoint block extraction (combinatorial helper) -/

/-- A finset of size `≥ B·t` contains `B` pairwise disjoint subsets of size `≥ t`. -/
theorem exists_disjoint_blocks {α : Type} [DecidableEq α] :
    ∀ (B : ℕ) (W : Finset α) (t : ℕ), B * t ≤ W.card →
      ∃ T : Fin B → Finset α,
        (∀ r, T r ⊆ W) ∧ (∀ r, t ≤ (T r).card) ∧
        ∀ r s, r ≠ s → Disjoint (T r) (T s) := by
  intro B
  induction B with
  | zero =>
    intro W t _
    exact ⟨fun r => r.elim0, fun r => r.elim0, fun r => r.elim0, fun r => r.elim0⟩
  | succ B ih =>
    intro W t hcard
    have ht : t ≤ W.card := by
      have h1 : t ≤ (B + 1) * t := Nat.le_mul_of_pos_left t (Nat.succ_pos B)
      exact le_trans h1 hcard
    obtain ⟨T0, hT0W, hT0card⟩ := Finset.exists_subset_card_eq ht
    have hrest : B * t ≤ (W \ T0).card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hT0W, hT0card]
      have hmul : (B + 1) * t = B * t + t := by ring
      omega
    obtain ⟨T', hT'W, hT'card, hT'disj⟩ := ih (W \ T0) t hrest
    refine ⟨fun r => if hr : (r : ℕ) < B then T' ⟨r, hr⟩ else T0, ?_, ?_, ?_⟩
    · intro r
      by_cases hr : (r : ℕ) < B
      · simpa only [dif_pos hr] using (hT'W _).trans Finset.sdiff_subset
      · simpa only [dif_neg hr] using hT0W
    · intro r
      by_cases hr : (r : ℕ) < B
      · simpa only [dif_pos hr] using hT'card _
      · simp only [dif_neg hr]
        exact hT0card.ge
    · intro r s hrs
      by_cases hr : (r : ℕ) < B <;> by_cases hs : (s : ℕ) < B
      · simp only [dif_pos hr, dif_pos hs]
        refine hT'disj _ _ fun he => hrs ?_
        simp only [Fin.mk.injEq] at he
        exact Fin.ext he
      · simp only [dif_pos hr, dif_neg hs]
        exact Finset.sdiff_disjoint.mono_left (hT'W _)
      · simp only [dif_neg hr, dif_pos hs]
        exact (Finset.sdiff_disjoint.mono_left (hT'W _)).symm
      · have h1 := r.isLt
        have h2 := s.isLt
        exact absurd (Fin.ext (by omega : (r : ℕ) = (s : ℕ))) hrs

/-! ## The generalized pencil floor -/

/-- **The generalized pencil floor, block form.**  Given a codeword `h`, pairwise disjoint
blocks `T r` off the agreement set of `h` with the direction, each completing the agreement
set to size `≥ a`, and pairwise distinct scalars `γ r`, the single explicit offset
`u₀ = h − γ_r·(u₁ − h)` on block `r` (and `= h` elsewhere) makes every `γ r` bad — witnessed
by the codeword `(1 + γ_r)·h`.  G92's `worstBad_ge_of_agree_pred` is the case of singleton
blocks at `z = a − 1`. -/
theorem worstBad_ge_of_pencil_blocks (dom : Fin n ↪ F) {k a : ℕ} {h u₁ : Fin n → F}
    (hcode : h ∈ (rsCode dom k : Submodule F (Fin n → F)))
    {B : ℕ} (T : Fin B → Finset (Fin n)) (γ : Fin B → F)
    (hγ : Function.Injective γ)
    (hdisj : ∀ r s, r ≠ s → Disjoint (T r) (T s))
    (hTZ : ∀ r, Disjoint (T r) (agreeSet h u₁))
    (hcard : ∀ r, a ≤ (agreeSet h u₁).card + (T r).card) :
    B ≤ worstBad dom k a u₁ := by
  classical
  set u₀ : Fin n → F :=
    fun i => if hri : ∃ r, i ∈ T r then h i - γ hri.choose • (u₁ i - h i) else h i
    with hu₀def
  have hchoose : ∀ (i : Fin n) (r : Fin B), i ∈ T r → ∀ (hex : ∃ s, i ∈ T s),
      hex.choose = r := by
    intro i r hir hex
    by_contra hne
    exact (Finset.disjoint_left.mp (hdisj _ _ hne) hex.choose_spec) hir
  have hmem : ∀ r : Fin B, γ r ∈ SpreadExcess.lineBadScalars dom k a u₀ u₁ := by
    intro r
    simp only [SpreadExcess.lineBadScalars, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun i => (1 + γ r) * h i, ?_, ?_⟩
    · have hmem' := Submodule.smul_mem _ (1 + γ r) hcode
      have hfn : (fun i => (1 + γ r) * h i) = (1 + γ r) • h := by
        funext i
        simp
      rw [hfn]
      exact hmem'
    · have hsub : agreeSet h u₁ ∪ T r
          ⊆ agreeSet (fun i => (1 + γ r) * h i) (fun i => u₀ i + γ r • u₁ i) := by
        intro i hi
        simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and, smul_eq_mul]
        rcases Finset.mem_union.mp hi with hiZ | hiT
        · have hhi : h i = u₁ i := by
            simpa only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and] using hiZ
          have hnT : ¬ ∃ s, i ∈ T s := by
            rintro ⟨s, hs⟩
            exact (Finset.disjoint_left.mp (hTZ s) hs) hiZ
          have hu0 : u₀ i = h i := by
            simp only [hu₀def, dif_neg hnT]
          rw [hu0, ← hhi]
          ring
        · have hex : ∃ s, i ∈ T s := ⟨r, hiT⟩
          have hu0 : u₀ i = h i - γ r * (u₁ i - h i) := by
            simp only [hu₀def, dif_pos hex, hchoose i r hiT hex, smul_eq_mul]
          rw [hu0]
          ring
      have hcards : a ≤ (agreeSet h u₁ ∪ T r).card := by
        rw [Finset.card_union_of_disjoint (hTZ r).symm]
        exact hcard r
      exact le_trans hcards (Finset.card_le_card hsub)
  have hcount : B ≤ (SpreadExcess.lineBadScalars dom k a u₀ u₁).card := by
    have hinj := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin B)))
      (t := SpreadExcess.lineBadScalars dom k a u₀ u₁) γ (fun r _ => hmem r) hγ.injOn
    simpa using hinj
  unfold worstBad
  exact le_trans hcount
    (Finset.le_sup (f := fun u₀ => (SpreadExcess.lineBadScalars dom k a u₀ u₁).card)
      (Finset.mem_univ u₀))

/-- **The generalized pencil floor, division form.**  Any codeword `h` with agreement set of
size `z < a` forces `worstBad ≥ ⌊(n − z)/(a − z)⌋`.  No farness or window hypothesis; the
field is automatically large enough because the domain embeds into it. -/
theorem worstBad_ge_pencil_div (dom : Fin n ↪ F) {k a : ℕ} {h u₁ : Fin n → F}
    (hcode : h ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hza : (agreeSet h u₁).card < a) :
    (n - (agreeSet h u₁).card) / (a - (agreeSet h u₁).card) ≤ worstBad dom k a u₁ := by
  classical
  set z : ℕ := (agreeSet h u₁).card with hz
  set B : ℕ := (n - z) / (a - z) with hB
  have hWcard : B * (a - z) ≤ ((agreeSet h u₁)ᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin, ← hz]
    exact Nat.div_mul_le_self _ _
  obtain ⟨T, hTW, hTcard, hTdisj⟩ :=
    exists_disjoint_blocks B ((agreeSet h u₁)ᶜ) (a - z) hWcard
  have hBF : B ≤ Fintype.card F := by
    calc B ≤ n - z := Nat.div_le_self _ _
      _ ≤ n := Nat.sub_le _ _
      _ = Fintype.card (Fin n) := (Fintype.card_fin n).symm
      _ ≤ Fintype.card F := Fintype.card_le_of_injective dom dom.injective
  obtain ⟨e⟩ : Nonempty (Fin B ↪ F) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hBF)
  refine worstBad_ge_of_pencil_blocks dom hcode T e e.injective hTdisj ?_ ?_
  · intro r
    exact Finset.disjoint_left.mpr fun x hx hxZ => (Finset.mem_compl.mp (hTW r hx)) hxZ
  · intro r
    have h1 := hTcard r
    omega

/-! ## The universal far-direction floor (Lagrange interpolation supplies the core) -/

/-- Every direction admits a codeword agreeing with it on at least `k` coordinates:
interpolate it through any `k` domain points. -/
theorem exists_codeword_agree_card_ge (dom : Fin n ↪ F) {k : ℕ} (hkn : k ≤ n)
    (u₁ : Fin n → F) :
    ∃ h ∈ (rsCode dom k : Submodule F (Fin n → F)), k ≤ (agreeSet h u₁).card := by
  classical
  obtain ⟨S, -, hScard⟩ := Finset.exists_subset_card_eq
    (show k ≤ (Finset.univ : Finset (Fin n)).card by
      rw [Finset.card_univ, Fintype.card_fin]; exact hkn)
  refine ⟨fun i => (Lagrange.interpolate S (⇑dom) u₁).eval (dom i),
    ⟨Lagrange.interpolate S (⇑dom) u₁, ?_, rfl⟩, ?_⟩
  · rw [← hScard]
    exact_mod_cast Lagrange.degree_interpolate_lt _ dom.injective.injOn
  · have hsub : S ⊆ agreeSet (fun i => (Lagrange.interpolate S (⇑dom) u₁).eval (dom i)) u₁ := by
      intro i hi
      simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Lagrange.eval_interpolate_at_node _ dom.injective.injOn hi
    calc k = S.card := hScard.symm
      _ ≤ _ := Finset.card_le_card hsub

/-- The pencil value `(n − z)/(a − z)` is monotone in the core size `z` (for `z < a ≤ n`),
so the worst core (`z = k`) still gives a floor. -/
theorem pencil_div_mono {n a k z : ℕ} (hkz : k ≤ z) (hza : z < a) (han : a ≤ n) :
    (n - k) / (a - k) ≤ (n - z) / (a - z) := by
  have hak : 0 < a - k := by omega
  have haz : 0 < a - z := by omega
  rw [Nat.le_div_iff_mul_le haz]
  have h1 : (n - k) / (a - k) * (a - k) ≤ n - k := Nat.div_mul_le_self _ _
  have h2 : 1 ≤ (n - k) / (a - k) := (Nat.one_le_div_iff hak).mpr (by omega)
  have h3 : (n - k) / (a - k) * (a - z) + (n - k) / (a - k) * (z - k)
      = (n - k) / (a - k) * (a - k) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have h4 : z - k ≤ (n - k) / (a - k) * (z - k) := Nat.le_mul_of_pos_left _ h2
  omega

/-- **The universal far-direction floor.**  EVERY `a`-far direction (monomial, spread, or
otherwise) has `worstBad ≥ ⌊(n − k)/(a − k)⌋` — approximately `n/a`, i.e. `√(n/k)` at the
Johnson boundary.  Farness is used only to keep the interpolation core below `a`. -/
theorem worstBad_ge_div_of_far (dom : Fin n ↪ F) {k a : ℕ} {u₁ : Fin n → F}
    (hka : k < a) (han : a ≤ n) (hfar : FarDirection dom k a u₁) :
    (n - k) / (a - k) ≤ worstBad dom k a u₁ := by
  obtain ⟨h, hcode, hzk⟩ := exists_codeword_agree_card_ge dom (le_trans hka.le han) u₁
  have hza : (agreeSet h u₁).card < a := hfar h hcode
  exact le_trans (pencil_div_mono hzk hza han) (worstBad_ge_pencil_div dom hcode hza)

/-! ## Transport to the monomial baseline -/

/-- A far monomial's `worstBad` is a lower bound for the baseline (sup entry). -/
theorem le_monoBaseline_of_far (dom : Fin n ↪ F) {k a j : ℕ} (hjn : j < n)
    (hfar : FarDirection dom k a (monoDir dom j)) :
    worstBad dom k a (monoDir dom j) ≤ monoBaseline dom k a := by
  classical
  have hval : ((⟨j, hjn⟩ : Fin n) : ℕ) = j := rfl
  rw [← hval] at hfar ⊢
  unfold monoBaseline
  exact Finset.le_sup (f := fun jm : Fin n => worstBad dom k a (monoDir dom (jm : ℕ)))
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfar⟩)

/-- **The gcd-boosted baseline floor.**  Any codeword agreeing with a far monomial `x^j`
(`k ≤ j < a`, farness automatic by degree count) on `z < a` points pushes the monomial
baseline up to `⌊(n − z)/(a − z)⌋`. -/
theorem monoBaseline_ge_pencil_div (dom : Fin n ↪ F) {k a j : ℕ}
    (hkj : k ≤ j) (hja : j < a) (hjn : j < n) {h : Fin n → F}
    (hcode : h ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hza : (agreeSet h (monoDir dom j)).card < a) :
    (n - (agreeSet h (monoDir dom j)).card) / (a - (agreeSet h (monoDir dom j)).card)
      ≤ monoBaseline dom k a :=
  le_trans (worstBad_ge_pencil_div dom hcode hza)
    (le_monoBaseline_of_far dom hjn (farDirection_monoDir dom hkj hja))

/-- **The universal baseline growth law.**  At EVERY cell `k < a ≤ n` (in particular every
window cell) the monomial baseline is at least `⌊(n − k)/(a − k)⌋ ≈ n/a`.  At the Johnson
boundary `a ≈ √(nk)` this is `≈ √(n/k)`: the G92 collapse premise ("monomial baselines are
`O(1)` at boundary cells") is false at every scale. -/
theorem monoBaseline_ge_div_universal (dom : Fin n ↪ F) {k a : ℕ}
    (hka : k < a) (han : a ≤ n) :
    (n - k) / (a - k) ≤ monoBaseline dom k a := by
  have hkn : k < n := lt_of_lt_of_le hka han
  have hfar : FarDirection dom k a (monoDir dom k) := farDirection_monoDir dom le_rfl hka
  exact le_trans (worstBad_ge_div_of_far dom hka han hfar)
    (le_monoBaseline_of_far dom hkn hfar)

/-- **No constant bound survives the window.**  Any cell with room `(M+1)·(a−k) ≤ n−k`
(available at every fixed `k` for `n` large along the boundary) puts the baseline above `M`:
a "certify `monoBaseline ≤ M` at large boundary cells" strategy is impossible for every
fixed `M`. -/
theorem monoBaseline_gt_of_window_room (dom : Fin n ↪ F) {k a M : ℕ}
    (hka : k < a) (han : a ≤ n) (hroom : (M + 1) * (a - k) ≤ n - k) :
    M < monoBaseline dom k a := by
  have h1 : M + 1 ≤ (n - k) / (a - k) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    exact hroom
  have h2 := monoBaseline_ge_div_universal dom hka han
  omega

/-! ## Smooth (multiplicative subgroup) domains: the gcd core -/

/-- The multiplicative domain `l ↦ ω^l` of an element of exact order `n`. -/
def powDom (ω : F) (hn : orderOf ω = n) : Fin n ↪ F :=
  ⟨fun l => ω ^ (l : ℕ), fun l₁ l₂ hl => by
    refine Fin.ext (pow_injOn_Iio_orderOf ?_ ?_ hl)
    · exact Set.mem_Iio.mpr (by rw [hn]; exact l₁.isLt)
    · exact Set.mem_Iio.mpr (by rw [hn]; exact l₂.isLt)⟩

/-- On a multiplicative domain, the agreement set of the constant codeword `1 = x^0` with the
monomial direction `x^j` is the subgroup `{l : n ∣ l·j}` — size `gcd(j, n)`, far above the
generic interpolation core `k`. -/
theorem agreeSet_one_monoDir (ω : F) (hn : orderOf ω = n) (j : ℕ) :
    agreeSet (monoDir (powDom ω hn) 0) (monoDir (powDom ω hn) j)
      = Finset.univ.filter (fun l : Fin n => n ∣ (l : ℕ) * j) := by
  ext i
  simp only [agreeSet, monoDir, powDom, Function.Embedding.coeFn_mk, Finset.mem_filter,
    Finset.mem_univ, true_and, pow_zero, ← pow_mul]
  rw [eq_comm, ← orderOf_dvd_iff_pow_eq_one, hn]

/-! ## The G92 kill cell `n = 32, k = 4, a = 11`: the correction -/

/-- At `n = 32`, the constant codeword agrees with `x^8` on exactly the `8` multiples of `4`. -/
theorem card_agree_x8_mu32 (ω : F) (hn : orderOf ω = 32) :
    (agreeSet (monoDir (powDom ω hn) 0) (monoDir (powDom ω hn) 8)).card = 8 := by
  rw [agreeSet_one_monoDir ω hn 8]
  decide

/-- **The G92 correction.**  At the probed kill cell `n = 32, k = 4, a = 11` (window:
`6 ≤ 11`, `121 ≤ 128`), the monomial baseline on every μ₃₂ domain is at least
`(32 − 8)/(11 − 8) = 8` — G92's search value `6` was an artifact of search effort, not a
collapse. -/
theorem monoBaseline_ge_eight_g92cell (ω : F) (hn : orderOf ω = 32) :
    8 ≤ monoBaseline (powDom ω hn) 4 11 := by
  have hcode : monoDir (powDom ω hn) 0
      ∈ (rsCode (powDom ω hn) 4 : Submodule F (Fin 32 → F)) :=
    monoDir_mem_rsCode _ (by norm_num)
  have hcard := card_agree_x8_mu32 ω hn
  have h := monoBaseline_ge_pencil_div (powDom ω hn) (k := 4) (a := 11) (j := 8)
    (by norm_num) (by norm_num) (by norm_num) hcode (by rw [hcard]; norm_num)
  rw [hcard] at h
  norm_num at h
  exact h

/-- The certification step G92 proposed for its `C = 3` kill ("needs only
`monoBaseline ≤ 7` certified") is **impossible** on every μ₃₂ domain. -/
theorem no_le_seven_certificate_g92cell (ω : F) (hn : orderOf ω = 32) :
    ¬ (monoBaseline (powDom ω hn) 4 11 ≤ 7) := by
  have h8 := monoBaseline_ge_eight_g92cell ω hn
  omega

/-- **The floor socket is blocked at `C = 3` on the G92 cell.**  For every elevated-agreement
witness set `S` with `S.card + 1 = a = 11`, the kill condition
`3·monoBaseline < 32 − S.card` of `not_spreadExcessLaw_of_floor_beats` fails:
`32 − 10 = 22 < 24 ≤ 3·monoBaseline`. -/
theorem floor_socket_blocked_c3_g92cell (ω : F) (hn : orderOf ω = 32)
    (S : Finset (Fin 32)) (hS : S.card + 1 = 11) :
    ¬ (3 * monoBaseline (powDom ω hn) 4 11 < 32 - S.card) := by
  have h8 := monoBaseline_ge_eight_g92cell ω hn
  omega

/-- Consumer-shaped form: G92's refutation socket
(`not_spreadExcessLaw_of_floor_beats` at `C = 3`) can never fire at the cell
`n = 32, k = 4, a = 11` on a μ₃₂ domain, whatever spread direction and agreement witness are
offered — its `hgt` hypothesis is unsatisfiable. -/
theorem g92_kill_route_c3_impossible (ω : F) (hn : orderOf ω = 32)
    {j j' : ℕ} {c : F} {h : Fin 32 → F}
    (hS : (agreeSet h (spread2Dir (powDom ω hn) j j' c)).card + 1 = 11) :
    ¬ (3 * monoBaseline (powDom ω hn) 4 11
        < 32 - (agreeSet h (spread2Dir (powDom ω hn) j j' c)).card) :=
  floor_socket_blocked_c3_g92cell ω hn _ hS

/-! ## Forward cells at `n = 64` -/

/-- At `n = 64`, the constant codeword agrees with `x^8` on exactly the `8` multiples of `8`. -/
theorem card_agree_x8_mu64 (ω : F) (hn : orderOf ω = 64) :
    (agreeSet (monoDir (powDom ω hn) 0) (monoDir (powDom ω hn) 8)).card = 8 := by
  rw [agreeSet_one_monoDir ω hn 8]
  decide

/-- The exact-boundary cell `n = 64, k = 4, a = 16` (`a² = 256 = nk`):
baseline `≥ (64 − 8)/(16 − 8) = 7`. -/
theorem monoBaseline_ge_seven_boundary64 (ω : F) (hn : orderOf ω = 64) :
    7 ≤ monoBaseline (powDom ω hn) 4 16 := by
  have hcode : monoDir (powDom ω hn) 0
      ∈ (rsCode (powDom ω hn) 4 : Submodule F (Fin 64 → F)) :=
    monoDir_mem_rsCode _ (by norm_num)
  have hcard := card_agree_x8_mu64 ω hn
  have h := monoBaseline_ge_pencil_div (powDom ω hn) (k := 4) (a := 16) (j := 8)
    (by norm_num) (by norm_num) (by norm_num) hcode (by rw [hcard]; norm_num)
  rw [hcard] at h
  norm_num at h
  exact h

/-- The near-boundary cell `n = 64, k = 2, a = 11` (`121 ≤ 128`):
baseline `≥ (64 − 8)/(11 − 8) = 18`. -/
theorem monoBaseline_ge_eighteen_n64k2 (ω : F) (hn : orderOf ω = 64) :
    18 ≤ monoBaseline (powDom ω hn) 2 11 := by
  have hcode : monoDir (powDom ω hn) 0
      ∈ (rsCode (powDom ω hn) 2 : Submodule F (Fin 64 → F)) :=
    monoDir_mem_rsCode _ (by norm_num)
  have hcard := card_agree_x8_mu64 ω hn
  have h := monoBaseline_ge_pencil_div (powDom ω hn) (k := 2) (a := 11) (j := 8)
    (by norm_num) (by norm_num) (by norm_num) hcode (by rw [hcard]; norm_num)
  rw [hcard] at h
  norm_num at h
  exact h

/-! ## Axiom audit -/

#print axioms exists_disjoint_blocks
#print axioms worstBad_ge_of_pencil_blocks
#print axioms worstBad_ge_pencil_div
#print axioms exists_codeword_agree_card_ge
#print axioms pencil_div_mono
#print axioms worstBad_ge_div_of_far
#print axioms le_monoBaseline_of_far
#print axioms monoBaseline_ge_pencil_div
#print axioms monoBaseline_ge_div_universal
#print axioms monoBaseline_gt_of_window_room
#print axioms powDom
#print axioms agreeSet_one_monoDir
#print axioms card_agree_x8_mu32
#print axioms monoBaseline_ge_eight_g92cell
#print axioms no_le_seven_certificate_g92cell
#print axioms floor_socket_blocked_c3_g92cell
#print axioms g92_kill_route_c3_impossible
#print axioms card_agree_x8_mu64
#print axioms monoBaseline_ge_seven_boundary64
#print axioms monoBaseline_ge_eighteen_n64k2

end ProximityGap.Frontier.G101FMonomialBaselineGrowth

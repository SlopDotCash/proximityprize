/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SpreadExcessLaw
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SecondWitnessFloor

/-!
# G92: the bounded spread-excess law at `C = 3` — probe + the provable fragments (#466)

Successor lane to the REFUTED windowed `SumsetExtremal`
(`466-r1-windowed-extremal-spread-beats`) and to the `C = 2` calibration of the bounded
spread-excess law, refuted in evidence by the P5 referee audit
(`docs/kb/deltastar-466b-p5-referee-2026-07-01.md`: spread `x⁴+x¹⁴` reaches ≥ 21 vs monomial
baseline 9 at `n=16, k=4, a=7` — ratio ≥ 2.33).  The live conjecture is
`_SpreadExcessLaw.SpreadExcessLaw 3`.

## Probe (part A — `probe_g92_spread_excess_c3.py`, this lane's run)

Symmetric-effort, exact-count sweep over `n ∈ {8, 16, 32}` (`k ∈ {2, 4}`), 2–3 primes
`≡ 1 mod n` per scale, all Lean-guard window levels (`k+2 ≤ a`, `a² ≤ n·k`).  Headline
(completed n=32 run, `scripts/probes/_out_g92_n32.txt`): **`C = 3` is REFUTED IN EVIDENCE** —
at `n=32, k=4, a=11` (in-window: `121 ≤ 128`) the ratio reaches `23/6 = 3.833` at BOTH probed
primes (`1048609`, `1048897`), with explicit `u₀` witnesses recorded.  The ratio GROWS with
scale (`n=16` max `2.55` at `a ∈ {6,7}` → `n=32` max `3.83` at `a=11`), driven by the
`n − (a−1)` floor THEOREM below: near the Johnson boundary the monomial baseline collapses
(`6` at `a=11`) while the floor stays `≈ n − √(nk)` — so NO constant `C` survives the
boundary cells unless the monomial baseline is proven to grow there.  `C = 2` stays dead;
at the boundary itself (`a² = n·k`) monomials win (ratio < 1).  The extremal spread
directions are exactly the directions with elevated code agreement `agreemax = a − 1`.
Caveat: spread values are certified by explicit witnesses; monomial baselines are
symmetric-effort search lower bounds, so the ratios are evidence, not theorems.

**CORRECTION (2026-07-10, G101F — `_G101FMonomialBaselineGrowth.lean`):** the `n=32, a=11`
baseline `6` above was a search artifact.  Kernel-checked: `monoBaseline ≥ 8` at that cell
(`monoBaseline_ge_eight_g92cell`), so the best-known ratio there is `23/8 = 2.875 < 3` and
the C = 3 refutation-in-evidence is RETRACTED; `SpreadExcessLaw 3` is OPEN.  Moreover the
kill route below is formally blocked at C = 3 at this cell
(`g92_kill_route_c3_impossible`), and the monomial baseline provably GROWS at boundary
cells (generalized pencil floor, θ ≈ 1/2 at fixed k).  The C = 2 refutation (n = 16) also
rests on an unproven mono upper bound and should be treated as evidence only.

## What is PROVEN here (axiom-clean, part B)

1. **Invariances of the worst-offset bad-scalar functional** — `worstBad` is invariant under
   nonzero scaling of the direction (`worstBad_smul`) and under translating the direction by
   a codeword (`worstBad_add_codeword`); same for `FarDirection`.

2. **The in-code-component collapse (`C = 1` subclass of the law, unconditional).**  If one
   component of a 2-component direction has exponent `< k` (so it lies in the code), the
   spread direction's `worstBad` EQUALS a monomial's, hence is at most the monomial baseline:
   `spread_worstBad_le_monoBaseline_of_second_lt` / `..._of_first_lt`.  The spread-excess
   phenomenon lives entirely in the both-components-`≥ k` sector.

3. **The elevated-agreement floor (the P5-referee mechanism, formalized).**  If a codeword
   agrees with a direction on exactly `a − 1` coordinates, the direction's worst offset has
   at least `n − (a−1)` bad scalars (`worstBad_ge_of_agree_pred`), by an explicit pencil
   construction: no search, no window or farness hypothesis.  Consumers pin the kill
   condition for every candidate constant: `SpreadExcessLaw C` forces
   `n − (a−1) ≤ C · monoBaseline` on every such window cell (`spreadExcessLaw_floor_le`),
   and a cell with `C · monoBaseline < n − (a−1)` refutes the law at `C`
   (`not_spreadExcessLaw_of_floor_beats`).

4. **The level functional is NOT subadditive in Fourier components**
   (`worstBad_not_subadditive`): `worstBad` is a sup of counts, not a norm — the direction
   `0 = d + (−d)` has ALL `|F|` scalars bad (`worstBad_zero`), while any far direction is
   capped at `C(n, a)` (`worstBad_le_choose`, consuming the landed incidence cap of
   `_SecondWitnessFloor`), and far monomial directions exist whenever `k ≤ j < a`
   (`farDirection_monoDir`).  So for `2·C(n,a) < |F|` the triangle inequality FAILS.  This
   kills the "component-count-weighted bound is trivial by subadditivity" route for the
   spread-excess law: any proof must use far-sector structure, not norm formalities.

## What is NOT proven (honest scope)

`SpreadExcessLaw 3` itself remains OPEN: the probe values are search lower bounds on both
classes (the `u₀`-space is `q^n`), so "ratio ≤ 3 at all probed cells" is evidence, not a
theorem; and no upper bound proved here relates `worstBad` of a far 2-component direction to
the monomial baseline in the both-components-`≥ k` sector.  The floor consumers give the
sharp refutation surface; nothing here asserts the law's truth at any `C`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ProximityGap.Frontier.G92SpreadExcessProbe

open ProximityGap.SpikeFloor ProximityGap.Ownership ProximityGap.Frontier.SpreadExcess

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## Agreement-set transport lemmas -/

/-- Agreement is invariant under adding the same word to both sides. -/
theorem agreeSet_add_same (x y w : Fin n → F) :
    agreeSet (fun i => x i + w i) (fun i => y i + w i) = agreeSet x y := by
  ext i
  simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact add_left_inj (w i)

/-- Agreement is invariant under a common nonzero scaling. -/
theorem agreeSet_smul_same {lam : F} (hlam : lam ≠ 0) (x y : Fin n → F) :
    agreeSet (fun i => lam * x i) (fun i => lam * y i) = agreeSet x y := by
  ext i
  simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact mul_right_inj' hlam

/-- Self-agreement is everything. -/
theorem agreeSet_self (x : Fin n → F) : agreeSet x x = Finset.univ := by
  ext i
  simp [agreeSet]

/-! ## Invariance of `FarDirection` under the direction symmetries -/

/-- Farness is invariant under translating the direction by a codeword. -/
theorem farDirection_add_codeword_iff (dom : Fin n ↪ F) {k a : ℕ} {u₁ c₁ : Fin n → F}
    (hc₁ : c₁ ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    FarDirection dom k a (fun i => u₁ i + c₁ i) ↔ FarDirection dom k a u₁ := by
  constructor
  · intro hfar c hc
    have h := hfar (fun i => c i + c₁ i) (Submodule.add_mem _ hc hc₁)
    rw [agreeSet_add_same] at h
    exact h
  · intro hfar c hc
    have hmem : (fun i => c i - c₁ i) ∈ (rsCode dom k : Submodule F (Fin n → F)) :=
      Submodule.sub_mem _ hc hc₁
    have h := hfar _ hmem
    have hset : agreeSet (fun i => (c i - c₁ i) + c₁ i) (fun i => u₁ i + c₁ i)
        = agreeSet (fun i => c i - c₁ i) u₁ := agreeSet_add_same _ _ _
    have hc' : (fun i => (c i - c₁ i) + c₁ i) = c := by
      funext i
      ring
    rw [hc'] at hset
    rw [← hset] at h
    exact h

/-- Farness is invariant under nonzero scaling of the direction. -/
theorem farDirection_smul_iff (dom : Fin n ↪ F) {k a : ℕ} {u₁ : Fin n → F} {lam : F}
    (hlam : lam ≠ 0) :
    FarDirection dom k a (fun i => lam * u₁ i) ↔ FarDirection dom k a u₁ := by
  constructor
  · intro hfar c hc
    have h := hfar (fun i => lam * c i) (Submodule.smul_mem _ lam hc)
    rw [agreeSet_smul_same hlam] at h
    exact h
  · intro hfar c hc
    have hmem : (fun i => lam⁻¹ * c i) ∈ (rsCode dom k : Submodule F (Fin n → F)) :=
      Submodule.smul_mem _ lam⁻¹ hc
    have h := hfar _ hmem
    have hset : agreeSet (fun i => lam * (lam⁻¹ * c i)) (fun i => lam * u₁ i)
        = agreeSet (fun i => lam⁻¹ * c i) u₁ := agreeSet_smul_same hlam _ _
    have hc' : (fun i => lam * (lam⁻¹ * c i)) = c := by
      funext i
      field_simp
    rw [hc'] at hset
    rw [← hset] at h
    exact h

/-! ## Invariance of the bad-scalar sets and `worstBad` -/

/-- Translating the direction by a codeword leaves the bad-scalar set of EVERY offset
unchanged (the codeword absorbs into the witnessing codeword, scalar by scalar). -/
theorem lineBadScalars_add_codeword (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c₁ : Fin n → F)
    (hc₁ : c₁ ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    SpreadExcess.lineBadScalars dom k a u₀ (fun i => u₁ i + c₁ i)
      = SpreadExcess.lineBadScalars dom k a u₀ u₁ := by
  ext γ
  simp only [SpreadExcess.lineBadScalars, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, hc, hagree⟩
    refine ⟨fun i => c i - γ • c₁ i, Submodule.sub_mem _ hc (Submodule.smul_mem _ γ hc₁), ?_⟩
    have hset : agreeSet (fun i => c i - γ • c₁ i) (fun i => u₀ i + γ • u₁ i)
        = agreeSet c (fun i => u₀ i + γ • (u₁ i + c₁ i)) := by
      ext i
      simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and, smul_eq_mul]
      constructor
      · intro h; linear_combination h
      · intro h; linear_combination h
    rw [hset]
    exact hagree
  · rintro ⟨c, hc, hagree⟩
    refine ⟨fun i => c i + γ • c₁ i, Submodule.add_mem _ hc (Submodule.smul_mem _ γ hc₁), ?_⟩
    have hset : agreeSet (fun i => c i + γ • c₁ i) (fun i => u₀ i + γ • (u₁ i + c₁ i))
        = agreeSet c (fun i => u₀ i + γ • u₁ i) := by
      ext i
      simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and, smul_eq_mul]
      constructor
      · intro h; linear_combination h
      · intro h; linear_combination h
    rw [hset]
    exact hagree

/-- Scaling the direction by a nonzero constant reparametrizes the bad scalars bijectively:
the count of EVERY offset is unchanged. -/
theorem lineBadScalars_smul_card (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    {lam : F} (hlam : lam ≠ 0) :
    (SpreadExcess.lineBadScalars dom k a u₀ (fun i => lam * u₁ i)).card
      = (SpreadExcess.lineBadScalars dom k a u₀ u₁).card := by
  refine Finset.card_bij (fun γ _ => γ * lam) ?_ ?_ ?_
  · intro γ hγ
    simp only [SpreadExcess.lineBadScalars, Finset.mem_filter, Finset.mem_univ,
      true_and] at hγ ⊢
    obtain ⟨c, hc, hagree⟩ := hγ
    refine ⟨c, hc, ?_⟩
    have hfun : (fun i => u₀ i + γ • (lam * u₁ i)) = fun i => u₀ i + (γ * lam) • u₁ i := by
      funext i
      simp only [smul_eq_mul]
      ring
    rw [← hfun]
    exact hagree
  · intro γ₁ h₁ γ₂ h₂ h
    exact mul_right_cancel₀ hlam h
  · intro δ hδ
    simp only [SpreadExcess.lineBadScalars, Finset.mem_filter, Finset.mem_univ,
      true_and] at hδ
    obtain ⟨c, hc, hagree⟩ := hδ
    refine ⟨δ * lam⁻¹, ?_, by field_simp⟩
    simp only [SpreadExcess.lineBadScalars, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨c, hc, ?_⟩
    have hfun : (fun i => u₀ i + (δ * lam⁻¹) • (lam * u₁ i))
        = fun i => u₀ i + δ • u₁ i := by
      funext i
      simp only [smul_eq_mul]
      field_simp
    rw [hfun]
    exact hagree

/-- `worstBad` is invariant under translating the direction by a codeword. -/
theorem worstBad_add_codeword (dom : Fin n ↪ F) (k a : ℕ) (u₁ c₁ : Fin n → F)
    (hc₁ : c₁ ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    worstBad dom k a (fun i => u₁ i + c₁ i) = worstBad dom k a u₁ := by
  unfold worstBad
  exact Finset.sup_congr rfl fun u₀ _ => by
    rw [lineBadScalars_add_codeword dom k a u₀ u₁ c₁ hc₁]

/-- `worstBad` is invariant under nonzero scaling of the direction. -/
theorem worstBad_smul (dom : Fin n ↪ F) (k a : ℕ) (u₁ : Fin n → F) {lam : F}
    (hlam : lam ≠ 0) :
    worstBad dom k a (fun i => lam * u₁ i) = worstBad dom k a u₁ := by
  unfold worstBad
  exact Finset.sup_congr rfl fun u₀ _ => lineBadScalars_smul_card dom k a u₀ u₁ hlam

/-! ## The in-code-component collapse: the `C = 1` subclass of the law -/

/-- Monomials of exponent `< k` are codewords. -/
theorem monoDir_mem_rsCode (dom : Fin n ↪ F) {k j : ℕ} (hj : j < k) :
    monoDir dom j ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
  refine ⟨X ^ j, ?_, ?_⟩
  · rw [Polynomial.degree_X_pow]
    exact_mod_cast hj
  · funext i
    simp [monoDir]

/-- Scaled monomials of exponent `< k` are codewords. -/
theorem smul_monoDir_mem_rsCode (dom : Fin n ↪ F) {k j' : ℕ} (c : F) (hj' : j' < k) :
    (fun i => c * dom i ^ j') ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
  have h := Submodule.smul_mem _ c (monoDir_mem_rsCode dom hj')
  have hfn : (fun i => c * dom i ^ j') = c • monoDir dom j' := by
    funext i
    simp [monoDir]
  rw [hfn]
  exact h

/-- A 2-component direction whose SECOND component is in-code (`j' < k`) has exactly a
monomial's worst-offset bad-scalar count. -/
theorem worstBad_spread2Dir_of_second_lt (dom : Fin n ↪ F) {k j j' : ℕ} (a : ℕ) (c : F)
    (hj' : j' < k) :
    worstBad dom k a (spread2Dir dom j j' c) = worstBad dom k a (monoDir dom j) := by
  have hfun : spread2Dir dom j j' c = fun i => monoDir dom j i + c * dom i ^ j' := by
    funext i
    simp [spread2Dir, monoDir]
  rw [hfun,
    worstBad_add_codeword dom k a (monoDir dom j) (fun i => c * dom i ^ j')
      (smul_monoDir_mem_rsCode dom c hj')]

/-- Farness transfer for the second-component-in-code case. -/
theorem farDirection_spread2Dir_of_second_lt (dom : Fin n ↪ F) {k a j j' : ℕ} (c : F)
    (hj' : j' < k)
    (hfar : FarDirection dom k a (spread2Dir dom j j' c)) :
    FarDirection dom k a (monoDir dom j) := by
  have hfun : spread2Dir dom j j' c = fun i => monoDir dom j i + c * dom i ^ j' := by
    funext i
    simp [spread2Dir, monoDir]
  rw [hfun] at hfar
  exact (farDirection_add_codeword_iff dom (smul_monoDir_mem_rsCode dom c hj')).mp hfar

/-- **The `C = 1` subclass theorem**: a far 2-component direction with second component
in-code (`j' < k`, first exponent `< n`) obeys the spread-excess law with constant `1` —
no window hypothesis needed. -/
theorem spread_worstBad_le_monoBaseline_of_second_lt (dom : Fin n ↪ F)
    {k a j j' : ℕ} (c : F) (hj : j < n) (hj' : j' < k)
    (hfar : FarDirection dom k a (spread2Dir dom j j' c)) :
    worstBad dom k a (spread2Dir dom j j' c) ≤ monoBaseline dom k a := by
  classical
  rw [worstBad_spread2Dir_of_second_lt dom a c hj']
  have hval : ((⟨j, hj⟩ : Fin n) : ℕ) = j := rfl
  have hfarm : FarDirection dom k a (monoDir dom j) :=
    farDirection_spread2Dir_of_second_lt dom c hj' hfar
  rw [← hval] at hfarm ⊢
  unfold monoBaseline
  exact Finset.le_sup (f := fun jm : Fin n => worstBad dom k a (monoDir dom (jm : ℕ)))
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfarm⟩)

/-- **The `C = 1` subclass theorem, first component in-code** (`j < k`, second exponent
`< n`, `a ≤ n`): the coefficient `c` is absorbed by scaling invariance (and `c = 0` is
incompatible with farness). -/
theorem spread_worstBad_le_monoBaseline_of_first_lt (dom : Fin n ↪ F)
    {k a j j' : ℕ} (c : F) (han : a ≤ n) (hj : j < k) (hj' : j' < n)
    (hfar : FarDirection dom k a (spread2Dir dom j j' c)) :
    worstBad dom k a (spread2Dir dom j j' c) ≤ monoBaseline dom k a := by
  classical
  rcases eq_or_ne c 0 with rfl | hc
  · exfalso
    have hself : spread2Dir dom j j' (0 : F) = monoDir dom j := by
      funext i
      simp [spread2Dir, monoDir]
    have h := hfar (monoDir dom j) (monoDir_mem_rsCode dom hj)
    rw [hself, agreeSet_self, Finset.card_univ, Fintype.card_fin] at h
    omega
  · have hfun : spread2Dir dom j j' c = fun i => c * dom i ^ j' + monoDir dom j i := by
      funext i
      simp only [spread2Dir, monoDir]
      ring
    have hfar' := hfar
    rw [hfun] at hfar'
    have h1 : FarDirection dom k a (fun i => c * dom i ^ j') :=
      (farDirection_add_codeword_iff dom (monoDir_mem_rsCode dom hj)).mp hfar'
    have hsc : (fun i => c * dom i ^ j') = fun i => c * monoDir dom j' i := by
      funext i
      simp [monoDir]
    rw [hsc] at h1
    have hval : ((⟨j', hj'⟩ : Fin n) : ℕ) = j' := rfl
    have hfarm : FarDirection dom k a (monoDir dom j') :=
      (farDirection_smul_iff dom hc).mp h1
    rw [hfun,
      worstBad_add_codeword dom k a (fun i => c * dom i ^ j') (monoDir dom j)
        (monoDir_mem_rsCode dom hj),
      hsc, worstBad_smul dom k a (monoDir dom j') hc]
    rw [← hval] at hfarm ⊢
    unfold monoBaseline
    exact Finset.le_sup (f := fun jm : Fin n => worstBad dom k a (monoDir dom (jm : ℕ)))
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfarm⟩)

/-! ## The elevated-agreement floor (the P5-referee mechanism, formalized) -/

/-- **The elevated-agreement floor.**  If a codeword `h` agrees with the direction `u₁` on
exactly `a − 1` coordinates (`card + 1 = a`), then some offset has at least `n − (a−1)` bad
scalars: for each coordinate `l` outside the agreement set, the scalar `γ = dom l` is bad
for the explicit offset `u₀ = h − dom·(u₁ − h)`, witnessed by the codeword `(1 + dom l)•h`
agreeing on `S ∪ {l}`.  No window or farness hypothesis; no search. -/
theorem worstBad_ge_of_agree_pred (dom : Fin n ↪ F) {k a : ℕ} {h u₁ : Fin n → F}
    (hcode : h ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hS : (agreeSet h u₁).card + 1 = a) :
    n - (agreeSet h u₁).card ≤ worstBad dom k a u₁ := by
  classical
  unfold worstBad
  set S : Finset (Fin n) := agreeSet h u₁ with hSdef
  set u₀ : Fin n → F := fun i => h i - dom i * (u₁ i - h i) with hu₀
  have hkey : ∀ l : Fin n, l ∉ S → dom l ∈ SpreadExcess.lineBadScalars dom k a u₀ u₁ := by
    intro l hl
    simp only [SpreadExcess.lineBadScalars, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun i => (1 + dom l) * h i, ?_, ?_⟩
    · have hmem := Submodule.smul_mem _ (1 + dom l) hcode
      have hfn : (fun i => (1 + dom l) * h i) = (1 + dom l) • h := by
        funext i
        simp
      rw [hfn]
      exact hmem
    · have hsub : insert l S
          ⊆ agreeSet (fun i => (1 + dom l) * h i) (fun i => u₀ i + dom l • u₁ i) := by
        intro i hi
        simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and]
        simp only [hu₀, smul_eq_mul]
        rcases Finset.mem_insert.mp hi with rfl | hiS
        · ring
        · have hhi : h i = u₁ i := by
            rw [hSdef] at hiS
            simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hiS
            exact hiS
          rw [← hhi]
          ring
      calc a = S.card + 1 := hS.symm
        _ = (insert l S).card := (Finset.card_insert_of_notMem hl).symm
        _ ≤ _ := Finset.card_le_card hsub
  have himg : (Sᶜ).image (fun l => dom l) ⊆ SpreadExcess.lineBadScalars dom k a u₀ u₁ := by
    intro γ hγ
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hγ
    exact hkey l (Finset.mem_compl.mp hl)
  have hcount : n - S.card ≤ (SpreadExcess.lineBadScalars dom k a u₀ u₁).card := by
    calc n - S.card = (Sᶜ).card := by
          rw [Finset.card_compl, Fintype.card_fin]
      _ = ((Sᶜ).image (fun l => dom l)).card :=
          (Finset.card_image_of_injective _ dom.injective).symm
      _ ≤ _ := Finset.card_le_card himg
  exact le_trans hcount
    (Finset.le_sup (f := fun u₀ => (SpreadExcess.lineBadScalars dom k a u₀ u₁).card)
      (Finset.mem_univ u₀))

/-- **Floor consumer (kill-condition socket).**  Any true `SpreadExcessLaw C` must absorb
the elevated-agreement floor: on every window cell carrying a far 2-component direction
with an exact `(a−1)`-agreement codeword witness, `n − (a−1) ≤ C · monoBaseline`. -/
theorem spreadExcessLaw_floor_le {C : ℕ} (hlaw : SpreadExcessLaw C)
    (dom : Fin n ↪ F) {k a j j' : ℕ} {c : F} {h : Fin n → F}
    (hwin1 : k + 2 ≤ a) (hwin2 : a * a ≤ n * k)
    (hfar : FarDirection dom k a (spread2Dir dom j j' c))
    (hcode : h ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hS : (agreeSet h (spread2Dir dom j j' c)).card + 1 = a) :
    n - (agreeSet h (spread2Dir dom j j' c)).card ≤ C * monoBaseline dom k a :=
  le_trans (worstBad_ge_of_agree_pred dom hcode hS)
    (hlaw F n dom k a j j' c hwin1 hwin2 hfar)

/-- **Refutation socket.**  A single window cell whose floor beats `C · monoBaseline`
refutes the spread-excess law at `C` (this is how a probe cell kills a constant). -/
theorem not_spreadExcessLaw_of_floor_beats {C : ℕ}
    (dom : Fin n ↪ F) {k a j j' : ℕ} {c : F} {h : Fin n → F}
    (hwin1 : k + 2 ≤ a) (hwin2 : a * a ≤ n * k)
    (hfar : FarDirection dom k a (spread2Dir dom j j' c))
    (hcode : h ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hS : (agreeSet h (spread2Dir dom j j' c)).card + 1 = a)
    (hgt : C * monoBaseline dom k a < n - (agreeSet h (spread2Dir dom j j' c)).card) :
    ¬ SpreadExcessLaw C := fun hlaw =>
  absurd (spreadExcessLaw_floor_le hlaw dom hwin1 hwin2 hfar hcode hS) (not_le.mpr hgt)

/-! ## The level functional is a sup of counts, not a norm: subadditivity FAILS -/

/-- Far monomial directions exist purely by degree counting: `x^j` is `a`-far whenever
`k ≤ j < a` (a degree-`< k` polynomial can meet `x^j` in at most `j` points). -/
theorem farDirection_monoDir (dom : Fin n ↪ F) {k a j : ℕ} (hkj : k ≤ j) (hja : j < a) :
    FarDirection dom k a (monoDir dom j) := by
  rintro c ⟨P, hP, rfl⟩
  set Q : F[X] := X ^ j - P with hQ
  have hdegP : P.degree < ((j : ℕ) : WithBot ℕ) :=
    lt_of_lt_of_le hP (by exact_mod_cast hkj)
  have hdegQ : Q.degree = ((j : ℕ) : WithBot ℕ) := by
    rw [hQ, Polynomial.degree_sub_eq_left_of_degree_lt
      (by rwa [Polynomial.degree_X_pow])]
    exact Polynomial.degree_X_pow j
  have hQne : Q ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.degree_zero] at hdegQ
    simp at hdegQ
  have hroots : (agreeSet (fun i => P.eval (dom i)) (monoDir dom j)).image dom
      ⊆ Q.roots.toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and, monoDir] at hi
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQne]
    show Q.eval (dom i) = 0
    rw [hQ]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hi]
    ring
  calc (agreeSet (fun i => P.eval (dom i)) (monoDir dom j)).card
      = ((agreeSet (fun i => P.eval (dom i)) (monoDir dom j)).image dom).card :=
        (Finset.card_image_of_injective _ dom.injective).symm
    _ ≤ Q.roots.toFinset.card := Finset.card_le_card hroots
    _ ≤ Multiset.card Q.roots := Multiset.toFinset_card_le _
    _ ≤ Q.natDegree := Polynomial.card_roots' Q
    _ = j := Polynomial.natDegree_eq_of_degree_eq_some hdegQ
    _ < a := hja

/-- Far directions are capped: `worstBad ≤ C(n, a)` (the landed incidence cap of
`_SecondWitnessFloor`, transported to the `SpreadExcess` vocabulary). -/
theorem worstBad_le_choose (dom : Fin n ↪ F) {k a : ℕ} {u₁ : Fin n → F}
    (hk1 : 1 ≤ k) (hka : k ≤ a) (hfar : FarDirection dom k a u₁) :
    worstBad dom k a u₁ ≤ n.choose a := by
  unfold worstBad
  refine Finset.sup_le fun u₀ _ => ?_
  have hbridge : SpreadExcess.lineBadScalars dom k a u₀ u₁
      = ProximityGap.Ownership.lineBadScalars dom k a u₀ u₁ := by
    ext γ
    simp only [SpreadExcess.lineBadScalars, ProximityGap.Ownership.lineBadScalars,
      Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hbridge]
  exact ProximityGap.Ownership.lineBadScalars_card_le_choose dom k a hk1 hka u₀ u₁
    (fun c hc => hfar c hc)

/-- The degenerate direction `0` saturates the whole field: every scalar is bad. -/
theorem worstBad_zero (dom : Fin n ↪ F) {k a : ℕ} (han : a ≤ n) :
    worstBad dom k a (0 : Fin n → F) = Fintype.card F := by
  classical
  unfold worstBad
  apply le_antisymm
  · exact Finset.sup_le fun u₀ _ => Finset.card_le_univ _
  · have huniv : SpreadExcess.lineBadScalars dom k a (0 : Fin n → F) (0 : Fin n → F)
        = Finset.univ := by
      rw [Finset.eq_univ_iff_forall]
      intro γ
      simp only [SpreadExcess.lineBadScalars, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      have hset : agreeSet (0 : Fin n → F)
          (fun i => (0 : Fin n → F) i + γ • (0 : Fin n → F) i) = Finset.univ := by
        ext i
        simp [agreeSet]
      rw [hset, Finset.card_univ, Fintype.card_fin]
      exact han
    calc Fintype.card F
        = (SpreadExcess.lineBadScalars dom k a (0 : Fin n → F) (0 : Fin n → F)).card := by
          rw [huniv, Finset.card_univ]
      _ ≤ _ := Finset.le_sup
          (f := fun u₀ => (SpreadExcess.lineBadScalars dom k a u₀ (0 : Fin n → F)).card)
          (Finset.mem_univ (0 : Fin n → F))

/-- `worstBad` of the negated direction. -/
theorem worstBad_neg (dom : Fin n ↪ F) (k a : ℕ) (u₁ : Fin n → F) :
    worstBad dom k a (fun i => -u₁ i) = worstBad dom k a u₁ := by
  have hfun : (fun i => -u₁ i) = fun i => (-1 : F) * u₁ i := by
    funext i
    ring
  rw [hfun, worstBad_smul dom k a u₁ (neg_ne_zero.mpr one_ne_zero)]

/-- **The worst-offset bad-scalar functional is NOT subadditive in the direction** — the
triangle-inequality route to a component-count-weighted spread-excess bound is dead.  For
any level with a far monomial (`1 ≤ k ≤ j < a ≤ n`) over a field with `2·C(n,a) < |F|`, the
sum `d + (−d) = 0` of two far directions saturates all `|F|` scalars while each summand is
capped at `C(n, a)`. -/
theorem worstBad_not_subadditive (dom : Fin n ↪ F) {k a j : ℕ}
    (hk1 : 1 ≤ k) (hkj : k ≤ j) (hja : j < a) (han : a ≤ n)
    (hq : 2 * n.choose a < Fintype.card F) :
    ¬ ∀ d₁ d₂ : Fin n → F,
        worstBad dom k a (fun i => d₁ i + d₂ i)
          ≤ worstBad dom k a d₁ + worstBad dom k a d₂ := by
  intro hsub
  have hfar : FarDirection dom k a (monoDir dom j) := farDirection_monoDir dom hkj hja
  have hcap : worstBad dom k a (monoDir dom j) ≤ n.choose a :=
    worstBad_le_choose dom hk1 (le_trans hkj (le_of_lt hja)) hfar
  have hzero : (fun i => monoDir dom j i + -monoDir dom j i) = (0 : Fin n → F) := by
    funext i
    simp
  have h := hsub (monoDir dom j) (fun i => -monoDir dom j i)
  simp only [] at h
  rw [hzero, worstBad_zero dom han, worstBad_neg dom k a (monoDir dom j)] at h
  omega

/-! ## Axiom audit -/

#print axioms agreeSet_add_same
#print axioms agreeSet_smul_same
#print axioms agreeSet_self
#print axioms farDirection_add_codeword_iff
#print axioms farDirection_smul_iff
#print axioms lineBadScalars_add_codeword
#print axioms lineBadScalars_smul_card
#print axioms worstBad_add_codeword
#print axioms worstBad_smul
#print axioms monoDir_mem_rsCode
#print axioms smul_monoDir_mem_rsCode
#print axioms worstBad_spread2Dir_of_second_lt
#print axioms farDirection_spread2Dir_of_second_lt
#print axioms spread_worstBad_le_monoBaseline_of_second_lt
#print axioms spread_worstBad_le_monoBaseline_of_first_lt
#print axioms worstBad_ge_of_agree_pred
#print axioms spreadExcessLaw_floor_le
#print axioms not_spreadExcessLaw_of_floor_beats
#print axioms farDirection_monoDir
#print axioms worstBad_le_choose
#print axioms worstBad_zero
#print axioms worstBad_neg
#print axioms worstBad_not_subadditive

end ProximityGap.Frontier.G92SpreadExcessProbe

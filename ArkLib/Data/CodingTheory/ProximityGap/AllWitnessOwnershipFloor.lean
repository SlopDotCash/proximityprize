/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Level1RungPin

/-!
# The all-witness ownership floor: `≥ C(w−1, d+1)` unfit subsets in EVERY unfit witness (#371)

The per-witness `(d+2)`-subset counting surface of the dimension-ladder programme had, before
this file, a proven ownership floor only at the band edge: a non-fit `(d+3)`-set has at most one
fit `(d+2)`-subset (`fit_subsets_card_le_one`, equivalently the glueing law `#bad·(d+2) ≤
C(n,d+2)`), while the proven *ceiling* (`deviation_ownership_card`,
`OwnershipCensusSharpened.lean`) says the per-witness minimum ownership is at most
`C(w−1, d+1)`, attained by single-deviation directions.  This file closes the scheme by proving
the matching floor at **every** witness size:

> **`fit_subsets_card_le`** — if `u` has no degree-`d` fit on a `w`-set `S`, then at most
> `C(w−1, d+2)` of the `(d+2)`-subsets of `S` are fit; equivalently
> (**`unfit_subsets_card_ge`**) at least `C(w−1, d+1)` are unfit — i.e. owned, since an unfit
> subset inside a bad witness determines its scalar.

With the deviation ceiling, per-witness subset ownership is now **exact two-sided**: the true
minimum is `C(w−1, d+1)`, period.  The proof is a divided-difference double recursion (new to
this campaign; sharper than the glue-component superadditivity sketched in the issue thread):

1. For `w ≥ d+3` some point `x₀` keeps `S \ {x₀}` unfit — otherwise two fitting erasures glue
   through their `≥ d+1` common points (`fit_unique`) into a fit of all of `S`.
2. Fit subsets avoiding `x₀` recurse at `(d, w−1)` on `S \ {x₀}`.
3. Fit subsets containing `x₀` are EXACTLY the fit `(d+1)`-subsets at degree `d−1` of the
   **divided difference** `v(i) = (u(i) − u(x₀)) / (x_i − x_{x₀})` on `S \ {x₀}`
   (`fit_insert_iff_divDiff`) — recursing at `(d−1, w−1)`; the same equivalence at
   `G = S \ {x₀}` shows `v` is itself unfit, so the recursion is well-founded.  At `d = 0`
   the containing side is the value class of `u(x₀)`, missing at least one point.
4. Pascal closes: `C(w−2, d+2) + C(w−2, d+1) = C(w−1, d+2)`.

## Consumers

* **`allWitness_badScalars_card_mul_le`** — `#bad · C(w₀, d+1) ≤ C(n, d+2)` at every radius
  with witness threshold `w₀` (witness size `≥ w₀+1`).  This **strictly dominates both landed
  laws at every radius**: versus the sharp/glueing subset law it multiplies the divisor by
  `C(w₀,d+1)/(d+2) ≥ 1` (equality exactly at the band edge `w₀ = d+2`, where it reproduces
  `#bad·(d+2) ≤ C(n,d+2)`); versus the pair law (`sharpened_badScalars_card_mul_choose_le`,
  divisor-equivalent `C(w₀+1,d+1)/(d+2)`) the gain ratio is `(d+2)(w₀−d−1)/(w₀+1) > 1` for
  every `w₀ > d+2`.
* **`allWitness_epsMCA_le`** — `ε_mca(δ) ≤ (C(n,d+2)/C(w₀,d+1))/p`, radius-decoupled.
* **`le_mcaDeltaStar_allWitness`** — the threshold form.
* **`level1_engine_goodSide_F12289_sharp` / `deltaStar_ge_level1_radius_F12289_sharp`** — the
  concrete payoff at the level-1 rung instance (`p = 12289`, `n = 16`, `d = 2`, threshold 7):
  the unconditional good side drops `208/p → 91/p` (`C(16,4)/C(6,3) = 1820/20 = 91` — exactly
  the "realizable-extremal cap" the rung lane computed from the deviation ceiling, now proven
  to be the engine value), so the beyond-Johnson lower bound `δ* ≥ 5/8` holds at every
  `ε* ≥ 91/p`.

Probe: `scripts/probes/probe_allwitness_floor.py` (pre-registered, exit 0) — exhaustive floor
check at `p = 13` (`d ≤ 2`, every value pattern over a 3-letter alphabet plus random full-field
words), deviation tightness `unfit = C(w−1,d+1)` exactly, adversarial hill-climb minimization at
`p = 17` (`d ≤ 3`, `w ≤ 10`: the floor is attained but never beaten), and both recursion
invariants (erasure existence + the divided-difference equivalence) verified pointwise.

**Honest scope.**  This closes the per-witness subset-counting scheme (floor = ceiling); it does
NOT move the scheme's wall: the level-1 rung obligation needs `≤ 31 < 52 ≤ 91`, so the rung
stays open exactly as the saturation theorem says, and production dimension still needs a
different counting surface.  What it buys is the sharpest unconditional radius-decoupled good
side the scheme admits, at every threshold, in one statement.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction
open ArkLib.ProximityGap.KKH26DimGeneral

namespace ArkLib.ProximityGap.AllWitnessFloor

/-! ## The divided difference and the fit transport -/

/-- The first divided difference of `u` at the pivot `x₀` over the smooth domain:
`v(i) = (u(i) − u(x₀)) / (g^i − g^{x₀})`. -/
def divDiff {p : ℕ} [Fact p.Prime] (g : ZMod p) {n : ℕ} (u : Fin n → ZMod p) (x₀ : Fin n) :
    Fin n → ZMod p :=
  fun i => (u i - u x₀) / (g ^ (i : ℕ) - g ^ ((x₀ : Fin n) : ℕ))

/-- `polyFitOn` restricts to subsets (the same interpolant works). -/
theorem fit_mono {p : ℕ} {g : ZMod p} {n d : ℕ} {T T' : Finset (Fin n)}
    {y : Fin n → ZMod p} (h : polyFitOn g d T y) (hsub : T' ⊆ T) : polyFitOn g d T' y := by
  obtain ⟨q, hq, hv⟩ := h
  exact ⟨q, hq, fun i hi => hv i (hsub hi)⟩

/-- **The divided-difference fit transport**: for `d ≥ 1` and `x₀ ∉ G`, a degree-`d` fit of `u`
on `insert x₀ G` is the same thing as a degree-`(d−1)` fit of the divided difference
`divDiff g u x₀` on `G`.  (Forward: factor the root at `x₀` out of `q − u(x₀)`; backward:
re-multiply.)  This is the recursion step of the all-witness floor. -/
theorem fit_insert_iff_divDiff {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ}
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j)
    {d : ℕ} (hd : 1 ≤ d) {x₀ : Fin n} {G : Finset (Fin n)} (hxG : x₀ ∉ G)
    {u : Fin n → ZMod p} :
    polyFitOn g d (insert x₀ G) u ↔ polyFitOn g (d - 1) G (divDiff g u x₀) := by
  have hne : ∀ i ∈ G, g ^ (i : ℕ) - g ^ ((x₀ : Fin n) : ℕ) ≠ 0 := by
    intro i hi
    refine sub_ne_zero.mpr (fun h => hxG ?_)
    rw [← hginj i x₀ h]
    exact hi
  constructor
  · rintro ⟨q, hqdeg, hqval⟩
    have hroot : (q - Polynomial.C (u x₀)).IsRoot (g ^ ((x₀ : Fin n) : ℕ)) := by
      have := hqval x₀ (Finset.mem_insert_self _ _)
      simp [Polynomial.IsRoot, ← this]
    obtain ⟨R, hR⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
    refine ⟨R, ?_, fun i hi => ?_⟩
    · by_cases hR0 : R = 0
      · simp [hR0]
      · have h1 : (q - Polynomial.C (u x₀)).natDegree ≤ d :=
          le_trans (Polynomial.natDegree_sub_le _ _)
            (max_le hqdeg (by simp))
        rw [hR, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hR0,
          Polynomial.natDegree_X_sub_C] at h1
        omega
    · have hev : u i - u x₀
          = (g ^ (i : ℕ) - g ^ ((x₀ : Fin n) : ℕ)) * R.eval (g ^ (i : ℕ)) := by
        have hco := congrArg (Polynomial.eval (g ^ (i : ℕ))) hR
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X] at hco
        rw [← hqval i (Finset.mem_insert_of_mem hi)] at hco
        exact hco
      show (u i - u x₀) / (g ^ (i : ℕ) - g ^ ((x₀ : Fin n) : ℕ)) = R.eval (g ^ (i : ℕ))
      rw [hev, mul_div_cancel_left₀ _ (hne i hi)]
  · rintro ⟨R, hRdeg, hRval⟩
    refine ⟨Polynomial.C (u x₀)
      + (Polynomial.X - Polynomial.C (g ^ ((x₀ : Fin n) : ℕ))) * R, ?_, fun i hi => ?_⟩
    · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp) ?_)
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      rw [Polynomial.natDegree_X_sub_C]
      omega
    · rcases Finset.mem_insert.mp hi with h | h
      · subst h
        simp
      · have hv := hRval i h
        simp only [divDiff] at hv
        rw [div_eq_iff (hne i h)] at hv
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C]
        linear_combination hv

/-! ## The erasure step -/

/-- For `w ≥ d+3`, some erasure of an unfit set stays unfit: otherwise two fitting erasures
glue through their `≥ d+1` common points into a fit of all of `S`. -/
theorem exists_erase_unfit {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ}
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j)
    {d : ℕ} {S : Finset (Fin n)} (hcard : d + 3 ≤ S.card)
    {u : Fin n → ZMod p} (hunfit : ¬ polyFitOn g d S u) :
    ∃ x ∈ S, ¬ polyFitOn g d (S.erase x) u := by
  by_contra hcon
  push_neg at hcon
  -- two distinct points of S
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) a
  obtain ⟨qa, hqadeg, hqaval⟩ := hcon a ha
  obtain ⟨qb, hqbdeg, hqbval⟩ := hcon b hb
  have hcommon : d + 1 ≤ ((S.erase a).erase b).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hba, hb⟩),
      Finset.card_erase_of_mem ha]
    omega
  have hqq : qa = qb := by
    refine fit_unique hginj hcommon hqadeg hqbdeg (fun i hi => ?_)
    have hia : i ∈ S.erase a := Finset.mem_of_mem_erase hi
    have hib : i ∈ S.erase b := by
      have h1 := Finset.mem_erase.mp hi
      have h2 := Finset.mem_erase.mp hia
      exact Finset.mem_erase.mpr ⟨h1.1, h2.2⟩
    rw [← hqaval i hia, ← hqbval i hib]
  refine hunfit ⟨qa, hqadeg, fun i hi => ?_⟩
  by_cases hia : i = a
  · subst hia
    rw [hqq]
    exact hqbval i (Finset.mem_erase.mpr ⟨hba.symm, hi⟩)
  · exact hqaval i (Finset.mem_erase.mpr ⟨hia, hi⟩)

/-! ## The all-witness floor -/

open Classical in
/-- **The all-witness fit-subset bound** (auxiliary, fuel-indexed form): an unfit `w`-set has
at most `C(w−1, d+2)` fit `(d+2)`-subsets.  Divided-difference double recursion on `(d, w)`,
fueled by `N ≥ d + w`. -/
private theorem fit_subsets_card_le_aux {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ}
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j) :
    ∀ N d : ℕ, ∀ S : Finset (Fin n), ∀ u : Fin n → ZMod p, d + S.card ≤ N →
      ¬ polyFitOn g d S u →
      ((S.powersetCard (d + 2)).filter (fun T => polyFitOn g d T u)).card
        ≤ (S.card - 1).choose (d + 2) := by
  intro N
  induction N with
  | zero =>
    intro d S u hfuel hunfit
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
    refine absurd ⟨0, by simp, fun i hi => ?_⟩ hunfit
    rw [hS0] at hi
    exact absurd hi (Finset.notMem_empty i)
  | succ N ih =>
    intro d S u hfuel hunfit
    by_cases hsmall : S.card ≤ d + 2
    -- Degenerate sizes: the only candidate subset is S itself, which is unfit.
    · have hempty : (S.powersetCard (d + 2)).filter (fun T => polyFitOn g d T u) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro T hT
        obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
        have hTS : T = S := Finset.eq_of_subset_of_card_le hTsub (by omega)
        rw [hTS]
        exact hunfit
      simp [hempty]
    · push_neg at hsmall
      -- w ≥ d + 3: pick x₀ with the erasure unfit
      obtain ⟨x₀, hx₀S, hx₀unfit⟩ := exists_erase_unfit hginj (by omega) hunfit
      have hWcard : (S.erase x₀).card = S.card - 1 := Finset.card_erase_of_mem hx₀S
      set F := (S.powersetCard (d + 2)).filter (fun T => polyFitOn g d T u) with hFdef
      -- split on membership of x₀
      have hsplit : (F.filter (fun T => x₀ ∈ T)).card
          + (F.filter (fun T => ¬ x₀ ∈ T)).card = F.card :=
        Finset.filter_card_add_filter_neg_card_eq_card (s := F) (p := fun T => x₀ ∈ T)
      -- the avoiding side IS the fit family of the erasure
      have havoid : F.filter (fun T => ¬ x₀ ∈ T)
          = ((S.erase x₀).powersetCard (d + 2)).filter (fun T => polyFitOn g d T u) := by
        ext T
        simp only [hFdef, Finset.mem_filter, Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨⟨hTsub, hTcard⟩, hTfit⟩, hTx⟩
          exact ⟨⟨Finset.subset_erase.mpr ⟨hTsub, hTx⟩, hTcard⟩, hTfit⟩
        · rintro ⟨⟨hTsub, hTcard⟩, hTfit⟩
          obtain ⟨h1, h2⟩ := Finset.subset_erase.mp hTsub
          exact ⟨⟨⟨h1, hTcard⟩, hTfit⟩, h2⟩
      have havoid_le : (F.filter (fun T => ¬ x₀ ∈ T)).card
          ≤ (S.card - 2).choose (d + 2) := by
        rw [havoid]
        have h := ih d (S.erase x₀) u (by omega) hx₀unfit
        rwa [hWcard, show S.card - 1 - 1 = S.card - 2 from by omega] at h
      -- the containing side
      have hcontain_le : (F.filter (fun T => x₀ ∈ T)).card
          ≤ (S.card - 2).choose (d + 1) := by
        rcases Nat.eq_zero_or_pos d with hd0 | hdpos
        -- d = 0: the containing side injects into the value class of u(x₀) inside W
        · subst hd0
          -- the value class misses some point of the erasure
          obtain ⟨z, hzW, hzne⟩ : ∃ z ∈ S.erase x₀, u z ≠ u x₀ := by
            by_contra hcon
            push_neg at hcon
            refine hunfit ⟨Polynomial.C (u x₀), by simp, fun i hi => ?_⟩
            rw [Polynomial.eval_C]
            by_cases hix : i = x₀
            · rw [hix]
            · exact hcon i (Finset.mem_erase.mpr ⟨hix, hi⟩)
          set M := (S.erase x₀).filter (fun y => u y = u x₀) with hMdef
          have hMcard : M.card ≤ S.card - 2 := by
            have hsub : M ⊆ (S.erase x₀).erase z := by
              intro y hy
              obtain ⟨hyW, hyv⟩ := Finset.mem_filter.mp hy
              exact Finset.mem_erase.mpr ⟨fun h => hzne (h ▸ hyv), hyW⟩
            calc M.card ≤ ((S.erase x₀).erase z).card := Finset.card_le_card hsub
            _ = (S.erase x₀).card - 1 := Finset.card_erase_of_mem hzW
            _ = S.card - 2 := by omega
          -- inject T ↦ T.erase x₀ into the 1-subsets of M
          have hmaps : ∀ T ∈ F.filter (fun T => x₀ ∈ T),
              T.erase x₀ ∈ M.powersetCard 1 := by
            intro T hT
            obtain ⟨hTF, hTx⟩ := Finset.mem_filter.mp hT
            rw [hFdef] at hTF
            obtain ⟨hTmem, hTfit⟩ := Finset.mem_filter.mp hTF
            obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hTmem
            refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
            · intro y hy
              obtain ⟨hyx, hyT⟩ := Finset.mem_erase.mp hy
              obtain ⟨q, hqdeg, hqval⟩ := hTfit
              have hq : q = Polynomial.C (q.coeff 0) :=
                Polynomial.eq_C_of_natDegree_le_zero hqdeg
              have hval : u y = u x₀ := by
                rw [hqval y hyT, hqval x₀ hTx, hq]
                simp
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_erase.mpr ⟨hyx, hTsub hyT⟩, hval⟩
            · rw [Finset.card_erase_of_mem hTx, hTcard]
          have hinj : Set.InjOn (fun T : Finset (Fin n) => T.erase x₀)
              ↑(F.filter (fun T => x₀ ∈ T)) := by
            intro T1 hT1 T2 hT2 h12
            have hx1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hT1)).2
            have hx2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hT2)).2
            have h12' : T1.erase x₀ = T2.erase x₀ := h12
            rw [← Finset.insert_erase hx1, ← Finset.insert_erase hx2, h12']
          calc (F.filter (fun T => x₀ ∈ T)).card
              ≤ (M.powersetCard 1).card := Finset.card_le_card_of_injOn _ hmaps hinj
          _ = M.card.choose 1 := Finset.card_powersetCard _ _
          _ = M.card := Nat.choose_one_right _
          _ ≤ (S.card - 2).choose (0 + 1) := by
              rw [Nat.choose_one_right]
              exact hMcard
        -- d ≥ 1: divided-difference descent
        · have hvunfit : ¬ polyFitOn g (d - 1) (S.erase x₀) (divDiff g u x₀) := by
            intro hfit
            have h := (fit_insert_iff_divDiff (G := S.erase x₀) hginj hdpos
              (Finset.notMem_erase x₀ S)).mpr hfit
            rw [Finset.insert_erase hx₀S] at h
            exact hunfit h
          have hmaps : ∀ T ∈ F.filter (fun T => x₀ ∈ T),
              T.erase x₀ ∈ ((S.erase x₀).powersetCard (d + 1)).filter
                (fun G => polyFitOn g (d - 1) G (divDiff g u x₀)) := by
            intro T hT
            obtain ⟨hTF, hTx⟩ := Finset.mem_filter.mp hT
            rw [hFdef] at hTF
            obtain ⟨hTmem, hTfit⟩ := Finset.mem_filter.mp hTF
            obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hTmem
            have hGsub : T.erase x₀ ⊆ S.erase x₀ := fun y hy => by
              obtain ⟨hyx, hyT⟩ := Finset.mem_erase.mp hy
              exact Finset.mem_erase.mpr ⟨hyx, hTsub hyT⟩
            have hGcard : (T.erase x₀).card = d + 1 := by
              rw [Finset.card_erase_of_mem hTx, hTcard]
              omega
            have hGfit : polyFitOn g (d - 1) (T.erase x₀) (divDiff g u x₀) := by
              refine (fit_insert_iff_divDiff hginj hdpos
                (Finset.notMem_erase x₀ T)).mp ?_
              rwa [Finset.insert_erase hTx]
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_powersetCard.mpr ⟨hGsub, hGcard⟩, hGfit⟩
          have hinj : Set.InjOn (fun T : Finset (Fin n) => T.erase x₀)
              ↑(F.filter (fun T => x₀ ∈ T)) := by
            intro T1 hT1 T2 hT2 h12
            have hx1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hT1)).2
            have hx2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hT2)).2
            have h12' : T1.erase x₀ = T2.erase x₀ := h12
            rw [← Finset.insert_erase hx1, ← Finset.insert_erase hx2, h12']
          have hrec : (((S.erase x₀).powersetCard ((d - 1) + 2)).filter
              (fun G => polyFitOn g (d - 1) G (divDiff g u x₀))).card
                ≤ ((S.erase x₀).card - 1).choose ((d - 1) + 2) :=
            ih (d - 1) (S.erase x₀) (divDiff g u x₀) (by omega) hvunfit
          rw [show (d - 1) + 2 = d + 1 from by omega, hWcard,
            show S.card - 1 - 1 = S.card - 2 from by omega] at hrec
          calc (F.filter (fun T => x₀ ∈ T)).card
              ≤ (((S.erase x₀).powersetCard (d + 1)).filter
                  (fun G => polyFitOn g (d - 1) G (divDiff g u x₀))).card :=
                Finset.card_le_card_of_injOn _ hmaps hinj
          _ ≤ (S.card - 2).choose (d + 1) := hrec
      -- Pascal closes
      have hpascal : (S.card - 2).choose (d + 1) + (S.card - 2).choose (d + 2)
          = (S.card - 1).choose (d + 2) := by
        rw [show S.card - 1 = (S.card - 2) + 1 from by omega]
        exact (Nat.choose_succ_succ (S.card - 2) (d + 1)).symm
      omega

open Classical in
/-- **THE ALL-WITNESS FIT-SUBSET BOUND.**  If `u` has no degree-`d` fit on `S` (`|S| = w`),
then at most `C(w−1, d+2)` of the `(d+2)`-subsets of `S` are fit. -/
theorem fit_subsets_card_le {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ}
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j)
    {d : ℕ} {S : Finset (Fin n)} {u : Fin n → ZMod p}
    (hunfit : ¬ polyFitOn g d S u) :
    ((S.powersetCard (d + 2)).filter (fun T => polyFitOn g d T u)).card
      ≤ (S.card - 1).choose (d + 2) :=
  fit_subsets_card_le_aux hginj (d + S.card) d S u le_rfl hunfit

open Classical in
/-- **THE ALL-WITNESS OWNERSHIP FLOOR.**  If `u` has no degree-`d` fit on `S` (`|S| = w`),
then at least `C(w−1, d+1)` of the `(d+2)`-subsets of `S` are unfit — the exact floor: the
single-deviation directions attain it (`deviation_ownership_card`,
`OwnershipCensusSharpened.lean`), so per-witness subset ownership is exact two-sided. -/
theorem unfit_subsets_card_ge {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ}
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j)
    {d : ℕ} {S : Finset (Fin n)} {u : Fin n → ZMod p}
    (hunfit : ¬ polyFitOn g d S u) :
    (S.card - 1).choose (d + 1)
      ≤ ((S.powersetCard (d + 2)).filter (fun T => ¬ polyFitOn g d T u)).card := by
  classical
  have hS1 : 1 ≤ S.card := by
    rcases Nat.eq_zero_or_pos S.card with h0 | h
    · exfalso
      refine hunfit ⟨0, by simp, fun i hi => ?_⟩
      rw [Finset.card_eq_zero.mp h0] at hi
      exact absurd hi (Finset.notMem_empty i)
    · exact h
  have hsplit : ((S.powersetCard (d + 2)).filter (fun T => polyFitOn g d T u)).card
      + ((S.powersetCard (d + 2)).filter (fun T => ¬ polyFitOn g d T u)).card
      = (S.powersetCard (d + 2)).card :=
    Finset.filter_card_add_filter_neg_card_eq_card
      (s := S.powersetCard (d + 2)) (p := fun T => polyFitOn g d T u)
  have htotal : (S.powersetCard (d + 2)).card = S.card.choose (d + 2) :=
    Finset.card_powersetCard _ _
  have hfit := fit_subsets_card_le hginj hunfit
  have hpascal : S.card.choose (d + 2)
      = (S.card - 1).choose (d + 1) + (S.card - 1).choose (d + 2) := by
    rw [show S.card = (S.card - 1) + 1 from by omega]
    rw [show (S.card - 1) + 1 - 1 = S.card - 1 from by omega]
    exact Nat.choose_succ_succ (S.card - 1) (d + 1)
  omega

/-! ## The assembly: `#bad · C(w₀, d+1) ≤ C(n, d+2)` at every radius -/

open Classical in
/-- **The all-witness ownership assembly.**  At witness threshold `w₀` (i.e. radius
`δ` with `w₀ < (1−δ)·n`, so every witness has `≥ w₀+1` points), every stack satisfies

  `#bad · C(w₀, d+1) ≤ C(n, d+2)`

— each bad scalar owns the unfit `(d+2)`-subsets of its witness (at least `C(w₀, d+1)` of
them by the all-witness floor), an owned subset determines its scalar through the line
constraint, and only `C(n, d+2)` subsets exist.  At the band edge `w₀ = d+2` this is the
glueing/sharp law (`C(d+2,d+1) = d+2`); at every deeper threshold it is strictly stronger
than every previously landed per-witness law. -/
theorem allWitness_badScalars_card_mul_le
    {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n] (d w₀ : ℕ)
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j)
    {δ : ℝ≥0} (hδ : ((w₀ : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (u₀ u₁ : Fin n → ZMod p) :
    (Finset.filter (fun γ : ZMod p =>
        mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ u₀ u₁ γ)
        Finset.univ).card * w₀.choose (d + 1)
      ≤ n.choose (d + 2) := by
  classical
  set B := Finset.filter (fun γ : ZMod p =>
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ u₀ u₁ γ)
      Finset.univ with hBdef
  -- witness extraction: size ≥ w₀+1, line degree-d-fit, u₁ NOT fit
  have hwit : ∀ γ ∈ B, ∃ S : Finset (Fin n), w₀ + 1 ≤ S.card ∧
      (∃ qS : Polynomial (ZMod p), qS.natDegree ≤ d ∧
        ∀ i ∈ S, u₀ i + γ * u₁ i = qS.eval (g ^ (i : ℕ))) ∧
      ¬ polyFitOn g d S u₁ := by
    intro γ hγ
    obtain ⟨S, hScard, ⟨w, hwC, hagree⟩, hnojoint⟩ := (Finset.mem_filter.mp hγ).2
    obtain ⟨qS, hqSdeg, hw⟩ := hwC
    have hlin : ∀ i ∈ S, u₀ i + γ * u₁ i = qS.eval (g ^ (i : ℕ)) := by
      intro i hi
      have h := hagree i hi
      rw [hw i, smul_eq_mul] at h
      exact h.symm
    have hSw : w₀ + 1 ≤ S.card := by
      have h2 : ((w₀ : ℕ) : ℝ≥0) < (S.card : ℝ≥0) := lt_of_lt_of_le hδ hScard
      have h2' : w₀ < S.card := by exact_mod_cast h2
      omega
    refine ⟨S, hSw, ⟨qS, hqSdeg, hlin⟩, ?_⟩
    rintro ⟨q₁, hq₁deg, hq₁⟩
    refine hnojoint ⟨fun i => (qS - Polynomial.C γ * q₁).eval (g ^ (i : ℕ)),
      polyEval_mem_evalCode _ (le_trans (Polynomial.natDegree_sub_le _ _)
        (max_le hqSdeg (le_trans (Polynomial.natDegree_C_mul_le _ _) hq₁deg))),
      fun i => q₁.eval (g ^ (i : ℕ)), polyEval_mem_evalCode _ hq₁deg,
      fun i hi => ⟨?_, ?_⟩⟩
    · show (qS - Polynomial.C γ * q₁).eval (g ^ (i : ℕ)) = u₀ i
      have e := hlin i hi
      have e1 := hq₁ i hi
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
      linear_combination γ * e1 - e
    · exact (hq₁ i hi).symm
  choose Sf hSf using hwit
  -- per-scalar owned family: unfit (d+2)-subsets of the witness
  set Pt : {x // x ∈ B} → Finset (Finset (Fin n)) := fun γ =>
    (((Finset.univ : Finset (Fin n)).powersetCard (d + 2)).filter
      (fun R => R ⊆ Sf γ.1 γ.2 ∧ ¬ polyFitOn g d R u₁)) with hPt
  -- THE FLOOR: each bad scalar owns ≥ C(w₀, d+1) unfit subsets.
  have hPr : ∀ γ : {x // x ∈ B}, w₀.choose (d + 1) ≤ (Pt γ).card := by
    intro γ
    obtain ⟨hcard, _, hunfit⟩ := hSf γ.1 γ.2
    have hfloor := unfit_subsets_card_ge hginj hunfit
    have hmono : w₀.choose (d + 1) ≤ ((Sf γ.1 γ.2).card - 1).choose (d + 1) :=
      Nat.choose_le_choose _ (by omega)
    have hsub : ((Sf γ.1 γ.2).powersetCard (d + 2)).filter
        (fun T => ¬ polyFitOn g d T u₁) ⊆ Pt γ := by
      intro R hR
      obtain ⟨hRmem, hRnf⟩ := Finset.mem_filter.mp hR
      obtain ⟨hRsub, hRc⟩ := Finset.mem_powersetCard.mp hRmem
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hRc⟩, hRsub, hRnf⟩
    calc w₀.choose (d + 1) ≤ ((Sf γ.1 γ.2).card - 1).choose (d + 1) := hmono
    _ ≤ (((Sf γ.1 γ.2).powersetCard (d + 2)).filter
          (fun T => ¬ polyFitOn g d T u₁)).card := hfloor
    _ ≤ (Pt γ).card := Finset.card_le_card hsub
  -- disjointness: a common owned subset would fit u₁ (the difference of the two line fits).
  have hPdisj : ∀ γ₁ ∈ B.attach, ∀ γ₂ ∈ B.attach, γ₁ ≠ γ₂ → Disjoint (Pt γ₁) (Pt γ₂) := by
    intro γ₁ _ γ₂ _ hne
    rw [Finset.disjoint_left]
    intro R hR1 hR2
    obtain ⟨_, hRsub1, hRunfit⟩ := Finset.mem_filter.mp hR1
    obtain ⟨_, hRsub2, _⟩ := Finset.mem_filter.mp hR2
    obtain ⟨q₁, hq₁deg, hl1⟩ := (hSf γ₁.1 γ₁.2).2.1
    obtain ⟨q₂, hq₂deg, hl2⟩ := (hSf γ₂.1 γ₂.2).2.1
    have hγne : γ₁.1 - γ₂.1 ≠ 0 := sub_ne_zero.mpr (fun h => hne (Subtype.ext h))
    refine hRunfit ⟨Polynomial.C (γ₁.1 - γ₂.1)⁻¹ * (q₁ - q₂),
      le_trans (Polynomial.natDegree_C_mul_le _ _)
        (le_trans (Polynomial.natDegree_sub_le _ _) (max_le hq₁deg hq₂deg)),
      fun i hi => ?_⟩
    have e1 := hl1 i (hRsub1 hi)
    have e2 := hl2 i (hRsub2 hi)
    have hdiff : (γ₁.1 - γ₂.1) * u₁ i = (q₁ - q₂).eval (g ^ (i : ℕ)) := by
      rw [Polynomial.eval_sub]
      linear_combination e1 - e2
    rw [Polynomial.eval_mul, Polynomial.eval_C, ← hdiff, ← mul_assoc,
      inv_mul_cancel₀ hγne, one_mul]
  -- assemble
  have hbig : B.attach.card * w₀.choose (d + 1) ≤ (B.attach.biUnion Pt).card := by
    rw [Finset.card_biUnion hPdisj]
    calc B.attach.card * w₀.choose (d + 1)
        = ∑ _γ ∈ B.attach, w₀.choose (d + 1) := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun γ _ => hPr γ)
  have hsubE : (B.attach.biUnion Pt) ⊆ (Finset.univ : Finset (Fin n)).powersetCard (d + 2) := by
    intro R hR
    obtain ⟨γ, _, hRP⟩ := Finset.mem_biUnion.mp hR
    exact (Finset.mem_filter.mp hRP).1
  calc B.card * w₀.choose (d + 1) = B.attach.card * w₀.choose (d + 1) := by
        rw [Finset.card_attach]
  _ ≤ (B.attach.biUnion Pt).card := hbig
  _ ≤ (((Finset.univ : Finset (Fin n))).powersetCard (d + 2)).card :=
        Finset.card_le_card hsubE
  _ = n.choose (d + 2) := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

open Classical in
/-- **The all-witness `ε_mca` bound:** at witness threshold `w₀ ≥ d+2`, the MCA error of
the degree-`d` code is at most `(C(n, d+2)/C(w₀, d+1))/p` — the sharpest radius-decoupled
bound per-witness subset counting admits. -/
theorem allWitness_epsMCA_le
    {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n] (d w₀ : ℕ)
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j)
    (hw₀ : d + 1 ≤ w₀)
    {δ : ℝ≥0} (hδ : ((w₀ : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) :
    epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
      ≤ ((n.choose (d + 2) / w₀.choose (d + 1) : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Nonempty (ZMod p) := ⟨0⟩
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card, ZMod.card p]
  simp only [ENNReal.coe_natCast]
  gcongr
  have h2 := allWitness_badScalars_card_mul_le (g := g) d w₀ hginj hδ (u 0) (u 1)
  exact (Nat.le_div_iff_mul_le (Nat.choose_pos hw₀)).mpr h2

/-- **The threshold form**: every radius with witness threshold `w₀` is a good point at the
all-witness budget `(C(n,d+2)/C(w₀,d+1))/p`. -/
theorem le_mcaDeltaStar_allWitness
    {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n] (d w₀ : ℕ)
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j)
    (hw₀ : d + 1 ≤ w₀) {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hδ : ((w₀ : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    {εstar : ℝ≥0∞}
    (hbudget : ((n.choose (d + 2) / w₀.choose (d + 1) : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n d) εstar :=
  le_mcaDeltaStar_of_good _ _ hδ1
    (le_trans (allWitness_epsMCA_le (g := g) d w₀ hginj hw₀ hδ) hbudget)

/-! ## The concrete payoff at the level-1 rung instance: `208/p → 91/p` -/

section Concrete12289

local instance fact_prime_12289_awf : Fact (Nat.Prime 12289) := ⟨by norm_num⟩

open ArkLib.ProximityGap.Level1Rung in
/-- **The sharpened unconditional good side at the level-1 rung instance**: the all-witness
floor at `w₀ = 6` gives `ε_mca(C, δ) ≤ 91/p` for every `δ < 5/8` at the dim-3 code on the
16-point smooth domain in `F₁₂₂₈₉` — `C(16,4)/C(6,3) = 1820/20 = 91`, improving the landed
engine value `208/p` by the factor the deviation ceiling predicted (the "realizable-extremal
cap" of the rung analysis is now the proven engine value). -/
theorem level1_engine_goodSide_F12289_sharp (δ : ℝ≥0) (hδ : δ < 5 / 8) :
    epsMCA (F := ZMod 12289) (evalCode (4134 : ZMod 12289) 16 2) δ
      ≤ (91 : ℝ≥0∞) / (12289 : ℝ≥0∞) := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  have hδ6 : ((6 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin 16) : ℝ≥0) := by
    have hsum : δ + 3 / 8 < 1 := by
      calc δ + 3 / 8 < 5 / 8 + 3 / 8 := by gcongr
      _ = 1 := by norm_num
    have hlt : (3 / 8 : ℝ≥0) < 1 - δ := lt_tsub_iff_right.mpr (by rwa [add_comm] at hsum)
    have hcard : ((Fintype.card (Fin 16) : ℕ) : ℝ≥0) = 16 := by
      rw [Fintype.card_fin]; norm_num
    rw [hcard]
    calc ((6 : ℕ) : ℝ≥0) = (3 / 8 : ℝ≥0) * 16 := by norm_num
    _ < (1 - δ) * 16 := mul_lt_mul_of_pos_right hlt (by norm_num)
  have h := allWitness_epsMCA_le (p := 12289) (g := (4134 : ZMod 12289)) (n := 16)
    2 6 ginj_4134 (by norm_num) hδ6
  have e1 : ((16 : ℕ).choose (2 + 2) / (6 : ℕ).choose (2 + 1) : ℕ) = 91 := rfl
  calc epsMCA (F := ZMod 12289) (evalCode (4134 : ZMod 12289) 16 2) δ
      ≤ (((16 : ℕ).choose (2 + 2) / (6 : ℕ).choose (2 + 1) : ℕ) : ℝ≥0∞)
        / ((12289 : ℕ) : ℝ≥0∞) := h
  _ = (91 : ℝ≥0∞) / (12289 : ℝ≥0∞) := by rw [e1]; norm_num

/-- **Unconditional beyond-Johnson `δ*` lower bound at the small prime, sharpened**: for
every budget `ε* ≥ 91/p`, the threshold of the dim-3 code at `p = 12289` is at least the
level-1 rung `5/8` — strictly beyond Johnson `1 − √(3/16) ≈ 0.567`.  The previous reach was
`ε* ≥ 208/p`; the all-witness floor more than halves the budget edge. -/
theorem deltaStar_ge_level1_radius_F12289_sharp (εstar : ℝ≥0∞)
    (h : (91 : ℝ≥0∞) / (12289 : ℝ≥0∞) ≤ εstar) :
    (5 / 8 : ℝ≥0) ≤ mcaDeltaStar (F := ZMod 12289) (A := ZMod 12289)
      (evalCode (4134 : ZMod 12289) 16 2) εstar := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  by_contra hnot
  rw [not_le] at hnot
  obtain ⟨δ, hδlo, hδhi⟩ := exists_between hnot
  have h58 : (5 / 8 : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by norm_num : (0 : ℝ≥0) < 8)]
    norm_num
  have hgood : δ ≤ mcaDeltaStar (F := ZMod 12289) (A := ZMod 12289)
      (evalCode (4134 : ZMod 12289) 16 2) εstar :=
    le_mcaDeltaStar_of_good _ _ (le_of_lt (lt_of_lt_of_le hδhi h58))
      (le_trans (level1_engine_goodSide_F12289_sharp δ hδhi) h)
  exact absurd hgood (not_le_of_gt hδlo)

end Concrete12289

end ArkLib.ProximityGap.AllWitnessFloor

#print axioms ArkLib.ProximityGap.AllWitnessFloor.fit_subsets_card_le
#print axioms ArkLib.ProximityGap.AllWitnessFloor.unfit_subsets_card_ge
#print axioms ArkLib.ProximityGap.AllWitnessFloor.allWitness_badScalars_card_mul_le
#print axioms ArkLib.ProximityGap.AllWitnessFloor.allWitness_epsMCA_le
#print axioms ArkLib.ProximityGap.AllWitnessFloor.le_mcaDeltaStar_allWitness
#print axioms ArkLib.ProximityGap.AllWitnessFloor.level1_engine_goodSide_F12289_sharp
#print axioms ArkLib.ProximityGap.AllWitnessFloor.deltaStar_ge_level1_radius_F12289_sharp

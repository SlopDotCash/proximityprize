/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandMultiplicity

/-!
# THE FROBENIUS SUBFIELD BLOWUP (#389): the sub-Johnson wall is DOMAIN-coupled

The Cauchy–Schwarz mean-degree law reaches the Johnson agreement `t² ≥ 2(k−1)n` and
stops there sharply: below it, set systems blow up (projective planes).  This file
proves the blowup is **realized by genuine Reed–Solomon agreement families** — so the
sub-Johnson supply statement cannot be rescued by coupling the word alone; it must
couple the *additive structure of the evaluation domain*.

The mechanism (`JH01`/`BSKR06`, here in the #389 charter objects): char `p`, `k = 2`,
the **Frobenius word** `w(z) = z^p`, over any domain whose image is closed under
`𝔽_p`-affine combinations (e.g. the full field `𝔽_{p^e}`).  By Freshman's dream, the
affine codeword `c(z) = z₀^p + u^{p−1}·(z − z₀)` agrees with `w` on the *entire* affine
`𝔽_p`-line `z₀ + 𝔽_p·u`: **every secant of the Frobenius graph is `p`-rich**.  Hence at
level `t = p` (sub-Johnson: `t² = p² ≤ n` once `n = p^e`, `e ≥ 2`):

* `frobenius_supply_floor` — the explainable-`p`-core count is `≥ n(n−1)/(p(p−1))`:
  **quadratic in `n` at fixed `(k, m) = (2, p−3)`**, refuting the linear growth-law
  census conjecture in its any-domain form (the census probes were prime-`q`);
* `frobenius_charter_floor` — the same floor against the named Prop
  `ExplainableCoreSupply`: any admissible `B` has `n(n−1) ≤ p(p−1)·B`;
* `frobenius_mass_floor` / `frobenius_mass_gt_two_n` — the agreement family is
  pairwise-`≤ 1`-intersecting (`frobenius_explainable_inter_le_one`), all members of
  size exactly `p`, with total mass `Σ|A| ≥ n(n−1)/(p−1) > 2n`: **the `2n` mean-degree
  law is FALSE for RS agreement families below Johnson** (at `e = 2` it fails one notch
  below: `t² = n < 2n`), saturating the universal pair bound exactly;
* `frobWord_not_mem_rsCode` — the word is genuinely outside the code.

What survives: `ExplainableCoreSupply` with subexponential `B` (the family here is only
quadratic).  What dies: every route to it that does not use the domain.  Production
smooth domains `μ_n ⊂ 𝔽_q` with `q` prime are immune to this exact mechanism (the only
`𝔽_p`-lines have size `q ≫ n`) — the open core is now provably a statement about the
domain's additive structure.  Probe: `scripts/probes/probe_frobenius_blowup.py`
(exact at `(p,e) = (3,2), (3,3), (5,2)`).  Issue #389.
-/

open Finset Polynomial

namespace ProximityGap.FrobeniusBlowup

open ProximityGap.SpikeFloor ProximityGap.Ownership

variable {F : Type} [Field F]
variable {p : ℕ} [hp : Fact p.Prime] [CharP F p]
variable {n : ℕ} {dom : Fin n ↪ F}

instance moduleInstance_FrobeniusSubfieldBlowup_1 : NeZero p := ⟨hp.out.ne_zero⟩

/-- The canonical embedding `𝔽_p → F` in characteristic `p`. -/
noncomputable abbrev fpCast : ZMod p →+* F := ZMod.castHom (dvd_refl p) F

/-- The domain image is closed under `𝔽_p`-affine combinations: the whole affine
`𝔽_p`-line through any two domain points stays in the domain.  Holds for the full
field `𝔽_{p^e}` and for any `𝔽_p`-affine subspace. -/
def AffClosed (dom : Fin n ↪ F) (p : ℕ) [Fact p.Prime] [CharP F p] : Prop :=
  ∀ (i j : Fin n) (c : ZMod p), ∃ l : Fin n,
    dom l = dom i + fpCast c * (dom j - dom i)

/-- A surjective domain (the full field) is `𝔽_p`-affine-closed. -/
theorem affClosed_of_surjective (dom : Fin n ↪ F) (hdom : Function.Surjective dom) :
    AffClosed dom p :=
  fun i j c => hdom (dom i + fpCast c * (dom j - dom i))

/-- The Frobenius word `w(z) = z^p` over the domain. -/
def frobWord (dom : Fin n ↪ F) (p : ℕ) : Fin n → F := fun i => (dom i) ^ p

/-- The index of the point `dom i + c·(dom j − dom i)` of the secant line. -/
noncomputable def secantIdx (hcl : AffClosed dom p) (i j : Fin n) (c : ZMod p) : Fin n :=
  (hcl i j c).choose

theorem secantIdx_spec (hcl : AffClosed dom p) (i j : Fin n) (c : ZMod p) :
    dom (secantIdx hcl i j c) = dom i + fpCast c * (dom j - dom i) :=
  (hcl i j c).choose_spec

/-- The secant of the Frobenius graph through `i` and `j`: the index set of the
affine `𝔽_p`-line through `dom i` and `dom j`. -/
noncomputable def secant (hcl : AffClosed dom p) (i j : Fin n) : Finset (Fin n) :=
  Finset.univ.image (secantIdx hcl i j)

theorem secantIdx_injective (hcl : AffClosed dom p) {i j : Fin n} (hij : i ≠ j) :
    Function.Injective (secantIdx hcl i j) := by
  intro c c' h
  have h2 : dom i + fpCast c * (dom j - dom i)
      = dom i + fpCast c' * (dom j - dom i) := by
    rw [← secantIdx_spec hcl i j c, ← secantIdx_spec hcl i j c', h]
  have hu : dom j - dom i ≠ 0 := sub_ne_zero.mpr (dom.injective.ne (Ne.symm hij))
  have h3 : fpCast c = fpCast c' :=
    mul_right_cancel₀ hu (add_left_cancel h2)
  exact (fpCast (p := p) (F := F)).injective h3

theorem mem_secant_left (hcl : AffClosed dom p) (i j : Fin n) :
    i ∈ secant hcl i j := by
  refine Finset.mem_image.mpr ⟨0, Finset.mem_univ _, dom.injective ?_⟩
  rw [secantIdx_spec hcl i j 0, map_zero]
  ring

theorem mem_secant_right (hcl : AffClosed dom p) (i j : Fin n) :
    j ∈ secant hcl i j := by
  refine Finset.mem_image.mpr ⟨1, Finset.mem_univ _, dom.injective ?_⟩
  rw [secantIdx_spec hcl i j 1, map_one]
  ring

theorem secant_card (hcl : AffClosed dom p) {i j : Fin n} (hij : i ≠ j) :
    (secant hcl i j).card = p := by
  rw [secant, Finset.card_image_of_injective _ (secantIdx_injective hcl hij),
    Finset.card_univ, ZMod.card]

/-- **The secant law (Freshman's dream)**: the affine codeword
`z₀^p + u^{p−1}(z − z₀)` agrees with the Frobenius word on the whole secant —
every secant of the Frobenius graph is an explainable `p`-core. -/
theorem secant_explainable (hcl : AffClosed dom p) (i j : Fin n) :
    ExplainableOn dom 2 (frobWord dom p) (secant hcl i j) := by
  haveI : ExpChar F p := ExpChar.prime hp.out
  set u : F := dom j - dom i with hu
  refine ⟨fun l => (C (u ^ (p - 1)) * X + C ((dom i) ^ p - u ^ (p - 1) * dom i)).eval
      (dom l), ⟨C (u ^ (p - 1)) * X + C ((dom i) ^ p - u ^ (p - 1) * dom i),
      lt_of_le_of_lt (degree_linear_le) (by decide), rfl⟩, ?_⟩
  intro l hl
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hl
  have hfrob : (dom i + fpCast c * u) ^ p = (dom i) ^ p + fpCast c * u ^ p := by
    rw [add_pow_char, mul_pow, ← map_pow fpCast c p, ZMod.pow_card]
  have hpow : u ^ (p - 1) * u = u ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le]
  simp only [frobWord, eval_add, eval_mul, eval_C, eval_X]
  rw [secantIdx_spec hcl i j c, ← hu, hfrob, ← hpow]
  ring

omit [CharP F p] in
open Classical in
/-- **The agreement cap**: any affine codeword agrees with the Frobenius word on at
most `p` points (root counting on `X^p − P`). -/
theorem frob_agreement_card_le (P : F[X]) (hP : P.degree < 2) :
    (Finset.univ.filter (fun i => P.eval (dom i) = (dom i) ^ p)).card ≤ p := by
  have hplt : P.degree < (X ^ p : F[X]).degree := by
    rw [degree_X_pow]
    exact lt_of_lt_of_le hP (by exact_mod_cast hp.out.two_le)
  have hgdeg : (X ^ p - P : F[X]).degree = p := by
    rw [degree_sub_eq_left_of_degree_lt hplt, degree_X_pow]
  have hg0 : (X ^ p - P : F[X]) ≠ 0 := by
    intro h
    rw [h, degree_zero] at hgdeg
    simp at hgdeg
  have hsub : ∀ i ∈ Finset.univ.filter (fun i => P.eval (dom i) = (dom i) ^ p),
      dom i ∈ (X ^ p - P : F[X]).roots.toFinset := by
    intro i hi
    rw [Multiset.mem_toFinset, mem_roots hg0]
    have hi' := (Finset.mem_filter.mp hi).2
    simp [IsRoot, hi']
  calc (Finset.univ.filter (fun i => P.eval (dom i) = (dom i) ^ p)).card
      ≤ (X ^ p - P : F[X]).roots.toFinset.card :=
        Finset.card_le_card_of_injOn dom hsub dom.injective.injOn
    _ ≤ Multiset.card (X ^ p - P : F[X]).roots := Multiset.toFinset_card_le _
    _ ≤ (X ^ p - P : F[X]).natDegree := card_roots' _
    _ = p := natDegree_eq_of_degree_eq_some hgdeg

open Classical in
/-- The level-`p` explainable-core family of the Frobenius word: the #389 charter's
supply object at `(k, m) = (2, p−3)`. -/
noncomputable def frobFamily (dom : Fin n ↪ F) (p : ℕ) : Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powersetCard p).filter
    (fun T => ExplainableOn dom 2 (frobWord dom p) T)

open Classical in
/-- **THE SUPPLY FLOOR** — the explainable-core count of the Frobenius word is at
least `n(n−1)/(p(p−1))`: quadratic in `n` at fixed `p`.  Every ordered pair of domain
indices lies on its secant, an explainable `p`-core; each `p`-core carries at most
`p(p−1)` ordered pairs. -/
theorem frobenius_supply_floor (hcl : AffClosed dom p) :
    n * n - n ≤ (p * p - p) * (frobFamily dom p).card := by
  have hmaps : ∀ q ∈ (Finset.univ : Finset (Fin n)).offDiag,
      secant hcl q.1 q.2 ∈ frobFamily dom p := by
    intro q hq
    obtain ⟨-, -, hne⟩ := Finset.mem_offDiag.mp hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, secant_card hcl hne⟩, ?_⟩
    exact secant_explainable hcl q.1 q.2
  have h1 : (Finset.univ : Finset (Fin n)).offDiag.card
      = ∑ T ∈ frobFamily dom p, ((Finset.univ : Finset (Fin n)).offDiag.filter
        (fun q => secant hcl q.1 q.2 = T)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have h2 : ∀ T ∈ frobFamily dom p,
      ((Finset.univ : Finset (Fin n)).offDiag.filter
        (fun q => secant hcl q.1 q.2 = T)).card ≤ p * p - p := by
    intro T hT
    have hTcard : T.card = p :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
    have hsub : (Finset.univ : Finset (Fin n)).offDiag.filter
        (fun q => secant hcl q.1 q.2 = T) ⊆ T.offDiag := by
      intro q hq
      obtain ⟨hqo, hfq⟩ := Finset.mem_filter.mp hq
      obtain ⟨-, -, hne⟩ := Finset.mem_offDiag.mp hqo
      exact Finset.mem_offDiag.mpr
        ⟨hfq ▸ mem_secant_left hcl q.1 q.2, hfq ▸ mem_secant_right hcl q.1 q.2, hne⟩
    calc ((Finset.univ : Finset (Fin n)).offDiag.filter
          (fun q => secant hcl q.1 q.2 = T)).card
        ≤ T.offDiag.card := Finset.card_le_card hsub
      _ = p * p - p := by rw [Finset.offDiag_card, hTcard]
  calc n * n - n
      = (Finset.univ : Finset (Fin n)).offDiag.card := by
        rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
    _ = ∑ T ∈ frobFamily dom p, ((Finset.univ : Finset (Fin n)).offDiag.filter
        (fun q => secant hcl q.1 q.2 = T)).card := h1
    _ ≤ ∑ _T ∈ frobFamily dom p, (p * p - p) := Finset.sum_le_sum h2
    _ = (frobFamily dom p).card * (p * p - p) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = (p * p - p) * (frobFamily dom p).card := mul_comm _ _

open Classical in
/-- **THE CHARTER FLOOR** — against the named Prop: any `B` admissible for
`ExplainableCoreSupply dom 2 m B` at the band `2 + m + 1 = p` satisfies
`n(n−1) ≤ p(p−1)·B`.  Quadratic at fixed `(k, m)`: the any-domain linear growth-law
conjecture is false. -/
theorem frobenius_charter_floor {m B : ℕ} (hcl : AffClosed dom p)
    (hm : 2 + m + 1 = p) (hB : ExplainableCoreSupply dom 2 m B) :
    n * n - n ≤ (p * p - p) * B := by
  refine le_trans (frobenius_supply_floor hcl) (Nat.mul_le_mul_left _ ?_)
  have h2 := hB (frobWord dom p)
  rw [hm] at h2
  unfold frobFamily
  convert h2 using 3

open Classical in
/-- The family is pairwise-`≤ 1`-intersecting: two distinct explainable `p`-cores of
the Frobenius word share at most one point (two affine explainers agreeing at two
points coincide; then both cores fill the unique `≤ p`-point agreement set). -/
theorem frobenius_explainable_inter_le_one {T T' : Finset (Fin n)}
    (hT : T ∈ frobFamily dom p) (hT' : T' ∈ frobFamily dom p) (hne : T ≠ T') :
    (T ∩ T').card ≤ 1 := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcon
  obtain ⟨hiT, hiT'⟩ := Finset.mem_inter.mp hi
  obtain ⟨hjT, hjT'⟩ := Finset.mem_inter.mp hj
  obtain ⟨hTmem, cT, hcT, hagrT⟩ := Finset.mem_filter.mp hT
  obtain ⟨hT'mem, cT', hcT', hagrT'⟩ := Finset.mem_filter.mp hT'
  obtain ⟨P, hPdeg, rfl⟩ := hcT
  obtain ⟨P', hP'deg, rfl⟩ := hcT'
  -- the two explainers agree at two distinct domain points, hence coincide
  have hPP' : P = P' := by
    by_contra hPne
    have hsub0 : P - P' ≠ 0 := sub_ne_zero.mpr hPne
    have hd : (P - P').degree < 2 :=
      lt_of_le_of_lt (degree_sub_le _ _) (max_lt hPdeg hP'deg)
    have hnat : (P - P').natDegree < 2 :=
      (natDegree_lt_iff_degree_lt hsub0).mpr hd
    have hroot : ∀ l : Fin n, l ∈ T → l ∈ T' → dom l ∈ (P - P').roots := by
      intro l hlT hlT'
      rw [mem_roots hsub0]
      have e1 := hagrT l hlT
      have e2 := hagrT' l hlT'
      simp only [frobWord] at e1 e2
      simp [IsRoot, e1, e2]
    have hpair : ({dom i, dom j} : Finset F) ⊆ (P - P').roots.toFinset := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Multiset.mem_toFinset.mpr (hroot i hiT hiT')
      · exact Multiset.mem_toFinset.mpr (hroot j hjT hjT')
    have h2le : 2 ≤ (P - P').roots.toFinset.card := by
      calc 2 = ({dom i, dom j} : Finset F).card :=
            (Finset.card_pair (dom.injective.ne hij)).symm
        _ ≤ (P - P').roots.toFinset.card := Finset.card_le_card hpair
    have := le_trans h2le (le_trans (Multiset.toFinset_card_le _) (card_roots' _))
    omega
  -- both cores fill the agreement set of the common explainer
  have hTcard : T.card = p := (Finset.mem_powersetCard.mp hTmem).2
  have hT'card : T'.card = p := (Finset.mem_powersetCard.mp hT'mem).2
  have hagrcard := frob_agreement_card_le (dom := dom) (p := p) P hPdeg
  have hTsub : T ⊆ Finset.univ.filter (fun l => P.eval (dom l) = (dom l) ^ p) := by
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hagrT l hl⟩
  have hT'sub : T' ⊆ Finset.univ.filter (fun l => P.eval (dom l) = (dom l) ^ p) := by
    intro l hl
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [hPP']
    exact hagrT' l hl
  have hTeq : T = Finset.univ.filter (fun l => P.eval (dom l) = (dom l) ^ p) :=
    Finset.eq_of_subset_of_card_le hTsub (le_trans hagrcard (le_of_eq hTcard.symm))
  have hT'eq : T' = Finset.univ.filter (fun l => P.eval (dom l) = (dom l) ^ p) :=
    Finset.eq_of_subset_of_card_le hT'sub (le_trans hagrcard (le_of_eq hT'card.symm))
  exact hne (hTeq.trans hT'eq.symm)

omit hp [CharP F p] in
open Classical in
/-- The family's total agreement mass equals `p · (#family)`. -/
theorem frobenius_mass_eq :
    ∑ T ∈ frobFamily dom p, T.card = p * (frobFamily dom p).card := by
  have h : ∀ T ∈ frobFamily dom p, T.card = p := fun T hT =>
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
  rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, mul_comm]

open Classical in
/-- **THE MASS FLOOR** — the Frobenius agreement family saturates the universal pair
bound: total mass `Σ|A| ≥ n(n−1)/(p−1)`. -/
theorem frobenius_mass_floor (hcl : AffClosed dom p) :
    n * n - n ≤ (p - 1) * ∑ T ∈ frobFamily dom p, T.card := by
  have h1 := frobenius_supply_floor hcl
  rw [frobenius_mass_eq, ← mul_assoc, Nat.sub_one_mul]
  exact h1

open Classical in
/-- **THE `2n` LAW DIES BELOW JOHNSON, IN RS** — once `n ≥ 2p`, the Frobenius
agreement family (pairwise-`≤1`, all sizes exactly `p = t`, sub-Johnson once
`p² ≤ n`) has total mass strictly above `2n`. -/
theorem frobenius_mass_gt_two_n (hcl : AffClosed dom p) (hn : 2 * p ≤ n) :
    2 * n < ∑ T ∈ frobFamily dom p, T.card := by
  have h1 := frobenius_mass_floor hcl
  set u := ∑ T ∈ frobFamily dom p, T.card with hu
  have hp2 : 2 ≤ p := hp.out.two_le
  obtain ⟨d, rfl⟩ : ∃ d, p = d + 2 := ⟨p - 2, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hN : 2 * d + 3 ≤ N := by omega
  have hx : (N + 1) * (N + 1) - (N + 1) = (N + 1) * N := by
    have : (N + 1) * (N + 1) = (N + 1) * N + (N + 1) := by ring
    omega
  rw [hx] at h1
  have hd1 : d + 2 - 1 = d + 1 := by omega
  rw [hd1] at h1
  -- (d+1)·u ≥ (N+1)·N ≥ (N+1)·(2d+3) > (d+1)·(2(N+1))
  have hchain : (d + 1) * (2 * (N + 1)) < (d + 1) * u := by
    calc (d + 1) * (2 * (N + 1)) < (N + 1) * (2 * d + 3) := by nlinarith
      _ ≤ (N + 1) * N := Nat.mul_le_mul_left _ hN
      _ ≤ (d + 1) * u := h1
  exact Nat.lt_of_mul_lt_mul_left hchain

/-- The Frobenius word is not a codeword (its agreement with any affine codeword is
at most `p < n`). -/
theorem frobWord_not_mem_rsCode (hpn : p < n) :
    frobWord dom p ∉ (rsCode dom 2 : Submodule F (Fin n → F)) := by
  classical
  rintro ⟨P, hPdeg, hPeq⟩
  have hall : (Finset.univ.filter (fun i => P.eval (dom i) = (dom i) ^ p))
      = (Finset.univ : Finset (Fin n)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact (congrFun hPeq i).symm
  have hcap := frob_agreement_card_le (dom := dom) (p := p) P hPdeg
  rw [hall, Finset.card_univ, Fintype.card_fin] at hcap
  omega

end ProximityGap.FrobeniusBlowup

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.FrobeniusBlowup.secant_explainable
#print axioms ProximityGap.FrobeniusBlowup.frob_agreement_card_le
#print axioms ProximityGap.FrobeniusBlowup.frobenius_supply_floor
#print axioms ProximityGap.FrobeniusBlowup.frobenius_charter_floor
#print axioms ProximityGap.FrobeniusBlowup.frobenius_explainable_inter_le_one
#print axioms ProximityGap.FrobeniusBlowup.frobenius_mass_floor
#print axioms ProximityGap.FrobeniusBlowup.frobenius_mass_gt_two_n
#print axioms ProximityGap.FrobeniusBlowup.frobWord_not_mem_rsCode

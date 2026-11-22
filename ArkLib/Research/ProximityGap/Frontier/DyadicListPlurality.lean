/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicDifferenceRoots

/-! # Exact maximum total agreements for a prescribed polynomial list

At each site a center can serve its most frequent symbol. A dynamic program
on polynomial gcds and unions computes the sizes of all plurality levels on a
dyadic coset without enumerating sites, received words, or equality partitions.
-/

set_option autoImplicit false
namespace ProximityGap.DyadicListPlurality
open CompPoly Polynomial Finset DyadicDifferenceRoots

variable {F : Type} [Field F] [DecidableEq F]
abbrev Poly (F : Type) [Field F] [DecidableEq F] := CPolynomial F

/-- Nonzero masks are squarefree divisors of the domain polynomial. Zero denotes
every site, including when the message difference vanishes identically. -/
def mask (h : ℕ) (c : F) (p : Poly F) : Poly F :=
  if p == 0 then 0 else if p == 1 then 1 else factor p h c

/-- Union by polynomial lcm. The input masks are already squarefree. -/
def unionMask (p q : Poly F) : Poly F :=
  (p.div (CPolynomial.gcdMonic p q)) * q

/-- Intersection of two masks. -/
def interMask (p q : Poly F) : Poly F := CPolynomial.gcdMonic p q

private def hit (p : Poly F) (z : F) : Prop := p.toPoly.eval z = 0

private theorem mask_hit {h : ℕ} {c z : F} (hz : z ^ (2 ^ h) = c) (p : Poly F) :
    hit (mask h c p) z ↔ hit p z := by
  by_cases hp : p = 0
  · simp [mask, hp]
  by_cases h1 : p = 1
  · simp [mask, h1, hit, CPolynomial.toPoly_one]
  simp only [mask, beq_iff_eq, ite_eq_right hp, ite_eq_right h1]
  change IsRoot (factor p h c).toPoly z ↔ IsRoot p.toPoly z
  rw [← dvd_iff_isRoot, dvd_factor_iff hp, ← dvd_iff_isRoot]
  exact and_iff_left (dvd_iff_isRoot.mpr (by simp [IsRoot.def, hz]))

private theorem union_hit (p q : Poly F) (z : F) :
    hit (unionMask p q) z ↔ hit p z ∨ hit q z := by
  let g := (CPolynomial.gcdMonic p q).toPoly
  have hgcd : g = normalize (EuclideanDomain.gcd p.toPoly q.toPoly) :=
    CPolynomial.gcdMonic_toPoly_eq_normalize_gcd p q
  have h1 : g ∣ p.toPoly := hgcd ▸ normalize_dvd_iff.mpr (EuclideanDomain.gcd_dvd_left _ _)
  have h2 : g ∣ q.toPoly := hgcd ▸ normalize_dvd_iff.mpr (EuclideanDomain.gcd_dvd_right _ _)
  obtain ⟨u, hu⟩ := h1
  obtain ⟨v, hv⟩ := h2
  simp only [hit, unionMask, CPolynomial.toPoly_mul, CPolynomial.div_toPoly_eq_div]
  change ((p.toPoly / g) * q.toPoly).eval z = 0 ↔ _
  rw [hu, hv]
  by_cases hg : g = 0
  · simp [hg]
  rw [mul_div_cancel_left₀ _ hg]
  simp only [eval_mul, mul_eq_zero]
  tauto

private theorem inter_hit (p q : Poly F) (z : F) :
    hit (interMask p q) z ↔ hit p z ∧ hit q z := by
  change IsRoot (CPolynomial.gcdMonic p q).toPoly z ↔ IsRoot p.toPoly z ∧ IsRoot q.toPoly z
  simp only [← dvd_iff_isRoot, CPolynomial.gcdMonic_toPoly_eq_normalize_gcd, dvd_normalize_iff]
  exact ⟨fun h => ⟨h.trans (EuclideanDomain.gcd_dvd_left _ _),
    h.trans (EuclideanDomain.gcd_dvd_right _ _)⟩, fun h => EuclideanDomain.dvd_gcd h.1 h.2⟩

private def before {m : ℕ} (r : Fin (m + 1)) : Fin (m + 1) := ⟨r.val - 1, by omega⟩

/-- A table indexed by thresholds from zero to `m`. The vector caches every
threshold during each update, using at most `m` gcds and unions per input. -/
def levels (m : ℕ) : List (Poly F) → Vector (Poly F) (m + 1)
  | [] => Vector.ofFn fun r => if r.val = 0 then 0 else 1
  | p :: ps =>
    let prev := levels m ps
    Vector.ofFn fun r => if r.val = 0 then 0 else
      unionMask (prev.get r) (interMask (prev.get (before r)) p)

private theorem levels_spec {m : ℕ} (z : F)
    (ps : List (Poly F)) (r : Fin (m + 1)) :
    hit ((levels m ps).get r) z ↔
      r.val ≤ ps.countP (fun p => decide (p.toPoly.eval z = 0)) := by
  induction ps generalizing r with
  | nil =>
    rw [levels, Vector.get_ofFn]
    by_cases hr : r.val = 0
    · rw [ite_eq_left hr]; simp [hr, hit, CPolynomial.toPoly_zero]
    · rw [ite_eq_right hr]; simp [hr, hit, CPolynomial.toPoly_one]
  | cons p ps ih =>
    rw [levels, Vector.get_ofFn]
    by_cases hr : r.val = 0
    · simp [hr, hit, CPolynomial.toPoly_zero]
    rw [ite_eq_right hr, union_hit, inter_hit, ih r, ih (before r)]
    change _ ∨ (r.val - 1 ≤ _ ∧ p.toPoly.eval z = 0) ↔ _
    by_cases hp : p.toPoly.eval z = 0 <;> simp [hp]; omega

private def anyMask (ps : List (Poly F)) : Poly F :=
  ps.foldr unionMask 1

private theorem any_spec (z : F) (ps : List (Poly F)) :
    hit (anyMask ps) z ↔ ∃ p ∈ ps, hit p z := by
  induction ps with
  | nil => simp [anyMask, hit, CPolynomial.toPoly_one]
  | cons p ps ih =>
    change hit (unionMask p (anyMask ps)) z ↔ _
    simp only [union_hit, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨q, hq, h⟩)
      · exact ⟨p, Or.inl rfl, h⟩
      · exact ⟨q, Or.inr hq, h⟩
    · rintro ⟨q, (rfl | hq), h⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, hq, h⟩

/-- A mask for each multiplicity threshold, taken over all potential anchor
messages. Each anchor table is computed once and shared across thresholds. -/
def pluralityLevels (h : ℕ) (c : F) (ps : List (Poly F)) : Vector (Poly F) (ps.length + 1) :=
  let tables := ps.map fun p => levels ps.length (ps.map fun q => mask h c (p - q))
  Vector.ofFn fun r => anyMask (tables.map fun table => table.get r)

/-- The number of messages taking a specified value at one point, counting repetitions. -/
noncomputable def multiplicity (ps : List (Poly F)) (z b : F) : ℕ :=
  ps.countP (fun p => decide (p.toPoly.eval z = b))

/-- Largest multiplicity among all symbols at a point. -/
noncomputable def plurality (ps : List (Poly F)) (z : F) : ℕ :=
  ps.toFinset.sup fun p => multiplicity ps z (p.toPoly.eval z)

private theorem anchorCount_spec {h : ℕ} {c z : F} (hz : z ^ (2 ^ h) = c)
    (ps : List (Poly F)) (p : Poly F) :
    (ps.map (fun q => mask h c (p - q))).countP (fun q => decide (q.toPoly.eval z = 0)) =
      multiplicity ps z (p.toPoly.eval z) := by
  rw [List.countP_map, multiplicity]
  congr 1
  funext q
  apply decide_eq_decide.mpr
  change hit (mask h c (p - q)) z ↔ _
  rw [mask_hit hz]
  rw [hit, CPolynomial.toPoly_sub, eval_sub, sub_eq_zero]
  exact eq_comm

private theorem pluralityLevels_spec {h : ℕ} {c z : F} (hz : z ^ (2 ^ h) = c)
    (ps : List (Poly F)) (r : Fin ps.length) :
    hit ((pluralityLevels h c ps).get r.succ) z ↔ r.val < plurality ps z := by
  rw [pluralityLevels, Vector.get_ofFn, any_spec z, plurality, Finset.lt_sup_iff]
  simp only [List.mem_map, List.mem_toFinset]
  constructor
  · rintro ⟨_, ⟨_, ⟨p, hp, rfl⟩, rfl⟩, hg⟩
    rw [levels_spec z, anchorCount_spec hz] at hg
    exact ⟨p, hp, hg⟩
  · rintro ⟨p, hp, hg⟩
    refine ⟨_, ⟨_, ⟨p, hp, rfl⟩, rfl⟩, ?_⟩
    rwa [levels_spec z, anchorCount_spec hz]

/-- The maximum total agreements achievable by a received word. -/
def capacity (h : ℕ) (c : F) (ps : List (Poly F)) : ℕ :=
  let tables := pluralityLevels h c ps
  ∑ r : Fin ps.length, rootCount (tables.get r.succ) h c

theorem capacity_eq {I : Type} [Fintype I] (D : I ↪ F) {h : ℕ} {c : F}
    (hn : Fintype.card I = 2 ^ h) (hD : ∀ i, D i ^ (2 ^ h) = c) (ps : List (Poly F)) :
    capacity h c ps = ∑ x, plurality ps (D x) := by
  classical
  have count (r : Fin ps.length) : rootCount ((pluralityLevels h c ps).get r.succ) h c =
      ∑ x, if r.val < plurality ps (D x) then 1 else 0 := by
    rw [rootCount_eq D hn hD, ArkLib.ProximityGap.Frontier.QuarterSplitPencilProduct.sites,
      Finset.card_filter]
    apply sum_congr rfl
    intro x _
    have hh := pluralityLevels_spec (hD x) ps r
    unfold hit at hh
    by_cases hl : r.val < plurality ps (D x)
    · simp [hl, hh.mpr hl]
    · simp [hl, mt hh.mp hl]
  unfold capacity
  simp_rw [count]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  have hb : plurality ps (D x) ≤ ps.length := Finset.sup_le fun _ _ => List.countP_le_length
  rw [← Finset.card_filter, ← Fintype.card_subtype]
  exact Fintype.card_fin_lt_of_le hb

private theorem multiplicity_le (ps : List (Poly F)) (z b : F) :
    multiplicity ps z b ≤ plurality ps z := by
  by_cases h : ∃ p ∈ ps, p.toPoly.eval z = b
  · obtain ⟨p, hp, rfl⟩ := h
    exact Finset.le_sup (f := fun p => multiplicity ps z (p.toPoly.eval z))
      (List.mem_toFinset.mpr hp)
  · have he : multiplicity ps z b = 0 := List.countP_eq_zero.mpr fun p hp hn =>
      h ⟨p, hp, of_decide_eq_true hn⟩
    simp [he]

private theorem exists_best (ps : List (Poly F)) (z : F) :
    ∃ b, multiplicity ps z b = plurality ps z := by
  by_cases h : ps.toFinset.Nonempty
  · obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup _ h
      (fun p => multiplicity ps z (p.toPoly.eval z))
    exact ⟨p.toPoly.eval z, hp.symm⟩
  · have he : ps = [] := by simpa using h
    exact ⟨0, by simp [he, multiplicity, plurality]⟩

/-- The returned integer bounds every center and is achieved by a single center,
including for the empty message list. -/
theorem exact {I : Type} [Fintype I] (D : I ↪ F) {h : ℕ} {c : F}
    (hn : Fintype.card I = 2 ^ h) (hD : ∀ i, D i ^ (2 ^ h) = c) (ps : List (Poly F)) :
    (∀ y : I → F, ∑ x, multiplicity ps (D x) (y x) ≤ capacity h c ps) ∧
      ∃ y : I → F, ∑ x, multiplicity ps (D x) (y x) = capacity h c ps := by
  rw [capacity_eq D hn hD]
  constructor
  · exact fun y => sum_le_sum fun x _ => multiplicity_le ps (D x) (y x)
  · choose y hy using fun x => exists_best ps (D x)
    exact ⟨y, sum_congr rfl fun x _ => hy x⟩

/-- A proposed family requiring at least `t` agreements from each of its
messages can be rejected using its computed capacity. A repeated message adds
the corresponding weight to the test. -/
theorem required {I : Type} [Fintype I] (D : I ↪ F) {h t : ℕ} {c : F}
    (hn : Fintype.card I = 2 ^ h) (hD : ∀ i, D i ^ (2 ^ h) = c)
    (ps : List (Poly F)) (y : I → F)
    (ht : ∀ p ∈ ps, t ≤ (univ.filter (fun x => p.toPoly.eval (D x) = y x)).card) :
    ps.length * t ≤ capacity h c ps := by
  have bound (qs : List (Poly F))
      (hq : ∀ p ∈ qs, t ≤ (univ.filter (fun x => p.toPoly.eval (D x) = y x)).card) :
      qs.length * t ≤ ∑ x, multiplicity qs (D x) (y x) := by
    induction qs with
    | nil => simp [multiplicity]
    | cons p qs ih =>
      have hp := hq p List.mem_cons_self
      have hs := ih (fun q hq' => hq q (List.mem_cons_of_mem _ hq'))
      rw [Finset.card_filter] at hp
      have step (x : I) : multiplicity (p :: qs) (D x) (y x) = multiplicity qs (D x) (y x) +
          (if p.toPoly.eval (D x) = y x then 1 else 0) := by
        by_cases he : p.toPoly.eval (D x) = y x <;> simp [multiplicity, he]
      simp only [step, sum_add_distrib, List.length_cons, Nat.succ_mul]
      exact Nat.add_le_add hs hp
  exact (bound ps ht).trans ((exact D hn hD ps).1 y)

/-- Every scalar list overflow gives a table of distinct messages whose every
weighted subfamily passes the center-optimized total agreement test. -/
theorem of_list {I : Type} [Fintype I] (D : I ↪ F) {h k B t : ℕ} {c : F}
    (hn : Fintype.card I = 2 ^ h) (hD : ∀ i, D i ^ (2 ^ h) = c)
    (hk : 0 < k) (ht : t ≤ Fintype.card I)
    (hlist : (B : ℕ∞) < Code.Lambda (ReedSolomon.code D k : Set (I → F))
      (((Fintype.card I - t : ℕ) : ℝ) / Fintype.card I)) :
    ∃ P : Fin (B + 1) → Poly F, Function.Injective P ∧ (∀ i, (P i).natDegree < k) ∧
      ∀ indices : List (Fin (B + 1)), indices.length * t ≤ capacity h c (indices.map P) := by
  classical
  obtain ⟨y, Q, S, hinj, hdeg, hsize, hag, -⟩ :=
    SaturatedListCliques.from_list_at_overlap D (s := 0) (r := 0) hk ht
      (hn ▸ pow_pos (by decide) _) (fun _ _ _ => SimpleGraph.not_cliqueFree_zero) hlist
  let P (i) := CPolynomial.ringEquiv.symm (Q i)
  have hP i : (P i).toPoly = Q i := CPolynomial.ringEquiv.apply_symm_apply _
  refine ⟨P, CPolynomial.ringEquiv.symm.injective.comp hinj, fun i => ?_, fun idx => ?_⟩
  · simpa only [CPolynomial.natDegree_toPoly, hP] using hdeg i
  · rw [← List.length_map (f := P) (as := idx)]
    apply required D hn hD _ y
    intro p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    rw [← hsize i]
    exact card_le_card fun x hx => mem_filter.mpr ⟨mem_univ _, by rw [hP i]; exact hag i x hx⟩

section
open ArkLib.ProximityGap
local instance : Fact (Nat.Prime PrizeShapePrimeP30.P) := ⟨PrizeShapePrimeP30.prime_P⟩
private abbrev TestField := ZMod PrizeShapePrimeP30.P
private def x : Poly TestField := CPolynomial.X
private def i₄ : TestField := 125829621549097067457234094028236226857884909488

set_option maxRecDepth 8000 in
/-- Both triples have one coincidence for each message pair. A common triple
intersection reduces the attainable total by one on the first named subgroup. -/
theorem first_prime_triples :
    let a : Poly TestField := x - 1
    let b : Poly TestField := 1 - x
    let f : Poly TestField := CPolynomial.C i₄ * (x + 1)
    rootCount a 30 1 = 1 ∧ rootCount b 30 1 = 1 ∧ rootCount (a - b) 30 1 = 1 ∧
    rootCount f 30 1 = 1 ∧ rootCount (a - f) 30 1 = 1 ∧
    capacity 30 (1 : TestField) [0, a, b] = 1073741826 ∧
    capacity 30 (1 : TestField) [0, a, f] = 1073741827 := by
  decide +kernel

end

#print axioms first_prime_triples
#print axioms of_list
#print axioms exact
end ProximityGap.DyadicListPlurality

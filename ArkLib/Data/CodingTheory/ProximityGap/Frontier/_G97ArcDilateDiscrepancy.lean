/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G80ZArcArithmeticInstantiation

/-!
# LANE G97 (#466, 2026-07-10): combinatorial discrepancy of the arc x dilate incidence
  system — the prefix reduction of the G80Z consumer, and the transference NO-GO

First contact of the combinatorial-discrepancy toolbox (Beck–Fiala / Banaszczyk vector
balancing / hereditary discrepancy ~ gamma_2 factorization norm (MNT) / LSV transference)
with the arc-equidistribution certificate that tool-shape doctrine v2 identifies as the one
missing non-Fourier input. Disambiguation: `Banaszczyk` in this tree so far means only the
LATTICE transference bound (`_FullRankLatticeTransferenceNoGo.lean` etc.), and the
R367/G77 "signed pair discrepancy" is a Fourier-gauge moment object — both are different
objects from the set-system (red-blue / hereditary) discrepancy studied here.

## Probe summary (probe_g97_arc_dilate_discrepancy.py, 2026-07-10)

For toy `p` with `n | p-1`, `mu_n` the order-`n` subgroup, dilate cosets `b·mu_n`, arcs at
scale `K ~ sqrt n` (rows `(arc j, dilate b)`, columns `mu_n`):

* specific-set measure discrepancy `D(b·mu_n) = sup_t |#{x : val(bx) < t} - n·t/p|` sits at
  `0.26–0.39 · sqrt(n log p)` (max over cosets; median `~0.22`), i.e. exactly square-root
  scale, and its distribution over cosets MATCHES random `n`-subsets of `F_p` — `mu_n` is
  TYPICAL within the system, not atypically good;
* system hereditary-discrepancy proxies stay bounded/polylog: determinant lower bound
  (LSV) `detlb in [1.00, 1.14]`, gamma_2 trace lower bound `in [1.6, 2.9]`, local-search
  red-blue coloring discrepancy upper bound `1..6` up to a `216 x 341` matrix;
* SEPARATION: specific-set arc deviation / coloring-disc grows `1.8x -> 19x` with `n`.

So the arc x dilate system (multiplicatively translated intervals = intervals in
`k = (p-1)/n` circular orders of the same ground set, the `k`-PERMUTATION discrepancy
problem, intermediate between intervals `O(1)` and Roth's APs `n^{1/4}`) has TINY red-blue
discrepancy — and that is precisely why LSV transference CANNOT produce the certificate:
hereditary discrepancy controls the best ROUNDING of a fractional vector, never the
deviation of the one specific 0/1 vector `1_{mu_n}`.

## What is formalized (all axiom-clean)

1. `signedPrefix_eq_parity` / `abs_sum_interval_le_one` / `hereditary_interval_disc_le_one`:
   the alternating coloring `x ↦ (-1)^{rank_S(x)}` keeps EVERY prefix sum in `{0,1}`, hence
   every interval sum in `[-1,1]`, for EVERY ground set `S` — the interval system has
   hereditary discrepancy exactly `1` (`interval_disc_ge_one` gives the matching lower
   bound on unimodular colorings).
2. `arcIndex_eq_iff` / `scaledPrefix_succ` / `arc_card_dev_le_two_mul`: the G80Z consumer's
   arc `{y : arcIndex K y = j}` is EXACTLY the difference of two scaled prefixes, so any
   prefix-equidistribution bound `eps` gives every arc deviation `<= 2·eps`.
3. `charSum_norm_le_of_scaledPrefix_equidistribution` (CAPSTONE): composed with the G80Z
   consumer's contrapositive — if all `K+1` scaled prefix counts of `S ⊆ ZMod p` are within
   `eps` of uniform, then `‖∑_{y∈S} e(val y/p)‖ ≤ #S·(2π/K) + 2·eps·K`. The missing
   non-Fourier certificate is thereby reduced from all arcs to `K+1` PREFIX counts of the
   dilated subgroup.
4. `per_dilate_arc_coloring`: for each FIXED dilate/scale, some ±1 coloring balances all
   arcs to `≤ 1` — the k-permutation identification: per-row-block the system is an
   interval system in a permuted order; only simultaneity across dilates costs anything.
5. `specific_set_escapes_hereditary_control` + `hereditary_control_cannot_yield_certificate`
   (NO-GO): the interval system has hereditary coloring discrepancy `≤ 1` uniformly, yet
   the SPECIFIC-set measure discrepancy `|#(S ∩ prefix) - #S·t/N|` is unbounded over
   instances. Hence no functional bound `specific-set disc ≤ f(herdisc)` exists: the
   LSV/Banaszczyk/MNT transference route to the arc certificate is structurally closed.

## Honest scope

Nothing here bounds the prefix deviation of `b·mu_n` itself; the prize input remains the
open non-Fourier anti-concentration certificate (BGK/Cilleruelo–Garaev face). What this
lane adds: (a) the certificate's test family shrinks from arcs to prefixes with zero loss
beyond a factor 2 (machine-checked against the G80Z consumer), and (b) the entire
hereditary-discrepancy/transference toolbox is now a mapped no-go, with the toy-scale
gamma_2/detlb/coloring numerics recorded above. CORE remains OPEN / ON-BGK.

Issue #466. Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false


open Finset

namespace ArkLib.ProximityGap.Frontier.G97ArcDilateDiscrepancy

/-! ## Part 1: the alternating coloring — interval herdisc = 1 on every ground set -/

/-- The alternating coloring of a ground set `S ⊆ ℕ`: `x ↦ (-1)^{#{y ∈ S : y < x}}`
(sign by rank in the sorted order). -/
def altSign (S : Finset ℕ) (x : ℕ) : ℤ := (-1) ^ ((S.filter (fun y => y < x)).card)

/-- The signed prefix sum of the alternating coloring up to `t`. -/
def signedPrefix (S : Finset ℕ) (t : ℕ) : ℤ :=
  ∑ x ∈ S.filter (fun y => y < t), altSign S x

theorem altSign_eq_one_or_neg_one (S : Finset ℕ) (x : ℕ) :
    altSign S x = 1 ∨ altSign S x = -1 := by
  rcases Nat.even_or_odd ((S.filter (fun y => y < x)).card) with he | ho
  · exact Or.inl (by rw [altSign, he.neg_one_pow])
  · exact Or.inr (by rw [altSign, ho.neg_one_pow])

private lemma filter_lt_succ (S : Finset ℕ) (t : ℕ) (ht : t ∈ S) :
    S.filter (fun y => y < t + 1) = insert t (S.filter (fun y => y < t)) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hx, hlt⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
    · exact Or.inr ⟨hx, h⟩
    · exact Or.inl h
  · rintro (rfl | ⟨hx, hlt⟩)
    · exact ⟨ht, Nat.lt_succ_self _⟩
    · exact ⟨hx, Nat.lt_succ_of_lt hlt⟩

private lemma filter_lt_succ_of_notMem (S : Finset ℕ) (t : ℕ) (ht : t ∉ S) :
    S.filter (fun y => y < t + 1) = S.filter (fun y => y < t) := by
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, hlt⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
    · exact ⟨hx, h⟩
    · exact absurd (h ▸ hx) ht
  · rintro ⟨hx, hlt⟩
    exact ⟨hx, Nat.lt_succ_of_lt hlt⟩

/-- **The prefix sums of the alternating coloring are exactly the parity of the prefix
count**: `signedPrefix S t = card % 2 ∈ {0,1}`. This is the exact form of
`herdisc(prefixes) ≤ 1`, hereditary because `S` is arbitrary. -/
theorem signedPrefix_eq_parity (S : Finset ℕ) (t : ℕ) :
    signedPrefix S t =
      if Even ((S.filter (fun y => y < t)).card) then 0 else 1 := by
  induction t with
  | zero =>
      have h : S.filter (fun y => y < 0) = ∅ :=
        Finset.filter_false_of_mem (fun x _ => Nat.not_lt_zero x)
      simp [signedPrefix, h]
  | succ t ih =>
      by_cases ht : t ∈ S
      · have hnot : t ∉ S.filter (fun y => y < t) := by simp
        have hsplit := filter_lt_succ S t ht
        have hstep : signedPrefix S (t + 1) = altSign S t + signedPrefix S t := by
          simp only [signedPrefix]
          rw [hsplit, Finset.sum_insert hnot]
        have hcard : (S.filter (fun y => y < t + 1)).card
            = (S.filter (fun y => y < t)).card + 1 := by
          rw [hsplit, Finset.card_insert_of_notMem hnot]
        rw [hstep, ih, hcard]
        simp only [altSign]
        rcases Nat.even_or_odd ((S.filter (fun y => y < t)).card) with he | ho
        · have hne1 : ¬ Even ((S.filter (fun y => y < t)).card + 1) := by
            rw [Nat.even_iff] at he ⊢
            omega
          rw [he.neg_one_pow, if_pos he, if_neg hne1]
          norm_num
        · have hne : ¬ Even ((S.filter (fun y => y < t)).card) := by
            rw [Nat.even_iff]
            rw [Nat.odd_iff] at ho
            omega
          have he1 : Even ((S.filter (fun y => y < t)).card + 1) := by
            rw [Nat.even_iff]
            rw [Nat.odd_iff] at ho
            omega
          rw [ho.neg_one_pow, if_neg hne, if_pos he1]
          norm_num
      · have hsplit := filter_lt_succ_of_notMem S t ht
        have h1 : signedPrefix S (t + 1) = signedPrefix S t := by
          simp only [signedPrefix]
          rw [hsplit]
        rw [h1, hsplit]
        exact ih

theorem signedPrefix_eq_zero_or_one (S : Finset ℕ) (t : ℕ) :
    signedPrefix S t = 0 ∨ signedPrefix S t = 1 := by
  rw [signedPrefix_eq_parity]
  split <;> simp

/-- Every interval sum of the alternating coloring is a difference of two prefix sums. -/
theorem sum_interval_eq_signedPrefix_sub (S : Finset ℕ) {a b : ℕ} (hab : a ≤ b) :
    ∑ x ∈ S.filter (fun y => a ≤ y ∧ y < b), altSign S x
      = signedPrefix S b - signedPrefix S a := by
  have hsplit : S.filter (fun y => y < b)
      = S.filter (fun y => y < a) ∪ S.filter (fun y => a ≤ y ∧ y < b) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hx, hlt⟩
      by_cases hxa : x < a
      · exact Or.inl ⟨hx, hxa⟩
      · exact Or.inr ⟨hx, Nat.le_of_not_lt hxa, hlt⟩
    · rintro (⟨hx, hlt⟩ | ⟨hx, -, hlt⟩)
      · exact ⟨hx, lt_of_lt_of_le hlt hab⟩
      · exact ⟨hx, hlt⟩
  have hdisj : Disjoint (S.filter (fun y => y < a))
      (S.filter (fun y => a ≤ y ∧ y < b)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨-, hlt⟩ := Finset.mem_filter.mp hx
    obtain ⟨-, hge, -⟩ := Finset.mem_filter.mp hx'
    exact absurd hge (Nat.not_le.mpr hlt)
  have hsum : signedPrefix S b
      = signedPrefix S a + ∑ x ∈ S.filter (fun y => a ≤ y ∧ y < b), altSign S x := by
    simp only [signedPrefix]
    rw [hsplit, Finset.sum_union hdisj]
  omega

/-- **Interval discrepancy ≤ 1, hereditarily**: the alternating coloring of ANY ground set
balances every interval `[a, b)` to within `1`. -/
theorem abs_sum_interval_le_one (S : Finset ℕ) {a b : ℕ} (hab : a ≤ b) :
    |∑ x ∈ S.filter (fun y => a ≤ y ∧ y < b), altSign S x| ≤ 1 := by
  rw [sum_interval_eq_signedPrefix_sub S hab]
  rcases signedPrefix_eq_zero_or_one S a with h1 | h1 <;>
    rcases signedPrefix_eq_zero_or_one S b with h2 | h2 <;>
      rw [h1, h2] <;> norm_num

/-- **Hereditary discrepancy of the interval system is ≤ 1** (existential coloring form,
for every ground set — hence for every restriction). -/
theorem hereditary_interval_disc_le_one (S : Finset ℕ) :
    ∃ χ : ℕ → ℤ, (∀ x, χ x = 1 ∨ χ x = -1) ∧
      ∀ a b : ℕ, a ≤ b → |∑ x ∈ S.filter (fun y => a ≤ y ∧ y < b), χ x| ≤ 1 :=
  ⟨altSign S, altSign_eq_one_or_neg_one S, fun _ _ hab => abs_sum_interval_le_one S hab⟩

/-- Matching lower bound: no unimodular coloring beats `1` (herdisc = 1 exactly). -/
theorem interval_disc_ge_one (χ : ℕ → ℤ) (hχ : χ 0 = 1 ∨ χ 0 = -1) :
    ∃ (S : Finset ℕ) (a b : ℕ), a ≤ b ∧
      1 ≤ |∑ x ∈ S.filter (fun y => a ≤ y ∧ y < b), χ x| := by
  refine ⟨{0}, 0, 1, Nat.zero_le 1, ?_⟩
  have h : ({0} : Finset ℕ).filter (fun y => 0 ≤ y ∧ y < 1) = {0} :=
    Finset.filter_true_of_mem (by intro x hx; simp only [Finset.mem_singleton] at hx; omega)
  rw [h, Finset.sum_singleton]
  rcases hχ with h1 | h1 <;> rw [h1] <;> norm_num

/-! ## Part 2: the arc = prefix-difference bridge on `ZMod p` (G80Z consumer language) -/

open ArkLib.ProximityGap.Frontier.G80ZArcArithmeticInstantiation

variable {p : ℕ} [NeZero p]

/-- Prefix count of `S ⊆ ZMod p` in the `K`-scaled value variable:
`#{y ∈ S : K·val(y) < c}`. The consumer's arcs are exactly differences of these. -/
def scaledPrefix (K : ℕ) (S : Finset (ZMod p)) (c : ℕ) : ℕ :=
  (S.filter (fun y => K * y.val < c)).card

/-- The consumer's arc assignment is the floor cell:
`arcIndex K y = j ↔ j·p ≤ K·val(y) < (j+1)·p`. -/
theorem arcIndex_eq_iff {K j : ℕ} (y : ZMod p) :
    arcIndex K y = j ↔ j * p ≤ K * y.val ∧ K * y.val < (j + 1) * p := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  rw [arcIndex]
  constructor
  · rintro rfl
    refine ⟨Nat.div_mul_le_self (K * y.val) p, ?_⟩
    exact (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self _)
  · rintro ⟨h1, h2⟩
    have hle : j ≤ K * y.val / p := (Nat.le_div_iff_mul_le hp).mpr h1
    have hlt : K * y.val / p < j + 1 := (Nat.div_lt_iff_lt_mul hp).mpr h2
    omega

/-- **Arc occupancy = difference of two scaled prefixes** (exact ℕ identity). -/
theorem scaledPrefix_succ (S : Finset (ZMod p)) (K j : ℕ) :
    scaledPrefix K S ((j + 1) * p)
      = scaledPrefix K S (j * p) + (S.filter (fun y => arcIndex K y = j)).card := by
  have hmul : j * p ≤ (j + 1) * p := mul_le_mul_right' (Nat.le_succ j) p
  have hsplit : S.filter (fun y => K * y.val < (j + 1) * p)
      = S.filter (fun y => K * y.val < j * p)
        ∪ S.filter (fun y => arcIndex K y = j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hx, hlt⟩
      by_cases hxa : K * x.val < j * p
      · exact Or.inl ⟨hx, hxa⟩
      · exact Or.inr ⟨hx, (arcIndex_eq_iff x).mpr ⟨Nat.le_of_not_lt hxa, hlt⟩⟩
    · rintro (⟨hx, hlt⟩ | ⟨hx, hj⟩)
      · exact ⟨hx, lt_of_lt_of_le hlt hmul⟩
      · exact ⟨hx, ((arcIndex_eq_iff x).mp hj).2⟩
  have hdisj : Disjoint (S.filter (fun y => K * y.val < j * p))
      (S.filter (fun y => arcIndex K y = j)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨-, hlt⟩ := Finset.mem_filter.mp hx
    obtain ⟨-, hj⟩ := Finset.mem_filter.mp hx'
    exact absurd ((arcIndex_eq_iff x).mp hj).1 (Nat.not_le.mpr hlt)
  rw [scaledPrefix, scaledPrefix, hsplit, Finset.card_union_of_disjoint hdisj]

/-- **Prefix control transfers to arc control with factor 2**: if both bounding prefixes
deviate from references `u, v` by at most `ε`, the arc occupancy deviates from `v - u`
by at most `2ε`. -/
theorem arc_card_dev_le_two_mul (S : Finset (ZMod p)) (K j : ℕ) {u v ε : ℝ}
    (h1 : |(scaledPrefix K S (j * p) : ℝ) - u| ≤ ε)
    (h2 : |(scaledPrefix K S ((j + 1) * p) : ℝ) - v| ≤ ε) :
    |((S.filter (fun y => arcIndex K y = j)).card : ℝ) - (v - u)| ≤ 2 * ε := by
  have h := scaledPrefix_succ S K j
  have hcast : ((S.filter (fun y => arcIndex K y = j)).card : ℝ)
      = (scaledPrefix K S ((j + 1) * p) : ℝ) - (scaledPrefix K S (j * p) : ℝ) := by
    have h' : (scaledPrefix K S ((j + 1) * p) : ℝ)
        = (scaledPrefix K S (j * p) : ℝ)
          + ((S.filter (fun y => arcIndex K y = j)).card : ℝ) := by
      exact_mod_cast h
    linarith
  rw [hcast]
  have hkey : (scaledPrefix K S ((j + 1) * p) : ℝ) - (scaledPrefix K S (j * p) : ℝ)
      - (v - u)
      = ((scaledPrefix K S ((j + 1) * p) : ℝ) - v)
        + (u - (scaledPrefix K S (j * p) : ℝ)) := by
    ring
  rw [hkey]
  calc |((scaledPrefix K S ((j + 1) * p) : ℝ) - v)
        + (u - (scaledPrefix K S (j * p) : ℝ))|
      ≤ |(scaledPrefix K S ((j + 1) * p) : ℝ) - v|
        + |u - (scaledPrefix K S (j * p) : ℝ)| := abs_add_le _ _
    _ = |(scaledPrefix K S ((j + 1) * p) : ℝ) - v|
        + |(scaledPrefix K S (j * p) : ℝ) - u| := by rw [abs_sub_comm u]
    _ ≤ ε + ε := add_le_add h2 h1
    _ = 2 * ε := by ring

/-! ## Part 3: composition with the G80Z consumer — the PREFIX form of the certificate -/

/-- **CAPSTONE — the missing non-Fourier certificate reduces to `K+1` prefix counts.**
If every scaled prefix count of `S ⊆ ZMod p` at the arc boundaries `j·p`, `j ≤ K`, is
within `ε` of the uniform reference `#S·j/K`, then the standard character sum obeys
`‖∑_{y∈S} e(val y/p)‖ ≤ #S·(2π/K) + 2·ε·K`. (Contrapositive composition of
`exists_arc_deviation_of_charSum_bias` with the arc = prefix-difference bridge.)
At `S = b·μ_n`, `K ≍ n/√(n log q)`, `ε ≍ √(n log q)`, this is the square-root-scale
Fourier bound `‖η_b‖ ≲ √(n log q)` from a purely order-theoretic prefix input. -/
theorem charSum_norm_le_of_scaledPrefix_equidistribution
    (S : Finset (ZMod p)) {K : ℕ} (hK : 2 ≤ K) {ε : ℝ}
    (hpre : ∀ j ≤ K,
      |(scaledPrefix K S (j * p) : ℝ) - (S.card : ℝ) * (j : ℝ) / (K : ℝ)| ≤ ε) :
    ‖∑ y ∈ S, Complex.exp ((charPhase y : ℂ) * Complex.I)‖ ≤
      (S.card : ℝ) * (2 * Real.pi / K) + 2 * ε * K := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hm : (0 : ℝ) ≤ (S.card : ℝ) / (K : ℝ) := by positivity
  obtain ⟨j, hjmem, hdev⟩ := exists_arc_deviation_of_charSum_bias S hK
    (‖∑ y ∈ S, Complex.exp ((charPhase y : ℂ) * Complex.I)‖)
    ((S.card : ℝ) / (K : ℝ)) hm (le_refl _)
  have hj : j < K := Finset.mem_range.mp hjmem
  have h1 := hpre j (le_of_lt hj)
  have h2 := hpre (j + 1) (by omega)
  have harc := arc_card_dev_le_two_mul S K j h1 h2
  have hvu : (S.card : ℝ) * ((j + 1 : ℕ) : ℝ) / (K : ℝ)
      - (S.card : ℝ) * (j : ℝ) / (K : ℝ) = (S.card : ℝ) / (K : ℝ) := by
    push_cast
    ring
  rw [hvu] at harc
  have hchain := le_trans hdev harc
  have hmul := (div_le_iff₀ hK0).mp hchain
  linarith

/-! ## Part 4: the k-permutation identification and the transference NO-GO -/

/-- **Per-dilate arc balancing is free** (the k-permutation identification): for every
`S ⊆ ZMod p` and every arc scale `K > 0`, SOME ±1 coloring balances every arc to `≤ 1` —
each fixed dilate/scale block of the arc x dilate system is an interval system in a
permuted (here: value-scaled) order, so its discrepancy is `≤ 1`. The entire difficulty of
the system is simultaneity across dilates; and by Part 5 even full simultaneous balancing
would not control the specific set `b·μ_n`. -/
theorem per_dilate_arc_coloring (S : Finset (ZMod p)) {K : ℕ} (hK : 0 < K) :
    ∃ χ : ZMod p → ℤ, (∀ y, χ y = 1 ∨ χ y = -1) ∧
      ∀ j : ℕ, |∑ y ∈ S.filter (fun y => arcIndex K y = j), χ y| ≤ 1 := by
  classical
  refine ⟨fun y => altSign (S.image (fun z => K * z.val)) (K * y.val),
    fun y => altSign_eq_one_or_neg_one _ _, fun j => ?_⟩
  show |∑ y ∈ S.filter (fun y => arcIndex K y = j),
      altSign (S.image (fun z => K * z.val)) (K * y.val)| ≤ 1
  have hmul : j * p ≤ (j + 1) * p := mul_le_mul_right' (Nat.le_succ j) p
  have hinj : ∀ x ∈ S.filter (fun y => arcIndex K y = j),
      ∀ y ∈ S.filter (fun y => arcIndex K y = j), K * x.val = K * y.val → x = y :=
    fun x _ y _ h => ZMod.val_injective p (Nat.eq_of_mul_eq_mul_left hK h)
  have himg : (S.filter (fun y => arcIndex K y = j)).image (fun z => K * z.val)
      = (S.image (fun z => K * z.val)).filter
          (fun t => j * p ≤ t ∧ t < (j + 1) * p) := by
    ext t
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨y, ⟨hyS, hyj⟩, rfl⟩
      exact ⟨⟨y, hyS, rfl⟩, (arcIndex_eq_iff y).mp hyj⟩
    · rintro ⟨⟨y, hyS, rfl⟩, hint⟩
      exact ⟨y, ⟨hyS, (arcIndex_eq_iff y).mpr hint⟩, rfl⟩
  have hsum : ∑ y ∈ S.filter (fun y => arcIndex K y = j),
      altSign (S.image (fun z => K * z.val)) (K * y.val)
      = ∑ t ∈ (S.image (fun z => K * z.val)).filter
          (fun t => j * p ≤ t ∧ t < (j + 1) * p),
          altSign (S.image (fun z => K * z.val)) t := by
    rw [← himg, Finset.sum_image hinj]
  rw [hsum]
  exact abs_sum_interval_le_one _ hmul

/-- **The transference NO-GO, quantitative core**: the SPECIFIC-set measure discrepancy
`|#(S ∩ [0,t)) - #S·t/N|` is unbounded over instances `(N, t, S ⊆ [0,N))` — even though
(by `hereditary_interval_disc_le_one`) the interval system has hereditary red-blue
discrepancy `≤ 1` on every one of these ground sets. Witness: the left half `S = [0, m)`
of `[0, 2m)` at `t = m` deviates by `m/2`. -/
theorem specific_set_escapes_hereditary_control (C : ℝ) :
    ∃ (N t : ℕ) (S : Finset ℕ), S ⊆ Finset.range N ∧ t ≤ N ∧
      C < |((S.filter (fun y => y < t)).card : ℝ)
        - (S.card : ℝ) * (t : ℝ) / (N : ℝ)| := by
  set m : ℕ := 2 * (⌈C⌉₊ + 1) with hm
  refine ⟨2 * m, m, Finset.range m, ?_, ?_, ?_⟩
  · exact Finset.range_subset_range.mpr (by omega)
  · omega
  have hfilter : (Finset.range m).filter (fun y => y < m) = Finset.range m :=
    Finset.filter_true_of_mem (fun x hx => Finset.mem_range.mp hx)
  rw [hfilter, Finset.card_range]
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hX : (m : ℝ) - (m : ℝ) * (m : ℝ) / ((2 * m : ℕ) : ℝ) = (m : ℝ) / 2 := by
    have hne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
    push_cast
    field_simp
    ring
  rw [hX, abs_of_nonneg (by positivity)]
  have h1 : C ≤ ((⌈C⌉₊ : ℕ) : ℝ) := Nat.le_ceil C
  have h2 : (m : ℝ) = 2 * (((⌈C⌉₊ : ℕ) : ℝ) + 1) := by
    rw [hm]
    push_cast
    ring
  linarith

/-- **Headline NO-GO**: hereditary interval discrepancy is `≤ 1` on EVERY ground set,
yet specific-set measure discrepancy is unbounded — so no bound of the shape
`specific-set deviation ≤ f(hereditary discrepancy)` can exist, and the
Lovász–Spencer–Vesztergombi / Banaszczyk / Matoušek–Nikolov–Talwar transference toolbox
cannot, by itself, produce the arc-occupancy certificate the G80Z consumer needs: it
controls the best ROUNDING of the uniform fractional vector, never the one specific
indicator `1_{b·μ_n}`. -/
theorem hereditary_control_cannot_yield_certificate :
    (∀ S : Finset ℕ, ∃ χ : ℕ → ℤ, (∀ x, χ x = 1 ∨ χ x = -1) ∧
        ∀ a b : ℕ, a ≤ b → |∑ x ∈ S.filter (fun y => a ≤ y ∧ y < b), χ x| ≤ 1) ∧
      (∀ C : ℝ, ∃ (N t : ℕ) (S : Finset ℕ), S ⊆ Finset.range N ∧ t ≤ N ∧
        C < |((S.filter (fun y => y < t)).card : ℝ)
          - (S.card : ℝ) * (t : ℝ) / (N : ℝ)|) :=
  ⟨hereditary_interval_disc_le_one, specific_set_escapes_hereditary_control⟩

end ArkLib.ProximityGap.Frontier.G97ArcDilateDiscrepancy

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G97ArcDilateDiscrepancy.signedPrefix_eq_parity
#print axioms
  ArkLib.ProximityGap.Frontier.G97ArcDilateDiscrepancy.abs_sum_interval_le_one
#print axioms
  ArkLib.ProximityGap.Frontier.G97ArcDilateDiscrepancy.hereditary_interval_disc_le_one
#print axioms
  ArkLib.ProximityGap.Frontier.G97ArcDilateDiscrepancy.interval_disc_ge_one
#print axioms
  ArkLib.ProximityGap.Frontier.G97ArcDilateDiscrepancy.arcIndex_eq_iff
#print axioms
  ArkLib.ProximityGap.Frontier.G97ArcDilateDiscrepancy.scaledPrefix_succ
#print axioms
  ArkLib.ProximityGap.Frontier.G97ArcDilateDiscrepancy.arc_card_dev_le_two_mul
#print axioms
  ArkLib.ProximityGap.Frontier.G97ArcDilateDiscrepancy.charSum_norm_le_of_scaledPrefix_equidistribution
#print axioms
  ArkLib.ProximityGap.Frontier.G97ArcDilateDiscrepancy.per_dilate_arc_coloring
#print axioms
  ArkLib.ProximityGap.Frontier.G97ArcDilateDiscrepancy.specific_set_escapes_hereditary_control
#print axioms
  ArkLib.ProximityGap.Frontier.G97ArcDilateDiscrepancy.hereditary_control_cannot_yield_certificate

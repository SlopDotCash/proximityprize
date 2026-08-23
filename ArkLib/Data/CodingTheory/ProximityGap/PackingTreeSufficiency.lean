/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWindowedLaw

/-!
# Issue #232 — TREE-REALIZABLE MULTISETS TILE: the sufficiency half of the
# packing tree law (natural disjoint covering systems are realizable)

The packing tree law (probed exhaustively at `n = 12, 18, 24` — zero
mismatches over all 184/462/2710 volume-feasible multiplicity vectors) says:
a multiplicity vector of canonical cosets is packable in `ℤ_n` iff its
completed step multiset is **tree-realizable** — derivable by recursive
splitting of residue classes.  This file proves the SUFFICIENCY direction
constructively, at every modulus:

* `TreeRealizable n m M` — the inductive splitting tree: at class scale `m`
  either a leaf (`M = {m}`: the full class as one coset) or a split into
  `p ≥ 1` subclasses at scale `m·p`, with `M` the sum of the parts.
* `treeRealizable_tiles` — **the realization theorem**: a derivation of `M`
  at scale `m` produces, for EVERY residue class `c < m`, an explicit base
  set `B` and step assignment `σ` of canonical cosets with step counts
  exactly `M`, pairwise disjoint, whose union is exactly the class
  `{e < n : e ≡ c (mod m)}`.
* `treeRealizable_tiles_range` — the root consumer (`m = 1`): a derivation
  at scale `1` tiles all of `[0, n)`; any subfamily is a packing (drop the
  singleton padding), so every tree-realizable completed multiset realizes
  its multiplicity vector as a window-ready disjoint coset family.

Together with O119 (two-generator iff), O121 (the chromatic obstruction),
O122 (packing = CSP) and O123 (the subdivision engine), the only remaining
open content of the exact `k`-generator packing law is the NECESSITY
direction — Berger–Felzenbaum–Fraenkel naturality (every disjoint cover at
two-prime moduli is tree-derived), the genuinely open research half.

Conventions: cosets are carried by their STEP `s` (`s ∣ n`); the coset of
step `s` over base `r < s` is `cosetOf n (n/s) r` (size `n/s`, step
`n/(n/s) = s`).
-/

namespace PackingTreeSufficiency

open Finset DeBruijnWindowedLaw

/-- The residue class `{e < n : e % m = c}` as a `Finset`. -/
def classFinset (n m c : ℕ) : Finset ℕ :=
  (Finset.range n).filter (· % m = c)

lemma mem_classFinset {n m c e : ℕ} :
    e ∈ classFinset n m c ↔ e < n ∧ e % m = c := by
  simp [classFinset]

/-- **The splitting tree**: `M` is derivable at class scale `m` if it is the
single full-class coset (leaf) or splits into `p ≥ 1` parts at scale
`m·p`. -/
inductive TreeRealizable (n : ℕ) : ℕ → Multiset ℕ → Prop
  | leaf {m : ℕ} (hm : m ∣ n) (hm0 : 0 < m) : TreeRealizable n m {m}
  | split {m p : ℕ} (hp : 0 < p) (parts : Fin p → Multiset ℕ)
      (h : ∀ i, TreeRealizable n (m * p) (parts i)) :
      TreeRealizable n m (∑ i, parts i)

/-- Scales of derivations divide `n` and are positive. -/
lemma TreeRealizable.scale_dvd {n m : ℕ} {M : Multiset ℕ}
    (h : TreeRealizable n m M) : m ∣ n ∧ 0 < m := by
  induction h with
  | leaf hm hm0 => exact ⟨hm, hm0⟩
  | @split m p hp parts h ih =>
    obtain ⟨hdvd, hpos⟩ := ih ⟨0, hp⟩
    refine ⟨dvd_of_mul_right_dvd hdvd, ?_⟩
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · rw [hm0, zero_mul] at hpos
      omega
    · exact hm0

/-- The coset of step `s` over base `r` is exactly the image of
`j ↦ r + j·s` over `range (n/s)` (the step bookkeeping `n/(n/s) = s`). -/
lemma cosetOf_step {n s r : ℕ} (hs : s ∣ n) (hn : 0 < n) :
    cosetOf n (n / s) r
      = (Finset.range (n / s)).image (fun j => r + j * s) := by
  rw [cosetOf, Nat.div_div_self hs hn.ne']

/-- Membership in a step-`s` coset, characterized. -/
lemma mem_cosetOf_step {n s r e : ℕ} (hs : s ∣ n) (hn : 0 < n) (hr : r < s) :
    e ∈ cosetOf n (n / s) r ↔ e < n ∧ e % s = r := by
  rw [cosetOf_step hs hn]
  have hs0 : 0 < s := Nat.pos_of_dvd_of_pos hs hn
  have hns : n / s * s = n := Nat.div_mul_cancel hs
  constructor
  · intro he
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
    rw [Finset.mem_range] at hj
    constructor
    · calc r + j * s < s + j * s := Nat.add_lt_add_right hr _
        _ = (j + 1) * s := by ring
        _ ≤ n / s * s := Nat.mul_le_mul_right _ (by omega)
        _ = n := hns
    · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  · rintro ⟨hlt, hmod⟩
    refine Finset.mem_image.mpr ⟨e / s, Finset.mem_range.mpr ?_, ?_⟩
    · exact Nat.div_lt_div_of_lt_of_dvd hs hlt
    · show r + e / s * s = e
      have h := Nat.mod_add_div e s
      have hcomm : e / s * s = s * (e / s) := Nat.mul_comm _ _
      omega

/-- A step-`s` coset with `m ∣ s` lies in the residue class of its base
mod `m`. -/
lemma cosetOf_step_subset_class {n s m r : ℕ} (hs : s ∣ n) (hn : 0 < n)
    (hr : r < s) (hms : m ∣ s) :
    cosetOf n (n / s) r ⊆ classFinset n m (r % m) := by
  intro e he
  rw [mem_cosetOf_step hs hn hr] at he
  obtain ⟨hlt, hmod⟩ := he
  refine mem_classFinset.mpr ⟨hlt, ?_⟩
  conv_lhs => rw [← Nat.mod_add_div e s]
  obtain ⟨k, rfl⟩ := hms
  rw [hmod, show m * k * (e / (m * k)) = (k * (e / (m * k))) * m from by ring,
    Nat.add_mul_mod_self_right]

/-- **The leaf identity**: the step-`m` coset over base `c < m` IS the full
residue class `c` mod `m`. -/
lemma cosetOf_step_eq_class {n m c : ℕ} (hm : m ∣ n) (hn : 0 < n)
    (hc : c < m) :
    cosetOf n (n / m) c = classFinset n m c := by
  ext e
  rw [mem_cosetOf_step hm hn hc, mem_classFinset]

/-- **The class-splitting identity**: the class `c` mod `m` is the disjoint
union of the classes `c + i·m` mod `m·p`, `i < p`. -/
lemma classFinset_split {n m p c : ℕ} (hp : 0 < p) (hc : c < m) :
    classFinset n m c
      = (Finset.range p).biUnion (fun i => classFinset n (m * p) (c + i * m)) := by
  have hm0 : 0 < m := by omega
  ext e
  simp only [mem_classFinset, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨hlt, hmod⟩
    refine ⟨e % (m * p) / m, ?_, hlt, ?_⟩
    · exact Nat.div_lt_of_lt_mul (Nat.mod_lt _ (by positivity))
    · have h1 : e % (m * p) % m = e % m := Nat.mod_mod_of_dvd e ⟨p, rfl⟩
      have h2 := Nat.mod_add_div (e % (m * p)) m
      have hcomm : e % (m * p) / m * m = m * (e % (m * p) / m) :=
        Nat.mul_comm _ _
      omega
  · rintro ⟨i, hi, hlt, hmod⟩
    refine ⟨hlt, ?_⟩
    have h1 : e % (m * p) % m = e % m := Nat.mod_mod_of_dvd e ⟨p, rfl⟩
    rw [hmod] at h1
    rw [← h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

/-- The classes `c + i·m` mod `m·p` are pairwise disjoint over `i < p`. -/
lemma classFinset_split_disjoint {n m p c : ℕ} (hc : c < m)
    {i j : ℕ} (hi : i < p) (hj : j < p) (hij : i ≠ j) :
    Disjoint (classFinset n (m * p) (c + i * m))
      (classFinset n (m * p) (c + j * m)) := by
  have hm0 : 0 < m := by omega
  refine Finset.disjoint_left.mpr fun e he he' => ?_
  rw [mem_classFinset] at he he'
  have : c + i * m = c + j * m := he.2.symm.trans he'.2
  have : i * m = j * m := by omega
  exact hij (Nat.eq_of_mul_eq_mul_right hm0 this)

/-- **The tiling realization predicate**: an explicit base set `B` with step
assignment `σ` of canonical cosets, with step counts exactly `M`, pairwise
disjoint, union exactly the class `c` mod `m`. -/
def TilesClass (n m c : ℕ) (M : Multiset ℕ) : Prop :=
  ∃ (B : Finset ℕ) (σ : ℕ → ℕ),
    (∀ r ∈ B, σ r ∣ n ∧ m ∣ σ r ∧ r < σ r ∧ r % m = c) ∧
    (∀ s, ((B.filter (fun r => σ r = s)).card) = M.count s) ∧
    (∀ r₁ ∈ B, ∀ r₂ ∈ B, r₁ ≠ r₂ →
      Disjoint (cosetOf n (n / σ r₁) r₁) (cosetOf n (n / σ r₂) r₂)) ∧
    B.biUnion (fun r => cosetOf n (n / σ r) r) = classFinset n m c

/-- **THE REALIZATION THEOREM**: tree-derivable multisets tile every residue
class at their scale — constructively, by structural induction on the
derivation (leaf = the full-class coset; split = the union of the parts'
tilings of the subclasses). -/
theorem treeRealizable_tiles {n : ℕ} (hn : 0 < n) :
    ∀ {m : ℕ} {M : Multiset ℕ}, TreeRealizable n m M →
      ∀ c < m, TilesClass n m c M := by
  intro m M h
  induction h with
  | @leaf m hm hm0 =>
    intro c hc
    refine ⟨{c}, fun _ => m, ?_, ?_, ?_, ?_⟩
    · intro r hr
      rw [Finset.mem_singleton] at hr
      subst hr
      exact ⟨hm, dvd_refl m, hc, Nat.mod_eq_of_lt hc⟩
    · intro s
      by_cases hsm : m = s
      · subst hsm
        rw [Finset.filter_true_of_mem (fun r _ => rfl), Finset.card_singleton]
        simp
      · rw [Finset.filter_false_of_mem (fun r _ => hsm), Finset.card_empty,
          Multiset.count_singleton, if_neg (fun h => hsm h.symm)]
    · intro r₁ h₁ r₂ h₂ hne
      rw [Finset.mem_singleton] at h₁ h₂
      exact absurd (h₁.trans h₂.symm) hne
    · rw [Finset.singleton_biUnion]
      exact cosetOf_step_eq_class hm hn hc
  | @split m p hp parts hparts ih =>
    intro c hc
    have hm0 : 0 < m := by omega
    -- choose the parts' tilings of the subclasses
    have hsub : ∀ i : Fin p, c + i.val * m < m * p := by
      intro i
      calc c + i.val * m < m + i.val * m := Nat.add_lt_add_right hc _
        _ = (i.val + 1) * m := by ring
        _ ≤ p * m := Nat.mul_le_mul_right _ i.isLt
        _ = m * p := mul_comm _ _
    choose B σ hvalid hcount hdisj huni using
      fun i : Fin p => ih i (c + i.val * m) (hsub i)
    -- which part a base belongs to, recovered from its residue
    -- (for r ∈ B i: r % (m·p) = c + i·m, so (r % (m·p) − c) / m = i)
    have hBclass : ∀ i : Fin p, ∀ r ∈ B i, r % (m * p) = c + i.val * m :=
      fun i r hr => (hvalid i r hr).2.2.2
    -- the combined base set and step map
    classical
    set idx : ℕ → Fin p := fun r => ⟨(r % (m * p) - c) / m % p, Nat.mod_lt _ hp⟩
      with hidx
    have hidx_eq : ∀ i : Fin p, ∀ r ∈ B i, idx r = i := by
      intro i r hr
      have h := hBclass i r hr
      have hdiv : (r % (m * p) - c) / m = i.val := by
        rw [h, Nat.add_sub_cancel_left, mul_comm]
        exact Nat.mul_div_cancel_left _ hm0
      apply Fin.ext
      show (r % (m * p) - c) / m % p = i.val
      rw [hdiv, Nat.mod_eq_of_lt i.isLt]
    set Btot : Finset ℕ := Finset.univ.biUnion (fun i : Fin p => B i) with hBtot
    set σtot : ℕ → ℕ := fun r => σ (idx r) r with hσtot
    have hσ_eq : ∀ i : Fin p, ∀ r ∈ B i, σtot r = σ i r := by
      intro i r hr
      simp only [hσtot, hidx_eq i r hr]
    -- the part base sets are pairwise disjoint
    have hBdisj : ∀ i j : Fin p, i ≠ j → Disjoint (B i) (B j) := by
      intro i j hij
      refine Finset.disjoint_left.mpr fun r hri hrj => ?_
      have h1 := hBclass i r hri
      have h2 := hBclass j r hrj
      have : c + i.val * m = c + j.val * m := h1.symm.trans h2
      have : i.val * m = j.val * m := by omega
      exact hij (Fin.ext (Nat.eq_of_mul_eq_mul_right hm0 this))
    refine ⟨Btot, σtot, ?_, ?_, ?_, ?_⟩
    · -- validity
      intro r hr
      obtain ⟨i, _, hri⟩ := Finset.mem_biUnion.mp hr
      obtain ⟨hdvd, hmp, hlt, hres⟩ := hvalid i r hri
      rw [hσ_eq i r hri]
      refine ⟨hdvd, dvd_trans ⟨p, rfl⟩ hmp, hlt, ?_⟩
      have h1 : r % (m * p) % m = r % m := Nat.mod_mod_of_dvd r ⟨p, rfl⟩
      rw [hres] at h1
      rw [← h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
    · -- step counts: sum over the parts
      intro s
      have hfilter : Btot.filter (fun r => σtot r = s)
          = Finset.univ.biUnion
              (fun i : Fin p => (B i).filter (fun r => σ i r = s)) := by
        ext r
        constructor
        · intro hmem
          obtain ⟨hB, hs⟩ := Finset.mem_filter.mp hmem
          obtain ⟨i, _, hri⟩ := Finset.mem_biUnion.mp hB
          exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
            Finset.mem_filter.mpr ⟨hri, by rw [← hσ_eq i r hri]; exact hs⟩⟩
        · intro hmem
          obtain ⟨i, _, hri'⟩ := Finset.mem_biUnion.mp hmem
          obtain ⟨hri, hs⟩ := Finset.mem_filter.mp hri'
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hri⟩,
              by rw [hσ_eq i r hri]; exact hs⟩
      rw [hfilter, Finset.card_biUnion (fun i _ j _ hij =>
        Finset.disjoint_filter_filter (hBdisj i j hij))]
      have hM : (∑ i : Fin p, parts i).count s
          = ∑ i : Fin p, (parts i).count s := by
        classical
        exact Multiset.count_sum'
      rw [hM]
      exact Finset.sum_congr rfl fun i _ => hcount i s
    · -- pairwise disjointness
      intro r₁ h₁ r₂ h₂ hne
      obtain ⟨i₁, _, hr₁⟩ := Finset.mem_biUnion.mp h₁
      obtain ⟨i₂, _, hr₂⟩ := Finset.mem_biUnion.mp h₂
      rw [hσ_eq i₁ r₁ hr₁, hσ_eq i₂ r₂ hr₂]
      by_cases hii : i₁ = i₂
      · subst hii
        exact hdisj i₁ r₁ hr₁ r₂ hr₂ hne
      · -- cross-part: cosets live in disjoint subclasses
        obtain ⟨hdvd₁, hmp₁, hlt₁, hres₁⟩ := hvalid i₁ r₁ hr₁
        obtain ⟨hdvd₂, hmp₂, hlt₂, hres₂⟩ := hvalid i₂ r₂ hr₂
        have hsub₁ : cosetOf n (n / σ i₁ r₁) r₁
            ⊆ classFinset n (m * p) (c + i₁.val * m) := by
          rw [← hres₁]
          exact cosetOf_step_subset_class hdvd₁ hn hlt₁ hmp₁
        have hsub₂ : cosetOf n (n / σ i₂ r₂) r₂
            ⊆ classFinset n (m * p) (c + i₂.val * m) := by
          rw [← hres₂]
          exact cosetOf_step_subset_class hdvd₂ hn hlt₂ hmp₂
        exact Finset.disjoint_of_subset_left hsub₁
          (Finset.disjoint_of_subset_right hsub₂
            (classFinset_split_disjoint hc i₁.isLt i₂.isLt
              (fun hcon => hii (Fin.ext hcon))))
    · -- the union is the class
      have hclass := classFinset_split (n := n) (m := m) (c := c) hp hc
      rw [hclass]
      ext e
      constructor
      · intro hmem
        obtain ⟨r, hrB, he⟩ := Finset.mem_biUnion.mp hmem
        obtain ⟨i, _, hri⟩ := Finset.mem_biUnion.mp hrB
        refine Finset.mem_biUnion.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, ?_⟩
        rw [← huni i]
        exact Finset.mem_biUnion.mpr ⟨r, hri, by rwa [hσ_eq i r hri] at he⟩
      · intro hmem
        obtain ⟨i, hi, he⟩ := Finset.mem_biUnion.mp hmem
        rw [Finset.mem_range] at hi
        rw [← huni ⟨i, hi⟩] at he
        obtain ⟨r, hri, hre⟩ := Finset.mem_biUnion.mp he
        refine Finset.mem_biUnion.mpr ⟨r,
          Finset.mem_biUnion.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, hri⟩, ?_⟩
        rwa [hσ_eq ⟨i, hi⟩ r hri]

/-- **The root consumer**: a derivation at scale `1` tiles all of `[0, n)` —
an explicit pairwise-disjoint canonical-coset family with step counts `M`
whose union is the full range.  Any subfamily (e.g. dropping the singleton
padding) is a packing realizing its sub-multiset. -/
theorem treeRealizable_tiles_range {n : ℕ} (hn : 0 < n) {M : Multiset ℕ}
    (h : TreeRealizable n 1 M) :
    ∃ (B : Finset ℕ) (σ : ℕ → ℕ),
      (∀ r ∈ B, σ r ∣ n ∧ r < σ r) ∧
      (∀ s, ((B.filter (fun r => σ r = s)).card) = M.count s) ∧
      (∀ r₁ ∈ B, ∀ r₂ ∈ B, r₁ ≠ r₂ →
        Disjoint (cosetOf n (n / σ r₁) r₁) (cosetOf n (n / σ r₂) r₂)) ∧
      B.biUnion (fun r => cosetOf n (n / σ r) r) = Finset.range n := by
  obtain ⟨B, σ, hvalid, hcount, hdisj, huni⟩ :=
    treeRealizable_tiles hn h 0 one_pos
  refine ⟨B, σ, fun r hr => ⟨(hvalid r hr).1, (hvalid r hr).2.2.1⟩,
    hcount, hdisj, ?_⟩
  rw [huni]
  ext e
  simp [classFinset, Nat.mod_one]

/-! ## Teeth: the O121 positive instance through the tree

The mixed full tiling `{6·μ_6-steps… }` at `n = 36` — steps `(6, 6, 6, 4, 4)`
in multiset form `{6, 6, 6, 4, 4}` (three `μ_6`-cosets of step 6... NOTE:
step `s` corresponds to divisor `d = n/s`; the O119/O121 instance
`Packable 36 6 9 3 2` has three `μ_6`-cosets (step `6`) and two `μ_9`-cosets
(step `4`)) — is tree-derivable: split `[0,36)` by `p = 2` into two parity
classes at scale `2`; split the even class by `p = 3` into classes at scale
`6` (three step-6 leaves); split the odd class by `p = 2` into classes at
scale `4` (two step-4 leaves). -/

example : TreeRealizable 36 1 ({6, 6, 6} + {4, 4}) := by
  have h6 : TreeRealizable 36 6 {6} :=
    TreeRealizable.leaf (by norm_num) (by norm_num)
  have h4 : TreeRealizable 36 4 {4} :=
    TreeRealizable.leaf (by norm_num) (by norm_num)
  have heven : TreeRealizable 36 2 ({6, 6, 6} : Multiset ℕ) := by
    have h := TreeRealizable.split (n := 36) (m := 2) (p := 3) (by norm_num)
      (fun _ => ({6} : Multiset ℕ)) (fun _ => h6)
    have hsum : (∑ _i : Fin 3, ({6} : Multiset ℕ)) = {6, 6, 6} := by
      rw [Fin.sum_univ_three]
      rfl
    rwa [hsum] at h
  have hodd : TreeRealizable 36 2 ({4, 4} : Multiset ℕ) := by
    have h := TreeRealizable.split (n := 36) (m := 2) (p := 2) (by norm_num)
      (fun _ => ({4} : Multiset ℕ)) (fun _ => h4)
    have hsum : (∑ _i : Fin 2, ({4} : Multiset ℕ)) = {4, 4} := by
      rw [Fin.sum_univ_two]
      rfl
    rwa [hsum] at h
  have h := TreeRealizable.split (n := 36) (m := 1) (p := 2) (by norm_num)
    (fun i => if i = 0 then ({6, 6, 6} : Multiset ℕ) else {4, 4})
    (fun i => by
      by_cases hi : i = 0
      · subst hi
        show TreeRealizable 36 (1 * 2)
          (if (0 : Fin 2) = 0 then ({6, 6, 6} : Multiset ℕ) else {4, 4})
        rw [if_pos rfl]
        exact heven
      · show TreeRealizable 36 (1 * 2)
          (if i = 0 then ({6, 6, 6} : Multiset ℕ) else {4, 4})
        rw [if_neg hi]
        exact hodd)
  have hsum : (∑ i : Fin 2, if i = 0 then ({6, 6, 6} : Multiset ℕ) else {4, 4})
      = {6, 6, 6} + {4, 4} := by
    rw [Fin.sum_univ_two, if_pos rfl, if_neg (by decide)]
  rwa [hsum] at h

end PackingTreeSufficiency

#print axioms PackingTreeSufficiency.TreeRealizable.scale_dvd
#print axioms PackingTreeSufficiency.cosetOf_step_eq_class
#print axioms PackingTreeSufficiency.classFinset_split
#print axioms PackingTreeSufficiency.treeRealizable_tiles
#print axioms PackingTreeSufficiency.treeRealizable_tiles_range

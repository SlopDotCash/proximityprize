/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ThreadSplit
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnIndicatorDisjointness

/-!
# Issue #232 — THE FINAL ASSEMBLY: de Bruijn 1953 (two-prime case) as one theorem

This file assembles the three kernel-checked ingredients —

* `ThreadSplit.thread_vanishing_of_vanishing` (O93): for `p² ∣ n`, a vanishing power
  sum at a primitive `n`-th root `ζ` splits thread-by-thread at `ζ^p`;
* `DeBruijnIndicatorDisjointness.debruijn_squarefree_two_prime` (O87): at the
  squarefree base `n = p·q`, a vanishing indicator sum forces shift-closure under
  `+p` or under `+q`;
* the geometric-sum sufficiency engine (the converse, generic) —

into **de Bruijn 1953, two-prime case** as a single iff: for `n = p^a·q^b`
(`a, b ≥ 1`, `p ≠ q` primes) and a primitive `n`-th root of unity `ζ` in a
characteristic-zero field,

    `Σ_{e∈S} ζ^e = 0  ↔  S is a disjoint union of rotated full prime packets`,

where a packet is an arithmetic progression `{r + t·(n/d) : t < d}` for `d ∈ {p, q}`.

**Canonical form (the load-bearing design choice):** every rotated full `μ_d`-packet
mod `n` has a unique representative with base `r < n/d`, and then
`r + (d−1)·(n/d) < n` — no modular wraparound appears anywhere in the development.
The lift `e ↦ r + u·e` through the descending prime `u` preserves canonical form
exactly (`isPacket_lift`): `{s + t·(m/d) : t < d}` lifts to
`{(r + u·s) + t·(u·(m/d)) : t < d}` with new base `r + u·s < u·(m/d) = (u·m)/d`.

* `IsPacket` / `IsPacketUnion` — the packet predicate (canonical form) and the
  disjoint-union decomposition predicate.
* `packet_sum_eq_zero` / `sum_eq_zero_of_isPacketUnion` — **the converse**: every
  packet kills the sum (geometric sum at `ζ^(n/d)`), hence every disjoint union does.
* `isPacket_lift` — **the lift lemma** (O93's named residual): canonical packets at
  level `m` lift through `e ↦ r + u·e` to canonical packets at level `u·m`.
* `isPacketUnion_of_closure` — the squarefree seam: shift-closure under `+k`
  (`n = w·k`) IS a disjoint union of canonical step-`k` packets (the orbit argument).
* `isPacketUnion_of_threads` — **the induction step**: if every thread of `S` at
  level `m` decomposes, `S` decomposes at level `u·m` (lift + cross-thread
  disjointness by residues mod `u`).
* `isPacketUnion_of_sum_eq_zero` — **the strong induction wrapper** (O93's named
  residual): recurse thread-split down the digits of `n = p^a·q^b` to the squarefree
  base `p·q`, apply the O87 dichotomy there, lift back up.
* `debruijn_two_prime` — **the headline iff**.

Falsified first: `scripts/probes/probe_debruijn_two_prime_assembly.py` (exact integer
arithmetic mod `Φ_n`, meet-in-the-middle over the FULL `2^n` mask space; exit 0):
the headline iff as a set identity (disjoint-canonical-packet-union family ==
vanishing family) EXHAUSTIVELY at `n = 12, 18, 20, 28`, the recursion executed on
every vanishing mask with the exact lift index map asserted at every lift, plus
mixture witnesses (both packet types occur in one decomposition — pure type genuinely
fails past the squarefree level, so the mixed statement here is the honest one).

Literature pin: de Bruijn, *On the factorization of cyclic groups* (Indag. Math.
1953), §3, as modernized by Lam–Leung (J. Algebra 224 (2000)) — the two-prime
vanishing-sums theorem.  Per the O91 search (2026-06-09), no prior formalization of
this theorem exists in any proof assistant.
-/

namespace DeBruijnTwoPrimeAssembly

open Finset

/-! ## The packet predicates (canonical form) -/

/-- A **canonical rotated full prime packet** at level `n` with `d` teeth: the
arithmetic progression `{r + t·(n/d) : t < d}` with base `r < n/d`.  Canonical form
means no modular wraparound: all elements are `< n` when `d ∣ n`. -/
def IsPacket (n d : ℕ) (P : Finset ℕ) : Prop :=
  ∃ r < n / d, P = (Finset.range d).image (fun t => r + t * (n / d))

/-- `S` is a **disjoint union of rotated full prime packets** (either type) at level
`n` — de Bruijn's ℕ-combination statement, sharpened to indicators. -/
def IsPacketUnion (n p q : ℕ) (S : Finset ℕ) : Prop :=
  ∃ Ps : Finset (Finset ℕ), (∀ P ∈ Ps, IsPacket n p P ∨ IsPacket n q P) ∧
    (↑Ps : Set (Finset ℕ)).PairwiseDisjoint id ∧ S = Ps.biUnion id

/-- A packet has exactly `d` elements (the progression is injective). -/
lemma IsPacket.card_eq {n d : ℕ} (hnd : 0 < n / d) {P : Finset ℕ}
    (h : IsPacket n d P) : P.card = d := by
  obtain ⟨r, _, rfl⟩ := h
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro t₁ _ t₂ _ heq
  have heq' : r + t₁ * (n / d) = r + t₂ * (n / d) := heq
  exact Nat.eq_of_mul_eq_mul_right hnd (by omega)

/-! ## The converse: packets (hence packet unions) kill the sum -/

/-- **Per-packet vanishing**: a rotated full prime packet sums to zero against any
primitive `n`-th root of unity — `ζ^r · Σ_{t<d} (ζ^{n/d})^t = ζ^r · 0`. -/
theorem packet_sum_eq_zero {L : Type*} [Field L] {n d : ℕ} (hd : 1 < d)
    (hdn : d ∣ n) (hn : 0 < n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    {P : Finset ℕ} (hP : IsPacket n d P) :
    ∑ e ∈ P, ζ ^ e = 0 := by
  obtain ⟨r, _, rfl⟩ := hP
  have hstep : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) (by omega)
  have hinj : ∀ t₁ ∈ Finset.range d, ∀ t₂ ∈ Finset.range d,
      r + t₁ * (n / d) = r + t₂ * (n / d) → t₁ = t₂ := by
    intro t₁ _ t₂ _ h
    exact Nat.eq_of_mul_eq_mul_right hstep (by omega)
  rw [Finset.sum_image hinj]
  have hprim : IsPrimitiveRoot (ζ ^ (n / d)) d :=
    hζ.pow hn (Nat.div_mul_cancel hdn).symm
  calc ∑ t ∈ Finset.range d, ζ ^ (r + t * (n / d))
      = ζ ^ r * ∑ t ∈ Finset.range d, (ζ ^ (n / d)) ^ t := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [pow_add, mul_comm t (n / d), pow_mul]
    _ = 0 := by rw [hprim.geom_sum_eq_zero hd, mul_zero]

/-- **The converse of the headline** (generic — any level with both primes
dividing): a disjoint union of rotated full prime packets has vanishing sum. -/
theorem sum_eq_zero_of_isPacketUnion {L : Type*} [Field L] {n p q : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hpn : p ∣ n) (hqn : q ∣ n) (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) {S : Finset ℕ}
    (h : IsPacketUnion n p q S) : ∑ e ∈ S, ζ ^ e = 0 := by
  obtain ⟨Ps, hpk, hdisj, rfl⟩ := h
  rw [Finset.sum_biUnion hdisj]
  refine Finset.sum_eq_zero fun P hP => ?_
  rcases hpk P hP with h | h
  · exact packet_sum_eq_zero hp hpn hn hζ h
  · exact packet_sum_eq_zero hq hqn hn hζ h

/-! ## The lift lemma (O93's first named residual)

Canonical packets at level `m` lift through `e ↦ r + u·e` (`r < u`) to canonical
packets at level `u·m`: the base maps to `r + u·s < u·(m/d) = (u·m)/d` and the step
multiplies by `u` — the exact index map asserted by the probe at every lift. -/

/-- **The lift lemma**: the image of a canonical `d`-packet at level `m` under
`e ↦ r + u·e` is a canonical `d`-packet at level `u·m`. -/
theorem isPacket_lift {m d u r : ℕ} (hdm : d ∣ m) (hr : r < u)
    {P : Finset ℕ} (hP : IsPacket m d P) :
    IsPacket (u * m) d (P.image (fun e => r + u * e)) := by
  obtain ⟨s, hs, rfl⟩ := hP
  have hstep : u * m / d = u * (m / d) := Nat.mul_div_assoc u hdm
  refine ⟨r + u * s, ?_, ?_⟩
  · rw [hstep]
    have h1 : u * (s + 1) ≤ u * (m / d) := Nat.mul_le_mul_left u hs
    have h2 : u * (s + 1) = u * s + u := by ring
    omega
  · rw [Finset.image_image]
    congr 1
    funext t
    simp only [Function.comp_apply]
    rw [hstep]
    ring

/-! ## The squarefree seam: shift-closure is a canonical packet decomposition -/

/-- **Closure ⟹ canonical packets** (the orbit argument): if `n = w·k` and
`S ⊆ [0, n)` is closed under `e ↦ (e + k) % n`, then `S` is a disjoint union of
canonical step-`k` packets `{r + t·k : t < w}` with `r < k` — one per residue
class of `S` mod `k`. -/
theorem isPacketUnion_of_closure {n w k : ℕ} (_hw : 0 < w) (hk : 0 < k)
    (hn : n = w * k) {S : Finset ℕ} (hS : ∀ e ∈ S, e < n)
    (hcl : ∀ e ∈ S, (e + k) % n ∈ S) :
    ∃ Ps : Finset (Finset ℕ),
      (∀ P ∈ Ps, ∃ r < k, P = (Finset.range w).image (fun t => r + t * k)) ∧
      (↑Ps : Set (Finset ℕ)).PairwiseDisjoint id ∧ S = Ps.biUnion id := by
  classical
  -- iterated closure
  have hiter : ∀ j : ℕ, ∀ e ∈ S, (e + j * k) % n ∈ S := by
    intro j
    induction j with
    | zero => intro e he; simpa [Nat.mod_eq_of_lt (hS e he)] using he
    | succ j ih =>
      intro e he
      have h1 := hcl _ (ih e he)
      rw [Nat.mod_add_mod] at h1
      have h2 : e + j * k + k = e + (j + 1) * k := by ring
      rwa [h2] at h1
  -- every residue fiber of an element of `S` is entirely inside `S`
  have hfiber : ∀ e ∈ S, ∀ t < w, e % k + t * k ∈ S := by
    intro e he t ht
    have hek : e / k < w := by
      rw [Nat.div_lt_iff_lt_mul hk]
      rw [hn] at hS
      exact hS e he
    have hsplit : k * (e / k) + e % k = e := Nat.div_add_mod e k
    have hkey : e + (w + t - e / k) * k = e % k + t * k + n := by
      have h1 : e / k + (w + t - e / k) = w + t := by omega
      calc e + (w + t - e / k) * k
          = (k * (e / k) + e % k) + (w + t - e / k) * k := by rw [hsplit]
        _ = e % k + (e / k + (w + t - e / k)) * k := by ring
        _ = e % k + (w + t) * k := by rw [h1]
        _ = e % k + t * k + w * k := by ring
        _ = e % k + t * k + n := by rw [hn]
    have hlt : e % k + t * k < n := by
      have h2 : e % k < k := Nat.mod_lt _ hk
      have h3 : (t + 1) * k ≤ w * k := Nat.mul_le_mul_right k (by omega)
      have h4 : (t + 1) * k = t * k + k := by ring
      omega
    have h5 := hiter (w + t - e / k) e he
    rwa [hkey, Nat.add_mod_right, Nat.mod_eq_of_lt hlt] at h5
  refine ⟨(S.image (· % k)).image (fun r => (Finset.range w).image (fun t => r + t * k)),
    ?_, ?_, ?_⟩
  · -- packet form
    intro P hP
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨e % k, Nat.mod_lt _ hk, rfl⟩
  · -- pairwise disjointness: distinct packets have distinct residues mod `k`
    have hres : ∀ r < k, ∀ x ∈ (Finset.range w).image (fun t => r + t * k),
        x % k = r := by
      intro r hrk x hx
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrk]
    intro P₁ h₁ P₂ h₂ hne
    obtain ⟨r₁, hr₁, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp h₁)
    obtain ⟨r₂, hr₂, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp h₂)
    obtain ⟨e₁, _, rfl⟩ := Finset.mem_image.mp hr₁
    obtain ⟨e₂, _, rfl⟩ := Finset.mem_image.mp hr₂
    have hrr : e₁ % k ≠ e₂ % k := fun h => hne (by rw [h])
    simp only [Function.onFun, id_eq]
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    exact hrr ((hres _ (Nat.mod_lt _ hk) x hx₁).symm.trans
      (hres _ (Nat.mod_lt _ hk) x hx₂))
  · -- the union is exactly `S`
    ext x
    rw [Finset.mem_biUnion]
    constructor
    · intro hx
      refine ⟨(Finset.range w).image (fun t => x % k + t * k),
        Finset.mem_image.mpr ⟨x % k, Finset.mem_image.mpr ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
      have hdlt : x / k < w := by
        rw [Nat.div_lt_iff_lt_mul hk]
        rw [hn] at hS
        exact hS x hx
      exact Finset.mem_image.mpr
        ⟨x / k, Finset.mem_range.mpr hdlt, Nat.mod_add_div' x k⟩
    · rintro ⟨P, hP, hxP⟩
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hxP
      exact hfiber e he t (Finset.mem_range.mp ht)

/-! ## The induction step: threads decompose ⟹ the level above decomposes -/

/-- **The thread-assembly step**: if every thread
`T_r = {e' < m : r + u·e' ∈ S}` (`r < u`) is a disjoint packet union at level `m`,
then `S ⊆ [0, u·m)` is a disjoint packet union at level `u·m` — lift each thread's
packets through `e ↦ r + u·e` (the lift lemma keeps them canonical); packets from
different threads are disjoint because their elements have different residues
mod `u`. -/
theorem isPacketUnion_of_threads {u m p q : ℕ} (hu : 0 < u)
    (hpm : p ∣ m) (hqm : q ∣ m)
    {S : Finset ℕ} (hS : ∀ e ∈ S, e < u * m)
    (hdec : ∀ r < u, IsPacketUnion m p q
      ((Finset.range m).filter (fun e' => r + u * e' ∈ S))) :
    IsPacketUnion (u * m) p q S := by
  classical
  -- non-dependent choice of the thread decompositions
  have hdec' : ∀ r : ℕ, ∃ Ps : Finset (Finset ℕ), r < u →
      ((∀ P ∈ Ps, IsPacket m p P ∨ IsPacket m q P) ∧
        (↑Ps : Set (Finset ℕ)).PairwiseDisjoint id ∧
        (Finset.range m).filter (fun e' => r + u * e' ∈ S) = Ps.biUnion id) := by
    intro r
    by_cases hr : r < u
    · obtain ⟨Ps, h⟩ := hdec r hr
      exact ⟨Ps, fun _ => h⟩
    · exact ⟨∅, fun h => absurd h hr⟩
  choose Pf hPf using hdec'
  -- elements of a lifted packet from thread `r` have residue `r` mod `u`
  have hres : ∀ r < u, ∀ (P : Finset ℕ), ∀ x ∈ P.image (fun e => r + u * e),
      x % u = r := by
    intro r hr P x hx
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hx
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  refine ⟨(Finset.range u).biUnion
    (fun r => (Pf r).image (fun P => P.image (fun e => r + u * e))), ?_, ?_, ?_⟩
  · -- every member is a packet at level `u·m` (the lift lemma)
    intro Q hQ
    obtain ⟨r, hr, hQ'⟩ := Finset.mem_biUnion.mp hQ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ'
    have hru := Finset.mem_range.mp hr
    rcases (hPf r hru).1 P hP with h | h
    · exact Or.inl (isPacket_lift hpm hru h)
    · exact Or.inr (isPacket_lift hqm hru h)
  · -- pairwise disjointness
    intro Q₁ h₁ Q₂ h₂ hne
    obtain ⟨r₁, hr₁, hQ₁⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp h₁)
    obtain ⟨r₂, hr₂, hQ₂⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp h₂)
    obtain ⟨P₁, hP₁, rfl⟩ := Finset.mem_image.mp hQ₁
    obtain ⟨P₂, hP₂, rfl⟩ := Finset.mem_image.mp hQ₂
    have hru₁ := Finset.mem_range.mp hr₁
    have hru₂ := Finset.mem_range.mp hr₂
    simp only [Function.onFun, id_eq]
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    by_cases hrr : r₁ = r₂
    · -- same thread: lifted disjointness through injectivity of `e ↦ r + u·e`
      subst hrr
      have hPne : P₁ ≠ P₂ := by
        rintro rfl
        exact hne rfl
      have hd := (hPf r₁ hru₁).2.1 (Finset.mem_coe.mpr hP₁)
        (Finset.mem_coe.mpr hP₂) hPne
      simp only [Function.onFun, id_eq] at hd
      obtain ⟨e₁, he₁, rfl⟩ := Finset.mem_image.mp hx₁
      obtain ⟨e₂, he₂, heq⟩ := Finset.mem_image.mp hx₂
      have he : e₂ = e₁ := by
        have h1 : u * e₂ = u * e₁ := by omega
        exact Nat.eq_of_mul_eq_mul_left hu h1
      exact Finset.disjoint_left.mp hd he₁ (he ▸ he₂)
    · -- different threads: residues mod `u` differ
      exact hrr ((hres r₁ hru₁ P₁ x hx₁).symm.trans (hres r₂ hru₂ P₂ x hx₂))
  · -- the union is exactly `S`
    ext x
    rw [Finset.mem_biUnion]
    constructor
    · intro hx
      have hrlt : x % u < u := Nat.mod_lt _ hu
      have hdlt : x / u < m := by
        rw [Nat.div_lt_iff_lt_mul hu, mul_comm m u]
        exact hS x hx
      have hxeq : x % u + u * (x / u) = x := Nat.mod_add_div x u
      have hmem : x / u ∈ (Finset.range m).filter
          (fun e' => x % u + u * e' ∈ S) := by
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨hdlt, by rwa [hxeq]⟩
      rw [(hPf (x % u) hrlt).2.2] at hmem
      obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.mp hmem
      refine ⟨P.image (fun e => x % u + u * e), ?_, ?_⟩
      · exact Finset.mem_biUnion.mpr ⟨x % u, Finset.mem_range.mpr hrlt,
          Finset.mem_image.mpr ⟨P, hP, rfl⟩⟩
      · exact Finset.mem_image.mpr ⟨x / u, hxP, hxeq⟩
    · rintro ⟨Q, hQ, hxQ⟩
      obtain ⟨r, hr, hQ'⟩ := Finset.mem_biUnion.mp hQ
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ'
      obtain ⟨e, heP, rfl⟩ := Finset.mem_image.mp hxQ
      have hmem : e ∈ (Finset.range m).filter (fun e' => r + u * e' ∈ S) := by
        rw [(hPf r (Finset.mem_range.mp hr)).2.2]
        exact Finset.mem_biUnion.mpr ⟨P, hP, heP⟩
      exact (Finset.mem_filter.mp hmem).2

/-! ## ZMod bridges for the squarefree base -/

/-- Subset sums over `[0, n)` exponents agree with their `ZMod n` images. -/
lemma sum_image_cast {L : Type*} [Field L] {n : ℕ} (ζ : L)
    {S : Finset ℕ} (hS : ∀ e ∈ S, e < n) :
    ∑ x ∈ S.image ((↑) : ℕ → ZMod n), ζ ^ x.val = ∑ e ∈ S, ζ ^ e := by
  rw [Finset.sum_image (fun x hx y hy hxy => by
    have hx' := ZMod.val_cast_of_lt (hS x hx)
    have hy' := ZMod.val_cast_of_lt (hS y hy)
    rw [← hx', ← hy', hxy])]
  exact Finset.sum_congr rfl fun e he => by rw [ZMod.val_cast_of_lt (hS e he)]

/-- `ZMod`-closure under `+c` descends to ℕ-closure under `e ↦ (e + c) % n` on the
representative set. -/
lemma closure_nat_of_closure_zmod {n c : ℕ} (hn : 0 < n) {S : Finset ℕ}
    (hS : ∀ e ∈ S, e < n)
    (hcl : ∀ x ∈ S.image ((↑) : ℕ → ZMod n),
      x + ((c : ℕ) : ZMod n) ∈ S.image ((↑) : ℕ → ZMod n)) :
    ∀ e ∈ S, (e + c) % n ∈ S := by
  haveI : NeZero n := ⟨hn.ne'⟩
  intro e he
  have hx := hcl _ (Finset.mem_image_of_mem _ he)
  obtain ⟨e₂, he₂, heq⟩ := Finset.mem_image.mp hx
  have hcast : ((e₂ : ℕ) : ZMod n) = (((e + c) % n : ℕ) : ZMod n) := by
    rw [heq, ZMod.natCast_mod, Nat.cast_add]
  have hval : e₂ = (e + c) % n := by
    have h1 := ZMod.val_cast_of_lt (hS e₂ he₂)
    have h2 := ZMod.val_cast_of_lt (Nat.mod_lt (e + c) hn)
    rw [← h1, hcast, h2]
  exact hval ▸ he₂

/-! ## The strong induction wrapper -/

/-- **The forward direction of de Bruijn two-prime** (the strong induction): for
`n = p^a·q^b` (`a, b ≥ 1`), a vanishing power sum over `S ⊆ [0, n)` at a primitive
`n`-th root forces `S` to be a disjoint union of rotated full prime packets.
Recursion: thread-split (O93) descends the `p`-digits to `a = 1`, then the
`q`-digits to `b = 1`; the squarefree dichotomy (O87) lands the base; the lift
lemma carries packets back up. -/
theorem isPacketUnion_of_sum_eq_zero {L : Type*} [Field L] [CharZero L]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∀ a, 0 < a → ∀ b, 0 < b → ∀ ζ : L, IsPrimitiveRoot ζ (p ^ a * q ^ b) →
      ∀ S : Finset ℕ, (∀ e ∈ S, e < p ^ a * q ^ b) → (∑ e ∈ S, ζ ^ e = 0) →
      IsPacketUnion (p ^ a * q ^ b) p q S := by
  intro a
  induction a with
  | zero => exact fun h => absurd h (lt_irrefl 0)
  | succ a iha =>
    intro _ b
    induction b with
    | zero => exact fun h => absurd h (lt_irrefl 0)
    | succ b ihb =>
      intro _ ζ hζ S hS hsum
      rcases Nat.eq_zero_or_pos a with ha0 | hapos
      · subst ha0
        rcases Nat.eq_zero_or_pos b with hb0 | hbpos
        · -- BASE CASE: `n = p·q` — the O87 squarefree dichotomy
          subst hb0
          have h11 : p ^ (0 + 1) * q ^ (0 + 1) = p * q := by ring
          rw [h11] at hζ hS ⊢
          have hnpos : 0 < p * q := Nat.mul_pos hp.pos hq.pos
          haveI : NeZero (p * q) := ⟨hnpos.ne'⟩
          have hsum' : ∑ x ∈ S.image ((↑) : ℕ → ZMod (p * q)), ζ ^ x.val = 0 := by
            rw [sum_image_cast ζ hS]
            exact hsum
          rcases DeBruijnIndicatorDisjointness.debruijn_squarefree_two_prime
            hp hq hpq hζ hsum' with hcl | hcl
          · -- closed under `+p`: disjoint union of `μ_q`-packets (step `p`)
            have hcln := closure_nat_of_closure_zmod hnpos hS hcl
            obtain ⟨Ps, hpk, hdisj, huni⟩ := isPacketUnion_of_closure hq.pos hp.pos
              (mul_comm p q) hS hcln
            refine ⟨Ps, fun P hP => Or.inr ?_, hdisj, huni⟩
            obtain ⟨r, hr, heq⟩ := hpk P hP
            have hdq : p * q / q = p := by
              rw [Nat.mul_comm p q]
              exact Nat.mul_div_cancel_left p hq.pos
            rw [IsPacket, hdq]
            exact ⟨r, hr, heq⟩
          · -- closed under `+q`: disjoint union of `μ_p`-packets (step `q`)
            have hcln := closure_nat_of_closure_zmod hnpos hS hcl
            obtain ⟨Ps, hpk, hdisj, huni⟩ := isPacketUnion_of_closure hp.pos hq.pos
              rfl hS hcln
            refine ⟨Ps, fun P hP => Or.inl ?_, hdisj, huni⟩
            obtain ⟨r, hr, heq⟩ := hpk P hP
            have hdp : p * q / p = q := Nat.mul_div_cancel_left q hp.pos
            rw [IsPacket, hdp]
            exact ⟨r, hr, heq⟩
        · -- DESCEND `q` (`a = 0`, `b ≥ 1`): thread-split at `u = q`
          have hn_eq : p ^ (0 + 1) * q ^ (b + 1) = q * (p ^ (0 + 1) * q ^ b) := by
            ring
          rw [hn_eq] at hζ hS ⊢
          have hm : 0 < p ^ (0 + 1) * q ^ b :=
            Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)
          have hqm : q ∣ p ^ (0 + 1) * q ^ b :=
            dvd_mul_of_dvd_right (dvd_pow_self q hbpos.ne') _
          have hpm : p ∣ p ^ (0 + 1) * q ^ b :=
            dvd_mul_of_dvd_left (dvd_pow_self p one_ne_zero) _
          have hth := ThreadSplit.thread_vanishing_of_vanishing hq hm hqm hζ hS hsum
          have hζq : IsPrimitiveRoot (ζ ^ q) (p ^ (0 + 1) * q ^ b) :=
            hζ.pow (Nat.mul_pos hq.pos hm) rfl
          refine isPacketUnion_of_threads hq.pos hpm hqm hS fun r hr => ?_
          refine ihb hbpos (ζ ^ q) hζq _ (fun e he => Finset.mem_range.mp
            (Finset.mem_filter.mp he).1) ?_
          rw [Finset.sum_filter]
          exact hth r hr
      · -- DESCEND `p` (`a ≥ 1`): thread-split at `u = p`
        have hn_eq : p ^ (a + 1) * q ^ (b + 1) = p * (p ^ a * q ^ (b + 1)) := by
          ring
        rw [hn_eq] at hζ hS ⊢
        have hm : 0 < p ^ a * q ^ (b + 1) :=
          Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)
        have hpm : p ∣ p ^ a * q ^ (b + 1) :=
          dvd_mul_of_dvd_left (dvd_pow_self p hapos.ne') _
        have hqm : q ∣ p ^ a * q ^ (b + 1) :=
          dvd_mul_of_dvd_right (dvd_pow_self q (Nat.succ_ne_zero b)) _
        have hth := ThreadSplit.thread_vanishing_of_vanishing hp hm hpm hζ hS hsum
        have hζp : IsPrimitiveRoot (ζ ^ p) (p ^ a * q ^ (b + 1)) :=
          hζ.pow (Nat.mul_pos hp.pos hm) rfl
        refine isPacketUnion_of_threads hp.pos hpm hqm hS fun r hr => ?_
        refine iha hapos (b + 1) (Nat.succ_pos b) (ζ ^ p) hζp _
          (fun e he => Finset.mem_range.mp (Finset.mem_filter.mp he).1) ?_
        rw [Finset.sum_filter]
        exact hth r hr

/-! ## The headline: de Bruijn 1953, two-prime case -/

/-- **DE BRUIJN 1953, TWO-PRIME CASE** (Indag. Math. 1953 §3; Lam–Leung 2000,
indicator form, sharpened to disjoint unions): for `n = p^a·q^b` (`a, b ≥ 1`,
`p ≠ q` primes) and a primitive `n`-th root of unity `ζ` in a characteristic-zero
field, a power sum over exponents `S ⊆ [0, n)` vanishes **iff** `S` is a disjoint
union of rotated full prime packets — arithmetic progressions
`{r + t·(n/p) : t < p}` or `{r + t·(n/q) : t < q}`.

Probe-verified exhaustively over the full `2^n` subset space at `n = 12, 18, 20, 28`
(the disjoint-packet-union family EQUALS the vanishing family). -/
theorem debruijn_two_prime {L : Type*} [Field L] [CharZero L]
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha : 0 < a) (hb : 0 < b)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b))
    {S : Finset ℕ} (hS : ∀ e ∈ S, e < p ^ a * q ^ b) :
    (∑ e ∈ S, ζ ^ e = 0) ↔ IsPacketUnion (p ^ a * q ^ b) p q S := by
  constructor
  · exact fun h => isPacketUnion_of_sum_eq_zero hp hq hpq a ha b hb ζ hζ S hS h
  · intro h
    exact sum_eq_zero_of_isPacketUnion hp.one_lt hq.one_lt
      (dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') _)
      (dvd_mul_of_dvd_right (dvd_pow_self q hb.ne') _)
      (Nat.mul_pos (pow_pos hp.pos a) (pow_pos hq.pos b)) hζ h

/-! ## Non-vacuity witnesses (fired at `ℂ`, `n = 12 = 2²·3`, with teeth)

The converse produces the genuine nonempty vanishing sum `1 + ζ₁₂⁶ = 0` from a
one-packet decomposition; the forward direction converts a hypothetical vanishing
of the singleton `{0}` into a cardinality contradiction (a packet inside a
singleton would need `≥ 2` elements) — the iff genuinely discriminates. -/

private lemma exp_twelfth_primitive :
    IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 12)) (2 ^ 2 * 3 ^ 1) := by
  have h := Complex.isPrimitiveRoot_exp 12 (by norm_num)
  norm_num at h ⊢
  exact h

/-- The converse fired: `{0, 6}` is the canonical `μ_2`-packet at `n = 12`
(base `0`, step `6`), so its sum vanishes — `1 + ζ₁₂⁶ = 0` produced by the
headline. -/
example : ∑ e ∈ ({0, 6} : Finset ℕ),
    Complex.exp (2 * Real.pi * Complex.I / 12) ^ e = 0 := by
  refine (debruijn_two_prime Nat.prime_two Nat.prime_three (by norm_num)
    (by norm_num) (by norm_num) exp_twelfth_primitive (by decide)).mpr ?_
  refine ⟨{({0, 6} : Finset ℕ)}, fun P hP => ?_, ?_, ?_⟩
  · rw [Finset.mem_singleton] at hP
    subst hP
    exact Or.inl ⟨0, by norm_num, by decide⟩
  · rw [Finset.coe_singleton]
    exact Set.pairwiseDisjoint_singleton _ _
  · rw [Finset.singleton_biUnion]
    rfl

/-- The forward direction fired (with teeth): the singleton `{0}` cannot vanish —
a hypothetical vanishing sum would decompose `{0}` into packets of size `2` or
`3`, contradicting `|{0}| = 1`.  So `(1 : ℂ) ≠ 0` falls out of de Bruijn
structure alone. -/
example : ¬ (∑ e ∈ ({0} : Finset ℕ),
    Complex.exp (2 * Real.pi * Complex.I / 12) ^ e = 0) := by
  intro hcon
  obtain ⟨Ps, hpk, _, huni⟩ := (debruijn_two_prime Nat.prime_two Nat.prime_three
    (by norm_num) (by norm_num) (by norm_num) exp_twelfth_primitive
    (by decide)).mp hcon
  have h0 : (0 : ℕ) ∈ (Ps.biUnion id) := huni ▸ Finset.mem_singleton_self 0
  obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.mp h0
  have hsub : P ⊆ {0} := fun x hx =>
    huni ▸ Finset.mem_biUnion.mpr ⟨P, hP, hx⟩
  have hcard : P.card ≤ 1 := by
    calc P.card ≤ ({0} : Finset ℕ).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton 0
  rcases hpk P hP with h | h
  · have := h.card_eq (by norm_num) -- `(2^2*3^1)/2 = 6 > 0`
    omega
  · have := h.card_eq (by norm_num) -- `(2^2*3^1)/3 = 4 > 0`
    omega

end DeBruijnTwoPrimeAssembly

#print axioms DeBruijnTwoPrimeAssembly.packet_sum_eq_zero
#print axioms DeBruijnTwoPrimeAssembly.sum_eq_zero_of_isPacketUnion
#print axioms DeBruijnTwoPrimeAssembly.isPacket_lift
#print axioms DeBruijnTwoPrimeAssembly.isPacketUnion_of_closure
#print axioms DeBruijnTwoPrimeAssembly.isPacketUnion_of_threads
#print axioms DeBruijnTwoPrimeAssembly.isPacketUnion_of_sum_eq_zero
#print axioms DeBruijnTwoPrimeAssembly.debruijn_two_prime

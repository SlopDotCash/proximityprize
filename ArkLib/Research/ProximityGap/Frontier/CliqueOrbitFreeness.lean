/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Freeness of the rotation action on `(k+1)`-subsets of `μ_n` (n = 2^a):
  the orbit-SIZE half of `lalalune`'s decay-rate orbit-count reformulation (#444)

`lalalune`'s 2026-06-15 22:13 "decay-rate attack" on #444 reformulated the prize's open
decay-rate core as an orbit count

  > `D*(m) = (orbit size ≤ n) · #clique-orbits(m)`,   rotation `R' ↦ ζ·R'` sends `γ ↦ ζ^{a−b}γ`.

The companion file `SchurRatioRotationEquivariance.lean` (push `ce06fef0a`/`925a5c26c`) landed the
**equivariance substrate**: the Schur-ratio level sets `L_γ` and the bad-α vanishing locus are
unions of `⟨ζ⟩`-orbits. What that substrate leaves open is the **orbit SIZE**: `lalalune` carries
the weak "`orbit size ≤ n`". This file sharpens it to "`= n` EXACTLY" in the prize regime, via a
clean parity criterion.

## The result

Model a `(k+1)`-subset `R'` of `μ_n` by its **exponent set** `E : Finset G` over the cyclic rotation
group `G ≅ ZMod n` (`μ_n ≅ ZMod n`, `ζ·R' ↦ E + 1`). The rotation action is translation `E ↦ E + j`.

  **Parity criterion (`even_card_of_fixed_by_orderTwo`).** If an **involution** translation by `h`
  (`h ≠ 0`, `h + h = 0`) fixes `E` (`∀ x ∈ E, x + h ∈ E`), then `E.card` is **even**: `x ↦ x + h` is a
  fixed-point-free involution of `E`, so `E` splits into 2-element orbits.

  **Even-order ⇒ even card (`even_card_of_fixed_by_evenOrder`).** If a translation by `j` whose
  additive order is even and ≥ 2 fixes `E` (`∀ x ∈ E, x + j ∈ E`), then `E.card` is even (the
  half-order multiple `h = (d/2)•j` is an order-two element of `⟨j⟩` that still fixes `E`).

  **Freeness for `n = 2^a`, odd `k+1` (`odd_card_not_fixed_of_evenOrder`).** When the rotation
  element `j ≠ 0` has even additive order (true for every nonzero `j` in `ZMod (2^a)`), an
  **odd**-card `E` cannot be fixed by translation-by-`j`: its rotation orbit has size `> 1`. In the
  prize regime `k = n/4`, `k+1 = n/4+1` is odd, so the action is free (orbit size exactly `n`).

## Honest scope
This is the **orbit-SIZE** half of `D*(m) = (orbit size)·#clique-orbits(m)`, NOT a bound on
`#clique-orbits(m)` (the irreducible open cyclotomic-collision content `lalalune` pinned). Pure cyclic
parity: character-sum-free, char-agnostic, NOT thinness-essential; does **not** close CORE
`M(μ_n) ≤ C·√(n·log(p/n))`. It removes the orbit-size slack ("`≤ n`" ⤳ "`= n`").

Probe: `scripts/probes/probe_clique_orbit_freeness.py` (freeness of `E ↦ E+j` on `(k+1)`-subsets of
`ZMod n`; EVEN `k+1` stabilized, ODD `k+1` free; arithmetic + direct, n up to 256; NEVER `n=q−1`).
-/

open scoped Pointwise

namespace ProximityGap.CliqueOrbitFreeness

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- **A fixed-point-free involution translation forces even cardinality.**
If `h ≠ 0` with `h + h = 0` (an order-two element) and the finset `E` is closed under translation by
`h` (`∀ x ∈ E, x + h ∈ E`), then `E.card` is even: `x ↦ x + h` is a fixed-point-free involution of
`E`, so `E` splits into 2-element orbits. Proved by strong induction on `E.card`, peeling off the
pair `{x, x+h}` at each step. -/
theorem even_card_of_fixed_by_orderTwo {h : G} (hne : h ≠ 0) (hord : h + h = 0) :
    ∀ E : Finset G, (∀ x ∈ E, x + h ∈ E) → Even E.card := by
  intro E
  induction E using Finset.strongInduction with
  | _ E ih =>
    intro hcl
    rcases E.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · -- `x + h ∈ E`, distinct from `x`, peel the pair `{x, x+h}`.
      have hxh : x + h ∈ E := hcl x hx
      have hxne : x + h ≠ x := by
        intro hc
        exact hne (by
          have : x + h = x + 0 := by simpa using hc
          exact add_left_cancel this)
      set p : Finset G := {x, x + h} with hp
      have hpsub : p ⊆ E := by
        intro y hy
        rw [hp, Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact hx
        · exact hxh
      set E' : Finset G := E \ p with hE'
      have hssub : E' ⊂ E := by
        refine Finset.sdiff_ssubset hpsub ?_
        exact ⟨x, by rw [hp]; exact Finset.mem_insert_self _ _⟩
      have hcl' : ∀ y ∈ E', y + h ∈ E' := by
        -- (closure descends to `E' = E \ {x, x+h}`)
        intro y hy
        rw [hE', Finset.mem_sdiff] at hy ⊢
        rw [hp, Finset.mem_insert, Finset.mem_singleton] at hy
        simp only [not_or] at hy
        obtain ⟨hyE, hyx, hyxh⟩ := hy
        refine ⟨hcl y hyE, ?_⟩
        rw [hp, Finset.mem_insert, Finset.mem_singleton]
        simp only [not_or]
        constructor
        · -- y + h ≠ x : else y = x + h, but y ≠ x+h
          intro hc
          apply hyxh
          have hkey := congrArg (· + h) hc
          simp only [add_assoc, hord, add_zero] at hkey
          exact hkey
        · -- y + h ≠ x + h : else y = x, but y ≠ x
          intro hc
          apply hyx
          have hkey := congrArg (· + (-h)) hc
          simpa [add_assoc] using hkey
      have hpc : p.card = 2 := by
        rw [hp, Finset.card_insert_of_notMem, Finset.card_singleton]
        rw [Finset.mem_singleton]; exact fun hc => hxne hc.symm
      have hcard : E.card = E'.card + 2 := by
        have hadd := Finset.card_sdiff_add_card_eq_card (s := p) (t := E) hpsub
        rw [← hE'] at hadd
        omega
      rw [hcard]
      have hE'even : Even E'.card := ih E' hssub hcl'
      rcases hE'even with ⟨c, hc⟩
      exact ⟨c + 1, by omega⟩

omit [DecidableEq G] in
/-- **Closure under `j` propagates to closure under any multiple `m • j`.** If `E` is closed under
translation-by-`j`, it is closed under translation-by-`(m • j)` for every `m : ℕ`. -/
theorem fixed_nsmul {j : G} {E : Finset G} (hcl : ∀ x ∈ E, x + j ∈ E) :
    ∀ (m : ℕ), ∀ x ∈ E, x + m • j ∈ E := by
  intro m
  induction m with
  | zero => intro x hx; simpa using hx
  | succ k ih =>
      intro x hx
      have : x + (k + 1) • j = (x + k • j) + j := by
        rw [succ_nsmul, add_assoc]
      rw [this]
      exact hcl _ (ih x hx)

/-- **Even additive order of the rotation element forces even cardinality of a fixed set.**
If `j` has **even** additive order `d ≥ 2` and `E` is closed under translation-by-`j`, then `E.card`
is even. Mechanism: `h := (d/2) • j` is an order-two element (`h + h = d • j = 0`, `h ≠ 0` since
`d/2 < d = addOrderOf j`), and closure under `j` gives closure under `h` (`fixed_nsmul`); apply
`even_card_of_fixed_by_orderTwo`. -/
theorem even_card_of_fixed_by_evenOrder {j : G} (hev : Even (addOrderOf j))
    (hpos : 0 < addOrderOf j) {E : Finset G} (hcl : ∀ x ∈ E, x + j ∈ E) : Even E.card := by
  classical
  set d := addOrderOf j with hd
  obtain ⟨t, ht⟩ := hev          -- d = t + t
  set h := t • j with hh
  have htpos : 0 < t := by omega
  have htlt : t < d := by omega
  -- h + h = d • j = 0
  have hord : h + h = 0 := by
    have hhh : h + h = (t + t) • j := by rw [hh, add_nsmul]
    rw [hhh, ← ht, hd]
    exact addOrderOf_nsmul_eq_zero j
  -- h ≠ 0 : else addOrderOf j ∣ t with 0 < t < d
  have hne : h ≠ 0 := by
    intro hzero
    have hdvd : addOrderOf j ∣ t := (addOrderOf_dvd_iff_nsmul_eq_zero).mpr hzero
    have := Nat.le_of_dvd htpos hdvd
    omega
  -- closure under h = t • j from closure under j
  have hclh : ∀ x ∈ E, x + h ∈ E := fun x hx => fixed_nsmul hcl t x hx
  exact even_card_of_fixed_by_orderTwo hne hord E hclh

/-- **Freeness criterion: an odd-cardinality fixed set forces the trivial rotation.**
If every nonzero element `j` of the rotation group has **even** additive order (true for
`ZMod (2^a)`), then any **odd**-cardinality `E` is fixed (closed under translation-by-`j`) only by
`j = 0`. Contrapositive of `even_card_of_fixed_by_evenOrder`: a nonzero `j` fixing `E` would force
`E.card` even. This is the orbit-SIZE freeness: the translation-stabilizer of an odd-card `E` is
trivial, so its rotation orbit has size exactly `addOrderOf (1) = n` on `ZMod n`. -/
theorem fixed_eq_zero_of_odd_card
    (heven_order : ∀ j : G, j ≠ 0 → Even (addOrderOf j) ∧ 0 < addOrderOf j)
    {E : Finset G} (hodd : Odd E.card) {j : G} (hcl : ∀ x ∈ E, x + j ∈ E) : j = 0 := by
  by_contra hjne
  obtain ⟨hev, hpos⟩ := heven_order j hjne
  have : Even E.card := even_card_of_fixed_by_evenOrder hev hpos hcl
  exact (Nat.not_even_iff_odd.mpr hodd) this

/-! ### Prize-regime instantiation: the rotation group `ZMod (2^a)` -/

/-- **Every nonzero element of `ZMod (2^a)` has even (and positive) additive order** (`a ≥ 1`).
Its additive order divides `Nat.card (ZMod (2^a)) = 2^a`, so it is a power of `2`; being `> 1`
(a nonzero element has order `> 1`) it is `≥ 2`, hence even. This is the hypothesis that makes the
rotation action on `μ_{2^a}` free on odd-cardinality carriers. -/
theorem zmod_two_pow_even_order (a : ℕ) (j : ZMod (2 ^ a)) (hj : j ≠ 0) :
    Even (addOrderOf j) ∧ 0 < addOrderOf j := by
  haveI : NeZero (2 ^ a) := ⟨pow_ne_zero a two_ne_zero⟩
  haveI : Fintype (ZMod (2 ^ a)) := ZMod.fintype _
  have hpos : 0 < addOrderOf j := addOrderOf_pos j
  refine ⟨?_, hpos⟩
  -- addOrderOf j ∣ Nat.card (ZMod (2^a)) = 2^a
  have hdvd : addOrderOf j ∣ 2 ^ a := by
    have h := addOrderOf_dvd_natCard j
    rwa [Nat.card_eq_fintype_card, ZMod.card] at h
  -- a nonzero element has order ≠ 1 (else j = 1 • j = 0)
  have hne1 : addOrderOf j ≠ 1 := by
    intro h1
    apply hj
    have : (1 : ℕ) • j = 0 := by
      rw [← h1]; exact addOrderOf_nsmul_eq_zero j
    simpa using this
  -- order is a power of 2, and ≠ 1, so ≥ 2, so even
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hkpos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exact absurd (by rw [hk, hk0, pow_zero]) hne1
    · exact hk0
  rw [hk]
  have hkne : k ≠ 0 := by omega
  rw [Nat.even_pow]
  exact ⟨even_two, hkne⟩

/-- **Prize-regime freeness (the orbit-SIZE sharpening of `lalalune`'s `D*(m) = (orbit size ≤ n)·
#clique-orbits(m)`).** Over the rotation group `G = ZMod (2^a)` (so `n = 2^a`), an
**odd**-cardinality exponent set `E` (the prize regime `k = n/4` gives carrier size `k+1 = n/4+1`,
which is odd) is fixed by translation-by-`j` **only** for `j = 0`. Hence the rotation orbit of an
odd-card `E` is free: its stabilizer is trivial and the orbit has size exactly `n = 2^a`. The weak
"`orbit size ≤ n`" is sharpened to "`= n`", with NO cyclotomic content (that lives only in
`#clique-orbits(m)`, the irreducible open object). -/
theorem prize_regime_fixed_eq_zero (a : ℕ)
    {E : Finset (ZMod (2 ^ a))} (hodd : Odd E.card)
    {j : ZMod (2 ^ a)} (hcl : ∀ x ∈ E, x + j ∈ E) : j = 0 :=
  fixed_eq_zero_of_odd_card (fun j hj => zmod_two_pow_even_order a j hj) hodd hcl

end ProximityGap.CliqueOrbitFreeness

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only, no sorryAx)
#print axioms ProximityGap.CliqueOrbitFreeness.even_card_of_fixed_by_orderTwo
#print axioms ProximityGap.CliqueOrbitFreeness.fixed_nsmul
#print axioms ProximityGap.CliqueOrbitFreeness.even_card_of_fixed_by_evenOrder
#print axioms ProximityGap.CliqueOrbitFreeness.fixed_eq_zero_of_odd_card
#print axioms ProximityGap.CliqueOrbitFreeness.zmod_two_pow_even_order
#print axioms ProximityGap.CliqueOrbitFreeness.prize_regime_fixed_eq_zero

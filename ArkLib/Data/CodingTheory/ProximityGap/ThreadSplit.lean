/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.PowerBasis
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

/-!
# Issue #232 — THREAD-SPLIT: vanishing sums of `n`-th roots of unity split into
# `p` vanishing thread sums at `ζ^p` when `p² ∣ n`

O92 (`DeBruijnPrimePower.lean`) closed with one named wall for the full two-prime
de Bruijn 1953 theorem: **thread-split** — for `p² ∣ n` and a primitive `n`-th root
`ζ` in a characteristic-zero field, a vanishing sum `Σ_{e∈S} ζ^e = 0` splits
thread-by-thread: writing `e = r + p·e'` (`r < p`), every thread sum
`Σ_{e'∈T_r} (ζ^p)^{e'}` vanishes at level `n/p`.  This file is that brick.

* `minpoly_adjoin_pow_prime_eq_binomial` — **the engine**: for `n = p·m` with
  `p ∣ m` (i.e. `p² ∣ n`), the minimal polynomial of `ζ` over `ℚ⟮ζ^p⟯ = ℚ(ζ_{n/p})`
  is the monic binomial `X^p − ζ^p`.  Degree pinch: `≤ p` because `ζ` is a root of
  the binomial; `≥ p` by the totient tower bound
  `p·φ(m) = φ(p·m) = [ℚ(ζ):ℚ] ≤ [ℚ⟮ζ^p⟯⟮ζ⟯:ℚ] = φ(m)·[ℚ⟮ζ^p⟯⟮ζ⟯:ℚ⟮ζ^p⟯]`
  (`Nat.totient_mul_of_prime_of_dvd` — this is where `p² ∣ n` is load-bearing —
  plus `Module.finrank_mul_finrank`); then monic divisor of matching degree
  (`eq_of_monic_of_dvd_of_natDegree_le`), the `CRTPacketMinpoly` pattern at the
  NON-coprime tower step the coprime brick cannot reach.
* `sum_eq_thread_sum` — the exact bookkeeping identity (any commutative ring):
  `Σ_{e∈S} ζ^e = Σ_{r<p} ζ^r · Σ_{e'<m} [r + p·e' ∈ S]·(ζ^p)^{e'}` via the digit
  bijection `e ↦ (e % p, e / p)`.
* `thread_vanishing_of_vanishing` — **the headline**: vanishing at `ζ` forces every
  thread sum to vanish.  The thread sums live in `K = ℚ⟮ζ^p⟯`; the engine gives
  `(minpoly K ζ).natDegree = p`, so `1, ζ, …, ζ^{p-1}` are `K`-linearly independent
  (`linearIndependent_pow`), and coefficient extraction kills each thread.
* `vanishing_of_thread_vanishing` — the trivial converse (pure linearity, stated
  over any commutative ring with no primality or primitivity hypotheses).
* `thread_split_iff` — the iff, the exact shape O92's probe verified.

Falsified first (`scripts/probes/probe_thread_split.py`, exact integer arithmetic
mod `Φ_n`, exit 0): the iff EXHAUSTIVELY over all `2^20`/`2^28` masks at
`n = 20, 28` (via the set identity vanishing-family = thread-product-family; counts
`1156 = 34²`, `16900 = 130²`), and sampled with teeth at `n = 50` (`p = 5`) and
`n = 45` (`p = 3`): 2000 planted all-threads-vanishing masks vanish, 20000 random
masks satisfy the iff pointwise, and 2000 single-bit toggles of planted masks are
non-vanishing with the toggled thread exactly the bad thread.  O92's probe had
already verified the iff exhaustively at `n = 12, 18`.

What remains for the full two-prime de Bruijn theorem (named, not claimed): the
ASSEMBLY induction — recurse `thread_split_iff` down the digits of `n = p^a·q^b` to
the squarefree base `p·q`, apply O87's dichotomy
(`debruijn_squarefree_two_prime_iff`), and lift packets through `e ↦ r + p·e'`
(packets lift to packets, both types, as the probe's decomposer executes).  Pure
bookkeeping: every analytic ingredient is now in-tree.
-/

namespace ThreadSplit

open Polynomial Finset IntermediateField Module

/-- Roots of unity are integral over any base field of the ambient field. -/
private lemma isIntegral_of_pow_eq_one {F L : Type*} [Field F] [Field L] [Algebra F L]
    {x : L} {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) : IsIntegral F x :=
  ⟨X ^ m - 1, by simpa using monic_X_pow_sub_C (1 : F) hm.ne', by simp [hx]⟩

/-! ## The engine: `minpoly ℚ(ζ^p) ζ = X^p − ζ^p` when `p² ∣ n` -/

/-- **The engine lemma.**  For a prime `p`, `0 < m` with `p ∣ m` (so `p² ∣ p·m`),
and a primitive `(p·m)`-th root of unity `ζ` in a characteristic-zero field, the
minimal polynomial of `ζ` over the intermediate field `ℚ⟮ζ^p⟯ = ℚ(ζ_m)` is the
monic binomial `X^p − ζ^p`.  Equivalently `[ℚ(ζ_n) : ℚ(ζ_{n/p})] = p` with power
basis `1, ζ, …, ζ^{p-1}` — the non-coprime tower step.

Degree pinch: `minpoly ∣ X^p − ζ^p` (since `ζ` is a root) bounds the degree by `p`
from above; the totient identity `φ(p·m) = p·φ(m)` (LOAD-BEARING use of `p ∣ m`:
it fails for `p ∤ m`, where the true degree is `p − 1`) and tower
multiplicativity bound it from below. -/
theorem minpoly_adjoin_pow_prime_eq_binomial
    {L : Type*} [Field L] [CharZero L] {p m : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hpm : p ∣ m)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p * m)) :
    minpoly ℚ⟮ζ ^ p⟯ ζ = X ^ p - C (AdjoinSimple.gen ℚ (ζ ^ p)) := by
  classical
  have hn : 0 < p * m := Nat.mul_pos hp.pos hm
  -- `ζ^p` is a primitive `m`-th root
  have hζp : IsPrimitiveRoot (ζ ^ p) m := hζ.pow hn rfl
  -- integrality of the players
  have hintζ : IsIntegral ℚ ζ := isIntegral_of_pow_eq_one hn hζ.pow_eq_one
  have hintζp : IsIntegral ℚ (ζ ^ p) := isIntegral_of_pow_eq_one hm hζp.pow_eq_one
  have hintζK : IsIntegral ℚ⟮ζ ^ p⟯ ζ := isIntegral_of_pow_eq_one hn hζ.pow_eq_one
  -- divisibility by the monic binomial: `ζ` is a root of `X^p − ζ^p`
  have hdvd : minpoly ℚ⟮ζ ^ p⟯ ζ ∣ X ^ p - C (AdjoinSimple.gen ℚ (ζ ^ p)) := by
    apply minpoly.dvd
    rw [map_sub, map_pow, aeval_X, aeval_C, AdjoinSimple.algebraMap_gen, sub_self]
  -- absolute degrees over ℚ, via unconditional rationals-cyclotomic irreducibility
  have hrkK : finrank ℚ ℚ⟮ζ ^ p⟯ = m.totient := by
    rw [IntermediateField.adjoin.finrank hintζp, ← cyclotomic_eq_minpoly_rat hζp hm,
      natDegree_cyclotomic]
  have hrkZ : finrank ℚ ℚ⟮ζ⟯ = (p * m).totient := by
    rw [IntermediateField.adjoin.finrank hintζ, ← cyclotomic_eq_minpoly_rat hζ hn,
      natDegree_cyclotomic]
  -- finite dimensionality up the tower
  haveI : FiniteDimensional ℚ ℚ⟮ζ ^ p⟯ := IntermediateField.adjoin.finiteDimensional hintζp
  haveI : FiniteDimensional ℚ⟮ζ ^ p⟯ ℚ⟮ζ ^ p⟯⟮ζ⟯ :=
    IntermediateField.adjoin.finiteDimensional hintζK
  haveI : FiniteDimensional ℚ ℚ⟮ζ ^ p⟯⟮ζ⟯ := Module.Finite.trans ℚ⟮ζ ^ p⟯ ℚ⟮ζ ^ p⟯⟮ζ⟯
  -- `ℚ⟮ζ⟯` embeds ℚ-linearly into `ℚ⟮ζ^p⟯⟮ζ⟯`
  have hζE : ζ ∈ ℚ⟮ζ ^ p⟯⟮ζ⟯ := mem_adjoin_simple_self ℚ⟮ζ ^ p⟯ ζ
  have hsub : ∀ {x : L}, x ∈ ℚ⟮ζ⟯ → x ∈ ℚ⟮ζ ^ p⟯⟮ζ⟯ := by
    intro x hx
    have hle : ℚ⟮ζ⟯ ≤ (ℚ⟮ζ ^ p⟯⟮ζ⟯).restrictScalars ℚ := by
      rw [adjoin_le_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hζE
    exact hle hx
  let f : ℚ⟮ζ⟯ →ₗ[ℚ] ℚ⟮ζ ^ p⟯⟮ζ⟯ :=
    { toFun := fun x => ⟨x.1, hsub x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective f := fun x y hxy => by
    have h1 := congrArg Subtype.val hxy
    exact Subtype.ext h1
  have hle : finrank ℚ ℚ⟮ζ⟯ ≤ finrank ℚ ℚ⟮ζ ^ p⟯⟮ζ⟯ :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have htower : finrank ℚ ℚ⟮ζ ^ p⟯ * finrank ℚ⟮ζ ^ p⟯ ℚ⟮ζ ^ p⟯⟮ζ⟯
      = finrank ℚ ℚ⟮ζ ^ p⟯⟮ζ⟯ :=
    Module.finrank_mul_finrank ℚ ℚ⟮ζ ^ p⟯ ℚ⟮ζ ^ p⟯⟮ζ⟯
  -- the totient pinch: `p ≤ natDegree (minpoly ℚ⟮ζ^p⟯ ζ)`
  have hdeg_ge : p ≤ (minpoly ℚ⟮ζ ^ p⟯ ζ).natDegree := by
    have hmul : m.totient * p ≤ m.totient * finrank ℚ⟮ζ ^ p⟯ ℚ⟮ζ ^ p⟯⟮ζ⟯ := by
      calc m.totient * p = p * m.totient := Nat.mul_comm _ _
        _ = (p * m).totient := (Nat.totient_mul_of_prime_of_dvd hp hpm).symm
        _ = finrank ℚ ℚ⟮ζ⟯ := hrkZ.symm
        _ ≤ finrank ℚ ℚ⟮ζ ^ p⟯⟮ζ⟯ := hle
        _ = finrank ℚ ℚ⟮ζ ^ p⟯ * finrank ℚ⟮ζ ^ p⟯ ℚ⟮ζ ^ p⟯⟮ζ⟯ := htower.symm
        _ = m.totient * finrank ℚ⟮ζ ^ p⟯ ℚ⟮ζ ^ p⟯⟮ζ⟯ := by rw [hrkK]
    have h2 : p ≤ finrank ℚ⟮ζ ^ p⟯ ℚ⟮ζ ^ p⟯⟮ζ⟯ :=
      Nat.le_of_mul_le_mul_left hmul (Nat.totient_pos.mpr hm)
    rwa [IntermediateField.adjoin.finrank hintζK] at h2
  -- monic divisor of matching degree
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintζK)
    (monic_X_pow_sub_C _ hp.pos.ne') hdvd
    (by rw [natDegree_X_pow_sub_C]; exact hdeg_ge)).symm

/-- The tower degree, extracted: `[ℚ(ζ_n) : ℚ(ζ_{n/p})] = p` when `p² ∣ n`. -/
theorem natDegree_minpoly_adjoin_pow_prime
    {L : Type*} [Field L] [CharZero L] {p m : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hpm : p ∣ m)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p * m)) :
    (minpoly ℚ⟮ζ ^ p⟯ ζ).natDegree = p := by
  rw [minpoly_adjoin_pow_prime_eq_binomial hp hm hpm hζ, natDegree_X_pow_sub_C]

/-! ## The bookkeeping identity: digit decomposition of the sum -/

/-- **The thread decomposition identity** (any commutative ring, no hypotheses on
`ζ` beyond the ring structure): a sum of powers over exponents `< p·m` regroups by
the bottom `p`-adic digit `e = r + p·e'` into `p` thread sums at `ζ^p`. -/
lemma sum_eq_thread_sum {L : Type*} [CommRing L] {p m : ℕ} (hp : 0 < p)
    (ζ : L) {S : Finset ℕ} (hS : ∀ e ∈ S, e < p * m) :
    ∑ e ∈ S, ζ ^ e
      = ∑ r ∈ Finset.range p,
          ζ ^ r * ∑ e' ∈ Finset.range m, (if r + p * e' ∈ S then (ζ ^ p) ^ e' else 0) := by
  classical
  calc ∑ e ∈ S, ζ ^ e
      = ∑ e ∈ Finset.range (p * m), (if e ∈ S then ζ ^ e else 0) := by
        rw [Finset.sum_ite_mem,
          Finset.inter_eq_right.mpr (fun e he => Finset.mem_range.mpr (hS e he))]
    _ = ∑ x ∈ Finset.range p ×ˢ Finset.range m,
          (if x.1 + p * x.2 ∈ S then ζ ^ (x.1 + p * x.2) else 0) := by
        refine (Finset.sum_nbij' (fun x : ℕ × ℕ => x.1 + p * x.2)
          (fun e => (e % p, e / p)) ?_ ?_ ?_ ?_ ?_).symm
        · -- maps into `range (p * m)`
          rintro ⟨r, c⟩ hx
          rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx
          rw [Finset.mem_range]
          calc r + p * c < p + p * c := by omega
            _ = p * (c + 1) := by ring
            _ ≤ p * m := Nat.mul_le_mul_left p (by omega)
        · -- maps back into the digit grid
          intro e he
          rw [Finset.mem_range] at he
          rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
          refine ⟨Nat.mod_lt _ hp, ?_⟩
          rw [Nat.div_lt_iff_lt_mul hp, Nat.mul_comm m p]
          exact he
        · -- left inverse on the grid
          rintro ⟨r, c⟩ hx
          rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx
          have h1 : (r + p * c) % p = r := by
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx.1]
          have h2 : (r + p * c) / p = c := by
            rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hx.1, Nat.zero_add]
          exact Prod.ext h1 h2
        · -- right inverse on `range (p * m)`
          intro e _
          exact Nat.mod_add_div e p
        · -- summand transport
          rintro ⟨r, c⟩ _
          rfl
    _ = ∑ r ∈ Finset.range p, ∑ e' ∈ Finset.range m,
          (if r + p * e' ∈ S then ζ ^ (r + p * e') else 0) := Finset.sum_product _ _ _
    _ = ∑ r ∈ Finset.range p,
          ζ ^ r * ∑ e' ∈ Finset.range m, (if r + p * e' ∈ S then (ζ ^ p) ^ e' else 0) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e' _ => ?_
        rw [mul_ite, mul_zero, ← pow_mul, ← pow_add]

/-! ## The headline: thread-split -/

/-- **THREAD-SPLIT (the O92 wall).**  For a prime `p` with `p² ∣ n` (written
`n = p·m`, `p ∣ m`) and a primitive `n`-th root of unity `ζ` in a
characteristic-zero field, a vanishing power sum `Σ_{e∈S} ζ^e = 0` over exponents
`S ⊆ [0, n)` splits thread-by-thread: for every residue `r < p`, the thread sum
`Σ_{e' < m, r + p·e' ∈ S} (ζ^p)^{e'}` vanishes — a vanishing sum at level `n/p`
for the primitive root `ζ^p`.

Mechanism: the thread sums are elements of `K = ℚ⟮ζ^p⟯`, the engine pins
`(minpoly K ζ).natDegree = p`, so `1, ζ, …, ζ^{p-1}` are `K`-linearly independent
(`linearIndependent_pow`) and the relation `Σ_{r<p} c_r·ζ^r = 0` from
`sum_eq_thread_sum` forces every `c_r = 0`. -/
theorem thread_vanishing_of_vanishing {L : Type*} [Field L] [CharZero L] {p m : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hpm : p ∣ m)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p * m))
    {S : Finset ℕ} (hS : ∀ e ∈ S, e < p * m)
    (hsum : ∑ e ∈ S, ζ ^ e = 0) :
    ∀ r < p, ∑ e' ∈ Finset.range m, (if r + p * e' ∈ S then (ζ ^ p) ^ e' else 0) = 0 := by
  classical
  intro r hr
  -- the thread coefficients, living inside `K = ℚ⟮ζ^p⟯`
  set g : ℚ⟮ζ ^ p⟯ := AdjoinSimple.gen ℚ (ζ ^ p) with hg
  have hcoe : algebraMap ℚ⟮ζ ^ p⟯ L g = ζ ^ p := AdjoinSimple.algebraMap_gen ℚ (ζ ^ p)
  set c : ℕ → ℚ⟮ζ ^ p⟯ :=
    fun r => ∑ e' ∈ Finset.range m, (if r + p * e' ∈ S then g ^ e' else 0) with hc
  have hmap : ∀ r : ℕ, algebraMap ℚ⟮ζ ^ p⟯ L (c r)
      = ∑ e' ∈ Finset.range m, (if r + p * e' ∈ S then (ζ ^ p) ^ e' else 0) := by
    intro r
    rw [hc, map_sum]
    refine Finset.sum_congr rfl fun e' _ => ?_
    rw [apply_ite (algebraMap ℚ⟮ζ ^ p⟯ L), map_pow, hcoe, map_zero]
  -- the vanishing sum as a `K`-linear relation on `1, ζ, …, ζ^{p-1}`
  have hrel : ∑ i : Fin p, c i.val • ζ ^ (i : ℕ) = 0 := by
    calc ∑ i : Fin p, c i.val • ζ ^ (i : ℕ)
        = ∑ r ∈ Finset.range p, c r • ζ ^ r :=
          Fin.sum_univ_eq_sum_range (fun r => c r • ζ ^ r) p
      _ = ∑ r ∈ Finset.range p, ζ ^ r *
            ∑ e' ∈ Finset.range m, (if r + p * e' ∈ S then (ζ ^ p) ^ e' else 0) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Algebra.smul_def, hmap, mul_comm]
      _ = ∑ e ∈ S, ζ ^ e := (sum_eq_thread_sum hp.pos ζ hS).symm
      _ = 0 := hsum
  -- linear independence of `1, ζ, …, ζ^{p-1}` over `K` (the engine)
  have hLI : LinearIndependent ℚ⟮ζ ^ p⟯ fun i : Fin p => ζ ^ (i : ℕ) := by
    have h := linearIndependent_pow (K := ℚ⟮ζ ^ p⟯) ζ
    rwa [natDegree_minpoly_adjoin_pow_prime hp hm hpm hζ] at h
  -- coefficient extraction kills the thread, then map back to `L`
  have hzero : c r = 0 :=
    Fintype.linearIndependent_iff.mp hLI (fun i => c i.val) hrel ⟨r, hr⟩
  have := congrArg (algebraMap ℚ⟮ζ ^ p⟯ L) hzero
  rwa [map_zero, hmap] at this

/-- **The trivial converse** (pure linearity, any commutative ring — no primality,
no primitivity): if every thread sum vanishes, the full sum vanishes. -/
theorem vanishing_of_thread_vanishing {L : Type*} [CommRing L] {p m : ℕ}
    (hp : 0 < p) (ζ : L) {S : Finset ℕ} (hS : ∀ e ∈ S, e < p * m)
    (h : ∀ r < p, ∑ e' ∈ Finset.range m, (if r + p * e' ∈ S then (ζ ^ p) ^ e' else 0) = 0) :
    ∑ e ∈ S, ζ ^ e = 0 := by
  rw [sum_eq_thread_sum hp ζ hS]
  refine Finset.sum_eq_zero fun r hr => ?_
  rw [h r (Finset.mem_range.mp hr), mul_zero]

/-- **Thread-split as an iff** — the exact shape verified exhaustively by the probe
at `n = 12, 18, 20, 28` and sampled with teeth at `n = 45, 50`: for `p² ∣ n`, a
power sum over `S ⊆ [0, n)` vanishes at a primitive `n`-th root `ζ` IFF all `p`
thread sums vanish at `ζ^p` (a primitive `(n/p)`-th root). -/
theorem thread_split_iff {L : Type*} [Field L] [CharZero L] {p m : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hpm : p ∣ m)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p * m))
    {S : Finset ℕ} (hS : ∀ e ∈ S, e < p * m) :
    (∑ e ∈ S, ζ ^ e = 0)
      ↔ ∀ r < p, ∑ e' ∈ Finset.range m, (if r + p * e' ∈ S then (ζ ^ p) ^ e' else 0) = 0 :=
  ⟨thread_vanishing_of_vanishing hp hm hpm hζ hS,
   vanishing_of_thread_vanishing hp.pos ζ hS⟩

/-! ## Non-vacuity witnesses (fired at `ℂ`, `n = 12 = 2²·3`, with teeth)

The forward direction converts a hypothetical vanishing of the {0,1}-sum into the
decidably false statement `1 = 0` via its `r = 0` thread — so `1 + ζ₁₂ ≠ 0` falls
out of thread-split alone.  The converse produces the genuine nonempty vanishing
sum `ζ₁₂ + ζ₁₂⁷ = 0` from its two vanishing threads (`r = 1` thread `= 1 + ζ₁₂⁶`,
killed by `ζ₁₂⁶ = −1`; `r = 0` thread empty). -/

private lemma exp_twelfth_primitive :
    IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 12)) (2 * 6) := by
  have h := Complex.isPrimitiveRoot_exp 12 (by norm_num)
  norm_num at h ⊢
  exact h

/-- The forward direction fired (with teeth): `1 + ζ₁₂ ≠ 0` derived from
thread-split — a hypothetical vanishing of `Σ_{e∈{0,1}} ζ₁₂^e` would force its
`r = 0` thread sum, which evaluates to `1`, to vanish. -/
example : (1 : ℂ) + Complex.exp (2 * Real.pi * Complex.I / 12) ≠ 0 := by
  intro hcon
  have hS : ∀ e ∈ ({0, 1} : Finset ℕ), e < 2 * 6 := by decide
  have hsum : ∑ e ∈ ({0, 1} : Finset ℕ),
      Complex.exp (2 * Real.pi * Complex.I / 12) ^ e = 0 := by
    rw [Finset.sum_insert (by decide), Finset.sum_singleton, pow_zero, pow_one]
    exact hcon
  have h := thread_vanishing_of_vanishing Nat.prime_two (by norm_num) (by norm_num)
    exp_twelfth_primitive hS hsum 0 (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at h
  norm_num [Finset.mem_insert, Finset.mem_singleton] at h

/-- The converse fired: the two threads of `S = {1, 7}` vanish (the `r = 1` thread
is `1 + ζ₁₂⁶ = 0` since `ζ₁₂⁶` is a primitive square root of unity; the `r = 0`
thread is empty), so `ζ₁₂ + ζ₁₂⁷ = 0` — a genuine nonempty vanishing sum produced
by the brick. -/
example : Complex.exp (2 * Real.pi * Complex.I / 12)
    + Complex.exp (2 * Real.pi * Complex.I / 12) ^ 7 = 0 := by
  have h6 : Complex.exp (2 * Real.pi * Complex.I / 12) ^ 6 = -1 := by
    have h2 : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 12) ^ 6) 2 :=
      exp_twelfth_primitive.pow (by norm_num) (by norm_num)
    exact h2.eq_neg_one_of_two_right
  have hS : ∀ e ∈ ({1, 7} : Finset ℕ), e < 2 * 6 := by decide
  have hv := vanishing_of_thread_vanishing (p := 2) (m := 6) (by norm_num)
    (Complex.exp (2 * Real.pi * Complex.I / 12)) hS ?_
  · rw [Finset.sum_insert (by decide), Finset.sum_singleton, pow_one] at hv
    exact hv
  · intro r hr
    interval_cases r
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      norm_num [Finset.mem_insert, Finset.mem_singleton]
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      norm_num [Finset.mem_insert, Finset.mem_singleton, ← pow_mul]
      rw [h6]
      ring

end ThreadSplit

#print axioms ThreadSplit.minpoly_adjoin_pow_prime_eq_binomial
#print axioms ThreadSplit.natDegree_minpoly_adjoin_pow_prime
#print axioms ThreadSplit.sum_eq_thread_sum
#print axioms ThreadSplit.thread_vanishing_of_vanishing
#print axioms ThreadSplit.vanishing_of_thread_vanishing
#print axioms ThreadSplit.thread_split_iff

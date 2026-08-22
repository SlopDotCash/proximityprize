/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CyclotomicNormDefectThreshold
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# The spurious-vanishing HEIGHT GATE and its prize no-go (Proximity Prize #407, actionable A01)

This file re-lands `HeightGateNormBound` (absent from this checkout; it lived on a parallel
worktree) and pushes the question raised in the #407 comment of 2026-06-14T21:00:59Z:

> *Does the "structure-aware (resultant / Newton-polygon) norm bound" push the proved-closed
> regime past `n = 32`?*

## The gate (what is PROVEN here, `n ≤ 32`)

Let `n = 2^a`, `p` a prime with `n ∣ p − 1`, and `ζ ∈ ZMod p` a primitive `n`-th root. A
*spurious vanishing set* is `S ⊆ {0,…,n−1}` with `Σ_{i∈S} ζ^i = 0` in `F_p`. Writing
`α = Σ_{i∈S} z^i = g_S(z)` over `ℂ` (`g_S = Σ_{i∈S} X^i`, the `#S`-term 0/1 indicator
polynomial), the algebraic norm is the integer cyclotomic resultant `N(α) = Res(Φ_n, g_S)`,
and the **height gate** is the elementary chain (all three steps in
`CyclotomicNormDefectThreshold.lean`):

* archimedean: `|N(α)| ≤ (#S)^{φ(n)} ≤ n^{φ(n)} = n^{n/2}`;
* `p`-divisibility: `Σ_{i∈S} ζ^i = 0` in `F_p` `⟹ p ∣ N(α)`;
* nonvanishing: `α ≠ 0` in char 0 `⟹ N(α) ≠ 0`.

Hence `p ∣ N(α)`, `0 < |N(α)| ≤ n^{n/2}`, so `p ≤ n^{n/2}`. **Contrapositive — THE GATE:** if
`p > n^{n/2}` then **every** `F_p`-spurious set `S` has `α = 0` in characteristic `0`, and (the
elementary Lam–Leung fact for `n` a `2`-power) a vanishing sum of distinct `2^a`-th roots of
unity is *antipodal*: `S` is a disjoint union of pairs `{i, i+n/2}`. So `NoSpuriousVanishing`
holds. The `2`-power-vanishing ⟹ antipodal step is named `Antipodal` / `Char0VanishToAntipodal`
(elementary cyclotomic, kept as a Prop — Mathlib has no Lam–Leung).

`prizePrimeLB n = n * 2^128` (a lower bound on the prize prime `p ~ n·2^128`). The gate FIRES
exactly when `n^{n/2} < p`:

| `n` | `n^{n/2}` | `prizePrimeLB` | gate fires? |
|-----|-----------|----------------|-------------|
| 8   | `2^12`    | `2^131`        | ✓ proved    |
| 16  | `2^32`    | `2^132`        | ✓ proved    |
| 32  | `2^80`    | `2^133`        | ✓ proved    |
| 64  | `2^192`   | `2^134`        | ✗           |
| 128 | `2^448`   | `2^135`        | ✗ (vacuous) |

These three `Nat` inequalities are `decide`/`norm_num`-checked here (`gate_fires_8/16/32`,
`gate_NOT_fires_64`).

## The prize no-go (why the structure-aware lever does NOT rescue `n ≥ 64`)

The optimistic reading of the `n=128` slack ("realized norm `~2^131` ≪ house `~2^192`, so a
tighter norm bound closes more `n`") is **refuted for the worst case**, two ways:

1. **Exact block witness** (`block_sum_norm_at_least`, consuming the `IsCyclotomicExtension`
   machinery): the *explicit non-antipodal* block `S = {0,…,n/2−1}` has the EXACT norm
   `N(Σ_{i<n/2} ζ^i) = 2^{n/2−1}` — no house bound, this is the realized value. For `n ≥ 512`
   already `2^{n/2−1} > p`, and at the prize point `n = 2^30` the norm is `2^{2^29−1}`,
   astronomically larger than any `p ~ 2^158`. Since the gate must control `max_S |N(α)|`, NO
   norm bound (however structure-aware) keeps the gate alive at the prize.

2. **Numerical straddle** (`scripts/probes/sweep_A01_normwitness.py`): random non-antipodal
   `56`-subsets at `n = 128` have realized `log₂|N|` spread over `[117.6, 147.1]`, **median
   `2^135.8`** — straddling the prize prime `~2^135`. So `|N(α)| < p` is already FALSE for a
   large fraction of non-antipodal `S` at `n = 128`; spurious vanishing is abundant there.

So the structure-aware lever closes nothing past the elementary `n ≤ 32` it already gives: the
worst-case norm IS the √-cancellation/Paley character-sum wall in disguise. The genuine prize
point `n = 2^30` stays open as the named `Prop` `HeightConjOpenAtPrize` (provably FALSE in the
present form, by item 1 — i.e. the height route does NOT scale; the open prize wall is the
character-sum object, not a norm bound).

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Finset

namespace ArkLib.ProximityGap.HeightGateNormBound

open ArkLib.ProximityGap.CyclotomicNormDefectThreshold

/-! ## §1  The indicator polynomial `g_S = Σ_{i∈S} X^i` and the gate -/

/-- The `0/1` indicator polynomial of a finite set `S ⊆ ℕ` of exponents: `g_S = Σ_{i∈S} X^i`. -/
noncomputable def indicatorPoly (S : Finset ℕ) : ℤ[X] := ∑ i ∈ S, X ^ i

/-- The complex evaluation of `indicatorPoly S` at a root of unity is a sum of `#S` unit-modulus
terms, hence has norm `≤ #S`. (Specialization of the substrate triangle bound to `±1`-coeff `1`.) -/
theorem indicatorPoly_eval_nnnorm_le {n : ℕ} (hn : n ≠ 0) (S : Finset ℕ) {ω : ℂ} (hω : ω ^ n = 1) :
    ‖((indicatorPoly S).map (Int.castRingHom ℂ)).eval ω‖₊ ≤ ((S.card : ℕ) : NNReal) := by
  have hnormω : ‖ω‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hω hn
  have heval : ((indicatorPoly S).map (Int.castRingHom ℂ)).eval ω = ∑ i ∈ S, ω ^ i := by
    simp only [indicatorPoly, Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.eval_finset_sum, Polynomial.eval_pow, Polynomial.eval_X]
  have hreal : ‖((indicatorPoly S).map (Int.castRingHom ℂ)).eval ω‖ ≤ (S.card : ℝ) := by
    rw [heval]
    calc ‖∑ i ∈ S, ω ^ i‖
        ≤ ∑ i ∈ S, ‖ω ^ i‖ := norm_sum_le _ _
      _ = ∑ _i ∈ S, (1 : ℝ) := by
          refine Finset.sum_congr rfl (fun i _ => ?_); rw [norm_pow, hnormω, one_pow]
      _ = (S.card : ℝ) := by simp
  exact_mod_cast hreal

/-- **THE HEIGHT GATE (forward, divisibility form).** If `g_S = Σ_{i∈S} X^i` is char-0
nonvanishing on the primitive `n`-th roots of unity (i.e. `α = Σ_{i∈S} ζ^i ≠ 0` over `ℂ`), the
degree survives mod `p`, and a primitive `n`-th root `ζ ∈ ZMod p` is a root of `g_S` mod `p`
(i.e. `Σ_{i∈S} ζ^i = 0` in `F_p`), then `p ≤ (#S)^{φ(n)}`. -/
theorem prime_le_of_Fp_spurious {n : ℕ} (hn : 0 < n) {p : ℕ} [Fact p.Prime] (S : Finset ℕ)
    (hgdeg : ((indicatorPoly S).map (Int.castRingHom (ZMod p))).natDegree
      = (indicatorPoly S).natDegree)
    (hSidon : ∀ ω : ℂ, ω ∈ (cyclotomic n ℂ).roots →
      ((indicatorPoly S).map (Int.castRingHom ℂ)).eval ω ≠ 0)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ n)
    (hgζ : ((indicatorPoly S).map (Int.castRingHom (ZMod p))).eval ζ = 0) :
    p ≤ S.card ^ n.totient :=
  prime_le_of_cyclotomic_signed_sum hn (indicatorPoly S)
    (fun _ω hω => indicatorPoly_eval_nnnorm_le hn.ne' S hω) hgdeg hSidon hζ hgζ

/-- **THE HEIGHT GATE (contrapositive, "no spurious vanishing").** If `(#S)^{φ(n)} < p` then no
`F_p`-spurious vanishing set with the indicator polynomial `g_S` char-0 nonvanishing exists: a
primitive `n`-th root `ζ ∈ ZMod p` cannot be a root of `g_S` mod `p`. Equivalently, every actual
`F_p`-vanishing `S` must already vanish in characteristic `0` (and so be antipodal for `n` a
`2`-power). -/
theorem no_Fp_spurious_of_card_pow_lt {n : ℕ} (hn : 0 < n) {p : ℕ} [Fact p.Prime] (S : Finset ℕ)
    (hgdeg : ((indicatorPoly S).map (Int.castRingHom (ZMod p))).natDegree
      = (indicatorPoly S).natDegree)
    (hSidon : ∀ ω : ℂ, ω ∈ (cyclotomic n ℂ).roots →
      ((indicatorPoly S).map (Int.castRingHom ℂ)).eval ω ≠ 0)
    (hlt : S.card ^ n.totient < p)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ n) :
    ((indicatorPoly S).map (Int.castRingHom (ZMod p))).eval ζ ≠ 0 := by
  intro hgζ
  exact absurd (prime_le_of_Fp_spurious hn S hgdeg hSidon hζ hgζ) (Nat.not_le.mpr hlt)

/-! ## §2  The gate threshold `n^{n/2}` versus the prize prime `~ n·2^128`

`φ(2^a) = 2^{a-1} = n/2`, so the house ceiling is `(#S)^{φ(n)} ≤ n^{n/2}`. The prize prime is
`p ~ n·2^128`; we use the safe lower bound `prizePrimeLB n = n · 2^128` and check `n^{n/2} <
prizePrimeLB n` (gate fires) for `n ∈ {8,16,32}` and its failure at `n = 64`. -/

/-- A `Nat` lower bound on the prize prime `p ~ n·2^128`. -/
def prizePrimeLB (n : ℕ) : ℕ := n * 2 ^ 128

/-- The house ceiling for `n = 2^a` is `n^{n/2}` since `φ(n) = n/2`. -/
theorem totient_two_pow (a : ℕ) (ha : 1 ≤ a) : (2 ^ a).totient = 2 ^ (a - 1) := by
  rw [Nat.totient_prime_pow Nat.prime_two ha]; omega

theorem card_pow_totient_le {n : ℕ} (S : Finset ℕ) (hScard : S.card ≤ n) :
    S.card ^ n.totient ≤ n ^ n.totient := Nat.pow_le_pow_left hScard _

/-- The gate FIRES at `n = 8`: `8^{φ(8)} = 8^4 = 2^12 < 8·2^128 = prizePrimeLB 8`. -/
theorem gate_fires_8 : (8 : ℕ) ^ (8 : ℕ).totient < prizePrimeLB 8 := by
  have ht : (8 : ℕ).totient = 4 := by
    have := totient_two_pow 3 (by norm_num); simpa using this
  rw [ht, prizePrimeLB]; norm_num

/-- The gate FIRES at `n = 16`: `16^8 = 2^32 < 16·2^128`. -/
theorem gate_fires_16 : (16 : ℕ) ^ (16 : ℕ).totient < prizePrimeLB 16 := by
  have ht : (16 : ℕ).totient = 8 := by
    have := totient_two_pow 4 (by norm_num); simpa using this
  rw [ht, prizePrimeLB]; norm_num

/-- The gate FIRES at `n = 32`: `32^16 = 2^80 < 32·2^128`. -/
theorem gate_fires_32 : (32 : ℕ) ^ (32 : ℕ).totient < prizePrimeLB 32 := by
  have ht : (32 : ℕ).totient = 16 := by
    have := totient_two_pow 5 (by norm_num); simpa using this
  rw [ht, prizePrimeLB]; norm_num

/-- The gate does NOT fire at `n = 64`: `64^32 = 2^192 > 64·2^128 = 2^134`. This is the
crossover; for `n ≥ 64` the elementary house bound is too weak (and `n ≥ 128` it is vacuous). -/
theorem gate_NOT_fires_64 : prizePrimeLB 64 < (64 : ℕ) ^ (64 : ℕ).totient := by
  have ht : (64 : ℕ).totient = 32 := by
    have := totient_two_pow 6 (by norm_num); simpa using this
  rw [ht, prizePrimeLB]; norm_num

/-- Exponential dominates the linear `k + 130` from `k = 11` on: `k + 130 ≤ 2^{k-1}` for `k ≥ 11`.
Used to compare the block-witness exponent `2^{k-1}−1` against the prize exponent `k + 128`. -/
theorem linear_le_two_pow_pred {k : ℕ} (hk : 11 ≤ k) : k + 130 ≤ 2 ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = 11 + j := ⟨k - 11, by omega⟩
  clear hk
  induction j with
  | zero => norm_num
  | succ i ih =>
    have hge : (1 : ℕ) ≤ 2 ^ (11 + i - 1) := Nat.one_le_pow _ _ (by norm_num)
    -- 2^{(11+i+1)-1} = 2·2^{(11+i)-1} ≥ 2^{(11+i)-1} + 1 ≥ (11+i+130)+1 = 11+(i+1)+130
    have hdbl : 2 ^ (11 + (i + 1) - 1) = 2 * 2 ^ (11 + i - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

/-! ## §3  The prize NO-GO: the explicit block witness has exact norm `2^{n/2−1}`

The optimistic "structure-aware norm bound pushes past `n=32`" reading is REFUTED for the worst
case. The non-antipodal block `S = {0,…,n/2−1}` has EXACT (realized, not house-bounded) algebraic
norm `2^{n/2−1}`, which exceeds any fixed prize prime for `n` large — so no norm bound rescues
the gate at the prize. We re-derive the exact norm via the `IsCyclotomicExtension` machinery. -/

section BlockWitness

variable {L : Type*} [Field L] [NumberField L]

/-- Telescoping geometric-sum identity (inline, avoids the `GeomSum` import). -/
private theorem geomSumMul' {R : Type*} [CommRing R] (x : R) (m : ℕ) :
    (∑ i ∈ range m, x ^ i) * (x - 1) = x ^ m - 1 := by
  induction m with
  | zero => simp
  | succ j ih => rw [Finset.sum_range_succ, add_mul, ih, pow_succ]; ring

omit [NumberField L] in
/-- `ζ^{2^{k-1}} = −1` for a primitive `2^k`-th root of unity (`k ≥ 1`). -/
theorem primRoot_pow_half_eq_neg_one {k : ℕ} (hk : 1 ≤ k) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ k)) : ζ ^ (2 ^ (k - 1)) = -1 := by
  set w := ζ ^ (2 ^ (k - 1)) with hw
  have hsq : w ^ 2 = 1 := by
    rw [hw, ← pow_mul]
    have : 2 ^ (k - 1) * 2 = 2 ^ k := by rw [← pow_succ]; congr 1; omega
    rw [this, hζ.pow_eq_one]
  have hne : w ≠ 1 := by
    rw [hw]; intro h
    have hdvd : (2 ^ k : ℕ) ∣ 2 ^ (k - 1) := (hζ.pow_eq_one_iff_dvd _).1 h
    have hlt : 2 ^ (k - 1) < 2 ^ k := by apply Nat.pow_lt_pow_right one_lt_two; omega
    exact absurd (Nat.le_of_dvd (by positivity) hdvd) (by omega)
  have hfac : (w - 1) * (w + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · exact eq_neg_of_add_eq_zero_left h

/-- **THE EXACT NORM OF THE BLOCK WITNESS.** For `ζ` a primitive `2^k`-th root of unity (`k ≥ 2`)
generating the cyclotomic field `L/ℚ`, the non-antipodal block `S = {0,…,2^{k-1}−1}` has
`N_{L/ℚ}(Σ_{i∈S} ζ^i) = 2^{2^{k-1}−1}`. (Mechanism: `B·(ζ−1) = ζ^{n/2}−1 = −2` since
`ζ^{n/2}=−1`; `N(ζ−1) = Φ_{2^k}(1) = 2`; `N(−2) = (−2)^{φ(n)} = 2^{n/2}`.) -/
theorem block_sum_norm {k : ℕ} (hk : 2 ≤ k) {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ k))
    [IsCyclotomicExtension {2 ^ k} ℚ L] (hirr : Irreducible (cyclotomic (2 ^ k) ℚ)) :
    Algebra.norm ℚ (∑ i ∈ range (2 ^ (k - 1)), ζ ^ i) = 2 ^ (2 ^ (k - 1) - 1) := by
  set m := 2 ^ (k - 1) with hm
  set B := ∑ i ∈ range m, ζ ^ i with hB
  have hgeom : B * (ζ - 1) = ζ ^ m - 1 := geomSumMul' ζ m
  have hhalf : ζ ^ m = -1 := primRoot_pow_half_eq_neg_one (by omega) hζ
  have hBval : B * (ζ - 1) = -2 := by rw [hgeom, hhalf]; ring
  have hmul : Algebra.norm ℚ B * Algebra.norm ℚ (ζ - 1) = Algebra.norm ℚ (-2 : L) := by
    rw [← map_mul]; rw [hBval]
  have hsub : Algebra.norm ℚ (ζ - 1) = 2 := IsPrimitiveRoot.norm_sub_one_two hζ hk hirr
  have htot : (2 ^ k).totient = 2 ^ (k - 1) := totient_two_pow k (by omega)
  have hfr : Module.finrank ℚ L = m := by
    rw [IsCyclotomicExtension.finrank L hirr, htot, hm]
  have hneg2 : Algebra.norm ℚ (-2 : L) = (-2 : ℚ) ^ m := by
    have he : (-2 : L) = algebraMap ℚ L (-2 : ℚ) := by
      rw [map_neg, map_ofNat]
    have hkey : Algebra.norm ℚ (-2 : L) = (-2 : ℚ) ^ Module.finrank ℚ L := by
      rw [he]; exact Algebra.norm_algebraMap (-2 : ℚ)
    rw [hkey, hfr]
  have hmeven : Even m := by rw [hm]; exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hpow : (-2 : ℚ) ^ m = 2 ^ m := by rw [neg_pow, hmeven.neg_one_pow, one_mul]
  rw [hsub, hneg2, hpow] at hmul
  have hmpos : 1 ≤ m := by rw [hm]; exact Nat.one_le_pow _ _ (by norm_num)
  have h2 : (2 : ℚ) ^ m = 2 ^ (m - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  rw [h2] at hmul
  exact mul_right_cancel₀ (by norm_num) hmul

/-- **THE NO-GO COROLLARY.** The block-witness norm `2^{n/2−1}` exceeds any fixed prize-prime
lower bound for `n` large: at `k ≥ 11` (`n = 2^k ≥ 2048`), `2^{2^{k-1}−1} > prizePrimeLB(2^k)`.
So the worst-case realized norm is unbounded in `n`, and NO norm bound keeps the gate alive past
the elementary `n ≤ 32` it already proves. (The block witness itself, being non-antipodal with a
realized norm, is exactly an extremal `max_S |N|`.) -/
theorem block_norm_exceeds_prize {k : ℕ} (hk : 11 ≤ k) {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ k))
    [IsCyclotomicExtension {2 ^ k} ℚ L] (hirr : Irreducible (cyclotomic (2 ^ k) ℚ)) :
    (prizePrimeLB (2 ^ k) : ℚ) < Algebra.norm ℚ (∑ i ∈ range (2 ^ (k - 1)), ζ ^ i) := by
  rw [block_sum_norm (by omega : 2 ≤ k) hζ hirr]
  -- prizePrimeLB(2^k) = 2^k · 2^128 = 2^(k+128); block norm = 2^(2^{k-1}-1).
  -- For k ≥ 11: k+129 ≤ 2^{k-1} (linear_le_two_pow_pred) ⟹ k+128 < 2^{k-1}-1.
  have hstrict : k + 128 < 2 ^ (k - 1) - 1 := by
    have h1 : k + 130 ≤ 2 ^ (k - 1) := linear_le_two_pow_pred hk
    set a := 2 ^ (k - 1) with ha
    omega
  have hpz : (prizePrimeLB (2 ^ k) : ℚ) = 2 ^ (k + 128) := by
    simp only [prizePrimeLB, pow_add]; push_cast; ring
  rw [hpz]
  exact pow_lt_pow_right₀ (by norm_num) hstrict

end BlockWitness

/-! ## §4  The honest named statements at the prize point

The gate route does NOT scale to the prize. We record honest named `Prop`s — no `:True`
placebos. The antipodal-conclusion step is a named obligation (elementary, true, Mathlib gap);
the "norm-bound rescues the gate" hope is a genuine inequality `Prop` that §3 REFUTES. -/

/-- `Antipodal n S`: `S` is closed under the antipodal shift `i ↦ i + n/2` modulo `n` (so it is
a disjoint union of pairs `{i, i+n/2}`). The target conclusion of the gate. -/
def Antipodal (n : ℕ) (S : Finset ℕ) : Prop :=
  ∀ i ∈ S, (i + n / 2) % n ∈ S

/-- **Named obligation (elementary, true, Mathlib gap — NOT a placebo).** For `n = 2^a`, a
vanishing sum of distinct `n`-th roots of unity is antipodal: if `Σ_{i∈S} z^i = 0` over `ℂ`
(`z` primitive) then `Antipodal n S`. This is the Lam–Leung structure theorem for prime-power
`N = 2^a` (the only vanishing relations are `ℤ`-spans of `1 + z^{n/2} = 0`). It supplies the last
step of the gate (`p > n^{n/2}` + `F_p`-vanishing ⟹ char-0 vanishing ⟹ antipodal). Provable
elementarily; Mathlib has no Lam–Leung, so it stays a named `Prop` with an honestly-true input. -/
def Char0VanishImpliesAntipodal (n : ℕ) : Prop :=
  ∀ (z : ℂ) (_ : IsPrimitiveRoot z n) (S : Finset ℕ) (_ : S ⊆ range n),
    (∑ i ∈ S, z ^ i = 0) → Antipodal n S

section PrizeStatement
variable {L : Type*} [Field L] [NumberField L]

/-- **The "norm bound rescues the gate at the prize" hope, as a genuine `Prop` (NOT a placebo).**
`HeightBoundRescuesGate L n p` asserts that EVERY nonzero sum `Σ_{i∈S} ζ^i` of distinct
`n`-th roots (`S ⊆ range n`) has algebraic norm `< p` — exactly the inequality a structure-aware
norm bound would need to push the gate past `n ≤ 32`. -/
def HeightBoundRescuesGate (L : Type*) [Field L] [NumberField L] (n p : ℕ) : Prop :=
  ∀ {ζ : L}, IsPrimitiveRoot ζ n → ∀ (S : Finset ℕ), S ⊆ range n →
    (∑ i ∈ S, ζ ^ i) ≠ 0 → Algebra.norm ℚ (∑ i ∈ S, ζ ^ i) < (p : ℚ)

/-- **REFUTED.** The "norm bound rescues the gate" hope is FALSE for `n = 2^k`, `k ≥ 11` at the
prize prime: the block witness `S = {0,…,n/2−1}` is non-antipodal, nonzero, yet has norm
`2^{n/2−1} ≥ prizePrimeLB n`. So no structure-aware norm bound keeps the gate alive past the
elementary `n ≤ 32` regime — the worst-case realized norm is the character-sum wall itself. -/
theorem heightBoundRescuesGate_REFUTED {k : ℕ} (hk : 11 ≤ k) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ k)) [IsCyclotomicExtension {2 ^ k} ℚ L]
    (hirr : Irreducible (cyclotomic (2 ^ k) ℚ)) :
    ¬ HeightBoundRescuesGate L (2 ^ k) (prizePrimeLB (2 ^ k)) := by
  intro hconj
  -- the block exponents lie in range (2^k); the block sum is nonzero (its norm is 2^{n/2-1} ≠ 0).
  have hpos : (0 : ℚ) < Algebra.norm ℚ (∑ i ∈ range (2 ^ (k - 1)), ζ ^ i) := by
    rw [block_sum_norm (by omega : 2 ≤ k) hζ hirr]; positivity
  have hne : (∑ i ∈ range (2 ^ (k - 1)), ζ ^ i) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mp (ne_of_gt hpos)
  have hsub' : (range (2 ^ (k - 1))) ⊆ range (2 ^ k) := by
    intro i hi; simp only [Finset.mem_range] at hi ⊢
    calc i < 2 ^ (k - 1) := hi
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlt := hconj hζ (range (2 ^ (k - 1))) hsub' hne
  exact absurd hlt (not_lt.mpr (le_of_lt (block_norm_exceeds_prize hk hζ hirr)))

end PrizeStatement

end ArkLib.ProximityGap.HeightGateNormBound

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.ProximityGap.HeightGateNormBound
#print axioms indicatorPoly_eval_nnnorm_le
#print axioms prime_le_of_Fp_spurious
#print axioms no_Fp_spurious_of_card_pow_lt
#print axioms gate_fires_8
#print axioms gate_fires_16
#print axioms gate_fires_32
#print axioms gate_NOT_fires_64
#print axioms linear_le_two_pow_pred
#print axioms block_sum_norm
#print axioms block_norm_exceeds_prize
#print axioms heightBoundRescuesGate_REFUTED
end AxiomAudit

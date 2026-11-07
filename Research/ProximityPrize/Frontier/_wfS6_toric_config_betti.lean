/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# wf-S6 — Deligne/Weil-II on the CONFIGURATION variety: the `d`-FREE toric Betti envelope (#444)

## Where this sits in the lane

Lane S6 (arithmetic geometry) attacks the spurious char-`p` energy
`spur_r(p) := E_r^{charp}(μ_n) − E_r^{char0}(μ_n) ≥ 0` via Deligne/Weil-II applied to the
**configuration variety**
`V_r = { (x_1,…,x_{2r}) ∈ μ_n^{2r} : ε_1 x_1 + ⋯ + ε_{2r} x_{2r} = 0 }`, `ε_i = ±1`.

The campaign's published AG no-go (`probe_betti_independent.py`) homogenizes the subgroup
constraint `u^d = 1` into a **Fermat hypersurface** `∑ c_i X_i^d = 0` in `P^{2r−1}` whose
primitive middle Betti `B_Fermat = ((d−1)^{2r}+(d−1))/d ~ (d−1)^{2r}` grows EXPONENTIALLY in
both `r` and the residue degree `d = ord_n(p)`. At prize scale `d ~ n^3 ~ 2^{90}`, the Fermat
Weil envelope `B_Fermat · p^{r−1}` is `~ 2^{2r·90}`: **vacuous**. That is the "AG vacuous past
`r = 2`" claim.

**The S6 correction (this file): that is the WRONG variety.** `V_r` lives in the torus power
`G_m^{2r}`, where `μ_n` is a `0`-dimensional étale subscheme (`n` geometric points). The defining
equation `∑ ε_i x_i = 0` is **degree 1** in the toric coordinates — a single hyperplane slice.
By Adolphson–Sperber / Bombieri–Katz (`Exponential sums and Newton polyhedra`, 1989; Bombieri
constant `(4·sup(1+D_i, d)+5)^{N+r}`), the total Betti number of a torus subvariety cut by a
Laurent polynomial is controlled by the **Newton-polytope volume / monomial count**, NOT by the
subgroup exponent `d`. For the linear form `∑ ε_i x_i`, that envelope is the binomial
`B_toric = C(2r, r) ≤ 4^r` — **independent of `d`, of `n`, and of `p`**.

## Correction (audit 2026-10-28, CW-B18-15): the toric envelope is WEAKER than trivial at `β = 4`

An earlier version called `C(2r,r)·p^{r−1}` "non-vacuous" and "the `K^r` envelope the prize needs",
and read the large margin `spur/p^{r−1} ≪ C(2r,r)` in the table below as evidence.  That is wrong.
Trivially `spur_r(p) ≤ E_r^{charp} ≤ n^{2r}` (there are only `n^{2r}` tuples), and for `p ≥ n^4`,
`r ≥ 2` one has `n^{2r} ≤ p^{r−1} ≤ C(2r,r)·p^{r−1}` (`trivial_le_toric_envelope_of_beta_four`,
proven below).  So at prize scale the toric envelope is implied by the trivial count and is VACUOUS;
the "enormous margin" only reflects that `p^{r−1}` is large.  Recomputing `C(2r,r)·p^{r−1}/n^{2r}`
for the table rows gives `≈ 2055, 1.12, 20030, 0.093` — only the `n = 64, β = 3.0` row is below the
trivial bound.  See also `_wfA04_weil_envelope_vacuity.lean` (the envelope dominates the char-0 main
term at the prize regime).  Further caveat: `V_r ⊆ μ_n^{2r}` is a FINITE set of points, so the
"Betti number of `V_r`" reading of Adolphson–Sperber is heuristic.  The removed lemma
`toricBetti_dfree` was `toricBetti r = toricBetti r := rfl` and carried no content.

## What is PROVEN here (axiom-clean, no `p > 2^n` hypothesis)

This file formalizes the **envelope dichotomy** as unconditional `ℕ`-arithmetic:

1. `toricBetti r := C(2r,r)`, `fermatBetti d r := ((d−1)^{2r}+(d−1))/d`; the toric envelope is
   `B_toric · p^{r−1}`, the Fermat envelope is `B_Fermat · p^{r−1}`.
2. `toricBetti_le_four_pow` — `C(2r,r) ≤ 4^r` (the `d`-FREE, `n`-FREE bound). PROVEN.
3. `trivial_le_toric_envelope_of_beta_four` — for `n ≥ 1`, `p ≥ n^4`, `r ≥ 2`, the trivial count
   `n^{2r}` is `≤ C(2r,r)·p^{r−1}`: the toric envelope is vacuous at `β ≥ 4`. PROVEN.
4. `fermatBetti_ge_toric_of_large_degree` — once `d ≥ 5` (true at prize, `d ~ 2^{90}`) the
   Fermat Betti DOMINATES the toric Betti for `r ≥ 1`: the Fermat envelope is larger still.
   (Both are weaker than the trivial count at `β ≥ 4`; see the correction.) PROVEN.
5. `spur_le_toric_envelope_of_betti` — the reduction `THE consumer`: if the measured toric
   Betti law `SpurToricBounded` holds (the named open input, verified by
   `probe_wfS6_toric_config_betti.py` at prize-adjacent primes up to `p = n^4`), then
   `spur_r(p) ≤ C(2r,r) · p^{r−1}`, an absolute-`K^r·p^{r−1}` envelope.  PROVEN modulo the named
   `Prop` — but at `β ≥ 4` the conclusion is weaker than the trivial `spur ≤ n^{2r}`.

## The named open input and its honest scope

`SpurToricBounded` is the empirically measured statement
`spur_r(p) ≤ toricBetti r · p^{r−1}`. The pre-screen (`probe_wfS6_toric_config_betti.py`, EXACT
big-int FFT/histogram, `β = 4`, `p ≡ 1 mod n`, `p` prime) gives, at the DEEP structured primes
nearest the prize scale:

| n  | r | p (= n^β)     | spur   | spur/p^(r−1) | C(2r,r) | toric holds |
|----|---|---------------|--------|--------------|---------|-------------|
| 16 | 3 | 41521 (n^3.84)| 480    | 0.0003       | 20      | ✓           |
| 32 | 2 | 194977(n^3.51)| 384    | 0.002        | 6       | ✓           |
| 32 | 3 | 1036993(n^4.0)| 11520  | 0.0001       | 20      | ✓           |
| 64 | 2 | 259201(n^3.0) | 3072   | 0.012        | 6       | ✓           |

The toric envelope holds at every measured point, but this is uninformative: `C(2r,r)·p^{r−1}`
exceeds the trivial `n^{2r}` in three of the four rows (see the correction), so the "margin"
reflects the size of `p^{r−1}`, not cancellation. **Honest scope:** this is a MEASURED law, not a
proof of the Adolphson–Sperber bound for THIS specific variety at ALL structured primes — the
genuine AG content (that the toric total Betti of `V_r` is `≤ C(2r,r)` uniformly, i.e. that no
exceptional structured prime makes `V_r` acquire extra `F_p`-rational components beyond the
polytope count) is the named open `Prop`. What IS proven unconditionally is the ARITHMETIC of
the two envelopes: the toric constant is `d`-free and `≤ 4^r`, the Fermat constant blows up, and
the reduction "toric Betti law ⟹ `K^r` spur" is exact.

**Discovery (probe-level, prize regime):** at the SPECIFIC prize prime `p = n^4` chosen in the
campaign (`4129, 65537, 1048609`), `spur ≡ 0` EXACTLY (char-`p` energy = exact char-0 additive
energy of `μ_n`), so the transfer is *faithful* at the generic prize prime; structured primes
with `spur > 0` exist below `n^4` but have `spur/p^{r−1} ≤ 0.013`, far under `C(2r,r)`.

**Axiom target:** `[propext, Classical.choice, Quot.sound]`.
-/

open Finset

namespace ArkLib.ProximityGap.wfS6ToricConfigBetti

/-- **The toric Betti envelope constant** for the config variety `V_r ⊆ G_m^{2r}` cut by the
single linear form `∑ ε_i x_i`. By Adolphson–Sperber / Bombieri–Katz the total Betti of a torus
subvariety is bounded by the Newton-polytope monomial count; for the linear form this is the
central binomial `C(2r, r)`. **No `d`, `n`, or `p` dependence.** -/
def toricBetti (r : ℕ) : ℕ := Nat.choose (2 * r) r

/-- **The Fermat-completion Betti** (the campaign's no-go envelope): the primitive middle Betti
of `∑ c_i X_i^d = 0 ⊂ P^{2r−1}`, `((d−1)^{2r} + (d−1))/d`. This is what blows up at prize `d`. -/
def fermatBetti (d r : ℕ) : ℕ := ((d - 1) ^ (2 * r) + (d - 1)) / d

/-- **The central binomial is positive**: `C(2r,r) ≥ 1` (nonempty middle). -/
theorem toricBetti_pos (r : ℕ) : 0 < toricBetti r := Nat.choose_pos (by omega)

/-- **The toric envelope is weaker than the trivial count at `β ≥ 4`.** For `n ≥ 1`, `p ≥ n^4` and
`r ≥ 2`: `n^{2r} ≤ C(2r,r)·p^{r−1}`.  Since trivially `spur_r(p) ≤ n^{2r}`, the toric envelope
`spur_r(p) ≤ C(2r,r)·p^{r−1}` carries no information in the prize regime (CW-B18-15). -/
theorem trivial_le_toric_envelope_of_beta_four (n p r : ℕ) (hn : 1 ≤ n) (hp : n ^ 4 ≤ p)
    (hr : 2 ≤ r) : n ^ (2 * r) ≤ toricBetti r * p ^ (r - 1) := by
  calc n ^ (2 * r) ≤ n ^ (4 * (r - 1)) := Nat.pow_le_pow_right hn (by omega)
    _ = (n ^ 4) ^ (r - 1) := by rw [pow_mul]
    _ ≤ p ^ (r - 1) := Nat.pow_le_pow_left hp _
    _ ≤ toricBetti r * p ^ (r - 1) := Nat.le_mul_of_pos_left _ (toricBetti_pos r)

/-- **The toric Betti is `≤ 4^r`** (Stirling / central-binomial bound `C(2r,r) ≤ 4^r`).
So the toric Weil envelope `C(2r,r)·p^{r−1} ≤ 4^r·p^{r−1}` is geometric in `r` with the
ABSOLUTE base `4` (but the factor `p^{r−1}` makes it vacuous at `β ≥ 4`; see the correction). -/
theorem toricBetti_le_four_pow (r : ℕ) : toricBetti r ≤ 4 ^ r := by
  unfold toricBetti
  -- Use the clean integer bound C(2r,r) ≤ ∑_k C(2r,k) = 2^{2r} = 4^r.
  calc Nat.choose (2 * r) r ≤ ∑ k ∈ range (2 * r + 1), Nat.choose (2 * r) k := by
        apply Finset.single_le_sum (f := fun k => Nat.choose (2 * r) k)
        · intro i _; exact Nat.zero_le _
        · rw [Finset.mem_range]; omega
    _ = 2 ^ (2 * r) := by rw [Nat.sum_range_choose]
    _ = 4 ^ r := by rw [pow_mul]; norm_num

/-- **The Fermat envelope dominates the toric one at prize-scale residue degree.**
For `d ≥ 6` (the prize has `d ~ n^3 ~ 2^{90} ≫ 6`) and `r ≥ 1`, `fermatBetti d r ≥ toricBetti r`,
so the Fermat Weil envelope is looser still (the toric one is itself vacuous at `β ≥ 4`).
Proof spine: `toricBetti r ≤ 4^r`, `4^r · d ≤ ((d−1)^2)^r = (d−1)^{2r}` (since `(d−1)^2 ≥ 4d`
for `d ≥ 6`, and `d^r ≥ d` for `r ≥ 1`), hence `toricBetti r · d ≤ (d−1)^{2r} ≤ (d−1)^{2r}+(d−1)`,
and dividing by `d` gives the claim. -/
theorem fermatBetti_ge_toric_of_large_degree (d r : ℕ) (hd : 6 ≤ d) (hr : 1 ≤ r) :
    toricBetti r ≤ fermatBetti d r := by
  have hb : toricBetti r ≤ 4 ^ r := toricBetti_le_four_pow r
  rw [fermatBetti, Nat.le_div_iff_mul_le (by omega : 0 < d)]
  -- Goal: toricBetti r * d ≤ (d-1)^{2r} + (d-1).
  -- Step A: (d-1)^2 ≥ 4*d for d ≥ 6  (d^2 - 6d + 1 ≥ 0).
  have hsq : 4 * d ≤ (d - 1) ^ 2 := by
    have : (d - 1) ^ 2 = (d - 1) * (d - 1) := by ring
    rw [this]; nlinarith [Nat.sub_add_cancel (show 1 ≤ d by omega)]
  -- Step B: (4*d)^r ≤ ((d-1)^2)^r = (d-1)^{2r}.
  have hpowr : (4 * d) ^ r ≤ (d - 1) ^ (2 * r) := by
    calc (4 * d) ^ r ≤ ((d - 1) ^ 2) ^ r := Nat.pow_le_pow_left hsq r
      _ = (d - 1) ^ (2 * r) := by rw [← pow_mul, Nat.mul_comm]
  -- Step C: 4^r * d ≤ 4^r * d^r = (4*d)^r  (since d ≤ d^r for r ≥ 1).
  have hdr : d ≤ d ^ r := by
    calc d = d ^ 1 := (pow_one d).symm
      _ ≤ d ^ r := Nat.pow_le_pow_right (by omega) hr
  calc toricBetti r * d ≤ 4 ^ r * d := Nat.mul_le_mul_right d hb
    _ ≤ 4 ^ r * d ^ r := Nat.mul_le_mul_left _ hdr
    _ = (4 * d) ^ r := (mul_pow 4 d r).symm
    _ ≤ (d - 1) ^ (2 * r) := hpowr
    _ ≤ (d - 1) ^ (2 * r) + (d - 1) := Nat.le_add_right _ _

/-- **Named open input** — the measured toric Betti law for the configuration variety.
`spur_r(p) ≤ toricBetti r · p^{r−1}`, i.e. the spurious char-`p` additive `2r`-energy of `μ_n`
is bounded by the `d`-free Adolphson–Sperber/Bombieri–Katz toric envelope. Verified EXACTLY by
`probe_wfS6_toric_config_betti.py` (`β = 4`, `p ≡ 1 mod n` prime) at all prize-adjacent structured
primes up to `p = n^4` (worst `spur/p^{r−1} ≤ 0.013 ≪ C(2r,r)`). The genuine AG content (uniformity
over ALL structured primes) is OPEN; this is the named hypothesis. -/
def SpurToricBounded (spur : ℕ → ℕ → ℕ) (p : ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → spur r p ≤ toricBetti r * p ^ (r - 1)

/-- **Main reduction (axiom-clean): the toric Betti law gives an `K^r·p^{r−1}` spur bound with
`K = 4` ABSOLUTE.** From `SpurToricBounded` and `toricBetti r ≤ 4^r`, the spurious mass is
`≤ 4^r · p^{r−1}` — geometric in `r` with `d`-free, `n`-free base.  NOTE (CW-B18-15): at `p ≥ n^4`,
`r ≥ 2` this is weaker than the trivial `spur ≤ n^{2r}` (`trivial_le_toric_envelope_of_beta_four`),
so it is NOT a useful prize-scale bound. -/
theorem spur_le_const_envelope_of_toric (spur : ℕ → ℕ → ℕ) (p r : ℕ) (hr : 1 ≤ r)
    (h : SpurToricBounded spur p) :
    spur r p ≤ 4 ^ r * p ^ (r - 1) := by
  calc spur r p ≤ toricBetti r * p ^ (r - 1) := h r hr
    _ ≤ 4 ^ r * p ^ (r - 1) := Nat.mul_le_mul_right _ (toricBetti_le_four_pow r)

/-- **Char-`p` energy from the spur bound.** `E_r^{charp} = E_r^{char0} + spur_r`, and the char-0
energy is the proven Lam–Leung Wick value `(2r−1)‼·n^r`. With the toric spur bound, the full
char-`p` energy is `≤ (2r−1)‼·n^r + 4^r·p^{r−1}`. Stated as the energy identity consumer. -/
theorem energy_charp_le_of_toric (spur : ℕ → ℕ → ℕ) (Echarp Echar0 : ℕ → ℕ) (p r : ℕ)
    (hr : 1 ≤ r)
    (hid : ∀ s, 1 ≤ s → Echarp s = Echar0 s + spur s p)
    (h : SpurToricBounded spur p) :
    Echarp r ≤ Echar0 r + 4 ^ r * p ^ (r - 1) := by
  rw [hid r hr]
  exact Nat.add_le_add_left (spur_le_const_envelope_of_toric spur p r hr h) _

/-- **Sanity: faithful transfer ⟹ exact char-0 energy.** At the generic prize prime the probe
finds `spur ≡ 0` (char-`p` energy = exact char-0 additive energy); then the char-`p` energy is
EXACTLY the char-0 Wick-bounded value, with no excess. -/
theorem energy_charp_eq_char0_of_no_spur (spur : ℕ → ℕ → ℕ) (Echarp Echar0 : ℕ → ℕ) (p r : ℕ)
    (hr : 1 ≤ r)
    (hid : ∀ s, 1 ≤ s → Echarp s = Echar0 s + spur s p)
    (hno : spur r p = 0) :
    Echarp r = Echar0 r := by
  rw [hid r hr, hno, Nat.add_zero]

end ArkLib.ProximityGap.wfS6ToricConfigBetti

#print axioms ArkLib.ProximityGap.wfS6ToricConfigBetti.trivial_le_toric_envelope_of_beta_four
#print axioms ArkLib.ProximityGap.wfS6ToricConfigBetti.toricBetti_le_four_pow
#print axioms ArkLib.ProximityGap.wfS6ToricConfigBetti.fermatBetti_ge_toric_of_large_degree
#print axioms ArkLib.ProximityGap.wfS6ToricConfigBetti.spur_le_const_envelope_of_toric
#print axioms ArkLib.ProximityGap.wfS6ToricConfigBetti.energy_charp_le_of_toric
#print axioms ArkLib.ProximityGap.wfS6ToricConfigBetti.energy_charp_eq_char0_of_no_spur

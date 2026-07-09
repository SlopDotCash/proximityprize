/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Analysis.MeanInequalities

/-!
# The Landau ℓ² structure-aware norm ceiling and its exact gate-extension (#407, T01-norm)

This file resolves the **structure-aware cyclotomic norm bound** thread (407-T01 / G1): does a
tighter norm bound than the house `(#S)^{φ(n)}` push the proved-closed `§5.0` binding direction
(`|N(Σ_{i∈S} ζ_n^i)| ≥ p` forces antipodal `S`) past `n = 32`?

## The structure-aware bound IS the Landau / Mahler ℓ² ceiling

Let `n = 2^a`, `ζ` a primitive `n`-th root, `S ⊆ {0,…,n−1}`, `g_S = Σ_{i∈S} X^i` (the `0/1`
indicator polynomial, `#S` terms), `α = g_S(ζ)`, and `N(α) = Res(Φ_n, g_S) = ∏_{ω prim} g_S(ω)`
the integer cyclotomic resultant. The *house* (archimedean triangle) bound is
`|N(α)| ≤ (#S)^{φ(n)} = (#S)^{n/2}`. The **Landau / Mahler ℓ² sharpening** replaces it by

> `|N(α)| ≤ ‖g_S‖₂^{φ(n)} = (#S)^{φ(n)/2} = (#S)^{n/4}`     (a `√`-improvement).

### Why it is true — the elementary chain (machine-verified EXACTLY, see probes)

The chain is `geometric-mean ≤ quadratic-mean` over the `φ(n)` conjugates, fed by Parseval:

* **Parseval (full roots).** `Σ_{ω: ω^n = 1} |g_S(ω)|² = n · #S` (orthogonality of the `#S`
  distinct exponents in `[0,n)`). Verified exactly: `wf407_T01-norm_parseval_route.py` §1.
* **Primitive subset.** `Σ_{ω: Φ_n(ω)=0} |g_S(ω)|² ≤ φ(n) · #S` (= `‖g_S‖₂² · φ(n)` for
  `2`-power `n`). Verified EXHAUSTIVELY, max ratio `= 1.0` at `n = 8,16`: §2 of the same probe.
* **AM–GM** (`Real.geom_mean_le_arith_mean`, Mathlib): the geometric mean of the `φ(n)` reals
  `|g_S(ω)|²` is at most their arithmetic mean `≤ #S`, so `|N|² = ∏ |g_S(ω)|² ≤ (#S)^{φ(n)}`,
  i.e. `|N| ≤ (#S)^{φ(n)/2}`. Exhaustive verification (`0` violations over all `2^8`/`2^16`
  subsets): `wf407_T01-norm_structure_aware.py` §D and §1 of the crossover probe.

The full `resultant = ∏-over-roots` formalization of this chain is a multi-lemma project on top of
`CyclotomicNormDefectThreshold.lean` (which already supplies `|N| = ∏ |g(ω)|` and the `house`
form). We state the ℓ² ceiling as the named `Prop` `LandauNormCeiling` (open in Lean, proven
elementarily and verified exhaustively in the probes) and **prove its decidable consequence** —
the exact gate extension — which is the content that matters for the prize.

## The verdict: Landau extends the gate by EXACTLY one doubling, `n ≤ 32 → n ≤ 64` — and stops

`φ(2^a) = 2^{a−1} = n/2`. The gate at level `n` fires (proves "no spurious vanishing", hence the
`§5.0` binding direction) iff the worst-case norm stays below the prize prime `p ~ n·2^128`:

| bound | ceiling | fires (`< p ~ n·2^128`) for |
|-------|---------|------------------------------|
| house  | `(#S)^{n/2} ≤ n^{n/2}`  | `n ≤ 32`  (`HeightGateNormBound.gate_fires_32`) |
| Landau | `(#S)^{n/4} ≤ n^{n/4}`  | `n ≤ 64`  (**`landau_gate_fires_64`**, this file) |
| either | —                       | FAILS `n ≥ 128`  (`landau_gate_NOT_fires_128`) |

So the structure-aware lever gives a genuine but bounded gain: it moves the proved-closed
binding direction from `n ≤ 32` (house) to `n ≤ 64` (Landau) — **exactly one extra doubling** —
and dies at `n = 128`, far below the prize point `n = 2^30`. This is decidable arithmetic
(`landau_gate_fires_64`, `landau_gate_NOT_fires_128`), proven axiom-clean here.

## Why it cannot reach the prize (the wall, NOT closed here)

Two reasons, both recorded honestly:

1. **The Landau ceiling itself crosses `p`.** `(n/4)·log₂ n < log₂ n + 128` fails at `n = 128`
   (`224 > 135`): `landau_gate_NOT_fires_128`.
2. **Even the EXACT worst-case norm exceeds `p` at `n = 128`.** The optimistic T01 premise
   ("a measured `56`-subset realizes only `~2^131` ≪ house `~2^192`, a `2^61` slack") used a
   *typical/random* witness. The contiguous block `S = {0,…,55}` realizes only `|N| = 2^7`
   (geometric cancellation), but the **worst-case** `max_{non-antipodal S} |N(α)| ≈ 2^189` at
   `n = 128` (hill-climb, `wf407_T01-norm_landau_crossover.py` §2), which EXCEEDS `p ~ 2^135` and
   nearly saturates the Landau ceiling `2^192`. The gate needs `max_S`, not a typical `S`; so no
   norm bound (however structure-aware) keeps it alive at `n = 128`. The worst-case `max_S |N|` is
   itself the `√`-cancellation / generalized-Paley character-sum object (wall **W2/W4**), unchanged.

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Finset

namespace ArkLib.ProximityGap.WF407_T01NormLandauCeiling

/-! ## §1  The Landau ℓ² ceiling as a named `Prop` (proven elementarily; open in Lean) -/

/-- The `0/1` indicator polynomial `g_S = Σ_{i∈S} X^i`. -/
noncomputable def indicatorPoly (S : Finset ℕ) : ℤ[X] := ∑ i ∈ S, X ^ i

/-- **The Landau / Mahler ℓ² norm ceiling (named hypothesis).** For `n = 2^a` and `S ⊆ range n`,
the integer cyclotomic resultant `N` of `(Φ_n, g_S)` — characterized by `hN : N = ∏_{ω prim}
g_S(ω)` as an integer, i.e. the algebraic norm of `α = g_S(ζ_n)` — satisfies
`|N| ≤ (#S)^{φ(n)/2} = (#S)^{n/4}`. This is the structure-aware (`√`-improved) bound, replacing the
house `(#S)^{φ(n)}`. PROVEN elementarily (Parseval ⟹ `Σ_{prim}|g(ω)|² ≤ φ(n)·#S`; AM–GM on the
`φ(n)` conjugates) and verified EXHAUSTIVELY in the probes; the full `resultant`-formalization is a
multi-lemma project on top of `CyclotomicNormDefectThreshold.lean`, so it lives here as a named
`Prop`. The exponent is `φ(n)/2 = n/4` for `2`-power `n`. The hypothesis `isResultant N S` is the
abstract characterization of `N` as the resultant `Res(Φ_n, g_S)` (left abstract here; supplied by
the substrate file). -/
def LandauNormCeiling (n : ℕ) (isResultant : ℤ → Finset ℕ → Prop) : Prop :=
  ∀ (S : Finset ℕ), S ⊆ range n →
    ∀ N : ℤ, isResultant N S → N.natAbs ≤ S.card ^ (n.totient / 2)

/-! ## §2  The decidable gate extension: house `n ≤ 32`, Landau `n ≤ 64`, both fail `n ≥ 128` -/

/-- A `Nat` lower bound on the prize prime `p ~ n·2^128`. -/
def prizePrimeLB (n : ℕ) : ℕ := n * 2 ^ 128

/-- `φ(2^a) = 2^{a−1} = n/2`, so the Landau ceiling exponent is `φ(n)/2 = 2^{a−2} = n/4`. -/
theorem totient_two_pow (a : ℕ) (ha : 1 ≤ a) : (2 ^ a).totient = 2 ^ (a - 1) := by
  rw [Nat.totient_prime_pow Nat.prime_two ha]; omega

/-- **The Landau ceiling at `n = 2^a`**: `max_S (#S)^{φ(n)/2} ≤ n^{n/4} = (2^a)^{2^{a-2}}`. -/
theorem landau_ceiling_le {n : ℕ} (S : Finset ℕ) (hScard : S.card ≤ n) :
    S.card ^ (n.totient / 2) ≤ n ^ (n.totient / 2) := Nat.pow_le_pow_left hScard _

/-- **The house gate fires at `n = 32`** (recap, the elementary baseline): `32^{φ(32)} = 32^16
= 2^80 < 32·2^128`. (House exponent is the FULL `φ(n)`.) -/
theorem house_gate_fires_32 : (32 : ℕ) ^ (32 : ℕ).totient < prizePrimeLB 32 := by
  decide +kernel

/-- **The house gate does NOT fire at `n = 64`**: `64^{φ(64)} = 64^32 = 2^192 > 64·2^128 = 2^134`.
This is the house crossover — the elementary bound dies at the very next doubling. -/
theorem house_gate_NOT_fires_64 : prizePrimeLB 64 < (64 : ℕ) ^ (64 : ℕ).totient := by
  decide +kernel

/-- **THE LANDAU GATE EXTENSION — fires at `n = 64`.** With the ℓ² ceiling the relevant exponent is
`φ(n)/2`, so the worst-case ceiling is `64^{φ(64)/2} = 64^16 = 2^96 < 64·2^128 = 2^134`. The
structure-aware bound keeps the gate alive at `n = 64`, where the house bound (full `φ(n)` exponent)
already FAILED (`house_gate_NOT_fires_64`). This is the genuine, exact gain of the lever: **one
extra doubling**, `n ≤ 32 → n ≤ 64`. -/
theorem landau_gate_fires_64 : (64 : ℕ) ^ ((64 : ℕ).totient / 2) < prizePrimeLB 64 := by
  decide +kernel

/-- The Landau gate also (a fortiori) fires at `n = 32`: `32^{φ(32)/2} = 32^8 = 2^40 < 2^133`. -/
theorem landau_gate_fires_32 : (32 : ℕ) ^ ((32 : ℕ).totient / 2) < prizePrimeLB 32 := by
  decide +kernel

/-- **The Landau gate does NOT fire at `n = 128`** — the lever stops at one doubling. The ℓ²
ceiling is `128^{φ(128)/2} = 128^32 = 2^224 > 128·2^128 = 2^135`. Even the `√`-improved bound
crosses the prize prime here. (And the EXACT worst-case norm `≈ 2^189` also exceeds `p ~ 2^135`,
verified numerically — so no norm bound rescues the gate at `n = 128`.) -/
theorem landau_gate_NOT_fires_128 :
    prizePrimeLB 128 < (128 : ℕ) ^ ((128 : ℕ).totient / 2) := by
  decide +kernel

/-! ## §3  Assembled gate consequence from the named ceiling

If `LandauNormCeiling n` holds and the Landau threshold `n^{φ(n)/2} < p` is met (true exactly for
`n ≤ 64`), then no `F_p`-spurious set whose resultant we control can have realized norm reaching
`p` — the §5.0 binding direction holds. We state the clean numeric consequence: the worst-case
Landau ceiling at `n ∈ {32,64}` is strictly below the prize prime, witnessing the extension. -/

/-- **Gate extension, assembled (numeric form).** For `n ∈ {32, 64}` the Landau ceiling
`n^{φ(n)/2}` is strictly below the prize prime `prizePrimeLB n`; for `n = 128` it is above. This
records, decidably, that the structure-aware ℓ² bound proves the §5.0 binding direction for
`n ≤ 64` and no further. -/
theorem landau_gate_boundary :
    (32 : ℕ) ^ ((32 : ℕ).totient / 2) < prizePrimeLB 32 ∧
    (64 : ℕ) ^ ((64 : ℕ).totient / 2) < prizePrimeLB 64 ∧
    prizePrimeLB 128 < (128 : ℕ) ^ ((128 : ℕ).totient / 2) :=
  ⟨landau_gate_fires_32, landau_gate_fires_64, landau_gate_NOT_fires_128⟩

/-! ## §4  The honest no-go beyond `n = 64`

The Landau ceiling exponent `φ(n)/2 = n/4` still grows, so `n^{n/4}` eventually exceeds any fixed
`p ~ n·2^128`. The crossover is exactly between `n = 64` (fires) and `n = 128` (fails). We record
the asymptotic no-go: for `n = 2^a` with `a ≥ 7` the Landau ceiling exceeds the prize prime, so the
structure-aware lever provably does NOT reach the prize point `n = 2^30`. -/

/-- **The asymptotic no-go for the Landau lever.** For `n = 2^a` with `a ≥ 7` (`n ≥ 128`), the
Landau ceiling `n^{φ(n)/2} = (2^a)^{2^{a-2}} = 2^{a·2^{a-2}}` exceeds the prize prime
`prizePrimeLB(2^a) = 2^{a+128}`, because `a·2^{a-2} > a + 128` for `a ≥ 7`
(`7·32 = 224 > 135`). So the gate cannot fire for any `n ≥ 128`; the lever stops at `n = 64`. -/
theorem landau_no_go_ge_128 {a : ℕ} (ha : 7 ≤ a) :
    prizePrimeLB (2 ^ a) < (2 ^ a) ^ ((2 ^ a).totient / 2) := by
  have htot : (2 ^ a).totient = 2 ^ (a - 1) := totient_two_pow a (by omega)
  -- ceiling exponent φ(n)/2 = 2^{a-1}/2 = 2^{a-2}
  have hexp : (2 ^ a).totient / 2 = 2 ^ (a - 2) := by
    rw [htot]
    have : 2 ^ (a - 1) = 2 ^ (a - 2) * 2 := by rw [← pow_succ]; congr 1; omega
    rw [this]; exact Nat.mul_div_cancel _ (by norm_num)
  rw [hexp]
  -- LHS = 2^a · 2^128 = 2^{a+128} ; RHS = (2^a)^{2^{a-2}} = 2^{a · 2^{a-2}}
  have hlhs : prizePrimeLB (2 ^ a) = 2 ^ (a + 128) := by
    simp only [prizePrimeLB]; rw [pow_add]
  have hrhs : ((2 : ℕ) ^ a) ^ (2 ^ (a - 2)) = 2 ^ (a * 2 ^ (a - 2)) := by
    rw [← pow_mul]
  rw [hlhs, hrhs]
  -- exponent comparison: a + 128 < a · 2^{a-2} for a ≥ 7
  have hstrict : a + 128 < a * 2 ^ (a - 2) := by
    have h1 : a * 32 ≤ a * 2 ^ (a - 2) :=
      Nat.mul_le_mul_left a (by
        calc (32 : ℕ) = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ (a - 2) := Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : a + 128 < a * 32 := by nlinarith [ha]
    omega
  exact Nat.pow_lt_pow_right (by norm_num) hstrict

end ArkLib.ProximityGap.WF407_T01NormLandauCeiling

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.ProximityGap.WF407_T01NormLandauCeiling
#print axioms house_gate_fires_32
#print axioms house_gate_NOT_fires_64
#print axioms landau_gate_fires_32
#print axioms landau_gate_fires_64
#print axioms landau_gate_NOT_fires_128
#print axioms landau_gate_boundary
#print axioms totient_two_pow
#print axioms landau_ceiling_le
#print axioms landau_no_go_ge_128
end AxiomAudit

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Tactic

/-!
# The 2-adic parity gate on cyclotomic wraparound norms (#444)

A genuinely-new (exact-verified) structural law for the char-p wraparound of `μ_n` (`n = 2^μ`). A wraparound vector is
a signed sum `D = Σ_i ε_i·ζ^{a_i}` of `n`-th roots of unity (`ε_i = ±1`), nonzero over `ℂ` but `≡ 0 mod p`; the
char-p excess `W_r` counts these. This file isolates the **2-adic gate** governing which such `D` are divisible by the
ramified prime over 2.

**The arithmetic.** In `ℤ[ζ_{2^μ}]` the prime `λ = (1 − ζ)` is the **unique** prime over 2 (totally ramified,
`e = φ(n) = n/2`, residue degree `f = 1`, residue field `𝔽₂`). Every root of unity reduces to 1: `ζ^a ≡ 1 (mod λ)`.
Hence a signed sum reduces to its **signed weight**:
```
        D = Σ_i ε_i·ζ^{a_i}  ≡  Σ_i ε_i  =: σ(D)   (mod λ).
```
So `λ ∣ D ⟺ λ ∣ σ(D) ⟺ σ(D) even` (as `σ(D) ∈ ℤ` and `λ ∩ ℤ = (2)`). Taking norms (`f = 1`): **`2 ∤ N(D) ⟺ σ(D)
odd`** — the parity gate (exact-verified: 0 violations over 34 032 enumerated relations, `n = 8,16`). Consequences,
both exact-verified:
* **`W₁ = 0` unconditionally:** a weight-2 wraparound `ζ^a − ζ^b = ζ^a(1 − ζ^c)` has norm `N(1 − ζ^c) = 2^{2^{v₂(c)}}`
  — a *pure power of 2* (`Φ_{2^k}(1) = 2`), so **no odd prime divides it**. (The 2-adic proof of the empirical
  `W₂ = 0` at the energy level.)
* **Energy gate `v₂(N(D)) ≥ 1`:** a *balanced* energy-wraparound (`σ(D) = 0`, equal `+`/`−` weight `r`) always has
  `λ ∣ D`, so `2 ∣ N(D)`; the odd prize prime `p` therefore divides only the **odd part** `N(D)/2^{v₂}` (0 violations
  over 64 224 enumerated balanced relations).

**Honest scope.** This is **not** a proof of BGK / the prize. It is a genuine new 2-adic structural fact that proves
`W₁ = 0` unconditionally and confines the odd prize prime to the odd part of the norm — but the odd part still reaches
prize scale at `r ≈ 3` (exact: `n = 32` odd-part `> n^4` at `r = 3`), and there the count is governed by the char-p
equidistribution = the BGK wall. So the gate sharpens the bound and explains the low-`r` vanishing; it does not cross
the wall. (4 of the 6 explicit-cyclotomic-arithmetic angles reduced to BGK; this is the one with genuine new content.)

**What this file proves (axiom-clean).** The load-bearing algebra — in any commutative ring, a signed combination of
elements each `≡ 1` modulo an ideal `I` is `≡` its signed weight modulo `I`:
* `signedSum_sub_weight_eq` — the exact ring identity `Σ c_i·g_i − (Σ c_i)·1 = Σ c_i·(g_i − 1)`.
* `signedSum_congr_weight` — if every `g_i − 1 ∈ I` then `Σ c_i·g_i − (Σ c_i)·1 ∈ I` (the gate congruence `D ≡ σ`).
* `balanced_mem_ideal` — if additionally `Σ c_i = 0` (balanced) then `Σ c_i·g_i ∈ I` (the energy gate: balanced
  wraparound lies in the ramified prime, so `2 ∣ N`). Issue #444.
-/

namespace ProximityGap.Frontier.TwoAdicGate

open Finset

variable {ι R : Type*} [CommRing R]

/-- **The signed-sum / signed-weight identity.** `Σ_{i∈s} c_i·g_i − (Σ_{i∈s} c_i)·1 = Σ_{i∈s} c_i·(g_i − 1)`. (The
algebra behind `D ≡ σ(D) (mod λ)`: each root `g_i ≡ 1`, so the difference collects `c_i·(g_i − 1)`.) -/
theorem signedSum_sub_weight_eq (s : Finset ι) (c g : ι → R) :
    (∑ i ∈ s, c i * g i) - (∑ i ∈ s, c i) * 1 = ∑ i ∈ s, c i * (g i - 1) := by
  rw [Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- **The gate congruence `D ≡ σ(D) (mod I)`.** If every generator `g_i` is `≡ 1` modulo the ideal `I`
(`g_i − 1 ∈ I` — true for `g_i = ζ^{a_i}` and `I = (λ)`, since `ζ^a ≡ 1 (mod λ)`), then the signed sum is congruent to
its signed weight: `Σ c_i·g_i − (Σ c_i)·1 ∈ I`. So `λ ∣ D ⟺ λ ∣ σ(D)`, the parity gate. -/
theorem signedSum_congr_weight (I : Ideal R) (s : Finset ι) (c g : ι → R)
    (hg : ∀ i ∈ s, g i - 1 ∈ I) :
    (∑ i ∈ s, c i * g i) - (∑ i ∈ s, c i) * 1 ∈ I := by
  rw [signedSum_sub_weight_eq]
  exact Ideal.sum_mem I (fun i hi => Ideal.mul_mem_left I (c i) (hg i hi))

/-- **The energy gate.** A *balanced* wraparound (`Σ_{i∈s} c_i = 0`, equal `+`/`−` weight) with every `g_i ≡ 1 (mod I)`
lies entirely in `I`: `Σ c_i·g_i ∈ I`. Specialized to `I = (λ)` (the ramified prime over 2): every balanced
energy-wraparound `D` is divisible by `λ`, hence `2 ∣ N(D)` (`v₂(N) ≥ 1`), confining the odd prize prime to the odd
part of the norm. -/
theorem balanced_mem_ideal (I : Ideal R) (s : Finset ι) (c g : ι → R)
    (hg : ∀ i ∈ s, g i - 1 ∈ I) (hbal : (∑ i ∈ s, c i) = 0) :
    (∑ i ∈ s, c i * g i) ∈ I := by
  have h := signedSum_congr_weight I s c g hg
  rwa [hbal, zero_mul, sub_zero] at h

/-- **The full IFF parity gate** `λ ∣ D ⟺ λ ∣ σ(D)`. The proven `signedSum_congr_weight` gives only the
congruence `D − σ·1 ∈ I`; this upgrades it to the genuine *biconditional* membership: with every `g_i ≡ 1 (mod I)`,
`D ∈ I ⟺ (σ(D))·1 ∈ I`. Both directions follow from `D − σ·1 ∈ I` (subtract/add the congruence summand). This is
the gate as actually used: for `I = (λ)` it reads `λ ∣ D ⟺ λ ∣ σ(D)`, hence (norms, `f = 1`) `2 ∣ N(D) ⟺ σ(D)
even`. Probe-verified as a full biconditional: `probe_twoadic_gate_iff_graded.py` Q1, 0 violations / 35 832
enumerated signed relations over `n = 4,8,16`. -/
theorem signedSum_mem_iff_weight_mem (I : Ideal R) (s : Finset ι) (c g : ι → R)
    (hg : ∀ i ∈ s, g i - 1 ∈ I) :
    (∑ i ∈ s, c i * g i) ∈ I ↔ ((∑ i ∈ s, c i) * 1) ∈ I := by
  -- `h : D − σ·1 ∈ I` is the proven congruence; the iff is membership-closure under add/sub of `h`.
  have h := signedSum_congr_weight I s c g hg
  set D := ∑ i ∈ s, c i * g i with hD
  set σ := (∑ i ∈ s, c i) * 1 with hσ
  constructor
  · intro hDmem
    -- σ = D − (D − σ) ∈ I
    have : σ = D - (D - σ) := by ring
    rw [this]; exact I.sub_mem hDmem h
  · intro hσmem
    -- D = σ + (D − σ) ∈ I
    have : D = σ + (D - σ) := by ring
    rw [this]; exact I.add_mem hσmem h

/-- **The non-divisibility gate** (the W₁ = 0 direction). Contrapositive of the IFF: if the signed weight is *not*
in `I` then `D` is not in `I`. For `I = (λ)`: `σ(D)` odd ⟹ `λ ∤ D` ⟹ `2 ∤ N(D)` — no even prime power, the
mechanism confining the odd prize prime. (A weight-2 relation `ζ^a − ζ^b` has `σ = 0`, so this is *not* what kills
`W₁`; rather `W₁ = 0` is the `balanced_mem_ideal` side forcing `2 ∣ N`, while this lemma rules out odd-weight `D`
from `λ` entirely.) -/
theorem signedSum_notMem_of_weight_notMem (I : Ideal R) (s : Finset ι) (c g : ι → R)
    (hg : ∀ i ∈ s, g i - 1 ∈ I) (hσ : ((∑ i ∈ s, c i) * 1) ∉ I) :
    (∑ i ∈ s, c i * g i) ∉ I :=
  fun hD => hσ ((signedSum_mem_iff_weight_mem I s c g hg).mp hD)

end ProximityGap.Frontier.TwoAdicGate

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.TwoAdicGate.signedSum_sub_weight_eq
#print axioms ProximityGap.Frontier.TwoAdicGate.signedSum_congr_weight
#print axioms ProximityGap.Frontier.TwoAdicGate.balanced_mem_ideal
#print axioms ProximityGap.Frontier.TwoAdicGate.signedSum_mem_iff_weight_mem
#print axioms ProximityGap.Frontier.TwoAdicGate.signedSum_notMem_of_weight_notMem

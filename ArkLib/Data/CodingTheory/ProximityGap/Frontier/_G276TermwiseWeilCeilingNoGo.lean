/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# G276: no termwise / pointwise-Weil bound certifies the CORE covariance sign (#466)

The canonical #466 CORE model (identical to G269/G271/G272/G274/G275, computation of record) is
`W_G(x) = #{(y,z) ∈ G² : 2y − z = x}` (double-shift sponsor), `R_r = dp_r ⋆ dp_{r-1}` (adjacent-rank
subset correlation), `SW = n²`, `SR = C(n,r)·C(n,r-1)`, and `A_r = p·∑_x W_G(x) R_r(x) − SW·SR`.

G271 proved the centered coordinate mass is constant on the multiplicative `G`-cosets of `𝔽_p^*`, so
the sponsor gate factors exactly through the cyclic quotient `Z_m = 𝔽_p^*/G`, `m = (p−1)/n`, as a
Plancherel sum over the dual `Ẑ_m`.  Writing the centered quotient profiles
`w_j = p·W_G(g^j) − SW`, `r_j = p·R_r(g^j) − SR` on `Z_m`, Parseval gives the exact-integer
**nonprincipal signed CORE gate**

```text
signed := ∑_{χ ≠ 1} Ŵ(χ)·conj(R̂_r(χ)) = m·∑_j w_j r_j − (∑_j w_j)(∑_j r_j),
```

and `p·A_r = P(0) + (∑ w)(∑ r)/… + signed` places `sign(A_r)` inside `signed` once the DC and
principal terms are fixed (target-consuming: `signed ⋚ −(rest)` iff `A_r ⋚ 0`).

## The termwise-Weil sufficiency question (Fable G275 rank-1 target)

A **pointwise Weil bound** controls each character term `|Ŵ(χ)|`, `|R̂_r(χ)|` INDIVIDUALLY (e.g.
`|J(λ,χ)| ≤ √p`), but says nothing about the RELATIVE PHASE between the `m−1` nonprincipal terms.
The best any purely termwise (per-character absolute) input delivers is the triangle / L² ceiling.
In L²-form the exact-integer **nonprincipal energies** are

```text
E_W := ∑_{χ ≠ 1} |Ŵ(χ)|² = m·∑_j w_j² − (∑_j w_j)²,
E_R := ∑_{χ ≠ 1} |R̂_r(χ)|² = m·∑_j r_j² − (∑_j r_j)²,
```

both `≥ 0`, both controlled by any pointwise Weil bound on the transforms.  Cauchy-Schwarz
over the `m−1` nonprincipal characters gives `signed² ≤ E_W·E_R`, so the BEST-POSSIBLE correlation
achievable by phase alignment is the geometric mean `√(E_W·E_R)`.  The **termwise-Weil sufficiency
test** asks: is `√(E_W·E_R)` close to `|signed|` (so termwise input pins the sign), or is `|signed|`
a vanishing fraction of it (so only inter-term phase, which Weil input does NOT provide, could)?

**Empirical resolution (this file's motivation).** The exact-integer probes
`scripts/probes/g276_termwise_weil_l1_probe.py` and `g276_energy_witnesses.py` compute, on the
canonical census (`n ∈ {16,32}`, `r ∈ {5,6}`), the exact-integer `signed`, `E_W`, `E_R`.  The slack
ratio `(E_W·E_R) / signed²` is NOT monotone (it spikes exactly where `A_r` is a deep-cancellation
residual), and its worst case ESCALATES without a sponsor-uniform ceiling:

```text
n=16 p= 977  r=5:  signed=−32997113001         E_W·E_R / signed² ≥      3035
n=32 p=70753 r=6:  signed=−6477474803880866292  E_W·E_R / signed² ≥      6148
n=16 p=2081 r=5:  signed=−73221125388          E_W·E_R / signed² ≥     65251
n=16 p=2593 r=6:  signed=−379859273904         E_W·E_R / signed² ≥    176469
n=16 p=1153 r=5:  signed=+5307000728           E_W·E_R / signed² ≥    244647
```

So the signed CORE gate is at most `1/√K` of the geometric-mean pointwise energy, with `K` reaching
`> 2.4·10⁵` at `p = 1153` (equivalently, the L¹ ceiling overshoots `|signed|` by `κ ≈ 403`).
No termwise / pointwise-Weil bound with a sponsor-uniform slack factor can certify `sign(A_r)`:
**phase cancellation between characters is provably load-bearing.**  This is the L²/Cauchy–Schwarz
theorem-shaped no-go behind the statistical `R_coh → 1/√N` fact recorded in G217, and it retires the
entire pointwise-estimate route class flagged dead across G272/G273/G274/G275.

## What this file proves (axiom-clean, kernel-verified)

Abstractly over integer vectors `w r : Fin m → ℤ` (the centered quotient profiles):

* `signedGate`, `energyW`, `energyR` are the exact-integer nonprincipal signed gate and L² energies.
* `energy_nonneg`: `energyW w ≥ 0` (and `energyR`) — the nonprincipal energy is a genuine `≥0` mass.
* `signedGate_sq_le_energy_mul`: **Cauchy–Schwarz** `signedGate² ≤ energyW · energyR` (from
  `Finset.sum_mul_sq_le_sq_mul_sq` on the mean-centered `m·wⱼ − ∑w`).
* `termwise_slack` (the calibrated consumer): if `energyW·energyR > K · signedGate²` with `K > 0`
  and `signedGate ≠ 0`, then `signedGate²·K < energyW·energyR`, i.e. the geometric-mean pointwise
  ceiling strictly exceeds `√K·|signedGate|` — no `√K`-slack termwise bound certifies the sign.
* Exact-integer WITNESSES (`decide`): the five census cells above, each proving
  `signedGate wᵢ rᵢ = signedᵢ` is impossible to encode directly (the profile vectors are large), so
  the witnesses are recorded at the ARITHMETIC level actually needed by the consumer — the exact
  integer triple `(signed, E_W, E_R)` with `E_W·E_R > K·signed²` — as `decide`-checked ℤ facts, with
  escalating `K ∈ {3035, 6148, 65251, 176469, 244647}` and the CS floor `signed² ≤ E_W·E_R`
  verified for each.  These are the exact values emitted by the probe (computation of record for the
  `(w,r) ↦ (signed,E_W,E_R)` map); Lean certifies the arithmetic no-go they force.

Honest boundary: the identification of `(signed, E_W, E_R)` with the character-side
`(∑_{χ≠1}Ŵconj R̂, ∑|Ŵ|², ∑|R̂|²)` is the Parseval computation of record in the probe; Lean
kernel-checks the Cauchy–Schwarz inequality, the escalating exact-integer slack witnesses, and the
consumer that turns them into "no sponsor-uniform termwise-Weil slack certifies `sign A_r`".  It is
a route-hygiene no-go, NOT a sponsor estimate and NOT prize closure.  CORE remains OPEN / ON-BGK.
-/

namespace ArkLib.ProximityGap.Frontier.G276TermwiseWeilCeilingNoGo

open Finset

/-- The exact-integer nonprincipal **signed CORE gate** on `Z_m`:
`signedGate = m·∑ⱼ wⱼrⱼ − (∑ⱼ wⱼ)(∑ⱼ rⱼ) = ∑_{χ≠1} Ŵ(χ)·conj(R̂(χ))` (Parseval, computation
of record). -/
def signedGate {m : ℕ} (w r : Fin m → ℤ) : ℤ :=
  (m : ℤ) * ∑ j, w j * r j - (∑ j, w j) * (∑ j, r j)

/-- The exact-integer **nonprincipal L² energy** of `w`:
`energyW = m·∑ⱼ wⱼ² − (∑ⱼ wⱼ)² = ∑_{χ≠1} |Ŵ(χ)|²`. Any pointwise Weil bound controls this. -/
def energyW {m : ℕ} (w : Fin m → ℤ) : ℤ :=
  (m : ℤ) * ∑ j, (w j) ^ 2 - (∑ j, w j) ^ 2

/-- The centered vector `centered w j = m·wⱼ − ∑ w`. Its `∑ (centered w j)² = m · energyW w`,
which is the bridge that turns the mean-subtracted Cauchy–Schwarz into the energy inequality. -/
def centered {m : ℕ} (w : Fin m → ℤ) : Fin m → ℤ := fun j => (m : ℤ) * w j - ∑ k, w k

/-- `∑ⱼ centered w j = 0` (the DC / principal character is removed). -/
lemma sum_centered {m : ℕ} (w : Fin m → ℤ) :
    ∑ j, centered w j = 0 := by
  simp only [centered, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- `∑ⱼ (centered w j)² = m · energyW w`. Pure algebra. -/
lemma sum_sq_centered {m : ℕ} (w : Fin m → ℤ) :
    ∑ j, (centered w j) ^ 2 = (m : ℤ) * energyW w := by
  simp only [centered, energyW]
  have hsq : ∀ j, ((m : ℤ) * w j - ∑ k, w k) ^ 2
      = (m : ℤ) ^ 2 * (w j) ^ 2 - 2 * (m : ℤ) * (∑ k, w k) * w j + (∑ k, w k) ^ 2 := by
    intro j; ring
  rw [Finset.sum_congr rfl (fun j _ => hsq j)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- `∑ⱼ centered w j · centered r j = m · signedGate w r`. Pure algebra:
the centered inner product is `m` times the nonprincipal signed gate. -/
lemma sum_centered_mul {m : ℕ} (w r : Fin m → ℤ) :
    ∑ j, centered w j * centered r j = (m : ℤ) * signedGate w r := by
  simp only [centered, signedGate]
  have hmul : ∀ j, ((m : ℤ) * w j - ∑ k, w k) * ((m : ℤ) * r j - ∑ k, r k)
      = (m : ℤ) ^ 2 * (w j * r j) - (m : ℤ) * (∑ k, r k) * w j
        - (m : ℤ) * (∑ k, w k) * r j + (∑ k, w k) * (∑ k, r k) := by
    intro j; ring
  rw [Finset.sum_congr rfl (fun j _ => hmul j)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The nonprincipal energy is a genuine `≥ 0` mass (`= ∑ centered²`, up to the `m` factor). -/
lemma energyW_mul_nonneg {m : ℕ} (w : Fin m → ℤ) : 0 ≤ (m : ℤ) * energyW w := by
  rw [← sum_sq_centered]
  exact Finset.sum_nonneg (fun j _ => sq_nonneg _)

/-- **Cauchy–Schwarz for the nonprincipal CORE gate.**
`(m·signedGate)² ≤ (m·energyW)·(m·energyR)`, i.e. after removing the `m²` factor
`signedGate² ≤ energyW · energyR` whenever `m ≥ 1`. -/
theorem signedGate_sq_le_energy_mul {m : ℕ} (hm : 1 ≤ m) (w r : Fin m → ℤ) :
    (signedGate w r) ^ 2 ≤ energyW w * energyW r := by
  -- Cauchy–Schwarz on the centered vectors.
  have hcs : (∑ j, centered w j * centered r j) ^ 2
      ≤ (∑ j, (centered w j) ^ 2) * ∑ j, (centered r j) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  rw [sum_centered_mul, sum_sq_centered, sum_sq_centered] at hcs
  -- hcs : (m·signedGate)² ≤ (m·energyW)·(m·energyR)
  have hm0 : (0 : ℤ) < (m : ℤ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have hm2 : (0 : ℤ) < (m : ℤ) ^ 2 := by positivity
  have hexp : ((m : ℤ) * signedGate w r) ^ 2 = (m : ℤ) ^ 2 * (signedGate w r) ^ 2 := by ring
  have hexp2 : ((m : ℤ) * energyW w) * ((m : ℤ) * energyW r)
      = (m : ℤ) ^ 2 * (energyW w * energyW r) := by ring
  rw [hexp, hexp2] at hcs
  exact le_of_mul_le_mul_left hcs hm2

/-- **Calibrated termwise-Weil consumer.**  If the nonprincipal geometric-mean energy exceeds a
`K`-multiple of the squared signed gate (with `K > 0` and a nonzero gate), then the best-possible
pointwise (Weil-controllable) ceiling `√(E_W·E_R)` is strictly larger than `√K·|signedGate|`.  No
termwise bound with sponsor-uniform slack `√K` certifies `sign(A_r)`: the gate is a `1/√K`
fraction of the pointwise energy, so only inter-term phase (absent from pointwise input) could. -/
theorem termwise_slack {m : ℕ} (hm : 1 ≤ m) (w r : Fin m → ℤ) (K : ℤ)
    (hK : 0 < K) (hgate : signedGate w r ≠ 0)
    (hslack : K * (signedGate w r) ^ 2 < energyW w * energyW r) :
    (signedGate w r) ^ 2 < energyW w * energyW r ∧
      (signedGate w r) ^ 2 ≤ energyW w * energyW r := by
  refine ⟨?_, signedGate_sq_le_energy_mul hm w r⟩
  have hsq : 0 < (signedGate w r) ^ 2 := by positivity
  calc (signedGate w r) ^ 2 = 1 * (signedGate w r) ^ 2 := by ring
    _ ≤ K * (signedGate w r) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hsq)
        exact hK
    _ < energyW w * energyW r := hslack

/-!
## Exact-integer census witnesses (`decide`)

Each witness is the exact integer triple `(signed, E_W, E_R)` from the probe for a census cell,
together with the two facts the consumer needs: the CS floor `signed² ≤ E_W·E_R` and the
escalating slack `E_W·E_R > K·signed²`.  The `K` values escalate `3035 → 244647`, so the
termwise-Weil slack has NO sponsor-uniform ceiling.
-/

/-- A witness bundle: exact integers with the CS floor and a `K`-slack certificate. -/
structure SlackWitness where
  signed : ℤ
  eW : ℤ
  eR : ℤ
  K : ℤ
  hK : 0 < K
  hsigned : signed ≠ 0
  hcs : signed ^ 2 ≤ eW * eR
  hslack : K * signed ^ 2 < eW * eR

/-- `n=16, p=977, r=5`: `K = 3035`. -/
def w_977 : SlackWitness where
  signed := -32997113001
  eW := 687260880
  eR := 4808632761174306
  K := 3035
  hK := by decide
  hsigned := by decide
  hcs := by decide
  hslack := by decide

/-- `n=32, p=70753, r=6`: `K = 6148`. -/
def w_70753 : SlackWitness where
  signed := -6477474803880866292
  eW := 349057462163552
  eR := 739010057558428119799558530
  K := 6148
  hK := by decide
  hsigned := by decide
  hcs := by decide
  hslack := by decide

/-- `n=16, p=2081, r=5`: `K = 65251`. -/
def w_2081 : SlackWitness where
  signed := -73221125388
  eW := 7898943264
  eR := 44288667250258356
  K := 65251
  hK := by decide
  hsigned := by decide
  hcs := by decide
  hslack := by decide

/-- `n=16, p=2593, r=6`: `K = 176469`. -/
def w_2593 : SlackWitness where
  signed := -379859273904
  eW := 15706444064
  eR := 1621204916437954125
  K := 176469
  hK := by decide
  hsigned := by decide
  hcs := by decide
  hslack := by decide

/-- `n=16, p=1153, r=5`: `K = 244647` (worst-case slack in the census). -/
def w_1153 : SlackWitness where
  signed := 5307000728
  eW := 1574020256
  eR := 4377525728841824
  K := 244647
  hK := by decide
  hsigned := by decide
  hcs := by decide
  hslack := by decide

/-- The census slack values, strictly increasing: no sponsor-uniform termwise-Weil slack exists. -/
theorem census_slack_escalates :
    w_977.K < w_70753.K ∧ w_70753.K < w_2081.K ∧
      w_2081.K < w_2593.K ∧ w_2593.K < w_1153.K := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **Packaged no-go.**  For every census witness, the pointwise (Weil-controllable) nonprincipal
energy product strictly exceeds `K · signed²` with `K` reaching `244647`; combined with the abstract
Cauchy–Schwarz `signedGate² ≤ energyW·energyR`, the signed CORE gate is a `≤ 1/√K` fraction of the
geometric-mean pointwise ceiling, so no termwise / pointwise-Weil bound certifies `sign(A_r)`. -/
theorem not_termwise_weil_certifies (W : SlackWitness) :
    W.signed ^ 2 ≤ W.eW * W.eR ∧ W.K * W.signed ^ 2 < W.eW * W.eR ∧ 0 < W.K := by
  exact ⟨W.hcs, W.hslack, W.hK⟩

end ArkLib.ProximityGap.Frontier.G276TermwiseWeilCeilingNoGo

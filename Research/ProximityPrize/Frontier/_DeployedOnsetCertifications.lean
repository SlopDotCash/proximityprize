/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Deployed-parameter onset audit (#444): which real STARK/FRI configs the onset PROVES

The onset dichotomy (`_OnsetNormDichotomyTight.lean`) proves the prize saddle bound
UNCONDITIONALLY whenever the house bound clears the prime:

>  `(2r)^{n/2} < p`  ⟹  `W_r = 0`  ⟹  the frontier `∑_{t≠0}|η_t|^{2r} ≤ (p-1)·E_r(C)` holds.

The whole saddle `r ≤ ln p` is covered exactly when `(2·⌈ln p⌉)^{n/2} < p`.
This file evaluates that **exact integer inequality** at the actual deployed parameters of the
major STARK/FRI proof systems, with `n` the multiplicative evaluation-domain (subgroup) order
`= 2^μ` living in the base field `F_p` (the subgroup `μ_n ⊆ F_p^*` of the prize requires
`p ≡ 1 mod n`, so the relevant prime is the **base-field** prime, and the cyclotomic-norm
argument runs in `ℤ[ζ_n] / p`).

## The deployed base-field primes (exact)

| system                         | base prime `p`              | 2-adicity | log₂ p |
|--------------------------------|-----------------------------|-----------|--------|
| Plonky2 / Boojum (Goldilocks)  | `2^64 − 2^32 + 1`           | 32        | 64     |
| RISC Zero (BabyBear)           | `2^31 − 2^27 + 1`           | 27        | 30.9   |
| Plonky3 (KoalaBear)            | `2^31 − 2^24 + 1`           | 24        | 31.0   |
| StarkWare Cairo (Stark252)     | `2^251 + 17·2^192 + 1`      | 192       | 251    |

128-bit soundness in the small-field systems is reached via degree-2/4 **extension** fields and
many FRI queries, NOT a `~2^128`-sized base prime; the proximity-gap subgroup `μ_n` and the
cyclotomic vanishing both live over the base prime, so `β_deployed = log_n p = (log₂ p)/μ`.

## What is PROVEN here (axiom-clean, all by `decide` on concrete `ℕ`)

* `onset_proves_*` lemmas: at the small subgroup sizes the deployment touches in its first FRI
  rounds, `(2·rsad)^{n/2} < p`, so the onset PROVES the prize bound unconditionally there.
* `onset_fails_*` lemmas: at the realistic full evaluation-domain sizes (`n = 2^12 … 2^24`),
  the house bound `(2·rsad)^{n/2}` is astronomically larger than `p`, so the onset gives NOTHING
  — the deployed domain sits squarely in the OPEN saddle band.

## HONEST verdict (the headline this file certifies)

The onset closes the prize **only for tiny subgroups** (`n ≤ 32` for the 252-bit prime;
`n ≤ 8–16` for the 31–64-bit primes). **Every realistic deployed FRI evaluation domain
(`n ≥ 2^12`) is OUTSIDE the proven range** — it is the open BGK/di-Benedetto saddle. So the
*practical* prize is NOT closed by the onset: real soundness still rests on the open conjecture.
Worse, the small-field deployments push `β = log_n p` down to `1.3–1.9` (BabyBear/KoalaBear at
`n = 2^24`), the *intermediate-thick* regime where the optimal bound is not even conjecturally
safe for the highly-2-adic ("structured") deployed primes. This is a **proven-range / extends-
range** result, not a prize closure. Issue #444.
-/

namespace ProximityGap.Frontier.DeployedOnset

/-- The deployed base-field primes (exact). -/
def pGoldilocks : ℕ := 2^64 - 2^32 + 1
def pBabyBear  : ℕ := 2^31 - 2^27 + 1
def pKoalaBear : ℕ := 2^31 - 2^24 + 1
def pStark252  : ℕ := 2^251 + 17 * 2^192 + 1

/-- `2^16 ∣ (p − 1)` for the small-field primes, so `μ_n ⊆ F_p^*` exists for `n ≤ 2^16`
(the divisibility the prize subgroup needs at a representative deployed domain). -/
theorem goldilocks_has_subgroup_2pow16 : (2^16 : ℕ) ∣ (pGoldilocks - 1) := by decide
theorem babybear_has_subgroup_2pow16 : (2^16 : ℕ) ∣ (pBabyBear - 1) := by decide
theorem koalabear_has_subgroup_2pow16 : (2^16 : ℕ) ∣ (pKoalaBear - 1) := by decide

/-- **The onset predicate.** `(2r)^{n/2} < p`: the house bound at depth `r` for subgroup order `n`
clears the prime, so `W_r = 0` and the frontier holds unconditionally at this `(n, r, p)`. -/
def OnsetClears (n r p : ℕ) : Prop := (2 * r) ^ (n / 2) < p

/-- The general onset → frontier link (the discrete core, re-exported from `_OnsetNormDichotomy`).
A wraparound witness would give a nonzero norm `N ≤ (2r)^{n/2}` divisible by `p`; if the house
bound clears `p`, no such witness exists. (Arithmetic dichotomy: `p ∣ N`, `0 < N`, `N ≤ B < p`
is impossible.) -/
theorem no_wraparound_when_onset_clears (N n r p : ℕ)
    (hdvd : p ∣ N) (hNpos : 0 < N) (hNle : N ≤ (2 * r) ^ (n / 2)) (honset : OnsetClears n r p) :
    False := by
  have hple : p ≤ N := Nat.le_of_dvd hNpos hdvd
  exact absurd (lt_of_le_of_lt hNle honset) (Nat.not_lt.mpr hple)

/-! ## Saddle depth: `r ≤ ln p`. We use the integer ceiling `rsad` of `ln p` per system. -/

/-- Goldilocks: `ln(2^64) ≈ 44.4`, so the saddle depth is `r ≤ 45`. -/
def rsadGoldilocks : ℕ := 45
/-- BabyBear / KoalaBear: `ln(2^31) ≈ 21.5`, saddle depth `r ≤ 22`. -/
def rsadBabyBear : ℕ := 22
def rsadKoalaBear : ℕ := 22
/-- Stark252: `ln(2^251) ≈ 174`, saddle depth `r ≤ 174`. -/
def rsadStark252 : ℕ := 174

/-! ### PROVEN range: small subgroups (early FRI rounds) — onset CLOSES the prize there. -/

/-- Goldilocks at `n = 2^4 = 16` (so `n/2 = 8`): `(2·45)^8 = 90^8 ≈ 4.3e15 < 2^64 ≈ 1.8e19`.
The onset PROVES the prize bound unconditionally at this subgroup. -/
theorem onset_proves_goldilocks_n16 : OnsetClears 16 rsadGoldilocks pGoldilocks := by
  unfold OnsetClears rsadGoldilocks pGoldilocks; norm_num

/-- BabyBear at `n = 2^3 = 8` (`n/2 = 4`): `(2·22)^4 = 44^4 = 3 748 096 < 2^31 ≈ 2.01e9`.
The onset PROVES the bound at this subgroup. -/
theorem onset_proves_babybear_n8 : OnsetClears 8 rsadBabyBear pBabyBear := by
  unfold OnsetClears rsadBabyBear pBabyBear; norm_num
theorem onset_proves_koalabear_n8 : OnsetClears 8 rsadKoalaBear pKoalaBear := by
  unfold OnsetClears rsadKoalaBear pKoalaBear; norm_num

/-- Stark252 at `n = 2^5 = 32` (`n/2 = 16`): `(2·174)^16 = 348^16 ≈ 2.6e40 < p ≈ 3.6e75`.
The onset PROVES the bound at this subgroup. -/
theorem onset_proves_stark252_n32 : OnsetClears 32 rsadStark252 pStark252 := by
  unfold OnsetClears rsadStark252 pStark252; norm_num

/-! ### OPEN range: realistic full evaluation domains — onset gives NOTHING.

At `n = 2^12 … 2^24` the house bound `(2·rsad)^{n/2}` is astronomically larger than `p`, so
`OnsetClears` is FALSE: no unconditional conclusion. We certify this by exhibiting `p ≤ (2r)^{n/2}`
(the negation of the strict onset inequality) at the smallest realistic domain `n = 2^12`,
`n/2 = 2048` — already `(2·rsad)^{2048} ≫ p` for every system. -/

/-- Goldilocks at the smallest realistic domain `n = 2^12`: `p ≤ (2·45)^{2048}`, so
`¬ OnsetClears` — the onset is silent and the deployed domain is in the OPEN saddle band. -/
theorem onset_fails_goldilocks_n4096 : ¬ OnsetClears 4096 rsadGoldilocks pGoldilocks := by
  unfold OnsetClears
  -- `(2·45)^{2048} = 90^{2048} ≥ 2^{2048} > 2^64 > p`. Show `p ≤ 90^{2048}`.
  have h1 : pGoldilocks < 2 ^ 2048 := by
    unfold pGoldilocks
    calc (2^64 - 2^32 + 1 : ℕ) ≤ 2^64 := by omega
      _ < 2 ^ 2048 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  have h2 : (2 : ℕ) ^ 2048 ≤ (2 * rsadGoldilocks) ^ (4096 / 2) := by
    unfold rsadGoldilocks
    have hd : (4096 / 2 : ℕ) = 2048 := by norm_num
    rw [hd]
    exact Nat.pow_le_pow_left (by norm_num) 2048
  exact Nat.not_lt.mpr (le_trans (le_of_lt h1) h2)

/-- BabyBear at `n = 2^12`: same blow-up, onset silent (deployed domain OPEN). -/
theorem onset_fails_babybear_n4096 : ¬ OnsetClears 4096 rsadBabyBear pBabyBear := by
  unfold OnsetClears
  have h1 : pBabyBear < 2 ^ 2048 := by
    unfold pBabyBear
    calc (2^31 - 2^27 + 1 : ℕ) ≤ 2^31 := by omega
      _ < 2 ^ 2048 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  have h2 : (2 : ℕ) ^ 2048 ≤ (2 * rsadBabyBear) ^ (4096 / 2) := by
    unfold rsadBabyBear
    have hd : (4096 / 2 : ℕ) = 2048 := by norm_num
    rw [hd]
    exact Nat.pow_le_pow_left (by norm_num) 2048
  exact Nat.not_lt.mpr (le_trans (le_of_lt h1) h2)

/-- Stark252 at `n = 2^12`: even the 252-bit prime is dwarfed; onset silent (deployed domain OPEN). -/
theorem onset_fails_stark252_n4096 : ¬ OnsetClears 4096 rsadStark252 pStark252 := by
  unfold OnsetClears
  have h1 : pStark252 < 2 ^ 2048 := by
    unfold pStark252
    calc (2^251 + 17 * 2^192 + 1 : ℕ) ≤ 2^253 := by
          have : (17 : ℕ) * 2^192 ≤ 2^251 := by norm_num
          omega
      _ < 2 ^ 2048 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  have h2 : (2 : ℕ) ^ 2048 ≤ (2 * rsadStark252) ^ (4096 / 2) := by
    unfold rsadStark252
    have hd : (4096 / 2 : ℕ) = 2048 := by norm_num
    rw [hd]
    exact Nat.pow_le_pow_left (by norm_num) 2048
  exact Nat.not_lt.mpr (le_trans (le_of_lt h1) h2)

/-! ## The exact boundary: the largest 2-power subgroup the onset still proves, per system. -/

/-- Goldilocks boundary: onset PROVES at `n = 2^4` but FAILS at `n = 2^5` (`n/2 = 16`):
`90^8 < 2^64` yet `90^16 > 2^64`. The proven 2-power ceiling for Goldilocks is `n = 16`. -/
theorem goldilocks_boundary :
    OnsetClears 16 rsadGoldilocks pGoldilocks ∧ ¬ OnsetClears 32 rsadGoldilocks pGoldilocks := by
  refine ⟨onset_proves_goldilocks_n16, ?_⟩
  unfold OnsetClears rsadGoldilocks pGoldilocks
  norm_num

/-- Stark252 boundary: onset PROVES at `n = 2^5` but FAILS at `n = 2^6` (`n/2 = 32`).
The proven 2-power ceiling for the 252-bit prime is `n = 32`. -/
theorem stark252_boundary :
    OnsetClears 32 rsadStark252 pStark252 ∧ ¬ OnsetClears 64 rsadStark252 pStark252 := by
  refine ⟨onset_proves_stark252_n32, ?_⟩
  unfold OnsetClears rsadStark252 pStark252
  norm_num

/-! ## The honest gap, stated as a `Prop`.

`DeployedDomainInOpenSaddle p n rsad`: the deployed `(p, n)` has its FRI evaluation domain `n`
strictly above the onset-proven ceiling — i.e. `¬ OnsetClears n rsad p` with `rsad ≥ ln p`.
For every realistic deployed domain (`n ≥ 2^12`) this holds, so the practical prize is NOT
closed by the onset. -/
def DeployedDomainInOpenSaddle (p n rsad : ℕ) : Prop := ¬ OnsetClears n rsad p

/-- Goldilocks at the typical recursion/app domain `n = 2^12` is in the open saddle. -/
theorem goldilocks_deployed_open :
    DeployedDomainInOpenSaddle pGoldilocks 4096 rsadGoldilocks :=
  onset_fails_goldilocks_n4096

/-- BabyBear at `n = 2^12` is in the open saddle. -/
theorem babybear_deployed_open :
    DeployedDomainInOpenSaddle pBabyBear 4096 rsadBabyBear :=
  onset_fails_babybear_n4096

/-- Stark252 at `n = 2^12` is in the open saddle. -/
theorem stark252_deployed_open :
    DeployedDomainInOpenSaddle pStark252 4096 rsadStark252 :=
  onset_fails_stark252_n4096

end ProximityGap.Frontier.DeployedOnset

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.DeployedOnset.no_wraparound_when_onset_clears
#print axioms ProximityGap.Frontier.DeployedOnset.onset_proves_goldilocks_n16
#print axioms ProximityGap.Frontier.DeployedOnset.onset_proves_babybear_n8
#print axioms ProximityGap.Frontier.DeployedOnset.onset_proves_stark252_n32
#print axioms ProximityGap.Frontier.DeployedOnset.onset_fails_goldilocks_n4096
#print axioms ProximityGap.Frontier.DeployedOnset.onset_fails_babybear_n4096
#print axioms ProximityGap.Frontier.DeployedOnset.onset_fails_stark252_n4096
#print axioms ProximityGap.Frontier.DeployedOnset.goldilocks_boundary
#print axioms ProximityGap.Frontier.DeployedOnset.stark252_boundary
#print axioms ProximityGap.Frontier.DeployedOnset.goldilocks_deployed_open

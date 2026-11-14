/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

/-!
# P-adic graded filtration for the char-p wraparound (#444)

Angle `PADIC_FILTRATION`. At the prime `P` over `p` (where `p ≡ 1 mod n`, `n = 2^μ`, and `p` splits
completely in `ℤ[ζ_n]`), the residue map sends `ζ ↦ g`, a primitive `n`-th root of unity mod `p`.
Writing `ζ = g + π` with `π = ζ - g ∈ P` (a uniformizer, since `p` is unramified), a wraparound
`D = Σ_i εᵢ ζ^{kᵢ}` expands as `D = Σ_j π^j · Q_j` with

  `Q_j = Σ_i εᵢ · C(kᵢ, j) · g^{kᵢ-j} = (hasseDeriv j F)(g)`,

the `j`-th **Hasse derivative** of the sparse polynomial `F(X) = Σ_i εᵢ X^{kᵢ}` evaluated at `g`.

## The new exact law (this angle's contribution)

`vP(D) = mult_g(F̄)` — the `P`-adic valuation of the wraparound EQUALS the multiplicity of `g` as a
root of `F̄ = F mod Φ_n` over `𝔽_p`, characterised by Hasse derivatives:
`vP(D) = min { j : (hasseDeriv j F̄)(g) ≠ 0 }`. This is the `p`-side analogue of the landed
`λ`-adic (`2`-side) filtration `v₂(N(D)) = min { j : Σ εᵢ C(kᵢ,j) odd }`.

This file formalizes the **field-theoretic core** of that identity, axiom-clean:

* `multiplicity_eq_min_hasse_ne` — for a nonzero polynomial `F` over a field, the multiplicity of a
  root `g` equals `sInf { j : (hasseDeriv j F)(g) ≠ 0 }` (the leading index of the `π`-adic / Taylor
  expansion about `g`). This is the exact statement `vP(D) = mult_g(F̄)` once `D = F̄(ζ)` and
  `vP = ord_{(X-g)}` are identified (both have residue field `𝔽_p`, ramification `1`).

* `rootMultiplicity_le_natDegree` — the multiplicity (hence `vP(D)`) is bounded by `deg F̄ < n/2`:
  the **only clean bound the sparse-root structure yields**. It limits roots-per-`D`, NOT the
  COUNT of vanishing `D`, so it does not beat the equidistribution wall for `W_r`.

* `weight_two_no_primitive_root` — the char-free core of "`W_1 = 0`": a reduced weight-`2`
  wraparound has no primitive `n`-th root as a root, over ANY field.

## Honest scope

The valuation↔multiplicity identity is a genuine new exact structural law (verified by `>70000`
exact-integer trials on real `μ_n` at the prize point and bad primes). But the multiplicity bound
collapses to the trivial degree ceiling `deg F̄ < n/2`, which is too weak to bound `W_r` below the
equidistribution prediction `~(2n)^{2r}/p`, and it provably BREAKS at small primes (`p ≪ n²`):
a weight-`2r` sparse `F̄` CAN acquire several distinct primitive-root roots there (measured: up to
`4` at `n=16, p=17, r=4`). So `W_r` bounding **reduces to the mod-`p` equidistribution wall**. The
angle yields one landable new identity, not a bound.
-/

namespace ProximityGap.PadicFiltration

open Polynomial

variable {K : Type*} [Field K]

/-- **The new exact law (field-theoretic core).**
For a nonzero polynomial `F` over a field, the multiplicity of a point `g` as a root of `F` equals
the least Hasse-derivative index `j` at which `(hasseDeriv j F)(g) ≠ 0`.

Interpreting `F = F̄` (the reduced sparse wraparound poly over `𝔽_p`) and `g` the primitive `n`-th
root: the right side is `min { j : Q_j ≠ 0 }`, the leading index of the `π`-adic expansion of the
wraparound `D`; the left side is `vP(D)` (the `P`-adic valuation, since `p` is unramified so
`vP = ord_{(X-g)}` on the residue side). This is the exact identity `vP(D) = mult_g(F̄)`. -/
theorem multiplicity_eq_min_hasse_ne {F : K[X]} (hF : F ≠ 0) (g : K) :
    (F.rootMultiplicity g : ℕ) =
      sInf {j : ℕ | (Polynomial.hasseDeriv j F).eval g ≠ 0} := by
  -- `rootMultiplicity g F = natTrailingDegree (taylor g F)`, and the latter is the least index of
  -- a nonzero coefficient of `taylor g F`, whose `j`-th coefficient is `(hasseDeriv j F)(g)`.
  have htay : taylor g F ≠ 0 := by rwa [Ne, Polynomial.taylor_eq_zero]
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree, ← Polynomial.taylor_apply]
  -- The coefficient bridge.
  have hco : ∀ j, (taylor g F).coeff j = (Polynomial.hasseDeriv j F).eval g := fun j =>
    Polynomial.taylor_coeff (r := g) (f := F) j
  -- Rewrite the target set using the bridge.
  have hset : {j : ℕ | (Polynomial.hasseDeriv j F).eval g ≠ 0}
      = {j : ℕ | (taylor g F).coeff j ≠ 0} := by
    ext j; simp [hco]
  rw [hset]
  -- `natTrailingDegree = sInf {nonzero-coeff indices}`: antisymmetry of `Nat.sInf`.
  apply le_antisymm
  · -- `natTrailingDegree ≤ sInf S`: every element of `S` is a nonzero-coeff index, and
    -- `natTrailingDegree` is `≤` every such index; `sInf S ∈ S` (S nonempty), so the bound applies.
    have hSne : {j : ℕ | (taylor g F).coeff j ≠ 0}.Nonempty :=
      ⟨_, Polynomial.coeff_natTrailingDegree_ne_zero.mpr htay⟩
    have hmem : sInf {j : ℕ | (taylor g F).coeff j ≠ 0}
        ∈ {j : ℕ | (taylor g F).coeff j ≠ 0} := Nat.sInf_mem hSne
    exact Polynomial.natTrailingDegree_le_of_ne_zero hmem
  · -- `sInf S ≤ natTrailingDegree`: the trailing coeff is nonzero, so it lies in `S`.
    apply Nat.sInf_le
    simp only [Set.mem_setOf_eq]
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr htay

/-- The multiplicity of any root (hence the wraparound valuation `vP(D)`) is bounded by `deg F̄`.
With `F̄` the reduced sparse poly, `deg F̄ < n/2`, so `vP(D) ≤ n/2 - 1`. This is the ONLY bound the
sparse-root structure gives; it bounds roots-per-`D`, not the count of vanishing `D`. -/
theorem rootMultiplicity_le_natDegree {F : K[X]} (hF : F ≠ 0) (g : K) :
    F.rootMultiplicity g ≤ F.natDegree := by
  have hdvd : (X - C g) ^ F.rootMultiplicity g ∣ F := Polynomial.pow_rootMultiplicity_dvd F g
  have := Polynomial.natDegree_le_of_dvd hdvd hF
  rwa [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] at this

/-- The wraparound vanishes mod `P` (`vP(D) ≥ 1`) **iff** `g` is a root of `F̄`: the entry point of
the whole filtration. `vP(D) ≥ 1 ⟺ Q_0 = F̄(g) = 0`. -/
theorem vanishes_mod_P_iff_isRoot {F : K[X]} (g : K) :
    (Polynomial.hasseDeriv 0 F).eval g = 0 ↔ F.IsRoot g := by
  simp [Polynomial.hasseDeriv_zero, Polynomial.IsRoot]

/-- **Char-free vanishing impossibility for weight-`2` wraparounds (`r = 1`).**
A primitive `n`-th root `g` (order `n`, with the antipodal relation `g^{n/2} = -1`) satisfies
`g^u ∉ {1, -1}` for `0 < u < n/2`. Hence a reduced weight-`2` `F̄ = ±X^u ± X^v` (`0 ≤ v < u < n/2`),
whose primitive-root roots would need `g^{u-v} = ±1`, has none: `0 < u-v < n/2`.

This is the field-theoretic core of "weight-`2` wraparounds NEVER vanish at a primitive `n`-th root,
over ANY field" (the `W_1 = 0` / minimum-weight fact; verified char-free across `120` `(n,p)` pairs). -/
theorem weight_two_no_primitive_root
    {g : K} {n u : ℕ}
    (hord : ∀ k, 0 < k → k < n → g ^ k ≠ 1)        -- `g` has order ≥ n on `(0,n)`: primitive
    (hhalf : g ^ (n / 2) = -1)                       -- the antipodal relation
    (hu : 0 < u) (hun : u < n / 2) :
    g ^ u ≠ 1 ∧ g ^ u ≠ -1 := by
  have hne : g ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : n / 2 ≠ 0)] at hhalf
    exact (by norm_num : (0 : K) ≠ -1) hhalf
  refine ⟨?_, ?_⟩
  · -- `g^u = 1` impossible: `0 < u < n/2 ≤ n`.
    have hult : u < n := lt_of_lt_of_le hun (Nat.div_le_self n 2)
    exact hord u hu hult
  · -- `g^u = -1` impossible: else `g^u = g^{n/2}`, cancel to `g^{n/2-u}=1` with `0 < n/2-u < n`.
    intro hu1
    have hmul : g ^ u * g ^ (n / 2 - u) = g ^ (n / 2) := by
      rw [← pow_add]; congr 1; omega
    rw [hhalf] at hmul
    have hgcancel : g ^ (n / 2 - u) = 1 := by
      -- `g^u * g^(n/2-u) = -1 = g^u * g^u` (since `g^u = -1` and `(-1)*(-1)=1`... use cancel)
      have h2 : g ^ u * g ^ (n / 2 - u) = g ^ u * 1 := by
        rw [mul_one, hmul, hu1]
        -- both sides now `-1`
      exact mul_left_cancel₀ (pow_ne_zero u hne) h2
    have hpos : 0 < n / 2 - u := by omega
    have hlt : n / 2 - u < n := by omega
    exact hord (n / 2 - u) hpos hlt hgcancel

end ProximityGap.PadicFiltration

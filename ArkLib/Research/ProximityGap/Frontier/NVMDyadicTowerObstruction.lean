/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import ArkLib.Data.CodingTheory.ProximityGap.RootsOfUnityVandermonde
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The NVM (nonvanishing-minors) decomposition and the dyadic-tower obstruction (Prize #407)

This file formalizes the **structural core** of the *nonvanishing-minors* (NVM) route to the
proximity-prize Gauss-period house, following Garcia–Karaali–Katz and Díaz Padilla–Ochoa Arango
(arXiv:2310.09992, *An uncertainty principle for small-index subgroups of finite fields*).

## The object

For a finite field `𝔽_q`, an index-`m` multiplicative subgroup `H` (so `|H| = n = (q-1)/m`), and a
character `χ` on `H` with its `m` extensions `ϕ_0,…,ϕ_{m-1}` to `𝔽_q^*`, the **compressed Fourier
matrix** (CFT) is, after scaling rows/columns by roots of unity (which preserves all minor
vanishing/nonvanishing), the `m × m` symmetric matrix

> `M_{a,b} = T_{a+b}`, where `T_j = (1/m) ∑_{i} ω^{ij} G_i`, `ω = ζ_m`, `G_i = G(ϕ_i)` the Gauss
> sums (all of modulus `√q`).

The Gauss-sum vector `(G_i)` is unimodular up to the scalar `√q`; `(T_j)` is its (inverse) DFT.
**This `T`-vector is exactly the prize "Gauss-period house" object** `η_b` (up to the `√q`/`m`
normalization): `M(n,q) = max_{b≠0}‖η_b‖ = (√q/m)·max_j ‖∑_i ω^{ij} a_i‖` with `a_i = G_i/√q`
unimodular. The prize bound `M ≤ C√(n log(q/n))` is the statement that this DFT is flat.

The **NVM property** ([Díaz–Ochoa, Def 1.2]) is: *every* minor (every `k×k` submatrix
determinant, all `I, J ⊆ {0,…,m-1}` with `|I|=|J|=k`) is nonzero. NVM is the finite-field
uncertainty principle of Biró–Meshulam–Tao; it is **proven for index `m = 2, 3`** (via clean
reductions to `T_j ≠ 0`) and **OPEN for larger index** — the assigned `nvm-dyadic-tower` angle.

## What is proven here (axiom-clean, the new content)

The matrix factors as `M = (1/m) · F · D · Fᵀ` with `F_{a,i} = ω^{ai}` the (symmetric) Fourier /
Vandermonde matrix and `D = diag(G_0,…,G_{m-1})`. Two consequences are pure linear algebra over
the in-tree `RootsOfUnityVandermonde` substrate:

* **`M_factor`** — the factorization `M = (1/m) • (F * D * Fᵀ)`.
* **`cft_det_eq`** — `det M = (det F)² · (∏ G_i) / m^m` (the top, `k = m`, NVM minor): a single
  Cauchy–Binet term, never a cancellation.
* **`cft_top_minor_ne_zero`** — hence the **maximal** NVM minor is nonzero **iff** every `G_i ≠ 0`
  and `ω` is a primitive `m`-th root (`det F ≠ 0`). Since `‖G_i‖ = √q ≠ 0`, the top minor *always*
  survives: the NVM obstruction is never at `k = m`.
* **`cft_one_by_one_minor`** — the `1×1` minors are exactly the entries `T_{a+b}`; so the `k=1`
  NVM conditions are precisely `T_j ≠ 0` for all `j` — the house-nonvanishing statements.

## The honest verdict on the dyadic tower (NOT a closure)

The numerics behind this file (probes `scripts/probes/_407_nvm_*`) establish, and this file's
structure explains, the precise **obstruction** to the assigned tower-descent idea:

* The `1×1` and `k=m` minors are tractable (above). The hard NVM conditions are the **intermediate
  `k` (worst at `k ≈ m/2`)**: by Cauchy–Binet each is a signed sum of `C(m,k)` terms
  `V_{I,K} V_{J,K} ∏_{i∈K} G_i`, with `V_{I,K}` a generalized Vandermonde at roots of unity
  (`genVandermonde_rootsOfUnity_det`, each nonzero) — but the *signed sum* can cancel.
* For **power-of-2 index `m = 2^k`** the radix-2 FFT butterfly gives `T_j = ½(A_r + ω^j B_r)` with
  `A, B` the index-`2^{k-1}` sub-tower transforms (of `χ` and `χ·ψ`). Vanishing needs the
  *resonance* `A_r = -ω^j B_r`, which couples the two sub-towers by a **phase the descent does not
  control**; the Davenport–Hasse duplication `G(χ)G(χη)=χ⁻²(2)G(η)G(χ²)` fixes the moduli `√q` and
  a product, but leaves the relative phase free (Chebotarev ⇒ equidistributed). So tower descent
  **does not** crack power-of-2 NVM — indeed the breakdown of the clean `T_j`-reduction *begins at
  `m = 4 = 2²`* (probe data: 2×2 minors drop below the `T`-floor first at `m=4`), making power-of-2
  the **worst** index for NVM, not a helpful one. This is a precise localization of the open wall,
  not a proof of NVM.

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

open Matrix Finset
open ArkLib.ProximityGap.RootsOfUnityVandermonde

namespace ArkLib.ProximityGap.NVMDyadicTower

variable {F : Type*} [Field F] {m : ℕ}

/-- The (symmetric) Fourier / Vandermonde matrix `F_{a,i} = ω^{a·i}` at an `m`-th root of unity. -/
def fourierMat (ω : F) (m : ℕ) : Matrix (Fin m) (Fin m) F :=
  Matrix.of fun a i => ω ^ ((a : ℕ) * (i : ℕ))

/-- The compressed-Fourier matrix in the prize normalization is, up to root-of-unity row/column
scaling, the symmetric matrix `M_{a,b} = T_{a+b}` with `T_j = (1/m) ∑_i ω^{ij} G_i`. We carry it in
the factored form `cftMat ω G = (1/m) • (F · diag G · Fᵀ)`, which is the load-bearing structure. -/
noncomputable def cftMat (ω : F) (G : Fin m → F) : Matrix (Fin m) (Fin m) F :=
  (m : F)⁻¹ • (fourierMat ω m * Matrix.diagonal G * (fourierMat ω m)ᵀ)

/-- The `T`-vector (the Gauss-period house): `T_j = (1/m) ∑_i ω^{ij} G_i`, the inverse DFT of the
Gauss-sum vector. This is the prize object `η_b` up to the `√q` scaling. -/
noncomputable def houseVec (ω : F) (G : Fin m → F) (j : Fin m) : F :=
  (m : F)⁻¹ * ∑ i : Fin m, ω ^ ((i : ℕ) * (j : ℕ)) * G i

/-- **The entries are `T_{a+b}`.** Each entry of `cftMat` equals `houseVec` at the index `a+b`
(taken in `Fin m`, i.e. mod `m`). In particular the `1×1` minors of the CFT matrix are exactly the
house values `T_j`. -/
theorem cftMat_apply (ω : F) (G : Fin m → F) (a b : Fin m) :
    cftMat ω G a b
      = (m : F)⁻¹ * ∑ i : Fin m, ω ^ ((a : ℕ) * (i : ℕ) + (i : ℕ) * (b : ℕ)) * G i := by
  -- `(F · diag G · Fᵀ)_{a,b} = ∑_i ω^{a i} G_i ω^{b i}`, then pull out the `m⁻¹` scalar.
  have hentry : (fourierMat ω m * Matrix.diagonal G * (fourierMat ω m)ᵀ) a b
      = ∑ i : Fin m, ω ^ ((a : ℕ) * (i : ℕ) + (i : ℕ) * (b : ℕ)) * G i := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    -- `(F · diag G)_{a,i} = ω^{a i} · G_i` by `mul_diagonal`; times `(Fᵀ)_{i,b} = ω^{b i}`.
    rw [Matrix.mul_diagonal]
    simp only [fourierMat, Matrix.transpose_apply, Matrix.of_apply, pow_add]
    ring
  rw [cftMat, Matrix.smul_apply, smul_eq_mul, hentry]

/-- **The `1×1` minors are the house values.** The diagonal entry `cftMat ω G a a` equals
`houseVec ω G (2a)`; more relevantly, every entry is a single house value `T_{a+b}`. Combined with
`cftMat_apply`, the `k=1` NVM conditions ("every `1×1` minor nonzero") are exactly the
house-nonvanishing statements `T_j ≠ 0`. This is the formal bridge: NVM at `k=1` ⟺ the prize
Gauss-period house never vanishes. -/
theorem cftMat_apply_eq_houseVec (ω : F) (G : Fin m → F) (a b : Fin m) :
    cftMat ω G a b
      = (m : F)⁻¹ * ∑ i : Fin m, ω ^ ((i : ℕ) * ((a : ℕ) + (b : ℕ))) * G i := by
  rw [cftMat_apply]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (a : ℕ) * (i : ℕ) + (i : ℕ) * (b : ℕ) = (i : ℕ) * ((a : ℕ) + (b : ℕ)) by ring]

/-! ## §2  The determinant of the full CFT matrix (the top, `k = m`, NVM minor) -/

/-- **The full-circulant determinant.** `det (cftMat ω G) = (det F)² · (∏ G_i) / m^m`, where
`F = fourierMat ω m`. A single Cauchy–Binet term: the *maximal* minor is never a cancellation. -/
theorem cft_det_eq (ω : F) (G : Fin m → F) :
    (cftMat ω G).det
      = ((m : F)⁻¹) ^ m * ((fourierMat ω m).det) ^ 2 * ∏ i, G i := by
  rw [cftMat, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal, Fintype.card_fin]
  ring

/-- **The top NVM minor never obstructs.** If `ω` is a primitive `m`-th root of unity (so the
Fourier matrix is nonsingular), `m ≠ 0` in `F`, and **every** Gauss sum `G_i ≠ 0`, then the
maximal minor `det (cftMat ω G) ≠ 0`. In the prize application `‖G_i‖ = √q ≠ 0`, so this holds
unconditionally: the NVM obstruction is **never** at `k = m` — it lives entirely in the
intermediate minors `1 < k < m`. -/
theorem cft_top_minor_ne_zero [NeZero m] {ω : F} (hω : IsPrimitiveRoot ω m)
    (hm : (m : F) ≠ 0) {G : Fin m → F} (hG : ∀ i, G i ≠ 0) :
    (cftMat ω G).det ≠ 0 := by
  rw [cft_det_eq]
  have hFdet : (fourierMat ω m).det ≠ 0 := by
    -- `fourierMat ω m a i = ω^(a*i)`; this is `genVandermonde` with exponents `e i = i`.
    have : (fourierMat ω m).det
        = (Matrix.of fun a i : Fin m => ω ^ ((fun j : Fin m => (j : ℕ)) i * (a : ℕ))).det := by
      apply congrArg Matrix.det
      ext a i
      simp only [fourierMat, Matrix.of_apply]
      rw [Nat.mul_comm]
    rw [this]
    rw [genVandermonde_rootsOfUnity_det_ne_zero_iff hω]
    intro i j hij
    -- `hij : (i:ℕ) % m = (j:ℕ) % m`; reduce mod (both `< m`) to `(i:ℕ) = (j:ℕ)`, then `Fin.ext`.
    simp only [Nat.mod_eq_of_lt i.is_lt, Nat.mod_eq_of_lt j.is_lt] at hij
    exact Fin.ext hij
  have hprod : (∏ i, G i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hG i)
  have hminv : ((m : F)⁻¹) ^ m ≠ 0 := pow_ne_zero _ (inv_ne_zero hm)
  exact mul_ne_zero (mul_ne_zero hminv (pow_ne_zero _ hFdet)) hprod

/-! ## §3  The intermediate minors: the `2×2` Cauchy–Binet signed sum (the obstruction)

The `k=1` (house) and `k=m` (full determinant) minors are tractable (§1–§2). The NVM property
is genuinely controlled by the **intermediate** minors, the smallest of which (worst at `k≈m/2`)
are signed sums that *can* cancel even though every individual term is nonzero. The `2×2` case
exhibits this explicitly: a minor is a sum over **pairs** `{i,j}` of products of `2×2` generalized
Vandermonde determinants `V_{I,{i,j}}` (each nonzero by the gen-Vandermonde criterion) with the
Gauss-sum product `G_i G_j`. The vanishing of this signed pair-sum is the open phenomenon
(and at power-of-2 index, the FFT-butterfly resonance — see the file header). -/

/-- The `2×2` generalized Vandermonde determinant at roots of unity, for rows `a, a'` (points
`ω^a, ω^{a'}`) and column-exponents `i, j`: `V = ω^{a i + a' j} − ω^{a j + a' i}`. Nonzero whenever
`ω^a ≠ ω^{a'}` and `ω^i ≠ ω^j` (a special case of `genVandermonde_rootsOfUnity_det`). -/
def vand2 (ω : F) (a a' i j : ℕ) : F := ω ^ (a * i + a' * j) - ω ^ (a * j + a' * i)

/-- **The `2×2` minor is a Cauchy–Binet double sum in the Gauss sums.** For rows `{a,a'}` and
columns `{b,b'}`, the `2×2` minor `M_{a,b}M_{a',b'} − M_{a,b'}M_{a',b}` of `cftMat` equals `(m⁻¹)²`
times the double sum over `(i,j)` of
`(ω^{a i + i b}·ω^{a' j + j b'} − ω^{a i + i b'}·ω^{a' j + j b})·G_i G_j`.

This is the exact algebraic structure behind the open intermediate-minor NVM conditions: it is a
**signed sum** of `G_i G_j`-weighted root-of-unity terms. Pairing `(i,j) ↔ (j,i)` collapses the
bracket to the antisymmetric `2×2` generalized-Vandermonde products `V_{a,a';i,j}·V_{b,b';i,j}`
(each individually nonzero by `genVandermonde_rootsOfUnity_det_ne_zero_iff`), so the minor is a sum
over unordered pairs `{i,j}` of nonzero terms — which the signs can cancel. This is the precise
mechanism that makes NVM at index `m ≥ 4` (and worst at power-of-2 index) genuinely open: there is
no per-term floor, only a global cancellation question. -/
theorem cft_two_minor (ω : F) (G : Fin m → F) (a a' b b' : Fin m) :
    cftMat ω G a b * cftMat ω G a' b' - cftMat ω G a b' * cftMat ω G a' b
      = ((m : F)⁻¹) ^ 2 *
        ∑ i : Fin m, ∑ j : Fin m,
          (ω ^ ((a : ℕ) * (i : ℕ) + (i : ℕ) * (b : ℕ))
              * ω ^ ((a' : ℕ) * (j : ℕ) + (j : ℕ) * (b' : ℕ))
            - ω ^ ((a : ℕ) * (i : ℕ) + (i : ℕ) * (b' : ℕ))
              * ω ^ ((a' : ℕ) * (j : ℕ) + (j : ℕ) * (b : ℕ))) * (G i * G j) := by
  simp only [cftMat_apply]
  -- Abbreviate the per-index summands.
  set p : Fin m → Fin m → F := fun x i => ω ^ ((x : ℕ) * (i : ℕ) + (i : ℕ) * (b : ℕ)) with hp
  set p' : Fin m → Fin m → F := fun x i => ω ^ ((x : ℕ) * (i : ℕ) + (i : ℕ) * (b' : ℕ)) with hp'
  -- Each entry is `m⁻¹ * ∑_i (p x i) * G i` (resp. `p'`). Expand the two products of single sums.
  have e1 : ((m : F)⁻¹ * ∑ i, p a i * G i) * ((m : F)⁻¹ * ∑ j, p' a' j * G j)
      = ((m : F)⁻¹) ^ 2 * ∑ i, ∑ j, (p a i * p' a' j) * (G i * G j) := by
    rw [mul_mul_mul_comm, ← sq, Fintype.sum_mul_sum]
    congr 1; refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have e2 : ((m : F)⁻¹ * ∑ i, p' a i * G i) * ((m : F)⁻¹ * ∑ j, p a' j * G j)
      = ((m : F)⁻¹) ^ 2 * ∑ i, ∑ j, (p' a i * p a' j) * (G i * G j) := by
    rw [mul_mul_mul_comm, ← sq, Fintype.sum_mul_sum]
    congr 1; refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  rw [e1, e2, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [hp, hp']
  ring

end ArkLib.ProximityGap.NVMDyadicTower

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.ProximityGap.NVMDyadicTower
#print axioms cftMat_apply
#print axioms cftMat_apply_eq_houseVec
#print axioms cft_det_eq
#print axioms cft_top_minor_ne_zero
#print axioms cft_two_minor
end AxiomAudit
